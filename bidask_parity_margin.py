# -*- coding: utf-8 -*-
"""
BID/ASK-ONLY PARITY ENGINE — ALL DAY RUN
=======================================
Fork of exec_parity_test.py. Same 216-stock universe, same token/market-map
build, same cash/future/CE/PE subscriptions, same FULL mode, same ₹1,300 gate,
same staleness gate, same reconnection logic, same checkpointing. Engine 1 (LTP)
does not open windows here — the book is the only signal source.

ENGINE 2 — BID/ASK (the whole engine)
  Both sides are priced from the book, only the legs you would really trade:
    CHEAP    (buy CE, sell PE, sell FUT): pe_bid + fut_bid - ce_ask - K
    EXPENSIVE(sell CE, buy PE, buy FUT) : ce_bid - pe_ask - fut_ask + K
  The side with the larger number is the direction. The value is signed PROFIT
  per lot, so ₹1,300 is only reached when the trade still pays after the spread.
  Opens its own window on that number, tracks its own peak, closes its own
  window and asks its own basket margin at limit prices from the book.

ENGINE 1 (LTP) IS OFF: no parity_windows.csv.gz, no parity_ticks.csv.gz, no
LTP window state. The LTP prices are still read and printed beside every
book number (ltp_* columns) so you can see the two side by side, but a
window opens only on the book. Gate, formulas, lot logic, margin lookup and
staleness checks are byte-identical to exec_parity_test.py.

Output files (bidask_output/):
  exec_windows.csv      — windows, one row per completed window, written immediately
  exec_ticks.csv        — engine-2 ticks above gate
  console_log.txt       — live console, includes depth coverage every 15s
  startup_snapshot.json — checkpoint: market map + config, rewritten as it runs
  health.csv.gz, atm_events.csv.gz, sub_events.csv.gz — same as exec
"""

from __future__ import annotations

import atexit
import bisect
import csv
import collections
import gzip
import hashlib
import io
import json
import os
import queue
import sys
import threading
import time
import traceback
import urllib.error
import urllib.request
from datetime import datetime, timezone
from zoneinfo import ZoneInfo

from pyarrow_client import ArrowClient, ArrowStreams, DataMode
# ---- inlined from margin_system.py: NSE SPAN+ELM downloader + margin engine (no broker, no API) ----
import re
import zipfile
import datetime as dt
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
import requests

# ======================================================================== MARGIN ENGINE

INDEX_SYMBOLS = frozenset({"NIFTY", "BANKNIFTY", "FINNIFTY", "MIDCPNIFTY", "NIFTYNXT50"})
INDEX_ELM = 0.02
INDEX_EXPIRY_DAY_EXTRA = 0.02
N_SCENARIOS = 16


# ---------------------------------------------------------------- data types
@dataclass(frozen=True)
class Leg:
    symbol: str                 # underlying, e.g. "RELIANCE", "M&M"
    kind: str                   # "F" future, "C" call, "P" put
    side: int                   # +1 buy, -1 sell
    qty: int                    # units (lots * lot size), always positive
    expiry: str | None = None   # "YYYYMMDD"; None = nearest expiry in the file
    strike: float | None = None
    price: float | None = None  # live future price / live option premium; None = file price


# ---------------------------------------------------------------- parsing
def _f(tag, block, default=None):
    m = re.search(r"<%s>([^<]*)</%s>" % (tag, tag), block)
    if not m:
        return default
    try:
        return float(m.group(1))
    except ValueError:
        return default


def _ra(block):
    return [float(x) for x in re.findall(r"<a>([-\d.]+)</a>", block)]


def _code(block):
    raw = re.search(r"<pfCode>([^<]+)</pfCode>", block).group(1)
    return (raw.replace("&amp;", "&").replace("&#13;", "").replace("&lt;", "<")
               .replace("&gt;", ">").strip())


def _pe(block):
    return str(int(_f("pe", block, 0)))


def load_span(path, symbols=None):
    """-> spot{sym: price}, fut{(sym, pe): {price, ra}}, opt{(sym, pe, strike, 'C'|'P'): {price, ra}}"""
    with open(path, "rb") as fh:
        txt = fh.read().decode("utf-8", "replace")
    want = (lambda c: True) if symbols is None else (lambda c: c in symbols)
    spot, fut, opt = {}, {}, {}

    def arrays(ra, what):
        if len(ra) < N_SCENARIOS:        # fewer than 16 = a broken record; extra values are ignored (as the validated replay parser does)
            raise ValueError("%s: expected %d risk-array values, found %d" % (what, N_SCENARIOS, len(ra)))
        return ra[:N_SCENARIOS]

    for m in re.finditer(r"<phyPf>(.*?)</phyPf>", txt, re.S):
        b = m.group(1)
        code = _code(b)
        inner = re.search(r"<phy>(.*?)</phy>", b, re.S)
        if want(code) and inner:
            spot[code] = _f("p", inner.group(1))
    for m in re.finditer(r"<futPf>(.*?)</futPf>", txt, re.S):
        b = m.group(1)
        code = _code(b)
        if not want(code):
            continue
        for fm in re.finditer(r"<fut>(.*?)</fut>", b, re.S):
            fb = fm.group(1)
            pe = _pe(fb)
            fut[(code, pe)] = {"price": _f("p", fb),
                               "ra": arrays(_ra(fb), "future %s %s" % (code, pe))}
    for m in re.finditer(r"<oopPf>(.*?)</oopPf>", txt, re.S):
        b = m.group(1)
        code = _code(b)
        if not want(code):
            continue
        for sm in re.finditer(r"<series>(.*?)</series>", b, re.S):
            sb = sm.group(1)
            pe = _pe(sb)
            for om in re.finditer(r"<opt>(.*?)</opt>", sb, re.S):
                ob = om.group(1)
                cp = re.search(r"<o>([^<]+)</o>", ob).group(1)
                k = round(_f("k", ob), 2)
                opt[(code, pe, k, cp)] = {"price": _f("p", ob),
                                          "ra": arrays(_ra(ob), "option %s %s %s %s" % (code, pe, k, cp))}
    return spot, fut, opt


def load_elm(path):
    """-> {symbol: {'OTH': fraction, 'OTM': fraction}} from the 'Total applicable ELM%' column."""
    out = defaultdict(dict)
    with open(path, encoding="utf-8-sig", newline="") as fh:
        rd = csv.DictReader(fh)
        tot = [c for c in rd.fieldnames if "Total" in c][0]
        for row in rd:
            out[row["Symbol"].strip()][row["Instrument Type"].strip()] = float(row[tot]) / 100.0
    return dict(out)


# ---------------------------------------------------------------- engine
class MarginEngine:
    def __init__(self, span_path, elm_path, symbols=None, deep_otm_pct=None, nov_price="file"):
        """symbols: restrict parsing to these underlyings (fast).  deep_otm_pct: e.g. 0.15 sends options
        further than 15% from spot to the OTM ELM row; None (default) = OTH row everywhere.
        nov_price: 'file' (exchange's own premium, default) or 'trade' (leg.price when given)."""
        if nov_price not in ("file", "trade"):
            raise ValueError("nov_price must be 'file' or 'trade'")
        self.symbols = set(symbols) if symbols else None
        self.spot, self.fut, self.opt = load_span(span_path, self.symbols)
        self.elm = load_elm(elm_path)
        self.deep_otm_pct = deep_otm_pct
        self.nov_price = nov_price

    def with_elm(self, elm_path):
        """Same SPAN data, freshly loaded ELM table (cheap: the big SPAN file is not re-parsed)."""
        new = object.__new__(MarginEngine)
        new.__dict__.update(self.__dict__)
        new.elm = load_elm(elm_path)
        return new

    # -- lookups
    def expiries(self, symbol):
        return sorted({pe for (s, pe) in self.fut if s == symbol})

    def _resolve_expiry(self, leg):
        if leg.expiry:
            return str(int(leg.expiry))
        if leg.kind == "F":
            cands = [pe for (s, pe) in self.fut if s == leg.symbol]
        else:
            cands = [pe for (s, pe, k, cp) in self.opt
                     if s == leg.symbol and cp == leg.kind and k == round(leg.strike, 2)]
        if not cands:
            raise KeyError("no contract found for %s" % (leg,))
        return min(cands)

    def _contract(self, leg, pe):
        if leg.kind == "F":
            c = self.fut.get((leg.symbol, pe))
        else:
            c = self.opt.get((leg.symbol, pe, round(leg.strike, 2), leg.kind))
        if c is None:
            raise KeyError("contract not in SPAN file: %s expiry %s" % (leg, pe))
        return c

    def _elm_rate(self, symbol, deep, expiry, today, short_option, warnings):
        d = self.elm.get(symbol)
        if d is not None:
            return d["OTM"] if (deep and "OTM" in d) else d["OTH"]
        if symbol in INDEX_SYMBOLS:
            warnings.append("%s: index ELM %.0f%% used (UNVERIFIED; not in ael file)" % (symbol, INDEX_ELM * 100))
            extra = INDEX_EXPIRY_DAY_EXTRA if (short_option and today and str(expiry) == str(today)) else 0.0
            return INDEX_ELM + extra
        raise KeyError("%s has no row in the ael file" % symbol)

    # -- main call
    def margin(self, legs, spot=None, today=None):
        """legs: list[Leg].  spot: optional {symbol: live spot} for option ELM.  today: 'YYYYMMDD' (index expiry-day ELM)."""
        spot = spot or {}
        warnings = []

        # 1. resolve expiries and net identical contracts
        net = {}
        for lg in legs:
            if lg.kind not in ("F", "C", "P") or lg.side not in (1, -1) or lg.qty <= 0:
                raise ValueError("bad leg: %s" % (lg,))
            if lg.kind != "F" and lg.strike is None:
                raise ValueError("option leg needs a strike: %s" % (lg,))
            pe = self._resolve_expiry(lg)
            key = (lg.symbol, lg.kind, pe, None if lg.kind == "F" else round(lg.strike, 2))
            cur = net.get(key, [0, None])
            cur[0] += lg.side * lg.qty
            cur[1] = lg.price if lg.price is not None else cur[1]
            net[key] = cur
        net = {k: v for k, v in net.items() if v[0] != 0}

        # 2. SPAN per underlying
        by_sym = defaultdict(list)
        for (sym, kind, pe, k), (q, px) in net.items():
            by_sym[sym].append((kind, pe, k, q, px))
        span_total, scan_total, nov_total = 0.0, 0.0, 0.0
        per_symbol = {}
        for sym, items in by_sym.items():
            if len({pe for _, pe, _, _, _ in items}) > 1:
                warnings.append("%s: several expiries - calendar-spread charge NOT modelled" % sym)
            loss = [0.0] * N_SCENARIOS
            nov = 0.0
            for kind, pe, k, q, px in items:
                c = self._contract(Leg(sym, kind, 1 if q > 0 else -1, abs(q), pe, k), pe)
                for i in range(N_SCENARIOS):
                    loss[i] += q * c["ra"][i]
                if kind != "F":
                    p = px if (self.nov_price == "trade" and px is not None) else c["price"]
                    nov += q * p
            scan = max(loss)
            sp = max(0.0, scan - nov)
            per_symbol[sym] = {"scan": scan, "nov": nov, "span": sp}
            span_total += sp
            scan_total += scan
            nov_total += nov

        # 3. ELM: futures + net-short options only
        elm_total, detail = 0.0, []
        debit = credit = 0.0
        for (sym, kind, pe, k), (q, px) in net.items():
            c = self._contract(Leg(sym, kind, 1 if q > 0 else -1, abs(q), pe, k), pe)
            if kind == "F":
                base = px if px is not None else c["price"]
                rate = self._elm_rate(sym, False, pe, today, False, warnings)
            else:
                prem = px if px is not None else c["price"]
                if q > 0:
                    debit += q * prem
                    continue                      # long option: premium only, no ELM
                credit += -q * prem
                base = spot.get(sym, self.spot.get(sym))
                if base is None:
                    raise KeyError("no spot for %s (not in SPAN file, not supplied)" % sym)
                deep = (self.deep_otm_pct is not None
                        and abs(k / base - 1.0) > self.deep_otm_pct)
                rate = self._elm_rate(sym, deep, pe, today, True, warnings)
            e = rate * abs(q) * base
            elm_total += e
            detail.append({"symbol": sym, "kind": kind, "expiry": pe, "strike": k, "qty": q,
                           "rate": rate, "base": base, "elm": e})

        return {"span": span_total, "elm": elm_total, "total": span_total + elm_total,
                "scan": scan_total, "nov": nov_total,
                "premium_debit": debit, "premium_credit": credit,
                "by_symbol": per_symbol, "elm_detail": detail, "warnings": sorted(set(warnings))}


# ======================================================================== NSE DOWNLOADER
HOME = "https://www.nseindia.com/all-reports-derivatives"
API = "https://www.nseindia.com/api/reports"
ARCHIVE = "https://nsearchives.nseindia.com"
OUT = Path(os.getenv("NSE_DATA_DIR", "nse_data"))   # point at a Railway Volume to keep files across restarts

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
    ),
    "Accept": "*/*",
    "Accept-Language": "en-US,en;q=0.9",
    "Referer": HOME,
}

# Newest first within one trading day: End of day, 4 intraday, Begin of day.
SPAN_KINDS = [
    ("s", "F&O - Span Risk Parameter File (End of day)"),
    ("i5", "F&O - Span Risk Parameter File (4th intra-day)"),
    ("i4", "F&O - Span Risk Parameter File (3rd intra-day)"),
    ("i3", "F&O - Span Risk Parameter File (2nd intra-day)"),
    ("i2", "F&O - Span Risk Parameter File (1st intra-day)"),
    ("i1", "F&O - Span Risk Parameter File (Begin of day)"),
]
EXPOSURE_REPORT = "F&O - Exposure Limit file"


def day_dir(d: dt.date) -> Path:
    p = OUT / d.strftime("%Y%m%d")
    p.mkdir(parents=True, exist_ok=True)
    return p


def write_atomic(dest: Path, data: bytes) -> None:
    tmp = dest.with_name(dest.name + ".part")
    tmp.write_bytes(data)
    for i in range(5):         # Windows: rename fails briefly if a reader has the file open
        try:
            tmp.replace(dest)  # atomic rename: readers see the old file or the whole new one
            return
        except PermissionError:
            if i == 4:
                tmp.unlink(missing_ok=True)
                raise
            time.sleep(0.5)


def valid_spn(data: bytes) -> bool:
    """A complete SPAN file: has futures + options sections and the closing tag."""
    # zip CRC already catches truncation; this guards against a wrong/empty member
    return len(data) > 100_000 and b"<futPf>" in data and b"<oopPf>" in data


def valid_elm(data: bytes) -> bool:
    """A real ael table: header with Symbol + Total column and a sane number of rows."""
    try:
        txt = data.decode("utf-8-sig")
    except UnicodeDecodeError:
        return False
    lines = [l for l in txt.splitlines() if l.strip()]
    if len(lines) < 50:
        return False
    head = lines[0]
    return "Symbol" in head and "Total" in head and "Instrument Type" in head


def trading_days_back(n: int):
    """Today, then previous weekdays (holidays are simply tried and found empty)."""
    d = dt.date.today()
    out = []
    while len(out) <= n:
        if d.weekday() < 5:
            out.append(d)
        d -= dt.timedelta(days=1)
    return out


class NSE:
    def __init__(self) -> None:
        self.s = requests.Session()
        self.s.headers.update(HEADERS)
        self._warm()

    def _warm(self) -> None:
        # This page sets the session cookie; the site root returns 403.
        try:
            self.s.get(HOME, timeout=30)
        except requests.RequestException as e:
            print("warm-up failed:", e, file=sys.stderr)   # retried on the next request

    def report(self, name: str, d: dt.date) -> bytes | None:
        params = {
            "archives": json.dumps(
                [{"name": name, "type": "archives", "category": "derivatives", "section": "equity"}],
                separators=(",", ":"),
            ),
            "date": d.strftime("%d-%b-%Y"),
            "type": "equity",
            "mode": "single",
        }
        r = None
        for attempt in (1, 2):
            try:
                r = self.s.get(API, params=params, timeout=60)
            except requests.RequestException:
                if attempt == 1:
                    self._warm()
                    continue
                return None
            if r.status_code in (401, 403) and attempt == 1:
                self._warm()  # cookie expired
                continue
            break
        if r is None or r.status_code != 200 or not r.content:
            return None
        return r.content

    def archive_file(self, path: str) -> bytes | None:
        try:
            r = self.s.get(f"{ARCHIVE}{path}", timeout=60)
        except requests.RequestException:
            return None
        return r.content if r.status_code == 200 and r.content else None


# ---------------------------------------------------------------- SPAN
def fetch_span(nse: NSE, d: dt.date, code: str, name: str) -> Path | None:
    dest = day_dir(d) / f"nsccl.{d:%Y%m%d}.{code}.spn"
    if dest.exists():
        return dest
    data = nse.report(name, d)
    if not data or not zipfile.is_zipfile(io.BytesIO(data)):
        return None
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        members = [m for m in z.namelist() if m.lower().endswith(".spn")]
        if not members:
            return None
        body = z.read(members[0])
        if not valid_spn(body):
            return None
        write_atomic(dest, body)
    return dest


def latest_span(nse: NSE, days_back: int = 5) -> Path | None:
    for d in trading_days_back(days_back):
        for code, name in SPAN_KINDS:
            p = fetch_span(nse, d, code, name)
            if p:
                return p
            time.sleep(0.4)
    return None


# ---------------------------------------------------------------- once-a-day files
def fetch_exposure(nse: NSE, d: dt.date, refresh: bool = False) -> tuple[Path | None, bool]:
    """-> (path, changed).  With refresh=True the file is downloaded again and replaced if its bytes differ."""
    dest = day_dir(d) / f"ael_{d:%d%m%Y}.csv"
    if dest.exists() and not refresh:
        return dest, False
    data = nse.report(EXPOSURE_REPORT, d)
    if not data:
        return (dest if dest.exists() else None), False
    if zipfile.is_zipfile(io.BytesIO(data)):
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            data = z.read(z.namelist()[0])
    if not valid_elm(data):
        return (dest if dest.exists() else None), False
    if dest.exists() and dest.read_bytes() == data:
        return dest, False
    write_atomic(dest, data)
    return dest, True


def newest_elm(nse: NSE, days_back: int = 5) -> tuple[Path | None, bool]:
    """Today's ELM file (re-checked every call); if not out yet, the most recent earlier one."""
    for i, d in enumerate(trading_days_back(days_back)):
        p, changed = fetch_exposure(nse, d, refresh=(i == 0))
        if p:
            return p, changed
        time.sleep(0.4)
    return None, False


# ---------------------------------------------------------------- hooks (put your engine here)
def on_new_span(spn: Path) -> None:
    """A newer SPAN file is on disk and complete."""
    print(f"{dt.datetime.now():%H:%M:%S} new SPAN file: {spn}")


def on_new_elm(path: Path) -> None:
    """An ELM file for today is on disk (new or changed)."""
    print(f"{dt.datetime.now():%H:%M:%S} ELM file updated: {path}")


# ---------------------------------------------------------------- main loop
def cycle(nse: NSE, state: dict, on_span=None, on_elm=None) -> None:
    on_span = on_span or on_new_span
    on_elm = on_elm or on_new_elm
    elm, changed = newest_elm(nse)
    if elm is None:
        print(f"{dt.datetime.now():%H:%M:%S} ELM: NOT FOUND", file=sys.stderr)
    elif changed or elm != state.get("elm"):
        try:
            on_elm(elm)
            state["elm"] = elm          # only after the engine accepted it -> retried otherwise
        except Exception as e:
            print("on_new_elm failed (will retry):", e, file=sys.stderr)

    spn = latest_span(nse)
    if spn is None:
        print(f"{dt.datetime.now():%H:%M:%S} SPAN: NOT FOUND", file=sys.stderr)
    elif spn != state.get("span"):
        try:
            on_span(spn)
            state["span"] = spn
        except Exception as e:
            print("on_new_span failed (will retry):", e, file=sys.stderr)


# ======================================================================== SERVICE (fetch + engine + hot-swap)
class MarginService:
    def __init__(self, symbols=None, deep_otm_pct=None, nov_price="file", interval_min=10.0, nse=None):
        self.symbols, self.deep_otm_pct, self.nov_price = symbols, deep_otm_pct, nov_price
        self.interval = interval_min
        self.engine = None                 # current MarginEngine (swapped atomically)
        self._span = self._elm = None      # latest file paths
        self._elm_ver = 0                  # bumped every time an ELM file arrives (same file name, new content)
        self._built_span, self._built_elm_ver = None, -1
        self._nse, self._state = nse, {}
        self._stop = threading.Event()
        self._ready = threading.Event()
        self._lock = threading.Lock()      # serialises builds only; margin() never takes it
        self.last_error = None
        self.stats = collections.Counter()
        self.universe = {}                 # see set_universe()
        self.excluded = {}                 # symbol -> reason: never priced (mapping/price audit failed)
        self.audit_report = []             # last audit problems (strings)

    # -- hooks called by cycle()
    def _on_span(self, p):
        self._span = p
        self._rebuild()

    def _on_elm(self, p):
        self._elm = p
        self._elm_ver += 1
        self._rebuild()

    def _rebuild(self):
        with self._lock:
            if not (self._span and self._elm):
                return
            span_new = self._built_span != self._span
            if not span_new and self._built_elm_ver == self._elm_ver:
                return
            if self.engine is not None and not span_new:
                eng = self.engine.with_elm(self._elm)                    # ELM-only change; may raise
            else:
                eng = MarginEngine(self._span, self._elm, self.symbols, self.deep_otm_pct, self.nov_price)  # may raise
            self.engine = eng              # single reference assignment = atomic swap
            self._built_span, self._built_elm_ver = self._span, self._elm_ver
            self._ready.set()
            print(f"{dt.datetime.now():%H:%M:%S} engine loaded: {self._span.name} + {self._elm.name}")
            if self.universe:
                self._audit_and_report()

    def load_files(self, span_path, elm_path):
        """Use files already on disk (no download)."""
        self._span, self._elm = Path(span_path), Path(elm_path)
        self._elm_ver += 1
        self._rebuild()

    def poll_once(self):
        if self._nse is None:
            self._nse = NSE()
        cycle(self._nse, self._state, self._on_span, self._on_elm)

    def _loop(self):
        while not self._stop.is_set():
            try:
                self.poll_once()
                self.last_error = None
            except Exception as e:         # keep serving the old engine
                self.last_error = e
                print("poll error:", e, file=sys.stderr)
            self._stop.wait(self.interval * 60)

    def start(self):
        threading.Thread(target=self._loop, daemon=True, name="margin-fetch").start()
        return self

    def stop(self):
        self._stop.set()

    def wait_ready(self, timeout=120):
        return self._ready.wait(timeout)

    # -- parity-basket helpers (used on every tick; must never raise)
    def basket_margin(self, symbol, direction, strike, lot, expiry, ce_px, pe_px, fut_px, spot=None):
        """SPAN+ELM (Rs) for ONE lot of the parity basket at the given execution prices, or None.
        direction CHEAP    = buy CE, sell PE, sell FUT
        direction EXPENSIVE= sell CE, buy PE, buy FUT
        expiry 'YYYYMMDD' is mandatory: 'nearest' would pick the expiring series. Never raises."""
        eng = self.engine
        if eng is None:
            self.stats["no_engine"] += 1
            return None
        if symbol in self.excluded:
            self.stats["excluded"] += 1
            return None
        s = 1 if direction == "CHEAP" else -1
        try:
            legs = [Leg(symbol, "C", s, lot, expiry, strike, ce_px),
                    Leg(symbol, "P", -s, lot, expiry, strike, pe_px),
                    Leg(symbol, "F", -s, lot, expiry, None, fut_px)]
            r = eng.margin(legs, {symbol: spot} if spot else None)
            self.stats["ok"] += 1
            return r["total"]
        except Exception as e:             # missing contract/symbol, bad numbers
            self.stats["error"] += 1
            if self.stats["error"] <= 20 or self.stats["error"] % 1000 == 0:
                print(f"margin error #{self.stats['error']} {symbol} {direction} {strike}: {e}", file=sys.stderr)
            return None

    def set_universe(self, universe):
        """universe: {symbol: {"expiry": "YYYYMMDD", "strikes": [rupees...], "spot_ref": float|0, "fut_ref": float|0}}
        taken from the SAME broker rows the strategy subscribes to. Audited against every SPAN/ELM load."""
        self.universe = dict(universe)

    def audit(self, universe=None, price_tol=0.15):
        """Exact-key check of every stock/strike the strategy can trade against the loaded SPAN+ELM.
        Returns problem strings and fills self.excluded (stocks that must not be priced at all):
        missing future/spot/ELM row, or SPAN price far from the broker's own price (split/bonus/wrong series).
        A missing single strike is only reported (that strike gets no signal)."""
        eng = self.engine
        if eng is None:
            return ["engine not loaded"]
        uni = self.universe if universe is None else universe
        problems, excluded = [], {}
        for sym, u in sorted(uni.items()):
            pe = str(int(u["expiry"]))
            fut = eng.fut.get((sym, pe))
            if fut is None:
                excluded[sym] = f"no future for expiry {pe} in SPAN"
            if sym not in eng.elm:
                excluded[sym] = "no row in ael (ELM) file"
            if sym not in eng.spot:
                excluded[sym] = "no spot price in SPAN"
            if sym not in excluded:
                for what, file_px, ref in (("spot", eng.spot.get(sym), u.get("spot_ref")),
                                           ("future", fut["price"] if fut else None, u.get("fut_ref"))):
                    if file_px and ref and ref > 0 and not (1 - price_tol) <= file_px / ref <= 1 + price_tol:
                        excluded[sym] = f"{what}: SPAN price {file_px:g} vs broker price {ref:g} (corporate action / wrong series?)"
                        break
            if sym in excluded:
                problems.append(f"{sym}: EXCLUDED - {excluded[sym]}")
                continue
            missing = [(k, cp) for k in u.get("strikes", ()) for cp in ("C", "P")
                       if (sym, pe, round(float(k), 2), cp) not in eng.opt]
            if missing:
                ks = sorted({k for k, _ in missing})
                problems.append(f"{sym}: {len(missing)} option(s) not in SPAN for expiry {pe}, strikes "
                                f"{[format(k, 'g') for k in ks[:6]]}{'...' if len(ks) > 6 else ''}")
        self.excluded = excluded
        self.audit_report = problems
        return problems

    def _audit_and_report(self):
        try:
            problems = self.audit()
            n = len(self.universe)
            print(f"{dt.datetime.now():%H:%M:%S} margin audit: {n - len(self.excluded)}/{n} stocks priceable, "
                  f"{len(self.excluded)} excluded, {len(problems)} problem line(s)")
            for p in problems[:25]:
                print("    -", p)
        except Exception as e:
            print("margin audit failed:", e, file=sys.stderr)

    def margin(self, legs, spot=None, today=None):
        eng = self.engine                  # grab once: a swap mid-call cannot mix two engines
        if eng is None:
            raise RuntimeError("margin engine not loaded yet (no SPAN+ELM files)")
        return eng.margin(legs, spot, today)
# ---- end of inlined margin_system.py ----
import logging
logging.basicConfig(level=logging.WARNING, format='%(asctime)s [%(name)s] %(levelname)s: %(message)s')


# =====================================================
# CONFIG
# =====================================================
IST = ZoneInfo("Asia/Kolkata")
TEST_DURATION_SECONDS = 14400  # 4 hours
STATS_INTERVAL = 15
HFT_LATENCY_MS = 50
OUTPUT_DIR = "bidask_output"

# Date-based subfolder: bidask_output_DDMMYYYY
_today = datetime.now(IST)
OUTPUT_DIR = os.path.join(OUTPUT_DIR, f"bidask_output_{_today.strftime('%d%m%Y')}")

# Contract month to trade, pinned to the December cycle. Leaving it as None keeps
# the old roll-to-nearest behaviour, which on an expiry day still picks the series
# that dies that evening. A name with no series on this date is dropped by the
# startup audit rather than silently traded on a different month.
TARGET_EXPIRY = "2026-12-29"

# Engine 1 (LTP windows + LTP ticks) is switched off for this run: the book is
# the only thing allowed to open a window. LTP prices are still computed and
# reported beside every book read.
LTP_ENGINE_ENABLED = False

SUB_DELAY_SEC = 0.1
LOG_FLUSH_INTERVAL = 0.5

# A subscribe call is one WebSocket message, so the SDK receives symbol lists,
# not per-symbol requests. Bulk subscriptions are sliced to this many symbols
# and the drain groups whole requests up to this cap before sending.
SUB_CHUNK_SIZE = 200
SUB_CONNECT_PAUSE_SEC = 0.2

# Parity engine config — identical to arrow_fno_demo.py
PARITY_THRESHOLD_RS = 1300          # LTP-engine diagnostics only (shadow/no-book counters). Engine 2 does NOT use it.
# ENGINE 2 GATE: open a window when (gross arb - entry charges) >= MARGIN_GATE_PCT x basket margin.
# Basket margin = SPAN + ELM of the 3-leg hedge at the book prices, from NSE's own files (margin_system).
MARGIN_GATE_PCT = 0.01
MARGIN_WAIT_SEC = 90                # start-up wait for the first SPAN+ELM load
MARGIN_REFRESH_MIN = 10             # how often to look for a newer SPAN / ELM file
PARITY_MAX_LEG_AGE_MS = 1000        # Staleness gate — all 4 legs must be < 1s old
PARITY_TICK_FLUSH_SEC = 5           # Flush buffered parity ticks to disk
PARITY_WINDOWS_FILE = "parity_windows.csv.gz"
PARITY_TICKS_FILE = "parity_ticks.csv.gz"

# New comparison artifacts (plain CSV, opens straight in Excel)
EXEC_WINDOWS_FILE = "exec_windows.csv"
EXEC_TICKS_FILE = "exec_ticks.csv"

# =====================================================
# ENTRY-SIDE TRANSACTION CHARGES
# =====================================================
# Counted at entry only, never at exit. Brokerage = 0.
# rate = fraction of turnover (price × lot).
#            side      STT        stamp       NSE exchange   SEBI
CHARGES = {
    "FUT": {"BUY":  dict(stt=0.0,     stamp=0.00002, exch=0.0000183, sebi=1e-7),
            "SELL": dict(stt=0.0005,  stamp=0.0,     exch=0.0000183, sebi=1e-7)},
    "CE":  {"BUY":  dict(stt=0.0,     stamp=0.00003, exch=0.0003553, sebi=1e-7),
            "SELL": dict(stt=0.0015,  stamp=0.0,     exch=0.0003553, sebi=1e-7)},
    "PE":  {"BUY":  dict(stt=0.0,     stamp=0.00003, exch=0.0003553, sebi=1e-7),
            "SELL": dict(stt=0.0015,  stamp=0.0,     exch=0.0003553, sebi=1e-7)},
}
GST = 0.18   # on (brokerage + exchange + SEBI), not on STT or stamp

def leg_charge(leg, side, price, lot):
    r = CHARGES[leg][side]; t = price * lot
    exch, sebi = t * r["exch"], t * r["sebi"]
    return t * r["stt"] + t * r["stamp"] + exch + sebi + GST * (exch + sebi)


def basket_entry_charges(direction, ce_bid, ce_ask, pe_bid, pe_ask, fut_bid, fut_ask, lot):
    """What crossing the three legs costs, at the prices the signal trades at.

    CHEAP buys the CE and sells PE + FUT; EXPENSIVE is the mirror. Every leg
    turns over price x lot, which is the size the basket order actually uses.
    """
    if direction == "CHEAP":
        return (leg_charge("CE", "BUY", ce_ask, lot)
                + leg_charge("PE", "SELL", pe_bid, lot)
                + leg_charge("FUT", "SELL", fut_bid, lot))
    return (leg_charge("CE", "SELL", ce_bid, lot)
            + leg_charge("PE", "BUY", pe_ask, lot)
            + leg_charge("FUT", "BUY", fut_ask, lot))


# =====================================================
# DISCORD PARTNER ALERTS
# =====================================================
# Webhooks live in the file, next to the rest of the config, so what runs is
# exactly what is here. An empty list switches alerts off completely.
DISCORD_WEBHOOKS = [
    "https://discord.com/api/webhooks/1574105926007398485/BrGJciw6IBwbiWKnusXoia2jBKfXC-d_YPdMezRXzkS_Rr6iufSDwP_bBT2fbm0HA6nP",
    "https://discord.com/api/webhooks/1574114417237299392/Sn7uS4fbtegH9ImWhm108e5B80Hrhq86bysKMU1ciSzZBqZIl38x0l1WyjWR7pqg58WJ",
]

# Measured on this account: one webhook accepts ~5 requests per 2 s and a 429
# DROPS the message, so pacing plus a resend on the other webhook is mandatory.
DISCORD_MIN_SPACING_SEC = 0.40      # 5 per 2 s per webhook
DISCORD_HTTP_TIMEOUT_SEC = 2.0
DISCORD_MAX_ATTEMPTS = 3
DISCORD_POLL_SEC = 0.005
DISCORD_DRAIN_SEC = 5.0

DISCORD_LEG_TEXT = {
    "CHEAP": "Call buy · Put sell · Fut sell",
    "EXPENSIVE": "Call sell · Put buy · Fut buy",
}

# ENGINE 2's own window record. Timestamps are engine 2's open/peak/close, not
# engine 1's — that is the point of the run. The ltp_* columns hold engine 1's
# numbers read at the SAME instants, so one row answers "what did LTP say when
# the book said this".
EXEC_WINDOW_COLUMNS = [
    "stock", "window_open_ist", "peak_time_ist", "window_close_ist",
    "atm_strike", "lot_size", "direction",
    "ce_bid", "ce_ask", "pe_bid", "pe_ask", "fut_bid", "fut_ask",
    "open_exec_profit_points", "open_exec_arb_rupees", "open_exec_charges_rupees",
    "peak_exec_profit_points", "peak_exec_arb_rupees",
    "ltp_ce", "ltp_pe", "ltp_fut", "ltp_parity_points",
    "ltp_arb_rupees", "ltp_arb_peak",
    "ce_qty", "pe_qty", "fut_qty", "tradable_lots",
    "leg_max_age_ms", "duration_sec", "basket_margin", "close_reason",
]

EXEC_TICK_COLUMNS = [
    "timestamp_ist", "stock", "direction",
    "ce_bid", "ce_ask", "pe_bid", "pe_ask", "fut_bid", "fut_ask",
    "exec_arb_rupees", "ltp_ce", "ltp_pe", "ltp_fut", "ltp_arb_rupees",
    "tradable_lots",
]

REQUIRED_EXEC_WINDOW_COLS = (
    "basket_margin", "close_reason", "open_exec_arb_rupees",
    "open_exec_charges_rupees",
    "peak_exec_arb_rupees", "ltp_arb_rupees", "tradable_lots",
)

# One source of truth for the windows header, shared by the writer and the
# stale-schema guard so they can never drift apart.
PARITY_WINDOW_COLUMNS = [
    "stock", "window_open_ist", "peak_time_ist", "window_close_ist",
    "spot_cmp", "fut_value", "ce_atm_value", "pe_atm_value",
    "atm_strike", "open_parity_points", "open_arb_rupees",
    "peak_parity_points", "peak_arb_rupees",
    "lot_size", "direction", "duration_sec", "leg_max_age_ms",
    "basket_margin", "close_reason",
]
REQUIRED_WINDOW_COLS = ("basket_margin", "close_reason")

# Console recorder
CONSOLE_LOG_FILE = "console_log.txt"
CONSOLE_FSYNC_SEC = 2.0             # flush every line, fsync every 2s

FNO_STOCKS = [
    # Nifty 50 constituents (verified 2026-11-05 from Wikipedia/NSE)
    "ADANIENT", "ADANIPORTS", "APOLLOHOSP", "ASIANPAINT", "AXISBANK",
    "BAJAJ-AUTO", "BAJFINANCE", "BAJAJFINSV", "BEL", "BHARTIARTL",
    "BSE", "CIPLA", "COALINDIA", "DRREDDY", "EICHERMOT",
    "ETERNAL", "GRASIM", "HCLTECH", "HDFCBANK", "HDFCLIFE",
    "HINDALCO", "HINDUNILVR", "ICICIBANK", "INDIGO", "INFY",
    "ITC", "JIOFIN", "JSWSTEEL", "KOTAKBANK", "LT",
    "M&M", "MARUTI", "MAXHEALTH", "NESTLEIND", "NTPC",
    "ONGC", "POWERGRID", "RELIANCE", "SBILIFE", "SHRIRAMFIN",
    "SBIN", "SUNPHARMA", "TCS", "TATACONSUM", "TATASTEEL",
    "TECHM", "TITAN", "TMPV", "TRENT", "ULTRACEMCO",

    # --- Remaining 166 F&O stocks (active: 216 x 4 = 864 of 1,024 subscriptions) ---
    "360ONE", "ABB", "ABCAPITAL", "ADANIENSOL", "ADANIGREEN",
    "ADANIPOWER", "ALKEM", "AMBER", "AMBUJACEM", "ANANDRATHI",
    "ANGELONE", "APLAPOLLO", "ASHOKLEY", "ASTRAL", "ATHERENERG",
    "AUBANK", "AUROPHARMA", "BANDHANBNK", "BANKBARODA", "BANKINDIA",
    "BDL", "BHARATFORG", "BHEL", "BIOCON", "BLUESTARCO",
    "BOSCHLTD", "BPCL", "BRITANNIA", "CAMS", "CANBK",
    "CDSL", "CGPOWER", "CHOLAFIN", "COCHINSHIP", "COFORGE",
    "COLPAL", "CONCOR", "COROMANDEL", "CROMPTON", "CUB",
    "CUMMINSIND", "DABUR", "DATAPATTNS", "DELHIVERY", "DIVISLAB",
    "DIXON", "DLF", "DMART", "ENRIN", "FEDERALBNK",
    "FORCEMOT", "FORTIS", "GAIL", "GLENMARK", "GMRAIRPORT",
    "GODFRYPHLP", "GODREJCP", "GODREJPROP", "GVT&D", "HAL",
    "HAVELLS", "HDFCAMC", "HEROMOTOCO", "HINDPETRO", "HINDZINC",
    "HYUNDAI", "ICICIGI", "ICICILIFE", "IDEA", "IDFCFIRSTB",
    "INDHOTEL", "INDIANB", "INDUSINDBK", "INDUSTOWER",
    "INOXWIND", "IOC", "IRFC", "JINDALSTEL",
    "JSWENERGY", "JUBLFOOD", "KALYANKJIL", "KARURVYSYA", "KAYNES",
    "KEI", "KFINTECH", "KPITTECH", "LAURUSLABS", "LICHSGFIN",
    "LICI", "LODHA", "LTF", "LTM", "LUPIN",
    "MAHABANK", "MANAPPURAM", "MANKIND", "MARICO", "MAZDOCK",
    "MCX", "MFSL", "MOTHERSON", "MOTILALOFS", "MPHASIS",
    "MUTHOOTFIN", "NAM-INDIA", "NATIONALUM", "NAUKRI", "NAVINFLUOR",
    "NBCC", "NHPC", "NMDC", "NYKAA", "OBEROIRLTY",
    "OFSS", "OIL", "PAGEIND", "PATANJALI", "PAYTM",
    "PERSISTENT", "PETRONET", "PFC", "PGEL", "PHOENIXLTD",
    "PIDILITIND", "PIIND", "PNB", "PNBHOUSING", "POLICYBZR",
    "POLYCAB", "POWERINDIA", "PREMIERENE", "PRESTIGE", "RADICO",
    "RBLBANK", "RECLTD", "RVNL", "SAGILITY", "SAIL",
    "SBICARD", "SHREECEM", "SIEMENS", "SOLARINDS", "SONACOMS",
    "SRF", "SUPREMEIND", "SUZLON", "SWIGGY", "SYRMA",
    "TATAELXSI", "TATAPOWER", "TIINDIA", "TORNTPHARM", "TVSMOTOR",
    "UJJIVANSFB", "UNIONBANK", "UNITDSPR", "UNOMINDA", "UPL",
    "VBL", "VEDL", "VMM", "VOLTAS", "WAAREEENER",
    "WIPRO", "YESBANK", "ZYDUSLIFE",
]

# Lot sizes for each stock (re-verified 2026-11-22 against Arrow's live master: the
# 29-Dec-2026 futures rows match these numbers exactly, and so do the 23-Nov-2026 rows,
# so the Nov -> Dec shift needs no value change. They must stay the NEAREST expiry's lot
# — the 25-Jan-2027 rows carry different lots and will need revisiting in January.
# IEX and IREDA are dropped: 23-Nov-2026 is their last listed series.)
LOT_SIZES = {
    # Nifty 50 constituents (active)
    "ADANIENT": 309, "ADANIPORTS": 475, "APOLLOHOSP": 125, "ASIANPAINT": 250,
    "AXISBANK": 625, "BAJAJ-AUTO": 75, "BAJFINANCE": 750, "BAJAJFINSV": 300,
    "BEL": 1425, "BHARTIARTL": 475, "BSE": 200, "CIPLA": 425,
    "COALINDIA": 1350, "DRREDDY": 625, "EICHERMOT": 100, "ETERNAL": 2425,
    "GRASIM": 250, "HCLTECH": 400, "HDFCBANK": 650, "HDFCLIFE": 1100,
    "HINDALCO": 700, "HINDUNILVR": 300, "ICICIBANK": 700, "INDIGO": 150,
    "INFY": 400, "ITC": 1725, "JIOFIN": 2350, "JSWSTEEL": 675,
    "KOTAKBANK": 2000, "LT": 175, "M&M": 200, "MARUTI": 50,
    "MAXHEALTH": 525, "NESTLEIND": 500, "NTPC": 1500, "ONGC": 2250,
    "POWERGRID": 1900, "RELIANCE": 500, "SBILIFE": 375, "SHRIRAMFIN": 825,
    "SBIN": 750, "SUNPHARMA": 350, "TCS": 225, "TATACONSUM": 550,
    "TATASTEEL": 2750, "TECHM": 600, "TITAN": 175, "TMPV": 1600,
    "TRENT": 225, "ULTRACEMCO": 50,

    # --- Remaining F&O stocks (active, matching FNO_STOCKS) ---
    "360ONE": 500, "ABB": 125, "ABCAPITAL": 1550, "ADANIENSOL": 675,
    "ADANIGREEN": 600, "ADANIPOWER": 3550, "ALKEM": 125, "AMBER": 100,
    "AMBUJACEM": 1200, "ANANDRATHI": 250, "ANGELONE": 2500, "APLAPOLLO": 350,
    "ASHOKLEY": 5000, "ASTRAL": 425, "ATHERENERG": 375, "AUBANK": 500,
    "AUROPHARMA": 550, "BANDHANBNK": 3600, "BANKBARODA": 2925, "BANKINDIA": 5200,
    "BDL": 425, "BHARATFORG": 500, "BHEL": 2625, "BIOCON": 2500,
    "BLUESTARCO": 325, "BOSCHLTD": 25, "BPCL": 1975, "BRITANNIA": 125,
    "CAMS": 825, "CANBK": 6750, "CDSL": 475, "CGPOWER": 850,
    "CHOLAFIN": 625, "COCHINSHIP": 400, "COFORGE": 475, "COLPAL": 275,
    "CONCOR": 1250, "COROMANDEL": 300, "CROMPTON": 2150, "CUB": 2325,
    "CUMMINSIND": 100, "DABUR": 1250, "DATAPATTNS": 125, "DELHIVERY": 2075,
    "DIVISLAB": 100, "DIXON": 50, "DLF": 950, "DMART": 150,
    "ENRIN": 175, "FEDERALBNK": 2500, "FORCEMOT": 25, "FORTIS": 775,
    "GAIL": 3550, "GLENMARK": 375, "GMRAIRPORT": 6975, "GODFRYPHLP": 275,
    "GODREJCP": 500, "GODREJPROP": 325, "GVT&D": 125, "HAL": 150,
    "HAVELLS": 500, "HDFCAMC": 300, "HEROMOTOCO": 150, "HINDPETRO": 2025,
    "HINDZINC": 1225, "HYUNDAI": 275, "ICICIGI": 325, "ICICILIFE": 925,
    "IDEA": 71475, "IDFCFIRSTB": 9275, "INDHOTEL": 1000,
    "INDIANB": 1000, "INDUSINDBK": 700, "INDUSTOWER": 1700, "INOXWIND": 6400,
    "IOC": 4875, "IRFC": 5425, "JINDALSTEL": 625,
    "JSWENERGY": 1075, "JUBLFOOD": 1250, "KALYANKJIL": 1350, "KARURVYSYA": 1550,
    "KAYNES": 150, "KEI": 175, "KFINTECH": 575, "KPITTECH": 775,
    "LAURUSLABS": 425, "LICHSGFIN": 1000, "LICI": 1400, "LODHA": 625,
    "LTF": 2250, "LTM": 150, "LUPIN": 425, "MAHABANK": 6500,
    "MANAPPURAM": 3000, "MANKIND": 250, "MARICO": 1200, "MAZDOCK": 225,
    "MCX": 225, "MFSL": 400, "MOTHERSON": 6150, "MOTILALOFS": 775,
    "MPHASIS": 275, "MUTHOOTFIN": 275, "NAM-INDIA": 625, "NATIONALUM": 1875,
    "NAUKRI": 550, "NAVINFLUOR": 75, "NBCC": 6500, "NHPC": 6950,
    "NMDC": 6750, "NYKAA": 3125, "OBEROIRLTY": 350, "OFSS": 50,
    "OIL": 1400, "PAGEIND": 20, "PATANJALI": 1075, "PAYTM": 725,
    "PERSISTENT": 125, "PETRONET": 1900, "PFC": 1300, "PGEL": 950,
    "PHOENIXLTD": 350, "PIDILITIND": 500, "PIIND": 175, "PNB": 8000,
    "PNBHOUSING": 650, "POLICYBZR": 350, "POLYCAB": 125, "POWERINDIA": 25,
    "PREMIERENE": 650, "PRESTIGE": 450, "RADICO": 150, "RBLBANK": 3175,
    "RECLTD": 1575, "RVNL": 1925, "SAGILITY": 12000, "SAIL": 4700,
    "SBICARD": 800, "SHREECEM": 25, "SIEMENS": 175, "SOLARINDS": 25,
    "SONACOMS": 1225, "SRF": 200, "SUPREMEIND": 175, "SUZLON": 12700,
    "SWIGGY": 1825, "SYRMA": 325, "TATAELXSI": 125, "TATAPOWER": 1450,
    "TIINDIA": 200, "TORNTPHARM": 125, "TVSMOTOR": 175, "UJJIVANSFB": 8000,
    "UNIONBANK": 4425, "UNITDSPR": 400, "UNOMINDA": 550, "UPL": 1355,
    "VBL": 1275, "VEDL": 1150, "VMM": 4850, "VOLTAS": 375,
    "WAAREEENER": 175, "WIPRO": 3000, "YESBANK": 31100, "ZYDUSLIFE": 450,
}


# =====================================================
# HELPERS
# =====================================================
def ist_text():
    return datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S")

def get_secret(name):
    try:
        from google.colab import userdata
        v = userdata.get(name)
        if v:
            return v
    except Exception:
        pass
    return os.getenv(name, "")

def tick_to_dict(tick):
    if isinstance(tick, dict):
        return dict(tick)
    keys = [
        "token", "ltp", "open", "high", "low", "close",
        "volume", "oi", "vwap", "ltq", "tbq", "tsq",
        "bid_px", "bid_size", "bid_ord",
        "ask_px", "ask_size", "ask_ord",
        "bids", "asks",
        "ts", "timestamp", "time", "ltt",
    ]
    out = {}
    for k in keys:
        try:
            if hasattr(tick, k):
                out[k] = getattr(tick, k)
        except Exception:
            pass
    return out

def parse_expiry_date(s):
    for fmt in ("%d-%b-%Y", "%d-%m-%Y", "%Y-%m-%d", "%d-%m-%y"):
        try:
            return datetime.strptime(s.strip(), fmt).date()
        except Exception:
            continue
    return None

def to_paise(rupees):
    return int(round(float(rupees) * 100))

def from_paise(paise):
    return paise / 100.0


# =====================================================
# CONSOLE RECORDER (realtime txt of all stdout/stderr)
# =====================================================
class ConsoleSink:
    """Append-only writer for the console log. Every line is flushed
    immediately and fsynced periodically, so a mid-run Ctrl+C or a killed
    process still leaves a complete, readable file."""

    def __init__(self, path):
        self.path = path
        self._file = open(path, "a", encoding="utf-8", errors="replace")
        self._lock = threading.Lock()
        self._last_fsync = 0.0

    def write(self, text):
        with self._lock:
            self._file.write(text)
            self._file.flush()
            now = time.time()
            if now - self._last_fsync >= CONSOLE_FSYNC_SEC:
                self._last_fsync = now
                os.fsync(self._file.fileno())

    def sync(self):
        with self._lock:
            try:
                self._file.flush()
                os.fsync(self._file.fileno())
            except Exception:
                pass


class ConsoleRecorder:
    """Tee: sink file first, console second — a terminal encoding error can
    therefore never cost us a line of the log.

    print() writes the text and the newline as two separate calls, so the log
    is buffered until a newline and then handed to the sink as one atomic
    chunk; otherwise concurrent lines glue together into garbage.
    """

    def __init__(self, stream, sink):
        self._stream = stream
        self._sink = sink
        self._buf = ""
        self._buf_lock = threading.Lock()

    def _emit(self, text):
        try:
            self._sink.write(text)
        except Exception:
            pass

    def write(self, text):
        try:
            with self._buf_lock:
                self._buf += text
                if "\n" in self._buf:
                    complete, self._buf = self._buf.rsplit("\n", 1)
                    chunk = complete + "\n"
                else:
                    chunk = None
        except Exception:
            chunk = None
        if chunk:
            self._emit(chunk)
        try:
            self._stream.write(text)
        except UnicodeEncodeError:
            try:
                self._stream.write(text.encode("ascii", "replace").decode("ascii"))
            except Exception:
                pass
        except Exception:
            pass
        return len(text)

    def writelines(self, lines):
        for line in lines:
            self.write(line)

    def flush(self):
        with self._buf_lock:
            pending, self._buf = self._buf, ""
        if pending:
            self._emit(pending)
        try:
            self._stream.flush()
        except Exception:
            pass

    def isatty(self):
        try:
            return self._stream.isatty()
        except Exception:
            return False

    def fileno(self):
        return self._stream.fileno()


os.makedirs(OUTPUT_DIR, exist_ok=True)
console_sink = ConsoleSink(os.path.join(OUTPUT_DIR, CONSOLE_LOG_FILE))
atexit.register(console_sink.sync)


def log_only(text):
    """Write to console_log.txt without printing to the screen — for high-volume
    per-event lines that matter for analysis but drown the live view."""
    console_sink.write(text + "\n")

for _name in ("stdout", "stderr"):
    _real = getattr(sys, _name)
    try:
        _real.reconfigure(errors="replace")  # Windows cp1252 must never raise
    except Exception:
        pass
    setattr(sys, _name, ConsoleRecorder(_real, console_sink))

try:
    # Route the logging module (pyarrow_client warnings) through the tee too.
    for _h in logging.root.handlers:
        _h.setStream(sys.stderr)
except Exception:
    pass

print("\n" + "=" * 70)
print(f"  RUN START {ist_text()} | duration={TEST_DURATION_SECONDS}s "
      f"| threshold=Rs{PARITY_THRESHOLD_RS}")
print(f"  Console log -> {os.path.abspath(console_sink.path)}")
print("=" * 70)


# =====================================================
# LOGIN (auto_login with credentials)
# =====================================================
APP_ID      = "5c999bfe87dc"
APP_SECRET  = "9f7b9f755b4a05228bb574e45fd27f19f6b2de81c21854eddfcf2577f99a91fb"
USER_ID     = "AG5406"
PASSWORD    = "njqDIL85@"
TOTP_SECRET = "XERJTQWV2637ZVV5EAUYB6TI5XIE3RYT"

client = ArrowClient(app_id=APP_ID)
login_result = client.auto_login(
    user_id=USER_ID,
    password=PASSWORD,
    app_secret=APP_SECRET,
    totp_secret=TOTP_SECRET,
)
TOKEN = client.get_token()
_last_login_mono = time.monotonic()
print(f"[{ist_text()}] Login OK: {login_result.get('name', '?')}")


def refresh_token():
    """Re-login to Arrow and refresh the token. Returns True on success."""
    global TOKEN, _last_login_mono, client
    try:
        login_result = client.auto_login(
            user_id=USER_ID,
            password=PASSWORD,
            app_secret=APP_SECRET,
            totp_secret=TOTP_SECRET,
        )
        TOKEN = client.get_token()
        _last_login_mono = time.monotonic()
        print(f"[{ist_text()}] Token refreshed: {login_result.get('name', '?')}")
        return True
    except Exception as exc:
        print(f"[{ist_text()}] Token refresh FAILED: {exc}")
        return False


# =====================================================
# LOAD INSTRUMENTS
# =====================================================
raw = client.get_instruments()
text = raw.decode() if isinstance(raw, bytes) else raw
instruments = list(csv.DictReader(io.StringIO(text)))
print(f"[{ist_text()}] Loaded {len(instruments)} instruments")


# =====================================================
# BUILD PER-STOCK DATA
# =====================================================
today = datetime.now(IST).date()

TARGET_EXPIRY_DATE = (datetime.strptime(TARGET_EXPIRY, "%Y-%m-%d").date()
                      if TARGET_EXPIRY else None)
if TARGET_EXPIRY_DATE is not None and TARGET_EXPIRY_DATE < today:
    raise SystemExit(f"TARGET_EXPIRY {TARGET_EXPIRY} is already past — set it to the "
                     f"live cycle or to None to take the nearest expiry")

# --- Collect raw option data: underlying -> (expiry_str, strike) -> {CE: info, PE: info}
raw_options = collections.defaultdict(lambda: collections.defaultdict(dict))
# --- Collect futures: underlying -> list of {token, symbol, expiry_str, expiry_date}
raw_futures = collections.defaultdict(list)
# --- Collect cash/spot: underlying -> {token, symbol, ltp}
raw_cash = {}

# --- Master lookups used by the startup audit (every row of our 216 symbols)
token_exch = {}   # token -> Exchange
token_lot = {}    # token -> master LotSize (NSE rows only)
ALLOWED_EXCHANGE = "NSE"

for row in instruments:
    underlying = str(row.get("Symbol", "")).strip()
    if underlying not in FNO_STOCKS:
        continue

    opt_type = str(row.get("OptionType", "")).strip().upper()
    expiry_str = str(row.get("Expiry", "")).strip()
    tsym = str(row.get("TradingSymbol", "")).strip()
    segment = str(row.get("Segment", "")).strip()

    try:
        token = int(float(row["Token"])) if row.get("Token") else None
    except Exception:
        token = None
    if not token:
        continue

    exch = str(row.get("Exchange", "")).strip().upper()
    token_exch[token] = exch
    if exch != ALLOWED_EXCHANGE:
        continue
    try:
        token_lot[token] = int(float(row.get("LotSize", 0) or 0))
    except Exception:
        pass

    # Cash / EQ segment (CM segment, Series "EQ")
    if segment == "CM" and row.get("Series", "").strip() == "EQ" and underlying not in raw_cash:
        ltp_raw = float(row.get("LastPrice", 0) or 0)
        raw_cash[underlying] = {"token": token, "symbol": tsym, "ltp_raw": ltp_raw}

    # Options
    if opt_type in ("CE", "PE") and expiry_str and row.get("StrikePrice"):
        try:
            strike = float(row["StrikePrice"])
        except Exception:
            continue
        if opt_type not in raw_options[underlying][(expiry_str, strike)]:
            raw_options[underlying][(expiry_str, strike)][opt_type] = {
                "token": token, "symbol": tsym, "strike": strike,
            }

    # Futures (TradingSymbol ends with 'F', OptionType 'XX')
    if tsym.upper().endswith("F") and opt_type == "XX" and expiry_str:
        expiry_date = parse_expiry_date(expiry_str)
        if expiry_date:
            ltp_raw = float(row.get("LastPrice", 0) or 0)
            raw_futures[underlying].append({
                "token": token, "symbol": tsym,
                "expiry_str": expiry_str, "expiry_date": expiry_date,
                "ltp_raw": ltp_raw,
            })

# --- Resolve per-stock: nearest expiry, valid strikes (both CE+PE), future
stocks = {}
option_tokens = {}
underlying_strikes_paise = {}

for underlying in FNO_STOCKS:
    if underlying not in raw_cash:
        continue
    if underlying not in raw_futures:
        continue

    cash = raw_cash[underlying]

    # Pinned expiry, otherwise the nearest live series
    fut_list = raw_futures[underlying]
    if TARGET_EXPIRY_DATE is None:
        future_expiries = sorted(set(f["expiry_date"] for f in fut_list if f["expiry_date"] >= today))
    elif any(f["expiry_date"] == TARGET_EXPIRY_DATE for f in fut_list):
        future_expiries = [TARGET_EXPIRY_DATE]
    else:
        future_expiries = []
    if not future_expiries:
        continue
    nearest_expiry = future_expiries[0]
    current_futs = [f for f in fut_list if f["expiry_date"] == nearest_expiry]
    if not current_futs:
        continue
    fut = current_futs[0]

    # Build valid strikes for nearest expiry (must have both CE and PE)
    opts = raw_options.get(underlying, {})
    valid_strikes = set()
    opt_lookup = {}
    nearest_expiry_str = fut["expiry_str"]

    for (expiry_str, strike), type_map in opts.items():
        if expiry_str != nearest_expiry_str:
            ed = parse_expiry_date(expiry_str)
            if ed != nearest_expiry:
                continue
        if "CE" in type_map and "PE" in type_map:
            strike_p = to_paise(type_map["CE"]["strike"])
            valid_strikes.add(strike_p)
            opt_lookup[(strike_p, "CE")] = type_map["CE"]
            opt_lookup[(strike_p, "PE")] = type_map["PE"]

    if len(valid_strikes) < 3:
        continue

    sorted_strikes = sorted(valid_strikes)
    underlying_strikes_paise[underlying] = sorted_strikes
    option_tokens[underlying] = opt_lookup

    # Initial ATM from cash LTP (or future LTP as fallback)
    spot_ltp_raw = cash["ltp_raw"]
    fut_ltp_raw = fut["ltp_raw"]
    ref_price_raw = spot_ltp_raw if spot_ltp_raw > 0 else fut_ltp_raw

    if ref_price_raw > 0:
        ref_paise = int(ref_price_raw)
        idx = bisect.bisect_right(sorted_strikes, ref_paise)
        if idx == 0:
            initial_atm = sorted_strikes[0]
        elif idx >= len(sorted_strikes):
            initial_atm = sorted_strikes[-1]
        else:
            lo = sorted_strikes[idx - 1]
            hi = sorted_strikes[idx]
            initial_atm = lo if (ref_paise - lo) <= (hi - ref_paise) else hi
    else:
        initial_atm = sorted_strikes[len(sorted_strikes) // 2]

    stocks[underlying] = {
        "spot_token": cash["token"],
        "spot_symbol": cash["symbol"],
        "future_token": fut["token"],
        "future_symbol": fut["symbol"],
        "future_expiry": nearest_expiry_str,
        "nearest_expiry": nearest_expiry,
        "initial_atm": initial_atm,
        "master_spot_ltp_raw": spot_ltp_raw,
        "master_fut_ltp_raw": fut_ltp_raw,
    }

resolved = sorted(stocks.keys())
print(f"\n[{ist_text()}] Found {len(resolved)} F&O stocks in master"
      f" | expiry in use = {sorted(set(s['future_expiry'] for s in stocks.values()))}"
      f" | pinned = {TARGET_EXPIRY if TARGET_EXPIRY else 'no (nearest)'}")
for u in resolved:
    s = stocks[u]
    n_strikes = len(underlying_strikes_paise[u])
    print(f"  {u:<16} fut={s['future_symbol']} ATM={from_paise(s['initial_atm']):g} strikes={n_strikes}")


# =====================================================
# WRITE STARTUP SNAPSHOT
# =====================================================
os.makedirs(OUTPUT_DIR, exist_ok=True)


def rotate_stale_schema_files():
    """If parity_windows.csv.gz exists with an outdated header, archive (rename) it
    so this run starts a fresh, schema-correct file. Never deletes data."""
    path = os.path.join(OUTPUT_DIR, PARITY_WINDOWS_FILE)
    if not os.path.exists(path):
        return
    try:
        with gzip.open(path, "rt") as f:
            header = f.readline().strip()
    except Exception:
        return
    cols = [c.strip() for c in header.split(",")]
    missing = [c for c in REQUIRED_WINDOW_COLS if c not in cols]
    if missing:
        stamp = datetime.now(IST).strftime("%Y%m%d_%H%M%S")
        archive = os.path.join(OUTPUT_DIR, f"parity_windows_pre_{stamp}.csv.gz")
        try:
            os.rename(path, archive)
            print(f"  [schema] archived stale-header parity file (missing {missing}) -> {os.path.basename(archive)}")
        except Exception as e:
            print(f"  [schema] WARNING could not rotate stale parity file: {e}")


rotate_stale_schema_files()


def rotate_stale_exec_files():
    """Same guard for exec_windows.csv so an old column layout can't mix rows."""
    path = os.path.join(OUTPUT_DIR, EXEC_WINDOWS_FILE)
    if not os.path.exists(path) or os.path.getsize(path) == 0:
        return
    try:
        with open(path, "r", newline="", encoding="utf-8") as f:
            header = f.readline().strip()
    except Exception:
        return
    cols = [c.strip() for c in header.split(",")]
    missing = [c for c in REQUIRED_EXEC_WINDOW_COLS if c not in cols]
    if missing:
        stamp = datetime.now(IST).strftime("%Y%m%d_%H%M%S")
        archive = os.path.join(OUTPUT_DIR, f"exec_windows_pre_{stamp}.csv")
        try:
            os.rename(path, archive)
            print(f"  [schema] archived stale-header exec file (missing {missing}) -> {os.path.basename(archive)}")
        except Exception as e:
            print(f"  [schema] WARNING could not rotate stale exec file: {e}")


rotate_stale_exec_files()

snapshot = {
    "timestamp": ist_text(),
    "mode": "PENDING",
    "n_stocks": len(resolved),
    "config": {
        "subscription_policy": "atm_only_4_legs_per_instrument",
        "sub_delay_sec": SUB_DELAY_SEC,
        "test_duration_sec": TEST_DURATION_SECONDS,
        "stats_interval_sec": STATS_INTERVAL,
    },
    "underlyings": {},
}

for u in resolved:
    s = stocks[u]
    strikes_p = underlying_strikes_paise[u]
    opts = option_tokens[u]
    opt_dict = {}
    for sp in strikes_p:
        ce_info = opts.get((sp, "CE"))
        pe_info = opts.get((sp, "PE"))
        if ce_info and pe_info:
            opt_dict[str(sp)] = {
                "CE": {"token": ce_info["token"], "symbol": ce_info["symbol"]},
                "PE": {"token": pe_info["token"], "symbol": pe_info["symbol"]},
            }
    snapshot["underlyings"][u] = {
        "expiry": s["future_expiry"],
        "expiry_date": str(s["nearest_expiry"]),
        "spot_token": s["spot_token"],
        "spot_symbol": s["spot_symbol"],
        "future_token": s["future_token"],
        "future_symbol": s["future_symbol"],
        "master_spot_ltp": s["master_spot_ltp_raw"],
        "master_fut_ltp": s["master_fut_ltp_raw"],
        "initial_atm_paise": s["initial_atm"],
        "strikes_paise": strikes_p,
        "n_strikes": len(strikes_p),
        "options": opt_dict,
    }

snap_path = os.path.join(OUTPUT_DIR, "startup_snapshot.json")
with open(snap_path, "w", encoding="utf-8") as f:
    json.dump(snapshot, f, indent=2, default=str)
print(f"\n[{ist_text()}] Startup snapshot -> {snap_path}")


# =====================================================
# STARTUP SELF-AUDIT — refuses to subscribe on any bad leg
# =====================================================
def strike_from_symbol(sym, opt_type):
    """Independent cross-check: the strike embedded in the TradingSymbol."""
    try:
        tail = sym.rsplit(opt_type[0], 1)[-1]
        return float(tail) if tail[:1].isdigit() or tail[:1] == "." else None
    except Exception:
        return None


audit_problems = []

missing_stocks = [u for u in FNO_STOCKS if u not in stocks]
if missing_stocks:
    audit_problems.append(
        f"NOT RESOLVED on NSE: {missing_stocks} ({len(missing_stocks)} of {len(FNO_STOCKS)} stocks dropped)")

for u in sorted(stocks):
    s = stocks[u]
    for leg, tok in (("spot", s["spot_token"]), ("future", s["future_token"])):
        ex = token_exch.get(tok)
        if ex != ALLOWED_EXCHANGE:
            audit_problems.append(f"{u} {leg} token {tok}: exchange={ex} (expected {ALLOWED_EXCHANGE})")
    ml = token_lot.get(s["future_token"], 0)
    if ml and LOT_SIZES.get(u) != ml:
        audit_problems.append(f"{u} lot_size: code={LOT_SIZES.get(u)} master(NSE,{s['future_expiry']})={ml}")

    for (strike_p, otype), info in option_tokens[u].items():
        tok = info["token"]
        ex = token_exch.get(tok)
        if ex != ALLOWED_EXCHANGE:
            audit_problems.append(f"{u} {otype} {from_paise(strike_p)} token {tok}: exchange={ex}")
        if to_paise(info["strike"]) != strike_p:
            audit_problems.append(f"{u} {otype}: map key {from_paise(strike_p)} != master strike {info['strike']}")
        sm = strike_from_symbol(info["symbol"], otype)
        if sm is not None and abs(sm - info["strike"]) > 1e-9:
            audit_problems.append(f"{u} {otype}: symbol '{info['symbol']}' strike {sm} != master {info['strike']}")
        ol = token_lot.get(tok, 0)
        if ol and ol != LOT_SIZES.get(u):
            audit_problems.append(f"{u} {otype} {from_paise(strike_p)}: master lot {ol} != code {LOT_SIZES.get(u)}")

    pairs = collections.defaultdict(dict)
    for (strike_p, otype), info in option_tokens[u].items():
        pairs[strike_p][otype] = info
    for strike_p, pm in pairs.items():
        if "CE" in pm and "PE" in pm and pm["CE"]["token"] == pm["PE"]["token"]:
            audit_problems.append(f"{u} strike {from_paise(strike_p)}: CE and PE share token {pm['CE']['token']}")

n_legs = sum(1 + 1 + len(option_tokens[u]) for u in stocks)
if audit_problems:
    print(f"\n[{ist_text()}] STARTUP AUDIT FAILED — {len(audit_problems)} problem(s):")
    for p in audit_problems[:40]:
        print(f"    ✗ {p}")
    if len(audit_problems) > 40:
        print(f"    ... {len(audit_problems) - 40} more")
    raise SystemExit("Refusing to subscribe: instrument master did not pass the audit.")

snapshot["audit"] = {
    "passed": True,
    "exchange": ALLOWED_EXCHANGE,
    "stocks": len(stocks),
    "checked_legs": n_legs,
    "fractional_strikes": sum(1 for u in stocks for (sp, _o), _i in option_tokens[u].items() if sp % 100),
}
with open(snap_path, "w", encoding="utf-8") as f:
    json.dump(snapshot, f, indent=2, default=str)
print(f"\n[{ist_text()}] STARTUP AUDIT PASSED: {len(stocks)}/{len(FNO_STOCKS)} stocks, "
      f"{n_legs} legs, all exchange={ALLOWED_EXCHANGE}, strikes exact, lots match master.")


# =====================================================
# QUOTE PROBE — python exec_parity_test.py probe
# Prices every ATM basket from the REST quote book instead from last traded
# price, and prints both numbers side by side. It never opens a window, never
# enqueues margin and never touches the stream: its only job is to show, in one
# shot, what the book is actually worth versus what LTP claims.
# =====================================================
def _probe_side(levels, best="max"):
    """Best ₹ price from a depth list, a scalar, or None.
    best="max" for the bid side, "min" for the ask side."""
    if isinstance(levels, list):
        px = []
        for l in levels:
            if isinstance(l, dict):
                for k in ("price", "bidPrice", "askPrice", "bid", "ask"):
                    if l.get(k) not in (None, "", 0):
                        px.append(float(l[k]))
                        break
        if not px:
            return None
        return max(px) if best == "max" else min(px)
    if isinstance(levels, dict):
        return _probe_side(list(levels.values()), best)
    if levels in (None, "", 0):
        return None
    try:
        return float(levels)
    except Exception:
        return None


def _probe_find(rec, *names):
    for n in names:
        if isinstance(rec, dict) and rec.get(n) not in (None, ""):
            return rec[n]
    return None


def _probe_triple(rec):
    """(ltp, best_bid, best_ask) in the record's own unit — run_quote_probe puts
    them in ₹ using the strike as the yardstick, because bid/ltp tells you
    nothing about scale when both legs share it."""
    raw_ltp = _probe_find(rec, "ltp", "lastPrice", "last", "ltpPrice")
    if raw_ltp is None:
        return None
    ltp = float(raw_ltp)
    bid = _probe_side(_probe_find(rec, "bids", "bid", "bidPrice", "buyPrice"), "max")
    ask = _probe_side(_probe_find(rec, "asks", "ask", "askPrice", "sellPrice"), "min")
    return ltp, bid, ask


def run_quote_probe():
    from pyarrow_client import QuoteMode, Exchange
    want, owner = [], []
    for u, info in stocks.items():
        if not (info.get("future_symbol") and info.get("ce_symbol") and info.get("pe_symbol")):
            continue
        for s in (info["future_symbol"], info["ce_symbol"], info["pe_symbol"]):
            want.append((s, Exchange.NFO))
            owner.append(u)
    print(f"\n[{ist_text()}] QUOTE PROBE: {len(want)} legs over {len(set(owner))} stocks")

    quotes = {}
    step = 30
    for i in range(0, len(want), step):
        chunk = want[i:i + step]
        try:
            data = client.get_quotes(QuoteMode.FULL, chunk)
        except Exception as e:
            print(f"    chunk {i // step}: FAILED {type(e).__name__}: {e}")
            continue
        if i == 0:
            first = data[0] if isinstance(data, list) and data else data
            print(f"    raw record shape -> {json.dumps(first, default=str)[:900]}")
        recs = data if isinstance(data, list) else [data]
        for idx, rec in enumerate(recs):
            sym = (rec.get("symbol") or rec.get("tradingSymbol")) if isinstance(rec, dict) else None
            if not sym and idx < len(chunk):
                sym = chunk[idx][0]
            quotes[sym] = rec
        time.sleep(0.35)

    print(f"\n  {'stock':12s} {'strike':>8s} {'CE ltp/bid/ask':>24s} {'PE ltp/bid/ask':>24s} "
          f"{'FUT ltp/bid/ask':>28s} {'LTP arb':>9s} {'BOOK arb':>9s}  dir")
    got, nodict, noparse = 0, [], []
    for u, info in stocks.items():
        fs, cs, ps = (info.get("future_symbol"), info.get("ce_symbol"), info.get("pe_symbol"))
        if not (fs and cs and ps):
            continue
        if not all(q in quotes for q in (fs, cs, ps)):
            nodict.append(u)
            continue
        t_f, t_c, t_p = _probe_triple(quotes[fs]), _probe_triple(quotes[cs]), _probe_triple(quotes[ps])
        if not (t_f and t_c and t_p):
            noparse.append(u)
            continue
        K = from_paise(info["atm"])
        lot = LOT_SIZES.get(u, 1)
        if None in (t_f[1], t_f[2], t_c[1], t_c[2], t_p[1], t_p[2]):
            print(f"  {u:12s} book missing on at least one leg -> CE{t_c} PE{t_p} FUT{t_f}")
            continue
        # The ATM future trades within a percent or two of the strike, so its
        # magnitude says whether this reply came in ₹ or in paise.
        scale = 100.0 if t_f[0] > 4.0 * K else 1.0
        t_f = (t_f[0] / scale, t_f[1] / scale, t_f[2] / scale)
        t_c = (t_c[0] / scale, t_c[1] / scale, t_c[2] / scale)
        t_p = (t_p[0] / scale, t_p[1] / scale, t_p[2] / scale)
        ltp_pts = t_c[0] - t_p[0] - t_f[0] + K
        cheap = t_p[1] + t_f[1] - t_c[2] - K
        exp = t_c[1] - t_p[2] - t_f[2] + K
        book_pts, d = (cheap, "CHEAP") if cheap >= exp else (exp, "EXPENSIVE")
        print(f"  {u:12s} {K:8.2f} {t_c[0]:7.2f}/{t_c[1]:7.2f}/{t_c[2]:7.2f}  "
              f"{t_p[0]:7.2f}/{t_p[1]:7.2f}/{t_p[2]:7.2f}  "
              f"{t_f[0]:9.2f}/{t_f[1]:8.2f}/{t_f[2]:8.2f}  "
              f"{abs(ltp_pts) * lot:8.0f} {book_pts * lot:9.0f}  {d}"
              f"{'  <== BOOK CLEARS 1300' if book_pts * lot >= PARITY_THRESHOLD_RS else ''}")
        got += 1
    print(f"\n  probe priced {got} of {len(stocks)} stocks. No window, no margin call, no stream started.")
    if nodict:
        print(f"  arrow returned no quote record for {len(nodict)}: {nodict[:8]}")
    if noparse:
        print(f"  quote came but no ltp field recognised for {len(noparse)}: {noparse[:8]}")


# =====================================================
# MODE SELECTION
# =====================================================
print("\n" + "=" * 55)
print("  ARROW FnO DATA COLLECTOR — DEMO (ALL FnO)")
print("=" * 55)
print("\n  Select stream mode:")
print("    1 = HFT stream (full depth, low latency)")
print("    2 = Normal stream (full depth)")
print("\n  Note: HFT must be enabled on your Arrow account.")
print("        Auto-selecting Normal mode (HFT is off on this account).\n")

choice = "2"
MODE = "NORMAL"
snapshot["mode"] = MODE
with open(snap_path, "w", encoding="utf-8") as f:
    json.dump(snapshot, f, indent=2, default=str)

print(f"\n  Mode        : {MODE}")
print(f"  Duration    : {TEST_DURATION_SECONDS // 60} minutes")
print(f"  Stocks      : {len(stocks)}")
print(f"  Instruments : ~{len(stocks) * 4} (spot + future + CE + PE each)")
print("=" * 55 + "\n")


# =====================================================
# ATM TRACKER
# =====================================================
class AtmTracker:
    """Per-underlying ATM tracker.

    Subscription policy: an instrument never holds more than its cash, future
    and the current ATM CE/PE pair. The incoming strike is subscribed on the
    tick it becomes ATM, and the outgoing strike is released on that same tick.
    """

    def __init__(self, underlying, sorted_strikes, initial_atm):
        self.underlying = underlying
        self.strikes = sorted_strikes
        self.current_atm = initial_atm

    def nearest(self, spot_paise):
        idx = bisect.bisect_right(self.strikes, spot_paise)
        if idx == 0:
            return self.strikes[0], 0
        if idx >= len(self.strikes):
            return self.strikes[-1], len(self.strikes) - 1
        lo = self.strikes[idx - 1]
        hi = self.strikes[idx]
        if spot_paise - lo <= hi - spot_paise:
            return lo, idx - 1
        return hi, idx

    def on_spot(self, spot_paise):
        new_atm, _ = self.nearest(spot_paise)
        if new_atm == self.current_atm:
            return []

        old_atm = self.current_atm
        self.current_atm = new_atm
        return [
            ("flip", old_atm, new_atm),
            ("subscribe_new", new_atm),
            ("unsubscribe_old", old_atm),
        ]


# =====================================================
# TRACKING STATE
# =====================================================
lock = threading.Lock()
tick_counts = collections.defaultdict(int)
spot_ltp_paise = {}
future_ltp_paise = {}
disconnect_count = 0
error_count = 0
error_log = []
spot_connected = False
main_connected = False

flip_count = 0
emergency_count = 0
unsub_count = 0
atm_events_log = []

spot_call_count = 0
spot_timings = []

token_to_stock = {}

n_subscribed = 0
live_sub_items = set()

LOG_Q = collections.deque()
SUB_Q = collections.deque()

stop_event = threading.Event()

# =====================================================
# PARITY ENGINE STATE
# =====================================================
parity_price_store = {}   # token -> {"ltp": float, "ts_mono": int}
parity_windows = {}       # stock -> window tracker dict
parity_tick_buffer = collections.deque()
parity_next_flush = 0.0
parity_window_count = 0
parity_tick_count = 0
parity_skip_stale = 0
parity_skip_missing = 0
parity_flip_close_count = 0

# =====================================================
# BID/ASK (EXEC) DEPTH COUNTERS
# =====================================================
depth_ok_count = {}      # token -> ticks that carried a usable best bid+ask
depth_bad_count = {}     # token -> ticks that arrived with no usable depth

# =====================================================
# ENGINE 2 STATE — bid/ask parity, its own windows and clocks
# =====================================================
exec_windows = {}        # stock -> engine 2 window tracker dict
exec_tick_buffer = collections.deque()
exec_window_count = 0
exec_tick_count = 0
exec_shadow_count = 0      # reads where LTP cleared Rs1300 and the book did not
exec_nomargin_count = 0    # positive net but no margin number (engine not ready / contract missing)
exec_nodepth_count = 0     # reads where LTP cleared Rs1300 with no book to price
exec_flip_close_count = 0
exec_windows_written = 0
exec_ticks_written = 0

# =====================================================
# MARGIN WORKER STATE (async basket margin at window-open)
# =====================================================
margin_request_q = queue.Queue()
margin_pending = {}          # wid -> {"orders", "closed", "row", "margin", "written"}
margin_lock = threading.Lock()
margin_stop = threading.Event()
csv_write_lock = threading.Lock()
margin_fetched_count = 0
margin_failed_count = 0
margin_seq = 0                 # makes every window id unique
MARGIN_WORKER_POLL_SEC = 0.005


def rebuild_token_map():
    token_to_stock.clear()
    for u, info in stocks.items():
        if info.get("spot_token"):
            token_to_stock[info["spot_token"]] = (u, "spot")
        token_to_stock[info["future_token"]] = (u, "future")
        if info.get("ce_token"):
            token_to_stock[info["ce_token"]] = (u, "ce")
        if info.get("pe_token"):
            token_to_stock[info["pe_token"]] = (u, "pe")


# Initialize ATM trackers and per-stock option state
trackers = {}
for u in resolved:
    s = stocks[u]
    atm_p = s["initial_atm"]
    trackers[u] = AtmTracker(u, underlying_strikes_paise[u], atm_p)

    opts = option_tokens[u]
    ce_info = opts.get((atm_p, "CE"))
    pe_info = opts.get((atm_p, "PE"))
    s["ce_token"] = ce_info["token"] if ce_info else None
    s["ce_symbol"] = ce_info["symbol"] if ce_info else None
    s["ce_strike"] = atm_p if ce_info else None
    s["pe_token"] = pe_info["token"] if pe_info else None
    s["pe_symbol"] = pe_info["symbol"] if pe_info else None
    s["pe_strike"] = atm_p if pe_info else None
    s["atm"] = atm_p
    parity_windows[u] = {
        "active": False, "open_time": None, "peak_time": None,
        "peak_parity_pts": 0.0, "peak_arb_rs": 0.0,
        "peak_snapshot": None, "direction": None,
        "margin_wid": None,
    }

# Remove stocks without both CE and PE at initial ATM
incomplete = [u for u in list(stocks.keys())
              if not stocks[u].get("ce_token") or not stocks[u].get("pe_token")]
for u in incomplete:
    del stocks[u]
    if u in trackers:
        del trackers[u]
resolved = sorted(stocks.keys())
if incomplete:
    print(f"[{ist_text()}] Filtered {len(incomplete)} incomplete stocks (missing CE/PE at initial ATM)")

rebuild_token_map()

# The probe needs ce_symbol / pe_symbol / atm, which the block above just set,
# so it runs here and exits before any stream, window or margin call exists.
if "probe" in sys.argv:
    run_quote_probe()
    sys.exit(0)


# =====================================================
# SUBSCRIPTION QUEUE WORKER
# =====================================================
def _sub_send(op, stream_type, symbols):
    """One subscribe/unsubscribe WebSocket message carrying a batch of symbols."""
    if stream_type == "hft":
        if op == "sub":
            streams.subscribe_hft_data("full", symbols, latency=HFT_LATENCY_MS)
        elif op == "unsub":
            streams.unsubscribe_hft_data("full", symbols)
    else:
        if op == "sub":
            streams.subscribe_market_data(DataMode.FULL, symbols)
        elif op == "unsub":
            streams.unsubscribe_market_data(DataMode.FULL, symbols)


def _sub_fail(op, status):
    """Record a rejected subscribe message so the run shows it instead of
    silently holding a hole."""
    global error_count
    with lock:
        error_count += 1
        error_log.append(f"{ist_text()} | SUB {op} | {status[:120]}")


def _sub_groups(batch):
    """Split a same-op run into chunks of whole requests within SUB_CHUNK_SIZE."""
    groups, cur, cur_n = [], [], 0
    for item in batch:
        n = len(item[2])
        if cur and cur_n + n > SUB_CHUNK_SIZE:
            groups.append(cur)
            cur, cur_n = [], 0
        cur.append(item)
        cur_n += n
    if cur:
        groups.append(cur)
    return groups


def _subscribe_chunked(stream_type, op, symbols):
    """Bulk connect-time subscription: a request this large cannot go in one
    message, so it is sliced by symbol instead of by whole request."""
    for i in range(0, len(symbols), SUB_CHUNK_SIZE):
        chunk = symbols[i:i + SUB_CHUNK_SIZE]
        try:
            _sub_send(op, stream_type, chunk)
        except Exception as e:
            _sub_fail(op, str(e))
        time.sleep(SUB_CONNECT_PAUSE_SEC)


def _dispatch_sub(op, stream_type, group, symbols):
    """Send one message for a batch of whole requests, then account for it.

    A batch succeeds or fails as a unit, so a rejected batch is replayed request
    by request: one bad symbol then costs that symbol alone instead of blinding
    every other stock riding on the same message.
    """
    global n_subscribed, error_count
    t_ack = time.time_ns()
    status = "OK"
    try:
        _sub_send(op, stream_type, symbols)
    except Exception as e:
        status = str(e)[:120]
        _sub_fail(op, status)
        if len(group) > 1:
            for item in group:
                item_ack = time.time_ns()
                item_status = "OK"
                try:
                    _sub_send(op, stream_type, item[2])
                except Exception as e2:
                    item_status = str(e2)[:120]
                    _sub_fail(op, item_status)
                else:
                    if op == "sub":
                        n_subscribed += len(item[2])
                        with lock:
                            live_sub_items.update(item[2])
                    elif op == "unsub":
                        n_subscribed -= len(item[2])
                        with lock:
                            live_sub_items.difference_update(item[2])
                LOG_Q.append(("sub", (
                    item[3]["t_request_ns"], op,
                    item[3].get("underlying", ""), item[3].get("strike", ""),
                    item_ack, item_status,
                )))
                time.sleep(SUB_DELAY_SEC)
            return
    else:
        if op == "sub":
            n_subscribed += len(symbols)
            with lock:
                live_sub_items.update(symbols)
        elif op == "unsub":
            n_subscribed -= len(symbols)
            with lock:
                live_sub_items.difference_update(symbols)

    for item in group:
        LOG_Q.append(("sub", (
            item[3]["t_request_ns"], op,
            item[3].get("underlying", ""), item[3].get("strike", ""),
            t_ack, status,
        )))


def sub_worker():
    """Adjacent same-op requests merge into one run and leave as whole-request
    chunks of at most SUB_CHUNK_SIZE symbols. SUB_DELAY_SEC paces messages, so a
    burst of ATM flips costs a few calls instead of one call per pair."""
    while not stop_event.is_set() or SUB_Q:
        if not SUB_Q:
            time.sleep(0.01)
            continue

        run = [SUB_Q.popleft()]
        op, stream_type = run[0][0], run[0][1]
        while SUB_Q and SUB_Q[0][0] == op and SUB_Q[0][1] == stream_type:
            run.append(SUB_Q.popleft())

        for group in _sub_groups(run):
            symbols = []
            for item in group:
                symbols.extend(item[2])
            _dispatch_sub(op, stream_type, group, symbols)
            time.sleep(SUB_DELAY_SEC)


def enqueue_sub(op, stream_type, symbols, underlying="", strike=0):
    SUB_Q.append((op, stream_type, symbols, {
        "t_request_ns": time.time_ns(),
        "underlying": underlying,
        "strike": strike,
    }))


# =====================================================
# LOG WRITER THREAD
# =====================================================
def log_writer():
    paths = {
        "atm": os.path.join(OUTPUT_DIR, "atm_events.csv.gz"),
        "sub": os.path.join(OUTPUT_DIR, "sub_events.csv.gz"),
        "health": os.path.join(OUTPUT_DIR, "health.csv.gz"),
    }
    files = {k: gzip.open(p, "at", newline="") for k, p in paths.items()}
    writers = {k: csv.writer(f) for k, f in files.items()}

    writers["atm"].writerow([
        "time_ns", "underlying", "expiry", "spot_paise",
        "old_strike", "new_strike", "new_pair_live", "via_bisect",
    ])
    writers["sub"].writerow([
        "t_request_ns", "op", "underlying", "strike", "t_ack_ns", "status",
    ])
    writers["health"].writerow([
        "time_ns", "n_subscribed", "queue_depth",
        "spot_p50_ns", "spot_p99_ns", "ws_reconnects", "errors",
    ])

    while not stop_event.is_set() or LOG_Q:
        while LOG_Q:
            try:
                kind, row = LOG_Q.popleft()
                if kind in writers:
                    writers[kind].writerow(row)
            except Exception:
                pass
        for f in files.values():
            try:
                f.flush()
            except Exception:
                pass
        # Flush parity tick buffer periodically
        if parity_tick_buffer and time.time() >= parity_next_flush:
            flush_parity_ticks()
        if exec_tick_buffer and time.time() >= parity_next_flush:
            flush_exec_ticks()
        time.sleep(LOG_FLUSH_INTERVAL)

    for f in files.values():
        try:
            f.close()
        except Exception:
            pass


# =====================================================
# PARITY ENGINE
# =====================================================
def best_bid_ask(tick_dict):
    """Pull the best bid and best ask (₹ + size) out of a FULL-mode tick dict.

    Arrow's depth levels are [{'price','quantity','orders'}, ...] with price in
    paise. Best is max(bids)/min(asks) rather than index 0, so the answer does
    not depend on how the exchange ordered the levels.
    Returns (bid_rs, ask_rs, bid_qty, ask_qty) or None when depth is absent.
    """
    if not tick_dict:
        return None
    bids = tick_dict.get("bids")
    asks = tick_dict.get("asks")
    if not bids or not asks:
        return None
    try:
        bp = [float(l["price"]) for l in bids if isinstance(l, dict) and l.get("price")]
        ap = [float(l["price"]) for l in asks if isinstance(l, dict) and l.get("price")]
        if not bp or not ap:
            return None
        bl = max(bids, key=lambda l: float(l["price"]))
        al = min(asks, key=lambda l: float(l["price"]))
        return (max(bp) / 100.0, min(ap) / 100.0,
                int(bl.get("quantity") or 0), int(al.get("quantity") or 0))
    except Exception:
        return None


def update_parity_price(token, ltp_raw, tick_dict=None):
    """Store latest tick price + best bid/ask with monotonic receive timestamp. Arrow sends all prices in paise."""
    ltp_rupees = ltp_raw / 100.0
    ts_wall = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
    quote = best_bid_ask(tick_dict)
    with lock:
        if quote:
            depth_ok_count[token] = depth_ok_count.get(token, 0) + 1
        else:
            depth_bad_count[token] = depth_bad_count.get(token, 0) + 1
    entry = {
        "ltp": ltp_rupees,
        "ts_mono": time.monotonic_ns(),
        "ts_wall": ts_wall,
        "bid": None, "ask": None, "bid_qty": 0, "ask_qty": 0,
    }
    if quote:
        entry["bid"], entry["ask"] = quote[0], quote[1]
        entry["bid_qty"], entry["ask_qty"] = quote[2], quote[3]
    parity_price_store[token] = entry
    info = token_to_stock.get(token)
    if info:
        underlying, inst_type = info
        if inst_type in ("ce", "pe", "future", "spot"):
            check_parity(underlying, ts_wall)


def check_parity(underlying, event_ts):
    """Calculate parity from atomic snapshot, enforce staleness gate, track windows.

    event_ts is the arrival time of the tick that triggered this evaluation, so
    window open/peak/close stamp the parity-crossing event itself rather than
    the spot leg's last tick.

    Both engines are fed from the same snapshot and the same staleness gate:
    engine 1 (LTP) drives update_parity_window, engine 2 (bid/ask) drives
    update_exec_window. Each keeps its own windows and its own file.
    """
    global parity_window_count, parity_tick_count, parity_skip_stale, parity_skip_missing

    info = stocks.get(underlying)
    if not info:
        return

    spot_token = info.get("spot_token")
    fut_token = info.get("future_token")
    ce_token = info.get("ce_token")
    pe_token = info.get("pe_token")

    if not all([spot_token, fut_token, ce_token, pe_token]):
        return

    # Atomic snapshot under lock
    with lock:
        spot_data = parity_price_store.get(spot_token)
        fut_data = parity_price_store.get(fut_token)
        ce_data = parity_price_store.get(ce_token)
        pe_data = parity_price_store.get(pe_token)

    # All 4 legs must have at least one tick
    if not all([spot_data, fut_data, ce_data, pe_data]):
        parity_skip_missing += 1
        return

    # Staleness gate — all 4 legs must be within PARITY_MAX_LEG_AGE_MS
    now_mono = time.monotonic_ns()
    max_age_ms = PARITY_MAX_LEG_AGE_MS
    ages = [
        (now_mono - d["ts_mono"]) / 1_000_000
        for d in [spot_data, fut_data, ce_data, pe_data]
    ]
    if any(a > max_age_ms for a in ages):
        parity_skip_stale += 1
        return

    # Extract prices (all in ₹)
    spot_px = spot_data["ltp"]
    fut_px = fut_data["ltp"]
    ce_px = ce_data["ltp"]
    pe_px = pe_data["ltp"]
    atm_strike = from_paise(info["atm"])
    lot_size = LOT_SIZES.get(underlying, 1)
    ts_wall = event_ts
    leg_max_age_ms = max(ages)

    # Real put-call parity: parity = C - P - F + K
    parity_pts = ce_px - pe_px - fut_px + atm_strike
    arb_rs = abs(parity_pts) * lot_size

    # --- ENGINE 2 input: both sides priced off the book, side you can trade ---
    exec_info = None
    depth_ok = bool(ce_data.get("bid") and ce_data.get("ask")
                    and pe_data.get("bid") and pe_data.get("ask")
                    and fut_data.get("bid") and fut_data.get("ask"))
    if depth_ok:
        ce_bid, ce_ask = ce_data["bid"], ce_data["ask"]
        pe_bid, pe_ask = pe_data["bid"], pe_data["ask"]
        fut_bid, fut_ask = fut_data["bid"], fut_data["ask"]
        # CHEAP trade: BUY CE at ask, SELL PE at bid, SELL FUT at bid
        cheap_pts = pe_bid + fut_bid - ce_ask - atm_strike
        # EXPENSIVE trade: SELL CE at bid, BUY PE at ask, BUY FUT at ask
        exp_pts = ce_bid - pe_ask - fut_ask + atm_strike
        if cheap_pts >= exp_pts:
            exec_pts = cheap_pts
            qtys = (ce_data["ask_qty"], pe_data["bid_qty"], fut_data["bid_qty"])
            direction = "CHEAP"
        else:
            exec_pts = exp_pts
            qtys = (ce_data["bid_qty"], pe_data["ask_qty"], fut_data["ask_qty"])
            direction = "EXPENSIVE"
        charges_rs = basket_entry_charges(direction, ce_bid, ce_ask,
                                          pe_bid, pe_ask, fut_bid, fut_ask, lot_size)
        gross_rs = exec_pts * lot_size
        net_rs = gross_rs - charges_rs
        if direction == "CHEAP":
            ce_x, pe_x, fut_x = ce_ask, pe_bid, fut_bid
        else:
            ce_x, pe_x, fut_x = ce_bid, pe_ask, fut_ask
        if net_rs <= 0:
            margin_rs, gate_rs = None, float("inf")      # cannot pass: skip the margin work
        else:
            margin_rs = margin_svc.basket_margin(
                underlying, direction, atm_strike, lot_size,
                info["nearest_expiry"].strftime("%Y%m%d"), ce_x, pe_x, fut_x, spot_px)
            gate_rs = MARGIN_GATE_PCT * margin_rs if margin_rs else None
            if not margin_rs:
                margin_rs = None
        exec_info = {
            "ce_bid": ce_bid, "ce_ask": ce_ask,
            "pe_bid": pe_bid, "pe_ask": pe_ask,
            "fut_bid": fut_bid, "fut_ask": fut_ask,
            "exec_pts": exec_pts,
            "exec_arb_rs": gross_rs,
            "exec_charges_rs": charges_rs,
            "exec_net_rs": net_rs,
            "margin_rs": margin_rs,
            "gate_rs": gate_rs,
            "direction": direction,
            "ce_qty": qtys[0], "pe_qty": qtys[1], "fut_qty": qtys[2],
            "tradable_lots": min(qtys) // lot_size if lot_size > 0 else 0,
        }

    update_parity_window(
        underlying, arb_rs, parity_pts, ts_wall,
        spot_px, fut_px, ce_px, pe_px, atm_strike, lot_size, leg_max_age_ms,
    )
    update_exec_window(
        underlying, exec_info, parity_pts, arb_rs, ts_wall,
        spot_px, fut_px, ce_px, pe_px, atm_strike, lot_size, leg_max_age_ms,
    )


def _now_ms_str():
    return datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]


# =====================================================
# DISCORD ALERTS
# =====================================================
# Entry alerts outrank exit alerts, so a busy exit queue can never delay a new
# signal. The engine only ever puts a job on a queue — the network work happens
# on its own thread, so Discord can never slow a tick down.
discord_entry_q = queue.Queue()
discord_exit_q = queue.Queue()
discord_stop = threading.Event()
discord_lock = threading.Lock()
discord_next_free = [0.0] * len(DISCORD_WEBHOOKS)
discord_stats = collections.Counter()


def _discord_margin_line(margin, arb_rs):
    try:
        m = float(margin)
    except (TypeError, ValueError):
        return "margin  pending"
    if m <= 0:
        return "margin  pending"
    return f"margin ₹{m:,.0f}  →  net {arb_rs / m * 100:.2f}%  (gate {MARGIN_GATE_PCT * 100:.2f}%)"


def _discord_held(duration_sec):
    try:
        s = max(0.0, float(duration_sec))
    except (TypeError, ValueError):
        return "held  n/a"
    return f"held {int(s // 60)}m {s % 60:06.3f}s"


def _discord_direction_label(direction):
    """Return (REVERSAL) for CHEAP, (CONVERSAL) for EXPENSIVE."""
    return "( REVERSAL )" if direction == "CHEAP" else "( CONVERSAL )" if direction == "EXPENSIVE" else ""


def enqueue_discord_open(underlying, direction, pts, arb_rs, strike, ts_wall,
                         charges_rs, margin_rs):
    """Called at window-OPEN. Never raises into the engine."""
    if not DISCORD_WEBHOOKS:
        return
    try:
        label = _discord_direction_label(direction)
        text = (f"OPEN  {direction}  {underlying}  {strike:g} {label}\n"
                f"{ts_wall}\n"
                f"{DISCORD_LEG_TEXT[direction]} ( {direction} )\n"
                f"arb {pts:.2f} pts  =  ₹{arb_rs:,.0f}  −  ₹{charges_rs:,.0f} chg"
                f"  =  ₹{arb_rs - charges_rs:,.0f} net\n"
                f"{_discord_margin_line(margin_rs, arb_rs - charges_rs)}")
        discord_entry_q.put({"kind": "open", "text": text,
                             "queued_mono": time.monotonic(),
                             "tag": underlying})
    except Exception as exc:
        discord_stats["enqueue_error"] += 1
        log_only(f"{ist_text()} | ALERT-ENQUEUE-ERROR | open {underlying} | {exc}")


def enqueue_discord_close(exec_row, basket_margin):
    """Called at the exact instant the window row goes to CSV."""
    if not DISCORD_WEBHOOKS or exec_row is None:
        return
    try:
        direction = exec_row.get("direction") or ""
        label = _discord_direction_label(direction)
        arb_rs = (float(exec_row.get("open_exec_arb_rupees") or 0)
                  - float(exec_row.get("open_exec_charges_rupees") or 0))      # net, as the gate sees it
        peak_arb = float(exec_row.get("peak_exec_arb_rupees") or 0)
        peak_net = peak_arb - float(exec_row.get("open_exec_charges_rupees") or 0)
        margin_val = float(basket_margin) if basket_margin else 0
        peak_line = ""
        if margin_val > 0 and peak_net > 0:
            peak_pct = peak_net / margin_val * 100
            peak_line = f"peak ₹{peak_net:,.0f} → {peak_pct:.2f}%\n"
        text = (f"CLOSE  {direction}  {exec_row.get('stock', '')} {label}\n"
                f"{exec_row.get('window_close_ist', '')}\n"
                f"{_discord_held(exec_row.get('duration_sec'))}   (close - open)\n"
                f"{peak_line}"
                f"{_discord_margin_line(basket_margin, arb_rs)}")
        discord_exit_q.put({"kind": "close", "text": text,
                            "queued_mono": time.monotonic(),
                            "tag": exec_row.get("stock", "")})
    except Exception as exc:
        discord_stats["enqueue_error"] += 1
        log_only(f"{ist_text()} | ALERT-ENQUEUE-ERROR | close | {exc}")


def _discord_pick():
    """The webhook whose next-allowed slot comes up soonest."""
    with discord_lock:
        now = time.monotonic()
        idx = min(range(len(discord_next_free)), key=lambda i: discord_next_free[i])
        return idx, max(now, discord_next_free[idx])


def _discord_reserve(idx, next_free):
    with discord_lock:
        discord_next_free[idx] = next_free


def _discord_post(url, content):
    """One webhook POST. Returns (http_code, retry_after_sec); code 0 = no answer."""
    body = json.dumps({"content": content}).encode("utf-8")
    req = urllib.request.Request(
        f"{url}?wait=true", data=body, method="POST",
        headers={"Content-Type": "application/json",
                 "User-Agent": "bidask-parity-alerts"})
    try:
        with urllib.request.urlopen(req, timeout=DISCORD_HTTP_TIMEOUT_SEC) as resp:
            return resp.status, 0.0
    except urllib.error.HTTPError as exc:
        retry_after = 0.0
        try:
            retry_after = float(json.loads(
                exc.read().decode("utf-8", "replace")).get("retry_after") or 0)
        except Exception:
            pass
        return exc.code, retry_after
    except Exception:
        return 0, 0.0


def _discord_deliver(job):
    text = job["text"]

    for attempt in range(1, DISCORD_MAX_ATTEMPTS + 1):
        idx, when = _discord_pick()
        delay = when - time.monotonic()
        if delay > 0:
            time.sleep(delay)
        sent_at = time.monotonic()
        code, retry_after = _discord_post(DISCORD_WEBHOOKS[idx], text)
        if code in (200, 204):
            _discord_reserve(idx, sent_at + DISCORD_MIN_SPACING_SEC)
            discord_stats["sent"] += 1
            log_only(f"{ist_text()} | ALERT OK | {job['kind']} {job['tag']} "
                     f"| wh={idx + 1} try={attempt} "
                     f"| total={int((sent_at - job['queued_mono']) * 1000)}ms")
            return True
        if code == 429:
            _discord_reserve(idx, time.monotonic() + max(retry_after, DISCORD_MIN_SPACING_SEC))
        else:
            _discord_reserve(idx, time.monotonic() + DISCORD_MIN_SPACING_SEC)
        log_only(f"{ist_text()} | ALERT RETRY | {job['kind']} {job['tag']} "
                 f"| wh={idx + 1} try={attempt} code={code} retry_after={retry_after}")

    discord_stats["dropped"] += 1
    print(f"  [{ist_text()}] ⚠ ALERT DROPPED after {DISCORD_MAX_ATTEMPTS} tries: "
          f"{job['kind']} {job['tag']}")
    log_only(f"{ist_text()} | ALERT DROPPED | {job['kind']} {job['tag']} | {text}")
    return False


def _discord_next_job():
    for q in (discord_entry_q, discord_exit_q):
        try:
            return q.get_nowait()
        except queue.Empty:
            continue
    return None


def discord_alert_worker():
    while True:
        job = _discord_next_job()
        if job is None:
            if discord_stop.is_set() and discord_entry_q.empty() and discord_exit_q.empty():
                return
            time.sleep(DISCORD_POLL_SEC)
            continue
        try:
            _discord_deliver(job)
        except Exception as exc:
            discord_stats["worker_error"] += 1
            log_only(f"{ist_text()} | ALERT-WORKER-ERROR | {exc}")


def start_discord_alerts():
    if not DISCORD_WEBHOOKS:
        print(f"[{ist_text()}] Discord alerts: OFF (no webhooks in config)")
        return None
    cap = len(DISCORD_WEBHOOKS) * (2.0 / DISCORD_MIN_SPACING_SEC)
    print(f"[{ist_text()}] Discord alerts: {len(DISCORD_WEBHOOKS)} webhooks, "
          f"{cap:.0f} msg/2s capacity")
    t = threading.Thread(target=discord_alert_worker, daemon=True, name="discord-alerts")
    t.start()
    return t


def drain_discord_alerts():
    discord_stop.set()
    deadline = time.time() + DISCORD_DRAIN_SEC
    while time.time() < deadline:
        if discord_entry_q.empty() and discord_exit_q.empty():
            break
        time.sleep(0.1)
    print(f"[{ist_text()}] Discord alerts: sent={discord_stats['sent']} "
          f"dropped={discord_stats['dropped']} "
          f"errors={discord_stats['enqueue_error'] + discord_stats['worker_error']}")


def _finalize_window(underlying, w, close_time, reason):
    """Close an active ENGINE 1 window and route its row to disk.

    Shared by the normal threshold-close and the ATM-flip close so both use the
    same margin-handoff path. The row is written when BOTH the close event and
    the basket-margin reply have landed; whichever arrives last does the write.
    For reason="ATM_FLIP" the duration is a LOWER bound (the window was killed
    mid-life, not observed to decay).
    """
    global parity_flip_close_count

    snap = w.get("peak_snapshot")
    if snap is None:
        w["active"] = False
        w["margin_wid"] = None
        return False

    open_parity_pts = w.get("open_parity_pts", w["peak_parity_pts"])
    open_arb_rs = w.get("open_arb_rs", w["peak_arb_rs"])

    row = (
        underlying, w["open_time"], w["peak_time"], close_time,
        snap["spot"], snap["fut"], snap["ce"], snap["pe"],
        snap["strike"], open_parity_pts, open_arb_rs,
        w["peak_parity_pts"], w["peak_arb_rs"],
        snap["lot_size"], w["direction"], snap["leg_max_age_ms"],
    )

    wid = w.get("margin_wid")
    if wid is not None:
        with margin_lock:
            e = margin_pending.get(wid)
            if e is not None:
                # Keep the entry alive: a margin reply still in flight will
                # land in THIS row instead of being discarded.
                e["row"] = row
                e["reason"] = reason
                e["closed"] = True
                try_finalize_locked(wid)
            else:
                write_parity_window_row(*row, "RACE", reason)
    else:
        write_parity_window_row(*row, "NO_MARGIN", reason)

    if reason == "ATM_FLIP":
        parity_flip_close_count += 1

    w["active"] = False
    w["peak_snapshot"] = None
    w["margin_wid"] = None
    return True


def update_parity_window(underlying, arb_rs, parity_pts, ts_wall,
                         spot_px, fut_px, ce_px, pe_px, atm_strike, lot_size, leg_max_age_ms):
    """ENGINE 1 — track window open/peak/close on LTP.

    Byte-for-byte the behaviour of arrow_fno_demo.py: same gate, same state
    machine, same file. Never runs in this build (LTP_ENGINE_ENABLED=False):
    engine 1's state, tick buffer and both .csv.gz files stay untouched, so no
    engine-1 file is ever created.
    """
    global parity_window_count, parity_tick_count

    if not LTP_ENGINE_ENABLED:
        return

    if underlying not in parity_windows:
        parity_windows[underlying] = {
            "active": False,
            "open_time": None,
            "peak_time": None,
            "open_parity_pts": 0.0,
            "open_arb_rs": 0.0,
            "peak_parity_pts": 0.0,
            "peak_arb_rs": 0.0,
            "peak_snapshot": None,
            "direction": None,
            "margin_wid": None,
        }

    w = parity_windows[underlying]
    above = arb_rs >= PARITY_THRESHOLD_RS

    if above and not w["active"]:
        # Window OPEN
        w["active"] = True
        w["open_time"] = ts_wall
        w["peak_time"] = ts_wall
        w["open_parity_pts"] = parity_pts
        w["open_arb_rs"] = arb_rs
        w["peak_parity_pts"] = parity_pts
        w["peak_arb_rs"] = arb_rs
        w["direction"] = "EXPENSIVE" if parity_pts > 0 else "CHEAP"
        w["peak_snapshot"] = {
            "spot": spot_px, "fut": fut_px, "ce": ce_px, "pe": pe_px,
            "strike": atm_strike, "lot_size": lot_size, "leg_max_age_ms": leg_max_age_ms,
        }
        # Enqueue async basket-margin request using OPEN-time symbol + price snapshot.
        # Frozen forever against later ATM flips — the margin belongs to THIS strike.
        w["margin_wid"] = enqueue_margin_request(
            underlying, ts_wall, w["direction"], lot_size,
            fut_px, ce_px, pe_px, atm_strike,
        )
        parity_window_count += 1
        print(f"  [{ist_text()}] LTP OPEN: {underlying} arb=₹{arb_rs:.0f} "
              f"parity={parity_pts:+.2f} dir={w['direction']}")

    elif above and w["active"]:
        # Window ongoing — check for new peak
        if arb_rs > w["peak_arb_rs"]:
            w["peak_time"] = ts_wall
            w["peak_parity_pts"] = parity_pts
            w["peak_arb_rs"] = arb_rs
            w["peak_snapshot"] = {
                "spot": spot_px, "fut": fut_px, "ce": ce_px, "pe": pe_px,
                "strike": atm_strike, "lot_size": lot_size, "leg_max_age_ms": leg_max_age_ms,
            }

    if above:
        # Log every tick above threshold to tick buffer
        parity_tick_count += 1
        parity_tick_buffer.append([
            ts_wall, underlying, spot_px, fut_px, ce_px, pe_px,
            atm_strike, f"{parity_pts:+.2f}", f"{arb_rs:.0f}",
            lot_size, f"{leg_max_age_ms:.0f}",
        ])

    elif not above and w["active"]:
        # Window CLOSE — write only once margin has also landed.
        _finalize_window(underlying, w, ts_wall, "NORMAL")
        print(f"  [{ist_text()}] LTP CLOSE: {underlying} peak=₹{w['peak_arb_rs']:.0f} "
              f"parity={w['peak_parity_pts']:+.2f} dir={w['direction']} "
              f"open={w['open_time']} close={ts_wall}")


def update_exec_window(underlying, exec_info, parity_pts, arb_rs, ts_wall,
                       spot_px, fut_px, ce_px, pe_px, atm_strike, lot_size, leg_max_age_ms):
    """ENGINE 2 — the same state machine driven by bid/ask prices only.

    Opens when net-of-entry-charges profit reaches MARGIN_GATE_PCT of the basket margin
    (SPAN+ELM), so a spread that eats the opportunity means no window here at all. Keeps its own peak,
    its own clock, its own margin basket and its own file.
    """
    global exec_window_count, exec_tick_count, exec_shadow_count, exec_nodepth_count, exec_nomargin_count

    if underlying not in exec_windows:
        exec_windows[underlying] = {
            "active": False,
            "open_time": None,
            "peak_time": None,
            "open_exec_pts": 0.0,
            "open_exec_arb_rs": 0.0,
            "open_exec_charges_rs": 0.0,
            "open_margin_rs": None,
            "peak_exec_pts": 0.0,
            "peak_exec_arb_rs": 0.0,
            "peak_snapshot": None,
            "open_snapshot": None,
            "direction": None,
        }

    w = exec_windows[underlying]
    # No book on this tick -> nothing to gate on; an open window simply holds.
    # gated = this read has a real margin-based verdict. No margin number -> no verdict:
    # no new window, and an open window holds (silence is not evidence the spread ended).
    gated = exec_info is not None and exec_info.get("gate_rs") is not None
    above = gated and exec_info["exec_net_rs"] >= exec_info["gate_rs"]
    if exec_info is not None and not gated:
        exec_nomargin_count += 1

    if exec_info is None and arb_rs >= PARITY_THRESHOLD_RS:
        # Engine 1 saw a signal on this read but engine 2 had no book to price it
        # with. Counted separately so a zero can never be mistaken for silence.
        exec_nodepth_count += 1

    if above and not w["active"]:
        w["active"] = True
        w["open_time"] = ts_wall
        w["peak_time"] = ts_wall
        w["open_exec_pts"] = exec_info["exec_pts"]
        w["open_exec_arb_rs"] = exec_info["exec_arb_rs"]
        w["open_exec_charges_rs"] = exec_info["exec_charges_rs"]
        w["open_margin_rs"] = exec_info.get("margin_rs")
        w["peak_exec_pts"] = exec_info["exec_pts"]
        w["peak_exec_arb_rs"] = exec_info["exec_arb_rs"]
        w["direction"] = exec_info["direction"]
        w["peak_snapshot"] = _exec_snapshot(exec_info, spot_px, fut_px, ce_px, pe_px,
                                            atm_strike, lot_size, leg_max_age_ms,
                                            parity_pts, arb_rs)
        w["open_snapshot"] = w["peak_snapshot"]
        exec_window_count += 1
        enqueue_discord_open(underlying, w["direction"], exec_info["exec_pts"],
                             exec_info["exec_arb_rs"], atm_strike, ts_wall,
                             exec_info["exec_charges_rs"], exec_info.get("margin_rs"))
        print(f"  [{ist_text()}] BIDASK OPEN: {underlying} arb=₹{exec_info['exec_arb_rs']:.0f} "
              f"chg=₹{exec_info['exec_charges_rs']:.0f} "
              f"net=₹{exec_info['exec_net_rs']:.0f} "
              f"pts={exec_info['exec_pts']:+.2f} dir={w['direction']} "
              f"margin=₹{exec_info.get('margin_rs', 0):,.0f} "
              f"(ltp said ₹{arb_rs:.0f})")

    elif above and w["active"]:
        if exec_info["exec_arb_rs"] > w["peak_exec_arb_rs"]:
            w["peak_time"] = ts_wall
            w["peak_exec_pts"] = exec_info["exec_pts"]
            w["peak_exec_arb_rs"] = exec_info["exec_arb_rs"]
            w["peak_snapshot"] = _exec_snapshot(exec_info, spot_px, fut_px, ce_px, pe_px,
                                                atm_strike, lot_size, leg_max_age_ms,
                                                parity_pts, arb_rs)

    if above:
        exec_tick_count += 1
        exec_tick_buffer.append(build_exec_tick_row(ts_wall, underlying, w["direction"],
                                                    exec_info, ce_px, pe_px, fut_px, arb_rs))

    elif gated and not above and w["active"]:
        # Only a real book reading with a margin verdict can close this engine — a tick with no depth
        # is silence, not evidence that the opportunity ended.
        _finalize_exec_window(underlying, w, ts_wall, "NORMAL")
        print(f"  [{ist_text()}] BIDASK CLOSE: {underlying} peak=₹{w['peak_exec_arb_rs']:.0f} "
              f"pts={w['peak_exec_pts']:+.2f} dir={w['direction']} "
              f"open={w['open_time']} close={ts_wall}")

    elif gated and arb_rs >= PARITY_THRESHOLD_RS:
        # Engine 1 (LTP) says trade, engine 2 (book) says no. Same snapshot, same
        # 1000 ms gate, so the whole difference is in these six quotes — record
        # them. Engine 2's own decision and window state are untouched.
        exec_shadow_count += 1
        exec_tick_buffer.append(build_exec_tick_row(ts_wall, underlying, exec_info["direction"],
                                                    exec_info, ce_px, pe_px, fut_px, arb_rs))


def _exec_snapshot(exec_info, spot_px, fut_px, ce_px, pe_px, atm_strike, lot_size,
                   leg_max_age_ms, parity_pts, arb_rs):
    """Freeze everything one ENGINE 2 row needs, including engine 1's numbers at
    the same instant so the two engines are comparable without a second file."""
    return {
        "ce_bid": exec_info["ce_bid"], "ce_ask": exec_info["ce_ask"],
        "pe_bid": exec_info["pe_bid"], "pe_ask": exec_info["pe_ask"],
        "fut_bid": exec_info["fut_bid"], "fut_ask": exec_info["fut_ask"],
        "ce_qty": exec_info["ce_qty"], "pe_qty": exec_info["pe_qty"],
        "fut_qty": exec_info["fut_qty"], "tradable_lots": exec_info["tradable_lots"],
        "spot": spot_px, "fut": fut_px, "ce": ce_px, "pe": pe_px,
        "parity_pts": parity_pts, "arb_rs": arb_rs,
        "strike": atm_strike, "lot_size": lot_size, "leg_max_age_ms": leg_max_age_ms,
    }


def _finalize_exec_window(underlying, w, close_time, reason):
    """Close an active ENGINE 2 window and write its row to disk immediately."""
    global exec_flip_close_count

    snap = w.get("peak_snapshot")
    if snap is None:
        w["active"] = False
        return False

    row = _build_exec_row(underlying, w, close_time, snap)
    margin_rs = w.get("open_margin_rs")
    margin_str = f"{margin_rs:.2f}" if margin_rs else "PENDING"
    write_exec_window_row(row, margin_str, reason)

    if reason == "ATM_FLIP":
        exec_flip_close_count += 1

    w["active"] = False
    w["peak_snapshot"] = None
    w["open_snapshot"] = None
    return True


def enqueue_margin_request(underlying, open_time, direction, lot_size,
                           fut_px, ce_px, pe_px, atm_strike=0.0):
    """ENGINE 1: build the 3-leg basket at LTP prices and queue it for the worker.

    Direction → transactionType mapping:
      CHEAP  (parity<0, synthetic cheap): BUY CE + SELL PE + SELL FUT
      EXPENSIVE (parity>0, synthetic rich): SELL CE + BUY PE + BUY FUT
    Returns the pending-entry id on success, None on failure.
    """
    global margin_seq

    legs = _basket_legs(underlying, direction)
    if legs is None:
        return None
    fut_sym, ce_sym, pe_sym, ce_txn, pe_txn, fut_txn = legs

    orders = [
        _mk_order(ce_sym, ce_txn, lot_size, ce_px),
        _mk_order(pe_sym, pe_txn, lot_size, pe_px),
        _mk_order(fut_sym, fut_txn, lot_size, fut_px),
    ]

    margin_seq += 1
    wid = (underlying, open_time, margin_seq)
    with margin_lock:
        margin_pending[wid] = {
            "orders": orders, "closed": False,
            "row": None, "margin": None, "written": False, "reason": None,
        }
    margin_request_q.put(wid)
    return wid


def _basket_legs(underlying, direction):
    """Symbols + transaction sides for the 3-leg basket, or None if incomplete."""
    info = stocks.get(underlying)
    if not info:
        return None
    fut_sym = info.get("future_symbol")
    ce_sym = info.get("ce_symbol")
    pe_sym = info.get("pe_symbol")
    if not (fut_sym and ce_sym and pe_sym):
        return None
    if direction == "CHEAP":
        ce_txn, pe_txn, fut_txn = "B", "S", "S"
    else:
        ce_txn, pe_txn, fut_txn = "S", "B", "B"
    return fut_sym, ce_sym, pe_sym, ce_txn, pe_txn, fut_txn


def _mk_order(symbol, txn, lot_size, price):
    return {"exchange": "NFO", "symbol": symbol,
            "quantity": str(lot_size), "product": "M", "order": "LMT",
            "transactionType": txn, "price": f"{price:.2f}"}


def try_finalize_locked(wid):
    """Called under margin_lock. ENGINE 1 row written when close + margin ready."""
    e = margin_pending.get(wid)
    if e is None or e["written"]:
        return
    if not (e["closed"] and e["row"] is not None and e["margin"] is not None):
        return
    write_parity_window_row(*e["row"], e["margin"], e["reason"] or "NORMAL")
    e["written"] = True
    margin_pending.pop(wid, None)


def _margin_call(orders, stock, label):
    """One serial basket-margin REST call. Returns (value_string, ok)."""
    try:
        resp = client.basket_margin(orders=orders, include_positions=False)
        final = resp.get("final_margin") if isinstance(resp, dict) else None
        if final is None:
            return "NO_MARGIN", False
        return f"{float(final):.2f}", True
    except Exception as exc:
        safe = str(exc).encode("ascii", "replace").decode()[:180]
        print(f"  [{ist_text()}] MARGIN ERROR{label} {stock}: {safe}")
        return "ERROR", False


def _drain_one(queue_, pending):
    """Serve one queued margin request. True if a call ran."""
    global margin_fetched_count, margin_failed_count
    try:
        wid = queue_.get_nowait()
    except queue.Empty:
        return False

    with margin_lock:
        e = pending.get(wid)
        orders = e["orders"] if e is not None else None
    if orders is None:
        # Entry discarded (ATM flip aborted the window) — nothing to do
        return True

    value, ok = _margin_call(orders, wid[0], "")
    if ok:
        margin_fetched_count += 1
    else:
        margin_failed_count += 1

    with margin_lock:
        e = pending.get(wid)
        if e is not None:
            e["margin"] = value
            try_finalize_locked(wid)
    return True


def margin_worker():
    """Serially consume margin requests from Engine 1 (LTP) so we never exceed
    Arrow's 10 req/sec REST limit. Engine 2 uses in-house SPAN/ELM margin."""
    while not margin_stop.is_set():
        served = _drain_one(margin_request_q, margin_pending)
        if not served:
            time.sleep(MARGIN_WORKER_POLL_SEC)


def _f2(v):
    return f"{v:.2f}" if v is not None else ""


def _f0(v):
    return f"{v:.0f}" if v is not None else ""


def _build_exec_row(underlying, w, close_time, snap):
    """One ENGINE 2 window = one row.

    Timestamps, direction, prices and profit all come from the book. The ltp_*
    columns are engine 1's numbers read at the same instants, so the spread cost
    of a window is ltp_arb_rupees - open_exec_arb_rupees on that row.
    """
    op = w.get("open_snapshot") or snap
    return {
        "stock": underlying,
        "window_open_ist": w["open_time"],
        "peak_time_ist": w["peak_time"],
        "window_close_ist": close_time,
        "atm_strike": _f2(snap["strike"]),
        "lot_size": snap["lot_size"],
        "direction": w["direction"],
        "ce_bid": _f2(snap["ce_bid"]), "ce_ask": _f2(snap["ce_ask"]),
        "pe_bid": _f2(snap["pe_bid"]), "pe_ask": _f2(snap["pe_ask"]),
        "fut_bid": _f2(snap["fut_bid"]), "fut_ask": _f2(snap["fut_ask"]),
        "open_exec_profit_points": f"{w['open_exec_pts']:+.2f}",
        "open_exec_arb_rupees": _f0(w["open_exec_arb_rs"]),
        "open_exec_charges_rupees": _f0(w.get("open_exec_charges_rs", 0.0)),
        "peak_exec_profit_points": f"{w['peak_exec_pts']:+.2f}",
        "peak_exec_arb_rupees": _f0(w["peak_exec_arb_rs"]),
        "ltp_ce": _f2(op["ce"]), "ltp_pe": _f2(op["pe"]), "ltp_fut": _f2(op["fut"]),
        "ltp_parity_points": f"{op['parity_pts']:+.2f}",
        "ltp_arb_rupees": _f0(op["arb_rs"]),
        "ltp_arb_peak": _f0(snap["arb_rs"]),
        "ce_qty": snap["ce_qty"], "pe_qty": snap["pe_qty"], "fut_qty": snap["fut_qty"],
        "tradable_lots": snap["tradable_lots"],
        "leg_max_age_ms": f"{snap['leg_max_age_ms']:.0f}",
        "duration_sec": "",
    }


def build_exec_tick_row(ts_wall, underlying, direction, exec_info,
                        ce_px, pe_px, fut_px, arb_rs):
    """Per-tick row for every ENGINE 2 tick above its own gate."""
    return [
        ts_wall, underlying, direction,
        _f2(exec_info["ce_bid"]), _f2(exec_info["ce_ask"]),
        _f2(exec_info["pe_bid"]), _f2(exec_info["pe_ask"]),
        _f2(exec_info["fut_bid"]), _f2(exec_info["fut_ask"]),
        _f0(exec_info["exec_arb_rs"]),
        _f2(ce_px), _f2(pe_px), _f2(fut_px), _f0(arb_rs),
        exec_info["tradable_lots"],
    ]


def write_exec_window_row(exec_row, basket_margin, close_reason):
    """Append one engine 2 window to exec_windows.csv — crash safe, header once."""
    global exec_windows_written
    if exec_row is None:
        return
    try:
        open_dt = datetime.strptime(exec_row["window_open_ist"], "%Y-%m-%d %H:%M:%S.%f")
        close_dt = datetime.strptime(exec_row["window_close_ist"], "%Y-%m-%d %H:%M:%S.%f")
        exec_row["duration_sec"] = f"{max(0.0, (close_dt - open_dt).total_seconds()):.3f}"
    except Exception:
        exec_row["duration_sec"] = ""

    path = os.path.join(OUTPUT_DIR, EXEC_WINDOWS_FILE)
    with csv_write_lock:
        file_exists = os.path.exists(path) and os.path.getsize(path) > 0
        with open(path, "a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(EXEC_WINDOW_COLUMNS)
            out = []
            for col in EXEC_WINDOW_COLUMNS:
                if col == "basket_margin":
                    out.append(basket_margin)
                elif col == "close_reason":
                    out.append(close_reason)
                else:
                    out.append(exec_row.get(col, ""))
            writer.writerow(out)
    exec_windows_written += 1
    enqueue_discord_close(exec_row, basket_margin)


def flush_exec_ticks():
    """Write buffered per-tick bid/ask rows to exec_ticks.csv."""
    global exec_ticks_written
    if not exec_tick_buffer:
        return
    path = os.path.join(OUTPUT_DIR, EXEC_TICKS_FILE)
    file_exists = os.path.exists(path) and os.path.getsize(path) > 0
    rows = list(exec_tick_buffer)
    exec_tick_buffer.clear()
    with csv_write_lock:
        with open(path, "a", newline="", encoding="utf-8") as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(EXEC_TICK_COLUMNS)
            for row in rows:
                writer.writerow(row)
    exec_ticks_written += len(rows)


def write_parity_window_row(underlying, open_time, peak_time, close_time,
                            spot, fut, ce, pe, strike,
                            open_parity_pts, open_arb_rs,
                            peak_parity_pts, peak_arb_rs,
                            lot_size, direction, leg_max_age_ms,
                            basket_margin, close_reason):
    """Append one completed window to parity_windows.csv.gz — crash safe."""
    path = os.path.join(OUTPUT_DIR, PARITY_WINDOWS_FILE)
    open_dt = datetime.strptime(open_time, "%Y-%m-%d %H:%M:%S.%f")
    close_dt = datetime.strptime(close_time, "%Y-%m-%d %H:%M:%S.%f")
    duration = max(0.0, (close_dt - open_dt).total_seconds())
    with csv_write_lock:
        file_exists = os.path.exists(path)
        with gzip.open(path, "at", newline="") as f:
            writer = csv.writer(f)
            if not file_exists:
                writer.writerow(PARITY_WINDOW_COLUMNS)
            writer.writerow([
                underlying, open_time, peak_time, close_time,
                f"{spot:.2f}", f"{fut:.2f}", f"{ce:.2f}", f"{pe:.2f}",
                f"{strike:.2f}", f"{open_parity_pts:+.2f}", f"{open_arb_rs:.0f}",
                f"{peak_parity_pts:+.2f}", f"{peak_arb_rs:.0f}",
                lot_size, direction, f"{duration:.3f}", f"{leg_max_age_ms:.0f}",
                basket_margin, close_reason,
            ])


def flush_parity_ticks():
    """Write buffered parity tick rows to parity_ticks.csv.gz."""
    global parity_next_flush
    if not parity_tick_buffer:
        parity_next_flush = time.time() + PARITY_TICK_FLUSH_SEC
        return
    path = os.path.join(OUTPUT_DIR, PARITY_TICKS_FILE)
    file_exists = os.path.exists(path)
    rows = list(parity_tick_buffer)
    parity_tick_buffer.clear()
    with gzip.open(path, "at", newline="") as f:
        writer = csv.writer(f)
        if not file_exists:
            writer.writerow([
                "timestamp_ist", "stock", "spot", "fut", "ce", "pe",
                "atm_strike", "parity_points", "arb_rupees",
                "lot_size", "leg_max_age_ms",
            ])
        for row in rows:
            writer.writerow(row)
    parity_next_flush = time.time() + PARITY_TICK_FLUSH_SEC


def clear_parity_prices_for_stock(underlying):
    """Clear CE/PE prices on ATM flip — prevents stale-strike parity calc.

    An active window at flip time is CLOSED AND SAVED: its signal fired at the
    old strike, its prices were frozen at open, and its margin request is
    already in flight. Discarding it silently under-counted opportunities on
    flip-heavy stocks (~16% of the run).
    """
    info = stocks.get(underlying)
    if not info:
        return
    for key in ("ce_token", "pe_token"):
        t = info.get(key)
        if t and t in parity_price_store:
            del parity_price_store[t]
    if underlying in parity_windows:
        w = parity_windows[underlying]
        if w["active"]:
            _finalize_window(underlying, w, _now_ms_str(), "ATM_FLIP")
    if underlying in exec_windows:
        w = exec_windows[underlying]
        if w["active"]:
            _finalize_exec_window(underlying, w, _now_ms_str(), "ATM_FLIP")


def write_parity_summary():
    """Flush remaining tick buffers and close any open windows in BOTH engines."""
    # Flush remaining ticks
    flush_parity_ticks()
    flush_exec_ticks()

    # Close any still-active windows (forced close, margin marked PENDING).
    # Routed through the finalize helpers so an in-flight margin reply can still
    # land on the row instead of being dropped here.
    now_str = datetime.now(IST).strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
    for underlying, w in parity_windows.items():
        if w["active"] and w["peak_snapshot"]:
            _finalize_window(underlying, w, now_str, "SHUTDOWN")
    for underlying, w in exec_windows.items():
        if w["active"] and w["peak_snapshot"]:
            _finalize_exec_window(underlying, w, now_str, "SHUTDOWN")

    # Give the margin worker up to 5 seconds to drain in-flight requests
    margin_stop.set()
    deadline = time.time() + 5.0
    while time.time() < deadline:
        with margin_lock:
            if not margin_pending and margin_request_q.empty():
                break
        time.sleep(0.1)

    # Force-write any still-pending margin rows so we don't lose data
    with margin_lock:
        for wid, e in list(margin_pending.items()):
            if e["row"] is not None and not e["written"]:
                write_parity_window_row(*e["row"], "PENDING", e["reason"] or "SHUTDOWN")
                e["written"] = True
        margin_pending.clear()

    # Let every queued alert go out before the process ends — a partner must not
    # be left with an OPEN and no CLOSE for the same window.
    drain_discord_alerts()

    flush_exec_ticks()

    # Depth coverage across the whole run, by leg type
    def cov(key):
        got = tot = ticks_ok = ticks_bad = 0
        for u in resolved:
            t = stocks[u].get(key)
            if not t:
                continue
            tot += 1
            o = depth_ok_count.get(t, 0)
            b = depth_bad_count.get(t, 0)
            if o > 0:
                got += 1
            ticks_ok += o
            ticks_bad += b
        pct = 100.0 * got / tot if tot else 0.0
        share = 100.0 * ticks_ok / (ticks_ok + ticks_bad) if (ticks_ok + ticks_bad) else 0.0
        return f"{got}/{tot} instruments ({pct:.0f}%), {share:.0f}% of their ticks"

    abs_output = os.path.abspath(OUTPUT_DIR)
    if LTP_ENGINE_ENABLED:
        print(f"\n  ENGINE 1 — LTP (arrow_fno_demo.py behaviour):")
        print(f"    Windows completed : {parity_window_count}")
        print(f"    Closed by ATM flip: {parity_flip_close_count}")
        print(f"    Ticks logged      : {parity_tick_count}")
        print(f"    Margin fetched    : {margin_fetched_count}")
        print(f"    Margin failed     : {margin_failed_count}")
    else:
        print(f"\n  ENGINE 1 — LTP: DISABLED in this build (bid/ask opens windows only).")
    print(f"    Skipped (stale)   : {parity_skip_stale}")
    print(f"    Skipped (missing) : {parity_skip_missing}")
    print(f"\n  ENGINE 2 — BID/ASK:")
    print(f"    Windows completed : {exec_window_count}")
    print(f"    Closed by ATM flip: {exec_flip_close_count}")
    print(f"    Ticks logged      : {exec_tick_count}")
    print(f"    Rows written      : {exec_windows_written}")
    print(f"    Rejected LTP signals logged: {exec_shadow_count} "
          f"(LTP>=Rs{PARITY_THRESHOLD_RS:.0f}, book below)")
    print(f"    Rejected for no book:      {exec_nodepth_count}")
    print(f"    Depth coverage:")
    print(f"      future          : {cov('future_token')}")
    print(f"      CE              : {cov('ce_token')}")
    print(f"      PE              : {cov('pe_token')}")
    out_files = [EXEC_WINDOWS_FILE, EXEC_TICKS_FILE]
    if LTP_ENGINE_ENABLED:
        out_files = [PARITY_WINDOWS_FILE, PARITY_TICKS_FILE] + out_files
    for fname in out_files:
        fpath = os.path.join(abs_output, fname)
        if os.path.exists(fpath):
            sz = os.path.getsize(fpath)
            print(f"    {fname} ({sz:,} bytes)")
        else:
            print(f"    {fname} (no data)")


# =====================================================
# STREAM SETUP
# =====================================================
streams = ArrowStreams(appID=APP_ID, token=TOKEN, debug=False)

_spot_token_set = set(info["spot_token"] for info in stocks.values() if info.get("spot_token"))
_future_token_set = set(info["future_token"] for info in stocks.values())

opt_stream_type = "hft" if MODE == "HFT" else "market"


def _sub_items(ce, pe):
    if opt_stream_type == "hft":
        return [ce["symbol"], pe["symbol"]]
    else:
        return [ce["token"], pe["token"]]


def _process_tracker_events(underlying, events, spot_paise):
    global flip_count, emergency_count, unsub_count

    info = stocks[underlying]
    opts = option_tokens[underlying]
    expiry_str = info["future_expiry"]

    for ev in events:
        kind = ev[0]

        if kind == "flip":
            old_atm, new_atm = ev[1], ev[2]
            flip_count += 1
            clear_parity_prices_for_stock(underlying)

            new_ce = opts.get((new_atm, "CE"))
            new_pe = opts.get((new_atm, "PE"))
            new_pair_live = False
            if new_ce and new_pe:
                new_pair_live = all(i in live_sub_items for i in _sub_items(new_ce, new_pe))

            LOG_Q.append(("atm", (
                time.time_ns(), underlying, expiry_str, spot_paise,
                old_atm, new_atm, new_pair_live, True,
            )))

            atm_events_log.append((
                ist_text(), underlying, from_paise(old_atm),
                from_paise(new_atm), new_pair_live,
            ))
            log_only(f"  [{ist_text()}] ATM flip: {underlying} "
                     f"{from_paise(old_atm):g} -> {from_paise(new_atm):g} "
                     f"live={'YES' if new_pair_live else 'NO'}")

            if new_ce and new_pe:
                info["ce_token"] = new_ce["token"]
                info["ce_symbol"] = new_ce["symbol"]
                info["ce_strike"] = new_atm
                info["pe_token"] = new_pe["token"]
                info["pe_symbol"] = new_pe["symbol"]
                info["pe_strike"] = new_atm
            info["atm"] = new_atm
            rebuild_token_map()

        elif kind == "subscribe_new":
            strike = ev[1]
            emergency_count += 1
            ce = opts.get((strike, "CE"))
            pe = opts.get((strike, "PE"))
            if ce and pe:
                enqueue_sub("sub", opt_stream_type, _sub_items(ce, pe), underlying, strike)
            else:
                # Without this the ATM would stay unsubscribed and the stock
                # would silently stop producing parity.
                with lock:
                    error_count += 1
                    error_log.append(
                        f"{ist_text()} | NO OPTION PAIR | {underlying} "
                        f"strike {from_paise(strike):g} has no CE/PE row")

        elif kind == "unsubscribe_old":
            strike = ev[1]
            ce = opts.get((strike, "CE"))
            pe = opts.get((strike, "PE"))
            if ce and pe:
                unsub_count += 1
                enqueue_sub("unsub", opt_stream_type, _sub_items(ce, pe), underlying, strike)


def handle_spot_tick(raw):
    global spot_call_count
    t = tick_to_dict(raw) if not isinstance(raw, dict) else raw
    token = t.get("token")
    ltp = t.get("ltp")
    if token is None or ltp is None:
        return

    with lock:
        tick_counts[token] += 1

    underlying = None
    for u, info in stocks.items():
        if info.get("spot_token") == token:
            underlying = u
            break
    if underlying is None:
        return

    try:
        price = float(ltp)
        if price <= 0:
            return
    except Exception:
        return

    spot_paise = int(price)

    update_parity_price(token, spot_paise, t)

    with lock:
        spot_ltp_paise[underlying] = spot_paise

    spot_call_count += 1
    do_timing = (spot_call_count % 100 == 0)
    t0 = time.perf_counter_ns() if do_timing else 0

    tracker = trackers.get(underlying)
    if tracker:
        events = tracker.on_spot(spot_paise)
        if events:
            _process_tracker_events(underlying, events, spot_paise)

    if do_timing:
        elapsed = time.perf_counter_ns() - t0
        spot_timings.append(elapsed)


def handle_main_tick(raw):
    t = tick_to_dict(raw) if not isinstance(raw, dict) else raw
    token = t.get("token")
    if token is None:
        return

    with lock:
        tick_counts[token] += 1

    ltp = t.get("ltp")
    if ltp is not None:
        try:
            px = float(ltp)
            if px > 0:
                update_parity_price(token, px, t)
        except Exception:
            pass

    for u, info in stocks.items():
        if info.get("future_token") == token:
            if ltp is not None:
                try:
                    px = float(ltp)
                    with lock:
                        future_ltp_paise[u] = int(px)
                except Exception:
                    pass
            break


# --- Connect / disconnect callbacks ---
def on_data_connect():
    global spot_connected
    spot_connected = True
    print(f"[{ist_text()}] Data stream connected")
    all_tokens = []
    atm_pairs = []
    for info in stocks.values():
        if info.get("spot_token"):
            all_tokens.append(info["spot_token"])
        if info.get("future_token"):
            all_tokens.append(info["future_token"])
        if info.get("ce_token"):
            all_tokens.append(info["ce_token"])
        if info.get("pe_token"):
            all_tokens.append(info["pe_token"])
        if info.get("ce_token") and info.get("pe_token"):
            atm_pairs.append(_sub_items(
                {"token": info["ce_token"], "symbol": info.get("ce_symbol")},
                {"token": info["pe_token"], "symbol": info.get("pe_symbol")},
            ))
    if all_tokens:
        _subscribe_chunked("market", "sub", all_tokens)
        # Every instrument now holds exactly cash + future + ATM CE/PE.
        with lock:
            for items in atm_pairs:
                live_sub_items.update(items)
        print(f"  Subscribed {len(all_tokens)} tokens in "
              f"{-(-len(all_tokens) // SUB_CHUNK_SIZE)} chunks of "
              f"<= {SUB_CHUNK_SIZE} (FULL mode)")
        spot_connected = True


def on_data_disconnect():
    global spot_connected, disconnect_count
    spot_connected = False
    with lock:
        disconnect_count += 1
    print(f"[{ist_text()}] Data stream DISCONNECTED (#{disconnect_count})")


def on_data_close(close_status_code, close_msg):
    print(f"[{ist_text()}] Data stream CLOSE: code={close_status_code}, msg={close_msg}")


def on_main_connect():
    global main_connected
    main_connected = True
    print(f"[{ist_text()}] {MODE} stream connected — subscribing futures + options")
    fut_symbols = [info["future_symbol"] for info in stocks.values()]
    ce_symbols = [info["ce_symbol"] for info in stocks.values() if info.get("ce_symbol")]
    pe_symbols = [info["pe_symbol"] for info in stocks.values() if info.get("pe_symbol")]

    if MODE == "HFT":
        if fut_symbols:
            _subscribe_chunked("hft", "sub", fut_symbols)
            print(f"  Futures: {len(fut_symbols)} symbols (HFT full)")
        opt_symbols = ce_symbols + pe_symbols
        if opt_symbols:
            _subscribe_chunked("hft", "sub", opt_symbols)
            print(f"  Options: {len(opt_symbols)} symbols (HFT full)")
    else:
        all_symbols = fut_symbols + ce_symbols + pe_symbols
        if all_symbols:
            _subscribe_chunked("market", "sub", all_symbols)
            print(f"  Subscribed {len(all_symbols)} symbols (Normal FULL)")
            print(f"    Futures: {len(fut_symbols)} | Options: {len(ce_symbols) + len(pe_symbols)}")


def on_main_disconnect():
    global main_connected, disconnect_count
    main_connected = False
    with lock:
        disconnect_count += 1
    print(f"[{ist_text()}] {MODE} stream DISCONNECTED (#{disconnect_count})")


def on_main_response(resp):
    try:
        code = resp.get("error_code", "?")
        rtype = resp.get("request_type_str", "?")
        if code != "SUCCESS":
            with lock:
                global error_count
                error_count += 1
                error_log.append(f"{ist_text()} | {rtype} | {code}")
            print(f"  [SUB] {code} | type={rtype}")
    except Exception as exc:
        with lock:
            error_count += 1
            error_log.append(f"{ist_text()} | handler | {exc}")


def on_main_reconnect(attempt, delay):
    print(f"[{ist_text()}] {MODE} reconnecting... attempt={attempt}, delay={delay}s")


def on_main_no_reconnect():
    with lock:
        global error_count
        error_count += 1
        error_log.append(f"{ist_text()} | NO_RECONNECT | gave up")
    print(f"[{ist_text()}] {MODE} stream GAVE UP reconnecting")


def on_main_error(error):
    with lock:
        global error_count
        error_count += 1
        error_log.append(f"{ist_text()} | ERROR | {error}")
    print(f"[{ist_text()}] {MODE} error: {error}")


# Wire callbacks
streams.data_stream.on_connect = on_data_connect
streams.data_stream.on_disconnect = on_data_disconnect
streams.data_stream.on_close = on_data_close

if MODE == "NORMAL":
    streams.data_stream.on_reconnect = on_main_reconnect
    streams.data_stream.on_no_reconnect = on_main_no_reconnect
    streams.data_stream.on_error = on_main_error

    def combined_data_tick(tick):
        t = tick_to_dict(tick)
        token = t.get("token")
        if token is None:
            return
        if token in _spot_token_set:
            handle_spot_tick(t)
        else:
            handle_main_tick(t)
    streams.data_stream.on_ticks = combined_data_tick
else:
    streams.data_stream.on_ticks = handle_spot_tick

if MODE == "HFT":
    streams.hft_data_stream.on_full_tick = handle_main_tick
    streams.hft_data_stream.on_connect = on_main_connect
    streams.hft_data_stream.on_disconnect = on_main_disconnect
    streams.hft_data_stream.on_reconnect = on_main_reconnect
    streams.hft_data_stream.on_no_reconnect = on_main_no_reconnect
    streams.hft_data_stream.on_error = on_main_error
    streams.hft_data_stream.on_response = on_main_response
else:
    streams.data_stream.on_response = on_main_response
    streams.data_stream.on_reconnect = on_main_reconnect
    streams.data_stream.on_no_reconnect = on_main_no_reconnect
    streams.data_stream.on_error = on_main_error


# =====================================================
# MARGIN ENGINE (in-house SPAN + ELM, auto-downloaded and hot-swapped)
# =====================================================
margin_svc = MarginService(symbols=list(resolved), nov_price="trade", interval_min=MARGIN_REFRESH_MIN)
# Contract bridge: the SPAN keys come from the SAME broker rows we subscribe to (same name, expiry date, every strike).
margin_svc.set_universe({
    u: {"expiry": stocks[u]["nearest_expiry"].strftime("%Y%m%d"),
        "strikes": [from_paise(p) for p in underlying_strikes_paise[u]],
        "spot_ref": stocks[u]["master_spot_ltp_raw"] / 100.0,
        "fut_ref": stocks[u]["master_fut_ltp_raw"] / 100.0}
    for u in resolved})
margin_svc.start()
print(f"[{ist_text()}] Margin engine: downloading SPAN + ELM (waiting up to {MARGIN_WAIT_SEC}s)...")
if not margin_svc.wait_ready(MARGIN_WAIT_SEC):
    print(f"[{ist_text()}] WARNING: margin engine NOT ready - no signals until the SPAN/ELM files load "
          f"(retries every {MARGIN_REFRESH_MIN} min)")

# =====================================================
# START WORKER THREADS
# =====================================================
sub_thread = threading.Thread(target=sub_worker, daemon=True, name="sub-worker")
log_thread = threading.Thread(target=log_writer, daemon=True, name="log-writer")
margin_thread = threading.Thread(target=margin_worker, daemon=True, name="margin-worker")
sub_thread.start()
log_thread.start()
margin_thread.start()
discord_thread = start_discord_alerts()


# =====================================================
# CONNECT
# =====================================================
print(f"\n[{ist_text()}] Connecting data stream...")
streams.connect_data_stream()
time.sleep(1)

if MODE == "HFT":
    print(f"[{ist_text()}] Connecting HFT stream (futures + options)...")
    streams.connect_hft_data_stream()
else:
    print(f"[{ist_text()}] Normal mode — all subscriptions via on_data_connect callback")

n_subscribed = len(resolved) * 4
time.sleep(1)


# =====================================================
# AUTO-START: Wait until 9:20 AM if started earlier
# =====================================================
_now_ist = datetime.now(IST)
_start_time_ist = _now_ist.replace(hour=9, minute=20, second=0, microsecond=0)
if _now_ist < _start_time_ist:
    _wait_sec = (_start_time_ist - _now_ist).total_seconds()
    print(f"[{_start_time_ist.strftime('%H:%M:%S')}] Waiting {_wait_sec:.0f}s until 9:20 AM auto-start...")
    time.sleep(_wait_sec)
    print(f"[{ist_text()}] Auto-start: beginning session now.")

# =====================================================
# MONITOR LOOP
# =====================================================
_end_time_ist = datetime.now(IST).replace(hour=15, minute=0, second=0, microsecond=0)
print(f"\n[{ist_text()}] Monitoring until {_end_time_ist.strftime('%H:%M:%S')} (3:00 PM)...\n")

start_time = time.time()
last_stats_time = 0
last_health_time = 0
interrupted = False

try:
    while datetime.now(IST) < _end_time_ist:
        now = time.time()
        elapsed = now - start_time

        if now - last_health_time >= 1.0:
            with lock:
                timings_copy = list(spot_timings)
                spot_timings.clear()
                ec = error_count
                dc = disconnect_count

            p50 = p99 = 0
            if timings_copy:
                s = sorted(timings_copy)
                p50 = s[len(s) // 2]
                p99 = s[min(int(len(s) * 0.99), len(s) - 1)]

            LOG_Q.append(("health", (
                time.time_ns(), n_subscribed, len(SUB_Q),
                p50, p99, dc, ec,
            )))
            last_health_time = now

        # Token watchdog: refresh if >20 hours old
        if time.monotonic() - _last_login_mono > 72000:
            print(f"[{ist_text()}] Token age >20h — refreshing...")
            refresh_token()

        if now - last_stats_time >= STATS_INTERVAL:
            with lock:
                total = sum(tick_counts.values())
                dc = disconnect_count
                ec = error_count
                unique = len(tick_counts)

            mins = int(elapsed // 60)
            secs = int(elapsed % 60)
            spot_ok = sum(1 for u in resolved
                           if stocks[u].get("spot_token") and tick_counts.get(stocks[u]["spot_token"], 0) > 0)
            fut_ok = sum(1 for u in resolved
                          if tick_counts.get(stocks[u]["future_token"], 0) > 0)
            ce_ok = sum(1 for u in resolved
                         if stocks[u].get("ce_token") and tick_counts.get(stocks[u]["ce_token"], 0) > 0)
            pe_ok = sum(1 for u in resolved
                         if stocks[u].get("pe_token") and tick_counts.get(stocks[u]["pe_token"], 0) > 0)

            # Depth coverage: how many instruments of each type have ever sent a
            # usable best bid + best ask. This is the number that tells us whether
            # Arrow actually fills the book on option tokens.
            def depth_cov(key):
                got = tot = 0
                for u in resolved:
                    t = stocks[u].get(key)
                    if not t:
                        continue
                    tot += 1
                    if depth_ok_count.get(t, 0) > 0:
                        got += 1
                return f"{got}/{tot}"

            if LTP_ENGINE_ENABLED:
                engine_txt = (f"ltp_win={parity_window_count} bidask_win={exec_window_count} "
                              f"rows={parity_window_count}+{exec_windows_written} "
                              f"margins={margin_fetched_count} "
                              f"fail={margin_failed_count}")
            else:
                engine_txt = (f"bidask_win={exec_window_count} rows={exec_windows_written} "
                              f"nomargin={exec_nomargin_count} "
                              f"mgn_err={margin_svc.stats['error']}")

            print(
                f"[{ist_text()}] {mins:02d}:{secs:02d} | "
                f"ticks={total:,} tokens={unique} | "
                f"dc={dc} err={ec} flips={flip_count} fresh_subs={emergency_count} | "
                f"sub_q={len(SUB_Q)} | "
                f"spot={spot_ok}/{len(resolved)} fut={fut_ok}/{len(resolved)} "
                f"ce={ce_ok}/{len(resolved)} pe={pe_ok}/{len(resolved)} | "
                f"depth fut={depth_cov('future_token')} ce={depth_cov('ce_token')} "
                f"pe={depth_cov('pe_token')} | "
                f"{engine_txt}"
            )
            last_stats_time = now

        time.sleep(1)

except KeyboardInterrupt:
    interrupted = True
    print(f"\n\n[{ist_text()}] ⚠ Interrupted! Saving files...")


# =====================================================
# FINAL SUMMARY
# =====================================================
print("\n" + "=" * 70)
if interrupted:
    print("  FINAL SUMMARY (INTERRUPTED — partial data)")
else:
    print("  FINAL SUMMARY")
print("=" * 70)

# Parity engine final flush + summary
write_parity_summary()

total_time = time.time() - start_time
with lock:
    total_ticks = sum(tick_counts.values())
    f_disconnects = disconnect_count
    f_errors = error_count
    f_counts = dict(tick_counts)
    f_errors_log = list(error_log)
    f_future_ltp = {u: from_paise(p) for u, p in future_ltp_paise.items()}
    f_spot_ltp = {u: from_paise(p) for u, p in spot_ltp_paise.items()}

print(f"\n  Mode              : {MODE}")
print(f"  Duration          : {int(total_time // 60)}m {int(total_time % 60)}s")
print(f"  Stocks            : {len(resolved)}")
print(f"  Total ticks       : {total_ticks:,}")
print(f"  Unique tokens     : {len(f_counts)}")
print(f"  Ticks/sec         : {total_ticks / max(total_time, 1):.1f}")
print(f"  Disconnects       : {f_disconnects}")
print(f"  Errors            : {f_errors}")
print(f"  ATM flips         : {flip_count}")
print(f"  Fresh subs on flip: {emergency_count}")
print(f"  Strikes released  : {unsub_count}")

# Spot timing
all_timings = list(spot_timings)
if all_timings:
    s = sorted(all_timings)
    print(f"\n  on_spot timing (sampled every 100 calls):")
    print(f"    p50={s[len(s)//2]/1000:.1f}us  "
          f"p99={s[min(int(len(s)*0.99), len(s)-1)]/1000:.1f}us  "
          f"max={max(s)/1000:.1f}us  "
          f"samples={len(s)}")

# Per-stock table
print(f"\n  {'Stock':<16} {'Spot':>7} {'Fut':>7} {'CE':>7} {'PE':>7} {'Total':>8} {'ATM':>7} {'FutPx':>10}")
print("  " + "-" * 80)

stocks_with_ticks = 0
for u in resolved:
    info = stocks[u]
    s = f_counts.get(info.get("spot_token"), 0)
    f = f_counts.get(info["future_token"], 0)
    c = f_counts.get(info.get("ce_token"), 0)
    p = f_counts.get(info.get("pe_token"), 0)
    t = s + f + c + p
    if t > 0:
        stocks_with_ticks += 1
    fut_px = f_future_ltp.get(u, 0)
    atm = info.get("atm", 0)
    px_str = f"{fut_px:>10.2f}" if fut_px else f"{'N/A':>10}"
    atm_str = f"{from_paise(atm):>7g}" if atm else f"{'?':>7}"
    print(f"  {u:<16} {s:>7} {f:>7} {c:>7} {p:>7} {t:>8} {atm_str} {px_str}")

# Coverage
print(f"\n  COVERAGE:")
n = len(resolved)
spot_ok = sum(1 for u in resolved
              if stocks[u].get("spot_token") and f_counts.get(stocks[u]["spot_token"], 0) > 0)
fut_ok = sum(1 for u in resolved if f_counts.get(stocks[u]["future_token"], 0) > 0)
ce_ok = sum(1 for u in resolved
            if stocks[u].get("ce_token") and f_counts.get(stocks[u]["ce_token"], 0) > 0)
pe_ok = sum(1 for u in resolved
            if stocks[u].get("pe_token") and f_counts.get(stocks[u]["pe_token"], 0) > 0)
print(f"    Spot ticks  : {spot_ok}/{n}")
print(f"    Future ticks: {fut_ok}/{n}")
print(f"    CE ticks    : {ce_ok}/{n}")
print(f"    PE ticks    : {pe_ok}/{n}")
print(f"    Full coverage (all 4): {stocks_with_ticks}/{n}")

# ATM events
if atm_events_log:
    print(f"\n  ATM EVENTS ({len(atm_events_log)}): -> full rows in console_log.txt")
    for ev in atm_events_log:
        ts, und, old, new, live = ev
        log_only(f"    {ts} {und:<16} {old:>8g} -> {new:>8g}  "
                 f"live={'YES' if live else 'NO '}")

# Errors
if f_errors_log:
    print(f"\n  ERROR LOG (last 10):")
    for entry in f_errors_log[-10:]:
        print(f"    {entry}")

# Subscription stats
sub_ops = emergency_count + unsub_count
print(f"\n  SUBSCRIPTION OPS:")
print(f"    Total ops         : {sub_ops}")
print(f"    Flip subs issued  : {emergency_count}")
print(f"    Strikes released  : {unsub_count}")
if flip_count > 0:
    print(f"    Ops per flip      : {sub_ops / flip_count:.2f}")

# The policy is 4 legs per instrument, so the live option set must equal the
# current ATM pairs exactly — any extra entry means a stale strike is still
# holding a subscription slot.
print(f"\n  SUBSCRIPTION BUDGET CHECK:")
expected_live = set()
for u in resolved:
    info = stocks[u]
    if info.get("ce_token") and info.get("pe_token"):
        expected_live.update(_sub_items(
            {"token": info["ce_token"], "symbol": info.get("ce_symbol")},
            {"token": info["pe_token"], "symbol": info.get("pe_symbol")},
        ))
with lock:
    extra = sorted(live_sub_items - expected_live, key=str)
    missing = sorted(expected_live - live_sub_items, key=str)
for item in extra[:10]:
    print(f"    WARNING: held beyond ATM policy: {item}")
for item in missing[:10]:
    print(f"    WARNING: ATM pair not held: {item}")
if not extra and not missing:
    print(f"    Clean — {len(expected_live)} option legs held, 2 per instrument, nothing extra")

# Output files
print(f"\n  OUTPUT FILES:")
abs_output = os.path.abspath(OUTPUT_DIR)
out_names = ["startup_snapshot.json", "atm_events.csv.gz", "sub_events.csv.gz", "health.csv.gz",
             EXEC_WINDOWS_FILE, EXEC_TICKS_FILE]
if LTP_ENGINE_ENABLED:
    out_names += [PARITY_WINDOWS_FILE, PARITY_TICKS_FILE]
out_names.append("console_log.txt")
for fname in out_names:
    fpath = os.path.join(abs_output, fname)
    if os.path.exists(fpath):
        sz = os.path.getsize(fpath)
        print(f"    {fpath} ({sz:,} bytes)")
    else:
        print(f"    {fpath} (MISSING)")

print("\n" + "=" * 70)
if interrupted:
    print(f"  Demo interrupted after {int(total_time // 60)}m {int(total_time % 60)}s.")
else:
    print(f"  Demo complete. {MODE} stream ran for {int(total_time // 60)}m {int(total_time % 60)}s.")
print("=" * 70)


# =====================================================
# CLEANUP
# =====================================================
stop_event.set()

try:
    sub_thread.join(timeout=5)
except Exception:
    pass
try:
    log_thread.join(timeout=5)
except Exception:
    pass

try:
    streams.disconnect_all()
    print(f"[{ist_text()}] Disconnected")
except Exception:
    pass

print(f"[{ist_text()}] RUN END — full trace in {os.path.abspath(console_sink.path)}")
sys.stdout.flush()
sys.stderr.flush()
console_sink.sync()
