"""
MACD Scanner — 4H MACD Crossover + Pullback Entry Scanner
Detects: WATCH (approaching) | JUST CROSSED | PULLBACK ENTRY

Run: python macd_scanner.py
Open: http://localhost:5003
"""

from flask import Flask, jsonify, render_template_string, request
import requests, threading, time, math, os

app  = Flask(__name__)
BASE = "https://fapi.binance.com"

import urllib3
urllib3.disable_warnings()
SESSION = requests.Session()
adapter = requests.adapters.HTTPAdapter(pool_connections=30, pool_maxsize=30, max_retries=1)
SESSION.mount("https://", adapter)

cache = {
    "coins": [], "last_scan": None,
    "scanning": False, "progress": "",
    "progress_pct": 0, "error": None
}

auto_scan = {"enabled": True, "interval": 15, "last_run": 0, "next_run": 0}

# ── HTTP ───────────────────────────────────────────────────────────────────
def get(endpoint, params=None, timeout=8):
    try:
        r = SESSION.get(BASE + endpoint, params=params, timeout=timeout)
        r.raise_for_status()
        return r.json()
    except:
        return None

# ── Indicators ─────────────────────────────────────────────────────────────
def ema(data, period):
    if len(data) < period: return []
    k = 2 / (period + 1)
    result = [sum(data[:period]) / period]
    for price in data[period:]:
        result.append(price * k + result[-1] * (1 - k))
    return result

def calc_macd(closes, fast=12, slow=26, signal=9):
    """Calculate MACD line, Signal line, Histogram."""
    if len(closes) < slow + signal: return [], [], []
    ema_fast = ema(closes, fast)
    ema_slow = ema(closes, slow)
    # Align — ema_fast starts at fast-1, ema_slow at slow-1
    offset = slow - fast
    macd_line = [ema_fast[i + offset] - ema_slow[i]
                 for i in range(len(ema_slow))]
    signal_line = ema(macd_line, signal)
    # Align signal to macd
    sig_offset = len(macd_line) - len(signal_line)
    histogram = [macd_line[i + sig_offset] - signal_line[i]
                 for i in range(len(signal_line))]
    macd_aligned = macd_line[sig_offset:]
    return macd_aligned, signal_line, histogram

def sma(data, n):
    if len(data) < n: return None
    return sum(data[-n:]) / n

def rsi(closes, n=14):
    if len(closes) < n + 1: return None
    gains, losses = [], []
    for i in range(1, len(closes)):
        d = closes[i] - closes[i-1]
        gains.append(max(d, 0))
        losses.append(max(-d, 0))
    ag = sum(gains[:n]) / n
    al = sum(losses[:n]) / n
    for i in range(n, len(gains)):
        ag = (ag*(n-1) + gains[i]) / n
        al = (al*(n-1) + losses[i]) / n
    if al == 0: return 100.0
    return round(100 - 100 / (1 + ag/al), 2)

def atr(highs, lows, closes, n=14):
    if len(closes) < n + 1: return None
    trs = [max(highs[i]-lows[i], abs(highs[i]-closes[i-1]), abs(lows[i]-closes[i-1]))
           for i in range(1, len(closes))]
    a = sum(trs[:n]) / n
    for t in trs[n:]:
        a = (a*(n-1) + t) / n
    return a

# ── MACD Analysis ──────────────────────────────────────────────────────────
def analyze(klines_4h):
    """Full MACD analysis on 4H klines."""
    if not klines_4h or len(klines_4h) < 60:
        return None

    o4 = [float(k[1]) for k in klines_4h]
    h4 = [float(k[2]) for k in klines_4h]
    l4 = [float(k[3]) for k in klines_4h]
    c4 = [float(k[4]) for k in klines_4h]
    v4 = [float(k[5]) for k in klines_4h]
    price = c4[-1]

    # ── MACD ──
    macd_line, signal_line, histogram = calc_macd(c4)
    if len(macd_line) < 10:
        return None

    # Current values
    macd_now   = macd_line[-1]
    signal_now = signal_line[-1]
    hist_now   = histogram[-1]
    hist_prev  = histogram[-2]
    hist_prev2 = histogram[-3]
    gap        = macd_now - signal_now  # positive = MACD above signal

    # Gap trend — is MACD approaching signal?
    gap_prev  = macd_line[-2] - signal_line[-2]
    gap_prev2 = macd_line[-3] - signal_line[-3]
    gap_closing = gap > gap_prev2 and gap_prev > gap_prev2  # gap shrinking from below
    gap_velocity = gap - gap_prev  # rate of change

    # ── Detect cross events in recent history ──
    cross_bar = None   # how many bars ago was last bullish cross
    cross_type = None  # "bullish" or "bearish"

    for i in range(1, min(15, len(macd_line))):
        prev_gap = macd_line[-(i+1)] - signal_line[-(i+1)]
        curr_gap = macd_line[-i]     - signal_line[-i]
        if prev_gap < 0 and curr_gap >= 0:
            cross_bar  = i
            cross_type = "bullish"
            break
        if prev_gap > 0 and curr_gap <= 0:
            cross_bar  = i
            cross_type = "bearish"
            break

    # ── Histogram momentum ──
    hist_growing    = hist_now > hist_prev > 0           # growing positive bars
    hist_recovering = hist_prev < hist_prev2 < 0 and hist_now > hist_prev  # bottoming out

    # ── RSI ──
    rsi14 = rsi(c4, 14)

    # ── MAs ──
    ma50  = sma(c4, 50)
    ma200 = sma(c4, min(200, len(c4)))
    above_ma50  = ma50  and price > ma50
    above_ma200 = ma200 and price > ma200

    # ── Volume ──
    avg_vol = sma(v4, 20)
    rel_vol = round(v4[-1] / avg_vol, 2) if avg_vol else None
    vol_confirm = rel_vol and rel_vol >= 1.2

    # ── ATR ──
    atr14     = atr(h4, l4, c4, 14)
    avg_atr   = None
    if atr14 and len(c4) >= 34:
        atrs = []
        for i in range(20):
            a = atr(h4[:-(i+1)] if i > 0 else h4,
                    l4[:-(i+1)] if i > 0 else l4,
                    c4[:-(i+1)] if i > 0 else c4, 14)
            if a: atrs.append(a)
        avg_atr = sum(atrs)/len(atrs) if atrs else atr14
    atr_normal = avg_atr and atr14 and atr14 >= avg_atr * 0.7

    # ── Pullback detection ──
    pullback_pct    = None
    pullback_valid  = False
    cross_high      = None
    vol_on_cross    = None
    vol_on_pullback = None

    if cross_bar and cross_type == "bullish" and 2 <= cross_bar <= 10:
        # Find highest price AFTER the cross
        bars_after_cross = h4[-cross_bar:]
        cross_high       = max(bars_after_cross) if bars_after_cross else None
        if cross_high and cross_high > price:
            pullback_pct = round((cross_high - price) / cross_high * 100, 2)
            # Valid pullback: between 1.5% and 7%, MACD still bullish
            pullback_valid = (1.5 <= pullback_pct <= 7.0 and gap > 0)

        # Volume comparison: crossover candle vs pullback candles
        if cross_bar < len(v4):
            vol_on_cross    = v4[-cross_bar]
            vol_on_pullback = sum(v4[-min(cross_bar-1, 3):]) / min(cross_bar-1, 3) if cross_bar > 1 else None

    # ── Candle body strength ──
    last_body   = abs(c4[-1] - o4[-1]) / (h4[-1] - l4[-1] + 0.000001)
    cross_body  = None
    if cross_bar and cross_bar < len(c4):
        cb = abs(c4[-cross_bar] - o4[-cross_bar])
        cr = h4[-cross_bar] - l4[-cross_bar]
        cross_body = cb / (cr + 0.000001)

    # ── Price changes ──
    chg_1h  = round((c4[-1]-c4[-2])/c4[-2]*100, 3) if len(c4)>=2  else None
    chg_4h  = round((c4[-1]-c4[-5])/c4[-5]*100, 3) if len(c4)>=5  else None
    chg_24h = round((c4[-1]-c4[-25])/c4[-25]*100,3) if len(c4)>=25 else None

    # ── Zero line ──
    macd_above_zero   = macd_now > 0
    signal_above_zero = signal_now > 0

    # ── DETERMINE SIGNAL TYPE ──────────────────────────────────────────────
    signal_type = None
    score       = 0
    reasons     = []
    warnings    = []

    # PULLBACK ENTRY — highest priority
    if pullback_valid and cross_type == "bullish":
        signal_type = "PULLBACK ENTRY"

        # Score pullback entry
        s = 0
        if 2 <= pullback_pct <= 4:
            s += 25; reasons.append(f"Ideal Pullback {pullback_pct:.1f}% — sweet spot entry zone")
        elif pullback_pct <= 6:
            s += 15; reasons.append(f"Pullback {pullback_pct:.1f}% — valid entry zone")

        if cross_bar <= 4:
            s += 15; reasons.append(f"Fresh Cross {cross_bar} bars ago — early pullback")
        else:
            s += 8;  reasons.append(f"Cross {cross_bar} bars ago — pullback developing")

        if gap > 0:
            s += 15; reasons.append("MACD still above Signal — cross intact")

        if macd_above_zero:
            s += 15; reasons.append("MACD above zero — bullish territory")

        if rsi14 and 40 <= rsi14 <= 65:
            s += 10; reasons.append(f"RSI {rsi14:.0f} — room to run")
        elif rsi14 and rsi14 > 68:
            warnings.append(f"⚠ RSI {rsi14:.0f} high — pullback may extend")

        if vol_on_cross and vol_on_pullback and vol_on_cross > vol_on_pullback:
            s += 10; reasons.append("Lower volume on pullback — healthy retracement")

        if above_ma50:
            s += 5; reasons.append("Price above MA50 — trend aligned")

        if hist_growing:
            s += 5; reasons.append("Histogram growing — momentum intact")

        score = min(100, s)

    # JUST CROSSED
    elif cross_bar and cross_bar <= 2 and cross_type == "bullish":
        signal_type = "JUST CROSSED"

        s = 0
        if cross_bar == 1:
            s += 25; reasons.append("MACD crossed Signal THIS candle")
        else:
            s += 20; reasons.append("MACD crossed Signal last candle")

        if macd_above_zero:
            s += 20; reasons.append("Cross above zero line — strong bullish signal")
        else:
            s += 8;  reasons.append("Cross below zero — watch for zero line test")
            warnings.append("⚠ Below zero line — weaker signal")

        if hist_growing:
            s += 15; reasons.append("Histogram growing — momentum building")

        if rsi14 and 40 <= rsi14 <= 65:
            s += 15; reasons.append(f"RSI {rsi14:.0f} — ideal entry zone")
        elif rsi14 and rsi14 > 70:
            warnings.append(f"⚠ RSI {rsi14:.0f} overbought — wait for pullback")

        if vol_confirm:
            s += 10; reasons.append(f"Volume {rel_vol:.1f}x — institutions participating")
        else:
            warnings.append("⚠ Low volume on cross — weak signal")

        if above_ma50:
            s += 10; reasons.append("Price above MA50 — uptrend confirmed")

        if cross_body and cross_body > 0.6:
            s += 5; reasons.append("Strong candle body on cross — conviction")

        score = min(100, s)

    # WATCH — approaching cross
    elif gap < 0 and gap > gap_prev and gap_velocity > 0:
        # MACD below signal but closing the gap
        signal_type = "WATCH"

        s = 0
        gap_pct = abs(gap / max(abs(signal_now), 0.0001)) * 100

        if gap_pct < 5:
            s += 25; reasons.append(f"MACD very close to Signal — cross imminent")
        elif gap_pct < 15:
            s += 15; reasons.append(f"MACD approaching Signal (gap {gap_pct:.1f}%)")
        elif gap_pct < 30:
            s += 8;  reasons.append(f"MACD converging toward Signal")
        else:
            return None  # too far to be actionable

        if hist_recovering:
            s += 20; reasons.append("Histogram recovering from lows — momentum turning")
        elif hist_now > hist_prev:
            s += 12; reasons.append("Histogram improving")

        if macd_above_zero or signal_above_zero:
            s += 15; reasons.append("Near zero line — approaching bullish territory")

        if rsi14 and 35 <= rsi14 <= 60:
            s += 15; reasons.append(f"RSI {rsi14:.0f} — room to run on cross")

        if above_ma50:
            s += 10; reasons.append("Above MA50 — trend supports cross")

        if gap_velocity > abs(gap_prev - gap_prev2):
            s += 5; reasons.append("Gap closing faster — acceleration")

        score = min(100, s)

    else:
        return None  # No actionable signal

    if score < 35:
        return None  # Below minimum threshold

    return {
        "score":         score,
        "signal_type":   signal_type,
        "reasons":       warnings + reasons,
        "price":         round(price, 8),

        # MACD values
        "macd":          round(macd_now, 8),
        "signal":        round(signal_now, 8),
        "histogram":     round(hist_now, 8),
        "hist_prev":     round(hist_prev, 8),
        "hist_prev2":    round(hist_prev2, 8),
        "gap":           round(gap, 8),
        "gap_velocity":  round(gap_velocity, 8),
        "macd_above_zero":   macd_above_zero,
        "signal_above_zero": signal_above_zero,
        "hist_growing":  hist_growing,
        "hist_recovering":hist_recovering,

        # Cross info
        "cross_bar":     cross_bar,
        "cross_type":    cross_type,
        "cross_high":    round(cross_high, 8) if cross_high else None,
        "pullback_pct":  pullback_pct,
        "pullback_valid":pullback_valid,

        # Indicators
        "rsi14":         rsi14,
        "ma50":          round(ma50, 8) if ma50 else None,
        "above_ma50":    above_ma50,
        "above_ma200":   above_ma200,
        "rel_vol":       rel_vol,
        "vol_confirm":   vol_confirm,
        "atr_normal":    atr_normal,

        # Price
        "chg_1h":        chg_1h,
        "chg_4h":        chg_4h,
        "chg_24h":       chg_24h,

        # For chart
        "macd_series":   [round(v, 8) for v in macd_line[-60:]],
        "signal_series": [round(v, 8) for v in signal_line[-60:]],
        "hist_series":   [round(v, 8) for v in histogram[-60:]],
        "close_series":  c4[-60:],
        "high_series":   h4[-60:],
        "low_series":    l4[-60:],
        "open_series":   o4[-60:],
        "vol_series":    v4[-60:],
    }

# ── Scan ───────────────────────────────────────────────────────────────────
def do_scan():
    if cache["scanning"]: return
    cache["scanning"]     = True
    cache["error"]        = None
    cache["progress_pct"] = 0
    cache["progress"]     = "Starting scan..."

    try:
        cache["progress"] = "Step 1/2 — Fetching all USDT perp tickers..."
        tickers = get("/fapi/v1/ticker/24hr") or []
        usdt = sorted(
            [t for t in tickers if t["symbol"].endswith("USDT")
             and float(t.get("quoteVolume", 0)) > 500_000],
            key=lambda x: float(x.get("quoteVolume", 0)), reverse=True
        )[:300]

        cache["progress"] = f"Step 2/2 — Scanning {len(usdt)} pairs for MACD signals..."

        from concurrent.futures import ThreadPoolExecutor, as_completed
        results = []
        done    = [0]
        lock    = threading.Lock()
        total   = len(usdt)

        def process(t):
            sym = t["symbol"]
            try:
                k4h = get("/fapi/v1/klines",
                          params={"symbol": sym, "interval": "4h", "limit": 100})
                if not k4h: return None

                result = analyze(k4h)
                if result is None: return None

                return {
                    "symbol":  sym,
                    "base":    sym.replace("USDT", ""),
                    "vol24_m": round(float(t.get("quoteVolume", 0)) / 1_000_000, 1),
                    "chg24":   float(t.get("priceChangePercent", 0)),
                    "score":   result["score"],
                    **result
                }
            except: return None
            finally:
                with lock:
                    done[0] += 1
                    cache["progress"]     = f"Step 2/2 — [{done[0]}/{total}] scanning..."
                    cache["progress_pct"] = int((done[0] / total) * 95)

        with ThreadPoolExecutor(max_workers=20) as ex:
            futures = {ex.submit(process, t): t for t in usdt}
            for f in as_completed(futures, timeout=150):
                try:
                    r = f.result(timeout=15)
                    if r: results.append(r)
                except: pass

        results.sort(key=lambda x: (
            0 if x["signal_type"] == "PULLBACK ENTRY" else
            1 if x["signal_type"] == "JUST CROSSED"   else 2,
            -x["score"]
        ))

        cache["coins"]        = results
        cache["last_scan"]    = time.strftime("%Y-%m-%d %H:%M:%S")
        cache["progress"]     = f"✓ Done — {len(results)} MACD signals found"
        cache["progress_pct"] = 100

    except Exception as e:
        cache["error"]    = str(e)
        cache["progress"] = f"Error: {str(e)[:80]}"
    finally:
        cache["scanning"]     = False
        cache["progress_pct"] = 100

def auto_scan_worker():
    time.sleep(20)
    while True:
        try:
            now = time.time()
            if auto_scan["enabled"] and not cache["scanning"] and now >= auto_scan["next_run"]:
                auto_scan["last_run"] = now
                auto_scan["next_run"] = now + auto_scan["interval"] * 60
                threading.Thread(target=do_scan, daemon=True).start()
        except Exception as e:
            print(f"[AUTO] {e}")
        time.sleep(15)

# ── Routes ─────────────────────────────────────────────────────────────────
@app.route("/")
def index(): return render_template_string(HTML)

@app.route("/api/scan", methods=["POST"])
def api_scan():
    if cache["scanning"]: return jsonify({"status": "already_scanning"})
    threading.Thread(target=do_scan, daemon=True).start()
    return jsonify({"status": "started"})

@app.route("/api/status")
def api_status():
    coins = cache["coins"]
    now   = time.time()
    pullbacks   = [c for c in coins if c["signal_type"] == "PULLBACK ENTRY"]
    crossed     = [c for c in coins if c["signal_type"] == "JUST CROSSED"]
    watching    = [c for c in coins if c["signal_type"] == "WATCH"]
    above_zero  = [c for c in coins if c.get("macd_above_zero")]
    return jsonify({
        "scanning":     cache["scanning"],
        "progress":     cache["progress"],
        "progress_pct": cache["progress_pct"],
        "last_scan":    cache["last_scan"],
        "error":        cache["error"],
        "next_scan_in": max(0, int(auto_scan["next_run"] - now)),
        "coins":        coins[:200],
        "stats": {
            "total":      len(coins),
            "pullbacks":  len(pullbacks),
            "crossed":    len(crossed),
            "watching":   len(watching),
            "above_zero": len(above_zero),
            "high_score": len([c for c in coins if c["score"] >= 70]),
        }
    })

@app.route("/api/autoscan/config", methods=["POST"])
def autoscan_config():
    data = request.get_json() or {}
    if "enabled"  in data: auto_scan["enabled"]  = bool(data["enabled"])
    if "interval" in data:
        auto_scan["interval"] = max(1, int(data["interval"]))
        if auto_scan["last_run"]:
            auto_scan["next_run"] = auto_scan["last_run"] + auto_scan["interval"] * 60
    return jsonify({"status": "saved"})

@app.route("/api/autoscan/runnow", methods=["POST"])
def autoscan_runnow():
    if cache["scanning"]: return jsonify({"status": "already_scanning"})
    auto_scan["next_run"] = time.time() + auto_scan["interval"] * 60
    threading.Thread(target=do_scan, daemon=True).start()
    return jsonify({"status": "started"})

@app.route("/api/chart/<symbol>")
def api_chart(symbol):
    sym = symbol.upper()
    k4h = get("/fapi/v1/klines", params={"symbol": sym, "interval": "4h", "limit": 100})
    if not k4h: return jsonify({"error": "Could not fetch klines"})
    result = analyze(k4h)
    ohlc = [{"t": k[0], "o": float(k[1]), "h": float(k[2]),
              "l": float(k[3]), "c": float(k[4]), "v": float(k[5])}
            for k in k4h]
    return jsonify({
        "symbol": sym,
        "ohlc":   ohlc,
        "result": result,
    })

# ── HTML ───────────────────────────────────────────────────────────────────
HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0">
<title>MACD Scanner</title>
<link href="https://fonts.googleapis.com/css2?family=Outfit:wght@300;400;500;600;700;900&family=DM+Mono:wght@300;400;500&display=swap" rel="stylesheet">
<style>
:root{--bg:#070a0f;--bg2:#0c0f18;--bg3:#111520;--border:#1a1f30;
  --blue:#4d9fff;--green:#00e5a0;--red:#ff4d6d;--gold:#f0b429;--purple:#a78bfa;
  --text:#e2e8f8;--muted:#4a5578;--card:#0c0f17;}
*{margin:0;padding:0;box-sizing:border-box;}
body{background:var(--bg);color:var(--text);font-family:'DM Mono',monospace;min-height:100vh;}
body::before{content:'';position:fixed;inset:0;
  background:radial-gradient(ellipse at 10% 30%,rgba(77,159,255,0.04) 0%,transparent 55%),
             radial-gradient(ellipse at 90% 70%,rgba(0,229,160,0.03) 0%,transparent 50%);
  pointer-events:none;}

header{padding:16px 28px;border-bottom:1px solid var(--border);
  display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;
  background:rgba(7,10,15,.97);backdrop-filter:blur(12px);position:sticky;top:0;z-index:100;}
.logo{font-family:'Outfit',sans-serif;font-weight:900;font-size:20px;letter-spacing:-0.5px;}
.logo span{color:var(--blue);}
.logo sub{font-size:10px;color:var(--muted);font-weight:400;letter-spacing:2px;margin-left:8px;vertical-align:middle;}
.hright{display:flex;align-items:center;gap:8px;flex-wrap:wrap;}
.status-chip{display:flex;align-items:center;gap:6px;font-size:10px;color:var(--muted);
  background:var(--bg3);border:1px solid var(--border);padding:6px 12px;border-radius:20px;}
.pulse{width:6px;height:6px;border-radius:50%;background:var(--green);
  box-shadow:0 0 6px var(--green);animation:p 2s infinite;}
@keyframes p{0%,100%{opacity:1}50%{opacity:.2}}
.btn{font-family:'DM Mono',monospace;font-size:11px;font-weight:500;letter-spacing:1.5px;
  text-transform:uppercase;padding:8px 18px;border-radius:6px;border:none;cursor:pointer;transition:all .2s;}
.btn-primary{background:var(--blue);color:#fff;}
.btn-primary:hover{background:#3d8fff;box-shadow:0 0 16px rgba(77,159,255,0.35);}
.btn-primary:disabled{opacity:.4;cursor:not-allowed;}

#prog-wrap{display:none;padding:0 28px;border-bottom:1px solid var(--border);background:var(--bg2);}
.prog-row{display:flex;align-items:center;gap:12px;padding:9px 0;}
.prog-label{font-size:10px;color:var(--muted);letter-spacing:1px;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;}
.prog-track{width:100px;height:2px;background:var(--border);border-radius:1px;overflow:hidden;flex-shrink:0;}
.prog-fill{height:100%;background:linear-gradient(90deg,var(--blue),var(--green));border-radius:1px;transition:width .3s;width:0%;}
.prog-fill.ind{width:25%;animation:ind 1s ease-in-out infinite;}
@keyframes ind{0%{transform:translateX(-300%)}100%{transform:translateX(700%)}}

.stats{display:grid;grid-template-columns:repeat(auto-fit,minmax(120px,1fr));gap:1px;
  background:var(--border);border-bottom:1px solid var(--border);}
.stat{background:var(--bg2);padding:13px 18px;cursor:pointer;transition:background .15s;user-select:none;}
.stat:hover{background:var(--bg3);}
.stat.active{background:rgba(77,159,255,0.08);border-bottom:2px solid var(--blue);}
.stat-lbl{font-size:9px;color:var(--muted);text-transform:uppercase;letter-spacing:2px;margin-bottom:5px;}
.stat-val{font-family:'Outfit',sans-serif;font-size:26px;font-weight:700;line-height:1;}
.g{color:var(--green)}.b{color:var(--blue)}.r{color:var(--red)}.gold{color:var(--gold)}.grey{color:var(--muted);font-size:14px!important;}

#alert-box{display:none;padding:9px 28px;font-size:11px;color:var(--blue);
  background:rgba(77,159,255,0.05);border-bottom:1px solid rgba(77,159,255,0.15);}

.filters{padding:11px 28px;display:flex;gap:14px;flex-wrap:wrap;align-items:center;
  border-bottom:1px solid var(--border);background:var(--bg2);}
.fl{font-size:9px;color:var(--muted);text-transform:uppercase;letter-spacing:2px;}
.fg{display:flex;gap:5px;flex-wrap:wrap;}
.fc{font-family:'DM Mono',monospace;font-size:10px;background:transparent;
  border:1px solid var(--border);color:var(--muted);padding:4px 10px;border-radius:4px;
  cursor:pointer;transition:all .15s;text-transform:uppercase;letter-spacing:.5px;}
.fc:hover,.fc.on{border-color:var(--blue);color:var(--blue);background:rgba(77,159,255,0.06);}

.auto-wrap{display:flex;align-items:center;gap:8px;background:var(--bg3);
  border:1px solid var(--border);border-radius:6px;padding:6px 12px;}
.countdown{font-size:10px;color:var(--muted);background:var(--bg3);
  border:1px solid var(--border);padding:6px 12px;border-radius:6px;
  font-family:'DM Mono',monospace;letter-spacing:1px;min-width:90px;text-align:center;}

.tw{padding:18px 28px;overflow-x:auto;}
.tw::-webkit-scrollbar{height:4px;}
.tw::-webkit-scrollbar-track{background:var(--bg);}
.tw::-webkit-scrollbar-thumb{background:var(--border);border-radius:2px;}
.tw::-webkit-scrollbar-thumb:hover{background:var(--muted);}
.ttl{font-family:'Outfit',sans-serif;font-size:13px;font-weight:700;color:var(--muted);
  text-transform:uppercase;letter-spacing:3px;margin-bottom:12px;
  display:flex;align-items:center;justify-content:space-between;}
.rc{font-family:'DM Mono',monospace;font-size:10px;font-weight:400;}
table{width:100%;border-collapse:collapse;min-width:1100px;}
thead tr{border-bottom:1px solid var(--border);}
th{font-size:9px;color:var(--muted);text-transform:uppercase;letter-spacing:1px;
  padding:6px 8px;text-align:left;white-space:nowrap;}
tbody tr{border-bottom:1px solid rgba(26,31,48,0.5);cursor:pointer;transition:background .1s;}
tbody tr:hover{background:rgba(77,159,255,0.025);}
td{padding:8px 8px;font-size:11px;white-space:nowrap;}
.pname{font-family:'Outfit',sans-serif;font-weight:700;font-size:15px;}
.psub{font-size:9px;color:var(--muted);margin-top:2px;}

.score{display:inline-flex;align-items:center;justify-content:center;
  min-width:40px;height:22px;padding:0 7px;border-radius:4px;
  font-family:'Outfit',sans-serif;font-weight:700;font-size:13px;}
.s-hot {background:rgba(240,180,41,0.15);color:var(--gold);border:1px solid rgba(240,180,41,0.35);}
.s-good{background:rgba(0,229,160,0.1);color:var(--green);border:1px solid rgba(0,229,160,0.25);}
.s-watch{background:rgba(77,159,255,0.1);color:var(--blue);border:1px solid rgba(77,159,255,0.2);}
.s-low {background:rgba(74,85,120,0.1);color:var(--muted);border:1px solid var(--border);}

/* Signal badges */
.sig-badge{display:inline-block;padding:3px 8px;border-radius:4px;font-size:9px;
  font-weight:700;letter-spacing:.5px;text-transform:uppercase;}
.sig-pullback{background:rgba(240,180,41,0.15);color:var(--gold);border:1px solid rgba(240,180,41,0.3);}
.sig-crossed {background:rgba(0,229,160,0.12);color:var(--green);border:1px solid rgba(0,229,160,0.25);}
.sig-watch   {background:rgba(77,159,255,0.1);color:var(--blue);border:1px solid rgba(77,159,255,0.2);}

/* Histogram mini bars */
.hist-bars{display:flex;align-items:flex-end;gap:2px;height:24px;}
.hist-bar{width:6px;border-radius:1px;}

/* MACD gap indicator */
.gap-bar{display:flex;align-items:center;gap:5px;font-size:10px;}

.tag{display:inline-block;font-size:8px;padding:2px 5px;border-radius:3px;
  text-transform:uppercase;letter-spacing:.5px;margin-right:2px;cursor:help;position:relative;}
.t-green{background:rgba(0,229,160,0.08);color:var(--green);border:1px solid rgba(0,229,160,0.2);}
.t-gold {background:rgba(240,180,41,0.08);color:var(--gold);border:1px solid rgba(240,180,41,0.2);}
.t-blue {background:rgba(77,159,255,0.08);color:var(--blue);border:1px solid rgba(77,159,255,0.2);}
.t-red  {background:rgba(255,77,109,0.08);color:var(--red);border:1px solid rgba(255,77,109,0.2);}
.tag::after{content:attr(data-tip);position:absolute;bottom:calc(100% + 7px);left:50%;
  transform:translateX(-50%);background:#0a0c16;color:var(--text);
  font-size:11px;font-family:'DM Mono',monospace;padding:8px 12px;border-radius:4px;
  border:1px solid var(--border);white-space:normal;width:220px;line-height:1.5;
  text-transform:none;letter-spacing:0;z-index:999;opacity:0;pointer-events:none;transition:opacity .15s;}
.tag:hover::after{opacity:1;}

.score-tip{cursor:help;position:relative;}
.score-tip::after{content:attr(data-tip);position:absolute;bottom:calc(100% + 7px);
  left:50%;transform:translateX(-50%);background:#0a0c16;color:var(--text);
  font-size:10px;font-family:'DM Mono',monospace;padding:10px 14px;border-radius:4px;
  border:1px solid var(--border);white-space:normal;width:280px;line-height:1.7;
  z-index:999;opacity:0;pointer-events:none;transition:opacity .15s;}
.score-tip:hover::after{opacity:1;}

.reasons{font-size:8px;color:var(--muted);margin-top:3px;white-space:normal;max-width:180px;line-height:1.5;}
.empty{text-align:center;padding:80px;color:var(--muted);}
.empty-icon{font-size:36px;margin-bottom:12px;opacity:.3;}
footer{padding:12px 28px;border-top:1px solid var(--border);font-size:10px;color:var(--muted);
  display:flex;justify-content:space-between;flex-wrap:wrap;gap:6px;}
::-webkit-scrollbar{width:3px;height:3px;}
::-webkit-scrollbar-track{background:var(--bg);}
::-webkit-scrollbar-thumb{background:var(--border);}

/* Chart Modal */
#chart-modal{display:none;position:fixed;inset:0;z-index:9000;
  background:rgba(0,0,0,0.88);backdrop-filter:blur(4px);
  align-items:center;justify-content:center;}
.modal-box{background:var(--bg2);border:1px solid var(--border);border-radius:8px;
  width:94vw;max-width:1050px;max-height:92vh;overflow:hidden;display:flex;flex-direction:column;}
.modal-hdr{display:flex;align-items:center;justify-content:space-between;
  padding:14px 20px;border-bottom:1px solid var(--border);}
.modal-body{padding:16px 20px;flex:1;overflow:hidden;}
.modal-ftr{padding:10px 20px;border-top:1px solid var(--border);
  font-size:10px;color:var(--muted);display:flex;gap:16px;flex-wrap:wrap;}
.close-btn{font-family:'DM Mono',monospace;font-size:11px;background:var(--bg3);
  color:var(--muted);border:1px solid var(--border);padding:6px 14px;border-radius:4px;cursor:pointer;}
</style>
</head>
<body>

<header>
  <div class="logo">MACD<span>Scan</span><sub>4H CROSSOVER SCANNER</sub></div>
  <div class="hright">
    <div class="status-chip"><div class="pulse"></div><span id="st">READY</span></div>
    <div class="auto-wrap">
      <span style="font-size:10px;color:var(--muted);letter-spacing:1px;">AUTO</span>
      <div id="auto-track" onclick="toggleAuto()"
        style="position:relative;width:36px;height:20px;background:var(--blue);
               border-radius:10px;cursor:pointer;transition:.2s;flex-shrink:0;">
        <div id="auto-thumb"
          style="position:absolute;top:2px;left:18px;width:16px;height:16px;
                 background:#fff;border-radius:50%;transition:.2s;"></div>
      </div>
      <select id="auto-interval" onchange="setInterval2(this.value)"
        style="background:transparent;border:none;color:var(--text);
               font-family:'DM Mono',monospace;font-size:10px;cursor:pointer;outline:none;">
        <option value="5">5 min</option>
        <option value="10">10 min</option>
        <option value="15" selected>15 min</option>
        <option value="30">30 min</option>
      </select>
    </div>
    <div class="countdown" id="countdown">NEXT: —</div>
    <button class="btn btn-primary" id="scanBtn" onclick="manualScan()">⚡ SCAN NOW</button>
  </div>
</header>

<div id="prog-wrap">
  <div class="prog-row">
    <span class="prog-label" id="prog-label">Ready</span>
    <div class="prog-track"><div class="prog-fill" id="prog-fill"></div></div>
  </div>
</div>

<div class="stats">
  <div class="stat" onclick="statFilter('all',this)"><div class="stat-lbl">Signals Found</div><div class="stat-val g" id="s-total">—</div></div>
  <div class="stat" onclick="statFilter('pullback',this)"><div class="stat-lbl">🎯 Pullback Entry</div><div class="stat-val gold" id="s-pullback">—</div></div>
  <div class="stat" onclick="statFilter('crossed',this)"><div class="stat-lbl">⚡ Just Crossed</div><div class="stat-val g" id="s-crossed">—</div></div>
  <div class="stat" onclick="statFilter('watch',this)"><div class="stat-lbl">🔀 Watch</div><div class="stat-val b" id="s-watch">—</div></div>
  <div class="stat" onclick="statFilter('above_zero',this)"><div class="stat-lbl">☀ Above Zero</div><div class="stat-val g" id="s-zero">—</div></div>
  <div class="stat" onclick="statFilter('high_score',this)"><div class="stat-lbl">🔥 Score ≥70</div><div class="stat-val gold" id="s-high">—</div></div>
  <div class="stat"><div class="stat-lbl">Last Scan</div><div class="stat-val grey" id="s-time">—</div></div>
</div>

<div id="alert-box"></div>

<div class="filters">
  <span class="fl">Signal:</span>
  <div class="fg" id="fg1">
    <button class="fc on" onclick="setF('sig','all',this)">ALL</button>
    <button class="fc" onclick="setF('sig','pullback',this)">🎯 Pullback</button>
    <button class="fc" onclick="setF('sig','crossed',this)">⚡ Crossed</button>
    <button class="fc" onclick="setF('sig','watch',this)">🔀 Watch</button>
  </div>
  <span class="fl">Zero Line:</span>
  <div class="fg" id="fg2">
    <button class="fc on" onclick="setF('zero','all',this)">ALL</button>
    <button class="fc" onclick="setF('zero','above',this)">Above Zero ☀</button>
    <button class="fc" onclick="setF('zero','below',this)">Below Zero</button>
  </div>
  <span class="fl">Score:</span>
  <div class="fg" id="fg3">
    <button class="fc on" onclick="setF('score',0,this)">ALL</button>
    <button class="fc" onclick="setF('score',50,this)">50+</button>
    <button class="fc" onclick="setF('score',70,this)">70+ 🔥</button>
  </div>
  <span class="fl">Sort:</span>
  <div class="fg" id="fg4">
    <button class="fc on" onclick="setF('sort','signal',this)">SIGNAL ▼</button>
    <button class="fc" onclick="setF('sort','score',this)">SCORE</button>
    <button class="fc" onclick="setF('sort','pullback',this)">PULLBACK%</button>
    <button class="fc" onclick="setF('sort','vol',this)">VOLUME</button>
  </div>
</div>

<div class="tw">
  <div class="ttl">MACD SIGNALS — 4H <span class="rc" id="rc"></span>
    <span style="font-size:9px;color:var(--muted);font-weight:400;letter-spacing:1px;">← scroll →</span>
  </div>
  <table>
    <thead>
      <tr>
        <th>#</th><th>PAIR</th><th>PRICE</th>
        <th>4H%</th><th>24H%</th>
        <th>SIGNAL</th>
        <th>HISTOGRAM</th><th>ZERO</th>
        <th>CROSS</th><th>PULLBACK%</th>
        <th>RSI</th><th>MA50</th><th>VOL</th>
        <th>SCORE</th><th>TAGS</th>
      </tr>
    </thead>
    <tbody id="tb">
      <tr><td colspan="15">
        <div class="empty"><div class="empty-icon">📈</div>
        <div>Click SCAN NOW — Scans 300 pairs for MACD crossovers on 4H</div></div>
      </td></tr>
    </tbody>
  </table>
</div>

<footer>
  <span>MACDScan · 4H MACD(12,26,9) · Pullback Entry · Just Crossed · Watch · Pure Technical</span>
  <span id="ft"></span>
</footer>

<!-- Chart Modal -->
<div id="chart-modal" style="display:none;position:fixed;inset:0;z-index:9000;
  background:rgba(0,0,0,0.88);backdrop-filter:blur(4px);align-items:center;justify-content:center;">
  <div class="modal-box">
    <div class="modal-hdr">
      <div>
        <span id="chart-title" style="font-family:'Outfit',sans-serif;font-weight:700;font-size:18px;"></span>
        <span id="chart-sig" style="margin-left:12px;font-size:11px;color:var(--muted);"></span>
      </div>
      <div style="display:flex;align-items:center;gap:10px;">
        <span id="chart-price" style="font-family:'Outfit',sans-serif;font-weight:700;font-size:16px;color:var(--green);"></span>
        <button class="close-btn" onclick="closeChart()">✕ CLOSE</button>
      </div>
    </div>
    <div class="modal-body">
      <canvas id="price-canvas" style="width:100%;display:block;margin-bottom:8px;"></canvas>
      <canvas id="macd-canvas"  style="width:100%;display:block;"></canvas>
    </div>
    <div class="modal-ftr">
      <span><span style="color:var(--blue)">—</span> MACD Line</span>
      <span><span style="color:var(--gold)">—</span> Signal Line</span>
      <span><span style="color:var(--green)">■</span> Positive Histogram</span>
      <span><span style="color:var(--red)">■</span> Negative Histogram</span>
      <span><span style="color:var(--muted)">- -</span> Zero Line</span>
    </div>
  </div>
</div>

<script>
let coins=[], filt={sig:'all',zero:'all',score:0,sort:'signal'}, sortDesc=true;
let scanPoll=null, autoOn=true;

// ── Auto Scan ─────────────────────────────────────────────────────────────
function toggleAuto(){
  autoOn=!autoOn;
  document.getElementById('auto-track').style.background=autoOn?'var(--blue)':'var(--border)';
  document.getElementById('auto-thumb').style.left=autoOn?'18px':'2px';
  document.getElementById('auto-thumb').style.background=autoOn?'#fff':'var(--muted)';
  fetch('/api/autoscan/config',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({enabled:autoOn,interval:parseInt(document.getElementById('auto-interval').value)||15})});
}
function setInterval2(v){
  fetch('/api/autoscan/config',{method:'POST',headers:{'Content-Type':'application/json'},
    body:JSON.stringify({enabled:autoOn,interval:parseInt(v)})});
}
function updateCountdown(s){
  const el=document.getElementById('countdown');
  if(!autoOn){el.textContent='AUTO: OFF';el.style.color='var(--muted)';return;}
  if(s<=0){el.textContent='SCANNING...';el.style.color='var(--blue)';return;}
  const m=Math.floor(s/60),sec=s%60;
  el.textContent=`NEXT: ${m}:${sec.toString().padStart(2,'0')}`;
  el.style.color=s<60?'var(--blue)':'var(--muted)';
}

// ── Scan ──────────────────────────────────────────────────────────────────
function manualScan(){
  if(scanPoll) return;
  fetch('/api/autoscan/runnow',{method:'POST'}).then(r=>r.json()).then(d=>{
    if(d.status==='started') startPolling();
  }).catch(()=>{});
}
function startPolling(){
  if(scanPoll) return;
  document.getElementById('scanBtn').disabled=true;
  document.getElementById('scanBtn').textContent='⏳ SCANNING...';
  document.getElementById('prog-wrap').style.display='block';
  document.getElementById('prog-fill').style.width='0%';
  document.getElementById('prog-fill').classList.add('ind');
  document.getElementById('prog-label').textContent='Connecting to Binance...';
  document.getElementById('prog-label').style.color='';
  document.getElementById('alert-box').style.display='none';
  scanPoll=setInterval(pollStatus,1000);
}
function stopPolling(){
  clearInterval(scanPoll); scanPoll=null;
  document.getElementById('scanBtn').disabled=false;
  document.getElementById('scanBtn').textContent='⚡ SCAN NOW';
  setTimeout(()=>{
    document.getElementById('prog-wrap').style.display='none';
    document.getElementById('prog-fill').style.width='0%';
    document.getElementById('prog-fill').classList.remove('ind');
  },2000);
}
function pollStatus(){
  fetch('/api/status').then(r=>r.json()).then(d=>{
    const pl=document.getElementById('prog-label');
    pl.textContent=d.error?'✗ '+(d.error||'').slice(0,100):(d.progress||'');
    pl.style.color=d.error?'var(--red)':'';
    document.getElementById('st').textContent=d.scanning?'SCANNING':'LIVE';
    if(d.progress_pct>0){
      document.getElementById('prog-fill').classList.remove('ind');
      document.getElementById('prog-fill').style.width=d.progress_pct+'%';
    }
    updateCountdown(d.next_scan_in||0);
    if(!d.scanning&&d.coins&&d.coins.length>0){
      stopPolling(); coins=d.coins;
      updateStats(d.stats,d.last_scan);
      showAlert(d.coins); render();
    }
    if(d.error&&!d.scanning) stopPolling();
  }).catch(()=>{});
}
setInterval(()=>{
  if(scanPoll) return;
  fetch('/api/status').then(r=>r.json()).then(d=>{
    updateCountdown(d.next_scan_in||0);
    if(d.scanning){startPolling();return;}
    if(d.last_scan&&d.coins&&d.coins.length>0){
      const nt=d.last_scan.slice(11),ct=document.getElementById('s-time').textContent;
      if(nt!==ct){coins=d.coins;updateStats(d.stats,d.last_scan);showAlert(d.coins);render();}
    }
  }).catch(()=>{});
},5000);

function updateStats(st,ls){
  if(!st) return;
  document.getElementById('s-total').textContent=st.total;
  document.getElementById('s-pullback').textContent=st.pullbacks;
  document.getElementById('s-crossed').textContent=st.crossed;
  document.getElementById('s-watch').textContent=st.watching;
  document.getElementById('s-zero').textContent=st.above_zero;
  document.getElementById('s-high').textContent=st.high_score;
  document.getElementById('s-time').textContent=ls?ls.slice(11):'—';
  document.getElementById('ft').textContent='Last scan: '+(ls||'—');
}
function showAlert(ca){
  const hot=ca.filter(c=>c.signal_type==='PULLBACK ENTRY'&&c.score>=65);
  const ab=document.getElementById('alert-box');
  if(hot.length){
    ab.style.display='block';
    ab.innerHTML='🎯 <strong>'+hot.length+' PULLBACK ENTRY'+(hot.length>1?'S':'')+' DETECTED:</strong> '
      +hot.slice(0,8).map(c=>
        `<a href="https://www.binance.com/en/futures/${c.symbol}" target="_blank"
           onclick="event.stopPropagation()"
           style="color:var(--gold);text-decoration:none;font-weight:700;
                  background:rgba(240,180,41,0.1);border:1px solid rgba(240,180,41,0.3);
                  padding:2px 8px;border-radius:3px;margin:0 2px;display:inline-block;"
           onmouseover="this.style.background='rgba(240,180,41,0.25)'"
           onmouseout="this.style.background='rgba(240,180,41,0.1)'"
         >${c.base} <span style="font-size:9px;color:var(--green)">${c.pullback_pct?.toFixed(1)}%↓</span></a>`
      ).join(' ');
  } else ab.style.display='none';
}

// ── Render ────────────────────────────────────────────────────────────────
function render(){
  let data=[...coins];
  if(filt.sig==='pullback')    data=data.filter(c=>c.signal_type==='PULLBACK ENTRY');
  if(filt.sig==='crossed')     data=data.filter(c=>c.signal_type==='JUST CROSSED');
  if(filt.sig==='watch')       data=data.filter(c=>c.signal_type==='WATCH');
  if(filt.zero==='above')      data=data.filter(c=>c.macd_above_zero);
  if(filt.zero==='below')      data=data.filter(c=>!c.macd_above_zero);
  if(filt.score>0)             data=data.filter(c=>c.score>=filt.score);

  data.sort((a,b)=>{
    if(filt.sort==='signal'){
      const order={PULLBACK_ENTRY:0,'JUST CROSSED':1,WATCH:2};
      const ao=order[a.signal_type?.replace(' ','_')]??3;
      const bo=order[b.signal_type?.replace(' ','_')]??3;
      if(ao!==bo) return ao-bo;
      return b.score-a.score;
    }
    const av=filt.sort==='score'?a.score:filt.sort==='pullback'?(a.pullback_pct||0):filt.sort==='vol'?(a.vol24_m||0):a.score;
    const bv=filt.sort==='score'?b.score:filt.sort==='pullback'?(b.pullback_pct||0):filt.sort==='vol'?(b.vol24_m||0):b.score;
    return sortDesc?bv-av:av-bv;
  });

  document.getElementById('rc').textContent=data.length+' SIGNALS';
  if(!data.length){
    document.getElementById('tb').innerHTML='<tr><td colspan="15"><div class="empty"><div class="empty-icon">🔍</div><div>No signals match filters</div></div></td></tr>';
    return;
  }

  const fmt=p=>p==null?'—':p<0.00001?p.toFixed(8):p<0.001?p.toFixed(6):p<0.1?p.toFixed(5):p<1?p.toFixed(4):p<10?p.toFixed(3):p<1000?p.toFixed(2):p.toFixed(0);
  const fmtM=p=>p==null?'—':p<0.00001?p.toFixed(8):p<0.001?p.toFixed(6):p<0.1?p.toFixed(5):p<1?p.toFixed(5):p<10?p.toFixed(4):p<1000?p.toFixed(3):p.toFixed(0);
  const pct=v=>v==null?'<span style="color:var(--muted)">—</span>':
    `<span style="color:${Math.abs(v)<0.3?'var(--muted)':v>0?'var(--green)':'var(--red)'}">${v>0?'+':''}${v.toFixed(2)}%</span>`;
  const rsiC=v=>v==null?'var(--muted)':v<35?'var(--gold)':v<50?'var(--green)':v<65?'var(--text)':v<75?'var(--blue)':'var(--red)';

  document.getElementById('tb').innerHTML=data.slice(0,100).map((c,i)=>{
    const sc=c.score>=70?'s-hot':c.score>=50?'s-good':c.score>=35?'s-watch':'s-low';

    const sigBadge=
      c.signal_type==='PULLBACK ENTRY'?'<span class="sig-badge sig-pullback">🎯 PULLBACK ENTRY</span>':
      c.signal_type==='JUST CROSSED'  ?'<span class="sig-badge sig-crossed">⚡ JUST CROSSED</span>':
                                        '<span class="sig-badge sig-watch">🔀 WATCH</span>';

    const macdColor=c.macd>0?'var(--green)':'var(--red)';
    const histColor=c.histogram>0?'var(--green)':'var(--red)';
    const histTrend=c.hist_growing?'▲':c.histogram>c.hist_prev?'↑':'—';

    const zeroBadge=c.macd_above_zero
      ?'<span style="color:var(--green);font-size:10px">☀ ABOVE</span>'
      :'<span style="color:var(--muted);font-size:10px">☁ BELOW</span>';

    const crossCell=c.cross_bar
      ?`<span style="color:${c.cross_bar<=2?'var(--green)':c.cross_bar<=5?'var(--gold)':'var(--muted)'};">${c.cross_bar}H ago</span>`
      :'<span style="color:var(--muted)">—</span>';

    const pullbackCell=c.pullback_pct
      ?`<span style="color:${c.pullback_pct<=4?'var(--gold)':'var(--muted)'}">${c.pullback_pct.toFixed(1)}%</span>`
      :'<span style="color:var(--muted)">—</span>';

    const ma50Cell=c.ma50
      ?`<span style="color:${c.above_ma50?'var(--green)':'var(--red)'}">${c.above_ma50?'↑ Above':'↓ Below'}</span>`
      :'—';

    const rv=c.rel_vol!=null
      ?`<span style="color:${c.rel_vol>=1.5?'var(--green)':c.rel_vol>=1.2?'var(--gold)':'var(--muted)'}">${c.rel_vol.toFixed(2)}x</span>`
      :'—';

    const tags=[
      c.macd_above_zero    ?'<span class="tag t-green" data-tip="MACD line above zero — strong bullish territory">☀ ABOVE ZERO</span>':'',
      c.hist_growing       ?'<span class="tag t-green" data-tip="Histogram bars growing — momentum accelerating">📊 HIST↑</span>':'',
      c.vol_confirm        ?'<span class="tag t-blue" data-tip="Volume above 1.2x average — institutions participating">🔊 VOL OK</span>':'',
      c.above_ma50         ?'<span class="tag t-green" data-tip="Price above MA50 — trend aligned with signal">MA50↑</span>':'',
      c.pullback_valid     ?'<span class="tag t-gold" data-tip="Price pulled back 1.5-7% after MACD cross — ideal entry zone">🎯 PULLBACK</span>':'',
      c.hist_recovering    ?'<span class="tag t-blue" data-tip="Histogram recovering from lows — momentum turning bullish">📈 RECOVERING</span>':'',
      (c.rsi14&&c.rsi14>70)?'<span class="tag t-red" data-tip="RSI overbought — wait for pullback">⚠ RSI OB</span>':'',
    ].filter(Boolean).join('');

    const tipText=(c.reasons||[]).filter(r=>!r.startsWith('⚠')).join(' | ');

    return `<tr onclick="openChart('${c.symbol}','${c.signal_type||''}')">
      <td style="color:var(--muted);font-size:10px">${i+1}</td>
      <td><div class="pname">${c.base}/USDT</div><div class="psub">PERP · $${c.vol24_m}M</div></td>
      <td>${fmt(c.price)}</td>
      <td>${pct(c.chg_4h)}</td>
      <td>${pct(c.chg_24h)}</td>
      <td>${sigBadge}</td>
      <td style="color:${histColor};font-size:10px">${fmtM(c.histogram)} ${histTrend}</td>
      <td>${zeroBadge}</td>
      <td>${crossCell}</td>
      <td>${pullbackCell}</td>
      <td><span style="color:${rsiC(c.rsi14)}">${c.rsi14!=null?c.rsi14.toFixed(1):'—'}</span></td>
      <td>${ma50Cell}</td>
      <td>${rv}</td>
      <td><span class="score ${sc} score-tip" data-tip="${tipText}">${c.score}</span>
          <div class="reasons">${(c.reasons||[]).filter(r=>!r.startsWith('⚠')).slice(0,2).join(' · ')}</div></td>
      <td>${tags||'<span style="color:var(--muted);font-size:9px">—</span>'}</td>
    </tr>`;
  }).join('');
}

// ── Filters ───────────────────────────────────────────────────────────────
function setF(type,val,el){
  if(type==='sort'){
    if(filt.sort===val) sortDesc=!sortDesc; else{filt.sort=val;sortDesc=true;}
    document.getElementById('fg4').querySelectorAll('.fc').forEach(c=>{
      c.classList.remove('on');c.textContent=c.textContent.replace(' ▼','').replace(' ▲','');
    });
    el.classList.add('on');
    el.textContent=el.textContent.trim()+(sortDesc?' ▼':' ▲');
  } else {
    filt[type]=val;
    const g={sig:'fg1',zero:'fg2',score:'fg3'}[type];
    if(g){document.getElementById(g).querySelectorAll('.fc').forEach(c=>c.classList.remove('on'));el.classList.add('on');}
  }
  if(coins.length) render();
}
function statFilter(type,el){
  document.querySelectorAll('.stat').forEach(s=>s.classList.remove('active'));
  if(type!=='all') el.classList.add('active');
  filt.sig='all'; filt.zero='all'; filt.score=0;
  if(type==='pullback') filt.sig='pullback';
  else if(type==='crossed') filt.sig='crossed';
  else if(type==='watch') filt.sig='watch';
  else if(type==='above_zero') filt.zero='above';
  else if(type==='high_score') filt.score=70;
  if(coins.length) render();
}

// ── Chart ─────────────────────────────────────────────────────────────────
function openChart(sym, sigType){
  document.getElementById('chart-modal').style.display='flex';
  document.getElementById('chart-title').textContent=sym.replace('USDT','/USDT');
  document.getElementById('chart-sig').textContent=sigType;
  document.getElementById('chart-price').textContent='Loading...';
  fetch('/api/chart/'+sym).then(r=>r.json()).then(d=>{
    if(d.error){document.getElementById('chart-price').textContent='Error';return;}
    document.getElementById('chart-price').textContent=d.result?.price||'';
    drawPriceChart(d);
    drawMACDChart(d);
  }).catch(()=>{});
}
function closeChart(){
  document.getElementById('chart-modal').style.display='none';
}
document.getElementById('chart-modal').addEventListener('click',function(e){if(e.target===this)closeChart();});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeChart();});

function drawPriceChart(d){
  const canvas=document.getElementById('price-canvas');
  const W=canvas.parentElement.offsetWidth-40;
  const H=180; canvas.width=W; canvas.height=H;
  const ctx=canvas.getContext('2d');
  ctx.clearRect(0,0,W,H);

  const ohlc=d.ohlc||[];
  if(!ohlc.length) return;
  const data=ohlc.slice(-60);
  const n=data.length;
  const pad={l:8,r:60,t:10,b:20};
  const cW=W-pad.l-pad.r, cH=H-pad.t-pad.b;

  let minP=Math.min(...data.map(c=>c.l));
  let maxP=Math.max(...data.map(c=>c.h));
  const range=maxP-minP||1;
  const xS=i=>pad.l+(i/(n-1))*cW;
  const yS=p=>pad.t+(1-(p-minP)/range)*cH;

  // Grid
  ctx.strokeStyle='rgba(26,31,48,0.8)'; ctx.lineWidth=1;
  for(let i=0;i<=3;i++){
    const y=pad.t+(i/3)*cH;
    ctx.beginPath();ctx.moveTo(pad.l,y);ctx.lineTo(W-pad.r,y);ctx.stroke();
    const pr=maxP-(i/3)*range;
    ctx.fillStyle='#4a5578';ctx.font='9px DM Mono,monospace';ctx.textAlign='left';
    ctx.fillText(pr<1?pr.toFixed(5):pr.toFixed(2),W-pad.r+4,y+3);
  }

  // MA50 line
  if(d.result?.ma50){
    const y=yS(d.result.ma50);
    ctx.strokeStyle='rgba(77,159,255,0.5)';ctx.lineWidth=1;ctx.setLineDash([4,3]);
    ctx.beginPath();ctx.moveTo(pad.l,y);ctx.lineTo(W-pad.r,y);ctx.stroke();
    ctx.setLineDash([]);
    ctx.fillStyle='rgba(77,159,255,0.8)';ctx.font='8px DM Mono,monospace';ctx.textAlign='left';
    ctx.fillText('MA50',W-pad.r+4,y-2);
  }

  // Mark cross bar
  const cb=d.result?.cross_bar;
  if(cb&&cb<n){
    const xi=xS(n-1-cb);
    ctx.fillStyle='rgba(0,229,160,0.1)';
    ctx.fillRect(xi-6,pad.t,12,cH);
    ctx.fillStyle='rgba(0,229,160,0.8)';ctx.font='8px DM Mono,monospace';ctx.textAlign='center';
    ctx.fillText('X',xi,pad.t+10);
  }

  // Candles
  const bW=Math.max(1,cW/n*0.7);
  data.forEach((c,i)=>{
    const x=xS(i),op=yS(c.o),cl=yS(c.c),hi=yS(c.h),lo=yS(c.l);
    const bull=c.c>=c.o;
    ctx.strokeStyle=bull?'#00e5a0':'#ff4d6d';ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(x,hi);ctx.lineTo(x,lo);ctx.stroke();
    ctx.fillStyle=bull?'rgba(0,229,160,0.85)':'rgba(255,77,109,0.85)';
    ctx.fillRect(x-bW/2,Math.min(op,cl),bW,Math.max(1,Math.abs(cl-op)));
  });

  // Current price line
  const cy=yS(d.result?.price||data[data.length-1].c);
  ctx.strokeStyle='rgba(255,255,255,0.4)';ctx.lineWidth=1;ctx.setLineDash([3,3]);
  ctx.beginPath();ctx.moveTo(pad.l,cy);ctx.lineTo(W-pad.r,cy);ctx.stroke();
  ctx.setLineDash([]);
}

function drawMACDChart(d){
  const canvas=document.getElementById('macd-canvas');
  const W=canvas.parentElement.offsetWidth-40;
  const H=120; canvas.width=W; canvas.height=H;
  const ctx=canvas.getContext('2d');
  ctx.clearRect(0,0,W,H);
  if(!d.result) return;

  const macdS =d.result.macd_series||[];
  const sigS  =d.result.signal_series||[];
  const histS =d.result.hist_series||[];
  if(!macdS.length) return;

  const n=macdS.length;
  const pad={l:8,r:60,t:8,b:20};
  const cW=W-pad.l-pad.r, cH=H-pad.t-pad.b;

  const allVals=[...macdS,...sigS,...histS];
  let minV=Math.min(...allVals), maxV=Math.max(...allVals);
  const range=(maxV-minV)||1;
  const xS=i=>pad.l+(i/(n-1))*cW;
  const yS=v=>pad.t+(1-(v-minV)/range)*cH;

  // Zero line
  const zy=yS(0);
  ctx.strokeStyle='rgba(74,85,120,0.6)';ctx.lineWidth=1;ctx.setLineDash([4,3]);
  ctx.beginPath();ctx.moveTo(pad.l,zy);ctx.lineTo(W-pad.r,zy);ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle='rgba(74,85,120,0.7)';ctx.font='8px DM Mono,monospace';ctx.textAlign='left';
  ctx.fillText('0',W-pad.r+4,zy+3);

  // Histogram
  const bW=Math.max(1,cW/n*0.6);
  histS.forEach((v,i)=>{
    const x=xS(i),y=yS(v),z=yS(0);
    ctx.fillStyle=v>=0?'rgba(0,229,160,0.6)':'rgba(255,77,109,0.6)';
    ctx.fillRect(x-bW/2,Math.min(y,z),bW,Math.max(1,Math.abs(y-z)));
  });

  // Signal line
  ctx.strokeStyle='rgba(240,180,41,0.85)';ctx.lineWidth=1.5;
  ctx.beginPath();
  sigS.forEach((v,i)=>{i===0?ctx.moveTo(xS(i),yS(v)):ctx.lineTo(xS(i),yS(v));});
  ctx.stroke();

  // MACD line
  ctx.strokeStyle='rgba(77,159,255,0.9)';ctx.lineWidth=2;
  ctx.beginPath();
  macdS.forEach((v,i)=>{i===0?ctx.moveTo(xS(i),yS(v)):ctx.lineTo(xS(i),yS(v));});
  ctx.stroke();

  // Mark cross
  const cb=d.result?.cross_bar;
  if(cb&&cb<n){
    const xi=xS(n-1-cb);
    ctx.fillStyle='rgba(0,229,160,0.8)';
    ctx.beginPath();ctx.arc(xi,yS(macdS[n-1-cb]),4,0,Math.PI*2);ctx.fill();
  }

  // Current values label
  ctx.fillStyle='rgba(77,159,255,0.9)';ctx.font='8px DM Mono,monospace';ctx.textAlign='left';
  const mv=macdS[macdS.length-1];
  ctx.fillText('MACD: '+(mv<0.001?mv.toFixed(6):mv.toFixed(4)),W-pad.r+4,pad.t+10);
  const sv=sigS[sigS.length-1];
  ctx.fillStyle='rgba(240,180,41,0.9)';
  ctx.fillText('SIG: '+(sv<0.001?sv.toFixed(6):sv.toFixed(4)),W-pad.r+4,pad.t+22);
}

window.addEventListener('load',()=>{
  const sb=document.querySelector('#fg4 .fc');
  if(sb){sb.classList.add('on');sb.textContent='SIGNAL ▼';}
});
setInterval(()=>{document.getElementById('ft').textContent=new Date().toLocaleString();},1000);
</script>
</body>
</html>"""

if __name__ == "__main__":
    auto_scan["next_run"] = time.time() + 30
    threading.Thread(target=auto_scan_worker, daemon=True).start()
    print("\n" + "="*52)
    print("  MACDScan — 4H MACD Crossover Scanner")
    print("  Pullback Entry · Just Crossed · Watch")
    print("  Open browser → http://localhost:5003")
    print("  Press Ctrl+C to stop")
    print("="*52 + "\n")
    port = int(os.environ.get("PORT", 5003))
    app.run(debug=False, host="0.0.0.0", port=port, threaded=True)
