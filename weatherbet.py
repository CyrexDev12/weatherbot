#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
weatherbet.py — Weather Trading Bot for Polymarket
=====================================================
Tracks weather forecasts from 3 sources (ECMWF, HRRR, METAR),
compares with Polymarket markets, paper trades using Kelly criterion.

Usage:
    python weatherbet.py          # main loop
    python weatherbet.py report   # full report
    python weatherbet.py status   # balance and open positions
"""

import re
import os
import sys
import json
import math
import time
import requests
from datetime import datetime, timezone, timedelta
from pathlib import Path

# =============================================================================
# CONFIG
# =============================================================================

with open("config.json", encoding="utf-8") as f:
    _cfg = json.load(f)

BALANCE          = _cfg.get("balance", 10000.0)
MAX_BET          = _cfg.get("max_bet", 20.0)        # max bet per trade
MIN_EV           = _cfg.get("min_ev", 0.10)
MAX_PRICE        = _cfg.get("max_price", 0.45)
MIN_VOLUME       = _cfg.get("min_volume", 500)
MIN_HOURS        = _cfg.get("min_hours", 2.0)
MAX_HOURS        = _cfg.get("max_hours", 72.0)
KELLY_FRACTION   = _cfg.get("kelly_fraction", 0.25)
MAX_SLIPPAGE     = _cfg.get("max_slippage", 0.03)  # max allowed ask-bid spread
TAKER_FEE_RATE   = _cfg.get("taker_fee_rate", 0.05) # conservative weather rate
SCAN_INTERVAL    = _cfg.get("scan_interval", 3600)   # every hour
CALIBRATION_MIN  = _cfg.get("calibration_min", 30)
VC_KEY           = _cfg.get("vc_key", "")
DISCORD_WEBHOOK_URL = os.environ.get(
    "DISCORD_WEBHOOK_URL",
    _cfg.get("discord_webhook_url", "")
)
CLOB_HOST         = "https://clob.polymarket.com"

SIGMA_F = 2.0
SIGMA_C = 1.2

DATA_DIR         = Path("data")
DATA_DIR.mkdir(exist_ok=True)
STATE_FILE       = DATA_DIR / "state.json"
MARKETS_DIR      = DATA_DIR / "markets"
MARKETS_DIR.mkdir(exist_ok=True)
CALIBRATION_FILE = DATA_DIR / "calibration.json"

LOCATIONS = {
    "nyc":          {"lat": 40.7772,  "lon":  -73.8726, "name": "New York City", "station": "KLGA", "unit": "F", "region": "us"},
    "chicago":      {"lat": 41.9742,  "lon":  -87.9073, "name": "Chicago",       "station": "KORD", "unit": "F", "region": "us"},
    "miami":        {"lat": 25.7959,  "lon":  -80.2870, "name": "Miami",         "station": "KMIA", "unit": "F", "region": "us"},
    "dallas":       {"lat": 32.8471,  "lon":  -96.8518, "name": "Dallas",        "station": "KDAL", "unit": "F", "region": "us"},
    "seattle":      {"lat": 47.4502,  "lon": -122.3088, "name": "Seattle",       "station": "KSEA", "unit": "F", "region": "us"},
    "atlanta":      {"lat": 33.6407,  "lon":  -84.4277, "name": "Atlanta",       "station": "KATL", "unit": "F", "region": "us"},
    "london":       {"lat": 51.5048,  "lon":    0.0495, "name": "London",        "station": "EGLC", "unit": "C", "region": "eu"},
    "paris":        {"lat": 48.9962,  "lon":    2.5979, "name": "Paris",         "station": "LFPG", "unit": "C", "region": "eu"},
    "munich":       {"lat": 48.3537,  "lon":   11.7750, "name": "Munich",        "station": "EDDM", "unit": "C", "region": "eu"},
    "ankara":       {"lat": 40.1281,  "lon":   32.9951, "name": "Ankara",        "station": "LTAC", "unit": "C", "region": "eu"},
    "seoul":        {"lat": 37.4691,  "lon":  126.4505, "name": "Seoul",         "station": "RKSI", "unit": "C", "region": "asia"},
    "tokyo":        {"lat": 35.7647,  "lon":  140.3864, "name": "Tokyo",         "station": "RJTT", "unit": "C", "region": "asia"},
    "shanghai":     {"lat": 31.1443,  "lon":  121.8083, "name": "Shanghai",      "station": "ZSPD", "unit": "C", "region": "asia"},
    "singapore":    {"lat":  1.3502,  "lon":  103.9940, "name": "Singapore",     "station": "WSSS", "unit": "C", "region": "asia"},
    "lucknow":      {"lat": 26.7606,  "lon":   80.8893, "name": "Lucknow",       "station": "VILK", "unit": "C", "region": "asia"},
    "tel-aviv":     {"lat": 32.0114,  "lon":   34.8867, "name": "Tel Aviv",      "station": "LLBG", "unit": "C", "region": "asia"},
    "toronto":      {"lat": 43.6772,  "lon":  -79.6306, "name": "Toronto",       "station": "CYYZ", "unit": "C", "region": "ca"},
    "sao-paulo":    {"lat": -23.4356, "lon":  -46.4731, "name": "Sao Paulo",     "station": "SBGR", "unit": "C", "region": "sa"},
    "buenos-aires": {"lat": -34.8222, "lon":  -58.5358, "name": "Buenos Aires",  "station": "SAEZ", "unit": "C", "region": "sa"},
    "wellington":   {"lat": -41.3272, "lon":  174.8052, "name": "Wellington",    "station": "NZWN", "unit": "C", "region": "oc"},
}

TIMEZONES = {
    "nyc": "America/New_York", "chicago": "America/Chicago",
    "miami": "America/New_York", "dallas": "America/Chicago",
    "seattle": "America/Los_Angeles", "atlanta": "America/New_York",
    "london": "Europe/London", "paris": "Europe/Paris",
    "munich": "Europe/Berlin", "ankara": "Europe/Istanbul",
    "seoul": "Asia/Seoul", "tokyo": "Asia/Tokyo",
    "shanghai": "Asia/Shanghai", "singapore": "Asia/Singapore",
    "lucknow": "Asia/Kolkata", "tel-aviv": "Asia/Jerusalem",
    "toronto": "America/Toronto", "sao-paulo": "America/Sao_Paulo",
    "buenos-aires": "America/Argentina/Buenos_Aires", "wellington": "Pacific/Auckland",
}

MONTHS = ["january","february","march","april","may","june",
          "july","august","september","october","november","december"]
# =============================================================================
# DISCORD LOGGING
# =============================================================================

def discord_log(message, title="WeatherBot", color=3447003):
    """
    Sends a message to Discord using a webhook.
    Does nothing if DISCORD_WEBHOOK_URL is not configured.
    """
    if not DISCORD_WEBHOOK_URL:
        return

    payload = {
        "username": "WeatherBot",
        "embeds": [
            {
                "title": title,
                "description": message[:4000],
                "color": color,
                "timestamp": datetime.now(timezone.utc).isoformat()
            }
        ]
    }

    try:
        requests.post(DISCORD_WEBHOOK_URL, json=payload, timeout=(3, 5))
    except Exception as e:
        print(f"  [DISCORD] Failed to send webhook: {e}")


def discord_status_message():
    """Builds a short status message for Discord."""
    state = load_state()
    markets = load_all_markets()

    open_pos = [
        m for m in markets
        if m.get("position") and m["position"].get("status") == "open"
    ]

    resolved = [
        m for m in markets
        if m.get("status") == "resolved" and m.get("pnl") is not None
    ]

    bal = state.get("balance", BALANCE)
    start = state.get("starting_balance", BALANCE)
    ret_pct = ((bal - start) / start * 100) if start else 0.0

    stats = trade_stats(markets)
    wins = stats["wins"]
    losses = stats["losses"]
    total = stats["completed"]
    decided = wins + losses
    wr = f"{wins / decided:.0%}" if decided else "N/A"

    return (
        f"**Balance:** ${bal:,.2f}\n"
        f"**Return:** {'+' if ret_pct >= 0 else ''}{ret_pct:.1f}%\n"
        f"**Completed:** {total} | W: {wins} | L: {losses} | "
        f"BE: {stats['breakeven']} | WR: {wr}\n"
        f"**Estimated Fees Paid:** ${stats['fees']:.2f}\n"
        f"**Open Positions:** {len(open_pos)}\n"
        f"**Resolved Markets:** {len(resolved)}"
    )

# =============================================================================
# MATH
# =============================================================================

def norm_cdf(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))

def bucket_prob(forecast, t_low, t_high, sigma=None):
    """Probability mass for an integer-resolved bucket under forecast uncertainty."""
    mean = float(forecast)
    s = max(float(sigma if sigma is not None else 2.0), 0.1)

    # Temperature markets resolve to whole-degree values. Half-degree continuity
    # boundaries make exact and ranged buckets collectively cover the full curve.
    if t_low == -999:
        return norm_cdf((float(t_high) + 0.5 - mean) / s)
    if t_high == 999:
        return 1.0 - norm_cdf((float(t_low) - 0.5 - mean) / s)

    lower = float(t_low) - 0.5
    upper = float(t_high) + 0.5
    return max(0.0, min(1.0, norm_cdf((upper - mean) / s) - norm_cdf((lower - mean) / s)))

def estimate_taker_fee(shares, price, fee_rate=TAKER_FEE_RATE):
    """Estimate Polymarket's dynamic taker fee in USDC."""
    if shares <= 0 or price <= 0 or price >= 1 or fee_rate <= 0:
        return 0.0
    return round(float(shares) * float(fee_rate) * float(price) * (1.0 - float(price)), 5)

def calc_ev(p, price, fee_rate=TAKER_FEE_RATE):
    """Conservative expected ROI after estimated entry and early-exit fees."""
    if price <= 0 or price >= 1: return 0.0
    fee_per_share = estimate_taker_fee(1.0, price, fee_rate)
    capital = price + fee_per_share
    expected_profit = p - price - (2.0 * fee_per_share)
    return round(expected_profit / capital, 4)

def exit_financials(position, exit_price, charge_fee=True):
    """Return net proceeds, exit fee, and all-in PnL for a closed position."""
    shares = float(position["shares"])
    gross_proceeds = shares * float(exit_price)
    fee_rate = float(position.get("fee_rate", TAKER_FEE_RATE))
    exit_fee = estimate_taker_fee(shares, exit_price, fee_rate) if charge_fee else 0.0
    entry_fee = float(position.get("entry_fee", 0.0))
    pnl = gross_proceeds - exit_fee - float(position["cost"]) - entry_fee
    return round(gross_proceeds - exit_fee, 2), exit_fee, round(pnl, 2)

def calc_kelly(p, price):
    if price <= 0 or price >= 1: return 0.0
    fee_per_share = estimate_taker_fee(1.0, price)
    capital = price + fee_per_share
    net_win = 1.0 - price - (2.0 * fee_per_share)
    if capital <= 0 or net_win <= 0:
        return 0.0
    b = net_win / capital
    f = (p * b - (1.0 - p)) / b
    return round(min(max(0.0, f) * KELLY_FRACTION, 1.0), 4)

def bet_size(kelly, balance):
    raw = kelly * balance
    return round(min(raw, MAX_BET), 2)

# =============================================================================
# CALIBRATION
# =============================================================================

_cal: dict = {}
HOUR_BUCKETS = (
    (0, 12, "h00_12"),
    (12, 24, "h12_24"),
    (24, 48, "h24_48"),
    (48, float("inf"), "h48_plus"),
)

def load_cal():
    if CALIBRATION_FILE.exists():
        return json.loads(CALIBRATION_FILE.read_text(encoding="utf-8"))
    return {}

def hours_bucket(hours):
    try:
        value = max(0.0, float(hours))
    except (TypeError, ValueError):
        return "h48_plus"
    return next(label for low, high, label in HOUR_BUCKETS if low <= value < high)

def get_sigma(city_slug, source="ecmwf", hours=None):
    bucket_key = f"{city_slug}_{source}_{hours_bucket(hours)}"
    if hours is not None and bucket_key in _cal:
        return float(_cal[bucket_key]["sigma"])

    # Preserve compatibility with calibration.json files from older versions.
    legacy_key = f"{city_slug}_{source}"
    if legacy_key in _cal:
        return float(_cal[legacy_key]["sigma"])
    return SIGMA_F if LOCATIONS[city_slug]["unit"] == "F" else SIGMA_C

def run_calibration(markets):
    """Recalculate forecast-error sigma by city, source, and lead time."""
    resolved = [
        m for m in markets
        if m.get("status") == "resolved" and m.get("actual_temp") is not None
    ]
    cal = load_cal()
    updated = []

    for source in ["ecmwf", "hrrr", "metar"]:
        for city in set(m["city"] for m in resolved):
            group = [m for m in resolved if m["city"] == city]
            for _, _, bucket in HOUR_BUCKETS:
                errors = []
                for market in group:
                    candidates = [
                        snap for snap in market.get("forecast_snapshots", [])
                        if snap.get(source) is not None
                        and snap.get("hours_left") is not None
                        and hours_bucket(snap.get("hours_left")) == bucket
                    ]
                    if not candidates:
                        continue
                    # One observation per market/bin avoids overweighting days
                    # that happened to receive more scans.
                    snap = min(candidates, key=lambda item: float(item.get("hours_left", 999)))
                    errors.append(float(snap[source]) - float(market["actual_temp"]))

                if len(errors) < CALIBRATION_MIN:
                    continue
                rmse = math.sqrt(sum(error * error for error in errors) / len(errors))
                default = SIGMA_F if LOCATIONS[city]["unit"] == "F" else SIGMA_C
                key = f"{city}_{source}_{bucket}"
                old = float(cal.get(key, {}).get("sigma", default))
                new = round(max(rmse, 0.1), 3)
                cal[key] = {
                    "sigma": new,
                    "bias": round(sum(errors) / len(errors), 3),
                    "n": len(errors),
                    "hours_bucket": bucket,
                    "updated_at": datetime.now(timezone.utc).isoformat(),
                }
                if abs(new - old) > 0.05:
                    updated.append(
                        f"{LOCATIONS[city]['name']} {source}/{bucket}: {old:.2f}->{new:.2f}"
                    )

    CALIBRATION_FILE.write_text(json.dumps(cal, indent=2), encoding="utf-8")
    if updated:
        print(f"  [CAL] {', '.join(updated)}")
    return cal

# =============================================================================
# FORECASTS
# =============================================================================

def get_ecmwf(city_slug, dates):
    """ECMWF via Open-Meteo with bias correction. For all cities."""
    loc = LOCATIONS[city_slug]
    unit = loc["unit"]
    temp_unit = "fahrenheit" if unit == "F" else "celsius"
    result = {}
    url = (
        f"https://api.open-meteo.com/v1/forecast"
        f"?latitude={loc['lat']}&longitude={loc['lon']}"
        f"&daily=temperature_2m_max&temperature_unit={temp_unit}"
        f"&forecast_days=7&timezone={TIMEZONES.get(city_slug, 'UTC')}"
        f"&models=ecmwf_ifs025&bias_correction=true"
    )
    for attempt in range(3):
        try:
            data = requests.get(url, timeout=(5, 10)).json()
            if "error" not in data:
                for date, temp in zip(data["daily"]["time"], data["daily"]["temperature_2m_max"]):
                    if date in dates and temp is not None:
                        result[date] = round(temp, 1) if unit == "C" else round(temp)
            break
        except Exception as e:
            if attempt < 2:
                time.sleep(3)
            else:
                print(f"  [ECMWF] {city_slug}: {e}")
    return result

def get_hrrr(city_slug, dates):
    """HRRR via Open-Meteo. US cities only, up to 48h horizon."""
    loc = LOCATIONS[city_slug]
    if loc["region"] != "us":
        return {}
    result = {}
    url = (
        f"https://api.open-meteo.com/v1/forecast"
        f"?latitude={loc['lat']}&longitude={loc['lon']}"
        f"&daily=temperature_2m_max&temperature_unit=fahrenheit"
        f"&forecast_days=3&timezone={TIMEZONES.get(city_slug, 'UTC')}"
        f"&models=gfs_seamless"  # HRRR+GFS seamless — best option for US
    )
    for attempt in range(3):
        try:
            data = requests.get(url, timeout=(5, 10)).json()
            if "error" not in data:
                for date, temp in zip(data["daily"]["time"], data["daily"]["temperature_2m_max"]):
                    if date in dates and temp is not None:
                        result[date] = round(temp)
            break
        except Exception as e:
            if attempt < 2:
                time.sleep(3)
            else:
                print(f"  [HRRR] {city_slug}: {e}")
    return result

def get_metar(city_slug):
    """Current observed temperature from METAR station. D+0 only."""
    loc = LOCATIONS[city_slug]
    station = loc["station"]
    unit = loc["unit"]
    try:
        url = f"https://aviationweather.gov/api/data/metar?ids={station}&format=json"
        data = requests.get(url, timeout=(5, 8)).json()
        if data and isinstance(data, list):
            temp_c = data[0].get("temp")
            if temp_c is not None:
                if unit == "F":
                    return round(float(temp_c) * 9/5 + 32)
                return round(float(temp_c), 1)
    except Exception as e:
        print(f"  [METAR] {city_slug}: {e}")
    return None

def get_actual_temp(city_slug, date_str):
    """Actual temperature via Visual Crossing for closed markets."""
    loc = LOCATIONS[city_slug]
    station = loc["station"]
    unit = loc["unit"]
    vc_unit = "us" if unit == "F" else "metric"
    url = (
        f"https://weather.visualcrossing.com/VisualCrossingWebServices/rest/services/timeline"
        f"/{station}/{date_str}/{date_str}"
        f"?unitGroup={vc_unit}&key={VC_KEY}&include=days&elements=tempmax"
    )
    try:
        data = requests.get(url, timeout=(5, 8)).json()
        days = data.get("days", [])
        if days and days[0].get("tempmax") is not None:
            return round(float(days[0]["tempmax"]), 1)
    except Exception as e:
        print(f"  [VC] {city_slug} {date_str}: {e}")
    return None

def check_market_resolved(market_id):
    """
    Checks if the market closed on Polymarket and who won.
    Returns: None (still open), True (YES won), False (NO won)
    """
    try:
        r = requests.get(f"https://gamma-api.polymarket.com/markets/{market_id}", timeout=(5, 8))
        data = r.json()
        closed = data.get("closed", False)
        if not closed:
            return None
        # Check YES price — if ~1.0 then WIN, if ~0.0 then LOSS
        prices = parse_json_list(data.get("outcomePrices"))
        outcomes = parse_json_list(data.get("outcomes"))
        yes_index = next(
            (i for i, outcome in enumerate(outcomes) if str(outcome).lower() == "yes"), 0
        )
        if yes_index >= len(prices):
            return None
        yes_price = float(prices[yes_index])
        if yes_price >= 0.95:
            return True   # WIN
        elif yes_price <= 0.05:
            return False  # LOSS
        return None  # not yet determined
    except Exception as e:
        print(f"  [RESOLVE] {market_id}: {e}")
    return None

# =============================================================================
# POLYMARKET
# =============================================================================

def get_polymarket_event(city_slug, month, day, year):
    slug = f"highest-temperature-in-{city_slug}-on-{month}-{day}-{year}"
    try:
        r = requests.get(f"https://gamma-api.polymarket.com/events?slug={slug}", timeout=(5, 8))
        data = r.json()
        if data and isinstance(data, list) and len(data) > 0:
            return data[0]
    except Exception:
        pass
    return None

def parse_json_list(value):
    """Gamma returns some list fields as JSON strings and others as lists."""
    if isinstance(value, list):
        return value
    if isinstance(value, str):
        try:
            parsed = json.loads(value)
            return parsed if isinstance(parsed, list) else []
        except (TypeError, ValueError, json.JSONDecodeError):
            return []
    return []

def yes_token_id(market):
    """Return the CLOB asset ID for the market's YES outcome."""
    outcomes = parse_json_list(market.get("outcomes"))
    token_ids = parse_json_list(market.get("clobTokenIds"))
    for index, outcome in enumerate(outcomes):
        if str(outcome).strip().lower() == "yes" and index < len(token_ids):
            return str(token_ids[index])
    return str(token_ids[0]) if token_ids else None

def get_order_books(token_ids):
    """Fetch public CLOB books in one request and index them by asset ID."""
    unique_ids = list(dict.fromkeys(str(token_id) for token_id in token_ids if token_id))
    if not unique_ids:
        return {}
    try:
        response = requests.post(
            f"{CLOB_HOST}/books",
            json=[{"token_id": token_id} for token_id in unique_ids],
            timeout=(5, 12),
        )
        response.raise_for_status()
        return {str(book.get("asset_id")): book for book in response.json()}
    except Exception as e:
        print(f"  [CLOB] Order books unavailable: {e}")
        return {}

def get_order_book(token_id):
    if not token_id:
        return None
    try:
        response = requests.get(
            f"{CLOB_HOST}/book", params={"token_id": token_id}, timeout=(3, 8)
        )
        response.raise_for_status()
        return response.json()
    except Exception as e:
        print(f"  [CLOB] {token_id}: {e}")
        return None

def get_yes_token_for_market(market_id):
    """Backfill token IDs for positions saved before CLOB support was added."""
    try:
        response = requests.get(
            f"https://gamma-api.polymarket.com/markets/{market_id}", timeout=(3, 8)
        )
        response.raise_for_status()
        return yes_token_id(response.json())
    except Exception as e:
        print(f"  [TOKEN] {market_id}: {e}")
        return None

def book_quote(book):
    """Return the executable top-of-book quote for a YES token."""
    if not book:
        return None
    try:
        bids = [(float(x["price"]), float(x["size"])) for x in book.get("bids", [])]
        asks = [(float(x["price"]), float(x["size"])) for x in book.get("asks", [])]
    except (KeyError, TypeError, ValueError):
        return None
    if not bids or not asks:
        return None
    bid, bid_size = max(bids, key=lambda x: x[0])
    ask, ask_size = min(asks, key=lambda x: x[0])
    return {
        "bid": bid, "ask": ask, "bid_size": bid_size, "ask_size": ask_size,
        "spread": ask - bid, "mid": (ask + bid) / 2,
    }

def estimate_book_fill(book, side, amount):
    """Estimate a full taker fill. BUY amount is dollars; SELL amount is shares."""
    if not book or amount <= 0:
        return None
    levels = book.get("asks" if side == "buy" else "bids", [])
    try:
        parsed = [(float(x["price"]), float(x["size"])) for x in levels]
    except (KeyError, TypeError, ValueError):
        return None
    parsed.sort(key=lambda x: x[0], reverse=(side == "sell"))

    remaining = float(amount)
    total_cost = 0.0
    total_shares = 0.0
    for price, available_shares in parsed:
        if price <= 0 or available_shares <= 0:
            continue
        shares = min(available_shares, remaining / price) if side == "buy" else min(available_shares, remaining)
        total_cost += shares * price
        total_shares += shares
        remaining -= shares * price if side == "buy" else shares
        if remaining <= 1e-8:
            break
    if remaining > 1e-6 or total_shares <= 0:
        return None
    return {
        "price": total_cost / total_shares,
        "shares": total_shares,
        "cost": total_cost,
    }

def parse_temp_range(question):
    if not question: return None
    num = r'(-?\d+(?:\.\d+)?)'
    if re.search(r'or below', question, re.IGNORECASE):
        m = re.search(num + r'[°]?[FC] or below', question, re.IGNORECASE)
        if m: return (-999.0, float(m.group(1)))
    if re.search(r'or higher', question, re.IGNORECASE):
        m = re.search(num + r'[°]?[FC] or higher', question, re.IGNORECASE)
        if m: return (float(m.group(1)), 999.0)
    m = re.search(r'between ' + num + r'-' + num + r'[°]?[FC]', question, re.IGNORECASE)
    if m: return (float(m.group(1)), float(m.group(2)))
    m = re.search(r'be ' + num + r'[°]?[FC] on', question, re.IGNORECASE)
    if m:
        v = float(m.group(1))
        return (v, v)
    return None

def hours_to_resolution(end_date_str):
    try:
        end = datetime.fromisoformat(end_date_str.replace("Z", "+00:00"))
        return max(0.0, (end - datetime.now(timezone.utc)).total_seconds() / 3600)
    except Exception:
        return 999.0

def in_bucket(forecast, t_low, t_high):
    if t_low == t_high:
        return round(float(forecast)) == round(t_low)
    return t_low <= float(forecast) <= t_high

# =============================================================================
# MARKET DATA STORAGE
# Each market is stored in a separate file: data/markets/{city}_{date}.json
# =============================================================================

def market_path(city_slug, date_str):
    return MARKETS_DIR / f"{city_slug}_{date_str}.json"

def load_market(city_slug, date_str):
    p = market_path(city_slug, date_str)
    if p.exists():
        return json.loads(p.read_text(encoding="utf-8"))
    return None

def save_market(market):
    p = market_path(market["city"], market["date"])
    p.write_text(json.dumps(market, indent=2, ensure_ascii=False), encoding="utf-8")

def load_all_markets():
    markets = []
    for f in MARKETS_DIR.glob("*.json"):
        try:
            markets.append(json.loads(f.read_text(encoding="utf-8")))
        except Exception:
            pass
    return markets

def trade_stats(markets):
    """Calculate results from closed positions instead of fallible state counters."""
    completed = []
    for market in markets:
        position = market.get("position") or {}
        pnl = position.get("pnl")
        if position.get("status") == "closed" and isinstance(pnl, (int, float)):
            completed.append(market)

    wins = sum(1 for m in completed if m["position"]["pnl"] > 0)
    losses = sum(1 for m in completed if m["position"]["pnl"] < 0)
    return {
        "completed": len(completed),
        "wins": wins,
        "losses": losses,
        "breakeven": len(completed) - wins - losses,
        "fees": sum(float(m["position"].get("total_fees", 0.0)) for m in completed),
        "markets": completed,
    }

def new_market(city_slug, date_str, event, hours):
    loc = LOCATIONS[city_slug]
    return {
        "city":               city_slug,
        "city_name":          loc["name"],
        "date":               date_str,
        "unit":               loc["unit"],
        "station":            loc["station"],
        "event_end_date":     event.get("endDate", ""),
        "hours_at_discovery": round(hours, 1),
        "status":             "open",           # open | closed | resolved
        "position":           None,             # filled when position opens
        "actual_temp":        None,             # filled after resolution
        "resolved_outcome":   None,             # win / loss / no_position
        "pnl":                None,
        "forecast_snapshots": [],               # list of forecast snapshots
        "market_snapshots":   [],               # list of market price snapshots
        "all_outcomes":       [],               # all market buckets
        "created_at":         datetime.now(timezone.utc).isoformat(),
    }

# =============================================================================
# STATE (balance and open positions)
# =============================================================================

def load_state():
    if STATE_FILE.exists():
        return json.loads(STATE_FILE.read_text(encoding="utf-8"))
    return {
        "balance":          BALANCE,
        "starting_balance": BALANCE,
        "total_trades":     0,
        "wins":             0,
        "losses":           0,
        "peak_balance":     BALANCE,
    }

def save_state(state):
    STATE_FILE.write_text(json.dumps(state, indent=2, ensure_ascii=False), encoding="utf-8")

# =============================================================================
# CORE LOGIC
# =============================================================================

def take_forecast_snapshot(city_slug, dates):
    """Fetches forecasts from all sources and returns a snapshot."""
    now_str = datetime.now(timezone.utc).isoformat()
    ecmwf   = get_ecmwf(city_slug, dates)
    hrrr    = get_hrrr(city_slug, dates)
    today   = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    snapshots = {}
    for date in dates:
        snap = {
            "ts":    now_str,
            "ecmwf": ecmwf.get(date),
            "hrrr":  hrrr.get(date) if date <= (datetime.now(timezone.utc) + timedelta(days=2)).strftime("%Y-%m-%d") else None,
            "metar": get_metar(city_slug) if date == today else None,
        }
        # Best forecast: HRRR for US D+0/D+1, otherwise ECMWF
        loc = LOCATIONS[city_slug]
        if loc["region"] == "us" and snap["hrrr"] is not None:
            snap["best"] = snap["hrrr"]
            snap["best_source"] = "hrrr"
        elif snap["ecmwf"] is not None:
            snap["best"] = snap["ecmwf"]
            snap["best_source"] = "ecmwf"
        else:
            snap["best"] = None
            snap["best_source"] = None
        snapshots[date] = snap
    return snapshots

def scan_and_update():
    """Main function of one cycle: updates forecasts, opens/closes positions."""
    global _cal
    now      = datetime.now(timezone.utc)
    state    = load_state()
    balance  = state["balance"]
    new_pos  = 0
    closed   = 0
    resolved = 0

    for city_slug, loc in LOCATIONS.items():
        unit = loc["unit"]
        unit_sym = "F" if unit == "F" else "C"
        print(f"  -> {loc['name']}...", end=" ", flush=True)

        try:
            dates = [(now + timedelta(days=i)).strftime("%Y-%m-%d") for i in range(4)]
            snapshots = take_forecast_snapshot(city_slug, dates)
            time.sleep(0.3)
        except Exception as e:
            print(f"skipped ({e})")
            continue

        for i, date in enumerate(dates):
            dt    = datetime.strptime(date, "%Y-%m-%d")
            event = get_polymarket_event(city_slug, MONTHS[dt.month - 1], dt.day, dt.year)
            if not event:
                continue

            end_date = event.get("endDate", "")
            hours    = hours_to_resolution(end_date) if end_date else 0
            horizon  = f"D+{i}"

            # Load or create market record
            mkt = load_market(city_slug, date)
            if mkt is None:
                if hours < MIN_HOURS or hours > MAX_HOURS:
                    continue
                mkt = new_market(city_slug, date, event, hours)

            # Skip if market already resolved
            if mkt["status"] == "resolved":
                continue

            # Update outcomes list — prices taken directly from event
            outcomes = []
            event_markets = event.get("markets", [])
            books = get_order_books([yes_token_id(market) for market in event_markets])
            for market in event_markets:
                question = market.get("question", "")
                mid      = str(market.get("id", ""))
                token_id = yes_token_id(market)
                volume   = float(market.get("volume", 0))
                rng      = parse_temp_range(question)
                book     = books.get(token_id)
                quote    = book_quote(book)
                if not rng or not token_id or not quote:
                    continue
                outcomes.append({
                    "question":  question,
                    "market_id": mid,
                    "token_id":  token_id,
                    "range":     rng,
                    "bid":       round(quote["bid"], 4),
                    "ask":       round(quote["ask"], 4),
                    "bid_size":  round(quote["bid_size"], 2),
                    "ask_size":  round(quote["ask_size"], 2),
                    "price":     round(quote["mid"], 4),
                    "spread":    round(quote["spread"], 4),
                    "volume":    round(volume, 0),
                    "book":      book,
                })

            outcomes.sort(key=lambda x: x["range"][0])
            mkt["all_outcomes"] = outcomes

            # Forecast snapshot
            snap = snapshots.get(date, {})
            forecast_snap = {
                "ts":          snap.get("ts"),
                "horizon":     horizon,
                "hours_left":  round(hours, 1),
                "ecmwf":       snap.get("ecmwf"),
                "hrrr":        snap.get("hrrr"),
                "metar":       snap.get("metar"),
                "best":        snap.get("best"),
                "best_source": snap.get("best_source"),
            }
            mkt["forecast_snapshots"].append(forecast_snap)

            # Market price snapshot
            top = max(outcomes, key=lambda x: x["price"]) if outcomes else None
            market_snap = {
                "ts":       snap.get("ts"),
                "top_bucket": f"{top['range'][0]}-{top['range'][1]}{unit_sym}" if top else None,
                "top_price":  top["price"] if top else None,
            }
            mkt["market_snapshots"].append(market_snap)

            forecast_temp = snap.get("best")
            best_source   = snap.get("best_source")

            # --- STOP-LOSS AND TRAILING STOP ---
            if mkt.get("position") and mkt["position"].get("status") == "open":
                pos = mkt["position"]
                current_price = None
                for o in outcomes:
                    if o["market_id"] == pos["market_id"]:
                        current_price = o["bid"]
                        break

                if current_price is not None:
                    entry = pos["entry_price"]
                    stop  = pos.get("stop_price", entry * 0.80)  # 20% stop by default

                    # Trailing: if up 20%+ — move stop to breakeven
                    if current_price >= entry * 1.20 and stop < entry:
                        pos["stop_price"] = entry
                        pos["trailing_activated"] = True

                    # Check stop
                    if current_price <= stop:
                        fill = estimate_book_fill(o.get("book"), "sell", pos["shares"])
                        if not fill:
                            continue
                        current_price = fill["price"]
                        net_proceeds, exit_fee, pnl = exit_financials(pos, current_price)
                        balance += net_proceeds
                        pos["closed_at"]    = snap.get("ts")
                        pos["close_reason"] = "stop_loss" if current_price < entry else "trailing_stop"
                        pos["exit_price"]   = current_price
                        pos["exit_fee"]     = exit_fee
                        pos["total_fees"]   = round(pos.get("entry_fee", 0.0) + exit_fee, 5)
                        pos["pnl"]          = pnl
                        pos["status"]       = "closed"
                        closed += 1
                        reason = "STOP" if current_price < entry else "TRAILING BE"
                        print(f"  [{reason}] {loc['name']} {date} | entry ${entry:.3f} exit ${current_price:.3f} | PnL: {'+'if pnl>=0 else ''}{pnl:.2f}")
                        discord_log(
    (
        f"**City:** {loc['name']}\n"
        f"**Date:** {date}\n"
        f"**Reason:** {reason}\n"
        f"**Entry:** ${entry:.3f}\n"
        f"**Exit:** ${current_price:.3f}\n"
        f"**PnL:** {'+' if pnl >= 0 else ''}${pnl:.2f}"
    ),
    title="Position Closed",
    color=15548997 if pnl < 0 else 5763719
)

            # --- CLOSE POSITION if forecast shifted 2+ degrees ---
            if mkt.get("position") and forecast_temp is not None:
                pos = mkt["position"]
                old_bucket_low  = pos["bucket_low"]
                old_bucket_high = pos["bucket_high"]
                # 2-degree buffer — avoid closing on small forecast fluctuations
                unit = loc["unit"]
                buffer = 2.0 if unit == "F" else 1.0
                mid_bucket = (old_bucket_low + old_bucket_high) / 2 if old_bucket_low != -999 and old_bucket_high != 999 else forecast_temp
                forecast_far = abs(forecast_temp - mid_bucket) > (abs(mid_bucket - old_bucket_low) + buffer)
                if not in_bucket(forecast_temp, old_bucket_low, old_bucket_high) and forecast_far:
                    current_price = None
                    for o in outcomes:
                        if o["market_id"] == pos["market_id"]:
                            fill = estimate_book_fill(o.get("book"), "sell", pos["shares"])
                            current_price = fill["price"] if fill else None
                            break
                    if current_price is not None:
                        net_proceeds, exit_fee, pnl = exit_financials(pos, current_price)
                        balance += net_proceeds
                        mkt["position"]["closed_at"]    = snap.get("ts")
                        mkt["position"]["close_reason"] = "forecast_changed"
                        mkt["position"]["exit_price"]   = current_price
                        mkt["position"]["exit_fee"]     = exit_fee
                        mkt["position"]["total_fees"]   = round(pos.get("entry_fee", 0.0) + exit_fee, 5)
                        mkt["position"]["pnl"]          = pnl
                        mkt["position"]["status"]       = "closed"
                        closed += 1
                        print(f"  [CLOSE] {loc['name']} {date} — forecast changed | PnL: {'+'if pnl>=0 else ''}{pnl:.2f}")
                        discord_log(
    (
        f"**City:** {loc['name']}\n"
        f"**Date:** {date}\n"
        f"**Reason:** Forecast changed\n"
        f"**Old Bucket:** {old_bucket_low}-{old_bucket_high}{unit_sym}\n"
        f"**New Forecast:** {forecast_temp}{unit_sym}\n"
        f"**Exit Price:** ${current_price:.3f}\n"
        f"**PnL:** {'+' if pnl >= 0 else ''}${pnl:.2f}"
    ),
    title="Position Closed — Forecast Changed",
    color=16776960
)

            # --- OPEN POSITION ---
            if not mkt.get("position") and forecast_temp is not None and hours >= MIN_HOURS:
                sigma = get_sigma(city_slug, best_source or "ecmwf", hours)
                best_signal = None

                # Find exactly ONE bucket that matches the forecast
                # If forecast doesn't fit any bucket cleanly — skip this market
                matched_bucket = None
                for o in outcomes:
                    t_low, t_high = o["range"]
                    if in_bucket(forecast_temp, t_low, t_high):
                        matched_bucket = o
                        break

                if matched_bucket:
                    o = matched_bucket
                    t_low, t_high = o["range"]
                    volume = o["volume"]
                    bid    = o.get("bid", o["price"])
                    ask    = o.get("ask", o["price"])
                    spread = o.get("spread", 0)

                    # All filters — if any fails, skip this market entirely
                    if volume >= MIN_VOLUME:
                        p  = bucket_prob(forecast_temp, t_low, t_high, sigma)
                        ev = calc_ev(p, ask)
                        if ev >= MIN_EV:
                            kelly = calc_kelly(p, ask)
                            size  = bet_size(kelly, balance)
                            if size >= 0.50:
                                best_signal = {
                                    "market_id":    o["market_id"],
                                    "token_id":     o["token_id"],
                                    "question":     o["question"],
                                    "bucket_low":   t_low,
                                    "bucket_high":  t_high,
                                    "entry_price":  ask,
                                    "bid_at_entry": bid,
                                    "spread":       spread,
                                    "shares":       round(size / ask, 2),
                                    "cost":         size,
                                    "p":            round(p, 4),
                                    "ev":           round(ev, 4),
                                    "kelly":        round(kelly, 4),
                                    "forecast_temp":forecast_temp,
                                    "forecast_src": best_source,
                                    "sigma":        sigma,
                                    "opened_at":    snap.get("ts"),
                                    "status":       "open",
                                    "pnl":          None,
                                    "exit_price":   None,
                                    "close_reason": None,
                                    "closed_at":    None,
                                }

                if best_signal:
                    skip_position = False
                    fill = estimate_book_fill(matched_bucket.get("book"), "buy", best_signal["cost"])
                    if not fill:
                        print(f"  [SKIP] {loc['name']} {date} — insufficient CLOB ask depth")
                        skip_position = True
                    else:
                        real_ask = fill["price"]
                        real_bid = matched_bucket["bid"]
                        real_spread = round(real_ask - real_bid, 4)
                        real_ev = calc_ev(best_signal["p"], real_ask)
                        if real_spread > MAX_SLIPPAGE or real_ask >= MAX_PRICE or real_ev < MIN_EV:
                            print(f"  [SKIP] {loc['name']} {date} — fill ${real_ask:.3f} spread ${real_spread:.3f}")
                            skip_position = True
                        else:
                            best_signal["entry_price"] = real_ask
                            best_signal["bid_at_entry"] = real_bid
                            best_signal["spread"] = real_spread
                            best_signal["shares"] = round(fill["shares"], 4)
                            best_signal["cost"] = round(fill["cost"], 2)
                            best_signal["fee_rate"] = TAKER_FEE_RATE
                            best_signal["entry_fee"] = estimate_taker_fee(
                                best_signal["shares"], real_ask, TAKER_FEE_RATE
                            )
                            best_signal["total_fees"] = best_signal["entry_fee"]
                            best_signal["ev"] = round(real_ev, 4)

                    total_debit = best_signal["cost"] + best_signal.get("entry_fee", 0.0)
                    if not skip_position and best_signal["entry_price"] < MAX_PRICE and total_debit <= balance:
                        balance -= total_debit
                        mkt["position"] = best_signal
                        state["total_trades"] += 1
                        new_pos += 1
                        bucket_label = f"{best_signal['bucket_low']}-{best_signal['bucket_high']}{unit_sym}"
                        print(f"  [BUY]  {loc['name']} {horizon} {date} | {bucket_label} | "
                              f"${best_signal['entry_price']:.3f} | EV {best_signal['ev']:+.2f} | "
                              f"${best_signal['cost']:.2f} ({best_signal['forecast_src'].upper()})")
                        discord_log(
    (
        f"**City:** {loc['name']}\n"
        f"**Date:** {date} ({horizon})\n"
        f"**Bucket:** {bucket_label}\n"
        f"**Entry:** ${best_signal['entry_price']:.3f}\n"
        f"**Cost:** ${best_signal['cost']:.2f}\n"
        f"**Estimated Entry Fee:** ${best_signal['entry_fee']:.5f}\n"
        f"**Shares:** {best_signal['shares']}\n"
        f"**Forecast:** {best_signal['forecast_temp']}{unit_sym} "
        f"({best_signal['forecast_src'].upper()})\n"
        f"**EV:** {best_signal['ev']:+.2f}\n"
        f"**Kelly:** {best_signal['kelly']:.4f}"
    ),
    title="BUY Signal Opened",
    color=5763719
)

            # Market closed by time
            if hours < 0.5 and mkt["status"] == "open":
                mkt["status"] = "closed"

            # Keep quotes and liquidity, but do not persist the full depth payload.
            mkt["all_outcomes"] = [
                {key: value for key, value in outcome.items() if key != "book"}
                for outcome in outcomes
            ]
            save_market(mkt)
            time.sleep(0.1)

        print("ok")

    # --- AUTO-RESOLUTION ---
    for mkt in load_all_markets():
        if mkt["status"] == "resolved":
            continue

        pos = mkt.get("position")
        if not pos or pos.get("status") != "open":
            continue

        market_id = pos.get("market_id")
        if not market_id:
            continue

        # Check if market closed on Polymarket
        won = check_market_resolved(market_id)
        if won is None:
            continue  # market still open

        # Market closed — record result
        price  = pos["entry_price"]
        size   = pos["cost"]
        shares = pos["shares"]
        resolution_price = 1.0 if won else 0.0
        net_proceeds, exit_fee, pnl = exit_financials(
            pos, resolution_price, charge_fee=False
        )

        balance += net_proceeds
        pos["exit_price"]   = resolution_price
        pos["exit_fee"]     = exit_fee
        pos["total_fees"]   = round(pos.get("entry_fee", 0.0), 5)
        pos["pnl"]          = pnl
        pos["close_reason"] = "resolved"
        pos["closed_at"]    = now.isoformat()
        pos["status"]       = "closed"
        mkt["pnl"]          = pnl
        mkt["status"]       = "resolved"
        mkt["resolved_outcome"] = "win" if won else "loss"
        if mkt.get("actual_temp") is None and VC_KEY:
            mkt["actual_temp"] = get_actual_temp(mkt["city"], mkt["date"])

        if won:
            state["wins"] += 1
        else:
            state["losses"] += 1

        result = "WIN" if won else "LOSS"
        print(f"  [{result}] {mkt['city_name']} {mkt['date']} | PnL: {'+'if pnl>=0 else ''}{pnl:.2f}")
        discord_log(
    (
        f"**City:** {mkt['city_name']}\n"
        f"**Date:** {mkt['date']}\n"
        f"**Result:** {result}\n"
        f"**Entry:** ${price:.3f}\n"
        f"**Cost:** ${size:.2f}\n"
        f"**Fees:** ${pos.get('total_fees', 0.0):.5f}\n"
        f"**Shares:** {shares}\n"
        f"**PnL:** {'+' if pnl >= 0 else ''}${pnl:.2f}"
    ),
    title=f"Market Resolved — {result}",
    color=5763719 if won else 15548997
)
        
        resolved += 1

        save_market(mkt)
        time.sleep(0.3)

    state["balance"]      = round(balance, 2)
    state["peak_balance"] = max(state.get("peak_balance", balance), balance)
    save_state(state)

    # Run calibration if enough data collected
    all_mkts = load_all_markets()
    resolved_count = len([m for m in all_mkts if m["status"] == "resolved"])
    if resolved_count >= CALIBRATION_MIN:
        global _cal
        _cal = run_calibration(all_mkts)

    return new_pos, closed, resolved

# =============================================================================
# REPORT
# =============================================================================

def print_status():
    state    = load_state()
    markets  = load_all_markets()
    open_pos = [m for m in markets if m.get("position") and m["position"].get("status") == "open"]
    resolved = [m for m in markets if m["status"] == "resolved" and m.get("pnl") is not None]

    bal     = state.get("balance", BALANCE)
    start   = state.get("starting_balance", BALANCE)
    ret_pct = (bal - start) / start * 100 if start else 0.0
    stats   = trade_stats(markets)
    wins    = stats["wins"]
    losses  = stats["losses"]
    total   = stats["completed"]
    decided = wins + losses
    win_rate = wins / decided if decided else 0.0

    print(f"\n{'='*55}")
    print(f"  WEATHERBET — STATUS")
    print(f"{'='*55}")
    print(f"  Balance:     ${bal:,.2f}  (start ${start:,.2f}, {'+'if ret_pct>=0 else ''}{ret_pct:.1f}%)")
    print(f"  Completed:   {total} | W: {wins} | L: {losses} | "
          f"BE: {stats['breakeven']} | WR: {win_rate:.0%}" if total else "  No completed trades yet")
    print(f"  Fees paid:   ${stats['fees']:.2f}")
    print(f"  Open:        {len(open_pos)}")
    print(f"  Resolved:    {len(resolved)}")

    if open_pos:
        print(f"\n  Open positions:")
        total_unrealized = 0.0
        for m in open_pos:
            pos      = m["position"]
            unit_sym = "F" if m["unit"] == "F" else "C"
            label    = f"{pos['bucket_low']}-{pos['bucket_high']}{unit_sym}"

            # Current price from latest market snapshot
            current_price = pos["entry_price"]
            snaps = m.get("market_snapshots", [])
            if snaps:
                # Find our bucket price in all_outcomes
                for o in m.get("all_outcomes", []):
                    if o["market_id"] == pos["market_id"]:
                        current_price = o["price"]
                        break

            _, _, unrealized = exit_financials(pos, current_price)
            total_unrealized += unrealized
            pnl_str = f"{'+'if unrealized>=0 else ''}{unrealized:.2f}"

            print(f"    {m['city_name']:<16} {m['date']} | {label:<14} | "
                  f"entry ${pos['entry_price']:.3f} -> ${current_price:.3f} | "
                  f"PnL: {pnl_str} | {pos['forecast_src'].upper()}")

        sign = "+" if total_unrealized >= 0 else ""
        print(f"\n  Unrealized PnL: {sign}{total_unrealized:.2f}")

    print(f"{'='*55}\n")

def print_report():
    markets  = load_all_markets()
    resolved = [m for m in markets if m["status"] == "resolved" and m.get("pnl") is not None]

    print(f"\n{'='*55}")
    print(f"  WEATHERBET — FULL REPORT")
    print(f"{'='*55}")

    if not resolved:
        print("  No resolved markets yet.")
        return

    total_pnl = sum(m["pnl"] for m in resolved)
    total_fees = sum(float((m.get("position") or {}).get("total_fees", 0.0)) for m in resolved)
    wins      = [m for m in resolved if m["resolved_outcome"] == "win"]
    losses    = [m for m in resolved if m["resolved_outcome"] == "loss"]

    print(f"\n  Total resolved: {len(resolved)}")
    print(f"  Wins:           {len(wins)} | Losses: {len(losses)}")
    print(f"  Win rate:       {len(wins)/len(resolved):.0%}")
    print(f"  Total PnL:      {'+'if total_pnl>=0 else ''}{total_pnl:.2f}")
    print(f"  Fees paid:      ${total_fees:.2f}")

    print(f"\n  By city:")
    for city in sorted(set(m["city"] for m in resolved)):
        group = [m for m in resolved if m["city"] == city]
        w     = len([m for m in group if m["resolved_outcome"] == "win"])
        pnl   = sum(m["pnl"] for m in group)
        name  = LOCATIONS[city]["name"]
        print(f"    {name:<16} {w}/{len(group)} ({w/len(group):.0%})  PnL: {'+'if pnl>=0 else ''}{pnl:.2f}")

    print(f"\n  Market details:")
    for m in sorted(resolved, key=lambda x: x["date"]):
        pos      = m.get("position", {})
        unit_sym = "F" if m["unit"] == "F" else "C"
        snaps    = m.get("forecast_snapshots", [])
        first_fc = snaps[0]["best"] if snaps else None
        last_fc  = snaps[-1]["best"] if snaps else None
        label    = f"{pos.get('bucket_low')}-{pos.get('bucket_high')}{unit_sym}" if pos else "no position"
        result   = m["resolved_outcome"].upper()
        pnl_str  = f"{'+'if m['pnl']>=0 else ''}{m['pnl']:.2f}" if m["pnl"] is not None else "-"
        fc_str   = f"forecast {first_fc}->{last_fc}{unit_sym}" if first_fc else "no forecast"
        actual   = f"actual {m['actual_temp']}{unit_sym}" if m["actual_temp"] else ""
        print(f"    {m['city_name']:<16} {m['date']} | {label:<14} | {fc_str} | {actual} | {result} {pnl_str}")

    print(f"{'='*55}\n")

# =============================================================================
# MAIN LOOP
# =============================================================================

MONITOR_INTERVAL = 600  # monitor positions every 10 minutes

def monitor_positions():
    """Quick stop check on open positions without full scan."""
    markets  = load_all_markets()
    open_pos = [m for m in markets if m.get("position") and m["position"].get("status") == "open"]
    if not open_pos:
        return 0

    state   = load_state()
    balance = state["balance"]
    closed  = 0

    for mkt in open_pos:
        pos = mkt["position"]
        mid = pos["market_id"]
        token_id = pos.get("token_id") or get_yes_token_for_market(mid)
        if token_id and not pos.get("token_id"):
            pos["token_id"] = token_id
            save_market(mkt)

        # Value and liquidate against the actual YES-token CLOB bids.
        book = get_order_book(token_id)
        quote = book_quote(book)
        current_price = quote["bid"] if quote else None

        if current_price is None:
            continue

        entry = pos["entry_price"]
        stop  = pos.get("stop_price", entry * 0.80)
        city_name = LOCATIONS.get(mkt["city"], {}).get("name", mkt["city"])

        # Hours left to resolution
        end_date = mkt.get("event_end_date", "")
        hours_left = hours_to_resolution(end_date) if end_date else 999.0

        # Take-profit threshold based on hours to resolution
        if hours_left < 24:
            take_profit = None        # hold to resolution
        elif hours_left < 48:
            take_profit = 0.85        # 24-48h: take profit at $0.85
        else:
            take_profit = 0.75        # 48h+: take profit at $0.75

        # Trailing: if up 20%+ — move stop to breakeven
        if current_price >= entry * 1.20 and stop < entry:
            pos["stop_price"] = entry
            pos["trailing_activated"] = True
            print(f"  [TRAILING] {city_name} {mkt['date']} — stop moved to breakeven ${entry:.3f}")

        # Check take-profit
        take_triggered = take_profit is not None and current_price >= take_profit
        # Check stop
        stop_triggered = current_price <= stop

        if take_triggered or stop_triggered:
            fill = estimate_book_fill(book, "sell", pos["shares"])
            if not fill:
                print(f"  [SKIP] {city_name} {mkt['date']} — insufficient CLOB bid depth")
                continue
            current_price = fill["price"]
            net_proceeds, exit_fee, pnl = exit_financials(pos, current_price)
            balance += net_proceeds
            pos["closed_at"]    = datetime.now(timezone.utc).isoformat()
            if take_triggered:
                pos["close_reason"] = "take_profit"
                reason = "TAKE"
            elif current_price < entry:
                pos["close_reason"] = "stop_loss"
                reason = "STOP"
            else:
                pos["close_reason"] = "trailing_stop"
                reason = "TRAILING BE"
            pos["exit_price"]   = current_price
            pos["exit_fee"]     = exit_fee
            pos["total_fees"]   = round(pos.get("entry_fee", 0.0) + exit_fee, 5)
            pos["pnl"]          = pnl
            pos["status"]       = "closed"
            closed += 1
            print(f"  [{reason}] {city_name} {mkt['date']} | entry ${entry:.3f} exit ${current_price:.3f} | {hours_left:.0f}h left | PnL: {'+'if pnl>=0 else ''}{pnl:.2f}")

            discord_log(
    (
        f"**City:** {city_name}\n"
        f"**Date:** {mkt['date']}\n"
        f"**Reason:** {reason}\n"
        f"**Entry:** ${entry:.3f}\n"
        f"**Exit:** ${current_price:.3f}\n"
        f"**Hours Left:** {hours_left:.0f}\n"
        f"**PnL:** {'+' if pnl >= 0 else ''}${pnl:.2f}"
    ),
    title="Position Closed — Monitor",
    color=15548997 if pnl < 0 else 5763719
)
            
            save_market(mkt)

    if closed:
        state["balance"] = round(balance, 2)
        save_state(state)

    return closed


def run_loop():
    global _cal
    _cal = load_cal()

    print(f"\n{'='*55}")
    print(f"  WEATHERBET — STARTING")
    print(f"{'='*55}")
    print(f"  Cities:     {len(LOCATIONS)}")
    print(f"  Balance:    ${BALANCE:,.0f} | Max bet: ${MAX_BET}")
    print(f"  Scan:       {SCAN_INTERVAL//60} min | Monitor: {MONITOR_INTERVAL//60} min")
    print(f"  Sources:    ECMWF + HRRR(US) + METAR(D+0)")
    print(f"  Data:       {DATA_DIR.resolve()}")
    print(f"  Ctrl+C to stop\n")

    discord_log(
        discord_status_message(),
        title="WeatherBot on",
        color=5763719
    )

    last_full_scan = 0

    while True:
        now_ts = time.time()
        now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        # Full scan once per hour
        if now_ts - last_full_scan >= SCAN_INTERVAL:
            print(f"[{now_str}] full scan...")

            try:
                new_pos, closed, resolved = scan_and_update()
                state = load_state()

                print(
                    f"  balance: ${state['balance']:,.2f} | "
                    f"new: {new_pos} | closed: {closed} | resolved: {resolved}"
                )

                discord_log(
                    (
                        f"**Full scan complete**\n"
                        f"**Balance:** ${state['balance']:,.2f}\n"
                        f"**New Positions:** {new_pos}\n"
                        f"**Closed:** {closed}\n"
                        f"**Resolved:** {resolved}\n\n"
                        f"{discord_status_message()}"
                    ),
                    title="Hourly Scan Complete",
                    color=3447003
                )

                last_full_scan = time.time()

            except KeyboardInterrupt:
                print(f"\n  Stopping — saving state...")
                save_state(load_state())
                print(f"  Done. Bye!")
                break

            except requests.exceptions.ConnectionError:
                print(f"  Connection lost — waiting 60 sec")

                discord_log(
                    "Connection lost. Waiting 60 seconds before retrying.",
                    title="WeatherBot Connection Error",
                    color=15548997
                )

                time.sleep(60)
                continue

            except Exception as e:
                print(f"  Error: {e} — waiting 60 sec")

                discord_log(
                    f"Error: `{e}`\nWaiting 60 seconds before retrying.",
                    title="WeatherBot Error",
                    color=15548997
                )

                time.sleep(60)
                continue

        else:
            # Quick stop monitoring
            print(f"[{now_str}] monitoring positions...")

            try:
                stopped = monitor_positions()
                if stopped:
                    state = load_state()
                    print(f"  balance: ${state['balance']:,.2f}")

            except Exception as e:
                print(f"  Monitor error: {e}")

                discord_log(
                    f"Monitor error: `{e}`",
                    title="WeatherBot Monitor Error",
                    color=15548997
                )

        try:
            time.sleep(MONITOR_INTERVAL)

        except KeyboardInterrupt:
            print(f"\n  Stopping — saving state...")
            save_state(load_state())
            print(f"  Done. Bye!")
            break

# =============================================================================
# CLI
# =============================================================================

if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "run"
    if cmd == "run":
        run_loop()
    elif cmd == "status":
        _cal = load_cal()
        print_status()
    elif cmd == "report":
        _cal = load_cal()
        print_report()
    else:
        print("Usage: python weatherbet.py [run|status|report]")
