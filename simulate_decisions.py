#!/usr/bin/env python3
"""Replay telemetry against solar.py decision engine without GPIO/Telegram side effects."""
import argparse
import json
import os
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List

# solar.py reads required env at import time. Simulation supplies harmless local defaults.
_DEFAULT_ENV = {
    "MY_BOT_TOKEN": "simulate", "MY_CHAT_ID": "simulate", "MY_WEATHER_API": "simulate",
    "MY_LOCATION_LAT": "47.4979", "MY_LOCATION_LON": "19.0402", "MY_APP_ID": "simulate",
    "MY_APP_SECRET": "simulate", "MY_EMAIL": "simulate", "MY_PASSWORD": "simulate",
    "MY_DEVICE_SN": "simulate", "MY_QUOTE_FILE": "quote_sim.json", "MY_STATE_FILE": "state_sim.json",
    "MY_SOLARMAN_FILE": "solarman_sim.json", "WALLET_ADDRESS": "R" + "1" * 33,
}
for key, value in _DEFAULT_ENV.items():
    os.environ.setdefault(key, value)

import solar  # noqa: E402


def _parse_ts(value: str) -> datetime:
    dt = datetime.fromisoformat(value)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=solar.budapest_tz)
    return dt


def _sun_times_for(ts: datetime):
    # Deterministic local replay approximation; live app still uses OpenWeather sunrise/sunset.
    sunrise = ts.replace(hour=5, minute=16, second=0, microsecond=0)
    sunset = ts.replace(hour=20, minute=10, second=0, microsecond=0)
    return sunrise, sunset


def _weather_outlook_from_row(row: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "summary_5d": str(row.get("weather_risk_5d", "mixed") or "mixed"),
        "sunny_ratio_5d": float(row.get("weather_sunny_ratio_5d", 0.0) or 0.0),
        "bad_ratio_5d": float(row.get("weather_bad_ratio_5d", 0.0) or 0.0),
        "confidence": 0.7,
        "source": "telemetry_replay",
    }


def replay(telemetry_path: Path, history_dir: Path) -> Dict[str, Any]:
    rows = json.loads(telemetry_path.read_text(encoding="utf-8"))
    rows = [r for r in rows if isinstance(r, dict) and r.get("ts")]
    rows.sort(key=lambda r: r["ts"])

    solar.telemetry_history.clear()
    # Seed full context so same-day/refill model can use recorded charge behavior.
    for r in rows:
        solar.telemetry_history.append(r)
    solar.historical_profile = solar.build_historical_profile(str(history_dir))

    target_date = "2026-05-10" if any(str(r.get("ts", "")).startswith("2026-05-10") for r in rows) else str(rows[-1].get("ts", ""))[:10]
    replay_rows = [r for r in rows if str(r.get("ts", "")).startswith(target_date)]

    prev_state = "stop"
    transitions: List[Dict[str, Any]] = []
    dawn_cases: List[Dict[str, Any]] = []
    runtime_minutes = 0.0
    min_soc = 101.0
    max_soc = 0.0
    reached_full = False
    first_start = None
    stop_times: List[str] = []
    last_ts = None

    for row in replay_rows:
        ts = _parse_ts(row["ts"])
        sunrise, sunset = _sun_times_for(ts)
        battery = float(row.get("battery", 0.0) or 0.0)
        power = float(row.get("power", 0.0) or 0.0)
        min_soc = min(min_soc, battery)
        max_soc = max(max_soc, battery)
        reached_full = reached_full or battery >= 99.5

        wx = _weather_outlook_from_row(row)
        hist = solar._history_recommendation(ts, battery, power, sunrise, sunset, wx)
        # Historical observed min-stop wins for exact replay day if present.
        if row.get("min_stop_soc") is not None:
            hist["min_stop_soc"] = float(row.get("min_stop_soc") or hist.get("min_stop_soc", solar.BATTERY_FLOOR_SOC))
        start_guard = solar._compute_start_bridge_guard(ts, battery, power, sunrise, sunset, hist, solar.BATTERY_NOMINAL_V, solar.BATTERY_CAPACITY_AH)
        decision = solar._make_miner_decision(
            ts, prev_state, battery, power,
            float(row.get("inv_l1", 0.0) or 0.0), float(row.get("inv_l2", 0.0) or 0.0),
            float(row.get("inv_l3", 0.0) or 0.0), float(row.get("inv_lt", 0.0) or 0.0),
            str(row.get("condition", "unknown")), float(row.get("clouds", 0.0) or 0.0),
            str(row.get("condition", "unknown")), float(row.get("clouds", 0.0) or 0.0),
            str(row.get("condition", "unknown")), float(row.get("clouds", 0.0) or 0.0),
            sunrise, sunset, hist, start_guard, solar.BATTERY_NOMINAL_V, solar.BATTERY_CAPACITY_AH, wx,
        )
        desired = decision.get("desired_state", "stop")
        if desired == "hold":
            desired = prev_state
        if prev_state == "production" and desired == "stop" and not decision.get("hard_stop"):
            # Replay debounce: require 3 soft stop samples.
            if len(transitions) == 0 or transitions[-1].get("pending_soft_stop") != True:
                transitions.append({"ts": ts.isoformat(), "pending_soft_stop": True})
                desired = prev_state
        if desired != prev_state:
            transitions.append({"ts": ts.isoformat(), "from": prev_state, "to": desired, "summary": decision.get("decision_summary")})
            if desired == "production" and first_start is None:
                first_start = ts.isoformat()
            if desired == "stop":
                stop_times.append(ts.isoformat())
            prev_state = desired
        if prev_state == "production" and last_ts is not None:
            runtime_minutes += max(0.0, min(30.0, (ts - last_ts).total_seconds() / 60.0))
        last_ts = ts
        if power <= solar.DAWN_ZERO_PV_MAX_W:
            dawn_cases.append({
                "ts": ts.isoformat(), "soc": battery, "pv_w": power,
                "decision": desired, "allowed": bool(decision.get("zero_pv_bridge_start")),
                "summary": decision.get("decision_summary"),
                "available_wh": decision.get("metrics", {}).get("available_bridge_wh"),
                "required_wh": decision.get("metrics", {}).get("required_bridge_wh"),
                "cover": decision.get("metrics", {}).get("predicted_first_miner_cover_time"),
                "confidence": decision.get("confidence"),
            })

    clean_transitions = [t for t in transitions if "from" in t]
    return {
        "first_start_time": first_start,
        "stop_times": stop_times,
        "transitions": len(clean_transitions),
        "minimum_soc": min_soc if min_soc <= 100 else None,
        "maximum_soc": max_soc,
        "reached_100_soc": reached_full,
        "estimated_runtime_minutes": round(runtime_minutes, 1),
        "dawn_zero_pv_cases": dawn_cases,
        "replay_date": target_date,
        "transition_log": clean_transitions,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--telemetry", required=True)
    ap.add_argument("--history-dir", required=True)
    args = ap.parse_args()
    result = replay(Path(args.telemetry), Path(args.history_dir))
    print("Daily replay summary")
    print(json.dumps(result, indent=2, ensure_ascii=False))
    interesting = [x for x in result["dawn_zero_pv_cases"] if x["allowed"]]
    if interesting:
        print("\nDawn zero-PV key case:")
        print(json.dumps(interesting[0], indent=2, ensure_ascii=False))
    else:
        print("\nDawn zero-PV key case: no allowed start in replay")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
