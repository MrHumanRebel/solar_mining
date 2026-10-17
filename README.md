# Solar Mining

Raspberry Pi controller for a solar-powered mining rig, with a web dashboard,
OLED/DHT sensors, Telegram controls and unMineable USDT monitoring.

## Historical data and decisions

`solarman_json/*.json` is the **only historical measurement source**. Use the
provided downloaded Solarman exports. The application reads these files at
startup; it never updates them or creates a replacement measurement archive.
There is no `solarminer_json` recorder, telemetry backup, persisted live-data
cache, or learning from controller-generated recordings.

The model uses every nonduplicate timestamp from every available export, including
both the host and bundled directories. UTC offsets are normalized to
Europe/Budapest. Conflicting readings use the median of **distinct** values per
channel, so copying a file cannot overweight it. A bad SOC value does not discard
otherwise valid PV/consumption at that timestamp. Invalid fields are counted;
source files and raw chart measurements are never modified.

Historical control references are grouped by **ISO calendar week across all
available years**, without borrowing neighboring weeks or months. Each day first
contributes a median per 15-minute slot; those daily values are averaged with
equal day weights. Five-point checks replace isolated PV/SOC excursions only
when two nearby readings on each side agree (within a total 20-minute window).
Sustained clouds remain. Internal gaps of at most one hour are interpolated and
marked; longer gaps and unobserved edges stay missing. The plots show means,
25–75% bands, contributing days, years and corrected-outlier counts.

The current week's PV curve supplies W versus clock time, typical production
start, peak, energy and miner-only cover time. The SOC curve supplies charge
start and a typical bridge discharge estimate, anchored to today's measured
battery capacity. Its SOC change is advisory: those unlabelled old household/miner loads are
not an additional Wh charge against today's bridge, and cannot create available
energy or override live readings. Historical consumption is
for display only; it is never treated as household-only load or miner identity.

Bridge Wh is the maximum net battery drawdown **from now until sustained solar
cover of household + miner**, accounting for PV contribution and discharge losses.
It is independent of evening demand or the chosen run end. If sustained cover is
not forecast, bridge Wh is unavailable; the remaining day's deficit is never
reported as a bridge. If already covered, bridge Wh is zero. Startup Wh is shown
separately; the total start allowance is `(bridge deficit + startup) × 1.25`,
compared with battery Wh above the default **20%** floor. The former extra 6 SOC
points for starting have been removed. Historical SOC drop is reference-only.

The full run/refill plan remains a separate check. The GUI and Telegram also
show sunset SOC without mining and the current household-load assumption, so a
household-only refill failure is distinguished from an unaffordable bridge.
Current household demand is a forecast assumption re-evaluated every poll, not a
claim that a transient oven load will last all day. Few clouds (≤30%) uses the
sunny PV branch; timestamped rain/heavy-cloud forecasts still derate it. No extra
API calls or physical power-button actions are introduced.

The planner evaluates three stages every live control cycle:

1. Bridge from the current PV output to sustained solar cover, allowing a start
   before PV fully covers the rig and household. Available battery energy above
   the protected SOC floor must cover the deficit, startup energy and a 25%
   bridge margin. A new morning start needs sustained solar cover before its
   planned stop; the available Wh determine whether the bridge is affordable. A running rig or an afternoon start can use a finite battery budget
   without waiting for another solar peak, provided the night reserve is safe.
2. Choose a finite mining run (at least the minimum run duration for a new
   start), ending no later than the existing production stop, 90 minutes before
   astronomical sunset. Search for an earlier stop when needed; do not assume
   the miner must run all day to be allowed to start.
3. Forecast household-only demand and battery refill after the planned stop,
   through actual sunset. Production preserves a default 90% sunset household
   reserve (`MY_HARD_AFTERNOON_STOP_SOC`). This target can cause an earlier
   mining stop when the measured SOC is below full charge; it does not require
   100% SOC to start. No historical consumption is extrapolated into night load.

Independently, from 14:00 onward, if PV disappears (default ≤50 W) and measured
SOC is **below 90%**, immediately request STOP. Defaults are exposed as
`MY_HARD_AFTERNOON_STOP_HOUR`, `MY_AFTERNOON_PV_STOP_W` and
`MY_HARD_AFTERNOON_STOP_SOC`. The physical power guard must still identify the
running miner before pressing its button; the rule does not authorize blind
presses based on household load.

Daytime demand comes from the current measured consumption and the configured
rig allowance, counted once. `MY_MINER_POWER_W` is the whole-rig power
allowance (default **750 W**), including GPUs, CPU and PSU losses.
The supplied OC screenshots report 545.4–548.0 W for the five GPUs. For the
Ryzen 3 3100, motherboard, 8 GB RAM, M.2 SSD and eight fans, allow roughly
80–120 W combined beyond GPU readings. At an assumed 90% PSU efficiency that
means about 695–742 W AC; 750 W is a conservative planning estimate, not a
measured wall load. Set `MY_MINER_POWER_W` to a measured whole-rig AC value when
available; an existing explicit `.env` override takes precedence over this default.
This same allowance drives bridge/refill, cover times and running-load subtraction.
It does not change the physical guard's >1000 W total threshold or replace its
witnessed L2/L3 signature. Historical daytime consumption may already include
the miner and is never added to it again. While running, subtracting the rig
allowance to estimate the household-only refill period is an explicit load
estimate, not evidence about historical appliance states.

The existing free three-hour weather forecast is retained with its timestamps
and applied to the matching part of the day. Clear, mixed and wet forecasts use
different weekly PV quantiles. Current measured PV constrains the immediate
bridge; its influence fades over one hour instead of multiplying down the whole
day's forecast. No additional Solarman or weather requests are introduced.

The dashboard labels the minimum SOC and sunset SOC for the finite proposed
run/refill scenario, shows solar-cover time, planned mining stop, required versus
available bridge energy and protected evening reserve. If a start is rejected,
the projections are explicitly labelled as a rejected-run scenario; missing
inputs are unavailable rather than artificial zeros. A zero can still mean an
unsafe candidate would actually exhaust the battery. STOP reasons identify the
failed bridge, solar cover, missing coverage or night-reserve condition.

### Zero export and near-full batteries

This installation cannot export to the grid. Once the battery is full, measured
PV can fall to match current consumption; it is **delivered power**, not a
measurement of all available panel potential. Neither low PV at full SOC nor
low historical PV during curtailment proves that the miner cannot be supplied.
The controller does not invent an extra kW figure for that unmeasured potential.

If the full-day model rejects a run, a sunny afternoon with a near-full battery
can instead qualify for a **bounded surplus run**. New starts require at least
95% SOC (and sufficient energy); running miners can continue using only the
energy above the evening reserve, at least 90%. This start/continue band avoids
restarting at the reserve. The proposed window is at least the required minimum
run, at most 30 minutes, inside the existing production window. Directly
forecast adverse weather inside that window blocks it. Each scheduled live poll
re-evaluates the plan; no additional Solarman requests are made.

The energy test assumes **zero PV for the entire short window**, paying startup
plus household and miner load, discharge losses and the existing 25% margin
solely from Wh already above the 90% reserve. Thus it can cautiously start even
when the zero-export meter shows little/no PV, then see whether actual PV rises
with the new load. Insufficient battery capacity, high household load, stale or
invalid data, poor current weather and insufficient production time still block
this mode. It does not bypass phase limits, shutdown cooldown or the physical
power guard. The separate >1000 W total/identified-phase rule still determines
whether an automatic STOP decision may press the power button.

GUI and Telegram label this as a bounded surplus run, showing the zero-PV
worst-case SOC **at the planned mining stop**, required/available surplus Wh and
the scheduled stop. The raw delivered-PV sunset scenario remains in the API
with `sunset_projection_uncertain: true`; GUI/Telegram show the sunset and
household-only SOC as not estimable from curtailed PV, rather than presenting
an artificial low SOC as a reliable forecast. This mode does not claim a guaranteed 90% sunset
or a measured amount of extra solar potential. The normal bridge/refill model
continues to apply when feasible, including for low-SOC early starts.

The energy model includes battery capacity from Ah × V, battery saturation,
startup cost and charge/discharge losses. It remains an estimate: future clouds
and household demand can differ. It is recalculated at each live sample, while
the separate power guard controls whether a physical shutdown is authorized.
Missing or stale API data never substitutes a saved JSON measurement.

## Hardware shutdown and API cadence

Pool hashrate is display-only. The separate power guard uses fresh total
consumption and L2/L3 readings, a stable off baseline, and a witnessed load rise
after the controller's own start command. It supports either mapping of three
RTX3070 GPUs on one phase and two GPUs plus CPU on the other.

When STOP is required, one matching fresh reading above 1000 W total may authorize
a long press. No three-reading STOP delay is required. A lost phase signature,
ambiguous load, missing baseline or restart prevents automatic long presses;
there is at most one automatic shutdown press per witnessed run. Aggregate
meters cannot uniquely distinguish every oven/hob combination from a miner.
The guard retains only bounded working samples in memory, never a JSON history.

On the supplied Deye schema, `E_Puse_t1` with explicit W/kW units is total
instantaneous consumption. Pair it with `LPP_A/B/C` (whole-house phases), not
`C_P_L1/L2/L3` (a different load port). The supplied example is 1241 W =
25 + 808 + 408 W; the C_P readings sum to only 50 W. Each phase family is
selected as a complete group and checked against its total, never mixed.

When no consumption register exists, the guard accepts `INV_O_P_T` with
`INV_O_P_L1/L2/L3`, labelled as inverter output. It does not establish
consumption of grid-side appliances. Changes in source or phase family discard
the learned identity. kWh/VA counters are rejected. The dashboard shows the
selected safety meter and device collection time separately from HTTP polling
time, with specific missing-field, timestamp, unit or total/phase errors.

All control, display and guard freshness checks use a shared **420-second**
maximum device age: five-minute Solarman uploads plus the controller's one-minute
offset and request jitter. Future timestamps and older data remain rejected;
duplicate device timestamps cannot confirm a new hardware action. One cached
upload may produce a ten-minute device timestamp gap, so daylight identity is
retained for gaps up to 12 minutes. Longer gaps, changed sources and lost phase
signatures still disarm it. Overnight gap tolerance remains cadence + six minutes.

Solarman authentication and device polling run every five minutes between
astronomical sunrise and sunset, and once every 30 minutes overnight. Failed
attempts also consume a polling slot. Dashboard refresh, sensors and pool
updates do not trigger extra Solarman polling.

## Dashboard

Two separate current-week reference plots have fixed 00:00–24:00 axes: PV in W
and battery SOC in %. They always show this calendar week's cross-year curve,
independent of the history date filter. Four additional live plots show actual
L1, L2, L3 and SUM in W over the last 24 hours. The supplied exports contain no
historical phase columns: these plots use a bounded 288-point RAM buffer,
cleared on restart or meter-source changes, **never saved to JSON**. Fresh device
timestamps are deduplicated. Historical SUM remains date-filterable alongside
historical PV and SOC; no historical phases are fabricated.

Telegram `/now` and automatic run/stop messages use the same live plan and weekly
references as the GUI, including bridge Wh, cover/stop time, projected SOC,
evening reserve and the afternoon cutoff. `/phase` shows the selected true
meter phases and device time. Pool rate is explicitly display-only and may lag.
Neither command triggers an extra Solarman request.

Live metrics, pool hashrate (also while idle), the decision and energy budget are
shown separately from the supplied historical charts. Historical PV, consumption
and SOC come solely from the exports; historical miner states and phases are
not invented. Dates always use Hungarian order (`YYYY.MM.DD.`) and
Europe/Budapest time, even under an English/US browser locale. Both the input
and calendar icon open the calendar dialog; the calendar uses Hungarian month
names and Monday-first weekdays. API range queries accept ISO `YYYY-MM-DD` or
Hungarian dates and reject malformed/inverted ranges instead of silently
replacing them. Empty selections show the actual loaded date coverage.

The image keeps its complete exports in `/app/bundled_solarman_json`, outside
the host mount at `/app/solarman_json`. The loader reads and deduplicates both,
so an older 11-file host directory cannot hide the newer bundled exports. The
bundled history is refreshed by updating the image; no data is downloaded or
recorded at runtime. `/api/history/download` returns the normalized supplied history
without saving it. The old telemetry download endpoint has been removed.

## Run on Raspberry Pi

Supply the existing `.env` credentials: `MY_BOT_TOKEN`, `MY_CHAT_ID`,
`MY_WEATHER_API`, `MY_LOCATION_LAT`, `MY_LOCATION_LON`, `MY_APP_ID`,
`MY_APP_SECRET`, `MY_EMAIL`, `MY_PASSWORD`, and `MY_DEVICE_SN`.
Optional `MY_QUOTE_LIMIT` controls the displayed API allowance.

The supplied Compose configuration uses the existing `pihole_backend` network
and DNS host `172.31.0.100`. Adjust these for your installation. Ensure
`state.json` and `quote_usage.json` exist as files for their bind mounts.

```sh
docker compose pull
docker compose up -d
```

The dashboard listens on port 9000. GPIO/I2C/DHT require the Pi devices and
privileges configured in Compose. The image is built natively for ARM64 in CI.
Build locally with `docker build -f dockerfile -t solar-mining .` if needed.

`MY_HISTORY_DIR` selects the export directory (default `solarman_json`). Compose
mounts it read-only. Minimal controller state and API quota files remain writable;
these contain bookkeeping, not historical measurements.

### Migration

Use the updated Compose file: remove legacy `MY_TELEMETRY_FILE` and
`MY_SOLARMAN_FILE` settings and the `solarminer_json` / raw measurement mounts.
They are no longer read or written. Existing recordings on your Pi are left
untouched and can be archived or deleted independently. The repository's old
generated telemetry sample and recorder-specific replay tool have been removed.
The supplied `solarman_json` exports remain unchanged.

## Development and offline validation

Use Python 3.11 and the dependencies in `requirements.txt`. GPIO integrations are
skipped off the Pi. The tests use simulation defaults and mock external services;
do not launch the live main loop with production credentials for a replay.

```sh
python -m unittest -q test_history_model test_solar_polling test_idle_monitoring test_miner_power_guard test_mining_pool test_solarman_power_fields test_bridge_planning test_web_disconnect test_weekly_reference test_physical_bridge test_near_full_buffer
python simulate_decisions.py --history-dir solarman_json
python simulate_decisions.py --history-dir solarman_json --date 2026-10-16
```

The replay trains only on exports strictly before the selected local day and
walks that day's observations without API requests, GPIO or file writes. It uses
explicit unknown-weather and fixed 07:00–17:00 window assumptions and reports
these limitations. It does not infer historical miner state or phase behavior.
