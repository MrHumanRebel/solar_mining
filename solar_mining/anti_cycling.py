"""Solar-miner anti-cycling policy; no hardware actions or weather API calls.

Model uncertainty alone cannot turn a verified solar-covered run into a STOP.
Hard limits and the controller's physical-state checks remain authoritative.
"""
from datetime import datetime
import math


# Only forecast/optimization failures may be overridden by measured live cover.
# Missing/invalid inputs, protection-floor breaches and impossible reserves never are.
FORECAST_ONLY_FAILURES = frozenset({
    "household_only_refill_not_feasible",
    "night_household_reserve_not_recovered",
    "insufficient_battery_bridge",
    "no_sustained_solar_cover_for_morning_start",
    "insufficient_time_for_minimum_run",
})


def live_surplus_can_continue(*, requested_running, ping_reachable, plan_reason,
                              battery_soc, reserve_soc, protected_floor_soc,
                              pv_w, measured_load_w, surplus_margin_w=200.0,
                              battery_capacity_wh=None, minutes_until_stop=None):
    """Allow CONTINUATION ONLY, using delivered PV and whole-house measured load.

    This is not a prediction of future sunlight and MUST NOT authorize a new
    start. Require SOC close to the evening target, enough time to refill any
    deficit, generous current surplus, valid numbers and a ping-confirmed rig. The next live
    Solarman sample must reevaluate this decision.
    """
    if not requested_running or ping_reachable is not True or plan_reason not in FORECAST_ONLY_FAILURES:
        return False
    values=(battery_soc,reserve_soc,protected_floor_soc,pv_w,measured_load_w,surplus_margin_w)
    if not all(isinstance(v,(int,float)) and math.isfinite(v) for v in values):
        return False
    if not (0 <= protected_floor_soc < reserve_soc <= 100 and 0 <= battery_soc <= 100):
        return False
    if pv_w < 0 or measured_load_w <= 0 or surplus_margin_w < 0:
        return False
    if battery_soc < max(protected_floor_soc + 8, reserve_soc - 5):
        return False
    # A positive net reading with a deliberate buffer, not merely PV >= miner W.
    if pv_w < measured_load_w + max(surplus_margin_w, measured_load_w * .15):
        return False
    if battery_soc < reserve_soc:
        # Before the configured production cutoff, preserve enough time for
        # charging the *remaining* evening-reserve deficit with 90% efficiency,
        # a 25% uncertainty margin and 20 minutes of weather/polling slack.
        if (not isinstance(battery_capacity_wh,(int,float)) or
                not isinstance(minutes_until_stop,(int,float)) or
                not math.isfinite(battery_capacity_wh) or
                not math.isfinite(minutes_until_stop) or
                battery_capacity_wh <= 0 or minutes_until_stop <= 0):
            return False
        deficit_wh=(reserve_soc-battery_soc)*battery_capacity_wh/100
        surplus_w=pv_w-measured_load_w
        refill_minutes=60*deficit_wh/(surplus_w*.9)
        if minutes_until_stop <= refill_minutes*1.25+20:
            return False
    return True


class SoftStopDebouncer:
    """Require independent, increasingly recent Solarman readings for soft STOP.

    Reusing a cached device timestamp cannot count as a second/third warning.
    An explicit hard STOP always succeeds instantly. No saved state is required;
    after process restart only non-hard stops must reconfirm.
    """
    def __init__(self, confirm_samples=3):
        self.confirm_samples=max(2,int(confirm_samples))
        self.reset()

    def reset(self):
        self.samples=0
        self.last_sample_at=None

    def observe(self, *, prior_state, desired_state, hard_stop=False, sample_at=None):
        if hard_stop or prior_state != "production" or desired_state != "stop":
            self.reset()
            return True
        if not isinstance(sample_at, datetime) or sample_at.tzinfo is None:
            self.reset()
            return False
        if self.last_sample_at is not None:
            delta=(sample_at-self.last_sample_at).total_seconds()
            if delta <= 0:
                return self.samples >= self.confirm_samples
            # An unobserved long gap is not continuous adverse evidence.
            if delta > 20*60:
                self.samples=0
        self.last_sample_at=sample_at
        self.samples+=1
        return self.samples >= self.confirm_samples
