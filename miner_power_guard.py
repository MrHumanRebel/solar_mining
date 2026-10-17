"""Conservative, per-run L2/L3 load identification. Pool data is never used."""
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timedelta
from statistics import median


@dataclass(frozen=True)
class PowerSample:
    at: datetime
    total: float
    l1: float
    l2: float
    l3: float
    source: str = "consumption"


class MinerPowerGuard:
    """Require a witnessed two-phase rise after our own start command.

    Aggregate house meters cannot uniquely identify an appliance. Ambiguous
    changes, old samples, missing baselines and process restarts fail closed.
    One run permits at most one automatic long press, never a retry loop.
    """
    # Five-minute device uploads + the controller's one-minute offset + jitter.
    MAX_SAMPLE_AGE_SECONDS = 420

    def __init__(self):
        self.off = deque(maxlen=3)
        self.last_at = None
        self.source = None
        self.started = None
        self.baseline = None
        self.signature = None
        self.candidates = deque(maxlen=2)
        self.poll_interval_seconds = 300
        self.learning_timeout_seconds = 900
        self.reason = "No witnessed miner start"

    def disarm(self, reason):
        self.started = self.baseline = self.signature = None
        self.candidates.clear()
        self.learning_timeout_seconds = 900
        self.reason = reason

    @staticmethod
    def fresh(sample, now):
        return sample is not None and 0 <= (now - sample.at).total_seconds() <= MinerPowerGuard.MAX_SAMPLE_AGE_SECONDS

    def command_start(self, sample, now):
        self.disarm("Start has no stable off baseline")
        if not self.fresh(sample, now):
            return
        if any(s.source != sample.source for s in self.off):
            self.off.clear()
            return
        if not self.off or sample.at > self.off[-1].at:
            self.off.append(sample)
        slack = 120 if self.poll_interval_seconds == 300 else 360
        baseline_span = max(900, 2 * self.poll_interval_seconds + slack)
        if len(self.off) != 3 or (sample.at - self.off[0].at).total_seconds() > baseline_span:
            return
        if any(max(getattr(s, k) for s in self.off) - min(getattr(s, k) for s in self.off) > 80
               for k in ("l1", "l2", "l3")):
            return
        self.baseline = tuple(median(getattr(s, k) for s in self.off) for k in ("l1", "l2", "l3"))
        self.started = now
        self.learning_timeout_seconds = baseline_span
        self.off.clear()
        self.reason = "Waiting for stable L2/L3 rise after start"

    def observe(self, sample, now, expected_state, poll_interval_seconds=300):
        """Return True only for a newly confirmed automatic shutdown."""
        self.poll_interval_seconds = max(300, poll_interval_seconds)
        if not self.fresh(sample, now):
            self.reason = "Missing or stale consumption measurement"
            return False
        if self.reason == "Missing or stale consumption measurement":
            self.reason = ("Miner L2/L3 rise identified" if self.signature is not None else
                           "Waiting for stable L2/L3 rise after start" if self.started is not None else
                           "No witnessed miner start")
        if self.last_at is not None and sample.at <= self.last_at:
            return False
        if self.source is not None and self.source != sample.source:
            self.disarm("Power meter source changed; start identification lost")
            self.off.clear()
        self.source = sample.source
        slack = 120 if self.poll_interval_seconds == 300 else 360
        # One unchanged/cached device upload may create a ten-minute device
        # timestamp gap while HTTP polls still run every five minutes.
        allowed_gap = 720 if self.poll_interval_seconds == 300 else self.poll_interval_seconds + slack
        if self.last_at and (sample.at - self.last_at).total_seconds() > allowed_gap:
            self.disarm("Measurement gap; start identification lost")
            self.off.clear()
        self.last_at = sample.at
        if self.started is None:
            if expected_state == "stop":
                self.off.append(sample)
            return False
        if now - self.started > timedelta(hours=12):
            self.disarm("Start identification expired")
            return False
        delta = tuple(getattr(sample, k) - b for k, b in zip(("l1", "l2", "l3"), self.baseline))
        if self.signature is None:
            self.learning_timeout_seconds = max(self.learning_timeout_seconds, 2*self.poll_interval_seconds + slack)
            if (now - self.started).total_seconds() > self.learning_timeout_seconds:
                self.disarm("No identifiable two-phase mining load after start")
                return False
            # OC samples report ~546–548 W for all five GPUs (~98–125 W each).
            # The existing split bounds include ~350–380 W AC per phase for
            # 3 GPUs versus 2 GPUs + Ryzen/board/fans, with PSU losses.
            # Retain headroom for variation; learn the actual per-run rise.
            # Either L2/L3 assignment is accepted; only a bounded paired rise
            # after our start can arm the guard (not a sustained oven load).
            valid_split = ((250 <= delta[1] <= 550 and 200 <= delta[2] <= 650)
                           or (250 <= delta[2] <= 550 and 200 <= delta[1] <= 650))
            if expected_state != "production" or sample.at <= self.started or abs(delta[0]) > 100 or not valid_split or not 500 <= sum(delta[1:]) <= 1000:
                self.candidates.clear()
                return False
            if self.candidates and (sample.at - self.candidates[-1][0]).total_seconds() < 120:
                return False
            self.candidates.append((sample.at, delta[1:]))
            if len(self.candidates) == 2:
                if all(abs(self.candidates[0][1][i] - delta[i+1]) <= 80 for i in (0, 1)):
                    self.signature = tuple(median(c[1][i] for c in self.candidates) for i in (0, 1))
                    self.reason = "Miner L2/L3 rise identified"
            return False
        # Once either phase contribution disappears, later cooking loads must
        # never re-arm this run, even when household consumption exceeds 1 kW.
        if any(delta[i+1] < self.signature[i] * 0.4 for i in (0, 1)):
            self.disarm("Miner load disappeared; no more automatic presses this run")
            self.off.clear()
            self.off.append(sample)
            return False
        if expected_state != "stop":
            return False
        matches = (abs(delta[0]) <= 100 and all(
            abs(delta[i+1] - self.signature[i]) <= max(80, self.signature[i] * 0.2)
            for i in (0, 1)))
        if sample.total <= 1000 or not matches:
            self.reason = "No unambiguous mining load above 1000 W total"
            return False
        # Identification was learned while the rig ran. One newly collected
        # matching STOP sample is enough; do not wait for more polling cycles.
        self.disarm("Automatic shutdown issued; re-press disabled for this run")
        return True
