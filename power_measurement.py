"""Solarman measurements for energy planning/display, never GPIO authorization."""
from dataclasses import dataclass
from datetime import datetime

@dataclass(frozen=True)
class PowerSample:
    at: datetime
    total: float
    l1: float
    l2: float
    l3: float
    source: str = 'consumption'
    MAX_SAMPLE_AGE_SECONDS = 420

    @staticmethod
    def fresh(sample, now):
        return sample is not None and 0 <= (now-sample.at).total_seconds() <= PowerSample.MAX_SAMPLE_AGE_SECONDS
