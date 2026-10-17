from datetime import datetime,timedelta,timezone
from power_measurement import PowerSample
T=datetime(2026,10,16,10,tzinfo=timezone.utc)
def sample(minute,total=1200,l1=100,l2=550,l3=550):
    return PowerSample(T+timedelta(minutes=minute),total,l1,l2,l3)
