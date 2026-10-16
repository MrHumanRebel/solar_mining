"""Read-only Solarman export dataset and conservative energy-budget planning.

No live samples are accumulated or written. Historical consumption is aggregate
household load, not a labelled miner measurement.
"""
from collections import defaultdict
from datetime import datetime, timedelta, timezone
import json
import math
from pathlib import Path
import re
from statistics import median
from zoneinfo import ZoneInfo

LOCAL = ZoneInfo('Europe/Budapest')


def quantile(values, q):
    values = sorted(values)
    if not values:
        return 0.0
    p = (len(values)-1)*q
    lo = int(p)
    return values[lo]+(values[min(lo+1,len(values)-1)]-values[lo])*(p-lo)


def load_exports(directory, before=None):
    grouped = defaultdict(list)
    invalid = 0
    files = sorted(Path(directory).glob('*.json'))
    for path in files:
        try:
            payload = json.loads(path.read_text(encoding='utf-8'))
        except (OSError, ValueError):
            invalid += 1
            continue
        if not isinstance(payload,list):
            invalid += 1
            continue
        for row in payload:
            try:
                at = datetime.strptime(row['Updated Time'],'%Y/%m/%d %H:%M')
                zone = row.get('Time Zone')
                if zone:
                    match = re.fullmatch(r'UTC([+-])(\d{2}):(\d{2})',zone)
                    if not match:
                        raise ValueError('unknown export timezone')
                    hours, minutes = int(match[2]), int(match[3])
                    if hours > 23 or minutes > 59:
                        raise ValueError('invalid offset')
                    offset = timedelta(hours=hours,minutes=minutes)*(1 if match[1]=='+' else -1)
                    at = at.replace(tzinfo=timezone(offset)).astimezone(LOCAL)
                else:
                    at = at.replace(tzinfo=LOCAL)
                values = [float(row[key]) for key in
                          ('Production Power(W)','Consumption Power(W)','SoC(%)')]
                if not all(math.isfinite(v) for v in values) or min(values)<0 or values[2]>100:
                    raise ValueError('invalid PV/load/SOC')
                if before is not None and at >= before:
                    continue
                grouped[at].append(values)
            except (KeyError,TypeError,ValueError,OverflowError):
                invalid += 1
    rows = [{'ts':at.isoformat(),'power':median(v[0] for v in values),
             'consumption':median(v[1] for v in values),'battery':median(v[2] for v in values)}
            for at,values in sorted(grouped.items())]
    return {'rows':rows,'files':len(files),'invalid_rows':invalid,
            'duplicate_timestamps':sum(len(v)-1 for v in grouped.values()),
            'unique_timestamps':len(rows)}


def seasonal_profile(rows, month):
    """Nearest season; never fabricate miner, weather or phase labels."""
    available = {datetime.fromisoformat(r['ts']).month for r in rows}
    if not available:
        return {}
    distance = lambda m: min((month-m)%12,(m-month)%12)
    nearest = min(distance(m) for m in available)
    if nearest > 2:
        return {}
    selected = [r for r in rows if distance(datetime.fromisoformat(r['ts']).month) <= max(1,nearest)]
    hours = defaultdict(list)
    days = set()
    for row in selected:
        at = datetime.fromisoformat(row['ts'])
        hours[at.hour].append(row)
        days.add(at.date())
    return {'days':len(days),'samples':len(selected),'interpolated':month not in available,
            'hours':{h:{'pv_p25':quantile([r['power'] for r in rs],.25),
                         'pv_p50':quantile([r['power'] for r in rs],.5),
                         'load_p75':quantile([r['consumption'] for r in rs],.75),
                         'samples':len(rs)} for h,rs in hours.items()}}


def plan(profile, now, sunset, soc, pv, load, running, capacity_wh, miner_w,
         floor_soc=20, reserve_soc=90, weather='unknown', startup_wh=120):
    """Integrate a candidate mining run in Wh, including house demand.

    Use max(historical aggregate load, proposed current total), rather than
    adding the rig to unlabelled historical totals a second time. Forecast PV
    uses the lower quartile and can be derated, never boosted by weather.
    """
    valid = (profile and profile.get('days',0)>=3
             and all(isinstance(v,(int,float)) and math.isfinite(v) for v in
                     (soc,pv,load,capacity_wh,miner_w,startup_wh,floor_soc,reserve_soc))
             and capacity_wh>0 and miner_w>=0 and startup_wh>=0
             and 0<=floor_soc<=reserve_soc<=100
             and 0<=soc<=100 and pv>=0 and load>=0 and now<sunset)
    if not valid:
        return {'safe':False,'reason':'insufficient_history_or_live_data','coverage':0,
                'end_soc':None,'minimum_soc':None,'missing_hours':True}
    factor = {'solar_friendly':1.0,'mixed':.8,'solar_weak':.55}.get(weather,.7)
    if profile.get('interpolated'):
        factor *= .8
    hours = profile['hours']
    current = hours.get(now.hour,{})
    if current.get('pv_p25',0)>100:
        factor = min(factor,max(.2,pv/current['pv_p25']))
    energy = soc/100*capacity_wh-(0 if running else startup_wh)
    minimum = energy
    proposed_load = load+(0 if running else miner_w)
    produced = consumed = 0.0
    full_at = None
    cover_at = None
    missing = False
    t = now
    while t<sunset:
        end = min(t+timedelta(minutes=5),sunset)
        dt = (end-t).total_seconds()/3600
        h = hours.get(t.hour)
        if not h or h['samples']<3:
            missing = True
            expected_pv, expected_load = 0.0,proposed_load
        else:
            expected_pv = h['pv_p25']*factor
            expected_load = max(h['load_p75'],proposed_load)
        if cover_at is None and expected_pv>=expected_load:
            cover_at = t.isoformat()
        net = (expected_pv-expected_load)*dt
        energy = min(capacity_wh,energy+(net*.9 if net>=0 else net/.9))
        minimum = min(minimum,energy)
        if full_at is None and energy>=capacity_wh*.995:
            full_at = end.isoformat()
        produced += expected_pv*dt
        consumed += expected_load*dt
        t = end
    floor_wh = floor_soc/100*capacity_wh
    reserve_wh = reserve_soc/100*capacity_wh
    coverage = min(1.0,profile['days']/20)
    safe = not missing and minimum>=floor_wh and energy>=reserve_wh
    return {'safe':safe,'reason':'energy_budget_covers_reserve' if safe else 'battery_floor_or_evening_reserve',
            'coverage':coverage,'end_soc':round(max(0,min(100,energy/capacity_wh*100)),2),
            'minimum_soc':round(max(0,min(100,minimum/capacity_wh*100)),2),'missing_hours':missing,
            'reserve_shortfall_wh':round(max(0,reserve_wh-energy),2),
            'expected_pv_wh':round(produced,2),'expected_load_wh':round(consumed,2),
            'full_charge_time':full_at,'cover_time':cover_at,'weather_factor':factor,
            'available_bridge_wh':max(0,soc/100*capacity_wh-floor_wh),
            'required_bridge_wh':max(0,(soc/100*capacity_wh)-minimum)}
