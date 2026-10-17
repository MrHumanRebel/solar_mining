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
    directories = [directory] if isinstance(directory, (str, Path)) else directory
    files = sorted({p.resolve() for d in directories for p in Path(d).rglob('*.json')})
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
            if not isinstance(row,dict):
                invalid += 1
                continue
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
                         'pv_p75':quantile([r['power'] for r in rs],.75),
                         'load_p25':quantile([r['consumption'] for r in rs],.25),
                         'load_p50':quantile([r['consumption'] for r in rs],.5),
                         'load_p75':quantile([r['consumption'] for r in rs],.75),
                         'samples':len(rs)} for h,rs in hours.items()}}


def plan(profile, now, sunset, soc, pv, load, running, capacity_wh, miner_w,
         floor_soc=20, reserve_soc=None, weather='unknown', startup_wh=120,
         forecast=None, current_condition='unknown', clouds=None,
         production_stop=None, next_sunrise=None, min_run_minutes=18,
         bridge_safety_factor=1.25, reserve_floor_soc=None):
    """Plan a battery bridge, a finite mining run, and household-only refill.

    SOC projections describe the proposed finite run, not an assumption that
    mining continues all day. Daytime historical load is unlabelled, so current
    household demand drives daytime costs; historical night load sizes reserve.
    """
    valid = (profile and profile.get('days',0)>=3 and
             all(isinstance(v,(int,float)) and math.isfinite(v) for v in
                 (soc,pv,load,capacity_wh,miner_w,startup_wh,floor_soc)) and
             capacity_wh>0 and miner_w>=0 and startup_wh>=0 and
             0<=floor_soc<=100 and 0<=soc<=100 and pv>=0 and load>=0 and now<sunset)
    empty = {'safe':False,'reason':'insufficient_history_or_live_data','coverage':0,
             'end_soc':None,'minimum_soc':None,'missing_hours':True,
             'planned_stop':None,'cover_time':None}
    if not valid:
        return empty
    hours = profile['hours']
    stop = min(production_stop or sunset, sunset)
    next_sunrise = next_sunrise or (sunset+timedelta(days=1)).replace(hour=7,minute=0)
    if not sunset<next_sunrise<=sunset+timedelta(hours=24):
        return dict(empty,reason='invalid_overnight_time_window')
    def hourly(at):
        return hours.get(at.hour,{})
    def enough(at):
        return hourly(at).get('samples',0)>=3
    def kind(condition, cloud=None):
        c=str(condition).lower()
        if any(w in c for w in ('rain','snow','storm','drizzle')):
            return 'solar_weak'
        if any(w in c for w in ('clear','sun','fair')):
            return 'solar_friendly'
        if cloud is not None and cloud>=85:
            return 'solar_weak'
        if 'cloud' in c or 'overcast' in c:
            return 'mixed'
        return 'unknown'
    weather_points=[]
    for entry in forecast or []:
        try:
            at=datetime.fromisoformat(entry['ts'])
            if at.tzinfo is None:
                at=at.replace(tzinfo=LOCAL)
            weather_points.append((at,kind(entry.get('condition','unknown'),entry.get('clouds'))))
        except (ValueError,KeyError,TypeError):
            continue
    weather_points.sort()
    def solar(at):
        h=hourly(at)
        # Use the nearest 3-hour forecast only within its actual horizon.
        risk=weather
        if weather_points:
            nearest=min(weather_points,key=lambda item:abs((item[0]-at).total_seconds()))
            risk=nearest[1] if abs((nearest[0]-at).total_seconds())<=3*3600 else 'unknown'
        elif kind(current_condition,clouds)!='unknown':
            risk=kind(current_condition,clouds)
        median_pv=h.get('pv_p50',h.get('pv_p25',0))
        if risk=='solar_friendly':
            expected=h.get('pv_p75',median_pv)*.9
        elif risk=='solar_weak':
            expected=h.get('pv_p25',median_pv)*.65
        else:
            expected=median_pv*(.85 if risk=='mixed' else .8)
        if profile.get('interpolated'):
            expected*=.8
        # A cloud/dawn sample constrains the immediate bridge, not every hour
        # of the day. Its influence fades over the next hour.
        weight=max(0,1-(at-now).total_seconds()/3600)
        return max(0,expected*(1-weight)+pv*weight)
    house_now=max(0,load-(miner_w if running else 0))
    def house(at):
        # Daytime exports can already include this same miner. Current measured
        # non-rig demand is authoritative; never add historical mining again.
        return house_now
    # Reserve overnight household energy, not a blanket 90%/100% requirement.
    night_wh=0
    at=sunset
    missing_night=False
    while at<next_sunrise:
        end=min(at+timedelta(minutes=5),next_sunrise)
        missing_night |= not enough(at)
        h=hourly(at)
        night_wh+=h.get('load_p50',h.get('load_p75',0))*(end-at).total_seconds()/3600
        at=end
    floor_wh=capacity_wh*floor_soc/100
    reserve_floor_wh=capacity_wh*(floor_soc if reserve_floor_soc is None else reserve_floor_soc)/100
    target_wh=(reserve_floor_wh+night_wh/0.9*1.1 if reserve_soc is None else reserve_soc/100*capacity_wh)
    if missing_night and reserve_soc is None:
        return dict(empty,reason='missing_overnight_history')
    steps=[]
    at=now
    while at<sunset:
        end=min(at+timedelta(minutes=5),sunset)
        steps.append((at,end,solar(at),house(at),enough(at)))
        at=end
    if any(not row[4] for row in steps):
        return dict(empty,reason='missing_daytime_history')
    cover=None
    for i,(at,_,expected,household,_) in enumerate(steps):
        until=at+timedelta(minutes=min_run_minutes)
        segment=[row for row in steps[i:] if row[0]<until]
        if (until<=stop and segment and all(row[2]>=row[3]+miner_w for row in segment)):
            cover=at
            break
    initial=capacity_wh*soc/100
    # A candidate must run for a useful minimum period, then may stop early
    # enough to recharge. Re-evaluate it at each scheduled live measurement.
    minimum_stop=now+timedelta(minutes=min_run_minutes)
    candidates=[row[1] for row in steps if minimum_stop<=row[1]<=stop]
    def simulate(until):
        energy=initial-(0 if running else startup_wh)
        minimum=energy
        bridge_min=energy
        produced=consumed=0.0
        full_at=None
        for at,end,expected,household,_ in steps:
            demand=household+(miner_w if at<until else 0)
            dt=(end-at).total_seconds()/3600
            net=(expected-demand)*dt
            energy=min(capacity_wh,energy+(net*.9 if net>=0 else net/.9))
            minimum=min(minimum,energy)
            if cover is None or at<cover:
                bridge_min=min(bridge_min,energy)
            if full_at is None and energy>=capacity_wh*.995:
                full_at=end.isoformat()
            produced+=expected*dt
            consumed+=demand*dt
        bridge=max(0,initial-bridge_min)
        return energy,minimum,bridge,produced,consumed,full_at
    chosen=None
    reason='insufficient_time_for_minimum_run'
    result=simulate(now)  # Household-only outlook if no useful run fits.
    for until in reversed(candidates):
        result_candidate=simulate(until)
        ending,minimum,bridge,*_=result_candidate
        if target_wh>capacity_wh:
            reason='overnight_reserve_exceeds_battery_capacity'
        elif minimum<floor_wh:
            reason='battery_floor_would_be_crossed'
        elif (not running and now.hour<12 and
              (cover is None or cover>=until)):
            reason='no_sustained_solar_cover_for_morning_start'
        elif bridge*bridge_safety_factor>max(0,initial-floor_wh):
            reason='insufficient_battery_bridge'
        elif ending<target_wh:
            reason='night_household_reserve_not_recovered'
        else:
            chosen=until
            result=result_candidate
            reason='bridge_and_night_reserve_covered'
            break
        # Expose the useful minimum-run scenario when all candidates fail.
        result=result_candidate
    ending,minimum,bridge,produced,consumed,full_at=result
    return {'safe':chosen is not None,'reason':reason,'coverage':min(1,profile['days']/20),
            'end_soc':round(max(0,min(100,ending/capacity_wh*100)),2),
            'minimum_soc':round(max(0,min(100,minimum/capacity_wh*100)),2),
            'missing_hours':False,'reserve_soc':round(target_wh/capacity_wh*100,1),
            'required_reserve_wh':round(target_wh,1),
            'night_household_wh':round(night_wh,1),'reserve_shortfall_wh':round(max(0,target_wh-ending),1),
            'planned_stop':chosen.isoformat() if chosen else None,
            'projection_mode':'approved_run' if chosen else 'rejected_minimum_run',
            'cover_time':cover.isoformat() if cover else None,'full_charge_time':full_at,
            'expected_pv_wh':round(produced,1),'expected_load_wh':round(consumed,1),
            'available_bridge_wh':round(max(0,initial-floor_wh),1),
            'required_bridge_wh':round(bridge*bridge_safety_factor,1)}
