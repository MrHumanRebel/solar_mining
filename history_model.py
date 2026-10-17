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
from statistics import mean, median
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
    grouped = {}
    invalid = raw_count = 0
    directories = [directory] if isinstance(directory, (str, Path)) else directory
    files = sorted({p.resolve() for d in directories for p in Path(d).rglob('*.json')})
    for path in files:
        try:
            payload=json.loads(path.read_text(encoding='utf-8'))
        except (OSError,ValueError):
            invalid+=1
            continue
        if not isinstance(payload,list):
            invalid+=1
            continue
        for row in payload:
            try:
                at=datetime.strptime(row['Updated Time'],'%Y/%m/%d %H:%M')
                zone=row.get('Time Zone')
                if zone:
                    match=re.fullmatch(r'UTC([+-])(\d{2}):(\d{2})',zone)
                    if not match or int(match[2])>23 or int(match[3])>59:
                        raise ValueError('invalid offset')
                    offset=timedelta(hours=int(match[2]),minutes=int(match[3]))*(1 if match[1]=='+' else -1)
                    at=at.replace(tzinfo=timezone(offset)).astimezone(LOCAL)
                else:
                    at=at.replace(tzinfo=LOCAL)
                if before is not None and at>=before:
                    continue
                values={}
                bad=False
                for key,label in [('power','Production Power(W)'),('consumption','Consumption Power(W)'),('battery','SoC(%)')]:
                    try:
                        value=float(row[label])
                        if not math.isfinite(value) or value<0 or (key=='battery' and value>100):
                            raise ValueError('invalid measurement')
                        values[key]=value
                    except (ValueError,TypeError,KeyError):
                        values[key]=None
                        bad=True
                invalid+=int(bad)
                if not any(v is not None for v in values.values()):
                    continue
                # UTC identifies instants, including the repeated DST hour.
                key=at.astimezone(timezone.utc)
                channels=grouped.setdefault(key,{k:set() for k in values})
                for channel,value in values.items():
                    if value is not None:
                        channels[channel].add(value)
                raw_count+=1
            except (KeyError,TypeError,ValueError,OverflowError):
                invalid+=1
    rows=[{'ts':at.astimezone(LOCAL).isoformat(),**{k:median(v) if v else None for k,v in channels.items()}}
          for at,channels in sorted(grouped.items())]
    return {'rows':rows,'files':len(files),'invalid_rows':invalid,
            'duplicate_timestamps':raw_count-len(rows),'unique_timestamps':len(rows)}


def _clean_day(rows, channel):
    """Replace an isolated excursion only when both sides agree, at most 20 min apart."""
    values=[r.get(channel) for r in rows]
    result=list(values)
    removed=0
    for i in range(2,len(rows)-2):
        window=values[i-2:i+3]
        if any(v is None for v in window):
            continue
        times=[datetime.fromisoformat(r['ts']).astimezone(timezone.utc) for r in rows[i-2:i+3]]
        if (times[-1]-times[0]).total_seconds()>1200:
            continue
        if any(not 0<(b-a).total_seconds()<=600 for a,b in zip(times,times[1:])):
            continue
        neighbours=window[:2]+window[3:]
        middle=median(neighbours)
        agreement=max(150,.2*middle) if channel=='power' else 3
        excursion=max(300,.35*middle) if channel=='power' else 8
        if max(neighbours)-min(neighbours)<=agreement and abs(values[i]-middle)>excursion:
            result[i]=middle
            removed+=1
    return result,removed


def build_weekly_profiles(rows):
    """Every unique row contributes to its ISO calendar week across all years.

    First aggregate each day into 15-minute bins; then average days with equal
    weight. Raw rows remain unchanged. Long gaps stay missing.
    """
    days=defaultdict(list)
    for row in rows:
        days[datetime.fromisoformat(row['ts']).date()].append(row)
    weeks=defaultdict(lambda:{'days':set(),'years':set(),'samples':0,'outliers':0,
                              'bins':defaultdict(lambda:defaultdict(list))})
    for date,day in sorted(days.items()):
        day=sorted(day,key=lambda r:datetime.fromisoformat(r['ts']).timestamp())
        pv,pv_removed=_clean_day(day,'power')
        soc,soc_removed=_clean_day(day,'battery')
        year,week,_=date.isocalendar()
        target=weeks[week]
        target['days'].add(date.isoformat());target['years'].add(year)
        target['samples']+=len(day);target['outliers']+=pv_removed+soc_removed
        bins=defaultdict(lambda:defaultdict(list))
        for i,row in enumerate(day):
            at=datetime.fromisoformat(row['ts'])
            slot=(at.hour*60+at.minute)//15
            for name,value in [('pv',pv[i]),('soc',soc[i])]:
                if value is not None:
                    bins[slot][name].append(value)
        for slot,channels in bins.items():
            for name,values in channels.items():
                target['bins'][slot][name].append(median(values))
    result={}
    for week,source in weeks.items():
        curve=[]
        for slot in range(96):
            pv=source['bins'][slot]['pv'];soc=source['bins'][slot]['soc']
            curve.append({'minute':slot*15,'time':f'{slot//4:02}:{slot%4*15:02}',
                          'pv_w':mean(pv) if pv else None,
                          'pv_p25':quantile(pv,.25) if pv else None,'pv_p75':quantile(pv,.75) if pv else None,
                          'soc_pct':mean(soc) if soc else None,
                          'soc_p25':quantile(soc,.25) if soc else None,'soc_p75':quantile(soc,.75) if soc else None,
                          'pv_days':len(pv),'soc_days':len(soc)})
        # Fill only internal gaps <= 1 hour. Never extrapolate night/day edges.
        for channel,fields in [('pv_w',('pv_w','pv_p25','pv_p75')),('soc_pct',('soc_pct','soc_p25','soc_p75'))]:
            known=[i for i,r in enumerate(curve) if r[channel] is not None]
            for left,right in zip(known,known[1:]):
                if right-left<=4:
                    for i in range(left+1,right):
                        curve[i][channel+'_interpolated']=True
                        support='pv_days' if channel=='pv_w' else 'soc_days'
                        curve[i][support]=min(curve[left][support],curve[right][support])
                        for field in fields:
                            curve[i][field]=curve[left][field]+(curve[right][field]-curve[left][field])*(i-left)/(right-left)
        hours={}
        for hour in range(24):
            points=[r for r in curve[hour*4:hour*4+4] if r['pv_w'] is not None]
            if len(points)==4:
                hours[hour]={'pv_p25':mean(r['pv_p25'] for r in points),
                             'pv_p50':mean(r['pv_w'] for r in points),
                             'pv_p75':mean(r['pv_p75'] for r in points),'samples':min(r['pv_days'] for r in points)}
        result[week]={'week':week,'days':len(source['days']),'dates':sorted(source['days']),
                      'years':sorted(source['years']),'samples':source['samples'],
                      'outlier_points':source['outliers'],'curve':curve,'hours':hours}
    return result


def curve_value(profile, minute, channel):
    curve=profile.get('curve',[])
    if not curve or not 0<=minute<1440:
        return None
    left=min(95,int(minute//15));right=min(95,left+1)
    a,b=curve[left].get(channel),curve[right].get(channel)
    if a is None or b is None:
        return None
    return a+(b-a)*(minute-left*15)/15


def week_metrics(profile, miner_w, current_soc=None, minute=None):
    curve=profile.get('curve',[])
    def first(condition):
        return next((r['time'] for i,r in enumerate(curve[:-1])
                     if condition(r) and condition(curve[i+1])),None)
    pv=[r for r in curve if r['pv_w'] is not None]
    soc=[r for r in curve if r['soc_pct'] is not None]
    peak=max(pv,key=lambda r:r['pv_w']) if pv else {}
    charge=next((r['time'] for i,r in enumerate(curve[:-2]) if r['soc_pct'] is not None
                 and curve[i+2]['soc_pct'] is not None and curve[i+2]['soc_pct']-r['soc_pct']>=1),None)
    peak_soc=max(soc,key=lambda r:r['soc_pct']) if soc else {}
    falling=next((r['time'] for i,r in enumerate(curve[:-2]) if r['minute']>=peak_soc.get('minute',1440)
                  and r['soc_pct'] is not None and curve[i+2]['soc_pct'] is not None
                  and r['soc_pct']-curve[i+2]['soc_pct']>=1),None)
    result={'production_start':first(lambda r:r['pv_w'] is not None and r['pv_w']>=50),
            'miner_cover':first(lambda r:r['pv_w'] is not None and r['pv_w']>=miner_w),
            'peak_time':peak.get('time'),'peak_w':peak.get('pv_w'),
            'pv_energy_wh':sum(r['pv_w']*.25 for r in pv) if pv else None,'pv_coverage_hours':len(pv)/4,
            'charge_start':charge,'discharge_start':falling,'soc_peak_time':peak_soc.get('time'),'soc_min':min((r['soc_pct'] for r in soc),default=None),
            'soc_max':max((r['soc_pct'] for r in soc),default=None)}
    if minute is not None and current_soc is not None:
        anchor=curve_value(profile,minute,'soc_pct')
        if anchor is not None:
            result['anchored_full_time']=next((r['time'] for r in curve
                if r['minute']>=minute and r['soc_pct'] is not None and current_soc+r['soc_pct']-anchor>=99),None)
    return result


def plan(profile, now, sunset, soc, pv, load, running, capacity_wh, miner_w,
         floor_soc=20, reserve_soc=None, weather='unknown', startup_wh=120,
         forecast=None, current_condition='unknown', clouds=None,
         production_stop=None, next_sunrise=None, min_run_minutes=18,
         bridge_safety_factor=1.25, reserve_floor_soc=None):
    """Plan a battery bridge, a finite mining run, and household-only refill.

    SOC projections describe the proposed finite run, not an assumption that
    mining continues all day. Daytime historical load is unlabelled, so current
    household demand drives costs. History supplies only weekly PV/SOC guidance.
    """
    profile=profile or {'days':0,'hours':{}}
    valid = (
             all(isinstance(v,(int,float)) and math.isfinite(v) for v in
                 (soc,pv,load,capacity_wh,miner_w,startup_wh,floor_soc)) and
             capacity_wh>0 and miner_w>=0 and startup_wh>=0 and
             0<=floor_soc<=100 and 0<=soc<=100 and pv>=0 and load>=0 and now<sunset)
    empty = {'safe':False,'reason':'insufficient_history_or_live_data','coverage':0,
             'end_soc':None,'minimum_soc':None,'missing_hours':True,
             'planned_stop':None,'cover_time':None}
    if not valid:
        return empty
    hours = profile.get('hours',{})
    stop = min(production_stop or sunset, sunset)
    next_sunrise = next_sunrise or (sunset+timedelta(days=1)).replace(hour=7,minute=0)
    if not sunset<next_sunrise<=sunset+timedelta(hours=24):
        return dict(empty,reason='invalid_overnight_time_window')
    def hourly(at):
        if profile.get('curve'):
            minute=at.hour*60+at.minute+at.second/60
            values={key:curve_value(profile,minute,field) for key,field in
                    [('pv_p50','pv_w'),('pv_p25','pv_p25'),('pv_p75','pv_p75')]}
            support=curve_value(profile,minute,'pv_days')
            return dict(values,samples=support or 0) if values['pv_p50'] is not None else {}
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
        if 'few clouds' in c or ('cloud' in c and cloud is not None and cloud<=30):
            return 'solar_friendly'
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
    def weather_at(at):
        # Use the nearest 3-hour forecast only within its actual horizon.
        risk=weather
        if weather_points:
            nearest=min(weather_points,key=lambda item:abs((item[0]-at).total_seconds()))
            risk=nearest[1] if abs((nearest[0]-at).total_seconds())<=3*3600 else 'unknown'
        elif kind(current_condition,clouds)!='unknown':
            risk=kind(current_condition,clouds)
        return risk
    def solar(at):
        h=hourly(at)
        risk=weather_at(at)
        median_pv=h.get('pv_p50',h.get('pv_p25',0)) or 0
        if risk=='solar_friendly':
            expected=max(median_pv,h.get('pv_p75',median_pv) or 0)*.9
        elif risk=='solar_weak':
            expected=min(median_pv,h.get('pv_p25',median_pv) or 0)*.65
        else:
            expected=median_pv*(.85 if risk=='mixed' else .8)
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
    while at<next_sunrise:
        end=min(at+timedelta(minutes=5),next_sunrise)
        night_wh+=house_now*(end-at).total_seconds()/3600
        at=end
    floor_wh=capacity_wh*floor_soc/100
    reserve_floor_wh=capacity_wh*(floor_soc if reserve_floor_soc is None else reserve_floor_soc)/100
    target_wh=(reserve_floor_wh+night_wh/0.9*1.1 if reserve_soc is None else reserve_soc/100*capacity_wh)
    steps=[]
    at=now
    while at<sunset:
        end=min(at+timedelta(minutes=5),sunset)
        steps.append((at,end,solar(at),house(at),enough(at)))
        at=end
    missing_day=any(not row[4] for row in steps)
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
    # Bridge is ONLY the physical battery drawdown from now to sustained cover.
    # Never substitute the entire remaining day's deficit when cover is absent.
    bridge_deficit=None
    if cover is not None:
        energy=lowest=initial
        for at,end,expected,household,_ in steps:
            if at>=cover:
                break
            net=(expected-household-miner_w)*(end-at).total_seconds()/3600
            energy=min(capacity_wh,energy+(net*.9 if net>=0 else net/.9))
            lowest=min(lowest,energy)
        bridge_deficit=max(0,initial-lowest)
    startup=0 if running else startup_wh
    required_bridge=None if bridge_deficit is None else bridge_deficit*bridge_safety_factor
    required_start=None if bridge_deficit is None else (bridge_deficit+startup)*bridge_safety_factor

    def simulate(until):
        # A household-only counterfactual does not start the miner.
        energy=initial-(startup if until>now else 0)
        minimum=energy
        produced=consumed=0.0
        full_at=None
        for at,end,expected,household,_ in steps:
            demand=household+(miner_w if at<until else 0)
            dt=(end-at).total_seconds()/3600
            net=(expected-demand)*dt
            energy=min(capacity_wh,energy+(net*.9 if net>=0 else net/.9))
            minimum=min(minimum,energy)
            if full_at is None and energy>=capacity_wh*.995:
                full_at=end.isoformat()
            produced+=expected*dt
            consumed+=demand*dt
        return energy,minimum,produced,consumed,full_at
    # Unlabelled historical SOC includes old household/miner activity. It is
    # reference information, never an extra Wh cost added to today's bridge.
    historical_bridge_wh=None
    if cover is not None and profile.get('curve'):
        start_soc=curve_value(profile,now.hour*60+now.minute,'soc_pct')
        cover_soc=curve_value(profile,cover.hour*60+cover.minute,'soc_pct')
        if start_soc is not None and cover_soc is not None:
            historical_bridge_wh=max(0,start_soc-cover_soc)/100*capacity_wh
    household_only=simulate(now)
    chosen=None
    reason='insufficient_time_for_minimum_run'
    result=household_only  # No minimum-duration candidate may fit before stop.
    for until in reversed(candidates):
        result_candidate=simulate(until)
        ending,minimum,*_=result_candidate
        if target_wh>capacity_wh:
            reason='overnight_reserve_exceeds_battery_capacity'
        elif required_start is not None and required_start>max(0,initial-floor_wh):
            reason='insufficient_battery_bridge'
        elif (not running and now.hour<12 and (cover is None or cover>=until)):
            reason='no_sustained_solar_cover_for_morning_start'
        elif household_only[1]<floor_wh or household_only[0]<target_wh:
            reason='household_only_refill_not_feasible'
        elif minimum<floor_wh:
            reason='battery_floor_would_be_crossed'
        elif ending<target_wh:
            reason='night_household_reserve_not_recovered'
        else:
            chosen=until
            result=result_candidate
            reason='bridge_and_night_reserve_covered'
            break
        # Expose the useful minimum-run scenario when all candidates fail.
        result=result_candidate
    ending,minimum,produced,consumed,full_at=result
    return {'safe':chosen is not None,'reason':reason,'coverage':min(1,profile.get('days',0)/14),
            'end_soc':round(max(0,min(100,ending/capacity_wh*100)),2),
            'minimum_soc':round(max(0,min(100,minimum/capacity_wh*100)),2),
            'missing_hours':missing_day,'reserve_soc':round(target_wh/capacity_wh*100,1),
            'required_reserve_wh':round(target_wh,1),
            'night_household_wh':round(night_wh,1),'reserve_shortfall_wh':round(max(0,target_wh-ending),1),
            'planned_stop':chosen.isoformat() if chosen else None,
            'projection_mode':'approved_run' if chosen else ('rejected_minimum_run' if candidates else 'household_only'),
            'cover_time':cover.isoformat() if cover else None,'full_charge_time':full_at,
            'expected_pv_wh':round(produced,1),'expected_load_wh':round(consumed,1),
            'available_bridge_wh':round(max(0,initial-floor_wh),1),
            'bridge_status':'covered_now' if cover==now else ('until_cover' if cover else 'no_sustained_cover'),
            'bridge_duration_minutes':round((cover-now).total_seconds()/60,1) if cover else None,
            'bridge_deficit_wh':round(bridge_deficit,1) if bridge_deficit is not None else None,
            'required_bridge_wh':round(required_bridge,1) if required_bridge is not None else None,
            'startup_energy_wh':round(startup,1),
            'required_start_energy_wh':round(required_start,1) if required_start is not None else None,
            'household_only_end_soc':round(max(0,min(100,household_only[0]/capacity_wh*100)),2),
            'household_only_minimum_soc':round(max(0,min(100,household_only[1]/capacity_wh*100)),2),
            'household_load_w':round(house_now,1),
            'historical_bridge_wh':round(historical_bridge_wh,1) if historical_bridge_wh is not None else None}
