#!/usr/bin/env python3
"""Walk one exported day against a model trained only on earlier Solarman rows."""
import argparse
import json
import os
from datetime import datetime, timedelta
from pathlib import Path
from history_model import load_exports, LOCAL

_DEFAULT_ENV = {
    'MY_BOT_TOKEN':'simulate','MY_CHAT_ID':'simulate','MY_WEATHER_API':'simulate',
    'MY_LOCATION_LAT':'47.4979','MY_LOCATION_LON':'19.0402','MY_APP_ID':'simulate',
    'MY_APP_SECRET':'simulate','MY_EMAIL':'simulate','MY_PASSWORD':'simulate',
    'MY_DEVICE_SN':'simulate','MY_QUOTE_FILE':'quote_sim.json','MY_STATE_FILE':'state_sim.json',
    'WALLET_ADDRESS':'0xaedac36dcfc956864fcc03ec2ef256facaefd991',
}
for key,value in _DEFAULT_ENV.items():
    os.environ.setdefault(key,value)
import solar


def replay(history_dir, day=None):
    exports=load_exports(history_dir)
    if not exports['rows']:
        raise ValueError('No valid Solarman exports')
    day=day or exports['rows'][-1]['ts'][:10]
    cutoff=datetime.fromisoformat(day).replace(tzinfo=LOCAL)
    solar.historical_profile=solar.build_historical_profile(str(history_dir),before=cutoff)
    rows=[r for r in exports['rows'] if datetime.fromisoformat(r['ts']).date()==cutoff.date()
          and all(r.get(k) is not None for k in ('power','battery','consumption'))]
    if not rows:
        raise ValueError('Selected date has no exported measurements')
    state='stop'
    transitions=[]
    counts={'production':0,'stop':0}
    for row in rows:
        now=datetime.fromisoformat(row['ts'])
        # A deterministic scenario, not reconstructed historical weather/phase data.
        sunrise=now.replace(hour=7,minute=0,second=0,microsecond=0)
        sunset=now.replace(hour=17,minute=0,second=0,microsecond=0)
        decision=solar._make_miner_decision(now,state,row['battery'],row['power'],0,0,0,row['consumption'],
            'unknown',100,'unknown',100,'unknown',100,sunrise,sunset,{}, {},
            solar.BATTERY_NOMINAL_V,solar.BATTERY_CAPACITY_AH,{'summary_5d':'unknown'})
        desired=decision['desired_state']
        if desired!=state:
            transitions.append({'ts':row['ts'],'from':state,'to':desired,'reason':decision['decision_summary']})
        state=desired
        counts[state]+=1
    return {'date':day,'historical_training_rows':solar.historical_profile['unique_timestamps'],
            'training_before':cutoff.isoformat(),'replayed_rows':len(rows),'decision_counts':counts,
            'transitions':transitions,
            'limitations':['Exported SOC/load are observations, not counterfactual battery outcomes.',
                           'Unknown weather and fixed 07:00–17:00 solar window are explicit scenario inputs.',
                           'No historical mining/phase states are inferred; no GPIO or API calls are made.']}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--history-dir',type=Path,default=Path('solarman_json'))
    parser.add_argument('--date',help='YYYY-MM-DD; default latest exported local date')
    args=parser.parse_args()
    print(json.dumps(replay(args.history_dir,args.date),indent=2))
