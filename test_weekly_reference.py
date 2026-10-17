"""Weekly references are read-only helpers; live energy and hardware guards decide."""
from collections import deque
from datetime import datetime, timedelta
from pathlib import Path
import copy
import json
import tempfile
import unittest
from unittest.mock import patch

from history_model import LOCAL, _clean_day, build_weekly_profiles, curve_value, load_exports, plan, week_metrics
from simulate_decisions import solar
from status_messages import status, phases
from test_solarman_power_fields import payload, T


def row(at,pv=3000,soc=80):
    return dict(ts=at.isoformat(),power=pv,battery=soc,consumption=300)


class WeeklyReferenceTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(patch.object(solar,'send_telegram_message'))
        self.enterContext(patch.object(solar,'_last_power_notice_key',None))
        self.now=datetime(2026,10,12,10,tzinfo=LOCAL)

    def test_same_calendar_week_all_years_equal_day_weights(self):
        rows=[row(self.now+timedelta(minutes=i),3000) for i in range(15)]
        rows+=[row(datetime(2025,10,13,10,tzinfo=LOCAL),1000)]
        rows+=[row(self.now+timedelta(days=7),9000)]
        profile=build_weekly_profiles(rows)
        self.assertEqual(profile[42]['years'],[2025,2026])
        self.assertEqual(profile[42]['days'],2)
        self.assertEqual(profile[42]['curve'][40]['pv_w'],2000)
        self.assertEqual(profile[43]['curve'][40]['pv_w'],9000)
        self.assertEqual(sum(p['samples'] for p in profile.values()),len(rows))

    def test_isolated_pv_soc_excursions_are_filtered_without_mutating_raw_rows(self):
        rows=[row(self.now+timedelta(minutes=5*i),500 if i==2 else 3000,10 if i==2 else 80) for i in range(5)]
        original=copy.deepcopy(rows)
        self.assertEqual(_clean_day(rows,'power'),([3000]*5,1))
        self.assertEqual(_clean_day(rows,'battery'),([80]*5,1))
        self.assertEqual(build_weekly_profiles(rows)[42]['outlier_points'],2)
        self.assertEqual(rows,original)

    def test_sustained_clouds_and_unobserved_gaps_are_not_erased(self):
        rows=[row(self.now+timedelta(minutes=5*i),500 if i in (2,3) else 3000) for i in range(7)]
        self.assertEqual(_clean_day(rows,'power')[0],[r['power'] for r in rows])
        rows=[row(self.now+timedelta(minutes=10*i),500 if i==2 else 3000) for i in range(5)]
        self.assertEqual(_clean_day(rows,'power')[1],0)

    def test_interpolates_short_internal_gaps_only_with_support_provenance(self):
        p=build_weekly_profiles([row(self.now,1000),row(self.now+timedelta(minutes=30),3000),
                                 row(self.now+timedelta(hours=3),2000)])[42]
        self.assertEqual(curve_value(p,615,'pv_w'),2000)
        self.assertTrue(p['curve'][41]['pv_w_interpolated'])
        self.assertEqual(p['curve'][41]['pv_days'],1)
        self.assertIsNone(curve_value(p,660,'pv_w'))
        self.assertIsNone(curve_value(p,540,'pv_w'))
        self.assertEqual(len(p['curve']),96)

    def test_duplicate_copies_cannot_bias_conflicting_values_or_discard_valid_channels(self):
        base={'Updated Time':'2026/10/12 10:00','Time Zone':'UTC+02:00',
              'Production Power(W)':1000,'Consumption Power(W)':300,'SoC(%)':80}
        with tempfile.TemporaryDirectory() as root:
            path=Path(root)/'export.json'
            path.write_text(json.dumps([base,dict(base,**{'Production Power(W)':3000}),
                dict(base,**{'Updated Time':'2026/10/12 10:05','SoC(%)':'bad'})]))
            before=path.read_bytes()
            first=load_exports(root)
            (Path(root)/'copy.json').write_bytes(before)
            second=load_exports(root)
            self.assertEqual(first['rows'],second['rows'])
            self.assertEqual(second['rows'][0]['power'],2000)
            self.assertEqual(second['rows'][1]['power'],1000)
            self.assertIsNone(second['rows'][1]['battery'])
            self.assertEqual(path.read_bytes(),before)

    def test_live_capacity_not_historical_soc_grants_bridge(self):
        rows=[row(self.now.replace(hour=h,minute=m),3000 if 11<=h<16 else 0,100)
              for h in range(24) for m in (0,15,30,45)]
        p=build_weekly_profiles(rows)[42]
        result=plan(p,self.now,self.now.replace(hour=18),20,0,300,False,10000,900,
                    weather='solar_friendly',reserve_soc=90)
        self.assertFalse(result['safe'])
        result=plan(p,self.now,self.now.replace(hour=18),90,0,300,False,10000,900,
                    weather='solar_friendly',reserve_soc=90)
        self.assertTrue(result['safe'],result)
        self.assertGreater(result['minimum_soc'],20)
        self.assertGreaterEqual(result['end_soc'],90)

    def test_metrics_report_units_times_and_missing_channels_honestly(self):
        p=build_weekly_profiles([row(self.now,2000,None),row(self.now+timedelta(minutes=15),3000,None)])[42]
        m=week_metrics(p,1050)
        self.assertEqual(m['production_start'],'10:00')
        self.assertEqual(m['miner_cover'],'10:00')
        self.assertEqual((m['peak_w'],m['peak_time']),(3000,'10:15'))
        self.assertEqual(m['pv_energy_wh'],1250)
        self.assertEqual(m['pv_coverage_hours'],.5)
        self.assertIsNone(m['soc_min'])

    def test_afternoon_cutoff_is_immediate_below_90_when_pv_disappears(self):
        def decide(hour,soc,pv):
            now=self.now.replace(hour=hour)
            hints={'energy_budget':{'safe':True,'coverage':1,'reason':'bridge_and_night_reserve_covered'},'window_extension_minutes':0}
            with patch.object(solar,'_history_recommendation',return_value=hints), \
                 patch.object(solar,'_control_window_details',return_value={'active':True,'reason':'daylight'}):
                return solar._make_miner_decision(now,'production',soc,pv,0,400,400,800,
                    'clear sky',0,'clear sky',0,'clear sky',0,now.replace(hour=7),now.replace(hour=18),
                    {},{},52,200,{'summary_5d':'solar_friendly'})
        cutoff=decide(15,89,0)
        self.assertEqual(cutoff['desired_state'],'stop')
        self.assertTrue(cutoff['hard_stop'])
        self.assertIn('Afternoon cutoff',cutoff['decision_summary'])
        for case in [(15,90,0),(13,89,0),(15,89,100)]:
            self.assertEqual(decide(*case)['desired_state'],'production')

    def test_reference_api_independent_of_history_filter(self):
        p=build_weekly_profiles([row(self.now)])
        with patch.object(solar,'historical_profile',{'rows':[row(self.now)],'weeks':p}):
            a=solar._build_snapshot_payload('2026-10-12','2026-10-12')
            b=solar._build_snapshot_payload('2024-01-01','2024-01-02')
        self.assertEqual(a['weekly_reference'],b['weekly_reference'])
        self.assertEqual(a['weekly_reference']['fixed_axis_minutes'],[0,1440])
        self.assertEqual(b['history_count'],0)

    def test_phase_buffer_only_fresh_real_points_no_json_and_source_change_clears(self):
        buffer=deque(maxlen=288)
        with patch.object(solar,'_live_power_points',buffer), \
             patch.object(solar,'_power_guard',solar.MinerPowerGuard()),patch.object(solar,'is_rpi',False), \
             patch.object(solar,'press_power_button') as press:
            solar.supervise_runtime_by_power(T,'stop',payload())
            solar.supervise_runtime_by_power(T,'stop',payload())
            self.assertEqual(len(buffer),1)
            self.assertEqual([buffer[0][k] for k in ('l1','l2','l3','sum')],[100,550,550,1200])
            solar.supervise_runtime_by_power(T+timedelta(hours=1),'stop',payload())
            self.assertEqual(len(buffer),1)  # stale poll cannot add a fresh point
            later=T+timedelta(days=1,minutes=1)
            new=payload();new['collectionTime']=later.timestamp()
            solar.supervise_runtime_by_power(later,'stop',new)
            self.assertEqual(len(buffer),1)
            new['collectionTime']=(later+timedelta(minutes=5)).timestamp()
            new['dataList'] += [{'key':'E_Puse_t1','value':1200,'unit':'W'},
                 *[{'key':k,'value':v,'unit':'W'} for k,v in zip(('LPP_A','LPP_B','LPP_C'),(100,550,550))]]
            solar.supervise_runtime_by_power(later+timedelta(minutes=5),'stop',new)
            self.assertEqual(len(buffer),1)
            self.assertEqual(buffer[0]['source'],'consumption:LPP')
            press.assert_not_called()

    def test_telegram_matches_current_plan_no_obsolete_scoring_or_fake_zero(self):
        snap={'state':'stop','battery':89,'power':0,'hashrate_text':'200 TH/s',
              'weekly_reference':{'week':42,'years':[2025,2026],'days':12,'samples':3104,
                                  'metrics':{'peak_time':'12:00','peak_w':3000}},
              'historical_hints':{'decision_summary':'STOP: Afternoon cutoff',
                  'energy_budget':{'safe':False,'minimum_soc':85,'end_soc':95,'reserve_soc':90,
                                   'required_bridge_wh':500,'available_bridge_wh':700}},
              'power_measurement':{'l1':25,'l2':808,'l3':408,'total':1241,'at':self.now.isoformat(),'fresh':True},
              'power_measurement_source':'consumption:LPP'}
        text=status(snap,self.now,123,200000)
        for expected in ('2026.10.12. 10:00','42. heti','2025, 2026','85% / 95%','SUM 1241 W','500 Wh','akku < 90%','csak kijelzés'):
            self.assertIn(expected,text)
        for bad in ('None','score','0Ah','NaN'):
            self.assertNotIn(bad,text)
        self.assertLess(len(text),4096)
        self.assertIn('—',status({},self.now))
        self.assertIn('nincs érvényes',phases({}))

    def test_telegram_commands_use_current_shared_formatter_without_solar_api(self):
        with patch.object(solar,'_update_pool_hashrate'), \
             patch.object(solar,'_build_snapshot_payload',return_value={'state':'stop','battery':89,'power':0}), \
             patch.object(solar,'send_telegram_message') as send, \
             patch.object(solar,'fetch_current_data') as fetch:
            solar.process_message('/now',0,0,'stop','clear sky',self.now,self.now,0,None,None)
            self.assertIn('Akku: 89%',send.call_args.args[0])
            self.assertIn('heti referencia',send.call_args.args[0])
            solar.process_message('/phase',0,0,'stop','clear sky',self.now,self.now,0,None,None)
            self.assertIn('nincs érvényes',send.call_args.args[0])
            fetch.assert_not_called()


class RealWeeklyCoverageTests(unittest.TestCase):
    def test_every_unique_export_row_is_in_one_week_and_both_years_are_used(self):
        dataset=solar.build_historical_profile('solarman_json')
        self.assertEqual(len(dataset['weeks']),52)
        self.assertEqual(sum(p['samples'] for p in dataset['weeks'].values()),len(dataset['rows']))
        self.assertGreater(len(dataset['rows']),141177)
        self.assertEqual(dataset['weeks'][42]['years'],[2025,2026])
        self.assertEqual(dataset['weeks'][42]['days'],12)
        self.assertEqual(len(dataset['weeks'][42]['curve']),96)


if __name__=='__main__':
    unittest.main()
