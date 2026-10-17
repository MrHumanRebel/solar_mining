import copy
import json
from datetime import datetime, timedelta
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from solar_mining.history_model import LOCAL, plan
from tools.simulate_decisions import solar


class BridgePlanningTests(unittest.TestCase):
    def setUp(self):
        self.now=datetime(2026,7,10,7,tzinfo=LOCAL)
        self.profile={'days':30,'hours':{h:{'samples':30,'pv_p25':0,'pv_p50':0,'pv_p75':0,
                       'load_p25':250,'load_p50':300,'load_p75':1500} for h in range(24)}}
        for h in range(9,16):
            self.profile['hours'][h].update(pv_p25=1500,pv_p50=3000,pv_p75=3500)
    def budget(self,**overrides):
        args=dict(profile=self.profile,now=self.now,sunset=self.now.replace(hour=19),
                  production_stop=self.now.replace(hour=17,minute=30),next_sunrise=self.now+timedelta(days=1),
                  soc=80,pv=0,load=300,running=False,capacity_wh=11000,miner_w=900,weather='solar_friendly')
        args.update(overrides)
        return plan(**args)

    def test_sunny_dawn_bridges_to_cover_and_refills_after_an_early_stop(self):
        result=self.budget()
        self.assertTrue(result['safe'],result)
        self.assertGreater(result['minimum_soc'],20)
        self.assertGreater(result['end_soc'],result['reserve_soc'])
        self.assertLess(result['required_bridge_wh'],result['available_bridge_wh'])
        self.assertEqual(result['cover_time'],self.now.replace(hour=9).isoformat())
        self.assertIsNotNone(result['planned_stop'])

    def test_bridge_is_limited_by_available_energy_not_an_arbitrary_three_hour_delay(self):
        now=self.now.replace(hour=5)
        result=self.budget(now=now,soc=95,capacity_wh=16000)
        self.assertTrue(result['safe'],result)
        self.assertEqual(result['cover_time'],now.replace(hour=9).isoformat())
        self.assertLess(result['required_bridge_wh'],result['available_bridge_wh'])

    def test_low_soc_or_rain_cannot_borrow_the_night_reserve(self):
        self.assertFalse(self.budget(soc=25)['safe'])
        self.assertFalse(self.budget(soc=35,weather='solar_weak')['safe'])

    def test_near_term_forecast_overrides_an_unrelated_sunny_week(self):
        forecast=[{'ts':self.now.replace(hour=h).isoformat(),'condition':'heavy rain','clouds':100}
                  for h in (7,10,13,16,19)]
        bad=self.budget(soc=55,forecast=forecast)
        good=self.budget(soc=55,forecast=[dict(e,condition='clear sky',clouds=0) for e in forecast])
        self.assertFalse(bad['safe'])
        self.assertTrue(good['safe'],good)
        self.assertLess(bad['expected_pv_wh'],good['expected_pv_wh'])

    def test_weather_summary_retains_timestamped_forecasts_for_the_planner(self):
        at=self.now+timedelta(hours=2)
        payload={'list':[{'dt':at.timestamp(),'weather':[{'description':'clear sky'}],
                          'clouds':{'all':5}}]}
        outlook=solar._summarize_free_weather_outlook(payload,self.now)
        self.assertEqual(datetime.fromisoformat(outlook['forecast'][0]['ts']),at)
        self.assertEqual(outlook['forecast'][0]['condition'],'clear sky')
        self.assertEqual(outlook['forecast'][0]['clouds'],5)

    def test_cloud_at_dawn_does_not_erase_the_entire_day_forecast(self):
        dawn=self.budget(pv=0)
        self.assertTrue(dawn['safe'])
        self.assertGreater(dawn['expected_pv_wh'],12000)

    def test_afternoon_can_run_below_full_charge_and_keeps_night_reserve(self):
        now=self.now.replace(hour=14)
        result=self.budget(now=now,soc=78,pv=3000)
        self.assertTrue(result['safe'],result)
        self.assertLess(result['reserve_soc'],90)
        self.assertGreaterEqual(result['end_soc'],result['reserve_soc'])

    def test_afternoon_battery_run_can_stop_early_without_waiting_for_another_solar_peak(self):
        now=self.now.replace(hour=14)
        for h in range(14,24):
            self.profile['hours'][h].update(pv_p25=0,pv_p50=0,pv_p75=0)
        result=self.budget(now=now,soc=95,pv=0)
        self.assertTrue(result['safe'],result)
        self.assertIsNone(result['cover_time'])
        self.assertGreaterEqual(result['end_soc'],result['reserve_soc'])
        self.assertLess(datetime.fromisoformat(result['planned_stop']),now.replace(hour=17,minute=30))

    def test_running_rig_can_bridge_a_cloud_without_requiring_a_new_start_cover_event(self):
        now=self.now.replace(hour=11)
        for h in range(11,24):
            self.profile['hours'][h].update(pv_p25=0,pv_p50=0,pv_p75=0)
        result=self.budget(now=now,soc=100,pv=0,load=1200,running=True)
        self.assertTrue(result['safe'],result)
        self.assertGreaterEqual(result['end_soc'],result['reserve_soc'])

    def test_long_night_requires_more_reserve_than_short_night(self):
        short=self.budget(next_sunrise=self.now.replace(day=11,hour=5))
        long=self.budget(next_sunrise=self.now.replace(day=11,hour=9))
        self.assertGreater(long['night_household_wh'],short['night_household_wh'])
        self.assertGreater(long['reserve_soc'],short['reserve_soc'])

    def test_finite_plan_stops_early_to_refill_instead_of_rejecting_all_mining(self):
        for h in range(9,17):
            self.profile['hours'][h].update(pv_p25=1000,pv_p50=1700,pv_p75=1900)
        result=self.budget(soc=65,load=500)
        self.assertTrue(result['safe'],result)
        self.assertLess(datetime.fromisoformat(result['planned_stop']),self.now.replace(hour=17,minute=30))
        self.assertGreaterEqual(result['end_soc'],result['reserve_soc'])

    def test_unaffordable_night_reserve_is_not_hidden_by_clamping_it_to_100_percent(self):
        for h in range(19,24):
            self.profile['hours'][h]['load_p50']=3000
        result=self.budget(soc=100,load=3000)
        self.assertFalse(result['safe'])
        self.assertGreater(result['reserve_soc'],100)
        self.assertEqual(result['reason'],'overnight_reserve_exceeds_battery_capacity')

    def test_invalid_night_horizon_never_becomes_a_zero_reserve(self):
        result=self.budget(next_sunrise=self.now)
        self.assertFalse(result['safe'])
        self.assertEqual(result['reason'],'invalid_overnight_time_window')

    def test_yesterdays_weather_clock_does_not_remove_tonights_reserve(self):
        yesterday=self.now-timedelta(days=1)
        with patch.object(solar,'historical_profile',{'weeks':{self.now.isocalendar().week:self.profile}}), \
             patch.object(solar,'_weather_daylight',(yesterday,yesterday.replace(hour=19))):
            hints=solar._history_recommendation(self.now,80,0,self.now,self.now.replace(hour=17,minute=30),
                {'summary_5d':'solar_friendly'},300,False,55,200,'clear sky',0)
            self.assertGreater(hints['energy_budget']['night_household_wh'],3000)
            self.assertGreater(hints['energy_budget']['reserve_soc'],50)

    def test_no_unlabelled_historical_miner_is_added_to_live_load_again(self):
        expected=self.budget()
        for h in self.profile['hours'].values():
            h['load_p25']=1400
            h['load_p75']=2400
        result=self.budget()
        self.assertEqual(result['expected_load_wh'],expected['expected_load_wh'])
        self.assertEqual(result['safe'],expected['safe'])

    def test_running_load_deducts_rig_once_for_household_only_refill(self):
        stopped=self.budget(load=300)
        running=self.budget(load=1200,running=True)
        self.assertEqual(stopped['expected_load_wh'],running['expected_load_wh'])
        self.assertGreaterEqual(running['minimum_soc'],stopped['minimum_soc'])


class HistoryRangeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dataset=solar.build_historical_profile('solarman_json')

    def test_real_july_august_2026_range_contains_downloaded_rows(self):
        with patch.object(solar,'historical_profile',self.dataset):
            iso=solar._build_snapshot_payload('2026-07-10','2026-08-10')
            hu=solar._build_snapshot_payload('2026.07.10.','2026.08.10.')
            self.assertGreater(iso['history_count'],8000)
            self.assertEqual(iso['history'],hu['history'])
            self.assertTrue(all('2026-07-10'<=r['ts'][:10]<='2026-08-10' for r in iso['history']))
            self.assertEqual(iso['history_available_to'],'2026-10-16')

    def test_real_october_profile_does_not_force_zero_soc_on_a_sunny_bridge(self):
        now=datetime(2026,10,17,8,tzinfo=LOCAL)
        result=plan(self.dataset['weeks'][42],now,now.replace(hour=18),80,400,400,False,
                    10580,1050,26,None,'solar_friendly',120,
                    production_stop=now.replace(hour=16,minute=30),
                    next_sunrise=now.replace(day=18,hour=7),reserve_floor_soc=20)
        self.assertTrue(result['safe'],result)
        self.assertGreater(result['minimum_soc'],50)
        self.assertGreater(result['end_soc'],result['reserve_soc'])

    def test_invalid_live_values_are_unavailable_not_invalid_json_or_zero(self):
        with patch.object(solar,'historical_profile',{'rows':[]}), \
             patch.dict(solar._shared_snapshot,{'battery':float('nan'),'power':None}):
            payload=solar._build_snapshot_payload()
            self.assertIsNone(payload['battery'])
            self.assertIsNone(payload['power'])
            json.dumps(payload,allow_nan=False)

    def test_bad_or_inverted_range_is_not_silently_replaced(self):
        with patch.object(solar,'historical_profile',self.dataset):
            for start,end in [('2026-08-10','2026-07-10'),('10/07/2026','2026-08-10')]:
                with self.assertRaises(ValueError):
                    solar._build_snapshot_payload(start,end)

    def test_old_host_mount_does_not_hide_complete_bundled_history(self):
        row={'Updated Time':'2025/05/01 12:00','Time Zone':'UTC+01:00',
             'Production Power(W)':100,'Consumption Power(W)':200,'SoC(%)':80}
        with tempfile.TemporaryDirectory() as root:
            host=Path(root)/'host'
            bundle=Path(root)/'bundle'
            host.mkdir();bundle.mkdir()
            (host/'old.json').write_text(json.dumps([row]))
            (bundle/'new.json').write_text(json.dumps([row,dict(row,**{'Updated Time':'2026/07/10 12:00'})]))
            before={p:p.read_bytes() for p in Path(root).rglob('*.json')}
            data=solar.build_historical_profile(host,bundled_dir=bundle)
            self.assertEqual(len(data['rows']),2)
            with patch.object(solar,'historical_profile',data):
                self.assertEqual(solar._build_snapshot_payload('2026-07-10','2026-07-10')['history_count'],1)
            self.assertEqual(before,{p:p.read_bytes() for p in Path(root).rglob('*.json')})

    def test_empty_selection_reports_actual_available_history(self):
        with patch.object(solar,'historical_profile',self.dataset):
            payload=solar._build_snapshot_payload('2024-07-10','2024-08-10')
            self.assertEqual(payload['history_count'],0)
            self.assertGreater(payload['history_total_count'],140000)
            self.assertTrue(payload['history_available_from'].startswith('2025-05'))


if __name__=='__main__':
    unittest.main()
