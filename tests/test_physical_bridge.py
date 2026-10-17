"""Regressions for real bridge Wh, distinct from the full-day refill outlook."""
import copy
from datetime import datetime, timedelta
import unittest
from unittest.mock import patch
from solar_mining.history_model import LOCAL, plan
from tools.simulate_decisions import solar
from solar_mining.status_messages import status


class PhysicalBridgeTests(unittest.TestCase):
    def setUp(self):
        self.now=datetime(2026,7,10,6,tzinfo=LOCAL)
        self.profile={'days':20,'hours':{h:{'samples':20,'pv_p25':0,'pv_p50':0,'pv_p75':0}
                                       for h in range(24)}}
        for h in range(9,17):
            self.profile['hours'][h].update(pv_p25=3000,pv_p50=3000,pv_p75=3000)

    def budget(self,**overrides):
        args=dict(profile=self.profile,now=self.now,sunset=self.now.replace(hour=18),
                  production_stop=self.now.replace(hour=16,minute=30),soc=80,pv=0,load=300,
                  running=False,capacity_wh=10000,miner_w=900,floor_soc=20,reserve_soc=90,
                  weather='solar_friendly')
        args.update(overrides)
        return plan(**args)

    def test_three_hour_bridge_is_deficit_times_hours_with_losses_only_until_cover(self):
        b=self.budget()
        self.assertEqual(b['cover_time'],self.now.replace(hour=9).isoformat())
        self.assertEqual(b['bridge_duration_minutes'],180)
        self.assertAlmostEqual(b['bridge_deficit_wh'],(900+300)*3/.9,places=1)
        self.assertAlmostEqual(b['required_bridge_wh'],4000*1.25,places=1)
        self.assertAlmostEqual(b['required_start_energy_wh'],(4000+120)*1.25,places=1)
        self.assertEqual(b['available_bridge_wh'],6000)
        self.assertTrue(b['safe'],b)

    def test_live_pv_is_subtracted_from_rig_plus_household_demand(self):
        for h in range(9):
            self.profile['hours'][h].update(pv_p25=600,pv_p50=600,pv_p75=600)
        # Unknown weather uses .8 of the reference: 600*.8 = 480 W.
        b=self.budget(pv=480,weather='unknown')
        self.assertEqual(b['bridge_duration_minutes'],180)
        self.assertAlmostEqual(b['bridge_deficit_wh'],(900+300-480)*3/.9,places=1)

    def test_bridge_ignores_evening_deficit_and_run_stop_choice(self):
        a=self.budget()
        b=self.budget(sunset=self.now.replace(hour=23))
        for key in ('bridge_deficit_wh','required_bridge_wh','required_start_energy_wh','cover_time'):
            self.assertEqual(a[key],b[key])
        self.assertNotEqual(a['end_soc'],b['end_soc'])

    def test_cover_now_means_zero_bridge_startup_is_separate(self):
        b=self.budget(now=self.now.replace(hour=10),pv=3000)
        self.assertEqual(b['bridge_status'],'covered_now')
        self.assertEqual(b['bridge_duration_minutes'],0)
        self.assertEqual(b['required_bridge_wh'],0)
        self.assertEqual(b['startup_energy_wh'],120)
        self.assertEqual(b['required_start_energy_wh'],150)

    def test_no_cover_is_unavailable_not_an_entire_days_deficit(self):
        for h in self.profile['hours'].values():
            h.update(pv_p25=0,pv_p50=0,pv_p75=0)
        b=self.budget(soc=40,load=2000,pv=500)
        self.assertFalse(b['safe'])
        self.assertEqual(b['bridge_status'],'no_sustained_cover')
        for key in ('required_bridge_wh','required_start_energy_wh','bridge_duration_minutes','bridge_deficit_wh'):
            self.assertIsNone(b[key])
        self.assertEqual(b['reason'],'no_sustained_solar_cover_for_morning_start')
        self.assertGreater(b['expected_load_wh'],20000)

    def test_startup_is_not_charged_to_household_only_refill(self):
        a=self.budget(now=self.now.replace(hour=10),pv=3000,startup_wh=0)
        b=self.budget(now=self.now.replace(hour=10),pv=3000,startup_wh=500)
        self.assertEqual(a['household_only_end_soc'],b['household_only_end_soc'])
        self.assertEqual(a['household_only_minimum_soc'],b['household_only_minimum_soc'])
        self.assertEqual(b['household_only_minimum_soc'],80)

    def test_bad_night_refill_can_reject_run_without_inflating_bridge(self):
        b=self.budget(now=self.now.replace(hour=10),pv=3000,load=1500,soc=40)
        self.assertFalse(b['safe'])
        self.assertEqual(b['required_bridge_wh'],0)
        self.assertEqual(b['reason'],'household_only_refill_not_feasible')
        self.assertLess(b['household_only_end_soc'],90)

    def test_cannot_start_if_startup_and_bridge_exceed_actual_energy_above_floor(self):
        b=self.budget(soc=30)
        self.assertFalse(b['safe'])
        self.assertEqual(b['reason'],'insufficient_battery_bridge')
        self.assertEqual(b['available_bridge_wh'],1000)
        self.assertGreater(b['required_start_energy_wh'],b['available_bridge_wh'])

    def test_few_clouds_is_close_to_clear_but_rain_forecast_still_wins(self):
        args=dict(now=self.now.replace(hour=10),soc=50,pv=3000)
        clear=self.budget(**args,current_condition='clear sky',clouds=18)
        few=self.budget(**args,current_condition='few clouds',clouds=18)
        rain=self.budget(**args,current_condition='few clouds',clouds=18,
            forecast=[{'ts':self.now.replace(hour=h).isoformat(),'condition':'rain','clouds':100} for h in (9,12,15,18)])
        self.assertEqual(clear['expected_pv_wh'],few['expected_pv_wh'])
        self.assertLess(rain['expected_pv_wh'],few['expected_pv_wh'])

    def test_house_load_is_included_and_running_miner_not_added_twice(self):
        off=self.budget(load=300)
        on=self.budget(load=1200,running=True)
        self.assertEqual(off['bridge_deficit_wh'],on['bridge_deficit_wh'])
        self.assertEqual(off['household_load_w'],on['household_load_w'])
        self.assertEqual(on['startup_energy_wh'],0)
        self.assertEqual(on['required_start_energy_wh'],on['required_bridge_wh'])

    def test_telegram_no_cover_cannot_claim_a_numeric_bridge(self):
        for h in self.profile['hours'].values():
            h.update(pv_p25=0,pv_p50=0,pv_p75=0)
        b=self.budget(load=2000)
        text=status({'historical_hints':{'energy_budget':b}},self.now)
        self.assertIn('Bridge: — szükséges',text)
        self.assertIn('a napi hiányt nem írjuk ide',text)
        self.assertIn('teljes indulási keret',text)


class RealOctoberBridgeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.dataset=solar.build_historical_profile('solarman_json')

    def recommend(self,h,m,soc,pv,load):
        now=datetime(2026,10,17,h,m,tzinfo=LOCAL)
        with patch.object(solar,'historical_profile',self.dataset), \
             patch.object(solar,'_weather_daylight',(now.replace(hour=7,minute=1),now.replace(hour=17,minute=59))):
            return solar._history_recommendation(now,soc,pv,now.replace(hour=7,minute=1),
                now.replace(hour=16,minute=29),{'summary_5d':'mixed'},load,False,53.08,200,'few clouds',18)['energy_budget']

    def test_reported_0921_sample_with_few_clouds_can_run_and_refill(self):
        b=self.recommend(9,21,41,2364,557)
        self.assertTrue(b['safe'],b)
        self.assertEqual(b['required_bridge_wh'],0)
        self.assertEqual(b['required_start_energy_wh'],150)
        self.assertEqual(b['available_bridge_wh'],2229.4)
        self.assertGreater(b['minimum_soc'],20)
        self.assertGreaterEqual(b['end_soc'],90)

    def test_reported_0916_large_house_load_is_not_a_13kwh_bridge(self):
        b=self.recommend(9,16,40,2303,2061)
        self.assertFalse(b['safe'],b)  # This real household demand cannot be ignored.
        self.assertNotEqual(b['reason'],'battery_floor_would_be_crossed')
        if b['required_bridge_wh'] is not None:
            self.assertLess(b['required_bridge_wh'],3000)
        self.assertEqual(b['available_bridge_wh'],2123.2)

    def test_40_percent_can_start_before_cover_and_preserve_the_20_percent_floor(self):
        b=self.recommend(8,0,40,400,300)
        self.assertTrue(b['safe'],b)
        self.assertGreater(b['bridge_duration_minutes'],0)
        self.assertLess(b['required_start_energy_wh'],b['available_bridge_wh'])
        self.assertGreater(b['minimum_soc'],20)
        self.assertGreaterEqual(b['end_soc'],90)

    def test_running_rig_uses_battery_through_a_cloud_without_a_new_start_charge(self):
        now=datetime(2026,10,17,9,21,tzinfo=LOCAL)
        with patch.object(solar,'historical_profile',self.dataset), \
             patch.object(solar,'_weather_daylight',(now.replace(hour=7,minute=1),now.replace(hour=17,minute=59))):
            b=solar._history_recommendation(now,41,0,now.replace(hour=7,minute=1),
                now.replace(hour=16,minute=29),{'summary_5d':'mixed'},1350,True,53.08,200,'few clouds',18)['energy_budget']
        self.assertTrue(b['safe'],b)
        self.assertEqual(b['startup_energy_wh'],0)
        self.assertGreater(b['minimum_soc'],20)

    def test_historical_soc_discharge_is_advice_not_an_extra_physical_wh_charge(self):
        profile=copy.deepcopy(self.dataset['weeks'][42])
        now=datetime(2026,10,17,8,tzinfo=LOCAL)
        common=dict(now=now,sunset=now.replace(hour=18),soc=80,pv=400,load=300,running=False,
                    capacity_wh=10616,miner_w=1050,reserve_soc=90,weather='mixed')
        a=plan(profile,**common)
        for point in profile['curve']:
            point['soc_pct']=100 if point['minute']<=480 else 0
        b=plan(profile,**common)
        self.assertEqual(a['bridge_deficit_wh'],b['bridge_deficit_wh'])
        self.assertEqual(a['required_bridge_wh'],b['required_bridge_wh'])
        self.assertEqual(a['safe'],b['safe'])
        self.assertGreater(b['historical_bridge_wh'],a['historical_bridge_wh'])


if __name__=='__main__':
    unittest.main()
