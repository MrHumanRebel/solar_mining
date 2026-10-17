"""Zero-export, near-full battery regression and actual Solarman upload cadence."""
from datetime import datetime, timedelta
import unittest
from unittest.mock import patch
from solar_mining.history_model import LOCAL, plan
from tools.simulate_decisions import solar
from solar_mining.power_measurement import PowerSample
from tests.power_test_helpers import sample
from solar_mining.status_messages import status


class NearFullBufferTests(unittest.TestCase):
    def setUp(self):
        self.now=datetime(2026,10,17,13,31,tzinfo=LOCAL)
        self.profile={'days':12,'hours':{h:{'samples':12,'pv_p25':0,'pv_p50':0,'pv_p75':0} for h in range(24)}}

    def budget(self,**kw):
        args=dict(profile=self.profile,now=self.now,sunset=self.now.replace(hour=18),
                  production_stop=self.now.replace(hour=16,minute=29),soc=99,pv=956,load=960,
                  running=False,capacity_wh=10672,miner_w=750,floor_soc=20,reserve_soc=90,
                  current_condition='clear sky',clouds=4,weather='solar_weak')
        args.update(kw)
        return plan(**args)

    def test_near_full_zero_export_can_start_without_imaginary_extra_pv(self):
        b=self.budget()
        self.assertTrue(b['safe'],b)
        self.assertEqual(b['projection_mode'],'surplus_buffer_run')
        self.assertEqual(b['reason'],'bounded_solar_surplus_run')
        self.assertTrue(b['pv_curtailed_possible'])
        self.assertGreaterEqual(b['worst_case_stop_soc'],90)
        self.assertGreaterEqual(b['run_minimum_soc'],90)
        self.assertLessEqual(b['required_surplus_wh'],b['available_surplus_wh'])
        self.assertFalse(b['sunset_reserve_met'])  # Never claim a guaranteed 90% sunset.
        self.assertLess(b['end_soc'],90)
        until=datetime.fromisoformat(b['planned_stop'])
        self.assertGreaterEqual(until-self.now,timedelta(minutes=18))
        self.assertLessEqual(until-self.now,timedelta(minutes=30))
        duration=(until-self.now).total_seconds()/3600
        self.assertAlmostEqual(b['required_surplus_wh'],(120+(960+750)*duration/.9)*1.25,places=1)
        self.assertLessEqual(b['expected_pv_wh'],956)  # Measured PV fades; no invented watts.

    def test_running_mode_counts_rig_once_and_has_no_second_startup_cost(self):
        b=self.budget(load=1000,running=True,min_run_minutes=5)
        self.assertTrue(b['safe'],b)
        self.assertEqual(b['household_load_w'],250)
        self.assertEqual(b['startup_energy_wh'],0)
        until=datetime.fromisoformat(b['planned_stop'])
        self.assertAlmostEqual(b['required_surplus_wh'],1000*(until-self.now).total_seconds()/3600/.9*1.25,places=1)

    def test_start_continue_hysteresis_does_not_restart_near_reserve(self):
        self.assertFalse(self.budget(soc=94)['safe'])
        self.assertTrue(self.budget(soc=94,load=1000,running=True,min_run_minutes=5)['safe'])
        for soc in (89,90,90.2):
            self.assertFalse(self.budget(soc=soc,load=1000,running=True,min_run_minutes=5)['safe'])

    def test_small_battery_or_large_household_load_cannot_borrow_the_reserve(self):
        self.assertFalse(self.budget(capacity_wh=1000)['safe'])
        self.assertFalse(self.budget(load=3500)['safe'])

    def test_rain_inside_run_blocks_it_but_later_rain_does_not(self):
        rainy=lambda minute:dict(ts=(self.now+timedelta(minutes=minute)).isoformat(),condition='heavy rain',clouds=100)
        self.assertFalse(self.budget(forecast=[rainy(5)])['safe'])
        self.assertTrue(self.budget(forecast=[rainy(90)])['safe'])

    def test_sunlight_and_adequate_time_are_required_for_new_surplus_start(self):
        self.assertFalse(self.budget(current_condition='heavy rain',clouds=100)['safe'])
        self.assertFalse(self.budget(current_condition='unknown',clouds=None)['safe'])
        self.assertTrue(self.budget(pv=0)['safe'])  # Zero-export PV can be fully curtailed.
        self.assertFalse(self.budget(production_stop=self.now+timedelta(minutes=10))['safe'])
        self.assertFalse(self.budget(now=self.now.replace(hour=11))['safe'])

    def test_invalid_live_measurements_do_not_gain_a_surplus_bypass(self):
        for key in ('load','soc','pv','capacity_wh','bridge_safety_factor','min_run_minutes','reserve_soc'):
            self.assertFalse(self.budget(**{key:float('nan')})['safe'])

    def test_exact_minimum_stop_does_not_charge_a_whole_five_minute_bucket(self):
        b=self.budget(load=1005,pv=983)
        self.assertTrue(b['safe'],b)
        # The 20-minute window cannot fit zero-PV+startup margin; exactly 18 can.
        self.assertEqual(datetime.fromisoformat(b['planned_stop'])-self.now,timedelta(minutes=18))
        self.assertAlmostEqual(b['expected_load_wh'],1005*5+750*.3,places=1)

    def test_telegram_separates_run_reserve_from_unreliable_sunset_forecast(self):
        b=self.budget()
        text=status({'historical_hints':{'energy_budget':b}},self.now)
        self.assertIn('Nincs visszatáplálás',text)
        self.assertIn('Nulla PV-vel számolt',text)
        self.assertIn('nem garantált tartalék',text)
        self.assertLess(len(text),4096)


class CadenceTests(unittest.TestCase):
    def test_six_minute_upload_plus_request_jitter_is_fresh_consistently(self):
        s=sample(0)
        now=s.at+timedelta(seconds=360.9)
        self.assertTrue(PowerSample.fresh(s,now))
        self.assertIsNone(solar._power_measurement_reason({},s,now))
        for age in (420.1,600):
            now=s.at+timedelta(seconds=age)
            self.assertFalse(PowerSample.fresh(s,now))
            self.assertIn('maximum 420',solar._power_measurement_reason({},s,now))
        self.assertFalse(PowerSample.fresh(s,s.at-timedelta(seconds=1)))




class ReportedNearFullTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data=solar.build_historical_profile('solarman_json')

    def test_both_reported_midday_readings_allow_a_bounded_run(self):
        for minute,pv,load in ((26,983,1000),(31,956,960)):
            now=datetime(2026,10,17,13,minute,tzinfo=LOCAL)
            outlook={'summary_5d':'solar_weak','forecast':[{'ts':now.replace(hour=15).isoformat(),'condition':'heavy rain','clouds':100}]}
            with patch.object(solar,'historical_profile',self.data), \
                 patch.object(solar,'_weather_daylight',(now.replace(hour=7),now.replace(hour=17,minute=59))):
                decision=solar._make_miner_decision(now,'stop',99,pv,7,614,363,984,
                    'clear sky',4,'clear sky',4,'rain',100,now.replace(hour=7),now.replace(hour=16,minute=29),
                    {},{},53.36,200,outlook,current_load=load)
            self.assertEqual(decision['desired_state'],'production',decision)
            b=decision['history_hints']['energy_budget']
            self.assertGreaterEqual(b['worst_case_stop_soc'],90)
            self.assertIn('bounded run',decision['decision_summary'])
            self.assertNotIn('overnight household reserve covered',decision['decision_summary'])


if __name__=='__main__':
    unittest.main()
