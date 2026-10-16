import copy
from datetime import datetime, timedelta
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from history_model import LOCAL, load_exports, plan, seasonal_profile
from simulate_decisions import solar


class HistoryModelTests(unittest.TestCase):
    def setUp(self):
        self.now = datetime(2026, 6, 10, 10, tzinfo=LOCAL)
        self.sunset = self.now.replace(hour=18)
        self.profile = {'days': 30, 'hours': {h: {'pv_p25': 3000, 'load_p75': 500,
                        'samples': 30} for h in range(24)}}

    def budget(self, **kw):
        args = dict(profile=self.profile, now=self.now, sunset=self.sunset, soc=80,
                    pv=3000, load=300, running=False, capacity_wh=10000,
                    miner_w=900, weather='solar_friendly')
        args.update(kw)
        return plan(**args)

    def test_good_solar_can_start_but_household_demand_can_prevent_it(self):
        self.assertTrue(self.budget()['safe'])
        self.assertFalse(self.budget(load=3500)['safe'])

    def test_weather_and_current_solar_only_reduce_forecast(self):
        self.assertLess(self.budget(weather='solar_weak')['expected_pv_wh'], self.budget()['expected_pv_wh'])
        self.assertFalse(self.budget(pv=0)['safe'])
        self.assertEqual(self.budget(pv=9000)['expected_pv_wh'], self.budget()['expected_pv_wh'])

    def test_curtailed_midday_energy_cannot_cover_late_deficit(self):
        for h in range(14, 24):
            self.profile['hours'][h]['pv_p25'] = 0
        result = self.budget(soc=100)
        self.assertFalse(result['safe'])
        self.assertGreater(result['reserve_shortfall_wh'], 0)

    def test_missing_hours_history_or_invalid_measurements_fail_closed(self):
        self.profile['hours'].pop(12)
        self.assertFalse(self.budget()['safe'])
        self.assertFalse(self.budget(profile={})['safe'])
        for field in ('soc', 'pv', 'load', 'capacity_wh', 'miner_w'):
            self.assertFalse(self.budget(**{field: float('nan')})['safe'])
        self.assertFalse(self.budget(sunset=self.now)['safe'])

    def test_soc_floor_startup_cost_and_output_bounds(self):
        self.assertFalse(self.budget(soc=20)['safe'])
        self.assertTrue(self.budget(soc=20, running=True)['safe'])
        result = self.budget(load=10000)
        self.assertEqual(result['end_soc'], 0)
        self.assertEqual(result['minimum_soc'], 0)

    def test_aggregate_historical_load_is_not_charged_for_rig_twice(self):
        for hour in self.profile['hours'].values():
            hour['load_p75'] = 1500
        self.assertEqual(self.budget()['expected_load_wh'], 8*1500)

    def test_loader_timezone_duplicate_median_validation_cutoff_and_no_writes(self):
        row = {'Updated Time': '2026/06/10 08:00', 'Time Zone': 'UTC+00:00',
               'Production Power(W)': 2000, 'Consumption Power(W)': 500, 'SoC(%)': 80}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'export.json'
            rows = [row, dict(row, **{'Production Power(W)': 4000}),
                    dict(row, **{'SoC(%)': 'nan'}),
                    dict(row, **{'Updated Time': '2026/06/11 08:00'})]
            path.write_text(json.dumps(rows))
            original = path.read_bytes()
            result = load_exports(directory, before=self.now+timedelta(hours=1))
            self.assertEqual(result['invalid_rows'], 1)
            self.assertEqual(result['duplicate_timestamps'], 1)
            self.assertEqual(len(result['rows']), 1)
            self.assertEqual(result['rows'][0]['ts'], self.now.isoformat())
            self.assertEqual(result['rows'][0]['power'], 3000)
            self.assertEqual(path.read_bytes(), original)
            self.assertEqual(list(Path(directory).iterdir()), [path])

    def test_missing_season_is_not_filled_with_opposite_season(self):
        rows = [{'ts':self.now.isoformat(), 'power':3000, 'consumption':500}]
        self.assertEqual(seasonal_profile(rows, 12), {})
        self.assertTrue(seasonal_profile(rows, 7)['interpolated'])
        self.assertLess(self.budget(profile=dict(self.profile, interpolated=True))['expected_pv_wh'],
                        self.budget()['expected_pv_wh'])

    def test_dashboard_uses_exports_without_accumulating_live_readings(self):
        rows = [{'ts': self.now.isoformat(), 'power':100, 'consumption':500, 'battery':80}]
        before = copy.deepcopy(rows)
        with patch.object(solar, 'historical_profile', {'rows': rows}), patch.dict(solar._shared_snapshot, {'power':9999}):
            payload = solar._build_snapshot_payload()
            self.assertEqual(payload['power'], 9999)
            self.assertEqual(payload['history'], rows)
            self.assertEqual(payload['history_source'], 'solarman_json')
        self.assertEqual(rows, before)
        self.assertFalse(hasattr(solar, 'telemetry_history'))

    def test_decision_preserves_phase_limit_and_stops_without_history(self):
        def decide(profile, l2=0, running=False):
            with patch.object(solar, 'historical_profile', {'months':{6:profile}}):
                return solar._make_miner_decision(self.now, 'production' if running else 'stop',
                    95, 4000, 0, l2, 0, 300, 'clear sky', 0, 'clear sky', 0,
                    'clear sky', 0, self.now.replace(hour=7), self.sunset, {}, {},
                    50, 200, {'summary_5d':'solar_friendly'})
        self.assertEqual(decide(self.profile)['desired_state'], 'production')
        self.assertTrue(decide(self.profile, l2=3000)['hard_stop'])
        self.assertEqual(decide({}, running=True)['desired_state'], 'stop')
        self.assertTrue(decide({}, running=True)['hard_stop'])


    def test_live_controller_uses_measured_load_and_rejects_stale_data(self):
        now = self.now
        class FrozenDateTime(datetime):
            @classmethod
            def now(cls, tz=None):
                return now
        now = FrozenDateTime.fromisoformat(now.isoformat())
        weather = ('clear sky', now.replace(hour=7), now.replace(hour=18), 0,
                   'clear sky', 0, '', 'clear sky', 0, '', {'summary_5d':'solar_friendly'})
        fields = {'BMS_SOC':95, 'S_P_T':4000, 'INV_O_P_L1':100,
                  'INV_O_P_L2':100, 'INV_O_P_L3':100, 'INV_O_P_T':300, 'LOAD_P_T':300}
        data = {'collectionTime':now.timestamp(), 'dataList':[
            {'key':key,'value':value} for key,value in fields.items()]}
        with patch.object(solar,'datetime',FrozenDateTime), \
             patch.object(solar,'historical_profile',{'months':{6:self.profile}}), \
             patch.object(solar,'load_prev_state',return_value=('stop',now-timedelta(hours=1))), \
             patch.object(solar,'get_current_weather',return_value=weather), \
             patch.object(solar,'read_dht11',return_value={'temperature':20,'humidity':40}), \
             patch.object(solar,'is_rpi',False), patch.object(solar,'save_prev_state'), \
             patch.object(solar,'send_telegram_message'), patch.object(solar,'state','stop'), \
             patch.object(solar,'prev_state','stop'), patch.object(solar,'uptime',None), \
             patch.object(solar,'_last_production_start_at',None):
            result = solar.check_crypto_production_conditions(data,'','','')
            self.assertEqual(result[2],'production')
            data['dataList'] = [i for i in data['dataList'] if i['key'] != 'LOAD_P_T']
            result = solar.check_crypto_production_conditions(data,'','','')
            self.assertEqual(result[2],'production')
            data['collectionTime'] = (now-timedelta(minutes=10)).timestamp()
            result = solar.check_crypto_production_conditions(data,'','','')
            self.assertEqual(result[2],'stop')
            self.assertFalse(result[-1]['energy_budget']['safe'])


if __name__ == '__main__':
    unittest.main()
