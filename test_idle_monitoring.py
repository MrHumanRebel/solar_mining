from concurrent.futures import Future
from contextlib import redirect_stdout
from datetime import datetime, timedelta, timezone
import io
import unittest
from unittest.mock import Mock, patch

import simulate_decisions
from power_measurement import PowerSample
from miner_ping_guard import MinerPingGuard

solar = simulate_decisions.solar
SUNSET = datetime(2026, 10, 16, 18, tzinfo=timezone.utc)


class IdleMonitoringTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(patch.object(solar,'save_prev_state'))
        self.enterContext(patch.object(solar,'send_telegram_message_async'))

    def test_missing_and_invalid_display_values_are_unknown(self):
        for value in (None, '', '--', 'error', float('nan'), float('inf'), True):
            self.assertIsNone(solar.clean_value(value))
        self.assertEqual(solar.clean_value('-3.5 C'), -3)
        self.assertEqual(solar.clean_value('42%'), 42)
        self.assertEqual(solar.clean_value(0), 0)

    def test_oled_renders_missing_sensor_values_and_real_zero_distinctly(self):
        oled = Mock(width=128, height=32)
        draw = Mock()
        with patch.object(solar, 'oled', oled), patch.object(solar, 'draw', draw):
            self.assertTrue(solar.write_to_display('monitor', 0, 0, None, None))
        lines = [call.args[1] for call in draw.text.call_args_list]
        self.assertEqual(lines, ['SOC: 0% PWR: 0W','monitor','--C --%'])

    def test_oled_errors_never_escape_into_monitoring(self):
        for error in (ValueError('invalid OLED frame'), OSError('I2C unavailable')):
            oled = Mock(width=128, height=32)
            oled.show.side_effect = error
            with patch.object(solar, 'oled', oled), patch.object(solar, 'draw', Mock()), \
                 redirect_stdout(io.StringIO()):
                self.assertFalse(solar.write_to_display('monitor', None, None, None, None))

    def test_live_reads_continue_through_30_minutes_and_all_night_despite_oled_errors(self):
        data = {'collectionTime':SUNSET.timestamp(),'dataList':[
            {'key':'S_P_T','value':37}, {'key':'BMS_SOC','value':92},
            {'key':'INV_O_P_L1','value':10}, {'key':'INV_O_P_L2','value':100},
            {'key':'INV_O_P_L3','value':150}, {'key':'INV_O_P_T','value':260},
        ]}
        oled = Mock(width=128, height=32)
        oled.show.side_effect = ValueError('broken display')
        future = Future()
        future.set_result('test-token')
        minutes = [0,5,10,15,20,25,30,35,90,360]
        with patch.object(solar, 'fetch_current_data', return_value=data) as fetch, \
             patch.object(solar, 'record_live_power') as guard, \
             patch.object(solar, 'save_quote_usage'), patch.object(solar, 'used_quote', 0), \
             patch.object(solar, 'is_rpi', True), patch.object(solar, 'oled', oled), \
             patch.object(solar, 'draw', Mock()), patch.dict(solar._shared_snapshot), \
             redirect_stdout(io.StringIO()):
            for minute in minutes:
                now = SUNSET + timedelta(minutes=minute)
                data['collectionTime'] = now.timestamp()
                self.assertEqual(solar._idle_monitor_cycle(now, future, None, None), data)
                self.assertEqual(guard.call_args.args, (now, 'stop', data))
                self.assertEqual(solar._shared_snapshot['power'], 37)
                self.assertEqual(solar._shared_snapshot['inv_lt'], 260)
                self.assertEqual(solar._shared_snapshot['state'], 'stop')
            self.assertEqual(fetch.call_count, len(minutes))
            self.assertEqual(guard.call_count, len(minutes))
            self.assertEqual(oled.show.call_count, len(minutes))
            self.assertEqual(solar.used_quote, len(minutes))

    def test_unavailable_api_does_not_reuse_last_payload_as_live_measurement(self):
        future = Future()
        future.set_result('test-token')
        with patch.object(solar, 'fetch_current_data', side_effect=OSError('offline')), \
             patch.object(solar, 'save_quote_usage'), patch.object(solar, 'used_quote',0), \
             patch.object(solar, 'record_live_power') as guard, \
             patch.object(solar, 'is_rpi', False), patch.dict(solar._shared_snapshot), \
             redirect_stdout(io.StringIO()):
            solar._idle_monitor_cycle(SUNSET, future, None, None)
            guard.assert_called_once_with(SUNSET,'stop',{},poll_interval_seconds=300)
            self.assertIsNone(solar._shared_snapshot['power'])

    def test_missing_or_malformed_measurements_do_not_crash_idle_monitoring(self):
        future = Future()
        future.set_result('test-token')
        for payload in ({}, {'dataList':None}, {'dataList':[None,'invalid']}, {'dataList':3}):
            with self.subTest(payload=payload), \
                 patch.object(solar,'fetch_current_data',return_value=payload), \
                 patch.object(solar,'save_quote_usage'),patch.object(solar,'used_quote',0), \
                 patch.object(solar,'_runtime_guard',MinerPingGuard()), \
                 patch.object(solar,'is_rpi',False),patch.dict(solar._shared_snapshot), \
                 redirect_stdout(io.StringIO()):
                solar._idle_monitor_cycle(SUNSET,future,None,None)
                self.assertIsNone(solar._shared_snapshot['power'])


    def test_full_idle_loop_survives_more_than_12_missing_dht_samples(self):
        weather = ('clear sky', SUNSET-timedelta(hours=10), SUNSET, 0,
                   'clear',0,'','clear',0,'',{})
        def submit(fn, *args):
            result = Future()
            result.set_result(fn(*args))
            return result
        executor = Mock(submit=Mock(side_effect=submit))
        oled = Mock(width=128, height=32)
        oled.show.side_effect = OSError('OLED offline')
        slots = [(1800, i // 6) for i in range(13)]
        with patch.multiple(solar, historical_profile={}, state='stop', prev_state='stop',
                            last_quote_reset_date=SUNSET.date(), _solarman_poll_slot=Mock(side_effect=slots),
                            _solarman_poll_due=Mock(side_effect=[i%6==0 for i in range(13)])), \
             patch.object(solar, 'load_quote_usage',return_value=0), \
             patch.object(solar, 'save_quote_usage'), \
             patch.object(solar, 'get_current_weather',return_value=weather), \
             patch.object(solar, 'read_dht11',return_value={'temperature':None,'humidity':None}), \
             patch.object(solar, 'get_access_token',return_value='test-token') as auth, \
             patch.object(solar, 'fetch_current_data',return_value={'dataList':[]}) as fetch, \
             patch.object(solar.threading,'Thread'), \
             patch.object(solar,'ThreadPoolExecutor',return_value=executor), \
             patch.object(solar,'_control_window_details',return_value={'active':False}), \
             patch.object(solar,'_wallet_hashrate_hs_cached',return_value=200e12), \
             patch.object(solar,'record_live_power') as guard, \
             patch.object(solar,'sleep_until_next_5min',side_effect=[None]*12+[StopIteration]), \
             patch.object(solar,'is_rpi',True), patch.object(solar,'oled',oled), \
             patch.object(solar,'draw',Mock()), patch.dict(solar._shared_snapshot), \
             redirect_stdout(io.StringIO()):
            with self.assertRaises(StopIteration):
                solar.main_loop()
            self.assertEqual(fetch.call_count,3)
            self.assertEqual(auth.call_count,3)
            self.assertEqual(guard.call_count,3)
            self.assertEqual(solar._shared_snapshot['hashrate_hs'],200e12)


if __name__ == '__main__':
    unittest.main()
