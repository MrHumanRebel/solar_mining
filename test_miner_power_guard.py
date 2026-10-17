from datetime import datetime, timedelta, timezone
import unittest
from unittest.mock import Mock, patch
from concurrent.futures import Future
import json
from pathlib import Path

from miner_power_guard import MinerPowerGuard, PowerSample
import simulate_decisions

solar = simulate_decisions.solar
T = datetime(2026, 10, 16, 10, tzinfo=timezone.utc)


def sample(minute, total=1200, l1=100, l2=550, l3=550):
    return PowerSample(T + timedelta(minutes=minute), total, l1, l2, l3)


def armed_guard(swap=False):
    guard = MinerPowerGuard()
    for minute in (0, 5, 10):
        off = sample(minute, 400, 100, 100, 200)
        guard.observe(off, off.at, 'stop')
    guard.command_start(off, off.at + timedelta(seconds=1))
    for minute in (15, 20):
        run = sample(minute, 1200, 100, 450 if swap else 550, 650 if swap else 550)
        guard.observe(run, run.at, 'production')
    assert guard.signature is not None
    return guard


class PowerGuardTests(unittest.TestCase):
    def test_oc_rig_720w_paired_rise_is_identified_in_both_phase_assignments(self):
        for swap in (False,True):
            with self.subTest(swap=swap):
                guard=MinerPowerGuard()
                for minute in (0,5,10):
                    off=sample(minute,400,100,100,200)
                    guard.observe(off,off.at,'stop')
                guard.command_start(off,off.at+timedelta(seconds=1))
                l2,l3=(350,370) if swap else (370,350)
                for minute in (15,20):
                    run=sample(minute,1120,100,100+l2,200+l3)
                    self.assertFalse(guard.observe(run,run.at,'production'))
                self.assertEqual(guard.signature,(l2,l3))
                stop=sample(25,1120,100,100+l2,200+l3)
                self.assertTrue(guard.observe(stop,stop.at,'stop'))
                self.assertFalse(guard.observe(stop,stop.at,'stop'))

    def test_oc_rig_does_not_lower_existing_1000w_shutdown_threshold(self):
        guard=MinerPowerGuard()
        for minute in (0,5,10):
            off=sample(minute,200,20,80,100)
            guard.observe(off,off.at,'stop')
        guard.command_start(off,off.at+timedelta(seconds=1))
        for minute in (15,20):
            run=sample(minute,920,20,450,450)
            guard.observe(run,run.at,'production')
        self.assertIsNotNone(guard.signature)
        stop=sample(25,920,20,450,450)
        self.assertFalse(guard.observe(stop,stop.at,'stop'))

    def test_known_stopped_rig_load_never_arms_without_observed_start(self):
        rows=json.loads((Path(__file__).parent/'tests/fixtures/stopped_rig_oct16.json').read_text())
        guard=MinerPowerGuard()
        for row in rows:
            at=datetime.fromisoformat(row['ts'])
            self.assertFalse(guard.observe(PowerSample(at,row['inv_lt'],row['inv_l1'],row['inv_l2'],row['inv_l3']),at,'stop'))

    def test_first_fresh_matching_stop_sample_triggers_once(self):
        guard = armed_guard()
        for minute, expected in [(25, True), (30, False), (35, False), (40, False), (45, False)]:
            s = sample(minute)
            self.assertEqual(guard.observe(s, s.at, 'stop'), expected)

    def test_either_phase_assignment_is_supported(self):
        guard = armed_guard(swap=True)
        results = []
        for minute in (25, 30, 35):
            s = sample(minute, l2=450, l3=650)
            results.append(guard.observe(s, s.at, 'stop'))
        self.assertEqual(results, [True, False, False])

    def test_oven_only_and_unknown_start_never_arm(self):
        guard = MinerPowerGuard()
        for minute in range(0, 60, 5):
            s = sample(minute, total=2800, l2=2500, l3=200)
            self.assertFalse(guard.observe(s, s.at, 'stop'))
        self.assertIsNone(guard.signature)

    def test_oven_step_after_start_is_not_learned(self):
        guard = MinerPowerGuard()
        for minute in (0, 5, 10):
            s = sample(minute, 400, 100, 100, 200)
            guard.observe(s, s.at, 'stop')
        guard.command_start(s, s.at + timedelta(seconds=1))
        for minute in (15, 20, 25):
            s = sample(minute, 3000, 100, 2700, 200)
            self.assertFalse(guard.observe(s, s.at, 'production'))
        self.assertIsNone(guard.signature)

    def test_unstable_household_baseline_does_not_arm(self):
        guard = MinerPowerGuard()
        for minute in (0, 5, 10):
            s = sample(minute, l2=100+minute*100)
            guard.observe(s, s.at, 'stop')
        guard.command_start(s, s.at)
        self.assertIsNone(guard.started)

    def test_total_threshold_is_strict(self):
        guard = armed_guard()
        for minute in (25, 30, 35):
            s = sample(minute, total=1000)
            self.assertFalse(guard.observe(s, s.at, 'stop'))

    def test_cooking_on_each_phase_and_hob_are_ambiguous(self):
        for loads in [(2200,550,550), (100,2500,550), (100,550,2500), (100,1400,1600)]:
            guard = armed_guard()
            for minute in (25, 30, 35):
                s = sample(minute, total=sum(loads), l1=loads[0], l2=loads[1], l3=loads[2])
                self.assertFalse(guard.observe(s, s.at, 'stop'))

    def test_stopped_rig_cannot_be_rearmed_by_later_similar_cooking_load(self):
        guard = armed_guard()
        off = sample(25, 400, 100, 100, 200)
        self.assertFalse(guard.observe(off, off.at, 'stop'))
        for minute in (30, 35, 40, 45):
            s = sample(minute)
            self.assertFalse(guard.observe(s, s.at, 'stop'))

    def test_loss_of_one_mining_phase_disarms(self):
        guard = armed_guard()
        s = sample(25, l2=100)
        guard.observe(s, s.at, 'stop')
        self.assertIsNone(guard.signature)

    def test_missing_stale_future_and_repeated_samples_do_not_confirm(self):
        guard = armed_guard()
        s = sample(25)
        self.assertTrue(guard.observe(s, s.at, 'stop'))
        for _ in range(10):
            self.assertFalse(guard.observe(s, s.at, 'stop'))
        self.assertFalse(guard.observe(None, s.at, 'stop'))
        self.assertFalse(guard.observe(s, s.at + timedelta(minutes=10), 'stop'))
        future = sample(40)
        self.assertFalse(guard.observe(future, s.at, 'stop'))

    def test_armed_guard_rejects_repeated_stale_and_future_first_stop_readings(self):
        for at_minute, now_minute in ((20,25),(25,35),(40,25)):
            with self.subTest(at=at_minute,now=now_minute):
                guard = armed_guard()
                self.assertFalse(guard.observe(sample(at_minute),T+timedelta(minutes=now_minute),'stop'))
                self.assertIsNotNone(guard.signature)

    def test_gap_loses_identity_instead_of_reusing_old_running_measurement(self):
        guard = armed_guard()
        for minute in (35, 40, 45):
            s = sample(minute)
            self.assertFalse(guard.observe(s, s.at, 'stop'))

    def test_production_state_never_forces_stop(self):
        guard = armed_guard()
        for minute in (25, 30, 35):
            s = sample(minute)
            self.assertFalse(guard.observe(s, s.at, 'production'))

    def test_displayed_hashrate_never_authorizes_button(self):
        with patch.object(solar, '_power_guard', MinerPowerGuard()), \
             patch.object(solar, '_wallet_hashrate_hs_cached', side_effect=AssertionError('pool queried by guard')), \
             patch.object(solar, 'press_power_button') as press:
            solar.supervise_runtime_by_power(T, 'stop', {})
            press.assert_not_called()

    def test_gpio_is_pressed_once_for_confirmed_power_and_never_queries_pool(self):
        guard = armed_guard()
        with patch.object(solar, '_power_guard', guard), \
             patch.object(solar, '_extract_power_sample') as extract, \
             patch.object(solar, '_wallet_hashrate_hs_cached', side_effect=AssertionError('pool used')), \
             patch.object(solar, 'is_rpi', True), patch.object(solar, 'GPIO_AVAILABLE', True), \
             patch.object(solar, '_last_force_shutdown_at'), \
             patch.object(solar, 'save_prev_state'), patch.object(solar, 'send_telegram_message'), \
             patch.object(solar, 'press_power_button', return_value=True) as press:
            for minute in (25,30,35,40):
                s = sample(minute)
                extract.return_value = s
                solar.supervise_runtime_by_power(s.at, 'stop', {})
            press.assert_called_once_with(16, solar.POWER_BUTTON_LONG_PRESS_SECONDS)

    def test_timestamp_and_explicit_consumption_required(self):
        data = {'collectionTime': T.timestamp(), 'dataList': [
            {'key': 'LOAD_P_T', 'value': 1200},
            *[{'key': f'INV_O_P_L{i}', 'value': v} for i,v in [(1,100),(2,550),(3,550)]]
        ]}
        self.assertEqual(solar._extract_power_sample(data,T).total, 1200)
        del data['collectionTime']
        self.assertIsNone(solar._extract_power_sample(data,T))
        data['collectionTime'] = T.timestamp()
        data['dataList'] = data['dataList'][1:]
        self.assertIsNone(solar._extract_power_sample(data,T))

    def test_idle_pool_refresh_is_display_only(self):
        with patch.object(solar, '_wallet_hashrate_hs_cached', return_value=200e12), \
             patch.dict(solar._shared_snapshot), patch.object(solar, 'press_power_button') as press:
            solar._update_pool_hashrate(T)
            self.assertEqual(solar._build_snapshot_payload()['hashrate_text'], '200.00 TH/s')
            press.assert_not_called()

    def test_main_loop_refreshes_pool_and_live_power_while_idle(self):
        weather = ('clear sky', T, T + timedelta(hours=8), 0,
                   'clear', 0, '', 'clear', 0, '', {})
        def submit(fn, *args):
            future = Future()
            future.set_result(fn(*args))
            return future
        executor = Mock(submit=Mock(side_effect=submit))
        with patch.multiple(solar, historical_profile={}, state='stop', prev_state='stop',
                            last_quote_reset_date=T.date()), \
             patch.object(solar, 'load_quote_usage', return_value=0), \
             patch.object(solar, 'save_quote_usage'), \
             patch.object(solar, 'get_current_weather', return_value=weather), \
             patch.object(solar, 'read_dht11', return_value={'temperature':20, 'humidity':40}), \
             patch.object(solar, 'get_access_token', return_value='test-token'), \
             patch.object(solar, 'fetch_current_data', return_value={'dataList': []}) as fetch, \
             patch.object(solar.threading, 'Thread'), \
             patch.object(solar, 'ThreadPoolExecutor', return_value=executor), \
             patch.object(solar, '_control_window_details', return_value={'active':False}), \
             patch.object(solar, '_wallet_hashrate_hs_cached', return_value=200e12), \
             patch.object(solar, 'supervise_runtime_by_power') as power_guard, \
             patch.object(solar, 'sleep_until_next_5min', side_effect=StopIteration), \
             patch.object(solar, 'is_rpi', False), patch.dict(solar._shared_snapshot):
            with self.assertRaises(StopIteration):
                solar.main_loop()
            self.assertEqual(solar._shared_snapshot['hashrate_hs'], 200e12)
            self.assertEqual(solar._build_snapshot_payload()['hashrate_text'], '200.00 TH/s')
            fetch.assert_called_once_with('test-token')
            self.assertEqual(power_guard.call_args.args[1:], ('stop', {'dataList': []}))

    def test_real_gpio_start_registers_baseline_and_stop_disarms(self):
        gpio = Mock()
        guard = Mock()
        with patch.object(solar, 'is_rpi', True), patch.object(solar, 'GPIO_AVAILABLE', True), \
             patch.object(solar, 'GPIO', gpio, create=True), patch.object(solar.time, 'sleep'), \
             patch.object(solar, '_power_guard', guard):
            solar.press_power_button(16, solar.POWER_BUTTON_SHORT_PRESS_SECONDS)
            guard.command_start.assert_called_once()
            solar.press_power_button(16, solar.POWER_BUTTON_LONG_PRESS_SECONDS)
            guard.disarm.assert_called_once()


if __name__ == '__main__':
    unittest.main()
