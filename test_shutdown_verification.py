"""A logical STOP is not physical proof: verify long presses with device data."""
from datetime import timedelta
from unittest.mock import Mock, patch
import unittest
from test_miner_power_guard import armed_guard, sample, T
from simulate_decisions import solar
from miner_power_guard import MinerPowerGuard
from status_messages import status


class ShutdownVerificationTests(unittest.TestCase):
    def request(self,guard):
        s=sample(25)
        self.assertTrue(guard.observe(s,s.at,'stop'))
        guard.command_stop_finished(s.at+timedelta(seconds=10))
        return s

    def test_success_waits_for_post_press_both_phase_drop_and_never_retries(self):
        guard=armed_guard()
        first=self.request(guard)
        self.assertIsNotNone(guard.signature)
        self.assertEqual(guard.status(first.at)['state'],'stop_pending')
        cached=sample(25.1,400,100,100,200)  # before the ten-second press ended
        self.assertFalse(guard.observe(cached,cached.at,'stop'))
        self.assertEqual(guard.runtime_state,'stop_pending')
        off=sample(30,400,100,100,200)
        self.assertFalse(guard.observe(off,off.at,'stop'))
        self.assertEqual(guard.runtime_state,'off')
        self.assertEqual(guard.confirmed_off_at,off.at)
        for minute in (35,40,45):
            cook=sample(minute)
            self.assertFalse(guard.observe(cook,cook.at,'stop'))
        self.assertEqual(guard.shutdown_attempts,1)

    def test_later_cooking_load_becomes_unknown_without_rearming_a_confirmed_off_run(self):
        guard=armed_guard();self.request(guard)
        off=sample(30,400,100,100,200)
        guard.observe(off,off.at,'stop')
        self.assertEqual(guard.runtime_state,'off')
        cook=sample(35)
        self.assertFalse(guard.observe(cook,cook.at,'stop'))
        self.assertEqual(guard.runtime_state,'unknown')
        self.assertIsNone(guard.signature)
        self.assertEqual(guard.shutdown_attempts,1)

    def test_failure_retries_once_only_from_a_new_matching_post_press_reading(self):
        guard=armed_guard()
        self.request(guard)
        current=sample(30)
        self.assertTrue(guard.observe(current,current.at,'stop'))
        guard.command_stop_finished(current.at+timedelta(seconds=10))
        for minute in (35,40,45,50,55,60,65,70,75):
            current=sample(minute)
            self.assertFalse(guard.observe(current,current.at,'stop'))
        self.assertEqual(guard.shutdown_attempts,2)
        self.assertEqual(guard.runtime_state,'stop_failed')
        self.assertIn('manual inspection',guard.reason)
        self.assertIsNotNone(guard.signature)

    def test_l1_household_load_does_not_veto_identified_l2_l3_miner_stop(self):
        guard=armed_guard()
        current=sample(25,1325,225,550,550)
        self.assertTrue(guard.observe(current,current.at,'stop'))

    def test_one_phase_drop_is_ambiguous_not_success_and_cannot_rearm(self):
        guard=armed_guard()
        self.request(guard)
        partial=sample(30,750,100,100,550)
        self.assertFalse(guard.observe(partial,partial.at,'stop'))
        self.assertNotEqual(guard.runtime_state,'off')
        self.assertIsNone(guard.signature)
        self.assertFalse(guard.observe(sample(35),sample(35).at,'stop'))

    def test_unknown_restart_and_oven_do_not_authorize_any_automatic_press(self):
        guard=MinerPowerGuard()
        for minute in (0,5,10,15):
            current=sample(minute,3000,100,2700,200)
            self.assertFalse(guard.observe(current,current.at,'stop'))
        self.assertEqual(guard.status(sample(15).at)['state'],'unknown')
        self.assertEqual(guard.shutdown_attempts,0)

    def test_manual_stop_without_identity_is_pending_not_falsely_confirmed(self):
        guard=MinerPowerGuard()
        guard.command_stop_finished(T)
        off=sample(5,200,20,80,100)
        self.assertFalse(guard.observe(off,off.at,'stop'))
        self.assertNotEqual(guard.runtime_state,'off')
        self.assertEqual(guard.shutdown_attempts,1)

    def test_one_fresh_prestart_anchor_can_learn_two_stable_post_start_rises(self):
        guard=MinerPowerGuard()
        off=sample(0,400,100,100,200)
        guard.command_start(off,off.at+timedelta(seconds=1))
        self.assertIsNotNone(guard.baseline)
        for minute in (5,10):
            current=sample(minute)
            self.assertFalse(guard.observe(current,current.at,'production'))
        self.assertEqual(guard.runtime_state,'running')
        current=sample(15)
        self.assertTrue(guard.observe(current,current.at,'stop'))

    def test_shutdown_can_learn_pending_start_rise_even_when_decision_already_stop(self):
        guard=MinerPowerGuard()
        off=sample(0,400,100,100,200)
        guard.command_start(off,off.at+timedelta(seconds=1))
        self.assertFalse(guard.observe(sample(5),sample(5).at,'stop'))
        self.assertTrue(guard.observe(sample(10),sample(10).at,'stop'))

    def test_stale_duplicate_future_and_changed_source_do_not_retry(self):
        for kind in ('stale','duplicate','future','source','gap'):
            with self.subTest(kind=kind):
                guard=armed_guard();self.request(guard)
                current=sample(30);now=current.at
                if kind=='stale': now+=timedelta(minutes=10)
                elif kind=='duplicate': current=sample(25)
                elif kind=='future': now-=timedelta(minutes=1)
                elif kind=='source':
                    from dataclasses import replace
                    current=replace(current,source='other')
                elif kind=='gap': current=sample(45);now=current.at
                self.assertFalse(guard.observe(current,now,'stop'))
                self.assertNotEqual(guard.status(now)['state'],'off')

    def test_retry_does_not_drop_total_threshold_or_follow_ambiguous_oven_changes(self):
        for current in (sample(30,1000),sample(30,3000,100,2500,550)):
            guard=armed_guard();self.request(guard)
            self.assertFalse(guard.observe(current,current.at,'stop'))
            self.assertEqual(guard.runtime_state,'stop_failed')
            self.assertEqual(guard.shutdown_attempts,1)

    def test_gpio_failure_keeps_identity_and_is_not_reported_as_shutdown(self):
        guard=armed_guard()
        gpio=Mock()
        with patch.object(solar,'_power_guard',guard),patch.object(solar,'_latest_power_sample',sample(25)), \
             patch.object(solar,'is_rpi',True),patch.object(solar,'GPIO_AVAILABLE',True), \
             patch.object(solar,'GPIO',gpio,create=True),patch.object(solar.time,'sleep',side_effect=OSError('GPIO timer failed')), \
             patch.object(solar,'_last_force_shutdown_at',None):
            self.assertFalse(solar.press_power_button(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS))
        gpio.cleanup.assert_called_once()
        self.assertIn(unittest.mock.call(16,gpio.LOW),gpio.output.call_args_list)
        self.assertEqual(guard.runtime_state,'stop_failed')
        self.assertIsNotNone(guard.signature)

    def test_snapshot_and_telegram_distinguish_desired_stop_from_physical_failure(self):
        guard=armed_guard();self.request(guard)
        current=sample(30);guard.observe(current,current.at,'stop')
        guard.command_stop_finished(current.at+timedelta(seconds=10))
        current=sample(35);guard.observe(current,current.at,'stop')
        text=status({'state':'stop','runtime':guard.status(current.at)},current.at)
        self.assertIn('Kívánt állapot: stop',text)
        self.assertIn('Fizikai állapot: leállítás nincs igazolva',text)
        self.assertIn('2/2',text)

    def test_supervisor_uses_long_presses_and_announces_failed_shutdown(self):
        guard=armed_guard()
        with patch.object(solar,'_power_guard',guard),patch.object(solar,'is_rpi',True), \
             patch.object(solar,'GPIO_AVAILABLE',True),patch.object(solar,'_last_power_notice_key',None), \
             patch.object(solar,'_last_force_shutdown_at',None),patch.object(solar,'save_prev_state'), \
             patch.object(solar,'_latest_power_sample',None),patch.object(solar,'_power_measurement_error',None), \
             patch.object(solar,'_extract_power_sample') as extract, \
             patch.object(solar,'press_power_button',return_value=True) as press, \
             patch.object(solar,'send_telegram_message_async') as send, \
             patch.object(solar,'send_telegram_message') as sync_send:
            for minute in (25,30,35,40,45,50,55,60,65,70,75):
                current=sample(minute);extract.return_value=current
                solar.supervise_runtime_by_power(current.at,'stop',{})
            sync_send.assert_not_called()
            self.assertEqual(press.call_count,2)
            self.assertTrue(all(c.args==(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS) for c in press.call_args_list))
            self.assertGreaterEqual(solar.POWER_BUTTON_LONG_PRESS_SECONDS,10)
            self.assertIn('kézi ellenőrzés',send.call_args.args[0])
            self.assertEqual(guard.runtime_state,'stop_failed')
            self.assertEqual(send.call_count,3)  # first signal, retry, final failure; no spam

    def test_supervisor_confirms_success_without_a_second_press(self):
        guard=armed_guard()
        with patch.object(solar,'_power_guard',guard),patch.object(solar,'is_rpi',True), \
             patch.object(solar,'GPIO_AVAILABLE',True),patch.object(solar,'_last_power_notice_key',None), \
             patch.object(solar,'_last_force_shutdown_at',None),patch.object(solar,'save_prev_state'), \
             patch.object(solar,'_latest_power_sample',None),patch.object(solar,'_power_measurement_error',None), \
             patch.object(solar,'_extract_power_sample') as extract, \
             patch.object(solar,'press_power_button',return_value=True) as press, \
             patch.object(solar,'send_telegram_message_async') as send, \
             patch.object(solar,'send_telegram_message') as sync_send:
            for current in (sample(25),sample(30,400,100,100,200),sample(35,400,100,100,200)):
                extract.return_value=current
                solar.supervise_runtime_by_power(current.at,'stop',{})
            sync_send.assert_not_called()
            press.assert_called_once_with(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS)
            self.assertIn('eltűnt',send.call_args.args[0])
            self.assertEqual(guard.runtime_state,'off')

    def test_known_running_failed_stop_is_not_counted_as_household_only_load(self):
        from datetime import datetime
        from history_model import LOCAL
        guard=armed_guard();self.request(guard)
        guard.runtime_state='stop_failed'
        now=datetime(2026,10,17,15,tzinfo=LOCAL)
        with patch.object(solar,'_power_guard',guard), \
             patch.object(solar,'_history_recommendation',wraps=solar._history_recommendation) as recommend:
            result=solar._make_miner_decision(now,'stop',99,2000,100,550,550,1200,
                'clear sky',0,'clear sky',0,'clear sky',0,now.replace(hour=7),now.replace(hour=16),
                {},{},53,200,{},current_load=1200)
        self.assertTrue(recommend.call_args.args[7])
        self.assertEqual(result['desired_state'],'stop')
        self.assertTrue(result['hard_stop'])
        self.assertIn('Shutdown not confirmed',result['decision_summary'])

    def test_gui_and_telegram_stop_routes_use_only_long_press_and_do_not_claim_off(self):
        from datetime import datetime
        from history_model import LOCAL
        now=datetime.now(LOCAL)
        for action in ('stop','force_stop'):
            with patch.object(solar,'is_rpi',True),patch.object(solar,'GPIO_AVAILABLE',True), \
                 patch.object(solar,'press_power_button',return_value=True) as press, \
                 patch.object(solar,'send_telegram_message') as send, \
                 patch.object(solar,'send_telegram_message_async'):
                solar.process_message('/'+action,0,0,'stop','clear sky',now,now,0,None,None)
                self.assertEqual(press.call_args.args,(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS))
                self.assertTrue(any(word in send.call_args.args[0] for word in ('ellenőrzés','igazolva')))
                result=solar._miner_action(action)
                self.assertTrue(result['ok'])
                self.assertEqual(press.call_args.args,(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS))


if __name__=='__main__':
    unittest.main()
