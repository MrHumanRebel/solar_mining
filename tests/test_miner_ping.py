from datetime import datetime,timedelta,timezone
import subprocess
import unittest
from unittest.mock import Mock,patch
from solar_mining.miner_ping_guard import MinerPingGuard,ping_host
from tools.simulate_decisions import solar

T=datetime(2026,10,17,14,0,tzinfo=timezone.utc)

class PingStateTests(unittest.TestCase):
    def test_restart_stop_online_needs_no_old_start_or_power_reading(self):
        guard=MinerPingGuard();guard.set_desired('stop')
        self.assertTrue(guard.observe(True,T))
        self.assertEqual(guard.shutdown_attempts,1)
        self.assertEqual(guard.runtime_state,'stop_pending')

    def test_shutdown_requires_two_post_command_misses_and_retry_is_bounded(self):
        guard=MinerPingGuard();guard.set_desired('stop')
        self.assertTrue(guard.observe(True,T));guard.command_stop_finished(T+timedelta(seconds=10))
        self.assertFalse(guard.observe(True,T+timedelta(seconds=25)))
        self.assertTrue(guard.observe(True,T+timedelta(seconds=45)))
        guard.command_stop_finished(T+timedelta(seconds=55))
        self.assertFalse(guard.observe(True,T+timedelta(seconds=90)))
        self.assertEqual(guard.runtime_state,'stop_failed')
        self.assertFalse(guard.observe(True,T+timedelta(minutes=48)))
        self.assertEqual(guard.shutdown_attempts,2)
        self.assertFalse(guard.observe(False,T+timedelta(minutes=49)))
        self.assertNotEqual(guard.runtime_state,'off')
        self.assertFalse(guard.observe(False,T+timedelta(minutes=49,seconds=15)))
        self.assertEqual(guard.runtime_state,'off')

    def test_online_ping_between_misses_prevents_false_off_confirmation(self):
        g=MinerPingGuard();g.set_desired('production')
        for seconds,reply in ((0,False),(15,True),(30,False)):
            self.assertFalse(g.observe(reply,T+timedelta(seconds=seconds)))
            self.assertNotEqual(g.runtime_state,'off')

    def test_probe_errors_are_not_off_and_do_not_authorize_gpio(self):
        g=MinerPingGuard();g.set_desired('stop')
        for seconds in (0,15,30):self.assertFalse(g.observe(None,T+timedelta(seconds=seconds)))
        self.assertEqual(g.runtime_state,'stop_unverified')
        self.assertEqual(g.shutdown_attempts,0)

    def test_already_unreachable_target_is_not_pressed(self):
        g=MinerPingGuard();g.set_desired('stop')
        self.assertFalse(g.observe(False,T));self.assertFalse(g.observe(False,T+timedelta(seconds=15)))
        self.assertEqual(g.shutdown_attempts,0)
        self.assertEqual(g.runtime_state,'off')

    def test_online_return_under_standing_stop_creates_a_new_episode(self):
        g=MinerPingGuard();g.set_desired('stop')
        g.observe(False,T);g.observe(False,T+timedelta(seconds=15))
        self.assertTrue(g.observe(True,T+timedelta(seconds=30)))

    def test_production_or_unknown_intent_never_requests_shutdown(self):
        for intent in ('unknown','production'):
            g=MinerPingGuard();g.set_desired(intent)
            self.assertFalse(g.observe(True,T))
            self.assertEqual(g.runtime_state,'running')

    def test_old_ping_status_is_not_a_current_online_offline_claim(self):
        g=MinerPingGuard();g.observe(True,T)
        self.assertIsNone(g.status(T+timedelta(seconds=61))['reachable'])
        self.assertEqual(g.status(T+timedelta(seconds=61))['state'],'unknown')

    def test_boot_grace_and_error_do_not_confirm_shutdown(self):
        g=MinerPingGuard();g.command_start(T)
        g.observe(False,T+timedelta(seconds=15));g.observe(False,T+timedelta(seconds=30))
        self.assertEqual(g.runtime_state,'starting')
        g.observe(True,T+timedelta(seconds=45));self.assertEqual(g.runtime_state,'running')

    def test_command_reservation_not_double_counted_and_new_intent_resets_budget(self):
        g=MinerPingGuard();g.set_desired('stop');g.observe(True,T)
        self.assertFalse(g.set_desired('production'))  # Also while the GPIO command is reserved.
        g.command_stop_finished(T,success=False)
        self.assertEqual(g.shutdown_attempts,1)
        g.set_desired('stop');self.assertEqual(g.shutdown_attempts,1)
        self.assertFalse(g.set_desired('production'))
        self.assertEqual(g.desired_state,'stop')
        g.set_desired('production',force=True);self.assertEqual(g.shutdown_attempts,0)

class ProbeTests(unittest.TestCase):
    def test_linux_ping_return_codes_and_timeouts_are_distinguished(self):
        for code,expected in ((0,True),(1,False),(2,None)):
            with patch('solar_mining.miner_ping_guard.subprocess.run',return_value=Mock(returncode=code)) as run:
                self.assertIs(ping_host('192.168.0.185'),expected)
                self.assertEqual(run.call_args.args[0][-1],'192.168.0.185')
                self.assertNotIn('shell',run.call_args.kwargs)
        for error in (FileNotFoundError(),PermissionError(),subprocess.TimeoutExpired('ping',6)):
            with patch('solar_mining.miner_ping_guard.subprocess.run',side_effect=error):self.assertIsNone(ping_host('192.168.0.185'))

    def test_address_is_validated_without_shell_execution(self):
        with patch('solar_mining.miner_ping_guard.subprocess.run') as run:
            with self.assertRaises(ValueError):ping_host('192.168.0.185; false')
            run.assert_not_called()

class PingIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.guard=self.enterContext(patch.object(solar,'_runtime_guard',MinerPingGuard()))
        self.enterContext(patch.object(solar,'_last_power_notice_key',None))
        self.enterContext(patch.object(solar,'_last_force_shutdown_at',None))
        self.enterContext(patch.object(solar,'send_telegram_message_async'))
        self.enterContext(patch.object(solar,'save_prev_state'))
        self.enterContext(patch.object(solar,'is_rpi',True))
        self.enterContext(patch.object(solar,'GPIO_AVAILABLE',True))

    def test_tick_shutdowns_online_target_with_no_solarman_or_signature(self):
        self.guard.set_desired('stop')
        with patch.object(solar,'ping_host',return_value=True),patch.object(solar,'press_power_button',return_value=True) as press, \
             patch.object(solar,'fetch_current_data',side_effect=AssertionError('extra Solar API')):
            result=solar._runtime_tick()
        press.assert_called_once_with(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS)
        self.assertEqual(result['state'],'stop_pending')
        self.assertGreaterEqual(solar.POWER_BUTTON_LONG_PRESS_SECONDS,10)

    def test_monitor_runs_every_15_seconds_without_waiting_for_solar_polling(self):
        with patch.object(solar,'_runtime_tick') as tick,patch.object(solar.time,'sleep',side_effect=StopIteration) as sleep:
            with self.assertRaises(StopIteration):solar._ping_monitor_loop()
            tick.assert_called_once();sleep.assert_called_once_with(15)

    def test_main_restores_stop_before_starting_independent_ping_worker(self):
        weather=('clear sky',T,T+timedelta(hours=8),0,'clear',0,'','clear',0,'',{})
        with patch.object(solar,'historical_profile',{}),patch.object(solar,'load_prev_state',return_value=('stop',T)), \
             patch.object(solar,'load_quote_usage',return_value=0),patch.object(solar,'get_current_weather',return_value=weather), \
             patch.object(solar.threading,'Thread') as thread,patch.object(solar,'ThreadPoolExecutor'), \
             patch.object(solar,'_solarman_poll_slot',side_effect=StopIteration):
            with self.assertRaises(StopIteration):solar.main_loop()
            self.assertEqual(self.guard.desired_state,'stop')
            self.assertTrue(any(c.kwargs.get('target') is solar._ping_monitor_loop and c.kwargs.get('daemon') for c in thread.call_args_list))

    def test_start_never_pulses_a_reachable_or_uncertain_target(self):
        for replies in ([True],[None],[False,None],[False,True]):
            with patch.object(solar,'ping_host',side_effect=replies),patch.object(solar,'press_power_button') as press:
                solar._ensure_miner_started();press.assert_not_called()

    def test_start_pulses_only_after_two_unanswered_checks(self):
        with patch.object(solar,'ping_host',side_effect=[False,False]),patch.object(solar,'press_power_button',return_value=True) as press:
            self.assertTrue(solar._ensure_miner_started()['ok'])
        press.assert_called_once_with(16,solar.POWER_BUTTON_SHORT_PRESS_SECONDS)

    def test_gpio_hold_is_long_and_cleanup_always_runs(self):
        gpio=Mock()
        with patch.object(solar,'GPIO',gpio,create=True),patch.object(solar.time,'sleep') as sleep:
            self.assertTrue(solar.press_power_button(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS))
        sleep.assert_called_once_with(solar.POWER_BUTTON_LONG_PRESS_SECONDS)
        gpio.cleanup.assert_called_once()
        self.assertEqual(self.guard.runtime_state,'stop_pending')
        gpio.reset_mock()
        with patch.object(solar,'GPIO',gpio,create=True),patch.object(solar.time,'sleep',side_effect=OSError('timer failed')):
            self.assertFalse(solar.press_power_button(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS))
        gpio.cleanup.assert_called_once()
        self.assertEqual(self.guard.runtime_state,'stop_failed')

    def test_measurements_never_operate_gpio_or_ping(self):
        with patch.object(solar,'ping_host') as ping,patch.object(solar,'press_power_button') as press:
            solar.record_live_power(T,'stop',{})
            ping.assert_not_called();press.assert_not_called()

    def test_manual_gui_stop_routes_use_ping_then_long_press(self):
        for action in ('stop','force_stop'):
            self.guard.set_desired('production',force=True)
            with patch.object(solar,'ping_host',return_value=True),patch.object(solar,'press_power_button',return_value=True) as press:
                self.assertTrue(solar._miner_action(action)['ok'])
                press.assert_called_once_with(16,solar.POWER_BUTTON_LONG_PRESS_SECONDS)

if __name__=='__main__':unittest.main()
