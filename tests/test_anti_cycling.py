"""Regression tests for safe daytime mining continuity and switching frequency."""
import unittest
from datetime import datetime, timedelta
from unittest.mock import patch

from solar_mining.anti_cycling import live_surplus_can_continue, SoftStopDebouncer
from solar_mining.history_model import LOCAL
from tools.simulate_decisions import solar


T = datetime(2026, 11, 7, 13, 10, tzinfo=LOCAL)


class SolarSurplusContinuationTests(unittest.TestCase):
    def kwargs(self, **overrides):
        result=dict(requested_running=True, ping_reachable=True,
                    plan_reason='household_only_refill_not_feasible',
                    battery_soc=88, reserve_soc=90, protected_floor_soc=20,
                    pv_w=2369, measured_load_w=1133, surplus_margin_w=200)
        result.update(overrides)
        return result

    def test_reported_dashboard_solar_surplus_keeps_existing_rig_running(self):
        self.assertTrue(live_surplus_can_continue(**self.kwargs()))

    def test_cannot_start_stopped_or_unverified_machine_from_surplus(self):
        for updates in ({'requested_running':False},{'ping_reachable':None},
                        {'ping_reachable':False}):
            self.assertFalse(live_surplus_can_continue(**self.kwargs(**updates)))

    def test_never_borrows_unprotected_battery_or_acts_without_good_data(self):
        for updates in ({'battery_soc':80},{'pv_w':1200},
                        {'measured_load_w':float('nan')},{'pv_w':float('nan')},
                        {'reserve_soc':105},{'plan_reason':'battery_floor_would_be_crossed'},
                        {'plan_reason':'insufficient_history_or_live_data'},
                        {'plan_reason':'overnight_reserve_exceeds_battery_capacity'}):
            self.assertFalse(live_surplus_can_continue(**self.kwargs(**updates)))

    def decision(self, soc=88, pv=2369, load=1133, running=True, reason='household_only_refill_not_feasible'):
        budget={'safe':False,'reason':reason,'coverage':.5,'reserve_soc':90,
                'available_bridge_wh':7337,'required_bridge_wh':0}
        hints={'energy_budget':budget}
        status={'reachable':True if running else False,
                'state':'running' if running else 'off'}
        with patch.object(solar,'_history_recommendation',return_value=hints), \
             patch.object(solar._runtime_guard,'status',return_value=status), \
             patch.object(solar,'_control_window_details',
                          return_value={'active':True,'reason':'daylight'}):
            return solar._make_miner_decision(
                T,'production',soc,pv,33,556,544,1133,
                'clear sky',0,'clear sky',0,'clear sky',0,
                T.replace(hour=7),T.replace(hour=14,minute=54),
                {},{},55.2,200,{},current_load=load)

    def test_full_decision_never_hard_stops_on_forecast_only_noise(self):
        decision=self.decision()
        self.assertEqual(decision['desired_state'],'production',decision)
        self.assertTrue(decision['metrics']['solar_surplus_hold'])
        self.assertFalse(decision['hard_stop'])
        self.assertIn('measured PV surplus',decision['decision_summary'])

    def test_low_power_soft_stops_and_floor_still_hard_stops(self):
        low=self.decision(pv=900)
        self.assertEqual(low['desired_state'],'stop')
        self.assertFalse(low['hard_stop'])
        unsafe=self.decision(soc=20,pv=2369)
        self.assertEqual(unsafe['desired_state'],'stop')
        self.assertTrue(unsafe['hard_stop'])

    def test_missing_power_data_never_gets_live_surplus_bypass(self):
        bad=self.decision(load=float('nan'),reason='insufficient_history_or_live_data')
        self.assertEqual(bad['desired_state'],'stop')
        self.assertTrue(bad['hard_stop'])


class DebounceTests(unittest.TestCase):
    def test_three_independent_polls_needed_with_duplicate_uploads_ignored(self):
        guard=SoftStopDebouncer(3)
        def check(t,desired='stop',hard=False):
            return guard.observe(prior_state='production',desired_state=desired,
                                 hard_stop=hard,sample_at=t)
        self.assertFalse(check(T))
        self.assertEqual(guard.samples,1)
        self.assertFalse(check(T))  # Same upload, another controller loop.
        self.assertEqual(guard.samples,1)
        self.assertFalse(check(T+timedelta(minutes=5)))
        self.assertTrue(check(T+timedelta(minutes=10)))
        self.assertTrue(check(T+timedelta(minutes=10)))  # Does not add votes.
        self.assertTrue(check(T+timedelta(minutes=15),desired='production'))
        self.assertEqual(guard.samples,0)
        self.assertFalse(check(T+timedelta(minutes=20)))

    def test_real_safety_stop_is_immediate(self):
        guard=SoftStopDebouncer(3)
        self.assertTrue(guard.observe(prior_state='production',
                    desired_state='stop',hard_stop=True,sample_at=T))
        self.assertEqual(guard.samples,0)

    def test_missing_or_out_of_order_samples_cannot_advance_stop(self):
        guard=SoftStopDebouncer(3)
        self.assertFalse(guard.observe(prior_state='production',desired_state='stop',sample_at=T))
        self.assertFalse(guard.observe(prior_state='production',desired_state='stop',
                                       sample_at=T-timedelta(minutes=5)))
        self.assertEqual(guard.samples,1)
        self.assertFalse(guard.observe(prior_state='production',desired_state='stop',
                                       sample_at=T+timedelta(minutes=25)))
        self.assertEqual(guard.samples,1)
        self.assertFalse(guard.observe(prior_state='production',desired_state='stop',sample_at=None))
        self.assertEqual(guard.samples,0)

    def test_existing_transition_guard_holds_on_then_waits_before_restart(self):
        with patch.object(solar,'uptime',T),patch.object(solar,'MIN_RUN_MINUTES',30), \
             patch.object(solar,'MIN_RESTART_DELAY_MINUTES',45):
            self.assertEqual(solar._apply_transition_guard(
                'production','stop',T+timedelta(minutes=20))[0],'production')
            self.assertEqual(solar._apply_transition_guard(
                'production','stop',T+timedelta(minutes=31))[0],'stop')
            self.assertEqual(solar._apply_transition_guard(
                'stop','production',T+timedelta(minutes=30))[0],'stop')
            self.assertEqual(solar._apply_transition_guard(
                'stop','production',T+timedelta(minutes=46))[0],'production')


if __name__=='__main__':
    unittest.main()
