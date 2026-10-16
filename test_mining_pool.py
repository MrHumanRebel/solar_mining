"""Regression tests for the unMineable integration; no network or GPIO calls."""
import json
from pathlib import Path
import tempfile
import unittest
from datetime import timedelta
from unittest.mock import Mock, patch

import simulate_decisions

solar = simulate_decisions.solar
ADDRESS = '0xaedac36dcfc956864fcc03ec2ef256facaefd991'


def workers_payload(rate='70060000000000', online=True):
    return {'success': True, 'data': {'pearlpow': {'workers': [
        {'name': 'solarminer', 'online': online, 'rhr': rate, 'chr': '999999999999999'}
    ]}}}


class MiningPoolTests(unittest.TestCase):
    def setUp(self):
        self.config = patch.multiple(solar, MINING_ALGORITHM='pearlpow', MINING_WORKER='solarminer')
        self.config.start()
        self.addCleanup(self.config.stop)

    def test_address_and_dashboard_url(self):
        self.assertEqual(solar._parse_wallet_address(ADDRESS), ADDRESS)
        self.assertEqual(solar._parse_wallet_address(
            f'https://unmineable.com/address/{ADDRESS}?coin=USDT'), ADDRESS)
        self.assertEqual(solar._parse_wallet_address('0x' + 'A' * 40), '0x' + 'a' * 40)

    def test_rejects_rvn_wrong_coin_and_untrusted_urls(self):
        for value in ['R' + '1' * 33, '0x123', f'https://evil.test/address/{ADDRESS}',
                      f'https://unmineable.com/address/{ADDRESS}?coin=RVN',
                      f'https://unmineable.com/address/{ADDRESS}?coin=USDT&coin=RVN',
                      f'http://unmineable.com/address/{ADDRESS}']:
            with self.subTest(value=value):
                self.assertIsNone(solar._parse_wallet_address(value))

    def test_legacy_environment_falls_back_to_new_destination(self):
        with patch.object(solar, 'WALLET_ADDRESS', 'R' + '1' * 33):
            self.assertEqual(solar._effective_wallet_address(), ADDRESS)

    def test_legacy_state_does_not_restore_rvn(self):
        with tempfile.TemporaryDirectory() as directory:
            state = Path(directory) / 'state.json'
            state.write_text(json.dumps({'wallet_address': 'R' + '1' * 33}))
            with patch.object(solar, 'STATE_FILE', str(state)), patch.object(solar, 'WALLET_ADDRESS', ADDRESS), \
                 patch.object(solar, '_last_production_start_at'), patch.object(solar, '_last_hashrate_restart_at'), \
                 patch.object(solar, '_last_force_shutdown_at'):
                solar.load_prev_state()
                self.assertEqual(solar.WALLET_ADDRESS, ADDRESS)

    def test_reported_rate_is_hs_and_not_calculated_rate(self):
        self.assertEqual(solar._extract_hashrate_from_wallet_payload(workers_payload()), 70.06e12)
        self.assertEqual(solar._format_hashrate(70.06e12), '70.06 TH/s')

    def test_recorded_v5_response_returns_real_pearlpow_rate(self):
        fixture = Path(__file__).parent / 'tests/fixtures/unmineable_v5_workers.json'
        payload = json.loads(fixture.read_text())
        account = Mock(json=Mock(return_value={'success': True, 'data': {'uuid': 'test-account'}}))
        workers = Mock(json=Mock(return_value=payload))
        with patch.object(solar.requests, 'get', side_effect=[account, workers]) as get:
            rate = solar._wallet_hashrate_hs(ADDRESS)
            self.assertEqual(rate, 235187980540458)
            self.assertEqual(solar._format_hashrate(rate), '235.19 TH/s')
            self.assertEqual(get.call_count, 2)
            self.assertTrue(all(call.args[0].startswith('https://api.unmineable.com/v5/')
                                for call in get.call_args_list))
        with patch.dict(solar._shared_snapshot, {'hashrate_hs': rate}):
            self.assertEqual(solar._build_snapshot_payload()['hashrate_text'], '235.19 TH/s')

    def test_recorded_response_without_pearlpow_is_unknown_not_zero(self):
        fixture = Path(__file__).parent / 'tests/fixtures/unmineable_v5_workers.json'
        payload = json.loads(fixture.read_text())
        del payload['data']['pearlpow']
        self.assertIsNone(solar._extract_hashrate_from_wallet_payload(payload))

    def test_other_workers_and_algorithms_are_not_this_rig(self):
        payload = workers_payload()
        payload['data']['pearlpow']['workers'].append(
            {'name': 'other', 'online': True, 'rhr': '999999999999999999'})
        payload['data']['randomx'] = {'workers': [{'name': 'solarminer', 'online': True, 'rhr': '1000'}]}
        self.assertEqual(solar._extract_hashrate_from_wallet_payload(payload), 70.06e12)

    def test_all_workers_can_be_selected_explicitly(self):
        payload = workers_payload('10')
        payload['data']['pearlpow']['workers'].append({'name': 'other', 'online': True, 'rhr': '20'})
        with patch.object(solar, 'MINING_WORKER', ''):
            self.assertEqual(solar._extract_hashrate_from_wallet_payload(payload), 30)

    def test_offline_zero_and_no_matching_workers(self):
        self.assertEqual(solar._extract_hashrate_from_wallet_payload(workers_payload(online=False)), 0)
        self.assertEqual(solar._extract_hashrate_from_wallet_payload(workers_payload('0')), 0)
        payload = workers_payload()
        payload['data']['pearlpow']['workers'] = []
        self.assertEqual(solar._extract_hashrate_from_wallet_payload(payload), 0)

    def test_invalid_or_missing_data_is_unknown(self):
        for payload in [{}, {'success': False}, {'success': True, 'data': {}}, [],
                        workers_payload('NaN'), workers_payload('inf'), workers_payload('-1'),
                        workers_payload(None), workers_payload(True), workers_payload(online=None)]:
            with self.subTest(payload=payload):
                self.assertIsNone(solar._extract_hashrate_from_wallet_payload(payload))

    def test_v5_address_resolution_and_worker_request(self):
        account = Mock(json=Mock(return_value={'success': True, 'data': {'uuid': 'test-uuid'}}))
        workers = Mock(json=Mock(return_value=workers_payload()))
        with patch.object(solar.requests, 'get', side_effect=[account, workers]) as get:
            self.assertEqual(solar._wallet_hashrate_hs(ADDRESS), 70.06e12)
            self.assertEqual(get.call_args_list[0].args[0], f'https://api.unmineable.com/v5/address/{ADDRESS}')
            self.assertEqual(get.call_args_list[0].kwargs['params'], {'coin': 'USDT'})
            self.assertEqual(get.call_args_list[1].args[0], 'https://api.unmineable.com/v5/account/test-uuid/workers')

    def test_api_failure_does_not_scrape_or_query_old_pool(self):
        with patch.object(solar.requests, 'get', side_effect=solar.requests.HTTPError('403')) as get, \
             patch.object(solar.time, 'sleep'):
            self.assertIsNone(solar._wallet_hashrate_hs(ADDRESS))
            self.assertEqual(get.call_count, 3)
            self.assertTrue(all(call.args[0].startswith('https://api.unmineable.com/') for call in get.call_args_list))

    def test_cache_is_partitioned_by_wallet_and_worker(self):
        now = solar.datetime.now(tz=solar.budapest_tz)
        with patch.object(solar, '_last_wallet_hashrate_key', None), \
             patch.object(solar, '_last_wallet_hashrate_hs', None), \
             patch.object(solar, '_last_wallet_hashrate_at', None), \
             patch.object(solar, '_wallet_hashrate_hs', side_effect=[10, 20, 30]) as fetch:
            self.assertEqual(solar._wallet_hashrate_hs_cached(ADDRESS, now), 10)
            self.assertEqual(solar._wallet_hashrate_hs_cached(ADDRESS, now), 10)
            self.assertEqual(solar._wallet_hashrate_hs_cached('0x' + '2' * 40, now), 20)
            with patch.object(solar, 'MINING_WORKER', 'other'):
                self.assertEqual(solar._wallet_hashrate_hs_cached(ADDRESS, now), 30)
            self.assertEqual(fetch.call_count, 3)

    def test_unavailable_readings_are_cached_and_retried_after_expiry(self):
        now = solar.datetime.now(tz=solar.budapest_tz)
        with patch.object(solar, '_last_wallet_hashrate_key', None), \
             patch.object(solar, '_last_wallet_hashrate_hs', None), \
             patch.object(solar, '_last_wallet_hashrate_at', None), \
             patch.object(solar, '_wallet_hashrate_hs', side_effect=[None, 70.06e12]) as fetch:
            self.assertIsNone(solar._wallet_hashrate_hs_cached(ADDRESS, now))
            self.assertIsNone(solar._wallet_hashrate_hs_cached(ADDRESS, now + timedelta(seconds=60)))
            self.assertEqual(fetch.call_count, 1)
            self.assertEqual(solar._wallet_hashrate_hs_cached(ADDRESS, now + timedelta(seconds=121)), 70.06e12)
            self.assertEqual(fetch.call_count, 2)

    def test_snapshot_formats_missing_rate_as_unknown(self):
        with patch.dict(solar._shared_snapshot, {'hashrate_hs': None}):
            payload = solar._build_snapshot_payload()
            self.assertEqual(payload['hashrate_text'], 'N/A')
            self.assertEqual(payload['mining_coin'], 'USDT')
        self.assertEqual(solar._format_hashrate(0), '0.00 H/s')


if __name__ == '__main__':
    unittest.main()
