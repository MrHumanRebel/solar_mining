from contextlib import redirect_stdout
import io
import json
import unittest
from unittest.mock import patch

import requests

from tools.simulate_decisions import solar


def response(status, body):
    result = requests.Response()
    result.status_code = status
    result._content = json.dumps(body).encode('utf-8')
    return result


class SolarmanApiTests(unittest.TestCase):
    def setUp(self):
        self.enterContext(patch.multiple(solar, APP_ID='test-app-id',
                                         APP_SECRET='test-secret', EMAIL='sample@example.test',
                                         PASSWORD='test-password'))
        self.post = self.enterContext(patch.object(solar.requests, 'post'))
        self.log = self.enterContext(redirect_stdout(io.StringIO()))

    def test_fetches_token_and_readings_using_existing_authentication(self):
        readings = {'success': True, 'code': '1000000', 'dataList': [{'key': 'BMS_SOC', 'value': 79}]}
        self.post.side_effect = [response(200, {'access_token': 'test-token'}), response(200, readings)]

        token = solar.get_access_token()
        self.assertEqual('test-token', token)
        self.assertEqual(readings, solar.fetch_current_data(token))
        token_request, device_request = self.post.call_args_list
        self.assertEqual({'appId': 'test-app-id', 'language': 'en'}, token_request.kwargs['params'])
        self.assertEqual(solar.sha256_hash('test-password'), token_request.kwargs['json']['password'])
        self.assertEqual('Bearer test-token', device_request.kwargs['headers']['Authorization'])
        self.assertEqual({'deviceSn': solar.DEVICE_SN}, device_request.kwargs['json'])
        self.assertNotIn('test-token', self.log.getvalue())

    def test_http_success_with_api_rejection_logs_code_only(self):
        self.post.return_value = response(200, {'success': False, 'code': '2101025',
                                               'msg': 'test-secret sample@example.test'})
        self.assertIsNone(solar.get_access_token())
        self.assertIn('token: HTTP 200, request rejected, API code 2101025', self.log.getvalue())
        self.assertNotIn('test-secret', self.log.getvalue())
        self.assertNotIn('sample@example.test', self.log.getvalue())

    def test_empty_response_and_missing_configuration_have_distinct_diagnostics(self):
        with patch.object(solar, 'PASSWORD', ' '):
            self.assertIsNone(solar.get_access_token())
        self.post.assert_not_called()
        self.assertIn('missing configuration (MY_PASSWORD)', self.log.getvalue())

        self.post.return_value = response(200, {})
        self.assertIsNone(solar.get_access_token())
        self.assertIn('access_token missing or invalid', self.log.getvalue())

    def test_invalid_response_and_transport_error_do_not_expose_request_details(self):
        self.post.side_effect = [response(200, []), requests.Timeout('url with test-app-id')]
        self.assertIsNone(solar.get_access_token())
        self.assertIsNone(solar.get_access_token())
        self.assertIn('expected a JSON object', self.log.getvalue())
        self.assertIn('request failed (Timeout)', self.log.getvalue())
        self.assertNotIn('test-app-id', self.log.getvalue())

    def test_reports_device_api_error_and_empty_readings(self):
        self.post.side_effect = [response(403, {'code': 2101023}), response(200, {'dataList': []})]
        self.assertEqual({}, solar.fetch_current_data('test-token'))
        self.assertIn('currentData: HTTP 403, request rejected, API code 2101023', self.log.getvalue())
        self.assertEqual({'dataList': []}, solar.fetch_current_data('test-token'))
        self.assertIn('no device readings in response', self.log.getvalue())


if __name__ == '__main__':
    unittest.main()
