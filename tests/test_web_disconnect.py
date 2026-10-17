import io
import json
import socket
import struct
import threading
import unittest
from http.server import ThreadingHTTPServer
from unittest.mock import Mock, patch
from urllib.request import urlopen
from tools.simulate_decisions import solar


class WebDisconnectTests(unittest.TestCase):
    def handler(self):
        handler=solar.WebHandler.__new__(solar.WebHandler)
        handler.send_response=Mock()
        handler.send_header=Mock()
        handler.end_headers=Mock()
        handler.wfile=Mock()
        handler.close_connection=False
        return handler

    def test_disconnect_in_headers_or_body_is_handled(self):
        for stage in ('end_headers','write'):
            for error in (BrokenPipeError,ConnectionResetError):
                with self.subTest(stage=stage,error=error):
                    handler=self.handler()
                    target=handler.end_headers if stage=='end_headers' else handler.wfile.write
                    target.side_effect=error('client disconnected')
                    handler._write(200,b'{}','application/json')
                    self.assertTrue(handler.close_connection)
                    self.assertEqual(target.call_count,1)

    def test_server_errors_are_not_hidden(self):
        handler=self.handler()
        handler.wfile.write.side_effect=OSError('server failure')
        with self.assertRaises(OSError):
            handler._write(200,b'{}','application/json')

    def test_cancelled_response_never_repeats_miner_action(self):
        handler=self.handler()
        raw=json.dumps({'action':'stop'}).encode()
        handler.path='/api/action'
        handler.headers={'Content-Length':str(len(raw))}
        handler.rfile=io.BytesIO(raw)
        handler.wfile.write.side_effect=BrokenPipeError('client left')
        with patch.object(solar,'_miner_action',return_value={'ok':True}) as action:
            handler.do_POST()
            action.assert_called_once_with('stop')

    def test_real_socket_reset_keeps_server_available_without_traceback(self):
        headers_sent=threading.Event()
        client_closed=threading.Event()
        finished=threading.Event()
        errors=[]
        class Handler(solar.WebHandler):
            def end_headers(self):
                super().end_headers()
                if self.path=='/api/snapshot':
                    headers_sent.set()
                    if not client_closed.wait(5):
                        raise RuntimeError('client did not close')
        class Server(ThreadingHTTPServer):
            def handle_error(self,*args):
                errors.append(True)
            def process_request_thread(self,*args):
                try:
                    super().process_request_thread(*args)
                finally:
                    finished.set()
        server=Server(('127.0.0.1',0),Handler)
        thread=threading.Thread(target=server.serve_forever,daemon=True)
        thread.start()
        try:
            with patch.object(solar,'_build_snapshot_payload',return_value={}):
                with socket.create_connection(server.server_address,timeout=5) as client:
                    client.sendall(b'GET /api/snapshot HTTP/1.0\r\nHost: localhost\r\n\r\n')
                    self.assertTrue(headers_sent.wait(5))
                    client.setsockopt(socket.SOL_SOCKET,socket.SO_LINGER,struct.pack('ii',1,0))
                client_closed.set()
                self.assertTrue(finished.wait(5))
                self.assertEqual(errors,[])
                with urlopen(f'http://127.0.0.1:{server.server_port}/',timeout=5) as response:
                    self.assertIn(b'Solar Mining',response.read())
        finally:
            client_closed.set()
            server.shutdown()
            server.server_close()
            thread.join(timeout=5)
