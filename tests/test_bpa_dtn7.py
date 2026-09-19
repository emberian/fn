import http.server
import json
from pathlib import Path
import socket
import socketserver
import sys
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import bpa_dtn7 as bpa  # noqa: E402


class _Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    address_family = socket.AF_INET6


class _Handler(http.server.BaseHTTPRequestHandler):
    routes = {}
    seen = []

    def log_message(self, _format, *_args):
        pass

    def do_GET(self):
        self.__class__.seen.append(self.path)
        response = self.__class__.routes.get(self.path, (404, {}, b"not found"))
        if callable(response):
            response = response()
        status, headers, body = response
        self.send_response(status)
        for name, value in headers.items():
            self.send_header(name, value)
        self.end_headers()
        if isinstance(body, tuple):
            for chunk in body:
                self.wfile.write(chunk)
                self.wfile.flush()
        else:
            try:
                self.wfile.write(body)
            except (BrokenPipeError, ConnectionResetError):
                pass


class BpaDtn7ClientTests(unittest.TestCase):
    def setUp(self):
        _Handler.routes = {}
        _Handler.seen = []
        self.server = _Server(("::1", 0), _Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        self.client = bpa.BpaDtn7Client(self.server.server_port, timeout_seconds=0.2,
                                        max_bundle_bytes=128)

    def tearDown(self):
        self.server.shutdown()
        self.server.server_close()
        self.thread.join()

    @staticmethod
    def fixed(status, body):
        return status, {"Content-Length": str(len(body))}, body

    def test_inventory_uses_local_http_json_and_returns_bounded_tuple(self):
        body = json.dumps(["dtn://bp-a/-1", "dtn://bp-a/-2"]).encode()
        _Handler.routes["/status/bundles"] = self.fixed(200, body)
        self.assertEqual(self.client.inventory(), ("dtn://bp-a/-1", "dtn://bp-a/-2"))
        self.assertEqual(_Handler.seen, ["/status/bundles"])

    def test_download_is_bounded_and_percent_encodes_query_delimiters(self):
        bid = "dtn://bp-a/a?not-query"
        encoded = "/download?dtn://bp-a/a%3Fnot-query"
        _Handler.routes[encoded] = self.fixed(200, b"opaque-bp-cbor")
        self.assertEqual(self.client.download_bundle(bid), b"opaque-bp-cbor")
        self.assertEqual(_Handler.seen, [encoded])

    def test_delete_is_explicit_and_does_not_use_endpoint_pop(self):
        bid = "dtn://bp-a/-9"
        _Handler.routes["/delete?dtn://bp-a/-9"] = self.fixed(200, b"Deleted")
        self.client.delete(bid)
        self.assertEqual(_Handler.seen, ["/delete?dtn://bp-a/-9"])

    def test_declared_oversize_is_rejected_before_body_read(self):
        _Handler.routes["/status/bundles"] = (200, {"Content-Length": str(bpa.MAX_INVENTORY_RESPONSE_BYTES + 1)}, b"")
        with self.assertRaises(bpa.BpaDtn7ResponseTooLarge):
            self.client.inventory()

    def test_chunked_oversize_download_is_rejected(self):
        client = bpa.BpaDtn7Client(self.server.server_port, max_bundle_bytes=8)
        _Handler.routes["/download?dtn://bp-a/-1"] = (200, {"Transfer-Encoding": "chunked"},
            (b"8\r\n12345678\r\n", b"1\r\n9\r\n", b"0\r\n\r\n"))
        with self.assertRaises(bpa.BpaDtn7ResponseTooLarge):
            client.download_bundle("dtn://bp-a/-1")

    def test_bad_inventory_shape_duplicate_and_bad_utf8_are_refused(self):
        _Handler.routes["/status/bundles"] = self.fixed(200, b'{"not":"a list"}')
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            self.client.inventory()
        _Handler.routes["/status/bundles"] = self.fixed(200, b'["dtn://x/-1","dtn://x/-1"]')
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            self.client.inventory()
        _Handler.routes["/status/bundles"] = self.fixed(200, b'["\xff"]')
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            self.client.inventory()

    def test_http_refusal_and_timeout_propagate_as_bpa_boundary_errors(self):
        _Handler.routes["/download?dtn://bp-a/-gone"] = self.fixed(404, b"Bundle not found")
        with self.assertRaises(bpa.BpaDtn7HttpError) as failure:
            self.client.download_bundle("dtn://bp-a/-gone")
        self.assertEqual(failure.exception.status, 404)

        def slow():
            time.sleep(0.4)
            return self.fixed(200, b"[]")
        _Handler.routes["/status/bundles"] = slow
        with self.assertRaises(bpa.BpaDtn7Timeout):
            self.client.inventory()

    def test_a_transfer_inside_every_read_window_still_hits_the_total_deadline(self):
        """The per-read timeout alone cannot bound a transfer.

        This peer answers well inside the socket timeout, so no single read
        fails; only the whole-transfer deadline ends the call.
        """
        client = bpa.BpaDtn7Client(self.server.server_port, timeout_seconds=2.0,
                                   max_bundle_bytes=4096, total_deadline_seconds=0.2)

        def unhurried():
            time.sleep(0.5)
            return self.fixed(200, b"opaque-bp-cbor")

        _Handler.routes["/download?dtn://bp-a/-slow"] = unhurried
        started = time.monotonic()
        with self.assertRaisesRegex(bpa.BpaDtn7Timeout, "total deadline"):
            client.download_bundle("dtn://bp-a/-slow")
        elapsed = time.monotonic() - started
        # It ended on its own deadline, before the 2 s per-read timeout.
        self.assertLess(elapsed, 2.0)

    def test_delete_completion_is_observed_from_inventory_absence(self):
        """D14: a lost delete reply is resolved, never assumed either way."""
        _Handler.routes["/status/bundles"] = self.fixed(200, b'["dtn://bp-a/-1"]')
        self.assertFalse(self.client.delete_completed("dtn://bp-a/-1"))
        self.assertTrue(self.client.delete_completed("dtn://bp-a/-2"))
        _Handler.routes["/status/bundles"] = self.fixed(200, b"[]")
        self.assertTrue(self.client.delete_completed("dtn://bp-a/-1"))

    def test_loopback_and_input_boundaries_are_enforced(self):
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            bpa.BpaDtn7Client(3000, host="127.0.0.1")
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            self.client.download_bundle("dtn://x/" + "a" * bpa.MAX_BID_BYTES)
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            bpa.BpaDtn7Client(3000, timeout_seconds=0)
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            bpa.BpaDtn7Client(3000, total_deadline_seconds=0)
        with self.assertRaises(bpa.BpaDtn7ProtocolError):
            bpa.BpaDtn7Client(3000, total_deadline_seconds=bpa.MAX_TOTAL_DEADLINE_SECONDS + 1)


if __name__ == "__main__":
    unittest.main()
