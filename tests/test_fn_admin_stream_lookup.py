"""Stream identity comes from a served reply, never local sidecar numbering."""
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch, MagicMock
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import fn_admin as a

class StreamLookup(unittest.TestCase):
    def session(self, result):
        sess = MagicMock()
        sess.__enter__.return_value = sess
        sess.auth.return_value = result
        return sess

    def test_served_identity_overrides_stale_sidecar(self):
        with tempfile.TemporaryDirectory() as d:
            sock = str(Path(d) / 'ctl')
            Path(sock + '.groups').write_text('1\tops.audit\n')
            sess = self.session({'outcome': 'accepted', 'target': 71})
            with patch.object(a, 'ControlSession', return_value=sess):
                self.assertEqual(a.resolve_stream_id('ops.audit', sock), (71, None))
            sess.auth.assert_called_once_with('stream-resolve', name='ops.audit')

    def test_refusal_and_transport_never_default_local_test(self):
        result = {'outcome': 'refused', 'reason': 'unknown-stream'}
        sess = self.session(result)
        with patch.object(a, 'ControlSession', return_value=sess):
            self.assertEqual(a.resolve_stream_id('local.test', '/missing'), (0, result))
            sess.auth.side_effect = a.WireError('closed')
            with self.assertRaises(a.WireError):
                a.resolve_stream_id('local.test', '/missing')

    def test_numeric_target_needs_no_identity_lookup(self):
        with patch.object(a, 'ControlSession', side_effect=AssertionError('unexpected query')):
            self.assertEqual(a.resolve_stream_id('71', '/missing'), (71, None))

    def test_codec_exact_result_and_long_name(self):
        name = 'x' * 250
        kind, body = a.fnct_open(a.build_auth_request('stream-resolve', name=name))
        self.assertEqual((kind, body), (29, b'\x04' + a.octets16(name.encode())))
        for result in [b'', a.leb_encode(71) + b'\x00']:
            with self.assertRaises(a.WireError):
                a.decode_auth_reply('stream-resolve', a.fnct_seal(30, b'\x04\x00\x00\x00' + result))
        self.assertEqual(a.decode_auth_reply('stream-resolve', a.fnct_seal(30, b'\x04\x00\x00\x00' + a.leb_encode(71)))['target'], 71)

if __name__ == '__main__': unittest.main()
