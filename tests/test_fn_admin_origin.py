"""Actual startup hands explicit names to ACL2 without interpreting them."""
import argparse
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import fn_admin as admin

class OriginStartup(unittest.TestCase):
    def test_actual_init_and_serve_preserve_configured_text(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            (root/'tools').mkdir()
            (root/'tools/image-node.lsp').write_text('; mocked startup\n')
            args=argparse.Namespace(image=root/'node.img', size_mb=None, size=1048576,
                group=[], storage_fault_model=None, port='0', host=None,
                tls_certificate=None, tls_key=None, tls_handshakes=None,
                peer_pull_ca_file=None, peer_pull_tls_name=None,
                max_consumer_request_octets=None, max_consumer_discard_octets=None, consumer_body_timeout_ms=None,
                tls_window=None, tls_handshake_turns=None, tls_handshake_ms=None,
                peering=False, control_sock=None,
                origin_lineage='00017', origin_domain=None,
                origin_incarnation='bad-number', history_id='101', history_incarnation='7')
            with mock.patch.dict(os.environ, {'FN2_ORIGIN_DOMAIN':'23'}, clear=True), \
                 mock.patch.object(admin,'prepare_native_crypto'), \
                 mock.patch.object(admin,'prepare_native_tls'), \
                 mock.patch.object(admin.subprocess,'call',return_value=1) as start:
                self.assertEqual(admin.cmd_init(args,root),1)
                initial=start.call_args.kwargs['env']
            args.image.touch()
            with mock.patch.dict(os.environ, {'FN2_ORIGIN_DOMAIN':'23'}, clear=True), \
                 mock.patch.object(admin,'prepare_native_crypto'), \
                 mock.patch.object(admin,'prepare_native_tls'), \
                 mock.patch.object(admin.os,'chdir'),mock.patch.object(admin.os,'dup2'), \
                 mock.patch.object(admin.os,'execve') as start:
                admin.cmd_serve(args,root)
                restarted=start.call_args.args[2]
            expected={'FN2_ORIGIN_LINEAGE':'00017','FN2_ORIGIN_DOMAIN':'23',
                      'FN2_ORIGIN_INCARNATION':'bad-number','FN2_HISTORY_ID':'101',
                      'FN2_HISTORY_INCARNATION':'7'}
            for key,value in expected.items():
                self.assertEqual(initial[key],value)
                self.assertEqual(restarted[key],value)
            self.assertEqual(initial['FN2_IMAGE_MODE'],'init')
            self.assertEqual(restarted['FN2_IMAGE_MODE'],'serve')

if __name__=='__main__': unittest.main()
