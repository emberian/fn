"""Actual native custody/caller bodies with recording core callbacks.

This establishes adapter retention/ordering, not installed runtime funding,
ACL2 composition, genuine issuer activation or native-image qualification.
"""
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.test_native_receiver_failure_boundary import ROOT, proof_repl

SELECTED = {
    'host/native/io.lisp': ['fnn-store-error', 'fnn-store-fault',
        'fnn-store-indeterminate', 'fnn-os-error', 'fnn-refuse', 'fnn-fault', 'fnn-core-mv'],
    'host/native/owner.lisp': ['fnn-owner-connection-selected-p',
        'fnn-connection-custody-make', 'fnn-connection-custody-publish-raw',
        'fnn-connection-custody-retain', 'fnn-connection-custody-released',
        'fnn-owner-connection-open-locked', 'fnn-owner-connection-close-locked',
        'fnn-owner-connection-settle-locked', 'fnn-owner-connection-repin-joined-locked',
        'fnn-owner-shared-action-locked', 'fnn-owner-serialized', 'fnn-owner-transit-serialized'],
    'host/native/mux.lisp': ['fnn-mux-service', 'fnn-mux-admit', 'fnn-mux-finish', 'fnn-mux-guarded'],
    'host/native/web-host.lisp': ['fnn-web-open', 'fnn-web-close', 'fnn-web-request'],
    'host/native/pull-service.lisp': ['fnn-pull-local-open', 'fnn-pull-round'],
    'host/native/admin.lisp': ['fnn-owner-live-reconfigure-locked'],
}
STRUCTS = {'fnn-owner-service', 'fnn-connection-custody', 'fnn-mux-conn', 'fnn-mux-loop'}


def selected_source(tree):
    bodies, hashes = [], {}
    for path, names in SELECTED.items():
        forms = proof_repl.forms((tree / path).read_text())
        by_name = {proof_repl.head_and_name(f)[1]: f for f in forms}
        for f in forms:
            if any(f.startswith('(defstruct (' + name + ' ') for name in STRUCTS):
                bodies.append(f)
                hashes[f.split()[1][1:]] = hashlib.sha256(f.encode()).hexdigest()
        for name in names:
            body = by_name[name]
            bodies.append(body)
            hashes[name] = hashlib.sha256(body.encode()).hexdigest()
    return '\n\n'.join(bodies) + '\n', hashes


class NativeConnectionCustodyTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_actual_native_custody_and_endpoint_callers(self):
        source, hashes = selected_source(ROOT)
        fixture = (ROOT / 'tests/fixtures/native_connection_custody.lisp').read_text()
        with tempfile.TemporaryDirectory() as temp:
            p = Path(temp)
            (p / 'source.lisp').write_text(source)
            (p / 'driver.lisp').write_text(fixture.replace('__SOURCE_FILE__', json.dumps(str(p / 'source.lisp'))))
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                  '--script', str(p / 'driver.lisp')],
                                 capture_output=True, text=True, timeout=30)
        after, after_hashes = selected_source(ROOT)
        self.assertEqual(source, after, 'source changed during evaluation')
        if destination := os.environ.get('FN_CONNECTION_CUSTODY_EVIDENCE'):
            p = Path(destination)
            p.mkdir(parents=True, exist_ok=True)
            (p / 'selected-source.lisp').write_text(source)
            (p / 'run.log').write_text(run.stdout + run.stderr)
            (p / 'coordinate.json').write_text(json.dumps({
                'hashes_before': hashes, 'hashes_after': after_hashes,
                'fixture_sha256': hashlib.sha256(fixture.encode()).hexdigest(),
                'returncode': run.returncode,
                'scope': 'native adapter source, real SBCL mutexes, recording callbacks; no runtime funding or activation claim',
            }, indent=2) + '\n')
        self.assertEqual(0, run.returncode, run.stdout + run.stderr)
        self.assertNotRegex(run.stderr, r'caught\s+(?:[0-9]+\s+)?ERROR')
        self.assertIn('PASS native connection custody', run.stdout)

    def test_all_endpoint_sources_transport_direct_nodes(self):
        expected = {
            'mux.lisp': ['fnn-mux-conn-custody', 'fnn-owner-connection-open-locked', 'fnn-owner-connection-close-locked'],
            'web-host.lisp': ['(values opened custody)', '(fnn-web-close service cid custody)'],
            'pull-service.lisp': ['(setq cid opened custody node)', 'service old custody nil', 'service cid custody nil'],
            'admin.lisp': ['service :reader nil nil nil', 'service cid custody nil'],
        }
        for file, fragments in expected.items():
            source = (ROOT / 'host/native' / file).read_text()
            proof_repl.forms(source)
            for fragment in fragments:
                self.assertIn(fragment, source)


if __name__ == '__main__':
    unittest.main()
