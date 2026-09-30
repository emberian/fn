"""Exercise actual custody helpers inside their required outer extent span.

Real mutexes/contending threads; core and scheduler remain recording fixtures.
Each single-helper regression restores only its original nonrecursive lock.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests.test_native_connection_custody import ROOT, selected_source, proof_repl


class ConnectionExclusionTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_continuous_exclusion_and_single_helper_regressions(self):
        tree = Path(os.environ.get('FN_CONNECTION_CUSTODY_SOURCE_TREE', ROOT))
        source, hashes = selected_source(tree)
        fixture = (ROOT / 'tests/fixtures/native_connection_custody.lisp').read_text()
        extra = (ROOT / 'tests/fixtures/native_connection_exclusion.lisp').read_text()
        evidence = os.environ.get('FN_CONNECTION_EXCLUSION_EVIDENCE')
        records = []
        runs = [(name, None) for name in ('open', 'close', 'settle', 'complete', 'fault')]
        runs += [(name, 'fnn-owner-connection-' + name + '-locked')
                 for name in ('open', 'close', 'settle')]
        for name, restored in runs:
            with self.subTest(case=name, restored=restored):
                current = source
                if restored:
                    form = next(f for f in proof_repl.forms(source)
                                if proof_repl.head_and_name(f)[1] == restored)
                    self.assertEqual(form.count('sb-thread:with-recursive-lock'), 1)
                    current = current.replace(form, form.replace(
                        'sb-thread:with-recursive-lock', 'sb-thread:with-mutex'), 1)
                with tempfile.TemporaryDirectory() as directory:
                    p = Path(directory)
                    (p / 'source.lisp').write_text(current)
                    driver = fixture.replace('__SOURCE_FILE__', json.dumps(str(p / 'source.lisp')))
                    driver += '\n' + extra.replace('__CASE__', ':' + name)
                    (p / 'driver.lisp').write_text(driver)
                    run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger',
                                          '--script', str(p / 'driver.lisp')],
                                         capture_output=True, text=True, timeout=30)
                record = {'case': name, 'restored': restored, 'returncode': run.returncode,
                          'evaluated_source_sha256': hashlib.sha256(current.encode()).hexdigest()}
                records.append(record)
                if evidence:
                    p = Path(evidence)
                    p.mkdir(parents=True, exist_ok=True)
                    suffix = '-restored' if restored else ''
                    (p / (name + suffix + '.log')).write_text(run.stdout + run.stderr)
                    (p / 'coordinate.json').write_text(json.dumps({
                        'source_tree': str(tree), 'selected_hashes': hashes,
                        'custody_fixture_sha256': hashlib.sha256(fixture.encode()).hexdigest(),
                        'exclusion_fixture_sha256': hashlib.sha256(extra.encode()).hexdigest(),
                        'runs': records,
                        'scope': 'Actual native helpers; real locks/threads; recording core/scheduler. '
                                 'No complete caller installation, funding or image qualification.',
                    }, indent=2) + '\n')
                if restored:
                    self.assertNotEqual(run.returncode, 0, run.stdout)
                    self.assertIn('Recursive lock attempt', run.stdout + run.stderr)
                else:
                    self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
                    self.assertIn('PASS continuous connection exclusion', run.stdout)
        self.assertEqual((source, hashes), selected_source(tree), 'source changed during test')


if __name__ == '__main__':
    unittest.main()
