"""Reader-pool hazard controls for host/device.lisp.

Each control runs tests/native-device-concurrent-reads.lsp in its own SBCL on
a fresh temporary image. Each mutant run weakens exactly one rule in that
process; its control must refuse it.
"""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
DRIVER = 'tests/native-device-concurrent-reads.lsp'


def run(scenario, mutant=None):
    with tempfile.TemporaryDirectory(prefix='fn2-device-reads-') as tmp:
        env = dict(os.environ)
        env.pop('FN2_DEVICE_MUTANT', None)
        env['FN2_DEVICE_IMAGE'] = str(Path(tmp) / 'device.img')
        env['FN2_DEVICE_SCENARIO'] = scenario
        if mutant:
            env['FN2_DEVICE_MUTANT'] = mutant
        return subprocess.run(['sbcl', '--script', DRIVER], cwd=ROOT, env=env,
                              text=True, capture_output=True, timeout=60)


class DeviceConcurrentReadTests(unittest.TestCase):
    def assert_pass(self, scenario):
        result = run(scenario)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn(f'PASS {scenario} ', result.stdout)

    def test_reads_bypass_an_inflight_fence(self):
        self.assert_pass('fence-bypass')

    def test_read_waits_for_an_earlier_write(self):
        self.assert_pass('raw')

    def test_write_waits_for_an_earlier_read(self):
        self.assert_pass('war')

    def test_stop_joins_every_worker_then_closes_once(self):
        self.assert_pass('stop')

    def test_each_control_refuses_its_mutant(self):
        for scenario, mutant, diagnostic in (
                ('fence-bypass', 'fence-gate', 'Reads waited for the Fence'),
                ('raw', 'no-raw', 'the Read returned before the Write it follows'),
                ('war', 'no-war', 'the Write overtook an earlier Read'),
                ('stop', 'close-first', 'the fd was closed under an in-flight pread')):
            with self.subTest(mutant=mutant):
                result = run(scenario, mutant)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(f'FAIL {scenario}: {diagnostic}', result.stdout,
                              result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
