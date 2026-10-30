"""Unit tests for the fn.toml fuzzer: the independent fake agrees on every mutation, every plant is caught."""
import json
import tempfile
import unittest
from pathlib import Path

from fn2.tests.surface import config_fuzz


def run(plant=None, seeds='0..999'):
    with tempfile.TemporaryDirectory() as directory:
        code = config_fuzz.main(['--target', 'fake', '--seeds', seeds, '--out', directory] +
                                (['--plant', plant] if plant else []))
        return code, json.loads(Path(directory, 'summary.json').read_text())


class ConfigFuzzUnit(unittest.TestCase):
    def test_unmutated_fake_agrees_on_every_mutation(self):
        code, summary = run()
        self.assertEqual((code, summary['findings']), (0, 0))
        self.assertEqual(set(summary['by_mutation']), set(config_fuzz.ACCEPTED + config_fuzz.REFUSED))

    def test_each_plant_is_caught(self):
        for plant in config_fuzz.PLANTS:
            code, summary = run(plant, '0..499')
            self.assertEqual(code, 1, plant)
            self.assertGreater(summary['findings'], 0, plant)

    def test_cases_are_deterministic_and_sized(self):
        import random
        for seed in range(300):
            kind, expected, octets = config_fuzz.case(random.Random(seed))
            self.assertEqual(config_fuzz.case(random.Random(seed)), (kind, expected, octets))
            if kind == 'octets-16385':
                self.assertGreater(len(octets), 16384)
                self.assertLessEqual(octets.count(b'\n'), 128)
            if kind == 'lines-129':
                self.assertGreater(octets.count(b'\n'), 128)
                self.assertLess(len(octets), 16384)

    def test_judge(self):
        j = config_fuzz.judge
        self.assertIsNone(j('accepted', dict(exit=0, text='store path ...\n')))
        self.assertIsNone(j('refused', dict(exit=5, text='usage operator show (CONFIGURATION INVALID)\n')))
        self.assertIsNone(j('refused', dict(exit=5, text='fn-host: error: operator configuration file exceeds ACL2 bound\n')))
        self.assertIn('exit 4', j('refused', dict(exit=4, text='store: store file exceeds bound\n')))
        self.assertIn('expected refused', j('refused', dict(exit=0, text='')))
        self.assertIn('backtrace', j('refused', dict(exit=5, text='Backtrace for: x\nusage operator show X\n')))


if __name__ == '__main__':
    unittest.main()
