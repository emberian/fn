"""Unit tests for the fncu (consumer) and BPv7 (bp) fuzzers: the independent fakes agree, every plant is caught."""
import json
import tempfile
import unittest
from pathlib import Path

from fn2.tests.surface import bp_fuzz, fncu_fuzz


def run(module, plant=None, seeds='0..999'):
    with tempfile.TemporaryDirectory() as directory:
        code = module.main(['--target', 'fake', '--seeds', seeds, '--out', directory] +
                           (['--plant', plant] if plant else []))
        return code, json.loads(Path(directory, 'summary.json').read_text())


class CodecFuzzUnit(unittest.TestCase):
    def test_unmutated_fakes_agree_on_every_case(self):
        for module, cases in ((fncu_fuzz, fncu_fuzz.CASES), (bp_fuzz, bp_fuzz.CASES)):
            code, summary = run(module)
            self.assertEqual((code, summary['findings']), (0, 0), module.__name__)
            self.assertEqual(set(summary['by_mutation']), set(cases), module.__name__)

    def test_each_plant_is_caught(self):
        for module in (fncu_fuzz, bp_fuzz):
            for plant in module.PLANTS:
                code, summary = run(module, plant, '0..299')
                self.assertEqual(code, 1, (module.__name__, plant))

    def test_fncu_encoding_bounds(self):
        import random
        for seed in range(500):
            kind, expected, data = fncu_fuzz.case(random.Random(seed))
            if kind == 'none':
                self.assertLessEqual(len(data), fncu_fuzz.MAX)
                self.assertGreater(expected['registration-epoch'], 0)
            if kind == 'overbound':
                self.assertGreater(len(data), fncu_fuzz.MAX)

    def test_bp_golden_payloads_and_age_block(self):
        for name, (file, _, _, payload) in bp_fuzz.BUNDLES.items():
            data = (bp_fuzz.GOLDEN / file).read_bytes()
            self.assertIn(payload, data, name)
            self.assertEqual(bp_fuzz.fake_decode(data, bp_fuzz.BUNDLES[name][2] + 100)[0], 'accepted', name)
        self.assertIn(bp_fuzz.AGE_BLOCK_HEAD, (bp_fuzz.GOLDEN / bp_fuzz.BUNDLES['fn'][0]).read_bytes())


if __name__ == '__main__':
    unittest.main()
