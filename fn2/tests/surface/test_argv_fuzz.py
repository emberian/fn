"""Unit tests for the operator/store_ops argv fuzzer: the unmutated fakes agree, every plant is caught."""
import json
import tempfile
import unittest
from pathlib import Path

from fn2.tests.surface import argv_fuzz


def run(family, plant=None, seeds='0..19'):
    with tempfile.TemporaryDirectory() as directory:
        argv = ['--family', family, '--target', 'fake', '--seeds', seeds, '--out', directory]
        code = argv_fuzz.main(argv + (['--plant', plant] if plant else []))
        rows = [json.loads(l) for l in Path(directory, 'findings.jsonl').read_text().splitlines()]
        return code, rows, json.loads(Path(directory, 'summary.json').read_text())


class ArgvFuzzUnit(unittest.TestCase):
    def test_unmutated_fakes_agree_and_every_mutation_kind_runs(self):
        for family, kinds in (('operator', {'value', 'empty-token', 'non-ascii', 'unknown-verb', 'verb-alone', 'overlong'}),
                              ('store_ops', {'inspect', 'inspect-group', 'extra-argument', 'empty-token', 'non-ascii',
                                             'unknown-verb', 'overlong'})):
            code, rows, summary = run(family)
            self.assertEqual((code, rows), (0, []), family)
            self.assertLessEqual(kinds, set(summary['by_mutation']), family)

    def test_each_plant_is_caught(self):
        for family, plant, expect in (('operator', 'crash-on-overlong', 'killed by signal'),
                                      ('operator', 'fault-on-empty', 'fault on an argv mutation'),
                                      ('operator', 'accept-bad-capacity', 'capacity'),
                                      ('store_ops', 'crash-on-overlong', 'killed by signal'),
                                      ('store_ops', 'fault-on-empty', 'fault on an argv mutation'),
                                      ('store_ops', 'store-accept-extra', 'expected exit 5')):
            code, rows, _ = run(family, plant)
            self.assertEqual(code, 1, (family, plant))
            self.assertTrue(any(expect in r['problem'] for r in rows), (family, plant, rows[:2]))

    def test_universal_judgement(self):
        u = argv_fuzz.universal
        self.assertIsNone(u(dict(exit=5, text='usage operator request ARGV-MALFORMED\n'), 0.1, 5, tagged=True))
        self.assertIn('exit table', u(dict(exit=9, text=''), 0.1, 5, tagged=False))
        self.assertIn('backtrace', u(dict(exit=1, text='Backtrace for: main\nrefused operator x Y\n'), 0.1, 5, tagged=True))
        self.assertIn('took', u(dict(exit=1, text='refused operator x Y\n'), 9, 5, tagged=True))
        self.assertIn('tagged line word', u(dict(exit=1, text='accepted operator x\n'), 0.1, 5, tagged=True))
        self.assertIn('no tagged result line', u(dict(exit=1, text='nothing\n'), 0.1, 5, tagged=True))
        self.assertIsNone(u(dict(exit=1, text='nothing\n'), 0.1, 5, tagged=False))


if __name__ == '__main__':
    unittest.main()
