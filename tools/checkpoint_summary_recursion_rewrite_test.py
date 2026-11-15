"""Source controls for the fixed checkpoint-summary recursion repair.

These tests inspect Lisp source only; they do not claim ACL2 admission.
"""

import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import checkpoint_summary_recursion_rewrite as rw
import lisp_rewrite as lr


ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / 'tools/fixtures/checkpoint-summary-recursion-before.json'


def definition(source, name):
    found = lr.match('(defun ?name ?args ?*body)', lr.parse(source).forms,
                     deep=False, name=name)
    if len(found) != 1:
        raise AssertionError(f'{name}: expected one definition')
    node = found[0].node
    return source[node.start:node.end]


def measure(bound, index):
    return max(0, bound - max(0, index))


class RecursionSourceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(FIXTURE.read_text())

    def test_fixed_original_fixture_matches_all_nine_actual_definitions(self):
        expected = {(file, name, bound)
                    for file, targets in rw.TARGETS.items()
                    for name, bound in targets.items()}
        observed = {(item['file'], item['name'], item['bound'])
                    for item in self.fixture}
        self.assertEqual(len(self.fixture), 9)
        self.assertEqual(observed, expected)
        for item in self.fixture:
            before = item['before']
            name = item['name']
            bound = item['bound']
            self.assertEqual(definition(before, name), before)
            after, count = rw.rewrite(before, {name: bound})
            self.assertEqual(count, 1, name)
            self.assertEqual(rw.rewrite(after, {name: bound}), (after, 0))
            actual = definition((ROOT / item['file']).read_text(), name)
            if name=='fn2-checkpoint-summary-authority-live-descriptor':
                # Independent546 guard repair: the original fixed fixture
                # had an unbound SUMMARY guard although this helper's only
                # carriers are authority+bytes. Preserve the original input
                # and compose that explicit translation repair here.
                formal=lr.parse(after).forms[0].items[2]
                self.assertNotIn('fn2-checkpoint-summary',[x.low for x in formal.items])
                self.assertIn('(fn2-checkpoint-summary-wfp fn2-checkpoint-summary)',after)
                after=after.replace(' (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)','')
            self.assertEqual(actual, after, name)

    def test_whole_file_rewrite_has_no_other_changes(self):
        for file, targets in rw.TARGETS.items():
            actual = (ROOT / file).read_text()
            rewritten, count = rw.rewrite(actual, targets)
            self.assertEqual(count, 0, file)
            self.assertEqual(rewritten, actual, file)

    def test_negative_index_decreases_measure_and_natural_index_is_identical(self):
        for bound in (8, 32):
            for i in (-1000, -33, -2, -1):
                self.assertLess(measure(bound, 1 + max(0, i)),
                                measure(bound, i))
            for i in range(bound):
                self.assertEqual(1 + max(0, i), 1 + i)
                self.assertLess(measure(bound, 1 + max(0, i)),
                                measure(bound, i))
            for i in (bound, bound + 1):
                self.assertEqual(measure(bound, i), 0)

    def test_rejects_broken_measure_base_and_recursive_call(self):
        first = self.fixture[0]
        before = first['before']
        name = first['name']
        bound = first['bound']
        defects = (
            (f':measure (nfix (- {bound} (nfix i)))',
             f':measure (nfix (- {bound} i))'),
            (f'(>= (nfix i) {bound})', f'(>= i {bound})'),
            (f'({name} r (+ 1 i)', f'({name} r (+ 2 i)'),
        )
        for old, new in defects:
            self.assertEqual(before.count(old), 1)
            with self.assertRaises(ValueError):
                rw.rewrite(before.replace(old, new, 1), {name: bound})


if __name__ == '__main__':
    unittest.main()
