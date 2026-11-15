import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_fixed_rows_rewrite as rw
import event_archive_test_fixed_rows_rewrite as tests

ROOT=Path(__file__).resolve().parents[1]


class Rows(unittest.TestCase):
    def test_actual_five_boundary_checks_replay_idempotently(self):
        before=json.loads((ROOT/'tools/fixtures/event-archive-fixed-rows-before.json').read_text())
        count=0
        for name,old in before.items():
            count+=len(lr.match('(< 1 (fn2-run-loads-rows fn2-run-loads))',lr.parse(old).forms))
            after=rw.rewrite(old)
            self.assertEqual(after,(ROOT/'books'/name).read_text())
            self.assertEqual(after,rw.rewrite(after))
        self.assertEqual(count,5)

    def test_shared_provider_is_exact_peer_source_not_a_geometry_twin(self):
        provider=(ROOT/'tools/fixtures/event-archive-fixed-row-provider.lisp').read_text()
        actual=(ROOT/'books/machines-b.lisp').read_text()
        for n in lr.parse(provider).forms:
            name=n.items[1].low
            a=lr.match('(defun '+name+' ?*body)',lr.parse(actual).forms,deep=False)[0].node
            self.assertEqual(provider[n.start:n.end],actual[a.start:a.end])
        self.assertIn('(and (natp rows) (<= 2 rows))',provider)
        self.assertEqual(provider.count(':guard (fn2-b-fixed-cursor-rows-p rows)'),2)

    def test_exact_replay_tests_compose_the_same_later_transformation(self):
        before=json.loads((ROOT/'tools/fixtures/event-archive-fixed-row-tests-before.json').read_text())
        for name,old in before.items():
            after=tests.rewrite(old,name)
            self.assertEqual(after,(ROOT/'tools'/name).read_text())
            self.assertEqual(after,tests.rewrite(after,name))


if __name__=='__main__':unittest.main()
