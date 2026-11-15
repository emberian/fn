"""Actual three-edge mutation is shared; unbound catalogs never drop holders."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import release_evidence_common_rewrite as rw
def function(source,name):
    found=lr.match(f'(defun {name} ?*body)',lr.parse(source).forms,deep=False)
    if len(found)!=1:raise ValueError(name)
    return found[0].node
def calls(node,name):
    return [lr.emit(m.node) for m in lr.match(f'({name} ?*args)',[node])]
class Common(unittest.TestCase):
    def test_one_original_mutation_tail(self):
        before=(ROOT/'tools/fixtures/release-evidence-live-before.lisp').read_text()
        source=(ROOT/'books/release-evidence.lisp').read_text()
        old=function(before,'fn2-release-evidence-claim-children')
        shared=function(source,'fn2-release-evidence-claim-transition')
        expected=calls(old,'fn2-alloc-edge-add-transition')
        self.assertEqual(len(expected),3)
        self.assertEqual(expected,calls(shared,'fn2-alloc-edge-add-transition'))
        self.assertEqual(len(calls(function(source,'fn2-release-evidence-claim-children'),'fn2-release-evidence-claim-transition')),1)
        self.assertEqual(len(lr.match('(fn2-alloc-edge-add-transition ?*args)',lr.parse(source).forms)),3)
    def test_unbound_aggregate_is_explicit_but_physical_checks_mandatory(self):
        source=(ROOT/'books/release-evidence.lisp').read_text()
        shared=lr.emit(function(source,'fn2-release-evidence-claim-transition'))
        self.assertIn('(if (= bound 1)',shared)
        owned=function(source,'fn2-release-evidence-row-owned-p').items[-1].items[-1]
        self.assertEqual(owned.items[0].low,'and')
        mandatory=[n for n in owned.items[1:] if hasattr(n,'items') and n.items and getattr(n.items[0],'low','')=='fn2-alloc-edge-matchesp']
        self.assertEqual(len(mandatory),3)
        aggregate=lr.emit(function(source,'fn2-release-evidence-row-aggregate-p'))
        self.assertIn('(= c 0)',aggregate)
        self.assertNotIn('(defcost fn2-release-evidence-claim-transition',source)
    def test_extraction_refuses_changed_or_missing_admission(self):
        with self.assertRaises(ValueError):rw.extract('(unrelated)')
if __name__=='__main__':unittest.main()
