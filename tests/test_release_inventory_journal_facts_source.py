"""Actual prefix terminal namespaces cross-bind pending inventory journals."""
from pathlib import Path
import copy
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk

def source(name):return (ROOT/'books'/(name+'.lisp')).read_text()
def form(name,book,kind='defun'):
    return next(read_sexp(f) for f in forms(source(book)) if read_sexp(f)[:2]==[kind,name])
def stamp_good(node):
    calls=list(walk(node))
    actual=['fn2-origin-physicalp',['fn2-event-read-journal-history','0','fn2-event-read'],['fn2-event-read-journal-incarnation','0','fn2-event-read']]
    stamps=[n for n in calls if n[:2]==['fn2-checkpoint-restore-events-work-put','e'] and ['consumed','1'] in n]
    if actual not in calls or len(stamps)!=1:return False
    return (['journal-history',['fn2-event-read-journal-history','0','fn2-event-read']] in stamps[0]
            and ['journal-incarnation',['fn2-event-read-journal-incarnation','0','fn2-event-read']] in stamps[0])
def crossjoins(node):
    return [n for n in walk(node) if n and n[0]=='fn2-checkpoint-restore-events-journal-tuple-p']
class JournalFacts(unittest.TestCase):
    def test_only_verified_terminal_stamps_actual_pair(self):
        node=form('fn2-checkpoint-restore-events-journal-step','checkpoint-restore-events')
        self.assertTrue(stamp_good(node))
        for column in ('journal-history','journal-incarnation'):
            bad=copy.deepcopy(node)
            for n in walk(bad):
                if n and n[0]==column and len(n)==2:n[1]='0'
            self.assertFalse(stamp_good(bad))
        raw=source('checkpoint-restore-events')
        at=raw.index('(defun fn2-checkpoint-restore-events-journal-step')
        end=raw.index('(defun fn2-checkpoint-restore-events-frontier-begin',at)
        part=raw[at:end]
        self.assertLess(part.index('(fn2-event-read-member-core'),part.index('((unless good)'))
        self.assertLess(part.index('((unless good)'),part.index('(journal-history (fn2-event-read-journal-history'))
    def test_private_tuple_checks_identity_range_consumption_and_lower_stripe(self):
        node=form('fn2-checkpoint-restore-events-journal-tuple-p','checkpoint-restore-events-source')
        calls=list(walk(node))
        expected=[['=',['fn2-checkpoint-restore-events-work-'+column,'e','fn2-checkpoint-restore-events-work'],value]
                  for column,value in [('generation','generation'),('consumed','1'),('extent','e'),('commit','commit'),('epoch','epoch'),('allocation','allocation'),('journal-history','history'),('journal-incarnation','incarnation')]]
        for premise in expected:self.assertIn(premise,calls)
        self.assertIn(['<','e',['fn2-checkpoint-restore-events-work-capacity','fn2-checkpoint-restore-events-work']],calls)
        self.assertIn(['<=','first','event'],calls);self.assertIn(['<','event',['+','first','members']],calls)
        self.assertNotIn('fn2-checkpoint-restore-events-work-put',str(node))
    def test_both_namespaces_join_before_source_record_store(self):
        node=form('fn2-checkpoint-restore-release-inventory-entry','checkpoint-restore-release-inventory-reader','fn2-checkpoint-release-reader-operation')
        self.assertEqual(node[2],[])
        self.assertEqual(node[3][-1],'fn2-checkpoint-restore-events-work')
        self.assertNotIn('fn2-checkpoint-restore-events-work',node[4])
        joins=crossjoins(node);self.assertEqual(len(joins),2)
        self.assertEqual(joins[0][1:7],['journal','generation','commit','event','jepoch','jallocation'])
        self.assertEqual(joins[1][1:3],['installation','generation'])
        self.assertIn('*fn2-release-inventory-entry-field-installation-history*',str(joins[1]))
        self.assertIn('*fn2-release-inventory-entry-field-journal-history*',str(joins[0]))
        raw=source('checkpoint-restore-release-inventory-reader');a=raw.index('fn2-checkpoint-restore-events-journal-tuple-p journal')
        self.assertLess(a,raw.index('(fn2-checkpoint-release-store-entry base journal'))
        self.assertIn("(generation (fn2-checkpoint-restore-release-inventory-generation 0 fn2-checkpoint-restore-release-inventory))",raw)
        bad=copy.deepcopy(node)
        for n in walk(bad):
            if n and n[0]=='fn2-checkpoint-restore-events-journal-tuple-p' and n[1]=='installation':n[0]='equal'
        self.assertEqual(len(crossjoins(bad)),1)
    def test_namespace_columns_are_typed_and_refusal_fixture_tracks_new_readonly_source(self):
        state=form('fn2-checkpoint-restore-events-work','checkpoint-restore-events-state','defcolumns')
        self.assertIn(['journal-history',':u60'],state[2]);self.assertIn(['journal-incarnation',':u60'],state[2])
        raw=(ROOT/'tests/checkpoint-release-inventory-reader-refusal-unit.lisp').read_text()
        self.assertIn('fn2-checkpoint-restore-events-work',raw)
        unit=(ROOT/'tests/checkpoint-event-journal-fact-unit.lisp').read_text()
        for marker in ('typed','exact','bounds','refused','frame','unconsumed','upper','wrong-index','first-event'):
            self.assertIn(marker,unit)
        self.assertNotIn('set-phase',unit)
if __name__=='__main__':unittest.main()
