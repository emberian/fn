from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_summary_entry_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def fn(src,name):return lr.match(f'(defun {name} ?*body)',lr.parse(src).forms,deep=False)[0].node
def norm(n):return n.low if hasattr(n,'low') else tuple(norm(x) for x in n.items)
class Entry(unittest.TestCase):
 def setUp(self):
  self.before=(ROOT/'tools/fixtures/checkpoint-summary-entry-before.lisp').read_text()
  self.cold=(ROOT/'books/checkpoint-summary-catalog.lisp').read_text();self.entry=(ROOT/'books/checkpoint-summary-entry.lisp').read_text()
 def test_actual_extraction_reproduces(self):
  cold,entry=rw.rewrite(self.before);self.assertEqual(cold,self.cold);self.assertEqual(entry,self.entry)
 def test_hash_reader_expression_unchanged(self):
  self.assertEqual(norm(fn(self.before,'fn2-checkpoint-summary-load-hash').items[-1]),norm(fn(self.entry,'fn2-checkpoint-summary-load-hash').items[-1]))
 def test_cold_still_authenticates_and_checks_actual_map(self):
  c=fn(self.cold,'fn2-checkpoint-summary-capture')
  self.assertEqual(len(lr.match('(fn2-checkpoint-restore-semantic-entry ?*args)',[c])),1)
  for p in ['(fn2-checkpoint-summary-current-p ?*args)',
            '(= (fn2-checkpoint-restore-map-present e fn2-checkpoint-restore-map) 1)',
            '(= (fn2-checkpoint-restore-map-epoch e fn2-checkpoint-restore-map) epoch)',
            '(fn2-checkpoint-summary-record-fields 0 eb ?*args)']:
   self.assertTrue(lr.match(p,[c]),p)
 def test_shared_entry_cannot_overwrite_other_held_catalog(self):
  f=fn(self.entry,'fn2-checkpoint-summary-record-fields')
  gate=lr.match('(mv :held-source fn2-checkpoint-summary fn2-checkpoint-summary-sources)',[f])[0]
  write=lr.match('(fn2-checkpoint-summary-load-hash ?*args)',[f])[0]
  self.assertLess(gate.start,write.start)
  self.assertTrue(lr.match('(= (fn2-checkpoint-summary-sources-tag e fn2-checkpoint-summary-sources) (fn2-checkpoint-summary-tag other fn2-checkpoint-summary))',[f]))
  self.assertFalse('fn2-checkpoint-restore-map' in self.entry)
 def test_source_row_effects_unchanged(self):
  old=fn(self.before,'fn2-checkpoint-summary-capture');new=fn(self.entry,'fn2-checkpoint-summary-record-fields')
  for pattern in ['(fn2-checkpoint-summary-sources-put ?*args)']:
   self.assertEqual([norm(m.node) for m in lr.match(pattern,[old])],[norm(m.node) for m in lr.match(pattern,[new])])
  setcount=lr.match('(fn2-checkpoint-summary-set-count ?row rank fn2-checkpoint-summary)',[new])[0]
  self.assertEqual(setcount.captures['row'].low,'r')
if __name__=='__main__':unittest.main()
