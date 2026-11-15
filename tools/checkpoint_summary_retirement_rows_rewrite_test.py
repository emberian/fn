"""Fixed-original shared retirement and exact active0 delegation controls."""
from pathlib import Path
import json,unittest
import lisp_rewrite as lr
import checkpoint_summary_retirement_rows_rewrite as rw
R=Path(__file__).resolve().parents[1]
class Rows(unittest.TestCase):
 def test_fixed_original_class(self):
  for file,old in json.loads((R/'tools/fixtures/checkpoint-summary-retirement-rows-before.json').read_text()).items():
   self.assertEqual((R/file).read_text(),rw.rewrite(old,rw.TARGETS[file]))
 def test_active_wrappers_call_shared_row0_once(self):
  for file,targets in rw.TARGETS.items():
   forms=lr.parse(R/file).forms
   for old,new in targets.items():
    n=lr.match(f'(defun {old} ?*body)',forms)[0].node
    self.assertEqual(len(n.items[-1].items),len(n.items[2].items)+2)
    self.assertEqual(n.items[-1].items[0].low,new);self.assertEqual(n.items[-1].items[1].low,'0')
 def test_shared_exact_promise_and_source(self):
  forms=lr.parse(R/'books/checkpoint-summary-retire.lisp').forms
  n=lr.match('(defun fn2-checkpoint-summary-row-retire-row ?*body)',forms)[0].node
  for p in ['(fn2-checkpoint-cbase-row-promised-p s fn2-checkpoint-summary fn2-checkpoint-cbase-holds)','(fn2-checkpoint-summary-row-run-source-p s r fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-run-installed)','(= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-retired*)','(fn2-run-free-physical r fn2-run-installed)']:
   self.assertTrue(lr.match(p,[n]),p)
 def test_row_bound_and_no_cache_ownership(self):
  n=lr.match('(defun fn2-checkpoint-summary-row-retire-row ?*body)',lr.parse(R/'books/checkpoint-summary-retire.lisp').forms)[0].node
  self.assertTrue(lr.match('(< s 2)',[n]));self.assertTrue(lr.match('(< s (fn2-checkpoint-summary-rows fn2-checkpoint-summary))',[n]))
  self.assertFalse(lr.match('(fn2-pool-release ?*args)',[n]));self.assertFalse(lr.match('(fn2-run-cache-drop ?*args)',[n]))
if __name__=='__main__':unittest.main()
