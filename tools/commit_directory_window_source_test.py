from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def fn(p,name):return lr.match('(defun ?name ?*rest)',lr.parse((ROOT/p).read_text()).forms,name=name)[0].node
def has(n,p):return bool(lr.match(p,[n]))
class Source(unittest.TestCase):
 def test_window_counts_actual_proposed_suffix(self):
  n=fn('books/machines-b.lisp','fn2-commit-directory-window-state-p')
  self.assertTrue(has(n,'(<= (- proposed base) (- (fn2-commit-root-rows fn2-commit-root) 1))'))
  self.assertTrue(has(n,'(or (= base 0) (= (fn2-commit-root-base-ready 0 fn2-commit-root) 1))'))
 def test_headroom_and_actual_commit_admission_share_window(self):
  n=fn('books/machines-b.lisp','fn2-commit-directory-headroom')
  self.assertTrue(has(n,'(fn2-commit-directory-window-state-p fn2-commit-root)'))
  n=fn('books/commit.lisp','fn2-commit-frontier')
  self.assertTrue(has(n,'(fn2-commit-directory-admission-limit fn2-commit-root)'))
 def test_absolute_position_exceeds_physical_rows_in_control(self):
  s=(ROOT/'tests/checkpoint-directory-headroom-unit.lisp').read_text()
  self.assertIn('(base-batch 120)',s);self.assertIn('(fn2-commit-root-init 4',s)
  self.assertIn('(assert-event (fn2-cdh-rebased))',s)
if __name__=='__main__':unittest.main()
