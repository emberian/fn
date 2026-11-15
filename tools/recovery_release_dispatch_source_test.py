"""Source integration guards; actual recovery execution remains a separate gate."""
from pathlib import Path
import unittest
from lisp_rewrite import parse
ROOT=Path(__file__).resolve().parents[1]
class ReleaseDispatch(unittest.TestCase):
 def test_provider_before_materialization(self):
  s=(ROOT/'books/assembly-callbacks.lisp').read_text()
  self.assertLess(s.index('(include-book "recovery-release")'),s.index('(fn2-recovery-events-3)'))
 def test_release_keeps_authenticated_record(self):
  s=(ROOT/'books/recovery-payload.lisp').read_text()
  self.assertIn('((when (equal kind *record-kind-release-allocation*)) (mv :release roff 0 0 fn2-core))',s)
  self.assertIn('(equal kind *record-kind-release-allocation*) (not (equal event wevent))',s)
 def test_separate_read_stages(self):
  s=(ROOT/'books/recovery-machine.lisp').read_text()
  section=s[s.index('  (replay-release-begin'):s.index('  (replay-record')]
  for name in ('begin','issue','step'):self.assertIn('(fn2-recovery-release-'+name,section)
  self.assertIn('(pending (+ 1 row-pending)) (rc-stage 12)',section)
  self.assertNotIn('(rc-roff ',section)
  self.assertNotIn('(rc-filled ',section)
  self.assertNotIn('(:settled)',section)
 def test_completion_preserves_journal_window(self):
  s=(ROOT/'books/recovery-machine.lisp').read_text();s=s[s.index(' :observes'):]
  release=s[s.index('((and (equal row-rc-mode'):]
  for text in ('(equal row-rc-stage 12)','(equal outcome *fn2-outcome-done*)','(equal count 4096)','(fn2-recovery-release-read-state id row-generation)',':accept (:ready)','(rc-stage 13)'):self.assertIn(text,release)
  for text in ('(rc-filled ','(rc-count ','(rc-roff ','(pending '):self.assertNotIn(text,release)
 def test_parse(self):
  for name in ('recovery-machine','recovery-payload','assembly-callbacks'):self.assertTrue(parse((ROOT/('books/'+name+'.lisp')).read_text()).forms)
if __name__=='__main__':unittest.main()
