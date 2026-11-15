#!/usr/bin/env python3
"""Pin current served source preservation and the intentional rolling ABI."""
from pathlib import Path
import subprocess,unittest,lisp_rewrite as lr
import cns_source_leaf_source_test as leaves
R=Path(__file__).resolve().parents[1]
BASE='8897f790e840651bbfc402ec31ee35a434f8109b'
class Join(unittest.TestCase):
 def test_current_foundation_and_nonrolling_served_books_unchanged(self):
  for name in ['books/upload-feed.lisp','books/blake3.lisp','books/ribbon.lisp',
               'books/exec-state.lisp','books/cns-source-raw.lisp','books/machines-c-read.lisp',
               'books/cns.lisp','books/ctl-output-events.lisp','books/ctl-stream-events.lisp','books/conn-kind.lisp',
               'books/machines-c-bind.lisp','books/machines-c-stage.lisp']:
   old=subprocess.check_output(['git','show',BASE+':'+name],cwd=R)
   if name == 'books/machines-c-read.lisp':
    # Validate only the exact reviewed additions, then compare every original
    # complete AST, including original theories and proof hints.
    actual=leaves.parsed(name)
    leaves.original_consumer_forms(name,actual)
    extra=['include-book','"pool-dimensions"']
    self.assertEqual(actual.count(extra),1)
    original=[leaves.converted(x) for x in leaves.ledger.read_forms(old.decode())]
    remaining=[x for x in actual if x!=extra and x not in leaves.READ_DIMENSIONS]
    self.assertEqual(remaining,original,name)
   else:self.assertEqual((R/name).read_bytes(),old,name)
 def test_counted_core_callback_and_public_compatibility_are_both_real(self):
  s=(R/'books/assembly-callbacks-d.lisp').read_text()
  node=lr.match('(defun fn2-upload-feed-pool ?*body)',lr.parse(s).forms)[0]
  body=s[node.start:node.end]
  self.assertIn('fn2-upload-feed-counted',body)
  self.assertIn('(mv status start2 mode2 discard2 copied lines fn2-core)',body)
  f=(R/'books/upload-feed.lisp').read_text()
  self.assertTrue(lr.match('(defun fn2-upload-feed-slice ?*body)',lr.parse(f).forms))
  self.assertIn('fn2-upload-feed-counted',f)
 def test_default_limit_and_actual_projection(self):
  s=(R/'books/upload-window-geometry.lisp').read_text()
  self.assertIn('*fn2-upload-body-window-bytes* *fn2-commit-unit-bytes*',s)
  p=(R/'books/article-limit-config.lisp').read_text()
  self.assertIn('fn2-input-config-profilep',p)
  a=(R/'books/upload-page-geometry.lisp').read_text()
  self.assertIn('(nfix article-max)',a)
if __name__=='__main__':unittest.main()
