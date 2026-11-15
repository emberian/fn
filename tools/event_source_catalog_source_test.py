"""Actual source cone and retained-canonical routing controls (no ACL2 eval)."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
PATHS=['books/event-proof-source.lisp','books/event-read-source.lisp','books/event-read-verify.lisp','books/event-producer.lisp','books/event-build.lisp','tests/event-proof-source-unit.lisp','tests/event-read-verified-unit.lisp','tests/event-producer-unit.lisp','tests/event-build-unit.lisp']
def fn(p,name):return lr.match('(defun ?name ?*rest)',lr.parse((ROOT/p).read_text()).forms,name=name)[0].node
def need(n,p):
 if not lr.match(p,[n]):raise ValueError(p)
class Source(unittest.TestCase):
 def test_every_actual_child_call_has_complete_signature(self):
  defs={}
  for p in PATHS:
   for m in lr.match('(defun ?name ?args ?*rest)',lr.parse((ROOT/p).read_text()).forms):
    n=m.node;name=getattr(n.items[1],'low','')
    if name:defs[name]=len(n.items[2].items)
  for p in PATHS:
   for m in lr.match('(?head ?*args)',lr.parse((ROOT/p).read_text()).forms):
    n=m.node;h=getattr(n.items[0],'low','')
    if h in defs:self.assertEqual(len(n.items)-1,defs[h],(p,h))
 def test_archived_source_is_actual_canonical_catalog(self):
  n=fn('books/event-proof-source.lisp','fn2-event-source-lookup')
  need(n,'(<= batch (fn2-commit-root-base-batch 0 fn2-commit-root))')
  need(n,'(fn2-event-catalog-lookup batch ?*args)')
  need(n,'(fn2-commit-directory-lookup batch fn2-commit-root)')
  n=fn('books/event-proof-source.lisp','fn2-event-proof-pack-entry')
  need(n,'(fn2-event-catalog-held-p commit extent epoch allocation ?*args)')
  need(n,'(fn2-event-proof-entry-encode base slot gen off ?*args)')
  self.assertFalse(lr.match('(< commit (fn2-commit-root-rows fn2-commit-root))',[n]))
 def test_read_uses_same_physical_verifier_and_member_hasher(self):
  n=fn('books/event-read-source.lisp','fn2-event-read-issue')
  need(n,'(fn2-event-read-source-held-p ?*args)')
  need(n,'(fn2-block-read-children ?*args)')
  n=fn('books/event-read-verify.lisp','fn2-event-read-format-step')
  need(n,'(fn2-event-source-seal commit ?*args)')
  need(n,'(fn2-event-source-seal (- commit 1) ?*args)')
  need(n,'(fn2-event-read-format-core budget expected previous ?*args)')
  n=fn('books/event-read-verify.lisp','fn2-event-read-member-core')
  need(n,'(fn2-event-members-step ?*args)')
  n=fn('books/event-frontier.lisp','fn2-event-members-step')
  need(n,'(fn2-event-member-hash-step row leaf ?*args)')
 def test_genesis_predecessor_does_not_alias_positive_base(self):
  n=fn('books/event-read-verify.lisp','fn2-event-source-seal')
  need(n,'(and (eq code :genesis) (> (fn2-commit-root-base-batch 0 fn2-commit-root) 0))')
  need(n,'(fn2-event-source-load-seal 0 t 0 dst ?*args)')
 def test_seals_have_separate_named_digest_rows(self):
  n=fn('books/machines-b.lisp','fn2-b-event-expected-digest');need(n,'(+ 2 (fn2-b-event-leaf-digest ?*args))')
  n=fn('books/machines-b.lisp','fn2-b-event-previous-digest');need(n,'(+ 3 (fn2-b-event-leaf-digest ?*args))')
if __name__=='__main__':unittest.main()
