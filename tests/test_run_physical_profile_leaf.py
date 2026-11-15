"""Two-function source extraction identity and narrow-leaf dependency controls.
No ACL2 evaluation or guard/certification claim. AST digests freeze the actual
469269743 resource definitions before the move; they are not runtime hashes.
"""
import copy
import hashlib
import json
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
FROZEN={
 'fn2-run-load-checker-init':'684b0e02494827db506b3f51303cf6e49455cf966d480211a6acc1e614c109bb',
 'fn2-run-load-profile-init':'a7f4e30e59a8fc150dccd53eb761fb2ab8ff0ee072dcc12ebfd84baef1a312aa'}
def trees(path):return [read_sexp(t) for t in forms((ROOT/path).read_text())]
def walk(x):
 if isinstance(x,list):
  yield x
  for y in x:yield from walk(y)
def definitions(path):return {t[1]:t for t in trees(path) if isinstance(t,list) and t and t[0]=='defun'}
def digest(node):return hashlib.sha256(json.dumps(node,separators=(',',':')).encode()).hexdigest()
class RunPhysicalProfileLeaf(unittest.TestCase):
 def test_exact_two_existing_definition_asts_moved(self):
  profile=definitions('books/run-physical-profile.lisp')
  self.assertEqual(set(profile),set(FROZEN))
  for name,sha in FROZEN.items():self.assertEqual(digest(profile[name]),sha)
  changed=copy.deepcopy(profile['fn2-run-load-profile-init']);changed[-1]=['caller-selected-init']
  self.assertNotEqual(digest(changed),FROZEN['fn2-run-load-profile-init'])
 def test_resource_leaf_has_no_undefined_profile_helper_calls(self):
  resources=trees('books/run-physical-resources.lisp')
  used={n[0] for t in resources for n in walk(t) if n and isinstance(n[0],str)}
  self.assertFalse(set(FROZEN)&used)
  self.assertFalse(set(FROZEN)&set(definitions('books/run-physical-resources.lisp')))
  self.assertFalse({n for n in used if n.startswith('fn2-b-')},used)
  self.assertIn('(include-book "machines-b")',list(forms((ROOT/'books/run-physical-resources.lisp').read_text())))
  self.assertIn('fn2-run-load-reserve',definitions('books/run-physical-resources.lisp'))
  self.assertIn('fn2-run-load-roomp',definitions('books/run-physical-resources.lisp'))
 def test_full_provider_includes_profile_before_actual_child_initialization(self):
  provider=trees('books/machines-c.lisp')
  include=list(forms((ROOT/'books/machines-c.lisp').read_text())).index('(include-book "run-physical-profile")')
  inits=[i for i,t in enumerate(provider) if any(n and n[0]=='fn2-run-load-profile-init' for n in walk(t))]
  self.assertEqual(len(inits),1)
  self.assertLess(include,inits[0])
  profile=trees('books/run-physical-profile.lisp')
  includes=[t for t in forms((ROOT/'books/run-physical-profile.lisp').read_text()) if t.startswith('(include-book ')]
  self.assertEqual(includes,['(include-book "run-physical-resources")'])
if __name__=='__main__':unittest.main()
