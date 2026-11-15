#!/usr/bin/env python3
"""Source-only controls; actual ACL2 admission/termination remains unrun."""
from pathlib import Path
import json,unittest
import lisp_rewrite as lr
from rebase_fixed_recursion_rewrite import TARGETS,transform
ROOT=Path(__file__).resolve().parents[1]
class RebaseRecursion(unittest.TestCase):
 def test_all_five_actual_helpers_are_exact_recipe_outputs(self):
  fixtures=json.loads((ROOT/'tools/fixtures/rebase-fixed-recursion-before.json').read_text())
  self.assertEqual(len(fixtures),5)
  for item in fixtures:
   after,count=transform(item['before'],{item['name']:item['bound']})
   self.assertEqual(count,1)
   self.assertEqual(transform(after,{item['name']:item['bound']}),(after,0))
   s=(ROOT/item['file']).read_text();n=lr.match('(defun '+item['name']+' ?*body)',lr.parse(s).forms,deep=False)[0].node
   self.assertEqual(s[n.start:n.end],after)
 def test_whole_sources_are_idempotent_and_call_arity_preserved(self):
  for path,targets in TARGETS.items():
   s=(ROOT/path).read_text();self.assertEqual(transform(s,targets),(s,0))
   for name in targets:
    n=lr.match('(defun '+name+' ?*body)',lr.parse(s).forms,deep=False)[0].node
    call=lr.match('('+name+' ?*args)',[n.items[-1]])[0].node
    self.assertEqual(len(call.items)-1,len(n.items[2].items))
    index=[x.low for x in n.items[2].items].index('i')
    self.assertTrue(lr.match('(+ 1 (nfix i))',[call.items[index+1]],deep=False))
 def test_changed_bound_or_measure_is_refused(self):
  item=json.loads((ROOT/'tools/fixtures/rebase-fixed-recursion-before.json').read_text())[0]
  bad=item['before'].replace(':measure (nfix (- 520 (nfix i)))',':measure (nfix (- 519 (nfix i)))')
  with self.assertRaises(ValueError):transform(bad,{item['name']:item['bound']})
if __name__=='__main__':unittest.main()
