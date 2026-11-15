"""Structural foundation audit only, without evaluating ACL2 or a codec."""
from pathlib import Path
import subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'));import lisp_rewrite as r
BASE='f5f63a843';CURRENT='9c2eabc4c9b94de947c4705f8c7d684eeb61d136'
def source(rev,name):return subprocess.check_output(['git','show',rev+':books/'+name+'.lisp'],cwd=ROOT,text=True)
def walk(node):
 if isinstance(node,r.Lst):
  if len(node.items)>2 and getattr(node.items[0],'low',None)=='defun' and isinstance(node.items[1],r.Atom):yield node
  for child in node.items:yield from walk(child)
 elif isinstance(node,r.Pre):yield from walk(node.node)
def tree(node,drop_guard_hint=False):
 if isinstance(node,r.Lst):
  items=node.items
  if drop_guard_hint and items and getattr(items[0],'low',None)=='xargs':
   filtered=[];i=0
   while i<len(items):
    if getattr(items[i],'low',None)==':guard-hints':i+=2
    else:filtered.append(items[i]);i+=1
   items=filtered
  return tuple(tree(x,drop_guard_hint) for x in items)
 if isinstance(node,r.Pre):return (node.prefix,tree(node.node,drop_guard_hint))
 return ('string' if isinstance(node,r.Str) else 'atom',node.text)
def functions(text):return {node.items[1].low:node for form in r.parse(text).forms for node in walk(form)}
class CurrentFoundation(unittest.TestCase):
 def test_exact_current_shared_basis(self):
  for name in ['columns','operations','trace','layout','pool','blake3-pool-spec']:
   self.assertEqual((ROOT/'books'/f'{name}.lisp').read_text(),source(CURRENT,name),name)
 def test_runtime_and_guard_identity(self):
  for name in ['pool','layout']:
   old=functions(source(BASE,name));new=functions((ROOT/'books'/f'{name}.lisp').read_text())
   self.assertEqual(set(new)-set(old),{'fn2-pool-ignored-key-frame-events'} if name=='pool' else set())
   self.assertFalse(set(old)-set(new))
   for fn in old:
    if fn=='fn2-pool-op-conservation-events':continue # proof-event emitter only
    self.assertEqual(tree(old[fn],True),tree(new[fn],True),fn)
 def test_declarations_and_generator_runtime_forms(self):
  for name in ['pool','layout']:
   def declarations(text):
    return [tree(n) for n in r.parse(text).forms if isinstance(n,r.Lst) and n.items and getattr(n.items[0],'low',None) in ('defcolumns','deflayout','defconst')]
   self.assertEqual(declarations(source(BASE,name)),declarations((ROOT/'books'/f'{name}.lisp').read_text()),name)
  # The codec emitters are among the identical common definitions above;
  # this checks source structure, not executed macro-expansion equivalence.
 def test_blake_pool_runtime_and_theorem_claims_unchanged(self):
  old=source(BASE,'blake3-pool-spec');new=(ROOT/'books/blake3-pool-spec.lisp').read_text()
  self.assertEqual({name:tree(fn) for name,fn in functions(old).items()},
                   {name:tree(fn) for name,fn in functions(new).items()})
  def claims(text):
   return [tuple(tree(x) for x in node.items[:3]) for node in r.parse(text).forms
           if isinstance(node,r.Lst) and node.items and getattr(node.items[0],'low',None)=='defthm']
  self.assertEqual(claims(old),claims(new))
 def test_preserve_cold_and_avoid_behavior_parent_import(self):
  for name in ['alloc','arms','event-read-state','event-read-source','event-read-verify','pool-digest']:
   self.assertEqual((ROOT/'books'/f'{name}.lisp').read_text(),source(BASE,name),name)
if __name__=='__main__':unittest.main()
