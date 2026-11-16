"""Source ABI/park composition controls, not actual world execution."""
from pathlib import Path
import hashlib,json,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from read_observer_provider_rewrite import DATA,event,project_release
ABI=json.loads((ROOT/'tools/fixtures/read-observer-provider-abi.json').read_text())
def norm(x):
 if isinstance(x,lr.Lst):return [norm(y) for y in x.items]
 if isinstance(x,lr.Pre):return [x.prefix,norm(x.node)]
 return getattr(x,'low',getattr(x,'text',''))
def b_source_current_or_prefix(actual,row):
 if hashlib.sha256(actual).hexdigest()==row['sha256']:return True
 from physical_b_loader_rewrite import project_loader_prefix
 frozen=json.loads((ROOT/'tools/fixtures/physical-b-loader-prefix-source.json').read_text())
 return (frozen['frozen-current-sha256']==row['sha256'] and
         hashlib.sha256(frozen['frozen-current'].encode()).hexdigest()==row['sha256'] and
         actual.decode()==project_loader_prefix(frozen['frozen-current']))
class ReadProvider(unittest.TestCase):
 def test_current_read_body_and_abi_are_unchanged(self):
  text=(ROOT/'books/machines-c-read.lisp').read_text()
  self.assertEqual(hashlib.sha256(text.encode()).hexdigest(),ABI['read-source-sha256'])
  f=event(text,'defun','fn2-read-observer-enter')
  self.assertEqual(norm(f.items[2]),ABI['scalars']+ABI['stobjs-in'])
  self.assertEqual(len(ABI['stobjs-in']),9)
  self.assertNotIn('fn2-run-installed',ABI['stobjs-in'])
  self.assertNotIn('fn2-read-observer-enter-children',text)
  self.assertIn('(include-book "run-physical-park-region")',text)
  for m in lr.match('(fn2-read-observer-enter ?*args)',lr.parse(text).forms,deep=True):self.assertEqual(len(m.captures['args']),11)
 def test_park_projection_and_guards(self):
  actual=(ROOT/'books/run-physical-release.lisp').read_text()
  self.assertEqual(project_release(DATA['release-before']),actual)
  self.assertEqual(project_release(actual),actual)
  old=DATA['release-before']
  for name in ('fn2-run-load-release','fn2-run-load-park-source','fn2-run-load-parkable-p'):
   a=event(old,'defun',name);b=event(actual,'defun',name)
   self.assertEqual(norm(a.items[2]),norm(b.items[2]))
   self.assertEqual(norm(a.items[3]),norm(b.items[3]))
 def test_actual_mutation_factor_is_same_tail(self):
  old=DATA['release-before'];a=event(old,'defun','fn2-run-load-park-source').items[-1]
  donor=DATA['release-donor'];macro=event(donor,'defmacro','fn2-run-load-park-source-mutations').items[-1].node
  # Original gate stays in function; SAME remaining B* bindings/result move.
  tail=['b*',norm(a.items[1])[1:]]+[norm(x) for x in a.items[2:]]
  self.assertEqual(tail,norm(macro))
 def test_canonical_region_and_static_dependency_graph(self):
  self.assertEqual((ROOT/'books/run-physical-park-region.lisp').read_text(),DATA['park-donor'])
  graph=json.loads((ROOT/'tools/fixtures/read-observer-provider-closure.json').read_text())
  self.assertEqual(graph['missing'],[]);self.assertGreater(len(graph['read-closure']),100)
  self.assertIn('books/run-physical-region',graph['read-closure']['books/run-physical-park-region']['includes'])
  self.assertIn('books/run-physical-release',graph['read-closure']['books/run-physical-region']['includes'])
  for book,row in graph['read-closure'].items():
   self.assertTrue((ROOT/(book+'.lisp')).exists(),book)
   actual=(ROOT/(book+'.lisp')).read_bytes()
   if book=='books/machines-b':self.assertTrue(b_source_current_or_prefix(actual,row))
   else:self.assertEqual(hashlib.sha256(actual).hexdigest(),row['sha256'],book)
 def test_frozen_b_accepts_only_exact_compositional_prefix(self):
  from physical_b_loader_rewrite import project_loader_prefix
  frozen=json.loads((ROOT/'tools/fixtures/physical-b-loader-prefix-source.json').read_text())
  graph=json.loads((ROOT/'tools/fixtures/read-observer-provider-closure.json').read_text());row=graph['read-closure']['books/machines-b']
  original=frozen['frozen-current'];projected=project_loader_prefix(original)
  self.assertTrue(b_source_current_or_prefix(original.encode(),row))
  self.assertTrue(b_source_current_or_prefix(projected.encode(),row))
  self.assertFalse(b_source_current_or_prefix(projected.replace('(nfix cursor)','(nfix altered-cursor)').encode(),row))
 def test_prepared_gate_uses_actual_assembly_world(self):
  s=(ROOT/'tests/read-observer-provider-world-unit.lisp').read_text()
  self.assertIn('(include-book "../books/assembly-attach")',s)
  self.assertIn("(getpropc 'fn2-read-observer-enter 'formals",s)
  self.assertIn("(getpropc 'fn2-read-release 'stobjs-out",s)
  self.assertNotIn('(defun fn2-read-',s)
if __name__=='__main__':unittest.main()
