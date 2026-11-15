"""Current ROOT projection controls; no ACL2 execution or admission claim."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from physical_c_root_rewrite import DATA,node,source,project_runs,project_range,project_machines

def forms(text):return { (getattr(x.items[0],'low',''),getattr(x.items[1],'low','')):source(text,x) for x in lr.parse(text).forms if isinstance(x,lr.Lst) and len(x.items)>1}
class PhysicalCurrentRoot(unittest.TestCase):
 def test_named_projection_idempotence(self):
  for book,fn in (('runs',project_runs),('range',project_range),('machines-c',project_machines)):
   actual=(ROOT/'books'/(book+'.lisp')).read_text()
   self.assertEqual(fn(DATA['before'][book]),actual)
   self.assertEqual(fn(actual),actual)
 def test_all_other_run_events_unchanged(self):
  old=forms(DATA['before']['runs']);new=forms((ROOT/'books/runs.lisp').read_text())
  allowed={('defcolumns',n) for n in ('fn2-run-cursors','fn2-run-paths','fn2-run-installed')}|{('defun',n) for n in ('fn2-run-cursor-start','fn2-run-install','fn2-run-retired-next')}
  for key,value in old.items():
   if key not in allowed:self.assertEqual(new[key],value,key)
  # Qualified guard declarations are preserved even in changed constructors.
  for _,name in allowed:
   if ('defun',name) not in old:continue
   a=node(DATA['before']['runs'],'defun',name);actual=(ROOT/'books/runs.lisp').read_text();b=node(actual,'defun',name)
   self.assertEqual(source(DATA['before']['runs'],a.items[3]),source(actual,b.items[3]))
 def test_root_range_hints_preserved(self):
  actual=(ROOT/'books/range.lisp').read_text();old=DATA['before']['range']
  # ROOT's three call-guard-hint hooks stay present, with only actual callee renamed.
  for m in lr.match('(fn2-columns-call-guard-hint ?*args)',lr.parse(old).forms,deep=True):
   self.assertIn(source(old,m.node).replace('fn2-run-cursor-start ','fn2-run-cursor-start-installed '),actual)
  self.assertIn('fn2-run-cursor-start-installed c r',actual)
  self.assertIn('(okind (fn2-run-cursors-okind c fn2-run-cursors))',actual)
 def test_full_ref_wire_priority_and_count(self):
  actual=(ROOT/'books/runs.lisp').read_text()
  start=source(actual,node(actual,'defun','fn2-run-cursor-start-installed'))
  self.assertIn('(run (fn2-run-installed-wire-run r fn2-run-installed))',start)
  self.assertIn('(priority (fn2-run-installed-run r fn2-run-installed))',start)
  for i in range(8):self.assertIn('(hash-'+str(i)+' (fn2-run-installed-hash-'+str(i)+' r fn2-run-installed))',start)
  for name in ('fn2-run-install-physical','fn2-run-free-physical'):
   self.assertIn('update-fn2-run-installed-physical-count',source(actual,node(actual,'defun',name)))
  self.assertIn('(mv :physical fn2-run-installed)',source(actual,node(actual,'defun','fn2-run-retired-next')))
 def test_registered_completion_and_explicit_issue(self):
  actual=(ROOT/'books/machines-c.lisp').read_text()
  self.assertIn(':harvest (fn2-run-load-harvest ',actual)
  self.assertIn('(defcost fn2-run-page-read :child fn2-run-load-issue :answers t :descriptors 1',actual)
  self.assertIn(':effects ((:acquire (:operation)))',actual)
  self.assertIn('(fn2-run-cursors-init (fn2-b-run-cursor-rows profile)',actual)
  # Current ROOT successor geometry has not been replaced with an old donor.
  self.assertIn('(defconst *fn2-succ-block* 48)',actual)
 def test_literal_mv_limit(self):
  for book in ('runs','range','machines-c'):
   text=(ROOT/'books'/(book+'.lisp')).read_text()
   for m in lr.match('(mv ?*values)',lr.parse(text).forms,deep=True):self.assertLessEqual(len(m.captures['values']),32)
if __name__=='__main__':unittest.main()
