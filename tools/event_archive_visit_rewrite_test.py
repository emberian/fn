"""Same concrete restart-byte formula and exact operation/face cost replay."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_accumulator_rewrite as acc
import event_archive_fixed_rows_rewrite as fixed
import event_archive_visit_rewrite as rw
import event_archive_member_rewrite as member
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def form(s,p):
 n=lr.match(p,lr.parse(s).forms)[0].node
 return s[n.start:n.end]
class Visit(unittest.TestCase):
 def test_operation_template_replay_and_idempotence(self):
  old=read('tools/fixtures/archive-visit-before-event-archive-producer.lisp');after=rw.operation(old)
  self.assertEqual(form(after,'(defmacro fn2-event-archive-operation ?*args)'),form(read('books/event-archive-producer.lisp'),'(defmacro fn2-event-archive-operation ?*args)'))
  self.assertEqual(rw.operation(after),after)
  self.assertIn("(bytes (if costp (cadar body) '(* 2 *fn2-run-layout-max-entry-bytes*)))",after)
 def test_same_actual_formula_and_envelope_premises(self):
  old=read('tools/fixtures/archive-visit-before-checkpoint-restore-semantic-work.lisp')
  f=form(old,'(defconst *fn2-checkpoint-restore-semantic-entry-bytes* ?value)')
  shared=read('books/run-entry-work.lisp')
  self.assertEqual(f.replace('*fn2-checkpoint-restore-semantic-entry-bytes*','*fn2-run-entry-visit-bytes*'),form(shared,'(defconst *fn2-run-entry-visit-bytes* ?value)'))
  for p in ['(assert-event (<= *fn2-run-layout-max-entry-bytes* *fn2-format-page-size*))',
            '(assert-event (<= (+ (* 2 *fn2-run-entries-base*) *fn2-run-restart-bytes* 32) (* 2 *fn2-format-page-size*)))',
            '(assert-event (<= *fn2-run-entry-visit-bytes* *fn2-checkpoint-semantic-visit-bytes*))']:
   self.assertTrue(lr.match(p,lr.parse(shared).forms),p)
  s=read('books/checkpoint-restore-semantic-work.lisp')
  self.assertIn('(defconst *fn2-checkpoint-restore-semantic-entry-bytes* *fn2-run-entry-visit-bytes*)',s)
 def test_check_child_and_both_actual_core_faces_use_same_cost(self):
  old=read('tools/fixtures/archive-visit-before-event-archive-cold-boot.lisp')
  names=['fn2-boot-checkpoint-archive-check-raw','fn2-boot-checkpoint-archive-check']
  current=read('books/event-archive-cold-boot.lisp');after=rw.explicit(old,names)
  self.assertEqual(acc.project('boot', fixed.rewrite(member.boot(after))),current);self.assertEqual(rw.explicit(after,names),after)
  for path,name in [('event-archive-cold-cursor','fn2-event-archive-cold-cursor-step'),('event-archive-cold-reach','fn2-event-archive-cold-step-reach')]:
   s=read('books/'+path+'.lisp');n=lr.match('(fn2-event-archive-operation '+name+' ?*body)',lr.parse(s).forms)[0].node
   self.assertEqual(s[n.items[4].start:n.items[4].end],'(:bytes *fn2-run-entry-visit-bytes*)')
   before=read('tools/fixtures/archive-visit-before-'+path+'.lisp');before=acc.project(path, fixed.rewrite(member.cursor(before) if path=='event-archive-cold-cursor' else before));beforeform=form(before,'(fn2-event-archive-operation '+name+' ?*body)')
   restored=lr.write(s,[(n.items[4].start,n.items[4].end+1,'')])
   # Byte-cost directive alone must leave the actual implementation AST identical.
   norm=lambda x:lr.flat(lr.parse(x).forms[0])
   self.assertEqual(norm(form(restored,'(fn2-event-archive-operation '+name+' ?*body)')),norm(beforeform))
if __name__=='__main__':unittest.main()
