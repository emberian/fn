#!/usr/bin/env python3
"""Structural controls for actual D loader composition; no Lisp evaluation."""
from pathlib import Path
import sys, unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse, match, Lst, Atom
from cursor_physical_dispatch_rewrite import transform, transform_answers

def text(name): return (ROOT/'books'/name).read_text()
def block(src,head,name):
    found=match(f'({head} {name} ?*tail)',parse(src).forms,deep=False)
    assert len(found)==1,(head,name,len(found))
    return src[found[0].start:found[0].end]

class DispatchSource(unittest.TestCase):
    def test_all_actual_reads_route_miss(self):
        src=text('cursor.lisp'); self.assertEqual(transform(src),(src,0))
        routes=match('((:miss) (:set (load-read ?row)) (:goto run-load-start))',parse(src).forms)
        self.assertEqual(len(routes),10)
        costs=text('machines-c-read.lisp'); self.assertEqual(transform_answers(costs),(costs,0))
    def test_owner_constructor_is_selected_not_scalar(self):
        src=block(text('machines-c-read-loader.lisp'),'defun','fn2-read-loader-owner')
        self.assertIn('(fn2-read-loader-selected x ',src)
        self.assertLess(src.index('fn2-run-load-ownerp'),src.index('(fn2-run-cursors-put'))
        self.assertLess(src.index('fn2-checkpoint-summary-leases-owner-gen'),src.index('(fn2-run-cursors-put'))
        self.assertNotIn('fn2-block-read',src)
        mutant=src.replace('(fn2-read-loader-selected x ','(caller-cursor x ')
        self.assertNotIn('(fn2-read-loader-selected x ',mutant)
    def test_read_is_explicit_issue_only(self):
        src=text('cursor.lisp')
        calls=match('(:issue (fn2-run-page-read ?*args) ?*tail)',parse(src).forms)
        self.assertEqual(len(calls),1)
        self.assertFalse(match('(:do ?out (fn2-run-page-read ?*args) ?*tail)',parse(src).forms))
        self.assertIn('(:set (rready 0)) (:wait :completion',src[calls[0].start:calls[0].end])
        self.assertEqual(src.count('(run-load-step :on-refusal'),1)
    def test_admission_precedes_query_and_partial_refusal_waits_cleanup(self):
        src=text('cursor.lisp'); a=src.index('  (:select :on-refusal'); b=src.index('  (:seek :on-refusal',a); select=src[a:b]
        self.assertLess(select.index('fn2-run-page-bundle-reserve'),select.index('(:next (:if (equal complete 1) :seek :finish))'))
        self.assertIn('(load-refuse (if (equal complete 1) 0 1))',select)
        a=src.index('  (:finish :on-refusal');b=src.index('  (:draining',a);finish=src[a:b]
        self.assertLess(finish.index('fn2-cursor-lease-release'),finish.index('(:goto run-load-drain)'))
        self.assertLess(finish.index('(:goto run-load-drain)'),finish.index('((equal row-load-refuse 1)'))
        self.assertIn('*fn2-b-query-loader-jobs*',finish)
    def test_last_member_rank_and_operation_loan(self):
        src=text('machines-c-read-loader.lisp'); suffix=block(src,'defun','fn2-read-loader-suffix')
        self.assertIn('fn2-run-load-ownerp',suffix);self.assertIn('fn2-run-loads-windows',suffix)
        self.assertNotIn('pool-workspace-code',suffix)
        drain=block(src,'defun','fn2-read-loader-drain')
        self.assertIn('(equal (fn2-run-loads-pending c fn2-run-loads) 1)',drain)
        self.assertIn('(if retained :member :last)',drain)
        member=block(src,'defun','fn2-read-loader-member-release')
        self.assertIn('(eq code :member)',member);self.assertIn('(fn2-run-load-release c ',member)
        cost=block(src,'defcost','fn2-read-loader-member-release-op');self.assertNotIn(':effects',cost)
        actor=text('cursor.lisp')
        self.assertIn('(fn2-run-page-release c *fn2-cursor-kind* id row-generation)\n                :effects ((:release (:storage-window)))',actor)
    def test_physical_entry_owner_and_core_faces(self):
        lookup=block(text('machines-c-read.lisp'),'defun','fn2-rd-lookup')
        self.assertIn('(equal erow (+ b0 *fn2-read-heads* *fn2-run-reader-entry*))',lookup)
        for f in ('okind','oslot','ogen'): self.assertIn(f'(fn2-run-cursors-{f} tx fn2-run-cursors)',lookup)
        src=text('run-physical-core-faces.lisp'); self.assertIn('(fn2-arms-op-face-events op child world)',src)
        self.assertIn('(not (function-symbolp op world))', src)
        self.assertIn('(fn2-run-loader-core-face-events *fn2-read-loader-core-operations*', text('machines-c-read-loader.lisp'))
        c=text('assembly-callbacks-c-prepare.lisp')
        self.assertLess(c.index('(fn2-run-page-core-faces)'), c.index('(fn2-successor-prepare-events)'))
        for op in ('fn2-run-page-bind','fn2-run-page-step','fn2-run-page-read','fn2-run-page-release'):
            self.assertIn(op,src)
        self.assertIn('fn2-run-page-bundle-reserve', text('machines-c-read-loader.lisp'))
        callbacks=text('assembly-callbacks-d-cursor.lisp');self.assertLess(callbacks.index('(fn2-read-loader-core-faces)'),callbacks.index('(defmachine-arms fn2-cursor :wrappers)'))
    def test_prepared_adapter_refusal_and_hook_fixture(self):
        fixture=(ROOT/'tests'/'run-physical-dispatch-unit.lisp').read_text()
        self.assertIn('SYNTHETIC internal premises',fixture)
        self.assertIn('(fn2-run-cursor-start-installed 1 4',fixture)
        self.assertIn('(fn2-read-loader-owner 0 7 13 19',fixture)
        self.assertIn('(eq mismatch :source)',fixture)
        self.assertIn('(eq foreign :source)',fixture)
        self.assertIn('(eq lease :source)',fixture)
        self.assertIn('(eq range-bad :source)',fixture)
        self.assertIn('(eq pending :wait)',fixture)
        self.assertIn('(fn2-run-load-harvest 0 40 0',fixture)
        self.assertIn('(fn2-run-load-harvest 0 41 0',fixture)
        self.assertIn('(eq member :member)',fixture)
if __name__=='__main__': unittest.main()
