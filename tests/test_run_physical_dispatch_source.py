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
        self.assertLess(select.index('fn2-c-source-read-acquire'),select.index('fn2-cursor-physical-sources'))
        split=match('(:if (equal physical 0) ?resident ?physical)',parse(select).forms)
        self.assertEqual(len(split),1)
        branches=split[0].node.items
        resident=select[branches[2].start:branches[2].end]
        physical=select[branches[3].start:branches[3].end]
        self.assertIn('(:goto resident-admit)',resident)
        self.assertNotIn('fn2-run-page-bundle-reserve',resident)
        self.assertEqual(physical.count('fn2-run-page-bundle-reserve'),1)
        self.assertIn(':effects ((:acquire (:storage-window)))',physical)
        self.assertIn('(:goto source-release-refuse)',physical)
        a=src.index('  (:finish :on-refusal');b=src.index('  (:draining',a);finish=src[a:b]
        self.assertLess(finish.index('(lease *fn2-cursor-lease-none*)'),finish.index('(:goto run-load-drain)'))
        self.assertLess(finish.index('(:goto run-load-drain)'),finish.index('(:goto source-release-finish)'))
        release=match('(source-release-finish :on-refusal ?ref ?*steps)',parse(src).forms)[0]
        released=src[release.start:release.end]
        self.assertLess(released.index('fn2-c-source-read-release'),released.index('(equal row-load-refuse 1)'))
        self.assertIn('(:next :draining)',released)
        self.assertIn('*fn2-b-query-loader-jobs*',finish)
    def test_last_member_rank_and_operation_loan(self):
        src=text('machines-c-read-loader.lisp'); region=text('run-physical-region.lisp'); suffix=block(region,'defun','fn2-run-load-region-suffix')
        self.assertIn('fn2-run-load-ownerp',suffix);self.assertIn('fn2-run-loads-windows',suffix)
        self.assertNotIn('pool-workspace-code',suffix)
        drain=block(region,'defun','fn2-run-load-region-drain')
        self.assertIn('(equal (fn2-run-loads-pending c fn2-run-loads) 1)',drain)
        self.assertIn('(if retained :member :last)',drain)
        member=block(region,'defun','fn2-run-load-region-member-release')
        self.assertIn('(eq code :member)',member);self.assertIn('(fn2-run-load-release c ',member)
        cost=block(src,'defcost','fn2-read-loader-member-release-op');self.assertNotIn(':effects',cost)
        wrapper=block(src,'defun','fn2-read-loader-member-release')
        self.assertIn('(fn2-read-loader-job read0 ordinal',wrapper)
        self.assertIn('(fn2-run-load-region-member-release ordinal',wrapper)
        self.assertIn('(fn2-run-load-range-miss i n x (fn2-reads-sid x fn2-reads)',src)
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
    def test_article_borrows_unused_exact_page_without_same_rank_wait(self):
        src=text('cursor.lisp'); borrow=block(src,'defun','fn2-cursor-query-article-page-children')
        for evidence in ('fn2-machines-kind', 'fn2-machines-slot', 'fn2-cursor-generation',
                         'fn2-cursor-state-render', '(fn2-cursor-step row fn2-cursor) 22',
                         '*fn2-cursor-query-bundle-held*', '(fn2-cursor-load-active row fn2-cursor) 0',
                         '*fn2-succ-lookup-idle*', '*fn2-read-op-range*', '*fn2-read-op-scan*',
                         'fn2-run-load-ownerp', '(fn2-run-loads-pending c fn2-run-loads) 0', 'fn2-pool-workspace-code'):
            self.assertIn(evidence,borrow)
        self.assertIn('(physical 0)',borrow);self.assertIn('*fn2-run-load-phase-reserved*',borrow)
        self.assertLess(borrow.index('fn2-succ-txns-lphase'),borrow.index('(fn2-pool-reset'))
        self.assertNotIn('fn2-pool-reserve',borrow)
        # Physical article rendering still borrows a preadmitted exact page;
        # only the resident preheader path admits a standalone workspace.
        late=match('(art-lease :on-refusal ?ref ?*steps)',parse(src).forms)[0]
        late=src[late.start:late.end]
        self.assertIn('fn2-cursor-query-article-page',late)
        self.assertNotIn('fn2-cursor-lease-reserve',late)
        resident=match('(resident-admit :on-refusal ?ref ?*steps)',parse(src).forms)[0]
        resident=src[resident.start:resident.end]
        self.assertIn('fn2-cursor-lease-reserve',resident)
        self.assertIn('(:goto source-release-refuse)',resident)
        self.assertIn('(:next :seek)',resident)
        for name in ('art-fail','art-end',':finish'):
            scope=match(f'({name} :on-refusal ?ref ?*steps)',parse(src).forms)[0]
            scope=src[scope.start:scope.end]
            guarded=match('(:if (equal row-query-bundle *fn2-cursor-query-bundle-none*) ?standalone ?borrowed)',parse(scope).forms)
            self.assertEqual(len(guarded),1)
            standalone=guarded[0].node.items[2];borrowed=guarded[0].node.items[3]
            self.assertIn('fn2-cursor-lease-release',scope[standalone.start:standalone.end])
            self.assertEqual(scope[borrowed.start:borrowed.end],'()')
        self.assertNotIn('(:park :pool',src)
        self.assertIn('(fn2-cursor-query-article-page row-slot id row-generation)',src)
    def test_prepared_article_borrow_fixture(self):
        fixture=(ROOT/'tests'/'cursor-query-borrow-unit.lisp').read_text()
        self.assertIn('SYNTHETIC internal premises',fixture)
        self.assertIn('(fn2-run-load-reserve 1 *fn2-cursor-kind* 10 19',fixture)
        self.assertIn('(fn2-cursor-query-article-page-children 0 10 19',fixture)
        for result in ('active-refused','pending-refused','lookup-refused','xl-refused','bundle-refused','old-ready'):
            self.assertIn(result,fixture)
        self.assertIn('(equal (fn2-run-cursors-unit 3 fn2-run-cursors) 777)',fixture)
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
