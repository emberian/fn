"""Actual successor borrow-boundary source controls; not ACL2 evaluation."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def node(source,name):return lr.match(f'(defun {name} ?*body)',lr.parse(source).forms,deep=False)[0].node
def canon(n):
    if hasattr(n,'low'):return n.low
    return tuple(canon(x) for x in n.items)
def check_resolve(source):
    f=node(source,'fn2-succ-resolve-step')
    if not lr.match('(fn2-succ-copy-scalar-rows ?*args)',[f]) or not lr.match('(fn2-succ-source-values-scalar-p nv nk sid)',[f]):raise ValueError('resolved source values must be scalar-guarded')
    row=node(source,'fn2-succ-copy-scalar-row')
    for field in ['ref-slot','ref-gen','ref-off','ref-len']:
        if not lr.match(f'({field} 0)',[row]):raise ValueError('escaped source coordinate '+field)
    if not lr.match('(status (fn2-fields-status from fn2-fields))',[row]):raise ValueError('status changed')
    wrapper=node(source,'fn2-succ-resolve')
    if not lr.match('(and (eq code :ok) ?*rest)',[wrapper]):raise ValueError('incomplete resolve must retain observation')
    if not lr.match('(fn2-succ-clear-ref-rows *fn2-run-reader-fields* (+ b0 *fn2-idc-rb*) fn2-fields)',[wrapper]):raise ValueError('completed reader scratch escaped')
def check_stage(source):
    f=node(source,'fn2-succ-stage')
    if len(lr.match('(fn2-succ-stage-raw ?*args)',[f.items[-1]]))!=1:raise ValueError('not same single actual stage kernel')
    if not lr.match('(fn2-succ-clear-ref-rows *fn2-run-entry-rows* (+ b0 *fn2-idc-eb*) fn2-fields)',[f]):raise ValueError('decoded scratch escaped')
    if not lr.match('(if (and valid (not (eq code :ok))) (fn2-succ-clear-stage-refs *fn2-succ-slots* 0 b0 fn2-fields) fn2-fields)',[f]):raise ValueError('failed stage refs escaped')
    clear=node(source,'fn2-succ-clear-stage-refs')
    if not lr.match('(fn2-succ-clear-ref-rows *fn2-succ-fields-max* (+ b0 (* *fn2-succ-block* i)) fn2-fields)',[clear]):raise ValueError('cleanup crosses raw arguments')
class Source(unittest.TestCase):
    def setUp(self):
        self.resolve=(ROOT/'books/machines-c-successor.lisp').read_text();self.stage=(ROOT/'books/machines-c-stage.lisp').read_text()
    def test_actual_resolve_boundary(self):check_resolve(self.resolve)
    def test_actual_stage_boundary(self):check_stage(self.stage)
    def test_raw_expression_identity(self):
        old=(ROOT/'tools/fixtures/successor-source-before.lisp').read_text()
        for name,source in [('fn2-succ-resolve',self.resolve),('fn2-succ-stage',self.stage)]:
            before = ((ROOT/'tools/fixtures/successor-physical-owner-before.lisp').read_text()
                      if name == 'fn2-succ-resolve' else old)
            self.assertEqual(canon(node(before,name).items[-1]),canon(node(source,name+'-raw').items[-1]))
    def test_removed_reference_strip_refused(self):
        with self.assertRaises(ValueError):check_resolve(self.resolve.replace('(ref-gen 0)','(ref-gen (fn2-fields-ref-gen from fn2-fields))'))
    def test_failed_stage_without_cleanup_refused(self):
        with self.assertRaises(ValueError):check_stage(self.stage.replace('(not (eq code :ok))','nil'))
    def test_real_reuse_fixture(self):
        forms=lr.parse(ROOT/'tests/successor-source-lifetime-unit.lisp').forms
        replace=lr.match('(defun fn2-ssl-replace ?*body)',forms)[0].node
        for pattern in ['(fn2-successor-publish ?*args)','(fn2-ssl-seal fn2-core)']:
            self.assertTrue(lr.match(pattern,[replace]))
        overwrite=lr.match('(defun fn2-ssl-overwrite-old ?*body)',forms)[0].node
        self.assertTrue(lr.match('(fn2-core-reserve ?*args)',[overwrite]))
        self.assertTrue(lr.match('(when (= slot oldslot))',[overwrite]))
        body=lr.match('(defun fn2-ssl-body ?*body)',forms)[0].node
        for pattern in ['(eq stale :stale)','(eq staged3 :duplicate)','(= key-byte 7)']:
            self.assertTrue(lr.match(pattern,[body]))
if __name__=='__main__':unittest.main()
