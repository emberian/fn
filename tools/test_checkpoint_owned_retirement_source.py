"""Structural actor/refusal controls only; ACL2 assertions remain unexecuted."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
from rewrite_checkpoint_owned_retirement import rewrite_state, rewrite_arms, STATES, keyword_value
ROOT=Path(__file__).resolve().parents[1]
def fn(text,name): return lr.match('(defun '+name+' ?*body)',lr.parse(text).forms)[0].node
def require(node,pattern):
    if not lr.match(pattern,[node]):raise ValueError(pattern)
class OwnedRetirement(unittest.TestCase):
    def read(self,name):return (ROOT/'books'/name).read_text()
    def test_state_transform_and_foreign_frame(self):
        src='(defmachine foreign :states (:idle))\n(defmachine fn2-checkpoint-master :states (:idle) :holds () :arms ((:idle)))'
        out,n=rewrite_state(src);self.assertEqual(n,3);self.assertTrue(out.startswith('(defmachine foreign :states (:idle))'))
        d=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(out).forms)[0].node
        self.assertEqual([x.low for x in keyword_value(d,':states').items][1:],list(STATES))
        self.assertEqual(rewrite_state(out),(out,0))
    def test_arm_transform_changes_only_selector_done(self):
        src='(defmachine-arms fn2-checkpoint-master :declare :arms ((:other ((:done) (:next :done))) (:teardown-select ((:done) (:next :done) (:charge :steps 1)))))'
        out,n=rewrite_arms(src);self.assertEqual(n,2);self.assertIn('(:other ((:done) (:next :done)))',out)
        self.assertIn('((:done) (:next :teardown-owned-begin)',out)
        self.assertEqual(rewrite_arms(out),(out,0))
    def test_actual_state_body_and_resource_holds(self):
        state=lr.match('(defmachine fn2-checkpoint-master ?*body)',lr.parse(self.read('checkpoint-master-state.lisp')).forms)[0].node
        arms=lr.match('(defmachine-arms fn2-checkpoint-master ?*body)',lr.parse(self.read('checkpoint-master-arms.lisp')).forms)[0].node
        actual=keyword_value(arms,':arms')
        self.assertEqual([x.low for x in keyword_value(state,':states').items],[x.items[0].low for x in actual.items])
        for phase in [':teardown-owned-wait',':teardown-owned-holding-uncertain']:
            require(keyword_value(state,':holds'),'('+phase+' :storage-window)')
        require(actual,'((:done) (:next :teardown-owned-begin) ?*tail)')
    def test_no_candidate_or_caller_tuple_in_core_producer(self):
        text=self.read('checkpoint-owned-retirement.lisp')
        for name in ['submit','poll']:
            f=fn(text,'fn2-checkpoint-owned-retirement-'+name+'-op')
            self.assertEqual([x.low for x in f.items[2].items],['id','ogen','fn2-core'])
        for prohibited in ['fn2-checkpoints-','set-owner']:
            self.assertNotIn(prohibited,text)
        for call in ['fn2-alloc-free','fn2-alloc-release','fn2-alloc-cancel-reservation']:
            self.assertFalse(lr.match('('+call+' ?*args)',lr.parse(text).forms))
        require(fn(text,'fn2-checkpoint-owned-retirement-submit-op'),'(fn2-retirement-submit e epoch allocation *fn2-checkpoint-master-kind* id ogen fn2-core)')
    def test_poll_checks_full_exact_member_before_consumption(self):
        text=self.read('checkpoint-owned-retirement.lisp');f=fn(text,'fn2-checkpoint-owned-retirement-poll-op')
        for field,value in [('owner-kind','*fn2-checkpoint-master-kind*'),('owner-slot','id'),('owner-gen','ogen'),('extent','e'),('epoch','epoch'),('allocation','allocation'),('batch','batch'),('event','event')]:
            require(f,'(= (fn2-retirement-control-'+field+' 0 fn2-retirement-control) '+value+')')
        require(f,'((unless exact) (mv :uncertain :uncertain batch event fn2-core))')
        require(f,'(fn2-retirement-poll *fn2-checkpoint-master-kind* id ogen fn2-core)')
    def test_only_begin_clears_orphan_latch_and_zero_debt_wakes(self):
        text=self.read('checkpoint-owned-retirement.lisp');f=fn(text,'fn2-checkpoint-owned-retirement-begin-op')
        require(f,'(update-fn2-alloc-orphan-dirty 0 fn2-extents)')
        self.assertEqual(text.count('(update-fn2-alloc-orphan-dirty 0 fn2-extents)'),1)
        require(fn(self.read('checkpoint-teardown-sweep.lisp'),'fn2-checkpoint-teardown-needed'),'(or (= (fn2-alloc-orphan-dirty fn2-extents) 1) ?debt)')
    def test_transient_pins_do_not_notify_orphan_scan(self):
        f=fn(self.read('alloc.lisp'),'fn2-alloc-set-edge')
        require(f,'(and changed (fn2-alloc-durable-edgep kind))')
        require(f,'(not (equal value (fn2-alloc-edge-count i kind fn2-extents)))')
if __name__=='__main__':unittest.main()
