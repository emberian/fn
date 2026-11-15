"""Actual terminal owner/dispatcher controls; source only, no ACL2 execution."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import rewrite_checkpoint_dispose_master as rw
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk,declaration

def source(stem):return (ROOT/'books'/(stem+'.lisp')).read_text()
def definition(text,name):
    return next(n for s in forms(text) for n in walk(read_sexp(s)) if n[:2]==['defun',name])

class ActualMaster(unittest.TestCase):
    def test_schema_class_preserves_old_states_and_other_machine(self):
        fixture='(defmachine fn2-checkpoint-master :states (:idle :done) :fields ((x :u60)) :arms ((:idle) (:done)))\n(defmachine other :states (:idle))'
        out,n=rw.rewrite(fixture)
        self.assertEqual(n,3)
        self.assertEqual(rw.rewrite(out),(out,0))
        self.assertIn(':states (:idle :done :teardown-dispose-begin :teardown-dispose-step)',out)
        self.assertTrue(out.endswith('(defmachine other :states (:idle))'))
    def test_actual_callback_phase_actor_and_generation_derive_subject(self):
        text=source('checkpoint-dispose-callbacks')
        for name,phase in [('fn2-checkpoint-dispose-begin-op','begin'),('fn2-checkpoint-dispose-step-op','step')]:
            f=definition(text,name);calls=list(walk(f))
            self.assertIn(['=', ['fn2-machine-phase','id','fn2-core'],'*fn2-checkpoint-master-state-teardown-dispose-'+phase+'*'],calls)
            self.assertIn(['=', ['fn2-machine-generation','id','fn2-core'],'gen'],calls)
            self.assertIn('fn2-checkpoint-master-row-debt-scan',str(f))
            self.assertIn('fn2-checkpoint-master-row-token',str(f))
            self.assertIn('fn2-checkpoint-dispose-control-held-p',str(f))
        step=definition(text,'fn2-checkpoint-dispose-step-op')
        self.assertIn('fn2-checkpoint-master-row-teardown-debt-generation',str(step))
        for n in walk(read_sexp(next(s for s in forms(text) if 'defmacro fn2-checkpoint-dispose-events' in s))):
            if n and n[0]=='stobj-let':self.assertEqual(len(n),5)
    def test_callback_macro_emits_all_faces_in_one_body(self):
        text=source('checkpoint-dispose-callbacks')
        macro=next(read_sexp(s) for s in forms(text) if read_sexp(s)[:2]==['defmacro','fn2-checkpoint-dispose-events'])
        def emitted(value):
            if len(value)!=4 or value[3][0]!='let*' or len(value[3])!=3:return []
            bindings,body=value[3][1:]
            if [x[0] for x in bindings]!=['children','fields','bindings']:return []
            if body[0]!='quasiquote' or body[1][0]!='progn':return []
            return [n[:2] for n in body[1][1:]]
        expected=[['defun','fn2-checkpoint-dispose-control-held-p'],
                  ['defun','fn2-checkpoint-dispose-begin-op'],
                  ['fn2-core-preserves','fn2-checkpoint-dispose-begin-op'],
                  ['defun','fn2-checkpoint-dispose-step-op'],
                  ['fn2-core-preserves','fn2-checkpoint-dispose-step-op']]
        self.assertEqual(emitted(macro),expected)
        import copy
        bad=copy.deepcopy(macro);bad[3][1].append(bad[3].pop())
        self.assertNotEqual(emitted(bad),expected)
    def test_actual_generated_root1_output_inventory_fits_mv_limit(self):
        text=source('checkpoint-metadata-driver')
        inventory=next(read_sexp(s) for s in forms(text) if read_sexp(s)[:2]==['defconst','*fn2-checkpoint-root1-outputs*'])[2][1]
        self.assertTrue(inventory)
        # Each declaration includes its function name; replacing that name by
        # the CODE result gives exactly the emitted output count.
        for row in inventory:self.assertLessEqual(len(row),32,row[0])
    def test_actual_routes_close_before_drop_and_resume_after_partial_scrub(self):
        arms=declaration(source('checkpoint-master-arms'));amap={x[0]:x for x in arms[arms.index(':arms')+1]}
        self.assertIn([':next',':teardown-dispose-begin'],list(walk(amap[':teardown-source'])))
        self.assertIn([':next',':teardown-dispose-begin'],list(walk(amap[':teardown-select'])))
        for phase in (':teardown-dispose-begin',':teardown-dispose-step'):
            self.assertIn(['and',['natp','budget'],['<','0','budget']],list(walk(amap[phase])))
        step=list(walk(amap[':teardown-dispose-step']))
        self.assertIn(['fn2-checkpoint-dispose-step-op','budget','id','row-generation'],step)
        self.assertIn([':next',':teardown-retained'],step)
        select=definition(source('checkpoint-teardown-sweep'),'fn2-checkpoint-teardown-select')
        self.assertIn('fn2-checkpoint-dispose-current-p',str(select))
        self.assertIn("':dispose'",str(select))
    def test_providers_reach_actual_composition_without_include_cycle(self):
        seen=set();active=[]
        def visit(path):
            path=path.resolve()
            self.assertTrue(path.is_file(),str(path))
            self.assertNotIn(path,active)
            if path in seen:return
            seen.add(path);active.append(path)
            for match in lr.match('(include-book ?book ?*opts)',lr.parse(path.read_text()).forms,deep=False):
                opts=match.captures['opts']
                if not any(isinstance(x,lr.Atom) and x.low==':dir' for x in opts):
                    visit(path.parent/(match.captures['book'].text.strip('"')+'.lisp'))
            active.pop()
        visit(ROOT/'books/assembly-init.lisp')
        for name in ('checkpoint-dispose-callbacks','checkpoint-dispose','checkpoint-owned-retirement','checkpoint-payload-proof','event-archive-state'):
            self.assertIn((ROOT/'books'/(name+'.lisp')).resolve(),seen)
        self.assertIn('(fn2-checkpoint-master-events)',source('assembly-callbacks-c'))
        # Preserve the parent's real RELEASE harvest registration and its
        # successor geometry; packet composition must not copy old versions.
        self.assertIn('(include-book "release-allocation-harvest")',source('machines-b'))
        self.assertIn(':harvest (fn2-allocation-release-harvest',source('machines-b'))
        self.assertIn('(include-book "successor-schema-geometry")',source('machines-c'))
    def test_only_final_transition_resets_candidate_debt_and_wakes_orphans(self):
        text=source('checkpoint-dispose')
        self.assertIn('(update-fn2-alloc-orphan-dirty 1 fn2-extents)',text)
        self.assertIn('(fn2-checkpoint-teardown-debt-reset-row c',text)
        self.assertIn('(fn2-checkpoints-reset-row c',text)
        self.assertNotIn('construction-reset',text)
        self.assertNotIn('(fn2-alloc-release',text)
        self.assertNotIn('(fn2-alloc-retire',text)
        self.assertIn('(fn2-checkpoint-bank-closure-edge physical e',text)
        self.assertNotIn('(fn2-checkpoint-source-edge physical e',text)
        self.assertIn('(fn2-checkpoint-dispose-events)',source('checkpoint-master-events'))
        self.assertIn('(defconst *fn2-checkpoint-activation-qualified* nil)',source('checkpoint-master-state'))
if __name__=='__main__':unittest.main()
