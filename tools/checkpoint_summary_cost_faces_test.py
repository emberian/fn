"""Cold face inputs and bounded footprint controls, without ACL2 execution."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
import checkpoint_summary_cost_faces as cf
ROOT=Path(__file__).resolve().parents[1]
class Faces(unittest.TestCase):
    def test_all_actual_inputs_are_declared(self):
        for name,targets in cf.TARGETS.items():
            forms=lr.parse(ROOT/'books'/name).forms
            for child,nbytes,answers in targets:
                fn=lr.match(f'(defun {child} ?args ?*body)',forms,deep=False)[0]
                op=lr.match(f'(defcost {child}-op ?*body)',forms,deep=False)[0].node
                props={op.items[i].low:op.items[i+1] for i in range(2,len(op.items),2)}
                self.assertEqual(props[':child'].low,child)
                self.assertEqual([x.low for x in props[':tables'].items],['fn2-core-'+x.low[4:] for x in fn.captures['args'].items])
                self.assertEqual(props[':steps'].low,'*fn2-work-stage*')
                self.assertEqual(props[':bytes'].low,str(nbytes))
                self.assertEqual(props[':descriptors'].low,'0')
    def test_mutable_return_projection_is_exact(self):
        for name,targets in cf.TARGETS.items():
            forms=lr.parse(ROOT/'books'/name).forms
            for child,_,_ in targets:
                fn=lr.match(f'(defun {child} ?args ?*body)',forms,deep=False)[0]
                inputs=[x.low for x in fn.captures['args'].items]
                expected=(['fn2-checkpoint-summary','fn2-run-installed','fn2-id-engine','fn2-seals']
                          if child=='fn2-checkpoint-summary-apply-step' else
                          ['fn2-checkpoint-summary-authority'] if 'authority' in child else ['fn2-checkpoint-summary'])
                binders=set()
                for block in lr.match('(b* ?bindings ?*body)',[fn.node]):
                    for binding in block.captures['bindings'].items:
                        if hasattr(binding,'items') and binding.items and hasattr(binding.items[0],'items'):
                            head=binding.items[0]
                            if head.items and getattr(head.items[0],'low',None)=='mv':binders.add(head.start)
                for mv in lr.match('(mv ?*args)',[fn.node]):
                    if mv.start in binders:continue
                    outputs=[getattr(x,'low',None) for x in mv.captures['args']]
                    actual=[x for x in outputs if x in inputs]
                    if actual:self.assertEqual(actual,expected,(child,outputs))
    def test_fixture_only_emits_same_child(self):
        source='(defun fn2-test (fn2-left fn2-right) (mv :ok fn2-left))'
        after=cf.add_faces(source,[('fn2-test',0,':ok')])
        self.assertIn('(fn2-core-left fn2-core-right)',after)
        self.assertEqual(len(lr.match('(defun ?*body)',lr.parse(after).forms,deep=False)),1)
        with self.assertRaises(ValueError):cf.add_faces(after,[('fn2-test',0,':ok')])
    def test_actual_lowering_uses_stobjs_not_declared_tables(self):
        forms=lr.parse(ROOT/'books/machine-arms.lisp').forms
        fn=lr.match('(defun fn2-arms-op-face-events ?*body)',forms,deep=False)[0].node
        self.assertTrue(lr.match("(getpropc child 'stobjs-in nil world)",[fn]))
        self.assertTrue(lr.match("(getpropc child 'stobjs-out nil world)",[fn]))
        self.assertTrue(lr.match('(fn2-arms-core-stobj-lets sin world)',[fn]))
if __name__=='__main__':unittest.main()
