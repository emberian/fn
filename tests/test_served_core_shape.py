"""Refutation controls for conditional core-shape proposals (not Lean evidence)."""
import sys
from pathlib import Path
import unittest
import tempfile
sys.path.insert(0,str(Path(__file__).parents[1]/'meta/emit'))
from emit_lean import Atom as A, List as L
from served_core_shape import CoreShapeAnalyzer, emit_shape_candidates


def term(x):
    return L([term(y) for y in x]) if isinstance(x,list) else A(str(x))


class ShapeControls(unittest.TestCase):
    def check(self, body, path=(), n=3):
        a=CoreShapeAnalyzer({'F':(['CORE','X'],term(body),[],None)})
        return a.ensure('F',n,path,0)

    def test_bounded_update_preserves_shape_but_padding_does_not(self):
        self.assertTrue(self.check(['UPDATE-NTH',['QUOTE',2],'X','CORE']))
        self.assertFalse(self.check(['UPDATE-NTH',['QUOTE',3],'X','CORE']))
        self.assertFalse(self.check(['UPDATE-NTH','X','X','CORE']))

    def test_both_conditional_branches_are_required(self):
        good=['UPDATE-NTH',['QUOTE',1],'X','CORE']
        self.assertTrue(self.check(['IF','X',good,'CORE']))
        self.assertFalse(self.check(['IF','X',good,['QUOTE','NIL']]))

    def test_lambda_bindings_and_result_projection(self):
        body=[['LAMBDA',['TMP'],['CONS','X',['CONS','TMP',['QUOTE','NIL']]]],
              ['UPDATE-NTH',['QUOTE',1],'X','CORE']]
        self.assertTrue(self.check(body,path=(1,)))
        self.assertFalse(self.check(body,path=(0,)))
        self.assertFalse(self.check(body,path=(2,)))

    def test_recursive_and_unknown_calls_are_not_assumptions(self):
        self.assertFalse(self.check(['F','CORE','X']))
        self.assertFalse(self.check(['MISSING','CORE']))

    def test_callee_precondition_requires_shape_of_actual_argument(self):
        a=CoreShapeAnalyzer({
            'F':(['CORE','X'],term(['G','X']),[],None),
            'G':(['V'],term(['UPDATE-NTH',['QUOTE',1],['QUOTE',0],'V']),[],None)})
        self.assertFalse(a.ensure('F',3,(),0))
        a.definitions['F']=(['CORE','X'],term(['G','CORE']),[],None)
        b=CoreShapeAnalyzer(a.definitions)
        self.assertTrue(b.ensure('F',3,(),0))
        self.assertEqual(b.order,[('G',3,(),0),('F',3,(),0)])

    def test_emitted_statement_retains_precondition_and_dependency(self):
        a=CoreShapeAnalyzer({
            'F':(['CORE'],term(['G','CORE']),[],None),
            'G':(['CORE'],term(['UPDATE-NTH',['QUOTE',1],['QUOTE',0],'CORE']),[],None)})
        self.assertTrue(a.ensure('F',3,(),0))
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Shapes.lean'
            emit_shape_candidates(a,p,{},lambda text,_:text)
            source=p.read_text()
        self.assertEqual(source.count('(hcore : isListB 3 «CORE» = true)'),2)
        self.assertIn('«G_core_shape_3_whole_arg0»',source)
        self.assertIn('disch := first | assumption | decide',source)
        self.assertIn('«CORE» : Fin 3 → Val',source)
        self.assertIn('Combinators.tupleImage_kidsOfVal',source)
        self.assertIn('Int.reduceSub',source)
        self.assertNotIn('sorry',source)
        self.assertNotIn('axiom ',source)

    def test_only_consumed_dependency_closure_is_emitted(self):
        a=CoreShapeAnalyzer({
            'F':(['CORE'],term(['G','CORE']),[],None),
            'G':(['CORE'],term('CORE'),[],None),
            'UNUSED':(['CORE'],term('CORE'),[],None)})
        self.assertTrue(a.ensure('F',3,(),0))
        self.assertTrue(a.ensure('UNUSED',3,(),0))
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'Shapes.lean'
            emit_shape_candidates(a,p,{},lambda text,_:text,targets={('F',3,(),0)})
            source=p.read_text()
        self.assertIn('«G_core_shape_3_whole_arg0»',source)
        self.assertNotIn('UNUSED',source)


class AdapterRefusalControls(unittest.TestCase):
    def builder(self,body,core_mode=True,output=None):
        from served_proof_gen import ArmProofBuilder, TupleShapeAnalyzer
        b=object.__new__(ArmProofBuilder)
        b.core_mode=core_mode; b.n_tup=3
        b.kinfo={'ops':{'F':{'core_out':output or ['FN2-CORE'],
                            'core_in':['FN2-CORE'],'core_formals':['CORE']}}}
        definitions={'F':(['CORE'],term(body),[],None)}
        b.tuple_analyzer=TupleShapeAnalyzer(definitions,{})
        b.tuple_analyzer.core_shapes=CoreShapeAnalyzer(definitions)
        return b

    def test_adapter_refuses_padding_result(self):
        from served_proof_gen import UnsupportedArmError
        b=self.builder(['UPDATE-NTH',['QUOTE',3],['QUOTE',0],'CORE'])
        with self.assertRaisesRegex(UnsupportedArmError,'core shape unavailable'):
            b.prove_core_call({'op':'F'},None)

    def test_adapter_does_not_apply_core_rule_in_child_world(self):
        from served_proof_gen import UnsupportedArmError
        with self.assertRaisesRegex(UnsupportedArmError,'core result layout'):
            self.builder('CORE',False).prove_core_call({'op':'F'},None)

    def test_adapter_does_not_treat_multi_result_as_whole_core(self):
        from served_proof_gen import UnsupportedArmError
        with self.assertRaisesRegex(UnsupportedArmError,'core result tuple shape'):
            self.builder('CORE',output=[None,'FN2-CORE']).prove_core_call({'op':'F'},None)

    def test_core_projection_does_not_replace_proper_result_tuple_check(self):
        from served_proof_gen import UnsupportedArmError
        body=['CONS',['QUOTE',0],['CONS','CORE',['QUOTE',99]]]
        b=self.builder(body,output=[None,'FN2-CORE'])
        self.assertTrue(b.tuple_analyzer.core_shapes.ensure('F',3,(1,),0))
        with self.assertRaisesRegex(UnsupportedArmError,'core result tuple shape'):
            b.prove_core_call({'op':'F'},None)


if __name__=='__main__': unittest.main()
