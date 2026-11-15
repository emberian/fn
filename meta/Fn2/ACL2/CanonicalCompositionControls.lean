module
public import Fn2.ACL2.CanonicalEvaluationControls
@[expose] public section
namespace Fn2.ACL2.Translation.CompositionControls
open DomainControls

def pipeline : Term := .lam ["Y"] (.app "FN2-TV-TWICE-BUMP" [.var "Y"])
  [.app "FN2-TV-TWICE-BUMP" [.quote (.int 4)]]

-- The first callee's represented-result postcondition supplies the second
-- callee's input domain. Both calls use their closed body certificate.
theorem pipeline_correct :
    CanonicalEval program domain primitiveDomain [] pipeline (.int 8) ∧
    eval emitted [] pipeline 5 = .ok (.int 8) := by
  obtain ⟨first, closedFirst, evaluatedFirst, n, rfl⟩ :=
    canonical_call_correct (env := []) (fuel := 3)
      (by decide +kernel : "FN2-TV-TWICE-BUMP" ≠ "IF")
      (by decide +kernel : "FN2-TV-TWICE-BUMP" ≠ "RETURN-LAST")
      (nativeCall_none _ _ (by decide +kernel))
      (.cons (.quote (v := .int 4)) .nil) (by rfl)
      ⟨Or.inr rfl, 4, rfl⟩ twice_correct
  obtain ⟨second, closedSecond, evaluatedSecond, postSecond⟩ :=
    canonical_call_correct (env := [("Y", .int n)]) (fuel := 3)
      (by decide +kernel : "FN2-TV-TWICE-BUMP" ≠ "IF")
      (by decide +kernel : "FN2-TV-TWICE-BUMP" ≠ "RETURN-LAST")
      (nativeCall_none _ _ (by decide +kernel))
      (.cons (.var (name := "Y") rfl) .nil) (by rfl)
      ⟨Or.inr rfl, n, rfl⟩ twice_correct
  have joined := canonical_lambda_correct
    (.cons closedFirst .nil) (eval_args_cons evaluatedFirst (eval_args_nil emitted [] 4))
    (by rfl : ([Val.int n]).length = (["Y"] : List String).length)
    closedSecond evaluatedSecond
  change CanonicalEval program domain primitiveDomain [] pipeline second ∧
    eval emitted [] pipeline 5 = .ok second at joined
  have actual : eval emitted [] pipeline 5 = .ok (.int 8) := rfl
  have same : second = .int 8 := Except.ok.inj (joined.2.symm.trans actual)
  simpa only [same] using joined

def nativeShadow : Fns := fun _ _ => some (.int 0)

-- Without the notNative premise, emitted dispatch says zero while the actual
-- interpreter selects native integer addition first and returns five.
theorem native_shadow_rejected :
    nativeShadow "BINARY-+" [.int 2, .int 3] = some (.int 0) ∧
    eval nativeShadow [] (.app "BINARY-+" [.quote (.int 2), .quote (.int 3)]) 2 = .ok (.int 5) ∧
    eval nativeShadow [] (.app "BINARY-+" [.quote (.int 2), .quote (.int 3)]) 2 ≠ .ok (.int 0) := by
  refine ⟨rfl, rfl, ?_⟩
  intro wrong
  have impossible : (5 : Int) = 0 := Val.int.inj (Except.ok.inj wrong)
  omega

def truncatedLambda : Term := .lam ["X", "Y"] (.quote (.int 0)) [.quote (.int 1)]

-- Executable zip alone accepts this expression; the closed relation refuses
-- the missing formal, so a lambda composition cannot silently drop arity.
theorem missing_formal_rejected :
    eval emitted [] truncatedLambda 2 = .ok (.int 0) ∧
    ¬ CanonicalEval program domain primitiveDomain [] truncatedLambda (.int 0) := by
  refine ⟨rfl, ?_⟩
  intro accepted
  cases accepted with
  | lam arguments arity evaluated =>
    cases arguments with
    | cons head tail =>
      cases head
      cases tail
      contradiction

#print axioms pipeline_correct
#print axioms native_shadow_rejected
#print axioms missing_formal_rejected
end Fn2.ACL2.Translation.CompositionControls
end
