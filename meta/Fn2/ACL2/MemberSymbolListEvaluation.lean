module
public import Fn2.ACL2.MemberExecEvaluation
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.MemberSymbolListEvaluation
open Fn2.ACL2.Translation Fn2.Instances.LayerAWorld
open MemberExecEvaluation (program notDefinition atomDefinition endpDefinition eqDefinition
  memberDefinition notTerm atomTerm endpTerm eqTerm memberTerm
  not_decoded atom_decoded endp_decoded eq_decoded member_decoded)

/-! Complementary domain for the actual CNS PUT-ANSWER comparison: RC is
arbitrary, but each list element is a symbol. Existing symbol-key certificates
remain unchanged. Canonical object representation and live packet binding are
separate obligations; arbitrary encoded symbol names are not presumed valid. -/
def domain : CallDomain
  | "NOT", [_] => True
  | "ATOM", [_] => True
  | "ENDP", [v] => ∃ xs, v = Val.ofList xs
  | "EQ", [_, .sym _] => True
  | "MEMBER-EQ-EXEC", [_, v] => ∃ names : List String, v = Val.ofList (names.map Val.sym)
  | _, _ => False

def primitiveDomain : CallDomain
  | "CONSP", [_] => True
  | "EQUAL", [_, .sym _] => True
  | "CAR", [.cons _ _] => True
  | "CDR", [.cons _ _] => True
  | _, _ => False

theorem not_evaluates (v : Val) :
    CanonicalExportEval program domain primitiveDomain "NOT" [v]
      (if v.truthy then Val.nil else Val.t) := by
  refine ⟨notDefinition, notTerm, rfl, trivial, rfl, not_decoded, ?_⟩
  cases h : v.truthy
  · exact .if_false (.var rfl) h .quote
  · exact .if_true (.var rfl) h .quote

theorem atom_evaluates (v : Val) :
    CanonicalExportEval program domain primitiveDomain "ATOM" [v]
      (if v.isCons then Val.nil else Val.t) := by
  refine ⟨atomDefinition, atomTerm, rfl, trivial, rfl, atom_decoded, ?_⟩
  have hc : CanonicalEval program domain primitiveDomain [("X", v)]
      (.app "CONSP" [.var "X"]) (Prim.consp v) :=
    .primitive (by decide) (by decide) (.cons (.var rfl) .nil) trivial rfl
  have hn := canonical_call_of_export (actuals := [.app "CONSP" [.var "X"]])
    (by decide : "NOT" ≠ "IF") (by decide : "NOT" ≠ "RETURN-LAST")
    (.cons hc .nil) (nativeCall_none _ _ (by decide +kernel)) (not_evaluates (Prim.consp v))
  cases h : v.isCons <;>
    simpa [Prim.consp, h, Val.ofBool, Val.truthy, Val.nil, Val.t] using hn

theorem endp_evaluates (xs : List Val) :
    CanonicalExportEval program domain primitiveDomain "ENDP" [Val.ofList xs]
      (if (Val.ofList xs).isCons then Val.nil else Val.t) := by
  refine ⟨endpDefinition, endpTerm, rfl, ⟨xs, rfl⟩, rfl, endp_decoded, ?_⟩
  exact canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
    (nativeCall_none _ _ (by decide +kernel)) (atom_evaluates _)

theorem eq_evaluates (key : Val) (v : String) :
    CanonicalExportEval program domain primitiveDomain "EQ" [key, .sym v]
      (Prim.equal key (.sym v)) := by
  refine ⟨eqDefinition, eqTerm, rfl, trivial, rfl, eq_decoded, ?_⟩
  exact .primitive (by decide) (by decide)
    (.cons (.var rfl) (.cons (.var rfl) .nil)) trivial rfl

theorem closed_evaluation (key : Val) (xs : List String) :
    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"
      [key, Val.ofList (xs.map Val.sym)] (Native.memberEqual (key) (Val.ofList (xs.map Val.sym))) := by
  induction xs with
  | nil =>
    refine ⟨memberDefinition, memberTerm, rfl, ⟨[], rfl⟩, rfl, member_decoded, ?_⟩
    apply CanonicalEval.if_true
      (canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
        (nativeCall_none _ _ (by decide +kernel)) (endp_evaluates []))
    · rfl
    · exact .quote
  | cons head tail ih =>
    refine ⟨memberDefinition, memberTerm, rfl, ⟨head :: tail, rfl⟩, rfl, member_decoded, ?_⟩
    apply CanonicalEval.if_false
      (canonical_call_of_export (by decide) (by decide) (.cons (.var rfl) .nil)
        (nativeCall_none _ _ (by decide +kernel)) (endp_evaluates ((head :: tail).map Val.sym)))
    · rfl
    · have carEval : CanonicalEval program domain primitiveDomain
          [("X", key), ("LST", Val.ofList ((head :: tail).map Val.sym))]
          (.app "CAR" [.var "LST"]) (.sym head) :=
        .primitive (by decide) (by decide) (.cons (.var rfl) .nil) trivial rfl
      have eqEval := canonical_call_of_export (actuals := [.var "X", .app "CAR" [.var "LST"]]) (env := [("X", key), ("LST", Val.ofList ((head :: tail).map Val.sym))])
        (by decide : "EQ" ≠ "IF") (by decide : "EQ" ≠ "RETURN-LAST")
        (.cons (.var rfl) (.cons carEval .nil))
        (nativeCall_none _ _ (by decide +kernel)) (eq_evaluates key head)
      cases h : (key == Val.sym head)
      · simp only [List.map, Val.ofList, Native.memberEqual, h, Bool.false_eq_true, ↓reduceIte]
        apply CanonicalEval.if_false eqEval
        · simp [Prim.equal, h, Val.ofBool, Val.truthy, Val.nil]
        · exact canonical_call_of_export (by decide) (by decide)
            (.cons (.var rfl) (.cons (.primitive (by decide) (by decide)
              (.cons (.var rfl) .nil) trivial rfl) .nil))
            (nativeCall_none _ _ (by decide +kernel)) ih
      · simp only [List.map, Val.ofList, Native.memberEqual, h, ↓reduceIte]
        apply CanonicalEval.if_true eqEval
        · simp [Prim.equal, h, Val.ofBool, Val.truthy, Val.t]
        · exact .var rfl

/-- The result is the actual generated recursive MEMBER function, not an
arbitrary dispatcher. The complete global-dispatch body join is separate. -/
theorem emitted_eq_native (x lst : Val) :
    «MEMBER-EQ-EXEC» x lst = Native.memberEqual x lst := by
  obtain ⟨result, run, emitted⟩ := MemberExecEvaluation.adequate_emitted x lst
  have solved := Countdown.equals_solution MemberExecEvaluation.measure
    MemberExecEvaluation.step MemberExecEvaluation.decreases
    (fun a => Native.memberEqual a.1 a.2)
    (by
      intro a
      have h := MemberExecEvaluation.solution_equation a
      cases hs : MemberExecEvaluation.step a <;> simpa only [hs] using h)
    (MemberExecEvaluation.measure (x, lst) + 1) (x, lst) (by omega)
  exact emitted.symm.trans (Except.ok.inj ((run _ (by omega)).symm.trans solved))

theorem closed_adequate_emitted (key : Val) (names : List String) :
    domain "MEMBER-EQ-EXEC" [key, Val.ofList (names.map Val.sym)] ∧
    CanonicalExportEval program domain primitiveDomain "MEMBER-EQ-EXEC"
      [key, Val.ofList (names.map Val.sym)]
      («MEMBER-EQ-EXEC» key (Val.ofList (names.map Val.sym))) := by
  refine ⟨⟨names, rfl⟩, ?_⟩
  rw [emitted_eq_native]
  exact closed_evaluation key names

#print axioms closed_evaluation
#print axioms emitted_eq_native
#print axioms closed_adequate_emitted
end Fn2.ACL2.MemberSymbolListEvaluation
end
