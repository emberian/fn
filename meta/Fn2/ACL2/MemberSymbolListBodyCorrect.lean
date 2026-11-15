module
public import Fn2.ACL2.MemberBodyCorrect
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.MemberSymbolListBodyCorrect
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

def result (values : List Val) (value : Val) : Prop :=
  ∃ key names, values = [key, Val.ofList (names.map Val.sym)] ∧
    value = Native.memberEqual key (Val.ofList (names.map Val.sym))

theorem member_domain_witness {values : List Val}
    (admitted : domain "MEMBER-EQ-EXEC" values) :
    ∃ key names, values = [key, Val.ofList (names.map Val.sym)] := by
  cases values with
  | nil => simp [domain] at admitted
  | cons key tail =>
    cases tail with
    | nil => simp [domain] at admitted
    | cons lst tail =>
      cases tail with
      | cons y ys => simp [domain] at admitted
      | nil => obtain ⟨names, rfl⟩ := admitted; exact ⟨key, names, rfl⟩

/-- Same exact canonical records, concrete global dispatcher and fuel32 as the
existing certificate; only the complementary input domain is new. -/
theorem body_correct :
    CanonicalBodyCorrect program domain primitiveDomain fns "MEMBER-EQ-EXEC" result := by
  intro values admitted
  obtain ⟨key, names, rfl⟩ := member_domain_witness admitted
  refine ⟨memberDefinition, «MEMBER-EQ-EXEC» key (Val.ofList (names.map Val.sym)),
    rfl, rfl, ?_, «MEMBER-EQ-EXEC».fns_eq _ _, MemberBodyCorrect.eval_export_32 _ _,
    ⟨key, names, rfl, MemberBodyCorrect.emitted_eq_native _ _⟩⟩
  rw [MemberBodyCorrect.emitted_eq_native]
  exact closed_evaluation key names

/-- The actual reached MEMBER call: arbitrary RC, literal symbols, same result
for closed evaluation, emitted interpreter and the membership postcondition. -/
theorem literal_call (rc : Val) (names : List String) :
    ∃ value,
      CanonicalEval program domain primitiveDomain [("RC", rc)]
        (.app "MEMBER-EQ-EXEC" [.var "RC", .quote (Val.ofList (names.map Val.sym))]) value ∧
      eval fns [("RC", rc)]
        (.app "MEMBER-EQ-EXEC" [.var "RC", .quote (Val.ofList (names.map Val.sym))]) 33 = .ok value ∧
      result [rc, Val.ofList (names.map Val.sym)] value := by
  apply canonical_call_correct (name := "MEMBER-EQ-EXEC")
    (values := [rc, Val.ofList (names.map Val.sym)]) (fuel := 32)
  · decide
  · decide
  · rfl
  · exact .cons (.var rfl) (.cons .quote .nil)
  · rfl
  · exact ⟨names, rfl⟩
  · exact body_correct

/-- Preserve the exact literal values selected from the canonical packet;
Lean infers their symbol names from the equality, rather than Python recoding them. -/
theorem literal_values_call (rc : Val) (literals : List Val)
    (symbols : ∃ names : List String, literals = names.map Val.sym) :
    ∃ value,
      CanonicalEval program domain primitiveDomain [("RC", rc)]
        (.app "MEMBER-EQ-EXEC" [.var "RC", .quote (Val.ofList literals)]) value ∧
      eval fns [("RC", rc)]
        (.app "MEMBER-EQ-EXEC" [.var "RC", .quote (Val.ofList literals)]) 33 = .ok value ∧
      result [rc, Val.ofList literals] value := by
  obtain ⟨names, rfl⟩ := symbols
  exact literal_call rc names

#print axioms closed_evaluation
#print axioms body_correct
#print axioms literal_call
#print axioms literal_values_call
end Fn2.ACL2.MemberSymbolListBodyCorrect
end
