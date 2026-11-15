module
public import Fn2.ACL2.MemberBodyCorrect
public import Fn2.ACL2.MemberSymbolListEvaluation
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
open MemberExecEvaluation (program memberDefinition)
abbrev domain := MemberSymbolListEvaluation.domain
abbrev primitiveDomain := MemberSymbolListEvaluation.primitiveDomain

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
  exact MemberSymbolListEvaluation.closed_evaluation key names

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

#print axioms body_correct
#print axioms literal_call
#print axioms literal_values_call
end Fn2.ACL2.MemberSymbolListBodyCorrect
end
