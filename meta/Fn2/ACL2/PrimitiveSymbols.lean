module
public import Fn2.ACL2.CanonicalEvaluation
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveSymbols

def canonicalNil : Object := .symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76]
def canonicalTrue : Object := .symbol [67,79,77,77,79,78,45,76,73,83,80] [84]

/-- ACL2 EQUAL on canonical objects keeps package identity. It must not be
implemented by decoding both arguments and comparing the lossy Val results. -/
def equalObjects : String → List Object → Option Object
  | "EQUAL", [left, right] => some (if left = right then canonicalTrue else canonicalNil)
  | _, _ => none

/-- MEMBER compares its arbitrary key with a symbolic literal list element.
Either symbolic argument suffices; the key need not itself be a symbol. -/
def symbolEqualDomain (name : String) (values : List Val) : Prop :=
  name = "EQUAL" ∧ ∃ left right, values = [left, right] ∧
    ((∃ encoded, left = .sym encoded) ∨ (∃ encoded, right = .sym encoded))

theorem symbol_equal_correspondence :
    PrimitiveCorrespondence equalObjects symbolEqualDomain := by
  intro name objects values represented admitted result evaluated
  obtain ⟨rfl, leftValue, rightValue, rfl, symbolic⟩ := admitted
  cases represented with
  | @cons left _ _ _ leftRep rest =>
    cases rest with
    | @cons right _ _ _ rightRep tail =>
      cases tail
      have reflection : (left = right) ↔ (leftValue = rightValue) := by
        constructor
        · intro same
          rw [← same] at rightRep
          exact Option.some.inj (leftRep.symm.trans rightRep)
        · intro same
          rcases symbolic with ⟨encoded, encodedEq⟩ | ⟨encoded, encodedEq⟩
          · have l := leftRep.trans (congrArg some encodedEq)
            have r := rightRep.trans (congrArg some (same.symm.trans encodedEq))
            exact Option.some.inj ((object_value_symbol_roundtrip l).symm.trans
              (object_value_symbol_roundtrip r))
          · have l := leftRep.trans (congrArg some (same.trans encodedEq))
            have r := rightRep.trans (congrArg some encodedEq)
            exact Option.some.inj ((object_value_symbol_roundtrip l).symm.trans
              (object_value_symbol_roundtrip r))
      by_cases same : leftValue = rightValue
      · have native : nativeCall "EQUAL" [leftValue, rightValue] = some Val.t := by
          change some (Prim.equal leftValue rightValue) = _
          simp [Prim.equal, Val.ofBool, same]
        have resultEq : Val.t = result := Option.some.inj (native.symm.trans evaluated)
        refine ⟨canonicalTrue, ?_, ?_⟩
        · simp [equalObjects, reflection.mpr same]
        · rw [← resultEq]
          decide
      · have different : left ≠ right := fun equality => same (reflection.mp equality)
        have native : nativeCall "EQUAL" [leftValue, rightValue] = some Val.nil := by
          change some (Prim.equal leftValue rightValue) = _
          simp [Prim.equal, Val.ofBool, same]
        have resultEq : Val.nil = result := Option.some.inj (native.symm.trans evaluated)
        refine ⟨canonicalNil, ?_, ?_⟩
        · simp [equalObjects, different]
        · rw [← resultEq]
          decide

/-- Actual PUT-ANSWER compares RC, in this order, to these two keyword values.
No precondition on RC or its eventual reply is inserted. -/
theorem put_answer_comparison_domains (rc : Val) :
    symbolEqualDomain "EQUAL" [rc, .sym ":SIZE"] ∧
    symbolEqualDomain "EQUAL" [rc, .sym ":FULL"] := by
  exact ⟨⟨rfl, rc, .sym ":SIZE", rfl, Or.inr ⟨":SIZE", rfl⟩⟩,
         ⟨rfl, rc, .sym ":FULL", rfl, Or.inr ⟨":FULL", rfl⟩⟩⟩

#print axioms symbol_equal_correspondence
#print axioms put_answer_comparison_domains
end Fn2.ACL2.Translation.PrimitiveSymbols
end
