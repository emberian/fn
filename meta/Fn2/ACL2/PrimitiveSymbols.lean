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

/-- This is the existing MEMBER EQUAL-site domain, not a convenient keyword
restriction. Arbitrary represented objects on the right remain admitted. -/
def symbolEqualDomain (name : String) (values : List Val) : Prop :=
  name = "EQUAL" ∧ ∃ encoded value, values = [.sym encoded, value]

theorem symbol_equal_correspondence :
    PrimitiveCorrespondence equalObjects symbolEqualDomain := by
  intro name objects values represented admitted result evaluated
  obtain ⟨rfl, encoded, value, rfl⟩ := admitted
  cases represented with
  | @cons left _ _ _ leftRep rest =>
    cases rest with
    | @cons right _ _ _ rightRep tail =>
      cases tail
      have reflection : (left = right) ↔ (Val.sym encoded = value) := by
        constructor
        · intro same
          rw [← same] at rightRep
          exact Option.some.inj (leftRep.symm.trans rightRep)
        · intro same
          rw [← same] at rightRep
          exact Option.some.inj ((object_value_symbol_roundtrip leftRep).symm.trans
            (object_value_symbol_roundtrip rightRep))
      by_cases same : Val.sym encoded = value
      · have native : nativeCall "EQUAL" [.sym encoded, value] = some Val.t := by
          change some (Prim.equal (.sym encoded) value) = _
          simp [Prim.equal, Val.ofBool, same]
        have resultEq : Val.t = result := Option.some.inj (native.symm.trans evaluated)
        refine ⟨canonicalTrue, ?_, ?_⟩
        · simp [equalObjects, reflection.mpr same]
        · rw [← resultEq]
          decide
      · have different := fun equal => same (reflection.mp equal)
        have native : nativeCall "EQUAL" [.sym encoded, value] = some Val.nil := by
          change some (Prim.equal (.sym encoded) value) = _
          simp [Prim.equal, Val.ofBool, same]
        have resultEq : Val.nil = result := Option.some.inj (native.symm.trans evaluated)
        refine ⟨canonicalNil, ?_, ?_⟩
        · simp [equalObjects, different]
        · rw [← resultEq]
          decide

#print axioms symbol_equal_correspondence
end Fn2.ACL2.Translation.PrimitiveSymbols
end
