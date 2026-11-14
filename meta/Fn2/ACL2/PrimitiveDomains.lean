module

public import Fn2.ACL2.CanonicalEvaluation
public import Fn2.ACL2.PrimitiveIntegerPower

@[expose] public section

namespace Fn2.ACL2.Translation.PrimitiveDomains

/-- The integer-result fragment of EXPT. Negative exponents are deliberately
outside this relation: in particular 2^-1 is rational, not native integer zero.
This is a partial canonical object specification, not a claim about arbitrary
ACL2 numeric inputs or about all primitive sites of a served function. -/
def integerPowerObjects : String → List Object → Option Object
  | "EXPT", [.integer base, .integer exponent] =>
      if 0 ≤ exponent then some (.integer (base ^ exponent.toNat)) else none
  | _, _ => none

/-- The required premise belongs at each reached EXPT call, including calls in
translated unsigned-byte guards. A lexical occurrence does not discharge it. -/
def integerPowerDomain (name : String) (args : List Val) : Prop :=
  name = "EXPT" ∧ ∃ base : Int, ∃ exponent : Nat,
    args = [.int base, .int exponent]

theorem integer_power_correspondence :
    PrimitiveCorrespondence integerPowerObjects integerPowerDomain := by
  intro name objects values represented admitted result evaluated
  obtain ⟨rfl, base, exponent, rfl⟩ := admitted
  cases represented with
  | cons hb rest =>
    cases rest with
    | cons he tail =>
      cases tail
      cases object_of_value_integer hb
      cases object_of_value_integer he
      have actual : nativeCall "EXPT" [.int base, .int exponent] =
          some (.int (base ^ exponent)) := by
        change some (Native.expt (.int base) (.int exponent)) = _
        rw [PrimitiveContracts.expt_nonnegative]
      have result_eq : .int (base ^ exponent) = result := Option.some.inj (actual.symm.trans evaluated)
      refine ⟨.integer (base ^ exponent), ?_, ?_⟩
      · simp [integerPowerObjects]
      · simpa only [Object.value?] using congrArg some result_eq

/-- The primitive's output is represented, with no additional result-domain
assumption. This can be used by the next call's domain derivation. -/
theorem integer_power_result (base : Int) (exponent : Nat) :
    integerPowerDomain "EXPT" [.int base, .int exponent] ∧
    integerPowerObjects "EXPT" [.integer base, .integer exponent] =
      some (.integer (base ^ exponent)) ∧
    nativeCall "EXPT" [.int base, .int exponent] = some (.int (base ^ exponent)) ∧
    (Object.integer (base ^ exponent)).value? = some (.int (base ^ exponent)) := by
  refine ⟨⟨rfl, base, exponent, rfl⟩, ?_, ?_, rfl⟩
  · simp [integerPowerObjects]
  · change some (Native.expt (.int base) (.int exponent)) = _
    rw [PrimitiveContracts.expt_nonnegative]

end Fn2.ACL2.Translation.PrimitiveDomains
end
