module

public import Fn2.ACL2.PrimitiveDomains

@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveDomains

/-- Whole premises, canonical result, native result, and represented output. -/
theorem power_positive :
    RelatedArgs (fun (o : Object) (v : Val) => o.value? = some v)
      [.integer 3, .integer 4] [.int 3, .int 4] ∧
    integerPowerDomain "EXPT" [.int 3, .int 4] ∧
    integerPowerObjects "EXPT" [.integer 3, .integer 4] = some (.integer 81) ∧
    nativeCall "EXPT" [.int 3, .int 4] = some (.int 81) ∧
    (Object.integer 81).value? = some (.int 81) :=
  ⟨.cons rfl (.cons rfl .nil), integer_power_result 3 4⟩

/-- Removing the exponent domain admits represented arguments and a native
result, while the canonical integer fragment refuses. The separate rational
identity below explains why broadening this fragment to native zero is false. -/
theorem negative_exponent_domain_required :
    RelatedArgs (fun (o : Object) (v : Val) => o.value? = some v)
      [.integer 2, .integer (-1)] [.int 2, .int (-1)] ∧
    ¬ integerPowerDomain "EXPT" [.int 2, .int (-1)] ∧
    nativeCall "EXPT" [.int 2, .int (-1)] = some (.int 0) ∧
    integerPowerObjects "EXPT" [.integer 2, .integer (-1)] = none := by
  refine ⟨.cons rfl (.cons rfl .nil), ?_, rfl, rfl⟩
  rintro ⟨_, base, exponent, h⟩
  have impossible := congrArg (fun xs => (xs[1]!).toInt) h
  simp [Val.toInt] at impossible

/-- The canonical rational half has no value in the integer adapter, whereas
native completion returns represented zero. The existing Mathlib theorem
`rational_intermediate_not_integer_lowering` is retained unchanged; the paired
ACL2 fixture additionally checks the actual equation EXPT(2,-1)=1/2. -/
theorem negative_exponent_rational_mismatch :
    (Object.rational 1 2).value? = none ∧
    nativeCall "EXPT" [.int 2, .int (-1)] = some (.int 0) ∧
    (Object.integer 0).value? = some (.int 0) := ⟨rfl, rfl, rfl⟩

def changedPowerObjects : String → List Object → Option Object
  | "EXPT", [.integer base, .integer exponent] =>
      if 0 ≤ exponent then some (.integer (base + exponent)) else none
  | _, _ => none

/-- A changed operator cannot pass the same universal correspondence interface,
even though its arguments and output are all supported integers. -/
theorem changed_power_rejected :
    ¬ PrimitiveCorrespondence changedPowerObjects integerPowerDomain := by
  intro claimed
  obtain ⟨result, canonical, represented⟩ := claimed "EXPT"
    [.integer 3, .integer 4] [.int 3, .int 4]
    (.cons rfl (.cons rfl .nil)) ⟨rfl, 3, 4, rfl⟩ (.int 81) rfl
  have result_eq : result = .integer 7 := by simpa [changedPowerObjects] using canonical.symm
  subst result
  cases represented

#print axioms integer_power_correspondence
#print axioms integer_power_result
#print axioms power_positive
#print axioms negative_exponent_domain_required
#print axioms negative_exponent_rational_mismatch
#print axioms changed_power_rejected
end Fn2.ACL2.Translation.PrimitiveDomains
end
