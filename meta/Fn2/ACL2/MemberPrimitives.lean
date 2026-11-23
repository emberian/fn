module

public import Fn2.ACL2.PrimitiveLists
public import Fn2.ACL2.PrimitiveSymbols
public import Fn2.ACL2.MemberExecEvaluation
public import Fn2.ACL2.CanonicalGuardControls
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

namespace Fn2.ACL2.Translation.MemberPrimitives
open Fn2.ACL2 Fn2.ACL2.Translation
open Fn2.ACL2.Translation.PrimitiveLists Fn2.ACL2.Translation.PrimitiveSymbols

def objectConsp : Object → Object
  | .cons _ _ => canonicalTrue
  | _ => canonicalNil

def objectIntegerp : Object → Object
  | .integer _ => canonicalTrue
  | _ => canonicalNil

private theorem canonicalNil_value : canonicalNil.value? = some Val.nil := by decide +kernel
private theorem canonicalTrue_value : canonicalTrue.value? = some Val.t := by decide +kernel

theorem consp_correspondence {object : Object} {value : Val}
    (represented : object.value? = some value) :
    (objectConsp object).value? = some (Prim.consp value) := by
  cases object with
  | integer n =>
    cases represented
    exact canonicalNil_value
  | rational n d => cases represented
  | complex r i => cases represented
  | symbol p n =>
    cases he : symbolEncoding? p n with
    | none => simp [Object.value?, Object.symbolValue?, he] at represented
    | some encoded =>
      simp only [Object.value?, Object.symbolValue?, he] at represented
      change (if symbolObject? encoded = some (.symbol p n)
        then some (Val.sym encoded) else none) = some value at represented
      split at represented
      next =>
        cases represented
        exact canonicalNil_value
      next => cases represented
  | character n =>
    simp only [Object.value?] at represented
    split at represented
    · cases represented; exact canonicalNil_value
    · cases represented
  | string cs =>
    cases hs : codeString cs <;> simp [Object.value?, hs] at represented
    cases represented
    exact canonicalNil_value
  | cons a d =>
    cases ha : a.value? <;> cases hd : d.value? <;>
      simp [Object.value?, ha, hd] at represented
    cases represented
    exact canonicalTrue_value

theorem integerp_correspondence {object : Object} {value : Val}
    (represented : object.value? = some value) :
    (objectIntegerp object).value? = some (Prim.integerp value) := by
  cases object with
  | integer n =>
    cases represented
    exact canonicalTrue_value
  | rational n d => cases represented
  | complex r i => cases represented
  | symbol p n =>
    cases he : symbolEncoding? p n with
    | none => simp [Object.value?, Object.symbolValue?, he] at represented
    | some encoded =>
      simp only [Object.value?, Object.symbolValue?, he] at represented
      change (if symbolObject? encoded = some (.symbol p n)
        then some (Val.sym encoded) else none) = some value at represented
      split at represented
      next =>
        cases represented
        exact canonicalNil_value
      next => cases represented
  | character n =>
    simp only [Object.value?] at represented
    split at represented
    · cases represented; exact canonicalNil_value
    · cases represented
  | string cs =>
    cases hs : codeString cs <;> simp [Object.value?, hs] at represented
    cases represented
    exact canonicalNil_value
  | cons a d =>
    cases ha : a.value? <;> cases hd : d.value? <;>
      simp [Object.value?, ha, hd] at represented
    cases represented
    exact canonicalNil_value

/-- Canonical object model for cons spines, type predicates, and symbolic equality. -/
def consSpineObjects : String → List Object → Option Object
  | "CONS", [a, d] => some (.cons a d)
  | "CAR", [o] => some (objectCar o)
  | "CDR", [o] => some (objectCdr o)
  | "CONSP", [o] => some (objectConsp o)
  | "INTEGERP", [o] => some (objectIntegerp o)
  | "EQUAL", [left, right] => equalObjects "EQUAL" [left, right]
  | _, _ => none

def consSpineDomain (name : String) (values : List Val) : Prop :=
  (name = "CONS" ∧ ∃ a d, values = [a, d]) ∨
  (name = "CAR" ∧ ∃ v, values = [v]) ∨
  (name = "CDR" ∧ ∃ v, values = [v]) ∨
  (name = "CONSP" ∧ ∃ v, values = [v]) ∨
  (name = "INTEGERP" ∧ ∃ v, values = [v]) ∨
  symbolEqualDomain name values

theorem cons_spine_correspondence : PrimitiveCorrespondence consSpineObjects consSpineDomain := by
  intro name objects values represented admitted result evaluated
  rcases admitted with
    ⟨rfl, a, d, rfl⟩ | ⟨rfl, v, rfl⟩ | ⟨rfl, v, rfl⟩ |
    ⟨rfl, v, rfl⟩ | ⟨rfl, v, rfl⟩ | hEq
  · cases represented with
    | @cons ao _ _ _ ha rest =>
      cases rest with
      | @cons do_ _ _ _ hd tail =>
        cases tail
        have actual : nativeCall "CONS" [a, d] = some (.cons a d) := rfl
        have result_eq := Option.some.inj (actual.symm.trans evaluated)
        refine ⟨.cons ao do_, rfl, ?_⟩
        simp [Object.value?, ha, hd, result_eq]
  · cases represented with
    | @cons o _ _ _ ho tail =>
      cases tail
      have actual : nativeCall "CAR" [v] = some v.car := rfl
      have result_eq := Option.some.inj (actual.symm.trans evaluated)
      exact ⟨objectCar o, rfl, result_eq ▸ (object_spine_correspondence ho).1⟩
  · cases represented with
    | @cons o _ _ _ ho tail =>
      cases tail
      have actual : nativeCall "CDR" [v] = some v.cdr := rfl
      have result_eq := Option.some.inj (actual.symm.trans evaluated)
      exact ⟨objectCdr o, rfl, result_eq ▸ (object_spine_correspondence ho).2⟩
  · cases represented with
    | @cons o _ _ _ ho tail =>
      cases tail
      have actual : nativeCall "CONSP" [v] = some (Prim.consp v) := rfl
      have result_eq := Option.some.inj (actual.symm.trans evaluated)
      exact ⟨objectConsp o, rfl, result_eq ▸ consp_correspondence ho⟩
  · cases represented with
    | @cons o _ _ _ ho tail =>
      cases tail
      have actual : nativeCall "INTEGERP" [v] = some (Prim.integerp v) := rfl
      have result_eq := Option.some.inj (actual.symm.trans evaluated)
      exact ⟨objectIntegerp o, rfl, result_eq ▸ integerp_correspondence ho⟩
  · obtain ⟨rfl, leftVal, rightVal, rfl, hsym⟩ := hEq
    obtain ⟨objRes, hObj, hVal⟩ :=
      symbol_equal_correspondence "EQUAL" objects [leftVal, rightVal] represented
        ⟨rfl, leftVal, rightVal, rfl, hsym⟩ result evaluated
    cases represented with
    | cons _ rest =>
      cases rest with
      | cons _ tail =>
        cases tail
        exact ⟨objRes, hObj, hVal⟩

theorem member_primitive_domain_sub (name : String) (values : List Val)
    (h : Fn2.ACL2.MemberExecEvaluation.primitiveDomain name values) :
    consSpineDomain name values := by
  unfold Fn2.ACL2.MemberExecEvaluation.primitiveDomain at h
  split at h
  · rename_i v; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, v, rfl⟩)))
  · rename_i k v; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, .sym k, v, rfl, Or.inl ⟨k, rfl⟩⟩))))
  · rename_i a d; exact Or.inr (Or.inl ⟨rfl, .cons a d, rfl⟩)
  · rename_i a d; exact Or.inr (Or.inr (Or.inl ⟨rfl, .cons a d, rfl⟩))
  · cases h

/-- Discharges `PrimitiveCorrespondence` for the entire primitive call domain of `MemberExecEvaluation`. -/
theorem member_primitive_correspondence :
    PrimitiveCorrespondence consSpineObjects Fn2.ACL2.MemberExecEvaluation.primitiveDomain :=
  fun name objects values represented admitted result evaluated =>
    cons_spine_correspondence name objects values represented
      (member_primitive_domain_sub name values admitted) result evaluated

/-- Discharges `PrimitiveCorrespondence` for `GuardControls.guardPrimitives` (`INTEGERP`). -/
theorem guard_primitive_correspondence :
    PrimitiveCorrespondence consSpineObjects GuardControls.guardPrimitives := by
  intro name objects values represented admitted result evaluated
  obtain ⟨rfl, x, rfl⟩ := admitted
  exact cons_spine_correspondence "INTEGERP" objects [.int x] represented
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, .int x, rfl⟩))))) result evaluated

def sampleKeyObj : Object := .symbol [75, 69, 89, 87, 79, 82, 68] [79, 75]
def sampleCellObj : Object := .cons sampleKeyObj canonicalNil
def sampleCellVal : Val := .cons (.sym ":OK") Val.nil

/-- Positive witness: whole antecedent and conclusion hold across `CONSP`, `CAR`, `CDR`, and `EQUAL`. -/
theorem member_primitive_positive :
    sampleCellObj.value? = some sampleCellVal ∧
    Fn2.ACL2.MemberExecEvaluation.primitiveDomain "CONSP" [sampleCellVal] ∧
    Fn2.ACL2.MemberExecEvaluation.primitiveDomain "CAR" [sampleCellVal] ∧
    Fn2.ACL2.MemberExecEvaluation.primitiveDomain "CDR" [sampleCellVal] ∧
    Fn2.ACL2.MemberExecEvaluation.primitiveDomain "EQUAL" [.sym ":OK", .sym ":OK"] ∧
    consSpineObjects "CONSP" [sampleCellObj] = some canonicalTrue ∧
    consSpineObjects "CAR" [sampleCellObj] = some sampleKeyObj ∧
    consSpineObjects "CDR" [sampleCellObj] = some canonicalNil ∧
    consSpineObjects "EQUAL" [sampleKeyObj, sampleKeyObj] = some canonicalTrue :=
  ⟨by decide +kernel, trivial, trivial, trivial, trivial, rfl, rfl, rfl, rfl⟩

/-- Mutant: treating `NIL` as a cons breaks `PrimitiveCorrespondence` on `MemberExecEvaluation.primitiveDomain`. -/
def flippedConspObjects : String → List Object → Option Object
  | "CONSP", [_] => some canonicalTrue
  | name, args => consSpineObjects name args

theorem flipped_consp_mutant_rejected :
    ¬ PrimitiveCorrespondence flippedConspObjects Fn2.ACL2.MemberExecEvaluation.primitiveDomain := by
  intro claimed
  obtain ⟨res, hObj, hVal⟩ := claimed "CONSP" [canonicalNil] [Val.nil]
    (.cons (by decide +kernel) .nil) trivial Val.nil rfl
  have hEq : res = canonicalTrue := Option.some.inj hObj.symm
  subst hEq
  have bad : (canonicalTrue.value? == some Val.nil) = false := by decide +kernel
  rw [hVal] at bad
  cases bad

/-- Hypothesis-removal witness: `CONS` requires both elements to be represented in `Val`. -/
theorem unrepresented_cons_element_rejected :
    (Object.rational 1 2).value? = none ∧
    canonicalNil.value? = some Val.nil ∧
    (Object.cons (.rational 1 2) canonicalNil).value? = none :=
  ⟨rfl, by decide +kernel, rfl⟩

end Fn2.ACL2.Translation.MemberPrimitives

end
