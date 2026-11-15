module

public import Fn2.ACL2.CanonicalEvaluation
public import Fn2.ACL2.Pres

@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveLists

/-- Canonical COMMON-LISP NIL. This does not compare two symbol names or
identify arbitrary package-qualified symbols. -/
def objectNil : Object := .symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76]
def objectCar : Object → Object | .cons a _ => a | _ => objectNil
def objectCdr : Object → Object | .cons _ d => d | _ => objectNil

theorem object_spine_correspondence {object : Object} {value : Val}
    (represented : object.value? = some value) :
    (objectCar object).value? = some value.car ∧
    (objectCdr object).value? = some value.cdr := by
  cases object with
  | integer n => cases represented; exact ⟨rfl,rfl⟩
  | rational n d => cases represented
  | complex r i => cases represented
  | symbol p n =>
    cases he : symbolEncoding? p n with
    | none => simp [Object.value?, Object.symbolValue?, he] at represented
    | some encoded =>
      simp only [Object.value?, Object.symbolValue?, he, Option.bind_some] at represented
      split at represented
      next =>
        cases represented
        exact ⟨rfl, rfl⟩
      next => cases represented
  | character n =>
    simp only [Object.value?] at represented
    split at represented
    · cases represented; exact ⟨rfl,rfl⟩
    · cases represented
  | string cs =>
    cases hs : codeString cs <;> simp [Object.value?, hs] at represented
    cases represented
    exact ⟨rfl,rfl⟩
  | cons a d =>
    cases ha : a.value? <;> cases hd : d.value? <;>
      simp [Object.value?, ha, hd] at represented
    cases represented
    exact ⟨ha,hd⟩

/-- ACL2 list completion, including NIL beyond the spine and NIL padding on
write. The object functions are independent of native Val operations. -/
def objectNth : Nat → Object → Object
  | 0, object => objectCar object
  | n+1, object => objectNth n (objectCdr object)
def objectUpdateNth : Nat → Object → Object → Object
  | 0, value, object => .cons value (objectCdr object)
  | n+1, value, object => .cons (objectCar object) (objectUpdateNth n value (objectCdr object))

theorem nth_correspondence (n : Nat) {object : Object} {value : Val}
    (represented : object.value? = some value) :
    (objectNth n object).value? = some (Native.nthN n value) := by
  induction n generalizing object value with
  | zero => simpa only [objectNth, Pres.nthN_zero] using (object_spine_correspondence represented).1
  | succ n ih =>
    simpa only [objectNth, Pres.nthN_succ] using
      ih (object_spine_correspondence represented).2

theorem update_nth_correspondence (n : Nat) {object inserted : Object} {value newValue : Val}
    (represented : object.value? = some value)
    (insertedRepresented : inserted.value? = some newValue) :
    (objectUpdateNth n inserted object).value? = some (Native.updateNthN n newValue value) := by
  induction n generalizing object value with
  | zero =>
    simp only [objectUpdateNth, Object.value?, insertedRepresented,
      (object_spine_correspondence represented).2, Native.updateNthN]
    rfl
  | succ n ih =>
    simp only [objectUpdateNth, Object.value?, (object_spine_correspondence represented).1,
      ih (object_spine_correspondence represented).2, Native.updateNthN]
    rfl

def listObjects : String → List Object → Option Object
  | "NTH", [.integer index, object] =>
      if 0 ≤ index then some (objectNth index.toNat object) else none
  | "UPDATE-NTH", [.integer index, inserted, object] =>
      if 0 ≤ index then some (objectUpdateNth index.toNat inserted object) else none
  | _, _ => none

def listDomain (name : String) (args : List Val) : Prop :=
  (name = "NTH" ∧ ∃ index : Nat, ∃ value : Val, args = [.int index, value]) ∨
  (name = "UPDATE-NTH" ∧ ∃ index : Nat, ∃ inserted value : Val,
    args = [.int index, inserted, value])

/-- Recover the natural index from the selected INTEGERP/nonnegative branches
of a translated NATP check. Consumers must supply these reached branch facts;
this lemma does not assume a guard merely because its source declares one. -/
theorem natural_index_of_guard_branches (index : Val)
    (integer : (Prim.integerp index).truthy = true)
    (nonnegative : (Prim.lt index (.int 0)).truthy = false) :
    ∃ n : Nat, index = .int n := by
  cases index with
  | int i =>
    have hn : ¬ i < 0 := by
      intro negative
      have selected : (Prim.lt (.int i) (.int 0)).truthy = true := by
        change (Val.ofBool (decide (i < 0))).truthy = true
        rw [show decide (i < 0) = true by simp [negative]]
        rfl
      have impossible : true = false := selected.symm.trans nonnegative
      cases impossible
    have hi : 0 ≤ i := by omega
    exact ⟨i.toNat, congrArg Val.int (Int.toNat_of_nonneg hi).symm⟩
  | _ => simp [Prim.integerp, Val.isInt, Val.ofBool, Val.truthy, Val.nil] at integer

theorem nth_domain_of_guard_branches (index value : Val)
    (integer : (Prim.integerp index).truthy = true)
    (nonnegative : (Prim.lt index (.int 0)).truthy = false) :
    listDomain "NTH" [index, value] := by
  obtain ⟨n, rfl⟩ := natural_index_of_guard_branches index integer nonnegative
  exact Or.inl ⟨rfl, n, value, rfl⟩

theorem update_nth_domain_of_guard_branches (index inserted value : Val)
    (integer : (Prim.integerp index).truthy = true)
    (nonnegative : (Prim.lt index (.int 0)).truthy = false) :
    listDomain "UPDATE-NTH" [index, inserted, value] := by
  obtain ⟨n, rfl⟩ := natural_index_of_guard_branches index integer nonnegative
  exact Or.inr ⟨rfl, n, inserted, value, rfl⟩

theorem list_primitive_correspondence : PrimitiveCorrespondence listObjects listDomain := by
  intro name objects values represented admitted result evaluated
  rcases admitted with ⟨rfl, index, value, rfl⟩ | ⟨rfl, index, inserted, value, rfl⟩
  · cases represented with
    | cons hi rest =>
      cases rest with
      | cons ho tail =>
        cases tail
        cases object_of_value_integer hi
        rename_i object
        have actual : nativeCall "NTH" [.int index, value] = some (Native.nthN index value) := by
          change some (Native.nth (.int index) value) = _
          simp [Native.nth, Val.nfix, Val.toInt]
        have result_eq := Option.some.inj (actual.symm.trans evaluated)
        refine ⟨objectNth index object, ?_, ?_⟩
        · simp [listObjects]
        · simpa only [result_eq] using nth_correspondence index ho
  · cases represented with
    | cons hi rest =>
      cases rest with
      | cons hn rest =>
        cases rest with
        | cons ho tail =>
          cases tail
          cases object_of_value_integer hi
          rename_i insertedObject object
          have actual : nativeCall "UPDATE-NTH" [.int index, inserted, value] =
              some (Native.updateNthN index inserted value) := by
            change some (Native.updateNth (.int index) inserted value) = _
            simp [Native.updateNth, Val.nfix, Val.toInt]
          have result_eq := Option.some.inj (actual.symm.trans evaluated)
          refine ⟨objectUpdateNth index insertedObject object, ?_, ?_⟩
          · simp [listObjects]
          · simpa only [result_eq] using update_nth_correspondence index ho hn

end Fn2.ACL2.Translation.PrimitiveLists
end
