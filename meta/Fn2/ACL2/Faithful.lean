import Fn2.Instances.LayerAWorld

/-!
# Fn2.ACL2.Faithful: the natives satisfy ACL2's definitions

The embedding trusts two things beyond the reader: ACL2's primitives (`Fn2.ACL2.Prim`, with
ACL2's completions) and the natives (`Fn2.ACL2.Native`), the built-ins the emitter does not
translate. For each native whose ACL2 definition stays inside the subset, the emitter prints that
definition as `«F».acl2`, its body read like any other but with every native call, the native's
own recursive calls included, going to the Lean natives. `Faithful f g` then says the native
satisfies ACL2's defining equation; ACL2 admitted that equation with a measure, so it has one
solution, and the native is ACL2's function.

Proved here: `NTH`, `MV-NTH`, `UPDATE-NTH`, `LEN`, `MEMBER-EQUAL`, `LOGNOT`, `MOD` and
`NONNEGATIVE-INTEGER-QUOTIENT`. Owed (stated, `nativeOwed`): the bitwise natives `BINARY-LOGIOR`,
`BINARY-LOGXOR`, `BINARY-LOGEQV` and `LOGORC1`, whose definitions are in terms of
`BINARY-LOGAND`, itself outside the subset (`nativeOutside`: its definition calls `ZIP` and
recurses through `FLOOR`); `FLOOR`, `EVENP`, `EXPT` and `ACL2-COUNT` are defined through ACL2's
rationals and are trusted as written.
-/

namespace Fn2.ACL2.Faithful
open Fn2.ACL2 Fn2.Instances.LayerAWorld

/-- A unary native agrees with ACL2's definition on every argument. -/
def Faithful1 (native acl2 : Val → Val) : Prop := ∀ a, native a = acl2 a
def Faithful2 (native acl2 : Val → Val → Val) : Prop := ∀ a b, native a b = acl2 a b
def Faithful3 (native acl2 : Val → Val → Val → Val) : Prop := ∀ a b c, native a b c = acl2 a b c

/-- The natives whose ACL2 definitions are inside the subset but whose agreement is not yet
proved here. -/
def nativeOwed : List String := ["BINARY-LOGIOR", "BINARY-LOGXOR", "BINARY-LOGEQV", "LOGORC1"]

section
@[simp] theorem truthy_ofBool (b : Bool) : (Val.ofBool b).truthy = b := by cases b <;> rfl
@[simp] theorem truthy_t : Val.t.truthy = true := rfl
@[simp] theorem truthy_nil : Val.nil.truthy = false := rfl
@[simp] theorem truthy_int (i : Int) : (Val.int i).truthy = true := rfl
@[simp] theorem truthy_cons (a d : Val) : (Val.cons a d).truthy = true := rfl
@[simp] theorem truthy_ite (c : Prop) [Decidable c] (a b : Val) :
    (if c then a else b).truthy = if c then a.truthy else b.truthy := by split <;> rfl

attribute [local simp] Val.car Val.cdr Val.nfix Val.toInt
  Prim.consp Prim.integerp Prim.lt Prim.plus Prim.neg Prim.times Prim.equal Val.isCons Val.isInt
  «NOT» «ATOM» «ENDP» «ZP» «IFIX» «NFIX» «=»

theorem nth_faithful : Faithful2 Native.nth «NTH».acl2 := by
  intro n l
  cases l with
  | cons a d =>
    cases n with
    | int i =>
      by_cases h : 0 < i
      · have : i.toNat = (-1 + i).toNat + 1 := by omega
        simp [«NTH».acl2, Native.nth, h, this, Native.nthN]
      · have : i.toNat = 0 := by omega
        simp [«NTH».acl2, Native.nth, h, this, Native.nthN]
    | _ => simp [«NTH».acl2, Native.nth, Native.nthN]
  | _ => simp [«NTH».acl2, Native.nth, Native.nthN]

theorem mv_nth_faithful : Faithful2 Native.nth «MV-NTH».acl2 := by
  intro n l
  rw [nth_faithful]
  cases l <;> simp [«NTH».acl2, «MV-NTH».acl2]

theorem update_nth_faithful : Faithful3 Native.updateNth «UPDATE-NTH».acl2 := by
  intro k v l
  cases k with
  | int i =>
    by_cases h : 0 < i
    · have : i.toNat = (-1 + i).toNat + 1 := by omega
      simp [«UPDATE-NTH».acl2, Native.updateNth, h, this, Native.updateNthN]
    · have : i.toNat = 0 := by omega
      simp [«UPDATE-NTH».acl2, Native.updateNth, h, this, Native.updateNthN]
  | _ => simp [«UPDATE-NTH».acl2, Native.updateNth, Native.updateNthN]

theorem len_go (n : Nat) (l : Val) : Native.len.go n l = n + Native.len.go 0 l := by
  induction l generalizing n with
  | cons a d _ ihd =>
    simp only [Native.len.go]
    rw [ihd (n + 1), ihd (0 + 1)]
    omega
  | _ => simp [Native.len.go]

theorem len_faithful : Faithful1 Native.len «LEN».acl2 := by
  intro l
  cases l with
  | cons a d =>
    simp only [Native.len, «LEN».acl2, Native.len.go]
    rw [len_go]
    simp
  | _ => simp [Native.len, «LEN».acl2, Native.len.go]

theorem member_equal_faithful : Faithful2 Native.memberEqual «MEMBER-EQUAL».acl2 := by
  intro x l
  cases l with
  | cons a d =>
    by_cases h : x = a
    · subst h; simp [Native.memberEqual, «MEMBER-EQUAL».acl2]
    · simp [Native.memberEqual, «MEMBER-EQUAL».acl2, h]
  | _ => simp [Native.memberEqual, «MEMBER-EQUAL».acl2]

theorem lognot_faithful : Faithful1 Native.lognot «LOGNOT».acl2 := by
  intro a
  cases a <;> simp [Native.lognot, «LOGNOT».acl2] <;> omega

theorem floor_int (a b : Val) : ∃ q, Native.floor a b = .int q := by
  unfold Native.floor; dsimp only; split <;> exact ⟨_, rfl⟩

theorem mod_faithful : Faithful2 Native.mod «MOD».acl2 := by
  intro a b
  obtain ⟨q, hq⟩ := floor_int a b
  simp only [Native.mod, «MOD».acl2, Prim.plus, Prim.neg, Prim.times, hq, Val.toInt]
  congr 1
  rw [Int.mul_comm]; omega

theorem niq_faithful : Faithful2 Native.niq «NONNEGATIVE-INTEGER-QUOTIENT».acl2 := by
  intro i j
  cases i with
  | int a =>
    cases j with
    | int b =>
      by_cases hb : 0 < b
      · by_cases ha : a < b
        · by_cases ha0 : a < 0
          · simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2, ha, ha0]
          · have : a / b = 0 := Int.ediv_eq_zero_of_lt (by omega) ha
            simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2, ha, ha0, this]
        · have hd : (a + -b) / b = a / b + -1 := by
            have := Int.add_mul_ediv_left a (-1) (show b ≠ 0 by omega)
            rw [show a + b * -1 = a + -b by omega] at this
            exact this
          simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2, ha]
          simp only [show ¬ (b ≤ 0 ∨ a < 0) by omega,
            show ¬ ((b < 0 ∨ b = 0) ∧ (0 ≤ b → b = 0)) by omega,
            show ¬ (b ≤ 0 ∨ a + -b < 0) by omega, if_false, hd]
          congr 1; omega
      · simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2]
        simp only [show (b ≤ 0 ∨ a < 0) by omega, if_true]
        rw [if_pos (by omega)]
    | _ => simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2]
  | _ =>
    cases j <;> simp [Native.niq, «NONNEGATIVE-INTEGER-QUOTIENT».acl2] <;> omega

end

end Fn2.ACL2.Faithful
