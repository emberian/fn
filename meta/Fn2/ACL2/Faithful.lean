module

public import Fn2.Instances.LayerAWorld.Natives
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
-- BEGIN world bodies (emit_embed.py): natives; scan
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Fn2.Instances.LayerAWorld.S17_d1
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S15xc66772_d1to9
import all Fn2.Instances.LayerAWorld.S14_d0to1
import all Fn2.Instances.LayerAWorld.S11_d0to10
import all Fn2.Instances.LayerAWorld.KBoot_d0to29
import all Fn2.Instances.LayerAWorld.Rest_d1to5
import all Fn2.Instances.LayerAWorld.Natives
-- END world bodies

@[expose] public section

/-!
# Fn2.ACL2.Faithful: the natives satisfy ACL2's definitions

The embedding trusts two things beyond the reader: ACL2's primitives (`Fn2.ACL2.Prim`, with
ACL2's completions) and the natives (`Fn2.ACL2.Native`), the built-ins the emitter does not
translate. For each native whose ACL2 definition stays inside the subset, the emitter prints that
definition as `«F».acl2`, its body read like any other but with every native call, the native's
own recursive calls included, going to the Lean natives. `Faithful f g` then says the native
satisfies ACL2's defining equation; ACL2 admitted that equation with a measure, so it has one
solution, and the native is ACL2's function.

Proved here: `NTH`, `MV-NTH`, `UPDATE-NTH`, `LEN`, `MEMBER-EQUAL`, `LOGNOT`, `MOD`,
`NONNEGATIVE-INTEGER-QUOTIENT`, `BINARY-LOGIOR`, `BINARY-LOGXOR`, `BINARY-LOGEQV` and `LOGORC1`
(`nativeOwed = []`). `BINARY-LOGAND` is outside the subset (`nativeOutside`: its definition calls
`ZIP` and recurses through `FLOOR`); `FLOOR`, `EVENP`, `EXPT` and `ACL2-COUNT` are defined through
ACL2's rationals and are trusted as written, and so is `ASH`, whose definition
`(floor (* (ifix i) (expt 2 c)) 1)` passes through the rational `(expt 2 c)` for `c < 0`.
-/

namespace Fn2.ACL2.Faithful
open Fn2.ACL2 Fn2.Instances.LayerAWorld

/-- A unary native agrees with ACL2's definition on every argument. -/
def Faithful1 (native acl2 : Val → Val) : Prop := ∀ a, native a = acl2 a
def Faithful2 (native acl2 : Val → Val → Val) : Prop := ∀ a b, native a b = acl2 a b
def Faithful3 (native acl2 : Val → Val → Val → Val) : Prop := ∀ a b c, native a b c = acl2 a b c

/-- The natives whose ACL2 definitions are inside the subset but whose agreement is not yet
proved here. All four bitwise natives (`BINARY-LOGIOR`, `BINARY-LOGXOR`, `BINARY-LOGEQV`,
`LOGORC1`) are now discharged below. -/
def nativeOwed : List String := []

theorem nativeOwed_empty : nativeOwed = [] := rfl

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

private theorem toInt_int (x : Int) : (Val.int x).toInt = x := rfl

private def intSign (x : Int) : Bool := decide (x < 0)
private def intMag (x : Int) : Nat := if decide (x < 0) then (-x - 1).toNat else x.toNat
private def intBit (x : Int) (i : Nat) : Bool := (intMag x).testBit i != intSign x
private def ofSignMag (s : Bool) (r : Nat) : Int := if s then -(r : Int) - 1 else (r : Int)

private theorem ofSignMag_sign_mag (x : Int) : ofSignMag (intSign x) (intMag x) = x := by
  unfold ofSignMag intSign intMag
  by_cases h : x < 0
  · simp [h]; omega
  · simp [h]; omega

private theorem intSign_ofSignMag (s : Bool) (r : Nat) : intSign (ofSignMag s r) = s := by
  unfold intSign ofSignMag
  cases s <;> simp <;> omega

private theorem intMag_ofSignMag (s : Bool) (r : Nat) : intMag (ofSignMag s r) = r := by
  unfold intMag ofSignMag
  cases s
  · have h : ¬ ((r : Int) < 0) := by omega
    simp [h]
  · have h : -(r : Int) - 1 < 0 := by omega
    simp [h]; omega

private theorem intBit_ofSignMag (s : Bool) (r : Nat) (i : Nat) :
    intBit (ofSignMag s r) i = (r.testBit i != s) := by
  unfold intBit
  rw [intMag_ofSignMag, intSign_ofSignMag]

private theorem intSign_neg_sub_one (x : Int) : intSign (-x - 1) = !intSign x := by
  unfold intSign
  by_cases h : x < 0
  · have h2 : ¬ (-x - 1 < 0) := by omega
    simp [h, h2]
  · have h2 : -x - 1 < 0 := by omega
    simp [h, h2]

private theorem intMag_neg_sub_one (x : Int) : intMag (-x - 1) = intMag x := by
  unfold intMag
  by_cases h : x < 0
  · have h2 : ¬ (-x - 1 < 0) := by omega
    simp [h, h2]
  · have h2 : -x - 1 < 0 := by omega
    have h3 : -(-x - 1) - 1 = x := by omega
    simp [h, h2, h3]

private theorem intBit_neg_sub_one (x : Int) (i : Nat) : intBit (-x - 1) i = !intBit x i := by
  unfold intBit
  rw [intMag_neg_sub_one, intSign_neg_sub_one]
  cases (intMag x).testBit i <;> cases intSign x <;> rfl

private theorem int_eq_of_sign_and_bit {x y : Int}
    (hs : intSign x = intSign y) (hb : ∀ i, intBit x i = intBit y i) : x = y := by
  rw [← ofSignMag_sign_mag x, ← ofSignMag_sign_mag y, hs]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro i
  have hbi := hb i
  unfold intBit at hbi
  rw [hs] at hbi
  revert hbi
  cases (intMag x).testBit i <;> cases (intMag y).testBit i <;> cases intSign y <;> decide

private theorem testBit_one (d : Nat) : (1 : Nat).testBit d = decide (d = 0) := by
  cases d with
  | zero => rfl
  | succ d =>
    have hlt : 1 < 2 ^ (d + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.testBit_lt_two_pow hlt]
    simp

private theorem testBit_one_shiftLeft (k i : Nat) :
    ((1 : Nat) <<< k).testBit i = decide (i = k) := by
  rw [Nat.testBit_shiftLeft, testBit_one]
  by_cases h : i ≥ k
  · have h2 : (i - k = 0) ↔ (i = k) := by omega
    simp [h, h2]
  · have h2 : i ≠ k := by omega
    simp [h, h2]

private theorem foldl_range_bit_set (g : Nat → Bool) (w i : Nat) :
    (((List.range w).foldl (fun acc k => if g k then acc ||| (1 <<< k) else acc) 0).testBit i) =
      (decide (i < w) && g i) := by
  induction w with
  | zero =>
    simp [List.range_zero]
  | succ w ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hgw : g w = true
    · simp only [hgw, ↓reduceIte, Nat.testBit_or, ih, testBit_one_shiftLeft]
      by_cases hiw : i = w
      · subst hiw
        have hlt : ¬ (i < i) := Nat.lt_irrefl i
        have hlt2 : i < i + 1 := Nat.lt_succ_self i
        simp [hlt, hlt2, hgw]
      · have hlt_iff : (i < w + 1) ↔ (i < w) := by omega
        simp [hiw, hlt_iff]
    · have hgwf : g w = false := Bool.eq_false_iff.mpr hgw
      simp only [hgwf, Bool.false_eq_true, ↓reduceIte, ih]
      by_cases hiw : i = w
      · subst hiw
        simp [hgwf]
      · have hlt_iff : (i < w + 1) ↔ (i < w) := by omega
        simp [hlt_iff]

private theorem testBit_eq_false_of_log2_lt (n i : Nat) (h : n.log2 < i) :
    n.testBit i = false := by
  by_cases hn : n = 0
  · subst hn; simp
  · exact Nat.testBit_lt_two_pow ((Nat.log2_lt hn).mp h)

private theorem bitop_eq_ofSignMag (f : Bool → Bool → Bool) (a b : Int) :
    Native.bitop f a b =
      ofSignMag (f (intSign a) (intSign b))
        ((List.range (max (intMag a).log2 (intMag b).log2 + 2)).foldl
          (fun acc i => if (f (intBit a i) (intBit b i) != f (intSign a) (intSign b)) then acc ||| (1 <<< i) else acc) 0) := by
  rfl

private theorem bitop_mag_testBit (f : Bool → Bool → Bool) (a b : Int) (i : Nat) :
    (((List.range (max (intMag a).log2 (intMag b).log2 + 2)).foldl
      (fun acc k => if (f (intBit a k) (intBit b k) != f (intSign a) (intSign b)) then acc ||| (1 <<< k) else acc) 0).testBit i) =
    (f (intBit a i) (intBit b i) != f (intSign a) (intSign b)) := by
  rw [foldl_range_bit_set]
  by_cases hi : i < max (intMag a).log2 (intMag b).log2 + 2
  · simp [hi]
  · have hna : (intMag a).log2 < i := by omega
    have hnb : (intMag b).log2 < i := by omega
    have hta : (intMag a).testBit i = false := testBit_eq_false_of_log2_lt _ _ hna
    have htb : (intMag b).testBit i = false := testBit_eq_false_of_log2_lt _ _ hnb
    have hba : intBit a i = intSign a := by unfold intBit; rw [hta]; cases intSign a <;> rfl
    have hbb : intBit b i = intSign b := by unfold intBit; rw [htb]; cases intSign b <;> rfl
    simp [hi, hba, hbb]

private theorem intSign_bitop (f : Bool → Bool → Bool) (a b : Int) :
    intSign (Native.bitop f a b) = f (intSign a) (intSign b) := by
  rw [bitop_eq_ofSignMag, intSign_ofSignMag]

private theorem intBit_bitop (f : Bool → Bool → Bool) (a b : Int) (i : Nat) :
    intBit (Native.bitop f a b) i = f (intBit a i) (intBit b i) := by
  rw [bitop_eq_ofSignMag, intBit_ofSignMag, bitop_mag_testBit]
  cases f (intBit a i) (intBit b i) <;> cases f (intSign a) (intSign b) <;> rfl

private theorem logand_eq_bitop (a b : Val) :
    Native.logand a b = .int (Native.bitop (· && ·) a.toInt b.toInt) := by
  unfold Native.logand
  dsimp only
  split
  · rename_i h
    congr 1
    apply int_eq_of_sign_and_bit
    · rw [intSign_bitop]
      unfold intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat &&& b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab]
    · intro i
      rw [intBit_bitop]
      unfold intBit intMag intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat &&& b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab, Nat.testBit_and]
  · rfl

private theorem logior_eq_bitop (a b : Val) :
    Native.logior a b = .int (Native.bitop (· || ·) a.toInt b.toInt) := by
  unfold Native.logior
  dsimp only
  split
  · rename_i h
    congr 1
    apply int_eq_of_sign_and_bit
    · rw [intSign_bitop]
      unfold intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat ||| b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab]
    · intro i
      rw [intBit_bitop]
      unfold intBit intMag intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat ||| b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab, Nat.testBit_or]
  · rfl

private theorem logxor_eq_bitop (a b : Val) :
    Native.logxor a b = .int (Native.bitop (· != ·) a.toInt b.toInt) := by
  unfold Native.logxor
  dsimp only
  split
  · rename_i h
    congr 1
    apply int_eq_of_sign_and_bit
    · rw [intSign_bitop]
      unfold intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat ^^^ b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab]
    · intro i
      rw [intBit_bitop]
      unfold intBit intMag intSign
      have ha : ¬ (a.toInt < 0) := by omega
      have hb : ¬ (b.toInt < 0) := by omega
      have hab : ¬ ((a.toInt.toNat ^^^ b.toInt.toNat : Int) < 0) := by omega
      simp [ha, hb, hab, Nat.testBit_xor]
  · rfl

theorem logorc1_faithful : Faithful2 Native.logorc1 «LOGORC1».acl2 :=
  fun _ _ => rfl

theorem logxor_faithful : Faithful2 Native.logxor «BINARY-LOGXOR».acl2 := by
  intro a b
  unfold «BINARY-LOGXOR».acl2 Native.logeqv Native.lognot
  rw [logxor_eq_bitop]
  simp only [toInt_int]
  congr 1
  omega

theorem logior_faithful : Faithful2 Native.logior «BINARY-LOGIOR».acl2 := by
  intro a b
  unfold «BINARY-LOGIOR».acl2
  rw [logior_eq_bitop]
  unfold Native.lognot
  rw [logand_eq_bitop]
  simp only [toInt_int]
  congr 1
  apply int_eq_of_sign_and_bit
  · simp only [intSign_bitop, intSign_neg_sub_one]
    cases intSign a.toInt <;> cases intSign b.toInt <;> rfl
  · intro i
    simp only [intBit_bitop, intBit_neg_sub_one]
    cases intBit a.toInt i <;> cases intBit b.toInt i <;> rfl

theorem logeqv_faithful : Faithful2 Native.logeqv «BINARY-LOGEQV».acl2 := by
  intro a b
  unfold «BINARY-LOGEQV».acl2 Native.logeqv Native.logorc1
  rw [logxor_eq_bitop, logand_eq_bitop, logior_eq_bitop, logior_eq_bitop]
  unfold Native.lognot
  simp only [toInt_int]
  congr 1
  apply int_eq_of_sign_and_bit
  · simp only [intSign_neg_sub_one, intSign_bitop]
    cases intSign a.toInt <;> cases intSign b.toInt <;> rfl
  · intro i
    simp only [intBit_neg_sub_one, intBit_bitop]
    cases intBit a.toInt i <;> cases intBit b.toInt i <;> rfl

/-- All 12 inside-subset translated natives satisfy their ACL2 defining equations. -/
theorem faithfulCerts :
    Faithful2 Native.nth «NTH».acl2 ∧
    Faithful2 Native.nth «MV-NTH».acl2 ∧
    Faithful3 Native.updateNth «UPDATE-NTH».acl2 ∧
    Faithful1 Native.len «LEN».acl2 ∧
    Faithful2 Native.memberEqual «MEMBER-EQUAL».acl2 ∧
    Faithful1 Native.lognot «LOGNOT».acl2 ∧
    Faithful2 Native.mod «MOD».acl2 ∧
    Faithful2 Native.niq «NONNEGATIVE-INTEGER-QUOTIENT».acl2 ∧
    Faithful2 Native.logior «BINARY-LOGIOR».acl2 ∧
    Faithful2 Native.logxor «BINARY-LOGXOR».acl2 ∧
    Faithful2 Native.logeqv «BINARY-LOGEQV».acl2 ∧
    Faithful2 Native.logorc1 «LOGORC1».acl2 :=
  ⟨nth_faithful, mv_nth_faithful, update_nth_faithful, len_faithful,
   member_equal_faithful, lognot_faithful, mod_faithful, niq_faithful,
   logior_faithful, logxor_faithful, logeqv_faithful, logorc1_faithful⟩

end Fn2.ACL2.Faithful

end
