module

public import Fn2.ACL2.Val
public import Fn2.ACL2.PrimitiveIntegerPower
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

namespace Fn2.ACL2.PrimitiveContracts

/-- Rational intermediates are interpreted before the integer result is
represented. This includes negative divisors and ACL2's zero completion. -/
theorem floor_ratio (a b : Int) : Int.fdiv a b = ⌊(a : ℚ) / (b : ℚ)⌋ := by
  have positive (a : Int) (d : Nat) : Int.fdiv a d = ⌊(a : ℚ) / (d : ℚ)⌋ := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg d)]
    exact (Rat.floor_intCast_div_natCast a d).symm
  by_cases hb : 0 ≤ b
  · lift b to Nat using hb
    exact positive a b
  · let d := (-b).toNat
    have hd : b = -(d : Int) := by dsimp [d]; omega
    rw [hd]
    have hf : Int.fdiv a (-(d : Int)) = Int.fdiv (-a) d := by
      simpa using Int.neg_fdiv_neg (-a) (d : Int)
    have hr : (a : ℚ) / ((-(d : Int) : Int) : ℚ) = ((-a : Int) : ℚ) / (d : ℚ) := by
      push_cast
      ring
    rw [hf, hr]
    exact positive (-a) d

theorem floor_faithful (a b : Int) :
    Native.floor (.int a) (.int b) = .int ⌊(a : ℚ) / (b : ℚ)⌋ := by
  by_cases hb : b = 0
  · simp [Native.floor, Val.toInt, hb]
  · simp only [Native.floor, Val.toInt, if_neg hb, floor_ratio]

theorem ceiling_faithful (a b : Int) :
    Native.ceiling (.int a) (.int b) = .int (-⌊((-a : Int) : ℚ) / (b : ℚ)⌋) := by
  by_cases hb : b = 0
  · simp [Native.ceiling, Val.toInt, hb]
  · simp only [Native.ceiling, Val.toInt, if_neg hb, floor_ratio]

/-- The rational `2^c` is retained even when `c` is negative. The native
integer operation equals the floor of ACL2's rational defining expression. -/
theorem ash_faithful (i c : Int) :
    Native.ash (.int i) (.int c) = .int ⌊(i : ℚ) * (2 : ℚ) ^ c⌋ := by
  cases c with
  | ofNat n =>
    simpa [Native.ash, Val.toInt, Int.cast_mul, Int.cast_pow] using
      congrArg Val.int (Int.floor_intCast (R := ℚ) (i * 2 ^ n)).symm
  | negSucc n =>
    have hn : ¬ 0 ≤ Int.negSucc n := by omega
    simp only [Native.ash, Val.toInt, if_neg hn, Int.neg_negSucc, Int.toNat_natCast]
    rw [floor_ratio]
    congr 2
    simp [zpow_negSucc, div_eq_mul_inv]

theorem character_roundtrip (c : Char) (h : c.toNat < 256) :
    Prim.codeChar (Prim.charCode (.chr c)) = .chr c := by
  simp [Prim.codeChar, Prim.charCode, h]

theorem values_roundtrip (xs : List Val) : (Val.ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Val.ofList, Val.toList, ih]

theorem string_roundtrip (s : String) :
    Prim.coerce (Prim.coerce (.str s) (.sym "LIST")) (.sym "STRING") = .str s := by
  simp [Prim.coerce, values_roundtrip, List.map_map, Function.comp_def]

theorem negative_ash_positive :
    Native.ash (.int (-3)) (.int (-1)) = .int (-2) ∧
    ⌊(-3 : ℚ) * (2 : ℚ) ^ (-1 : Int)⌋ = (-2 : Int) := by
  constructor
  · decide
  · norm_num

theorem negative_ash_mutant_rejected :
    Native.ash (.int (-3)) (.int (-1)) ≠ .int (Int.tdiv (-3) 2) := by decide

theorem signed_division_control :
    Native.floor (.int 3) (.int (-2)) = .int (-2) ∧
    Native.ceiling (.int 3) (.int (-2)) = .int (-1) := by decide

theorem crlf_preserved :
    Prim.coerce (.str "\r\n") (.sym "LIST") =
      Val.ofList [.chr (Char.ofNat 13), .chr (Char.ofNat 10)] ∧
    Prim.coerce (.str "\r\n") (.sym "LIST") ≠ Prim.coerce (.str "\n") (.sym "LIST") := by decide

theorem rational_intermediate_not_integer_lowering :
    ((Native.expt (.int 2) (.int (-1))).toInt : ℚ) ≠ (2 : ℚ) ^ (-1 : Int) := by
  norm_num [Native.expt, Val.toInt]

end Fn2.ACL2.PrimitiveContracts

end
