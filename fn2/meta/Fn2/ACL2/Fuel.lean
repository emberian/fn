import Fn2.ACL2.Faithful

/-!
# Fn2.ACL2.Fuel: fuel adequacy for the recursive translations (PW1)

A recursive ACL2 function `F` is translated as `F.go` with fuel and `F x = F.go (measure x + 1) x`
(`emit_embed.py`). That is ACL2's function exactly when more fuel changes nothing: `go_fuel` below,
for each recursive function in the closure, states and proves that any fuel above the measure
gives the same value. The proof re-derives, in `Val`, the decrease ACL2's admitted measure
asserts; it is the bridge statement of the translation (LEAN-METATHEORY §1 row 3), not a twin of an
ACL2 instance proof.
-/

namespace Fn2.ACL2.Fuel
open Fn2.ACL2 Fn2.Instances.LayerAWorld Fn2.ACL2.Faithful

attribute [local simp] Val.car Val.cdr Val.nfix Val.toInt Prim.consp Prim.integerp Prim.lt Prim.plus
  Prim.neg Prim.times Prim.equal Val.isCons Val.isInt «NOT» «ATOM» «ENDP» «ZP» «IFIX» «NFIX» «=» «NATP»

theorem patch_loop_fuel (fuel k : Nat) (l c h s g ok os og p : Val) (hf : l.nfix < fuel) :
    «FN2-SCRIBE-PATCH-LOOP».go (fuel + k) l c h s g ok os og p =
    «FN2-SCRIBE-PATCH-LOOP».go fuel l c h s g ok os og p := by
  induction fuel generalizing l c h s g ok os og p with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [«FN2-SCRIBE-PATCH-LOOP».go]
    split
    · rfl
    · rename_i hc
      cases l with
      | int i =>
        have hi : 0 < i := Decidable.byContradiction fun hneg => hc (by simp [hneg])
        rw [ih]
        simp at hf ⊢; omega
      | _ => simp at hc

theorem fill_fuel (fuel k : Nat) (l c q h s g ok os og p : Val) (hf : l.nfix < fuel) :
    «FN2-SCRIBE-FILL».go (fuel + k) l c q h s g ok os og p =
    «FN2-SCRIBE-FILL».go fuel l c q h s g ok os og p := by
  induction fuel generalizing l c q h s g ok os og p with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [«FN2-SCRIBE-FILL».go]
    split
    · rfl
    · rename_i hc
      cases l with
      | int i =>
        have hi : 0 < i := Decidable.byContradiction fun hneg => hc (by simp [hneg])
        rw [ih]
        simp at hf ⊢; omega
      | _ => simp at hc

theorem verify_fuel (fuel k : Nat) (l c q h s g ok os og p : Val) (hf : l.nfix < fuel) :
    «FN2-SCRIBE-VERIFY».go (fuel + k) l c q h s g ok os og p =
    «FN2-SCRIBE-VERIFY».go fuel l c q h s g ok os og p := by
  induction fuel generalizing l c q h s g ok os og p with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [«FN2-SCRIBE-VERIFY».go]
    split
    · rfl
    · rename_i hc
      cases l with
      | int i =>
        have hi : 0 < i := Decidable.byContradiction fun hneg => hc (by simp [hneg])
        rw [ih]
        simp at hf ⊢; omega
      | _ => simp at hc

theorem class_scan_fuel (fuel k : Nat) (i n b z p : Val)
    (hf : (Val.int (16 - (i.nfix : Int))).nfix < fuel) :
    «FN2-POOL-CLASS-SCAN».go (fuel + k) i n b z p = «FN2-POOL-CLASS-SCAN».go fuel i n b z p := by
  induction fuel generalizing i n b z p with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-POOL-CLASS-SCAN».go]
    cases i with
    | int j =>
      by_cases h0 : 0 ≤ j
      · by_cases h16 : j < 16
        · have hl : ∀ q : Val, (Val.int (16 - ((Prim.plus (Val.int j) (Val.int 1)).nfix : Int))).nfix < m := by
            intro _; simp at hf ⊢; omega
          simp only [ih _ _ _ _ _ (hl n)]
        · simp [h0, h16]
      · simp [h0]
    | _ => simp

theorem nfix_nfix (l : Val) : («NFIX» l).nfix = l.nfix := by
  cases l with
  | int i => by_cases h : 0 ≤ i <;> simp [h] <;> omega
  | _ => simp

/-- The scribe's three loops are ACL2's functions: more fuel than the measure changes nothing. -/
theorem recursive_adequate :
    (∀ k l c h s g ok os og p, «FN2-SCRIBE-PATCH-LOOP».go (l.nfix + 1 + k) l c h s g ok os og p =
      «FN2-SCRIBE-PATCH-LOOP» l c h s g ok os og p) ∧
    (∀ k l c q h s g ok os og p, «FN2-SCRIBE-FILL».go (l.nfix + 1 + k) l c q h s g ok os og p =
      «FN2-SCRIBE-FILL» l c q h s g ok os og p) ∧
    (∀ k l c q h s g ok os og p, «FN2-SCRIBE-VERIFY».go (l.nfix + 1 + k) l c q h s g ok os og p =
      «FN2-SCRIBE-VERIFY» l c q h s g ok os og p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k l c h s g ok os og p
    rw [patch_loop_fuel _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-SCRIBE-PATCH-LOOP», nfix_nfix]
  · intro k l c q h s g ok os og p
    rw [fill_fuel _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-SCRIBE-FILL», nfix_nfix]
  · intro k l c q h s g ok os og p
    rw [verify_fuel _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-SCRIBE-VERIFY», nfix_nfix]

end Fn2.ACL2.Fuel
