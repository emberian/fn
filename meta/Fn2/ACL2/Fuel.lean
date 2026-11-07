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

attribute [local simp] «POSP»

/-- Universal fuel-adequacy schema for bounded-measure loops:
if one step `step` of a fuelled loop only depends on recursive calls at states `y`
with strictly smaller measure `μ y < μ x`, then any fuel `fuel > μ x` stabilizes `fuelLoop`. -/
def fuelLoop (step : (α → Val) → α → Val) : Nat → α → Val
  | 0, _ => Val.nil
  | fuel + 1, x => step (fuelLoop step fuel) x

theorem fuelLoop_adequate {α : Type} (μ : α → Nat) (step : (α → Val) → α → Val)
    (hstep : ∀ (g₁ g₂ : α → Val) (x : α),
      (∀ y, μ y < μ x → g₁ y = g₂ y) → step g₁ x = step g₂ x)
    (fuel k : Nat) (x : α) (hf : μ x < fuel) :
    fuelLoop step (fuel + k) x = fuelLoop step fuel x := by
  induction fuel generalizing x with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [fuelLoop]
    apply hstep
    intro y hy
    exact ih y (by omega)

theorem nfix_val_eq (x : Val) : «NFIX» x = Val.int (x.nfix : Int) := by
  cases x with
  | int i => by_cases h : 0 ≤ i <;> simp [h] <;> omega
  | _ => simp

/-- `ZP` of a natural number read through `NFIX` is its `NOT (< 0 _)` test (the countdown loops'
guard, Fn2.Instances.LayerAPres). -/
theorem zp_nfix (x : Val) : «ZP» («NFIX» x) = «NOT» (Prim.lt (Val.int 0) («NFIX» x)) := by
  rw [nfix_val_eq]; rfl

theorem nfix_diff_eq (n i : Val) :
    («NFIX» (Prim.plus («NFIX» n) (Prim.neg («NFIX» i)))).nfix = n.nfix - i.nfix := by
  rw [nfix_nfix, nfix_val_eq n, nfix_val_eq i]
  simp
  omega

theorem nfix_pred_lt {x : Val} (h : ¬ («ZP» x).truthy = true) :
    (Prim.plus (Val.int (-1)) x).nfix < x.nfix := by
  cases x with
  | int i =>
    have hi : 0 < i := Decidable.byContradiction fun hneg => h (by simp [hneg])
    simp; omega
  | _ => simp at h

theorem acl2Count_pred_lt {x : Val} (h : ¬ («ZP» x).truthy = true) :
    (Val.int (Val.acl2Count (Prim.plus (Val.int (-1)) x))).nfix <
      (Val.int (Val.acl2Count x)).nfix := by
  cases x with
  | int i =>
    have hi : 0 < i := Decidable.byContradiction fun hneg => h (by simp [hneg])
    have h1 : ((-1 + i).natAbs : Int) = -1 + i := Int.natAbs_of_nonneg (by omega)
    have h2 : (i.natAbs : Int) = i := Int.natAbs_of_nonneg (by omega)
    simp [Val.acl2Count, h1, h2]
    omega
  | _ => simp at h

theorem acl2Count_cdr_lt {x : Val} (h : ¬ («ENDP» x).truthy = true) :
    (Val.int (Val.acl2Count (Val.cdr x))).nfix < (Val.int (Val.acl2Count x)).nfix := by
  cases x with
  | cons a d =>
    simp [Val.acl2Count]
    omega
  | _ => simp at h

theorem cursor_pad_loop_fuel (fuel k : Nat) (n slot gen ok os og p : Val)
    (hf : (Val.int (Val.acl2Count n)).nfix < fuel) :
    «FN2-CURSOR-PAD-LOOP».go (fuel + k) n slot gen ok os og p =
    «FN2-CURSOR-PAD-LOOP».go fuel n slot gen ok os og p := by
  induction fuel generalizing n slot gen ok os og p with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-CURSOR-PAD-LOOP».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Val.int (Val.acl2Count (Prim.plus (Val.int (-1)) n))).nfix < m := by
        have := acl2Count_pred_lt hc
        omega
      rw [ih _ _ _ _ _ _ _ hlt]

theorem pool_compare_loop_fuel (fuel k : Nat) (a b i n p : Val)
    (hf : (n.nfix - i.nfix) < fuel) :
    «FN2-POOL-COMPARE-LOOP».go (fuel + k) a b i n p =
    «FN2-POOL-COMPARE-LOOP».go fuel a b i n p := by
  induction fuel generalizing a b i n p with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-POOL-COMPARE-LOOP».go]
    cases i with
    | int iv =>
      cases n with
      | int nv =>
        by_cases hi0 : 0 ≤ iv
        · by_cases hn0 : 0 ≤ nv
          · by_cases hlt : iv < nv
            · have hstep : ((Val.int nv).nfix - (Prim.plus (Val.int 1) (Val.int iv)).nfix) < m := by
                simp at hf ⊢; omega
              rw [ih _ _ _ _ _ hstep]
            · simp [hi0, hn0, hlt]
          · simp [hi0, hn0]
        · simp [hi0]
      | _ =>
        by_cases hi0 : 0 ≤ iv <;> simp [hi0]
    | _ => simp

theorem range_key_least_fuel (fuel k : Nat) (j nk sid qb wslot wgen fields : Val)
    (hf : (nk.nfix - j.nfix) < fuel) :
    «FN2-RANGE-KEY-LEAST».go (fuel + k) j nk sid qb wslot wgen fields =
    «FN2-RANGE-KEY-LEAST».go fuel j nk sid qb wslot wgen fields := by
  induction fuel generalizing j nk sid qb wslot wgen fields with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-RANGE-KEY-LEAST».go]
    cases j with
    | int jv =>
      cases nk with
      | int nkv =>
        by_cases hj0 : 0 ≤ jv
        · by_cases hnk0 : 0 ≤ nkv
          · by_cases hlt : jv < nkv
            · have hstep : ((Val.int nkv).nfix - (Prim.plus (Val.int 1) (Val.int jv)).nfix) < m := by
                simp at hf ⊢; omega
              rw [ih _ _ _ _ _ _ _ hstep]
            · simp [hj0, hnk0, hlt]
          · simp [hj0, hnk0]
        · simp [hj0]
      | _ => by_cases hj0 : 0 ≤ jv <;> simp [hj0]
    | _ => simp

theorem run_skip_fuel (fuel k : Nat) (sid lv m off slot gen rb ok os og fields pool : Val)
    (hf : m.nfix < fuel) :
    «FN2-RUN-SKIP».go (fuel + k) sid lv m off slot gen rb ok os og fields pool =
    «FN2-RUN-SKIP».go fuel sid lv m off slot gen rb ok os og fields pool := by
  induction fuel generalizing sid lv m off slot gen rb ok os og fields pool with
  | zero => omega
  | succ n ih =>
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [«FN2-RUN-SKIP».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Prim.plus (Val.int (-1)) m).nfix < n := by
        have := nfix_pred_lt hc
        omega
      rw [ih _ _ _ _ _ _ _ _ _ _ _ _ hlt]

theorem run_version_fuel (fuel k : Nat) (sid n inst : Val)
    (hf : n.nfix < fuel) :
    «FN2-RUN-VERSION».go (fuel + k) sid n inst =
    «FN2-RUN-VERSION».go fuel sid n inst := by
  induction fuel generalizing sid n inst with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-RUN-VERSION».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Prim.plus (Val.int (-1)) n).nfix < m := by
        have := nfix_pred_lt hc
        omega
      rw [ih _ _ _ hlt]

theorem range_add_overlays_fuel (fuel k : Nat) (n i g sid ranges sources overlays : Val)
    (hf : n.nfix < fuel) :
    «FN2-RANGE-ADD-OVERLAYS».go (fuel + k) n i g sid ranges sources overlays =
    «FN2-RANGE-ADD-OVERLAYS».go fuel n i g sid ranges sources overlays := by
  induction fuel generalizing n i g sid ranges sources overlays with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-RANGE-ADD-OVERLAYS».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Prim.plus (Val.int (-1)) n).nfix < m := by
        have := nfix_pred_lt hc
        omega
      rw [ih _ _ _ _ _ _ _ hlt, ih _ _ _ _ _ _ _ hlt]

theorem range_add_runs_fuel (fuel k : Nat) (n i g sid rlo ranges sources inst : Val)
    (hf : n.nfix < fuel) :
    «FN2-RANGE-ADD-RUNS».go (fuel + k) n i g sid rlo ranges sources inst =
    «FN2-RANGE-ADD-RUNS».go fuel n i g sid rlo ranges sources inst := by
  induction fuel generalizing n i g sid rlo ranges sources inst with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-RANGE-ADD-RUNS».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Prim.plus (Val.int (-1)) n).nfix < m := by
        have := nfix_pred_lt hc
        omega
      rw [ih _ _ _ _ _ _ _ _ hlt, ih _ _ _ _ _ _ _ _ hlt]

theorem succ_newest_run_fuel (fuel k : Nat) (cnt r sid bound best inst : Val)
    (hf : cnt.nfix < fuel) :
    «FN2-SUCC-NEWEST-RUN».go (fuel + k) cnt r sid bound best inst =
    «FN2-SUCC-NEWEST-RUN».go fuel cnt r sid bound best inst := by
  induction fuel generalizing cnt r sid bound best inst with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-SUCC-NEWEST-RUN».go]
    cases cnt with
    | int i =>
      by_cases hi : 0 < i
      · have hlt : (Prim.plus (Val.int (-1)) (Val.int i)).nfix < m := by
          simp at hf ⊢; omega
        rw [ih _ _ _ _ _ _ hlt]
      · simp [hi]
    | _ => simp

theorem xl_newest_frozen_fuel (fuel k : Nat) (cnt o sid bound best overlays : Val)
    (hf : cnt.nfix < fuel) :
    «FN2-XL-NEWEST-FROZEN».go (fuel + k) cnt o sid bound best overlays =
    «FN2-XL-NEWEST-FROZEN».go fuel cnt o sid bound best overlays := by
  induction fuel generalizing cnt o sid bound best overlays with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-XL-NEWEST-FROZEN».go]
    cases cnt with
    | int i =>
      by_cases hi : 0 < i
      · have hlt : (Prim.plus (Val.int (-1)) (Val.int i)).nfix < m := by
          simp at hf ⊢; omega
        rw [ih _ _ _ _ _ _ hlt]
      · simp [hi]
    | _ => simp

theorem gram_put_span_fuel (fuel k : Nat) (left i sslot sgen slot gen ok os og pool : Val)
    (hf : left.nfix < fuel) :
    «FN2-GRAM-PUT-SPAN».go (fuel + k) left i sslot sgen slot gen ok os og pool =
    «FN2-GRAM-PUT-SPAN».go fuel left i sslot sgen slot gen ok os og pool := by
  induction fuel generalizing left i sslot sgen slot gen ok os og pool with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-GRAM-PUT-SPAN».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Prim.plus (Val.int (-1)) left).nfix < m := by
        have := nfix_pred_lt hc
        omega
      rw [ih _ _ _ _ _ _ _ _ _ _ hlt]

theorem gram_put_digits_fuel (fuel k : Nat) (left n p slot gen ok os og pool : Val)
    (hf : left.nfix < fuel) :
    «FN2-GRAM-PUT-DIGITS».go (fuel + k) left n p slot gen ok os og pool =
    «FN2-GRAM-PUT-DIGITS».go fuel left n p slot gen ok os og pool := by
  induction fuel generalizing left n p slot gen ok os og pool with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-GRAM-PUT-DIGITS».go]
    cases left with
    | int i =>
      by_cases hi : 0 < i
      · have hlt : (Prim.plus (Val.int (-1)) (Val.int i)).nfix < m := by
          simp at hf ⊢; omega
        rw [ih _ _ _ _ _ _ _ _ _ hlt]
      · simp [hi]
    | _ => simp

theorem gram_pow10_fuel (fuel k : Nat) (left n p : Val)
    (hf : left.nfix < fuel) :
    «FN2-GRAM-POW10».go (fuel + k) left n p =
    «FN2-GRAM-POW10».go fuel left n p := by
  induction fuel generalizing left n p with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«FN2-GRAM-POW10».go]
    cases left with
    | int i =>
      by_cases hi : 0 < i
      · have hlt : (Prim.plus (Val.int (-1)) (Val.int i)).nfix < m := by
          simp at hf ⊢; omega
        rw [ih _ _ _ hlt]
      · simp [hi]
    | _ => simp

theorem member_eq_exec_fuel (fuel k : Nat) (x lst : Val)
    (hf : (Val.int (Val.acl2Count lst)).nfix < fuel) :
    «MEMBER-EQ-EXEC».go (fuel + k) x lst =
    «MEMBER-EQ-EXEC».go fuel x lst := by
  induction fuel generalizing x lst with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«MEMBER-EQ-EXEC».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Val.int (Val.acl2Count (Val.cdr lst))).nfix < m := by
        have := acl2Count_cdr_lt hc
        omega
      rw [ih _ _ hlt]

theorem member_eql_exec_fuel (fuel k : Nat) (x lst : Val)
    (hf : (Val.int (Val.acl2Count lst)).nfix < fuel) :
    «MEMBER-EQL-EXEC».go (fuel + k) x lst =
    «MEMBER-EQL-EXEC».go fuel x lst := by
  induction fuel generalizing x lst with
  | zero => omega
  | succ m ih =>
    rw [show m + 1 + k = (m + k) + 1 by omega]
    simp only [«MEMBER-EQL-EXEC».go]
    split
    · rfl
    · rename_i hc
      have hlt : (Val.int (Val.acl2Count (Val.cdr lst))).nfix < m := by
        have := acl2Count_cdr_lt hc
        omega
      rw [ih _ _ hlt]

/-- Cursor, pool, scan, grammar, and list recursive loops stabilize above their ACL2 measures. -/
theorem cursor_pool_scan_adequate :
    (∀ k n slot gen ok os og p,
      «FN2-CURSOR-PAD-LOOP».go ((Val.int (Val.acl2Count n)).nfix + 1 + k) n slot gen ok os og p =
        «FN2-CURSOR-PAD-LOOP» n slot gen ok os og p) ∧
    (∀ k a b i n p,
      «FN2-POOL-COMPARE-LOOP».go ((n.nfix - i.nfix) + 1 + k) a b i n p =
        «FN2-POOL-COMPARE-LOOP» a b i n p) ∧
    (∀ k j nk sid qb wslot wgen fields,
      «FN2-RANGE-KEY-LEAST».go ((nk.nfix - j.nfix) + 1 + k) j nk sid qb wslot wgen fields =
        «FN2-RANGE-KEY-LEAST» j nk sid qb wslot wgen fields) ∧
    (∀ k sid lv m off slot gen rb ok os og fields pool,
      «FN2-RUN-SKIP».go (m.nfix + 1 + k) sid lv m off slot gen rb ok os og fields pool =
        «FN2-RUN-SKIP» sid lv m off slot gen rb ok os og fields pool) ∧
    (∀ k sid n inst,
      «FN2-RUN-VERSION».go (n.nfix + 1 + k) sid n inst =
        «FN2-RUN-VERSION» sid n inst) ∧
    (∀ k n i g sid ranges sources overlays,
      «FN2-RANGE-ADD-OVERLAYS».go (n.nfix + 1 + k) n i g sid ranges sources overlays =
        «FN2-RANGE-ADD-OVERLAYS» n i g sid ranges sources overlays) ∧
    (∀ k n i g sid rlo ranges sources inst,
      «FN2-RANGE-ADD-RUNS».go (n.nfix + 1 + k) n i g sid rlo ranges sources inst =
        «FN2-RANGE-ADD-RUNS» n i g sid rlo ranges sources inst) ∧
    (∀ k cnt r sid bound best inst,
      «FN2-SUCC-NEWEST-RUN».go (cnt.nfix + 1 + k) cnt r sid bound best inst =
        «FN2-SUCC-NEWEST-RUN» cnt r sid bound best inst) ∧
    (∀ k cnt o sid bound best overlays,
      «FN2-XL-NEWEST-FROZEN».go (cnt.nfix + 1 + k) cnt o sid bound best overlays =
        «FN2-XL-NEWEST-FROZEN» cnt o sid bound best overlays) ∧
    (∀ k left i sslot sgen slot gen ok os og pool,
      «FN2-GRAM-PUT-SPAN».go (left.nfix + 1 + k) left i sslot sgen slot gen ok os og pool =
        «FN2-GRAM-PUT-SPAN» left i sslot sgen slot gen ok os og pool) ∧
    (∀ k left n p slot gen ok os og pool,
      «FN2-GRAM-PUT-DIGITS».go (left.nfix + 1 + k) left n p slot gen ok os og pool =
        «FN2-GRAM-PUT-DIGITS» left n p slot gen ok os og pool) ∧
    (∀ k left n p,
      «FN2-GRAM-POW10».go (left.nfix + 1 + k) left n p =
        «FN2-GRAM-POW10» left n p) ∧
    (∀ k x lst,
      «MEMBER-EQ-EXEC».go ((Val.int (Val.acl2Count lst)).nfix + 1 + k) x lst =
        «MEMBER-EQ-EXEC» x lst) ∧
    (∀ k x lst,
      «MEMBER-EQL-EXEC».go ((Val.int (Val.acl2Count lst)).nfix + 1 + k) x lst =
        «MEMBER-EQL-EXEC» x lst) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k n slot gen ok os og p
    rw [cursor_pad_loop_fuel _ _ _ _ _ _ _ _ _ (by omega)]
    rfl
  · intro k a b i n p
    rw [pool_compare_loop_fuel _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-POOL-COMPARE-LOOP», nfix_diff_eq]
  · intro k j nk sid qb wslot wgen fields
    rw [range_key_least_fuel _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-RANGE-KEY-LEAST», nfix_diff_eq]
  · intro k sid lv m off slot gen rb ok os og fields pool
    rw [run_skip_fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-RUN-SKIP», nfix_nfix]
  · intro k sid n inst
    rw [run_version_fuel _ _ _ _ _ (by omega)]
    simp only [«FN2-RUN-VERSION», nfix_nfix]
  · intro k n i g sid ranges sources overlays
    rw [range_add_overlays_fuel _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-RANGE-ADD-OVERLAYS», nfix_nfix]
  · intro k n i g sid rlo ranges sources inst
    rw [range_add_runs_fuel _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-RANGE-ADD-RUNS», nfix_nfix]
  · intro k cnt r sid bound best inst
    rw [succ_newest_run_fuel _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-SUCC-NEWEST-RUN», nfix_nfix]
  · intro k cnt o sid bound best overlays
    rw [xl_newest_frozen_fuel _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-XL-NEWEST-FROZEN», nfix_nfix]
  · intro k left i sslot sgen slot gen ok os og pool
    rw [gram_put_span_fuel _ _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-GRAM-PUT-SPAN», nfix_nfix]
  · intro k left n p slot gen ok os og pool
    rw [gram_put_digits_fuel _ _ _ _ _ _ _ _ _ _ _ (by omega)]
    simp only [«FN2-GRAM-PUT-DIGITS», nfix_nfix]
  · intro k left n p
    rw [gram_pow10_fuel _ _ _ _ _ (by omega)]
    simp only [«FN2-GRAM-POW10», nfix_nfix]
  · intro k x lst
    rw [member_eq_exec_fuel _ _ _ _ (by omega)]
    rfl
  · intro k x lst
    rw [member_eql_exec_fuel _ _ _ _ (by omega)]
    rfl

end Fn2.ACL2.Fuel
