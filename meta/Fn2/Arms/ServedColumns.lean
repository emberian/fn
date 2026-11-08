module

public import Fn2.Arms.Served
public import Fn2.Arms.Columns
public import Fn2.Instances.LayerAEqns1
public import Fn2.Instances.LayerAEqns2
public import Fn2.Instances.LayerAEqns3
public import Fn2.Instances.LayerAEqns4
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
-- BEGIN world bodies (emit_embed.py): kinds FN2-CURSOR; prefixes FN2-CURSOR- FN2-MACHINES-READY- FN2-MACHINES-SET-READY- FN2-MACHINES-WAIT-REASON FN2-MACHINES-SET-WAIT-REASON
import all Fn2.Instances.LayerAWorld.S34_d0to6
import all Fn2.Instances.LayerAWorld.S33_d1to7
import all Fn2.Instances.LayerAWorld.S17_d1
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Fn2.Instances.LayerAWorld.S13_d0to8
import all Fn2.Instances.LayerAWorld.S22_d1to7
import all Fn2.Instances.LayerAWorld.S19_d6to9
import all Fn2.Instances.LayerAWorld.S15xc66772_d1to9
import all Fn2.Instances.LayerAWorld.S20_d5to7
import all Fn2.Instances.LayerAWorld.S21_d6to7
import all Fn2.Instances.LayerAWorld.S16_d5to10
import all Fn2.Instances.LayerAWorld.S12_d0to10
import all Fn2.Instances.LayerAWorld.S12xff6259_d0to4
import all Fn2.Instances.LayerAWorld.S12xff6259_d5to6
import all Fn2.Instances.LayerAWorld.S10x95dbb5_d6to10
import all Fn2.Instances.LayerAWorld.S14_d0to1
import all Fn2.Instances.LayerAWorld.S11_d0to10
import all Fn2.Instances.LayerAWorld.S11x4c060b_d0to1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d3b0
import all Fn2.Instances.LayerAWorld.S11x4c060b_d3b1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d4
import all Fn2.Instances.LayerAWorld.S11x4c060b_d5b0
import all Fn2.Instances.LayerAWorld.S11x4c060b_d5b1
import all Fn2.Instances.LayerAWorld.S11x4c060b_d6to12
import all Fn2.Instances.LayerAWorld.S15_d6to11
import all Fn2.Instances.LayerAWorld.S18_d3to8
import all Fn2.Instances.LayerAWorld.S10_d1to9
import all Fn2.Instances.LayerAWorld.S12x9a9f8a_d0to12
import all Fn2.Instances.LayerAWorld.S9_d3to11
import all Fn2.Instances.LayerAWorld.S9x24d61a_d0to20
import all Fn2.Instances.LayerAWorld.S8_d2to12
import all Fn2.Instances.LayerAWorld.S5_d5to13
import all Fn2.Instances.LayerAWorld.S7_d0to13
import all Fn2.Instances.LayerAWorld.S6x90aa46_d0to21
import all Fn2.Instances.LayerAWorld.S5xf0eee3_d0to22
import all Fn2.Instances.LayerAWorld.S6_d5to10
import all Fn2.Instances.LayerAWorld.S4_d0to24
import all Fn2.Instances.LayerAWorld.S3_d0to23
import all Fn2.Instances.LayerAWorld.SAuthCnsCursor_d6to26
import all Fn2.Instances.LayerAWorld.SCnsCursorSealer_d6to25
import all Fn2.Instances.LayerAWorld.S2_d0to29
import all Fn2.Instances.LayerAWorld.SConnCursor_d0to20
import all Fn2.Instances.LayerAWorld.KConn_d0to24
import all Fn2.Instances.LayerAWorld.KCursor_d0to32
import all Fn2.Instances.LayerAWorld.Rest_d6b0
import all Fn2.Instances.LayerAWorld.Rest_d6b1
import all Fn2.Instances.LayerAWorld.Rest_d7b0
import all Fn2.Instances.LayerAWorld.Rest_d7b1
-- END world bodies

@[expose] public section

/-!
# Fn2.Arms.ServedColumns: the column and phase contracts for `FN2-CURSOR`

The registry's world discharges `TableFacts` for `FN2-CURSOR`: each column's getter and setter is
the generated `NTH`/`UPDATE-NTH-ARRAY` pair at the column's index in the kind's table (the
directory's at its index in `fn2-machines`), by the dispatch equations. Then every arm, handler
and sub-arm of the kind has checked written columns and checked reachable phases, and both
contracts hold on every run of the interpreter.
-/

namespace Fn2.Arms.ServedColumns
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Columns Fn2.Arms.Derive Fn2.Arms.Served Fn2.Instances.LayerAKinds

/-- The directory's row fields in `fn2-machines` (P1): `READY-PREV` 2, `READY-NEXT` 3,
`WAIT-REASON` 4. -/
def dirIdx (c : String) : Nat := directoryFields.idxOf c + 2

theorem idxOf_inj (l : List String) (a b : String) (ha : a ∈ l) (hb : b ∈ l)
    (h : l.idxOf a = l.idxOf b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.idxOf_cons] at h
    by_cases hxa : x = a
    · subst hxa
      by_cases hxb : x = b
      · exact hxb
      · have e : (x == b) = false := by simp [hxb]
        simp [e] at h
    · have e1 : (x == a) = false := by simp [hxa]
      by_cases hxb : x = b
      · subst hxb; simp [e1] at h
      · have e2 : (x == b) = false := by simp [hxb]
        simp only [e1, e2, cond_false, Nat.add_right_cancel_iff] at h
        exact ih (by simpa [Ne.symm hxa] using ha) (by simpa [Ne.symm hxb] using hb) h

/-- `FN2-CURSOR`'s table as the registry prints it (its fields in stobj order). -/
def cursorTable : List String :=
  ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "ACCOUNT-REF", "DEADLINE", "CONN", "CONN-GEN", "CONN-KIND", "MASK", "RX-SLOT", "RX-GEN", "LINE-S", "LINE-E", "TX-SLOT", "TX-GEN", "GROUP", "CURRENT", "PIN", "TAG", "K0", "A0", "B0", "K1", "A1", "B1", "STEP", "LO", "HI", "NEXT", "FOUND", "COUNT", "LOW", "HIGH", "SEL", "NCURRENT", "SPIN", "UPDATE", "REPLY", "ROFF", "LPOS", "SEEN", "HAVE", "TURN", "DONE", "CANCEL", "POSTING", "LGROUP", "KLEN", "STOPPED", "NEXT-FREE", "ART", "LUNIT", "LEPOCH", "LALLOC", "ALEN", "APOS", "PLEN", "LOFF", "AST", "LSLOT", "LGEN", "LEASE", "OAT", "MSO", "MLN", "SAID", "REVENT", "ROUTCOME", "RCOUNT", "RREADY", "MKIND", "MPOS", "BUNIT", "BEPOCH", "BALLOC", "BLEN", "BREADY", "MREAD", "BHASH", "BCV", "HMODE", "HK", "HSTEP", "PENDING", "CURSOR"]

set_option maxHeartbeats 0 in
/-- The registry's `FN2-CURSOR` accessors keep the columns' frame: each own column is the
`(NTH s (NTH i st))` / `UPDATE-NTH-ARRAY i` pair at its index `i` in the table, each directory
field the same in `fn2-machines`, by the generated dispatch (checked by the kernel's evaluation of
the dispatch tree, as the dispatch equations are). -/
theorem cursor_tableFacts : TableFacts world cursorK := by
  have hn : cursorK.name = "FN2-CURSOR" := by decide +kernel
  have ht : cursorK.table = cursorTable := by decide +kernel
  have hown : ownCols cursorK = cursorTable := by decide +kernel
  have hdir : dirCols cursorK = ["READY-PREV", "READY-NEXT", "WAIT-REASON"] := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [hn, hown]
    refine facts_of world cursorTable (fun c => "FN2-CURSOR" ++ "-" ++ c)
      (fun c => "FN2-CURSOR" ++ "-SET-" ++ c) (fun c => cursorTable.idxOf c) arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj _ a b ha hb h)
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [cursorTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) rfl
    · simp only [cursorTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) rfl
  · rw [hdir]
    refine facts_of world _ (fun c => "FN2-MACHINES-" ++ c) (fun c => "FN2-MACHINES-SET-" ++ c)
      dirIdx arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj directoryFields a b (by simpa [directoryFields] using ha)
        (by simpa [directoryFields] using hb) (by simpa [dirIdx] using h))
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) rfl
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) rfl

theorem cursor_shape : kindShape cursorK = true ∧ phasesCover cursorK = true := by
  decide +kernel

/-- **Every `FN2-CURSOR` arm, handler and sub-arm writes only its checked columns on every
run**: a column outside them (other than `PHASE`) reads back at every slot as passed in. -/
theorem cursor_arm_writes (a : Arm) (ha : a ∈ cursorK.subarms ++ cursorK.arms ++ cursorK.observes) :
    ∃ W, checkedWrites world cursorK a = some W ∧
      ∀ observe args fuel v, runArm world cursorK a observe args fuel = .ok v →
        ∃ pre ts, v = Val.ofList (pre ++ ts) ∧ ts.length = cursorK.tuple.length ∧
          ∀ c ∈ cursorK.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s,
            colGet world cursorK (stobj (tupleSt cursorK ts)) c s =
              colGet world cursorK (stobj (Inv.startSt cursorK observe args)) c s := by
  have hall : (cursorK.subarms ++ cursorK.arms ++ cursorK.observes).all
      (fun a => (checkedWrites world cursorK a).isSome) = true := by decide +kernel
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨W, hW, fun observe args fuel v hrun =>
    runArm_writes_sub world cursorK a observe args fuel v W hW cursor_tableFacts cursor_shape.1 hrun⟩

/-- **Every `FN2-CURSOR` arm, handler and sub-arm moves a row only to its checked phases on every
run**: `PHASE` at every slot reads back as passed in or as the value of one of them. -/
theorem cursor_arm_next (a : Arm) (ha : a ∈ cursorK.subarms ++ cursorK.arms ++ cursorK.observes) :
    ∃ D, checkedNext world cursorK a = some D ∧
      ∀ observe args fuel v, runArm world cursorK a observe args fuel = .ok v →
        ∃ pre ts, v = Val.ofList (pre ++ ts) ∧ ts.length = cursorK.tuple.length ∧
          ∀ s, colGet world cursorK (stobj (tupleSt cursorK ts)) "PHASE" s =
              colGet world cursorK (stobj (Inv.startSt cursorK observe args)) "PHASE" s ∨
            ∃ p ∈ D, ∃ i, (p, i) ∈ cursorK.phases ∧
              colGet world cursorK (stobj (tupleSt cursorK ts)) "PHASE" s = .ok (.int i) := by
  have hall : (cursorK.subarms ++ cursorK.arms ++ cursorK.observes).all
      (fun a => (checkedNext world cursorK a).isSome) = true := by decide +kernel
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨D, hD, fun observe args fuel v hrun =>
    runArm_next_mem world cursorK a observe args fuel v D hD cursor_tableFacts cursor_shape.1
      cursor_shape.2 hrun⟩

/-- What the checks give for the `SEEK-NAME` sub-arm: it writes only `STEP` and moves no row to
another phase (every run leaves `PHASE` as it was). -/
theorem cursor_seek_name_contracts :
    (cursorK.subarms.find? (·.tag == "SEEK-NAME")).bind (checkedWrites world cursorK) = some ["STEP"] ∧
    (cursorK.subarms.find? (·.tag == "SEEK-NAME")).bind (checkedNext world cursorK) = some [] := by
  decide +kernel

end Fn2.Arms.ServedColumns

end
