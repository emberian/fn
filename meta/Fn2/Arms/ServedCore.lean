module

public import Fn2.Arms.Core
public import Fn2.Arms.ServedColumns
-- BEGIN world bodies (emit_embed.py): kinds FN2-CNS FN2-CONN; prefixes FN2-CNS- FN2-CONN- FN2-MACHINES-READY- FN2-MACHINES-SET-READY- FN2-MACHINES-WAIT-REASON FN2-MACHINES-SET-WAIT-REASON
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
import all Fn2.Instances.LayerAWorld.SCnsConnUpload_d6to14
import all Fn2.Instances.LayerAWorld.SCnsCursorSealer_d6to25
import all Fn2.Instances.LayerAWorld.S2_d0to29
import all Fn2.Instances.LayerAWorld.S5x3ecb87_d7to12
import all Fn2.Instances.LayerAWorld.S5x3ecb87_d13to16
import all Fn2.Instances.LayerAWorld.S5x3ecb87_d17to30
import all Fn2.Instances.LayerAWorld.S4x4f0c14_d2to35
import all Fn2.Instances.LayerAWorld.SAuthCnsTxn_d0to36
import all Fn2.Instances.LayerAWorld.SCnsCtl_d6to14
import all Fn2.Instances.LayerAWorld.KCns_d0to12
import all Fn2.Instances.LayerAWorld.KCns_d13to40
import all Fn2.Instances.LayerAWorld.KCommit_d5to22
import all Fn2.Instances.LayerAWorld.SConnCursor_d0to20
import all Fn2.Instances.LayerAWorld.SConnListener_d6to10
import all Fn2.Instances.LayerAWorld.KConn_d0to24
import all Fn2.Instances.LayerAWorld.KCtl_d0to26
import all Fn2.Instances.LayerAWorld.KListener_d0to16
import all Fn2.Instances.LayerAWorld.STxnUpload_d2to17
import all Fn2.Instances.LayerAWorld.Rest_d6b0
import all Fn2.Instances.LayerAWorld.Rest_d6b1
import all Fn2.Instances.LayerAWorld.Rest_d7b0
import all Fn2.Instances.LayerAWorld.Rest_d7b1
-- END world bodies
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.ServedCore: the contracts for the served core-form kinds `FN2-CNS` and `FN2-CONN`

Both kinds are in core form (`cns_core_form_refused`, `conn_core_form_refused`: `runArm` refuses
them); `Fn2.Arms.Core.runCore` runs them through their core face over the 57 children of
`fn2-core` (`coreTuple`, printed from `*fn2-core-children*`). Over that face:

* every `FN2-CNS` arm's charge is bounded by its derived bound on every run (`cns_core_charge`);
  `FN2-CONN`'s arms have no derived bound (`conn_derived_costs`: its sub-arms charge
  `(+ *FN2-CONN-FRAME-BYTES* LEN)` with `LEN` a `MIN` of world values, which the interval
  analysis does not bound), so no charge theorem for it here;
* every arm, handler and sub-arm of both keeps its frame: the core's children outside its
  derived children (and the control, which the refused entry's stop writes) come back as passed
  in (`cns_core_frame`, `conn_core_frame`);
* the world's `FN2-CNS` and `FN2-CONN` accessors keep the columns' frame (`cns_tableFacts`,
  `conn_tableFacts`, from the generated layout by the dispatch), so every arm writes only its
  checked columns (`cns_core_writes`, `conn_core_writes`), and every arm whose phases check moves
  a row only to them (`cns_core_next`, `conn_core_next`; the arms the check refuses, those
  reaching an operation that returns the kind's table, are `cns_next_unchecked` and
  `conn_next_unchecked`).
-/

namespace Fn2.Arms.ServedCore
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Cost Fn2.Arms.Frame Fn2.Arms.Columns Fn2.Arms.Core Fn2.Arms.Derive
open Fn2.Arms.Served Fn2.Arms.ServedColumns Fn2.Instances.LayerAKinds

/-- The core face's world and kinds. -/
def cw : World := coreWorld world coreTuple
def cnsC : Kind := coreKind cnsK coreTuple
def connC : Kind := coreKind connK coreTuple

theorem layout : coreTuple.length = 57 ∧ coreTuple.Nodup ∧
    cnsK.childForm = false ∧ connK.childForm = false := by
  decide +kernel

/-- `FN2-CNS`'s derived charge bounds over its core face: the same as from its declarations alone
(`cns_derived_costs`), every arm bounded. -/
theorem cns_core_derived_costs :
    cnsK.arms.map (fun a => (a.tag, derivedCost cw cnsC a)) =
      [(":FREE", some (0, 1, 0)), (":DECODE", some (4096, 24, 0)), (":CHECK", some (4096, 24, 0)),
       (":LOOKUP", some (4096, 24, 0)), (":READ", some (4096, 24, 0)), (":PAGE", some (4096, 24, 1)),
       (":FETCH", some (4096, 24, 0)), (":PARK", some (512, 24, 0)), (":COMMIT", some (512, 24, 0)),
       (":APPEND", some (2048, 24, 0)), (":DRAINING", some (0, 24, 0)), (":RETIRED", some (0, 1, 0))] := by
  decide +kernel

theorem work_empty : const world "*FN2-WORK-EMPTY*" = .ok (.int 1) := by decide +kernel

/-- **Every `FN2-CNS` arm's charge is bounded on every run of its arm function** by its derived
bound (the refused entry's `*fn2-work-empty*` included). -/
theorem cns_core_charge (a : Arm) (ha : a ∈ cnsK.arms) :
    ∃ C, derivedCost cw cnsC a = some C ∧
      ∀ args fuel v, runCore world coreTuple cnsK a false args fuel = .ok v →
        CostLe (extractCharge v) C := by
  have hall : cnsK.arms.all (fun a => match derivedCost cw cnsC a with
      | some C => decide (CostLe (0, 1, 0) C)
      | none => false) = true := by decide +kernel
  have h := List.all_eq_true.mp hall a ha
  split at h
  · rename_i C hC
    refine ⟨C, hC, fun args fuel v hrun => runCore_charge_le_cost world coreTuple cnsK a args fuel v C hC
      (fun e he => ?_) hrun⟩
    rw [work_empty] at he
    cases he
    simpa [Val.toInt] using h
  · cases h

/-- The `:COMMIT` arm (it calls `fn2-cns-commit-op`, an operation with no child form): at most
512 bytes, 24 steps and no descriptor per turn. -/
theorem cns_commit_charge (args : List Val) (fuel : Nat) (v : Val)
    (hrun : runCore world coreTuple cnsK (cnsK.arms.getD 8 default) false args fuel = .ok v) :
    CostLe (extractCharge v) (512, 24, 0) :=
  runCore_charge_le_cost world coreTuple cnsK _ args fuel v _ (by decide +kernel)
    (fun e he => by rw [work_empty] at he; cases he; decide) hrun

/-- **Every `FN2-CNS` arm, handler and sub-arm keeps its frame on every run of its function.** -/
theorem cns_core_frame (a : Arm) (ha : a ∈ cnsK.subarms ++ cnsK.arms ++ cnsK.observes) :
    ∃ D, derivedTables cw cnsC a = some D ∧
      ∀ observe args fuel v, runCore world coreTuple cnsK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧ pre.length = nRes observe ∧
          core'.toList.length = coreTuple.length ∧
          ∀ i (hi : i < coreTuple.length), coreTuple[i] ∉ D → coreTuple[i] ≠ "FN2-CONTROL" →
            core'.toList[i]? = (args.getLastD Val.nil).toList[i]? := by
  have hall : (cnsK.subarms ++ cnsK.arms ++ cnsK.observes).all
      (fun a => (derivedTables cw cnsC a).isSome) = true := by decide +kernel
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨D, hD, fun observe args fuel v hrun =>
    runCore_frame world coreTuple cnsK a observe args fuel v D hD layout.2.1 hrun⟩

/-- **Every `FN2-CONN` arm, handler and sub-arm keeps its frame on every run of its function.** -/
theorem conn_core_frame (a : Arm) (ha : a ∈ connK.subarms ++ connK.arms ++ connK.observes) :
    ∃ D, derivedTables cw connC a = some D ∧
      ∀ observe args fuel v, runCore world coreTuple connK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧ pre.length = nRes observe ∧
          core'.toList.length = coreTuple.length ∧
          ∀ i (hi : i < coreTuple.length), coreTuple[i] ∉ D → coreTuple[i] ≠ "FN2-CONTROL" →
            core'.toList[i]? = (args.getLastD Val.nil).toList[i]? := by
  have hall : (connK.subarms ++ connK.arms ++ connK.observes).all
      (fun a => (derivedTables cw connC a).isSome) = true := by decide +kernel
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨D, hD, fun observe args fuel v hrun =>
    runCore_frame world coreTuple connK a observe args fuel v D hD layout.2.1 hrun⟩

theorem cw_fns (f : String) (args : List Val) (h : f.endsWith "@CORE" = false) :
    cw.fns f args = world.fns f args := by
  simp [cw, coreWorld, coreFns, h]

/-- `FN2-CNS`'s table as the registry prints it (its fields in stobj order). -/
def cnsTable : List String :=
  ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "ACCOUNT-REF", "DEADLINE", "CTL", "CTL-GEN", "REQUEST", "FPOS", "FLEN", "FKIND", "VERB", "CONSUMER", "EPOCH", "OP", "TO", "CSTART", "PAGE-LIMIT", "WAIT-MS", "CPOS", "VERSION", "PUB-FRONTIER", "COUNT", "MORE", "OUTCOME", "REASON", "POSTED", "POSTED-WORD", "EDGE", "TXN", "TXN-GEN", "TX-SLOT", "TX-GEN", "UPLOAD", "UPLOAD-GEN", "FSTART", "FED", "FEED-MODE", "FEED-DISCARD", "NAME-OFF", "NAME-LEN", "XSTEP", "XHEAD", "XGRANT", "IPOS", "IOFF", "ILEN", "NPOS", "ART", "ISTREAM", "ITYPE", "ALEN", "LUNIT", "LEPOCH", "LALLOC", "LSLOT", "LGEN", "LEASE", "REVENT", "ROUTCOME", "RCOUNT", "RREADY", "PENDING", "CURSOR", "XROW", "STOPPED", "NEXT-FREE"]

set_option maxHeartbeats 0 in
/-- The registry's `FN2-CNS` accessors keep the columns' frame through the core face's world:
each own column is the `(NTH s (NTH i st))` / `UPDATE-NTH-ARRAY i` pair at its index in the table,
each directory field the same in `fn2-machines`, by the generated dispatch. -/
theorem cns_tableFacts : TableFacts cw cnsC := by
  have hn : cnsC.name = "FN2-CNS" := by decide +kernel
  have hown : ownCols cnsC = cnsTable := by decide +kernel
  have hdir : dirCols cnsC = ["READY-PREV", "READY-NEXT", "WAIT-REASON"] := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [hn, hown]
    refine facts_of cw cnsTable (fun c => "FN2-CNS" ++ "-" ++ c)
      (fun c => "FN2-CNS" ++ "-SET-" ++ c) (fun c => cnsTable.idxOf c) arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj _ a b ha hb h)
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [cnsTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
    · simp only [cnsTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
  · rw [hdir]
    refine facts_of cw _ (fun c => "FN2-MACHINES-" ++ c) (fun c => "FN2-MACHINES-SET-" ++ c)
      dirIdx arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj directoryFields a b (by simpa [directoryFields] using ha)
        (by simpa [directoryFields] using hb) (by simpa [dirIdx] using h))
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)

theorem cns_shape : kindShape cnsC = true ∧ phasesCover cnsC = true := by
  decide +kernel

/-- **Every `FN2-CNS` arm, handler and sub-arm writes only its checked columns on every run of
its function**: a column outside them (other than `PHASE`) reads back at every slot as in the
core it was passed. -/
theorem cns_core_writes (a : Arm) (ha : a ∈ cnsC.subarms ++ cnsC.arms ++ cnsC.observes) :
    ∃ W, checkedWrites cw cnsC a = some W ∧
      ∀ observe args fuel v, runCore world coreTuple cnsK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧
          ∀ c ∈ cnsC.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s,
            colGet cw cnsC (stobj (coreSt coreTuple core')) c s =
              colGet cw cnsC (stobj (coreSt coreTuple (args.getLastD Val.nil))) c s := by
  have hall : (cnsC.subarms ++ cnsC.arms ++ cnsC.observes).all
      (fun a => (checkedWrites cw cnsC a).isSome) = true := by decide +kernel
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨W, hW, fun observe args fuel v hrun =>
    runCore_writes_sub world coreTuple _ a observe args fuel v W hW cns_tableFacts cns_shape.1 hrun⟩

/-- **A `FN2-CNS` arm, handler or sub-arm whose phases check moves a row only to those phases on
every run of its function.** The check refuses an arm that calls an operation whose outputs hold
the kind's table: over the core face every core-only operation (no `:child`) returns the whole
core, so its arms are listed by `cns_next_unchecked`. -/
theorem cns_core_next (a : Arm) (D : List String) (hD : checkedNext cw cnsC a = some D) :
    ∀ observe args fuel v, runCore world coreTuple cnsK a observe args fuel = .ok v →
      ∃ pre core', v.toList = pre ++ [core'] ∧
        ∀ s, colGet cw cnsC (stobj (coreSt coreTuple core')) "PHASE" s =
          colGet cw cnsC (stobj (coreSt coreTuple (args.getLastD Val.nil))) "PHASE" s ∨
          ∃ p ∈ D, ∃ i, (p, i) ∈ cnsK.phases ∧
            colGet cw cnsC (stobj (coreSt coreTuple core')) "PHASE" s = .ok (.int i) := by
  intro observe args fuel v hrun
  exact runCore_next_mem world coreTuple _ [] (fun _ h => by simp at h) a observe args fuel v D hD cns_tableFacts cns_shape.1
      cns_shape.2 hrun

/-- The arms `cns_core_next` does not cover: each reaches an operation whose outputs hold `FN2-CNS`'s
table (a core-only operation's adapter returns every child of the core), so the check cannot bound
the phases it writes. -/
theorem cns_next_unchecked :
    (cnsC.subarms ++ cnsC.arms ++ cnsC.observes).filterMap
      (fun a => if (checkedNext cw cnsC a).isSome then none else some a.tag) =
      ["HAND", "ANSWER", "REFUSE", "PUT-ARTICLE", "PUT", "ITEM", "PAGE-END", "PAGE-FAIL", ":DECODE", ":CHECK", ":LOOKUP", ":READ", ":PAGE", ":FETCH", ":PARK", ":COMMIT", ":APPEND"] := by
  decide +kernel

/-- `FN2-CONN`'s table as the registry prints it (its fields in stobj order). -/
def connTable : List String :=
  ["PHASE", "GENERATION", "PRINCIPAL-SLOT", "ACCOUNT-REF", "DEADLINE", "CAP-INDEX", "CAP-NONCE", "RX-SLOT", "RX-GEN", "TX-SLOT", "TX-GEN", "START", "POS", "OVERFLOW", "COMPACTING", "CURSOR", "TX-OFF", "AFTER", "PENDING", "BORROWS", "MASK", "ORDINAL", "ACCESS-REF", "AUTH-PENDING", "REFUSED", "STOPPED", "NEXT-FREE", "UPLOAD", "UPLOAD-GEN", "RULE", "REQUEST", "FEED-MODE", "FEED-DISCARD", "FED", "WORD", "OUTCOME-READY", "POSTING", "PEER-FAMILY", "PEER-PORT", "PEER-W0", "PEER-W1", "PEER-W2", "PEER-W3", "QUERY", "QUERY-GEN", "LINE-S", "LINE-E", "GROUP", "CURRENT", "PIN"]

set_option maxHeartbeats 0 in
/-- The registry's `FN2-CONN` accessors keep the columns' frame through the core face's world:
each own column is the `(NTH s (NTH i st))` / `UPDATE-NTH-ARRAY i` pair at its index in the table,
each directory field the same in `fn2-machines`, by the generated dispatch. -/
theorem conn_tableFacts : TableFacts cw connC := by
  have hn : connC.name = "FN2-CONN" := by decide +kernel
  have hown : ownCols connC = connTable := by decide +kernel
  have hdir : dirCols connC = ["READY-PREV", "READY-NEXT", "WAIT-REASON"] := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [hn, hown]
    refine facts_of cw connTable (fun c => "FN2-CONN" ++ "-" ++ c)
      (fun c => "FN2-CONN" ++ "-SET-" ++ c) (fun c => connTable.idxOf c) arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj _ a b ha hb h)
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [connTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
    · simp only [connTable, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
  · rw [hdir]
    refine facts_of cw _ (fun c => "FN2-MACHINES-" ++ c) (fun c => "FN2-MACHINES-SET-" ++ c)
      dirIdx arrGet arrSet ?_ ?_
      (fun a ha b hb h => idxOf_inj directoryFields a b (by simpa [directoryFields] using ha)
        (by simpa [directoryFields] using hb) (by simpa [dirIdx] using h))
      (fun i j s s' v t h => arr_ne i j s s' v t h) (fun i s s' v t => arr_same i s s' v t)
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)
    · simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals intro s v t; exact callFn_of_fns _ _ _ _ (by decide) ((cw_fns _ _ (by decide +kernel)).trans rfl)

theorem conn_shape : kindShape connC = true ∧ phasesCover connC = true := by
  decide +kernel

/-- **Every `FN2-CONN` arm, handler and sub-arm writes only its checked columns on every run of
its function**: a column outside them (other than `PHASE`) reads back at every slot as in the
core it was passed. -/
theorem conn_core_writes (a : Arm) (ha : a ∈ connC.subarms ++ connC.arms ++ connC.observes) :
    ∃ W, checkedWrites cw connC a = some W ∧
      ∀ observe args fuel v, runCore world coreTuple connK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧
          ∀ c ∈ connC.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s,
            colGet cw connC (stobj (coreSt coreTuple core')) c s =
              colGet cw connC (stobj (coreSt coreTuple (args.getLastD Val.nil))) c s := by
  have hall : (connC.subarms ++ connC.arms ++ connC.observes).all
      (fun a => (checkedWrites cw connC a).isSome) = true := by decide +kernel
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨W, hW, fun observe args fuel v hrun =>
    runCore_writes_sub world coreTuple _ a observe args fuel v W hW conn_tableFacts conn_shape.1 hrun⟩

/-- **A `FN2-CONN` arm, handler or sub-arm whose phases check moves a row only to those phases on
every run of its function.** The check refuses an arm that calls an operation whose outputs hold
the kind's table: over the core face every core-only operation (no `:child`) returns the whole
core, so its arms are listed by `conn_next_unchecked`. -/
theorem conn_core_next (a : Arm) (D : List String) (hD : checkedNext cw connC a = some D) :
    ∀ observe args fuel v, runCore world coreTuple connK a observe args fuel = .ok v →
      ∃ pre core', v.toList = pre ++ [core'] ∧
        ∀ s, colGet cw connC (stobj (coreSt coreTuple core')) "PHASE" s =
          colGet cw connC (stobj (coreSt coreTuple (args.getLastD Val.nil))) "PHASE" s ∨
          ∃ p ∈ D, ∃ i, (p, i) ∈ connK.phases ∧
            colGet cw connC (stobj (coreSt coreTuple core')) "PHASE" s = .ok (.int i) := by
  intro observe args fuel v hrun
  exact runCore_next_mem world coreTuple _ [] (fun _ h => by simp at h) a observe args fuel v D hD conn_tableFacts conn_shape.1
      conn_shape.2 hrun

/-- The arms `conn_core_next` does not cover: each reaches an operation whose outputs hold `FN2-CONN`'s
table (a core-only operation's adapter returns every child of the core), so the check cannot bound
the phases it writes. -/
theorem conn_next_unchecked :
    (connC.subarms ++ connC.arms ++ connC.observes).filterMap
      (fun a => if (checkedNext cw connC a).isSome then none else some a.tag) =
      ["INPUT", "FRAME", ":GREETING", ":COMMAND", ":ARTICLE-INPUT", ":DRAINING", ":QUERY", ":RECEIVE-RESULT", ":SEND-RESULT"] := by
  decide +kernel

end Fn2.Arms.ServedCore

end
