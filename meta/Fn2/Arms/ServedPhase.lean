module

public import Fn2.Instances.LayerAPhase
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.ServedPhase: every served core-form arm's phases, checked

`Fn2.Arms.ServedCore.cns_core_next` and `conn_core_next` cover the arms whose phase check admits
every operation they call; the check refuses an operation whose `stobjs-out` hold the kind's table,
and over the core face every core-only operation returns the whole core (`cns_next_unchecked`,
`conn_next_unchecked`). Each such operation's translation keeps the kind's `PHASE` column of the
core it is passed (`Fn2.Instances.LayerAPres`, proved from the translation; a countdown loop by
induction on its fuel), so its call keeps the arm's `PHASE` column (`Fn2.Arms.CorePhase`,
`Fn2.Instances.LayerAPhase`: `cnsPK`, `connPK`). With those operations admitted
(`Fn2.Arms.Columns.checkedNextP`), the check covers every arm, handler and sub-arm of both kinds:
`cns_core_next_all`, `conn_core_next_all`, and `cns_next_checked`, `conn_next_checked` (none left).
-/

namespace Fn2.Arms.ServedPhase
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Arms.Columns Fn2.Arms.ServedCore
open Fn2.Instances.LayerAKinds Fn2.Instances.LayerAPhase

/-- No `FN2-CNS` arm, handler or sub-arm is left unchecked once its kind-table operations are
admitted by their `KeepsPhase`. -/
theorem cns_next_checked :
    (cnsC.subarms ++ cnsC.arms ++ cnsC.observes).filterMap
      (fun a => if (checkedNextP cw cnsC cnsPK a).isSome then none else some a.tag) = [] := by
  decide +kernel

/-- No `FN2-CONN` arm, handler or sub-arm is left unchecked. -/
theorem conn_next_checked :
    (connC.subarms ++ connC.arms ++ connC.observes).filterMap
      (fun a => if (checkedNextP cw connC connPK a).isSome then none else some a.tag) = [] := by
  decide +kernel

/-- **Every `FN2-CNS` arm, handler and sub-arm moves a row only to its checked phases on every run
of its function.** -/
theorem cns_core_next_all (a : Arm) (ha : a ∈ cnsC.subarms ++ cnsC.arms ++ cnsC.observes) :
    ∃ D, checkedNextP cw cnsC cnsPK a = some D ∧
      ∀ observe args fuel v, runCore world coreTuple Served.cnsK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧
          ∀ s, colGet cw cnsC (stobj (coreSt coreTuple core')) "PHASE" s =
            colGet cw cnsC (stobj (coreSt coreTuple (args.getLastD Val.nil))) "PHASE" s ∨
            ∃ p ∈ D, ∃ i, (p, i) ∈ Served.cnsK.phases ∧
              colGet cw cnsC (stobj (coreSt coreTuple core')) "PHASE" s = .ok (.int i) := by
  have hall : (cnsC.subarms ++ cnsC.arms ++ cnsC.observes).all
      (fun a => (checkedNextP cw cnsC cnsPK a).isSome) = true := by decide +kernel
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨D, hD, fun observe args fuel v hrun =>
    runCore_next_mem world coreTuple _ cnsPK cns_keeps a observe args fuel v D hD cns_tableFacts
      cns_shape.1 cns_shape.2 hrun⟩

/-- **Every `FN2-CONN` arm, handler and sub-arm moves a row only to its checked phases on every
run of its function.** -/
theorem conn_core_next_all (a : Arm) (ha : a ∈ connC.subarms ++ connC.arms ++ connC.observes) :
    ∃ D, checkedNextP cw connC connPK a = some D ∧
      ∀ observe args fuel v, runCore world coreTuple Served.connK a observe args fuel = .ok v →
        ∃ pre core', v.toList = pre ++ [core'] ∧
          ∀ s, colGet cw connC (stobj (coreSt coreTuple core')) "PHASE" s =
            colGet cw connC (stobj (coreSt coreTuple (args.getLastD Val.nil))) "PHASE" s ∨
            ∃ p ∈ D, ∃ i, (p, i) ∈ Served.connK.phases ∧
              colGet cw connC (stobj (coreSt coreTuple core')) "PHASE" s = .ok (.int i) := by
  have hall : (connC.subarms ++ connC.arms ++ connC.observes).all
      (fun a => (checkedNextP cw connC connPK a).isSome) = true := by decide +kernel
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hall a ha)
  exact ⟨D, hD, fun observe args fuel v hrun =>
    runCore_next_mem world coreTuple _ connPK conn_keeps a observe args fuel v D hD conn_tableFacts
      conn_shape.1 conn_shape.2 hrun⟩

end Fn2.Arms.ServedPhase

end
