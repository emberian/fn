module

public import Fn2.Arms.Cost
public import Fn2.Arms.Frame
public import Fn2.Instances.LayerAKinds
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.Served: the proved contracts instantiated for served kinds of the registry

`FN2-CURSOR` is a served kind in child form: each of its arms' charge bound and frame is a theorem
about every run of the interpreter (`cursor_arm_charge`, `cursor_arm_frame`), with the bounds
themselves computed from the registry's declarations (`cursor_derived_costs`).

`FN2-CNS` and `FN2-CONN` are in core form: their arms take `fn2-core`, and the interpreter refuses
them (`cns_core_form_refused`, `conn_core_form_refused`), so no theorem about `runArm` can reach
them until they move to child form. What is derived from their declarations now is recorded:
`cns_derived_costs` (every arm bounded) and `conn_derived_costs` (no arm bounded: its sub-arms
charge `(+ *FN2-CONN-FRAME-BYTES* LEN)` with `LEN = (min .. (nfix (- CAP NFILL)))`, which the
interval analysis does not bound, `MIN` and `NFIX` being world functions).
-/

namespace Fn2.Arms.Served
open Fn2.ACL2 Fn2.Arms Fn2.Instances.LayerAKinds

def kindNamed (n : String) : Kind := (kinds.find? (·.name == n)).getD default

def cursorK : Kind := kindNamed "FN2-CURSOR"
def cnsK : Kind := kindNamed "FN2-CNS"
def connK : Kind := kindNamed "FN2-CONN"

/-- The registry's `FN2-CURSOR` arms and their derived charge bounds `(bytes, steps, descriptors)`. -/
theorem cursor_derived_costs :
    cursorK.childForm = true ∧
    cursorK.arms.map (fun a => (a.tag, Cost.derivedCost world cursorK a)) =
      [(":FREE", some (0, 1, 0)), (":SELECT", some (512, 24, 0)), (":SEEK", some (4096, 24, 0)),
       (":RENDER", some (8192, 24, 1)), (":SEND", some (0, 24, 0)), (":FETCH", some (8192, 24, 0)),
       (":FINISH", some (0, 24, 0)), (":DRAINING", some (0, 20, 0)), (":RETIRED", some (0, 1, 0))] := by
  decide +kernel

/-- **Every `FN2-CURSOR` arm's charge is bounded on every run** by its derived bound. -/
theorem cursor_arm_charge (a : Arm) (ha : a ∈ cursorK.arms) :
    ∃ C, Cost.derivedCost world cursorK a = some C ∧
      ∀ args fuel v, runArm world cursorK a false args fuel = .ok v →
        Cost.CostLe (Cost.extractCharge v) C := by
  have hall : cursorK.arms.all (fun a => (Cost.derivedCost world cursorK a).isSome) = true := by
    decide +kernel
  have := List.all_eq_true.mp hall a ha
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp this
  exact ⟨C, hC, fun args fuel v hrun => Cost.runArm_charge_le_cost world cursorK a args fuel v C hC hrun⟩

/-- The `:RENDER` arm, for instance: at most 8192 bytes, 24 steps and one descriptor per turn. -/
theorem cursor_render_charge (args : List Val) (fuel : Nat) (v : Val)
    (hrun : runArm world cursorK (cursorK.arms.getD 3 default) false args fuel = .ok v) :
    Cost.CostLe (Cost.extractCharge v) (8192, 24, 1) :=
  Cost.runArm_charge_le_cost world cursorK _ args fuel v _ (by decide +kernel) hrun

/-- **Every `FN2-CURSOR` arm, handler and sub-arm keeps its frame on every run**: the children
outside its derived set come back exactly as passed in. -/
theorem cursor_arm_frame (a : Arm) (ha : a ∈ cursorK.subarms ++ cursorK.arms ++ cursorK.observes) :
    ∃ D, Frame.derivedTables world cursorK a = some D ∧
      ∀ observe args fuel v, runArm world cursorK a observe args fuel = .ok v →
        ∃ pre ts, v.toList = pre ++ ts ∧ ts.length = cursorK.tuple.length ∧
          ∀ i (hi : i < cursorK.tuple.length), cursorK.tuple[i] ∉ D →
            ts[i]? = (args.drop (if observe then 10 else 5))[i]? := by
  have hall : (cursorK.subarms ++ cursorK.arms ++ cursorK.observes).all
      (fun a => (Frame.derivedTables world cursorK a).isSome) = true := by decide +kernel
  have hnd : cursorK.tuple.Nodup := by decide +kernel
  have := List.all_eq_true.mp hall a ha
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.mp this
  exact ⟨D, hD, fun observe args fuel v hrun =>
    Frame.runArm_frame world cursorK a observe args fuel v D hD hnd hrun⟩

/-- `:SELECT` can write only the cursor table, the directory and the control: the other 17 of the
20 children of its tuple are untouched by every run. -/
theorem cursor_select_tables :
    (Frame.derivedTables world cursorK (cursorK.arms.getD 1 default)).map
      (fun D => cursorK.tuple.filter (D.contains ·)) =
      some ["FN2-CURSOR", "FN2-MACHINES", "FN2-CONTROL"] := by
  decide +kernel

/-- `FN2-CNS` is in core form: the interpreter refuses each of its arms. -/
theorem cns_core_form_refused (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat) :
    (runArm world cnsK a observe args fuel).toOption = none := by
  have h : cnsK.childForm = false := by decide +kernel
  simp [runArm, h, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- `FN2-CONN` is in core form: the interpreter refuses each of its arms. -/
theorem conn_core_form_refused (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat) :
    (runArm world connK a observe args fuel).toOption = none := by
  have h : connK.childForm = false := by decide +kernel
  simp [runArm, h, throw, throwThe, MonadExceptOf.throw, Except.toOption]

/-- The charge bounds derived from `FN2-CNS`'s declarations (not yet linked to a run: core form). -/
theorem cns_derived_costs :
    cnsK.arms.map (fun a => (a.tag, Cost.derivedCost world cnsK a)) =
      [(":FREE", some (0, 1, 0)), (":DECODE", some (4096, 24, 0)), (":CHECK", some (4096, 24, 0)),
       (":LOOKUP", some (4096, 24, 0)), (":READ", some (4096, 24, 0)), (":PAGE", some (4096, 24, 1)),
       (":FETCH", some (4096, 24, 0)), (":PARK", some (512, 24, 0)), (":COMMIT", some (512, 24, 0)),
       (":APPEND", some (2048, 24, 0)), (":DRAINING", some (0, 24, 0)), (":RETIRED", some (0, 1, 0))] := by
  decide +kernel

/-- `FN2-CONN`'s declarations admit no derived charge bound for any arm (see the module doc). -/
theorem conn_derived_costs :
    connK.arms.all (fun a => (Cost.derivedCost world connK a).isNone) = true := by
  decide +kernel

end Fn2.Arms.Served

end
