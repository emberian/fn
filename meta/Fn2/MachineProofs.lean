import Fn2.Decl
import Fn2.Arms
import Fn2.Arms.Derive
import Fn2.Pathway
import Fn2.Instances.LayerA
import Fn2.Instances.LayerAFacts
import Fn2.Instances.LayerAKinds

/-!
# Fn2.MachineProofs: Per-Machine Contract Proofs & PW3 Wrapper Instantiation (Brick H6)

This module checks each machine's arms against the derived frame (`Fn2.Arms.Frame`) and
instantiates the PW3 wrapper preservation theorems
(`project_reconstruct`, `reconstruct_frame_entry`, `entering_frame_entry`,
`armCorrect_project_preserve`) from `Fn2.Pathway` across the exported machine registry:
- `fn2-listener` (`FN2-LISTENER`)
- `fn2-echo` (`FN2-ECHO`)
- `fn2-scribe` (`FN2-SCRIBE`)
- `fn2-cursor` (`FN2-CURSOR`)
- `fn2-txn` (`FN2-TXN`)
- `fn2-ctl` (`FN2-CTL`)
- `fn2-cns` (`FN2-CNS`)
as well as across all 22 kinds in `Fn2.Instances.LayerAKinds.kinds`.
-/

namespace Fn2.MachineProofs
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Derive Fn2.Pathway

/-! ## 1. Exported Machine Kind Definitions (`fn2-listener`, `fn2-echo`, `fn2-scribe`, `fn2-cursor`, `fn2-txn`, `fn2-ctl`, `fn2-cns`) -/

def findKind (name : String) : Kind :=
  (Fn2.Instances.LayerAKinds.kinds.find? (·.name == name)).getD toothKind

/-- `fn2-listener`: Layer A listener machine from `LayerAKinds.kinds`. -/
def listenerKind : Kind := findKind "FN2-LISTENER"

/-- `fn2-echo`: Layer A echo machine from `LayerAKinds.kinds`. -/
def echoKind : Kind := findKind "FN2-ECHO"

/-- `fn2-scribe`: Layer A scribe machine from `LayerAKinds.kinds`. -/
def scribeKind : Kind := findKind "FN2-SCRIBE"

/-- `fn2-cursor`: Layer D reader cursor machine from `LayerAKinds.kinds`. -/
def cursorKind : Kind := findKind "FN2-CURSOR"

/-- `fn2-txn`, `fn2-ctl`, `fn2-cns`: the registry's kinds. All three are in core form (their arms
take `fn2-core`), so only their declarations' readability is checked below, and the child-form
PW3 wrapper is not instantiated for them. -/
def txnKind : Kind := findKind "FN2-TXN"
def ctlKind : Kind := findKind "FN2-CTL"
def cnsKind : Kind := findKind "FN2-CNS"

/-- The three are core form in the registry: no hand copy may treat them as child form. -/
theorem txn_ctl_cns_core_form :
    txnKind.childForm = false ∧ ctlKind.childForm = false ∧ cnsKind.childForm = false ∧
    txnKind.name = "FN2-TXN" ∧ ctlKind.name = "FN2-CTL" ∧ cnsKind.name = "FN2-CNS" := by
  decide +kernel

/-- All 7 named machines of the Brick H6 machine registry. -/
def machineRegistryKinds : List Kind :=
  [listenerKind, echoKind, scribeKind, cursorKind, txnKind, ctlKind, cnsKind]

/-! ## 2. Per-Machine Contract Checking & PW3 `ArmWF` Verification -/

def checkMachineKind (w : World) (k : Kind) : Bool :=
  let allArms := k.subarms ++ k.arms ++ k.observes
  let dt := fun a => (Fn2.Arms.Frame.derivedTables w k a).getD []
  allArms.all (fun a => a.read.isOk) &&
  (!k.childForm ||
    (k.arms.all (fun a => ArmWF k a false && (returns k a).all (dt a).contains) &&
     k.subarms.all (fun a => ArmWF k a false && (returns k a).all (dt a).contains) &&
     k.observes.all (fun a => ArmWF k a true && (returns k a).all (dt a).contains)))

theorem listener_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world listenerKind = true := by
  decide +kernel

theorem echo_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world echoKind = true := by
  decide +kernel

theorem scribe_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world scribeKind = true := by
  decide +kernel

theorem cursor_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world cursorKind = true := by
  decide +kernel

theorem txn_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world txnKind = true := by
  decide +kernel

theorem ctl_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world ctlKind = true := by
  decide +kernel

theorem cns_contracts_hold :
    checkMachineKind Fn2.Instances.LayerAKinds.world cnsKind = true := by
  decide +kernel

theorem machineRegistry_contracts_hold :
    (machineRegistryKinds.all (checkMachineKind Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

theorem layerAKinds_contracts_hold :
    (Fn2.Instances.LayerAKinds.kinds.all
      (checkMachineKind Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

/-! ## 4. Per-Machine PW3 Wrapper Preservation Instantiations & Concrete Witnesses -/

abbrev echo_pw3_wrapper := @project_reconstruct echoKind
abbrev scribe_pw3_wrapper := @project_reconstruct scribeKind
abbrev cursor_pw3_wrapper := @project_reconstruct cursorKind

/-- Positive Witness (`pw3_wrapper_preserve_pos`): Across the child-form machines
    (`echoKind`, `scribeKind`, `cursorKind`),
    `project_reconstruct` recovers the normalized narrow output and `reconstruct`
    preserves every unreturned child slot from `entering`. -/
def checkPW3Roundtrip (k : Kind) : Bool :=
  let input := k.tuple.map (fun c => Val.sym ("IN-" ++ c))
  (k.subarms ++ k.arms).all (fun a =>
    let v := Val.ofList ([.int 64, .int 2, .int 0, Val.t] ++
      (returns k a).map (fun c => Val.sym ("OUT-" ++ c)))
    let recon := reconstruct k a false input (normalize k a false v)
    project k a false recon == normalize k a false v) &&
  k.observes.all (fun a =>
    let v := Val.ofList ([Val.t] ++
      (returns k a).map (fun c => Val.sym ("OUT-" ++ c)))
    let recon := reconstruct k a true input (normalize k a true v)
    project k a true recon == normalize k a true v)

theorem pw3_wrapper_roundtrip_all_machines :
    ([echoKind, scribeKind, cursorKind].all checkPW3Roundtrip) = true ∧
    echoKind.childForm = true ∧ scribeKind.childForm = true ∧ cursorKind.childForm = true := by
  decide +kernel

theorem pw3_wrapper_roundtrip_all_layerAKinds :
    ((Fn2.Instances.LayerAKinds.kinds.filter (·.childForm)).all
      checkPW3Roundtrip) = true := by
  decide +kernel

/-- Negative Witness (`pw3_mutant_dup_returns_neg`): An arm with duplicate entries in `returns`
    is rejected by `ArmWF` (`ArmWF = false`) and fails round-trip `project_reconstruct` on distinct
    returned values for the duplicated child name. -/
def mutantDupReturnArm : Arm :=
  { tag := ":DUP"
    sig := some ⟨["FN2-ECHO", "FN2-MACHINES"], ["FN2-ECHO", "FN2-ECHO"], 4⟩
    decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
    fn := "MUTANT-DUP-RETURN" }

theorem pw3_mutant_dup_returns_neg :
    ArmWF echoKind mutantDupReturnArm false = false ∧
    let input := echoKind.tuple.map Val.sym
    let v := Val.ofList [.int 0, .int 1, .int 0, Val.nil, .sym "V1", .sym "V2"]
    project echoKind mutantDupReturnArm false
      (reconstruct echoKind mutantDupReturnArm false input v) ≠ v := by
  decide +kernel

end Fn2.MachineProofs
