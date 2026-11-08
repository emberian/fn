module

public import Fn2.Arms.Core
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.CoreTeeth: witnesses and mutants for the core-form contracts

A toy core-form kind over a five-child core (`toothCoreKind`, the echo tooth of `Fn2.Arms.Derive`
in core form) with an operation that exists only over the core (`FN2-CORE-BUMP`, called through
its adapter), its snapshot read code accepting id 0 and refusing any other.

* positive witnesses: every antecedent of each `runCore_*` theorem holds on a successful run,
  through the adapter included;
* teeth: the charge theorem's work-empty hypothesis and the frame theorem's control exclusion
  are each needed (a refused entry breaks the conclusion without them), and a write or phase
  outside the checked sets is visible in the returned core.
-/

namespace Fn2.Arms.CoreTeeth
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Cost Fn2.Arms.Frame Fn2.Arms.Columns Fn2.Arms.Core Fn2.Arms.Derive

def ctTuple : List String := ["FN2-ECHO", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"]

def toothCoreKind : Kind := { toothKind with childForm := false, tuple := ["FN2-CORE"] }

/-- `(:do (code) (fn2-core-bump 7) :accept (:ok))`, then the tooth's step: an arm that calls an
operation with no child form. -/
def coreArmBump : Arm :=
  { tag := ":COMMAND", sig := none, fn := "FN2-ECHO-RUN-COMMAND"
    decl := Val.ofList [
      Val.ofList [.sym ":DO", Val.ofList [.sym "CODE"], Val.ofList [.sym "FN2-CORE-BUMP", .int 7],
        .sym ":ACCEPT", Val.ofList [.sym ":OK"]],
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
      Val.ofList [.sym ":NEXT", .sym ":REPLY"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2]] }

def coreArmStep : Arm := { toothArmStep with sig := none, fn := "FN2-ECHO-RUN-COMMAND" }
def coreArmIdle : Arm := { toothArmIdle with sig := none, fn := "FN2-ECHO-RUN-FREE" }
def coreMutantWrites : Arm := { mutantArmWrites with sig := none, fn := "FN2-ECHO-RUN-COMMAND" }
def coreMutantNext : Arm := { mutantArmNext with sig := none, fn := "FN2-ECHO-RUN-COMMAND" }

def ctFns (empty : Int) : Fns
  | "FN2-ECHO-SNAPSHOT-READ-CODE", [.int 0, _] => some (.sym ":OK")
  | "FN2-ECHO-SNAPSHOT-READ-CODE", [_, _] => some (.sym ":KIND")
  | "FN2-MACHINE-SLOT", [_, _] => some (.int 0)
  | "FN2-CONTROL-RECORD-STOP", [r, _] => some (Val.ofList [r])
  -- over the whole core: answers :ok and replaces the pool child (the third)
  | "FN2-CORE-BUMP", [_, core] =>
    some (Val.ofList [.sym ":OK", Val.ofList (core.toList.set 2 (.sym "BUMPED-POOL"))])
  | "*EMPTY*", [] => some (.int empty)
  | f, args => toothFns f args

def ctWorld (empty : Int := 1) : World :=
  { toothWorld with
    ops := [{ name := "FN2-CORE-BUMP", callee := none, formals := [], stobjsIn := [], stobjsOut := []
              answers := .open_, bound := some (0, 0, 0)
              coreFormals := ["X", "FN2-CORE"], coreIn := [none, some "FN2-CORE"],
              coreOut := [none, some "FN2-CORE"] }]
    consts := [("*FN2-WORK-EMPTY*", .int empty), ("*FN2-WORK-MAILBOX*", .int 2), ("*FN2-ECHO-KIND*", .int 3),
               ("*FN2-STOP-REASON-MACHINE-PHASE*", .int 15), ("*FN2-STOP-REASON-MACHINE-WRITE*", .int 13),
               ("*FN2-NONE*", .int 4294967295)]
    fns := ctFns empty }

/-- The core it is passed: the echo table (phase 1, stopped 0, off 99), the directory, then the
pool, ops and control. -/
def ctCore : Val :=
  Val.ofList [Val.ofList [.int 1, .int 0, .int 99], Val.ofList [.int 0], .sym "ORIG-POOL",
    .sym "ORIG-OPS", .sym "ORIG-CTRL"]

def ctArgs (id : Int) : List Val := [.int id, .int 10, ctCore]

def runCT (a : Arm) (id : Int := 0) (empty : Int := 1) : Val :=
  match runCore (ctWorld empty) ctTuple toothCoreKind a false (ctArgs id) 20 with
  | .ok v => v
  | .error _ => Val.nil

def ctOut (a : Arm) (id : Int := 0) (empty : Int := 1) : Val := (runCT a id empty).toList.getLastD Val.nil

/-! ### The charge bound -/

/-- Positive witness: an arm calling the core-only operation through its adapter has the derived
bound `(64, 2, 0)`, which covers the work-empty steps, and its run charges exactly that. -/
theorem runCore_charge_pos :
    derivedCost (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmBump =
      some (64, 2, 0) ∧
    const (ctWorld) "*FN2-WORK-EMPTY*" = .ok (.int 1) ∧ CostLe (0, 1, 0) (64, 2, 0) ∧
    runCore (ctWorld) ctTuple toothCoreKind coreArmBump false (ctArgs 0) 20 = .ok (runCT coreArmBump) ∧
    extractCharge (runCT coreArmBump) = (64, 2, 0) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide +kernel⟩

/-- Tooth (hypothesis removal): with `*fn2-work-empty*` at 5 steps, above the bound's 2, a refused
entry (id 1: the snapshot code answers `:kind`) charges `(0, 5, 0)`, outside the bound derived for
the arm, which is unchanged: the work-empty hypothesis is needed. -/
theorem runCore_charge_needs_empty :
    derivedCost (coreWorld (ctWorld 5) ctTuple) (coreKind toothCoreKind ctTuple) coreArmStep =
      some (64, 2, 0) ∧
    runCore (ctWorld 5) ctTuple toothCoreKind coreArmStep false (ctArgs 1) 20 =
      .ok (runCT coreArmStep 1 5) ∧
    extractCharge (runCT coreArmStep 1 5) = (0, 5, 0) ∧ ¬ CostLe (0, 5, 0) (64, 2, 0) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide⟩

/-! ### The frame -/

/-- Positive witness: the bump arm's derived children include the pool (the adapter returns the
whole core), and its run does replace the pool; the step arm's derived children are the table,
the directory and the control, and its run returns the pool and the ops as passed in. -/
theorem runCore_frame_pos :
    (derivedTables (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmBump).map
      (·.contains "FN2-POOL") = some true ∧
    (ctOut coreArmBump).toList.getD 2 Val.nil = .sym "BUMPED-POOL" ∧
    derivedTables (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmStep =
      some ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL", "FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"] ∧
    runCore (ctWorld) ctTuple toothCoreKind coreArmStep false (ctArgs 0) 20 = .ok (runCT coreArmStep) ∧
    ((ctOut coreArmStep).toList.drop 2).take 2 = [.sym "ORIG-POOL", .sym "ORIG-OPS"] ∧
    (ctOut coreArmStep).toList.getD 0 Val.nil ≠ ctCore.toList.getD 0 Val.nil := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- Tooth (the control exclusion): the idle arm derives no children at all, and a refused entry
still writes the control (the core stops): the conclusion without the exclusion is false. -/
theorem runCore_frame_needs_control :
    derivedTables (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmIdle = some [] ∧
    runCore (ctWorld) ctTuple toothCoreKind coreArmIdle false (ctArgs 1) 20 = .ok (runCT coreArmIdle 1) ∧
    (ctOut coreArmIdle 1).toList.getD 4 Val.nil ≠ ctCore.toList.getD 4 Val.nil := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### Columns and phases -/

/-- Positive witness: the step arm's checked writes are `["OFF"]` and its checked phases
`[":REPLY"]`; its run leaves `STOPPED` as passed in and moves the row from phase 1 to 2, the value of
`:REPLY`. -/
theorem runCore_cols_pos :
    checkedWrites (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmStep = some ["OFF"] ∧
    checkedNext (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreArmStep = some [":REPLY"] ∧
    kindShape (coreKind toothCoreKind ctTuple) = true ∧ phasesCover (coreKind toothCoreKind ctTuple) = true ∧
    colGet (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple)
      (stobj (coreSt ctTuple (ctOut coreArmStep))) "STOPPED" (.int 0) = .ok (.int 0) ∧
    colGet (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple)
      (stobj (coreSt ctTuple (ctOut coreArmStep))) "PHASE" (.int 0) = .ok (.int 2) ∧
    colGet (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple)
      (stobj (coreSt ctTuple ctCore)) "PHASE" (.int 0) = .ok (.int 1) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

/-- Tooth: a write of `STOPPED` is in the mutant's checked writes and visible in the core it
returns; a move to `:CLOSING` is in the mutant's checked phases and visible as phase 3. -/
theorem runCore_cols_mutants :
    (checkedWrites (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreMutantWrites).map
      (·.contains "STOPPED") = some true ∧
    colGet (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple)
      (stobj (coreSt ctTuple (ctOut coreMutantWrites))) "STOPPED" (.int 0) = .ok (.int 1) ∧
    checkedNext (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple) coreMutantNext = some [":CLOSING"] ∧
    colGet (coreWorld (ctWorld) ctTuple) (coreKind toothCoreKind ctTuple)
      (stobj (coreSt ctTuple (ctOut coreMutantNext))) "PHASE" (.int 0) = .ok (.int 3) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end Fn2.Arms.CoreTeeth

end
