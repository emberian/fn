import Fn2.Arms
import Fn2.ArmsLemmas
import Fn2.Pathway
import Fn2.Arms.Cost
import Fn2.Arms.Frame
import Fn2.Instances.LayerAKinds

/-!
# Fn2.Arms.Derive: declaration-derived contracts, their teeth, and agreement over LayerA

The contracts proved over the interpreter live beside this file:
* `Fn2.Arms.Cost.runArm_charge_le_cost`: a run arm charges at most `Cost.derivedCost`;
* `Fn2.Arms.Frame.runArm_frame`: children outside `Frame.derivedTables` come back unchanged.

This file keeps three further derivations read off a declaration, `derivedWrites` (row
columns), `derivedNext` (phases) and `derivedHolds` (D0 hold effects). They are computed
contracts, checked against concrete runs below; no theorem yet relates them to every run
(the columns a run writes and the phase it leaves are only visible through the world's table
accessors). Section 6 holds positive witnesses and mutant teeth for the proved contracts, and
the agreement check over the exported child-form kinds.
-/

namespace Fn2.Arms.Derive
open Fn2.ACL2 Fn2.Arms Fn2.Pathway

/-! ## 1. Shared pieces of the remaining derivations -/

/-- Row columns (excluding `"PHASE"`) written by a `:park` terminal. -/
def parkWrites (w : World) (wait : String) : List String :=
  match wait with
  | "POOL" => ["CURSOR", "WAIT-REASON"]
  | "OPERATION" | "ADMISSION" | "TAKEN" => []
  | other =>
    match w.waits.find? (·.kind == other) with
    | some ⟨_, none⟩ => ["WAIT-REASON"]
    | _ => []

/-- Phase names reachable from a `:next` expression `ph`. -/
def nextExprPhasesF (k : Kind) (rec : Expr → List String) : Expr → List String
  | .sym p =>
    if k.phases.any (·.1 == p) then [p]
    else if p.startsWith "ROW-" && k.columns.any (·.1 == (p.drop 4).toString) then k.states
    else []
  | .cons (.sym ":IF") rest =>
    match rest.toList with
    | [_, a, b] => rec a ++ rec b
    | _ => []
  | .cons (.sym ":CASE") rest =>
    rest.cdr.toList.flatMap fun arm => rec arm.cdr.car
  | _ => []

def nextExprPhases (k : Kind) : Expr → List String :=
  fixN 32 (nextExprPhasesF k) (fun _ => [])

/-- Resource/wait hold effects associated with a declared operation. -/
def opHolds (op : String) : List String :=
  if op == "FN2-CORE-RESERVE" then [":POOL-RESERVE"]
  else if op == "FN2-CORE-RELEASE" || op == "FN2-CORE-ACCEPT-HAND" then [":POOL-RELEASE"]
  else if op == "FN2-READ-LOOKUP" || op == "FN2-READ-RANGE" ||
          op == "FN2-READ-SCAN" || op == "FN2-READ-IDENTITY" then [":READ-CURSOR"]
  else if op == "FN2-READ-RELEASE" then [":READ-RELEASE"]
  else if op == "FN2-MACHINE-RECLAIM" || op == "FN2-CURSOR-RECLAIM" then [":ROW-RECLAIM"]
  else []


/-! ### 2.2 `stepWrites` / `stepsWrites` (by structural recursion on `Step` / `List Step`) -/

mutual
def stepWrites (w : World) (refW : List String) (subW : String → List String) :
    Step → List String
  | .let_ _ _ | .next _ | .repeatNext | .wakeRow _
  | .charge _ _ _ _ | .idle | .yield | .wake | .nowake | .stop _ _ => []
  | .set pairs => pairs.map (·.1)
  | .do_ _ _ _ _ _ _ cases => refW ++ casesWrites w refW subW cases
  | .issue _ ok refused =>
    stepsWrites w refW subW ok ++ stepsWrites w refW subW refused ++
      ["STOPPED", "WAIT-REASON"] ++ refW
  | .repeat_ _ body _ => stepsWrites w refW subW body
  | .if_ _ a b => stepsWrites w refW subW a ++ stepsWrites w refW subW b
  | .cond clauses => clausesWrites w refW subW clauses
  | .case_ _ arms => casesWrites w refW subW arms
  | .wait _ _ => ["PENDING", "WAIT-REASON"]
  | .halt => ["STOPPED", "WAIT-REASON"]
  | .park wait _ _ _ _ => parkWrites w wait
  | .goto name => subW name

def stepsWrites (w : World) (refW : List String) (subW : String → List String) :
    List Step → List String
  | [] => []
  | s :: ss => stepWrites w refW subW s ++ stepsWrites w refW subW ss

def casesWrites (w : World) (refW : List String) (subW : String → List String) :
    List (Option (List Val) × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsWrites w refW subW ss ++ casesWrites w refW subW cs

def clausesWrites (w : World) (refW : List String) (subW : String → List String) :
    List (Expr × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsWrites w refW subW ss ++ clausesWrites w refW subW cs
end

/-! ### 2.3 `stepHolds` / `stepsHolds` (by structural recursion on `Step` / `List Step`) -/

mutual
def stepHolds (refH : List String) (subH : String → List String) :
    Step → List String
  | .let_ _ _ | .set _ | .next _ | .repeatNext
  | .charge _ _ _ _ | .idle | .yield | .halt | .nowake | .stop _ _ => []
  | .wakeRow _ | .wake => [":WAKE"]
  | .wait _ _ => [":COMPLETION"]
  | .park wait _ _ _ _ => [":" ++ wait]
  | .do_ _ c _ _ _ _ cases =>
    opHolds c.op ++ refH ++ casesHolds refH subH cases
  | .issue c ok refused =>
    [":OPERATION", c.op] ++ stepsHolds refH subH ok ++ stepsHolds refH subH refused ++
      [":OPERATION"] ++ refH
  | .repeat_ _ body _ => stepsHolds refH subH body
  | .if_ _ a b => stepsHolds refH subH a ++ stepsHolds refH subH b
  | .cond clauses => clausesHolds refH subH clauses
  | .case_ _ arms => casesHolds refH subH arms
  | .goto name => subH name

def stepsHolds (refH : List String) (subH : String → List String) :
    List Step → List String
  | [] => []
  | s :: ss => stepHolds refH subH s ++ stepsHolds refH subH ss

def casesHolds (refH : List String) (subH : String → List String) :
    List (Option (List Val) × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsHolds refH subH ss ++ casesHolds refH subH cs

def clausesHolds (refH : List String) (subH : String → List String) :
    List (Expr × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsHolds refH subH ss ++ clausesHolds refH subH cs
end

/-! ### 2.4 `stepNext` / `stepsNext` (by structural recursion on `Step` / `List Step`) -/

def joinNext (a b : List String × Bool) : List String × Bool :=
  (a.1 ++ b.1, a.2 || b.2)

mutual
def stepNext (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool) :
    Step → List String × Bool
  | .let_ _ _ | .set _ | .wakeRow _ => ([], false)
  | .next ph => (nextExprPhases k ph, false)
  | .repeat_ _ body _ =>
    let (bp, _) := stepsNext k refN subN false body
    (bp, false)
  | .repeatNext => ([], !hasNext)
  | .do_ _ _ _ _ _ _ cases =>
    joinNext (casesNext k refN subN hasNext cases) (refN hasNext)
  | .issue _ ok refused =>
    let cOk := stepsNext k refN subN hasNext ok
    let cEx := joinNext (stepsNext k refN subN hasNext refused) ([], !hasNext)
    let cOt := joinNext (stepsNext k refN subN hasNext refused) (refN hasNext)
    joinNext cOk (joinNext cEx cOt)
  | .if_ _ a b =>
    joinNext (stepsNext k refN subN hasNext a) (stepsNext k refN subN hasNext b)
  | .cond clauses => clausesNext k refN subN hasNext clauses
  | .case_ _ arms => casesNext k refN subN hasNext arms
  | .charge _ _ _ _ | .idle | .yield | .wait _ _ | .halt | .park _ _ _ _ _
  | .stop _ _ | .wake | .nowake => ([], !hasNext)
  | .goto name => subN hasNext name

def stepsNext (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool) :
    List Step → List String × Bool
  | [] => ([], false)
  | s :: rest =>
    let hasNext' := match s with | .next _ => true | _ => hasNext
    joinNext (stepNext k refN subN hasNext s) (stepsNext k refN subN hasNext' rest)

def casesNext (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool) :
    List (Option (List Val) × List Step) → List String × Bool
  | [] => ([], false)
  | (_, ss) :: cs =>
    joinNext (stepsNext k refN subN hasNext ss) (casesNext k refN subN hasNext cs)

def clausesNext (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool) :
    List (Expr × List Step) → List String × Bool
  | [] => ([], false)
  | (_, ss) :: cs =>
    joinNext (stepsNext k refN subN hasNext ss) (clausesNext k refN subN hasNext cs)
end

/-! ## 2. Top-Level `Arm` Contract Functions (writes, next, holds) -/

def subWrites (w : World) (k : Kind) : Nat → String → List String
  | 0, _ => []
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refW := stepsWrites w [] (subWrites w k d) decl.onRefusal
        stepsWrites w refW (subWrites w k d) decl.steps
      | .error _ => []
    | none => []

/-- `derivedWrites w k a`: row columns (excluding `"PHASE"`) that `a` can mutate. -/
def derivedWrites (w : World) (k : Kind) (a : Arm) : List String :=
  match a.read with
  | .ok decl =>
    let subW := subWrites w k (k.subarms.length + 1)
    let refW := stepsWrites w [] subW decl.onRefusal
    (stepsWrites w refW subW decl.steps).eraseDups
  | .error _ => []

def subNext (k : Kind) : Nat → Bool → String → List String × Bool
  | 0, hasNext, _ => ([], !hasNext)
  | d + 1, hasNext, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refN := fun hn =>
          if decl.onRefusal.isEmpty then ([], !hn)
          else stepsNext k (fun h => ([], !h)) (subNext k d) hn decl.onRefusal
        stepsNext k refN (subNext k d) hasNext decl.steps
      | .error _ => ([], !hasNext)
    | none => ([], !hasNext)

/-- `derivedNext w k a`: phase symbols reachable at the end of `a`. -/
def derivedNext (_w : World) (k : Kind) (a : Arm) : List String :=
  match a.read with
  | .ok decl =>
    let subN := subNext k (k.subarms.length + 1)
    let refN := fun hn =>
      if decl.onRefusal.isEmpty then ([], !hn)
      else stepsNext k (fun h => ([], !h)) subN hn decl.onRefusal
    let (phs, stay) := stepsNext k refN subN false decl.steps
    let stayPhases :=
      if !stay then []
      else if k.states.contains a.tag then [a.tag]
      else decl.from_
    (phs ++ stayPhases).eraseDups
  | .error _ => []

def subHolds (k : Kind) : Nat → String → List String
  | 0, _ => []
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refH := stepsHolds [] (subHolds k d) decl.onRefusal
        stepsHolds refH (subHolds k d) decl.steps
      | .error _ => []
    | none => []

/-- `derivedHolds w k a`: D0 resource/wait/operation hold effects synthesized from `a`. -/
def derivedHolds (_w : World) (k : Kind) (a : Arm) : List String :=
  match a.read with
  | .ok decl =>
    let subH := subHolds k (k.subarms.length + 1)
    let refH := stepsHolds [] subH decl.onRefusal
    (stepsHolds refH subH decl.steps).eraseDups
  | .error _ => []


/-! ## 3. Positive Witnesses, Mutant Teeth, and Agreement -/

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
    if h : a = b then isTrue (by subst h; rfl)
    else isFalse (by intro hc; exact h (Except.ok.inj hc))
  | .error a, .error b =>
    if h : a = b then isTrue (by subst h; rfl)
    else isFalse (by intro hc; exact h (Except.error.inj hc))
  | .ok _, .error _ => isFalse (by intro hc; nomatch hc)
  | .error _, .ok _ => isFalse (by intro hc; nomatch hc)

/-- A concrete child-form test kind and world for exercising `runArm`, positive witnesses,
    and mutant-declaration negative teeth. -/
def toothKind : Kind :=
  { name := "FN2-ECHO"
    childForm := true
    tuple := ["FN2-ECHO", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"]
    states := [":FREE", ":COMMAND", ":REPLY", ":CLOSING", ":DRAINING", ":RETIRED"]
    phases := [(":FREE", 0), (":COMMAND", 1), (":REPLY", 2), (":CLOSING", 3),
               (":DRAINING", 4), (":RETIRED", 5)]
    columns := [("PHASE", .enum 6), ("STOPPED", .uw 1), ("OFF", .uw 32), ("WAIT-REASON", .enum 26)]
    table := ["PHASE", "STOPPED", "OFF"]
    stops := []
    links := []
    subarms := []
    arms := []
    observes := [] }

def toothArmIdle : Arm :=
  { tag := ":FREE"
    sig := some ⟨["FN2-ECHO", "FN2-MACHINES"], [], 4⟩
    decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
    fn := "FN2-ECHO-RUN-FREE-CHILDREN" }

def toothArmStep : Arm :=
  { tag := ":COMMAND"
    sig := some ⟨["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"],
                 ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
    decl := Val.ofList [
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
      Val.ofList [.sym ":NEXT", .sym ":REPLY"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2]
    ]
    fn := "FN2-ECHO-RUN-COMMAND-CHILDREN" }

/-- Mutant 1 (Cost Mutant): charges 999 bytes instead of 64, exceeding `toothArmStep`'s `derivedCost`. -/
def mutantArmCost : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
      Val.ofList [.sym ":NEXT", .sym ":REPLY"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 999, .sym ":STEPS", .int 2]
    ] }

/-- Mutant 2 (Writes Mutant): mutates `"STOPPED"`, which is outside `derivedWrites _ toothKind toothArmStep`. -/
def mutantArmWrites : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0], Val.ofList [.sym "STOPPED", .int 1]],
      Val.ofList [.sym ":NEXT", .sym ":REPLY"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2]
    ] }

/-- Mutant 3 (Next-Phase Mutant): transitions to `:CLOSING`, outside `derivedNext _ toothKind toothArmStep`. -/
def mutantArmNext : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
      Val.ofList [.sym ":NEXT", .sym ":CLOSING"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2]
    ] }

/-- Mutant 4 (Frame/Tables Mutant): touches `"FN2-POOL"` via `FN2-CORE-RESET`, outside `toothArmStep`'s `derivedTables`. -/
def mutantArmTables : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":DO", Val.ofList [.sym "CODE"],
        Val.ofList [.sym "FN2-CORE-RESET", .int 0, .int 0],
        .sym ":ACCEPT", Val.ofList [.sym ":OK"]],
      Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
      Val.ofList [.sym ":NEXT", .sym ":REPLY"],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2]
    ] }

def toothFns : Fns
  | "FN2-ECHO-ROWS", [_] => some (.int 4)
  | "FN2-MACHINES-ROWS", [_] => some (.int 4)
  | "FN2-ECHO-PHASE", [_, t] => some (Native.nth (.int 0) t)
  | "FN2-ECHO-STOPPED", [_, t] => some (Native.nth (.int 1) t)
  | "FN2-ECHO-OFF", [_, t] => some (Native.nth (.int 2) t)
  | "FN2-MACHINES-WAIT-REASON", [_, d] => some (Native.nth (.int 0) d)
  | "FN2-ECHO-SET-PHASE", [_, v, t] => some (Native.updateNth (.int 0) v t)
  | "FN2-ECHO-SET-STOPPED", [_, v, t] => some (Native.updateNth (.int 1) v t)
  | "FN2-ECHO-SET-OFF", [_, v, t] => some (Native.updateNth (.int 2) v t)
  | "FN2-MACHINES-SET-WAIT-REASON", [_, v, d] => some (Native.updateNth (.int 0) v d)
  | "FN2-POOL-RESET", [_, _, _] => some (Val.ofList [.sym ":OK", .sym "MUTATED-POOL"])
  | _, _ => none

def toothWorld : World :=
  { kinds := [toothKind]
    ops := [{ name := "FN2-CORE-RESET"
              callee := some "FN2-POOL-RESET"
              formals := ["SLOT", "GEN", "FN2-POOL"]
              stobjsIn := [none, none, some "FN2-POOL"]
              stobjsOut := [none, some "FN2-POOL"]
              answers := .open_
              bound := some (0, 0, 0) }]
    waits := []
    consts := [("*FN2-WORK-EMPTY*", .int 1), ("*FN2-WORK-MAILBOX*", .int 2)]
    fns := toothFns }

def toothArgs : List Val :=
  [.int 0, .int 0, .int 0, .int 0, .int 10,
   Val.ofList [.int 1, .int 0, .int 99],
   Val.ofList [.int 0],
   .sym "ORIG-POOL",
   .sym "ORIG-OPS",
   .sym "ORIG-CTRL"]

def runTooth (a : Arm) (fuel : Nat := 10) : Val :=
  match runArm toothWorld toothKind a false toothArgs fuel with
  | .ok v => v
  | .error _ => Val.nil
/-- `(:let N -5) (:charge :bytes (- 10 N) :steps 2)`: a negative operand under `-`. -/
def mutantArmNegOperand : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":LET", .sym "N", .int (-5)],
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", Val.ofList [.sym "-", .int 10, .sym "N"],
        .sym ":STEPS", .int 2]
    ] }

/-- `(:charge :bytes row-off :steps 2)`: a charge read from the row, which no static bound covers. -/
def mutantArmRowCharge : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":CHARGE", .sym ":BYTES", .sym "ROW-OFF", .sym ":STEPS", .int 2]
    ] }

/-! ### 3.1 The charge bound (`Cost.runArm_charge_le_cost`) -/

/-- Positive witness: `toothArmStep`'s derived bound is `(64, 2, 0)` and its run charges exactly
that, so the bound is attained. -/
theorem runArm_charge_le_cost_pos :
    Cost.derivedCost toothWorld toothKind toothArmStep = some (64, 2, 0) ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      Cost.extractCharge v = (64, 2, 0) :=
  ⟨by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- Tooth: the conclusion is falsifiable. `mutantArmCost` (a hand-mutated `:charge` of 999 bytes)
runs and violates the bound derived for `toothArmStep`; the derivation follows the mutation. -/
theorem mutant_charge_exceeds_cost_neg :
    Cost.derivedCost toothWorld toothKind mutantArmCost = some (999, 2, 0) ∧
    ∃ v, runArm toothWorld toothKind mutantArmCost false toothArgs 10 = .ok v ∧
      ¬ Cost.CostLe (Cost.extractCharge v) (64, 2, 0) :=
  ⟨by decide +kernel, runTooth mutantArmCost, by decide +kernel⟩

/-- Tooth for the interval: `(- 10 N)` with `N = -5` charges 15 bytes. An upper-only bound that
reads `(- x y)` as at most `x` (the bound this file used before `Fn2.Arms.Bound`) gives 10, which
the run exceeds; the interval gives exactly 15. -/
theorem negative_operand_charge :
    Cost.derivedCost toothWorld toothKind mutantArmNegOperand = some (15, 2, 0) ∧
    ∃ v, runArm toothWorld toothKind mutantArmNegOperand false toothArgs 10 = .ok v ∧
      Cost.extractCharge v = (15, 2, 0) ∧ ¬ Cost.CostLe (Cost.extractCharge v) (10, 2, 0) :=
  ⟨by decide +kernel, runTooth mutantArmNegOperand, by decide +kernel⟩

/-- Hypothesis-removal witness: a charge read from the row has no derived bound (`none`), and
its run charges the row's 99 bytes, above the 64 derived for `toothArmStep`; without
`derivedCost = some C` the theorem would have to bound this run, and it cannot. -/
theorem row_charge_unbounded :
    Cost.derivedCost toothWorld toothKind mutantArmRowCharge = none ∧
    ∃ v, runArm toothWorld toothKind mutantArmRowCharge false toothArgs 10 = .ok v ∧
      Cost.extractCharge v = (99, 2, 0) :=
  ⟨by decide +kernel, runTooth mutantArmRowCharge, by decide +kernel⟩

/-! ### 3.2 The frame (`Frame.runArm_frame`) -/

/-- Positive witness: the tooth kind names each child once; `toothArmStep`'s derived children
leave out `FN2-POOL` and `FN2-OPS`, and its run returns both as they were passed in. -/
theorem runArm_frame_pos :
    toothKind.tuple.Nodup ∧
    (Frame.derivedTables toothWorld toothKind toothArmStep).map
      (fun D => (D.contains "FN2-POOL", D.contains "FN2-OPS")) = some (false, false) ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      v.toList.getD 6 Val.nil = .sym "ORIG-POOL" ∧ v.toList.getD 7 Val.nil = .sym "ORIG-OPS" :=
  ⟨by decide, by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- Tooth: `mutantArmTables` calls an operation that writes `FN2-POOL`; its derived children
include `FN2-POOL`, and its run returns a different pool, violating the frame derived for
`toothArmStep`. -/
theorem mutant_frame_touched_neg :
    (Frame.derivedTables toothWorld toothKind mutantArmTables).map (·.contains "FN2-POOL") =
      some true ∧
    ∃ v, runArm toothWorld toothKind mutantArmTables false toothArgs 10 = .ok v ∧
      v.toList.getD 6 Val.nil ≠ .sym "ORIG-POOL" :=
  ⟨by decide +kernel, runTooth mutantArmTables, by decide +kernel⟩

/-! ### 3.3 Writes and next phase: checked on concrete runs (no general theorem yet) -/

/-- `derivedWrites` of `toothArmStep` is `["OFF"]`, and its run leaves the unwritten `STOPPED`
column as it was. -/
theorem derivedWrites_witness :
    derivedWrites toothWorld toothKind toothArmStep = ["OFF"] ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      Native.nth (.int 1) (v.toList.getD 4 Val.nil) = .int 0 :=
  ⟨by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- `mutantArmWrites` writes `STOPPED`; its derived writes say so and its run changes it. -/
theorem derivedWrites_mutant :
    "STOPPED" ∈ derivedWrites toothWorld toothKind mutantArmWrites ∧
    ∃ v, runArm toothWorld toothKind mutantArmWrites false toothArgs 10 = .ok v ∧
      Native.nth (.int 1) (v.toList.getD 4 Val.nil) ≠ .int 0 :=
  ⟨by decide +kernel, runTooth mutantArmWrites, by decide +kernel⟩

/-- `derivedNext` of `toothArmStep` is `[":REPLY"]` and its run leaves the row in phase 2. -/
theorem derivedNext_witness :
    derivedNext toothWorld toothKind toothArmStep = [":REPLY"] ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      Native.nth (.int 0) (v.toList.getD 4 Val.nil) = .int 2 :=
  ⟨by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- `mutantArmNext` moves to `:CLOSING` (3); its derived phases say so and its run does. -/
theorem derivedNext_mutant :
    ":CLOSING" ∈ derivedNext toothWorld toothKind mutantArmNext ∧
    ":CLOSING" ∉ derivedNext toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind mutantArmNext false toothArgs 10 = .ok v ∧
      Native.nth (.int 0) (v.toList.getD 4 Val.nil) = .int 3 :=
  ⟨by decide +kernel, by decide +kernel, runTooth mutantArmNext, by decide +kernel⟩

/-! ### 3.4 Agreement across the exported child-form kinds (`LayerAKinds`) -/

/-- A child-form kind names each child once, every arm, handler and sub-arm has a derived frame,
and every child an arm can write is among the children its narrowed signature returns. -/
def checkKindContracts (w : World) (k : Kind) : Bool :=
  !k.childForm ||
  (decide k.tuple.Nodup &&
   (k.subarms ++ k.arms ++ k.observes).all fun a =>
    match Frame.derivedTables w k a with
    | some D => (k.tuple.filter (D.contains ·)).all ((returns k a).contains ·)
    | none => false)

theorem layerA_childForm_contracts_agree :
    (Fn2.Instances.LayerAKinds.kinds.all
      (checkKindContracts Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

end Fn2.Arms.Derive
