import Fn2.Arms
import Fn2.ArmsLemmas
import Fn2.Pathway
import Fn2.Instances.LayerAKinds

/-!
# Fn2.Arms.Derive: Syntax-Driven Contract Derivation & Universal `Step` Composition Theorems

MACHINE-FORM §6.3 and LEAN-METATHEORY Brick F7:
1. Direct syntactic derivation of `derivedCost`, `derivedWrites`, `derivedNext`, `derivedHolds`,
   `derivedTables`, and `derivedFuel` from `Step` / `Arm` declarations by structural recursion
   on `Step` and `List Step`.
2. Contract agreement verification against the exported child-form kinds in
   `Fn2.Instances.LayerAKinds`.
3. Universal composition theorems proved by structural induction on `Step` / `List Step` and
   operational lemmas on `Fn2.Arms.put`, `flush`, `bindOuts`, `chargeResult`, `run`, and `runArm`
   (parametric in per-operation leaf hypotheses):
   * `runArm_charge_le_cost`: a successful `runArm` charges at most `derivedCost`.
   * `runArm_writes_sub`: any row mutation in `runArm` is within `derivedWrites` (plus `"PHASE"`).
   * `runArm_next_mem`: the resulting phase is in `derivedNext`.
   * `runArm_frame_untouched`: tables outside `derivedTables` are unchanged.
   * `runArm_terminates_within`: explicit fuel bound from step structure and `:repeat` bounds suffices.
4. Positive witnesses and mutant-declaration negative teeth for all five theorems.
-/

namespace Fn2.Arms.Derive
open Fn2.ACL2 Fn2.Arms Fn2.Pathway

/-! ## 1. Cost Algebra & Static Expression Bounds (`MACHINE-FORM §6.3`) -/

/-- A 3-dimensional resource cost `(bytes, steps, descriptors)`. -/
abbrev Cost := Int × Int × Int

def costZero : Cost := (0, 0, 0)

def costAdd (a b : Cost) : Cost :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def costMax (a b : Cost) : Cost :=
  (max a.1 b.1, max a.2.1 b.2.1, max a.2.2 b.2.2)

def costScale (k : Int) (c : Cost) : Cost :=
  (k * c.1, k * c.2.1, k * c.2.2)

/-- Componentwise ordering on 3-dimensional costs. -/
def CostLe (a b : Cost) : Prop :=
  a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

instance : DecidableRel CostLe := fun a b =>
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2))

@[simp] theorem costLe_refl (a : Cost) : CostLe a a :=
  ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _⟩

theorem costLe_trans {a b c : Cost} (h1 : CostLe a b) (h2 : CostLe b c) : CostLe a c :=
  ⟨Int.le_trans h1.1 h2.1, Int.le_trans h1.2.1 h2.2.1, Int.le_trans h1.2.2 h2.2.2⟩

theorem costLe_max_left (a b : Cost) : CostLe a (costMax a b) := by
  refine ⟨?_, ?_, ?_⟩ <;> (dsimp [costMax]; omega)

theorem costLe_max_right (a b : Cost) : CostLe b (costMax a b) := by
  refine ⟨?_, ?_, ?_⟩ <;> (dsimp [costMax]; omega)

theorem costLe_add {a₁ a₂ b₁ b₂ : Cost} (h1 : CostLe a₁ b₁) (h2 : CostLe a₂ b₂) :
    CostLe (costAdd a₁ a₂) (costAdd b₁ b₂) :=
  ⟨by have := h1.1; have := h2.1; dsimp [costAdd]; omega,
   by have := h1.2.1; have := h2.2.1; dsimp [costAdd]; omega,
   by have := h1.2.2; have := h2.2.2; dsimp [costAdd]; omega⟩

theorem costLe_scale {k₁ k₂ : Int} {c : Cost} (hk : k₁ ≤ k₂)
    (hc : 0 ≤ c.1 ∧ 0 ≤ c.2.1 ∧ 0 ≤ c.2.2) :
    CostLe (costScale k₁ c) (costScale k₂ c) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [costScale]; exact Int.mul_le_mul_of_nonneg_right hk hc.1
  · dsimp [costScale]; exact Int.mul_le_mul_of_nonneg_right hk hc.2.1
  · dsimp [costScale]; exact Int.mul_le_mul_of_nonneg_right hk hc.2.2

/-- Extract the `(bytes, steps, descriptors)` triple from a run arm's return value `v`. -/
def extractCharge (v : Val) : Cost :=
  let xs := v.toList
  ((xs.getD 0 Val.nil).toInt, (xs.getD 1 Val.nil).toInt, (xs.getD 2 Val.nil).toInt)

/-- Look up an integer constant in `w.consts`, falling back to `dflt`. -/
def constInt (w : World) (name : String) (dflt : Int := 0) : Int :=
  match w.consts.find? (·.1 == name) with
  | some (_, .int k) => k
  | _ => dflt

/-- Static upper bound of a step-language expression (`fn2-arms-bound` in `machine-arms.lisp`). -/
def boundExprF (w : World) (env : List (String × Int))
    (rec : Expr → Option Int) : Expr → Option Int
  | .int k => some (max 0 k)
  | .sym s =>
    match env.find? (·.1 == s) with
    | some (_, b) => some b
    | none =>
      match w.consts.find? (·.1 == s) with
      | some (_, .int k) => some (max 0 k)
      | _ => none
  | e =>
    match e.toList with
    | [.sym "QUOTE", .int k] => some (max 0 k)
    | [.sym "NFIX", x] => rec x
    | [.sym "-", x, _] => rec x
    | [.sym "1+", x] => (· + 1) <$> rec x
    | [.sym "1-", x] => rec x
    | [.sym "IF", _, a, b] => max <$> rec a <*> rec b
    | [.sym "MAX", a, b] => max <$> rec a <*> rec b
    | [.sym "MIN", a, b] =>
      match rec a, rec b with
      | some ba, some bb => some (min ba bb)
      | some ba, none => some ba
      | none, some bb => some bb
      | none, none => none
    | [.sym "*", a, b] => (· * ·) <$> rec a <*> rec b
    | .sym "+" :: args =>
      args.foldlM (fun acc a => (acc + ·) <$> rec a) 0
    | _ => none

def boundExpr (w : World) (env : List (String × Int)) : Expr → Option Int :=
  fixN 64 (boundExprF w env) (fun _ => none)

def boundOpt (w : World) (env : List (String × Int)) (e : Option Expr) (dflt : Int) : Int :=
  match e with
  | some x => (boundExpr w env x).getD dflt
  | none => dflt

def opBound (w : World) (name : String) : Cost :=
  match w.ops.find? (·.name == name) with
  | some { bound := some b, .. } => b
  | _ => costZero

/-- The static per-pass bound of a `:repeat` body: 1 step plus the sum of declared call bounds. -/
def repeatPassBound (w : World) (body : List Step) : Cost :=
  (body.flatMap Step.calls).foldl (fun acc op => costAdd acc (opBound w op)) (0, 1, 0)

/-! ## 2. Syntax-Driven Derivation on `Step`, `List Step`, and `Arm` -/

/-- Stobj tables written by a declared operation. -/
def opTables (w : World) (name : String) : List String :=
  match w.ops.find? (·.name == name) with
  | some o => o.stobjsOut.filterMap id
  | none => []

/-- Stobj tables written by a `:park` terminal. -/
def parkTables (w : World) (k : Kind) (wait : String) (parkKind : Option String) : List String :=
  match wait with
  | "OPERATION" => opTables w "FN2-MACHINE-PARK"
  | "ADMISSION" => opTables w "FN2-MACHINE-PARK-ADMISSION"
  | "TAKEN" => opTables w ("FN2-MACHINE-PARK-TAKEN-" ++ parkKind.getD "")
  | "POOL" => [k.name, "FN2-MACHINES", "FN2-CONTROL"]
  | other =>
    match w.waits.find? (·.kind == other) with
    | some ⟨_, some parker⟩ => opTables w parker
    | some ⟨_, none⟩ => [k.name, "FN2-MACHINES", "FN2-CONTROL"]
    | none => []

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

/-! ### 2.1 `stepTables` / `stepsTables` (by structural recursion on `Step` / `List Step`) -/

mutual
def stepTables (w : World) (k : Kind) (refT : List String) (subT : String → List String) :
    Step → List String
  | .let_ _ _ => []
  | .set pairs => if pairs.isEmpty then [] else [k.name, "FN2-MACHINES", "FN2-CONTROL"]
  | .next _ => [k.name, "FN2-MACHINES", "FN2-CONTROL"]
  | .do_ _ c _ _ _ _ cases =>
    let opT := opTables w c.op
    let ansT := match (w.ops.find? (·.name == c.op)).map (·.answers) with
      | some .none => []
      | _ => if refT.isEmpty then ["FN2-CONTROL"] else refT
    opT ++ ansT ++ casesTables w k refT subT cases
  | .issue c ok refused =>
    opTables w c.op ++ stepsTables w k refT subT ok ++ stepsTables w k refT subT refused ++
      opTables w "FN2-MACHINE-PARK" ++ [k.name, "FN2-MACHINES", "FN2-CONTROL"] ++ refT
  | .repeat_ _ body _ => stepsTables w k refT subT body
  | .repeatNext => []
  | .wakeRow _ => ["FN2-MACHINES", "FN2-CONTROL"]
  | .if_ _ a b => stepsTables w k refT subT a ++ stepsTables w k refT subT b
  | .cond clauses => clausesTables w k refT subT clauses
  | .case_ _ arms => casesTables w k refT subT arms
  | .charge _ _ _ _ | .idle | .yield | .wake | .nowake => []
  | .wait _ _ | .halt => [k.name, "FN2-MACHINES", "FN2-CONTROL"]
  | .park wait _ pk _ _ => parkTables w k wait pk
  | .stop _ _ => ["FN2-CONTROL"]
  | .goto name => subT name

def stepsTables (w : World) (k : Kind) (refT : List String) (subT : String → List String) :
    List Step → List String
  | [] => []
  | s :: ss => stepTables w k refT subT s ++ stepsTables w k refT subT ss

def casesTables (w : World) (k : Kind) (refT : List String) (subT : String → List String) :
    List (Option (List Val) × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsTables w k refT subT ss ++ casesTables w k refT subT cs

def clausesTables (w : World) (k : Kind) (refT : List String) (subT : String → List String) :
    List (Expr × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsTables w k refT subT ss ++ clausesTables w k refT subT cs
end

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

/-! ### 2.5 `stepCost` / `stepsCost` (by structural recursion on `Step` / `List Step`) -/

mutual
def stepCost (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int)) : Step → Cost
  | .let_ _ _ | .set _ | .next _ | .wakeRow _ | .repeatNext | .wake | .nowake => costZero
  | .repeat_ n body _ =>
    let nb := max 0 ((boundExpr w env n).getD 0)
    let per := repeatPassBound w body
    costScale nb per
  | .do_ _ c _ _ _ _ cases =>
    costMax (opBound w c.op) (costMax (casesCost w observe refC subC env cases) (refC env))
  | .issue c ok refused =>
    let mailboxWork := constInt w "*FN2-WORK-MAILBOX*" 2
    let cOk := stepsCost w observe refC subC env ok
    let cRef := stepsCost w observe refC subC env refused
    let cPark : Cost := (0, mailboxWork, 0)
    costMax (opBound w c.op)
      (costMax cOk (costMax (costAdd cRef cPark) (costAdd cRef (costMax cPark (refC env)))))
  | .if_ _ a b =>
    costMax (stepsCost w observe refC subC env a) (stepsCost w observe refC subC env b)
  | .cond clauses => clausesCost w observe refC subC env clauses
  | .case_ _ arms => casesCost w observe refC subC env arms
  | .charge b s d _ =>
    (boundOpt w env b 0, boundOpt w env s 0, boundOpt w env d 0)
  | .idle | .yield => (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)
  | .wait b s =>
    (boundOpt w env b 0, boundOpt w env s (constInt w "*FN2-WORK-MAILBOX*" 2), 1)
  | .halt => (0, constInt w "*FN2-WORK-MAILBOX*" 2, 0)
  | .park _ _ _ s _ =>
    (0, boundOpt w env s (constInt w "*FN2-WORK-MAILBOX*" 2), 0)
  | .stop _ s =>
    if observe then costZero else (0, boundOpt w env s (constInt w "*FN2-WORK-EMPTY*" 1), 0)
  | .goto name => subC env name

def stepsCost (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int)) : List Step → Cost
  | [] => costZero
  | s :: rest =>
    let env' := match s with
      | .let_ v e =>
        match boundExpr w env e with
        | some b => (v, b) :: env
        | none => env
      | _ => env
    let cStep := stepCost w observe refC subC env s
    let cRest := stepsCost w observe refC subC env' rest
    match s with
    | .repeat_ _ _ _ => costAdd cStep cRest
    | _ => costMax cStep cRest

def casesCost (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int)) : List (Option (List Val) × List Step) → Cost
  | [] => costZero
  | (_, ss) :: cs =>
    costMax (stepsCost w observe refC subC env ss) (casesCost w observe refC subC env cs)

def clausesCost (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int)) : List (Expr × List Step) → Cost
  | [] => costZero
  | (_, ss) :: cs =>
    costMax (stepsCost w observe refC subC env ss) (clausesCost w observe refC subC env cs)
end

/-! ### 2.6 `stepFuel` / `stepsFuel` (by structural recursion on `Step` / `List Step`) -/

mutual
def stepFuel (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) : Step → Nat
  | .let_ _ _ | .set _ | .next _ | .wakeRow _ | .repeatNext
  | .charge _ _ _ _ | .idle | .yield | .wait _ _ | .halt | .park _ _ _ _ _
  | .stop _ _ | .wake | .nowake => 1
  | .repeat_ n body _ =>
    let nb := ((boundExpr w env n).getD 0).toNat
    1 + nb + 1 + stepsFuel w refF subF [] body + 1
  | .do_ _ _ _ _ _ _ cases =>
    1 + max (casesFuel w refF subF env cases) (refF env)
  | .issue _ ok refused =>
    let fOk := stepsFuel w refF subF env ok
    let fRef := stepsFuel w refF subF env refused
    1 + max fOk (fRef + 1 + refF env)
  | .if_ _ a b =>
    1 + max (stepsFuel w refF subF env a) (stepsFuel w refF subF env b)
  | .cond clauses => 1 + clausesFuel w refF subF env clauses
  | .case_ _ arms => 1 + casesFuel w refF subF env arms
  | .goto name => 1 + subF env name

def stepsFuel (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) : List Step → Nat
  | [] => 1
  | s :: rest =>
    let env' := match s with
      | .let_ v e =>
        match boundExpr w env e with
        | some b => (v, b) :: env
        | none => env
      | _ => env
    stepFuel w refF subF env s + stepsFuel w refF subF env' rest

def casesFuel (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) : List (Option (List Val) × List Step) → Nat
  | [] => 1
  | (_, ss) :: cs =>
    max (stepsFuel w refF subF env ss) (casesFuel w refF subF env cs)

def clausesFuel (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) : List (Expr × List Step) → Nat
  | [] => 1
  | (_, ss) :: cs =>
    max (stepsFuel w refF subF env ss) (clausesFuel w refF subF env cs)
end

/-! ### 2.7 Top-Level `Arm` Contract Functions -/

def subTables (w : World) (k : Kind) : Nat → String → List String
  | 0, _ => []
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refT := stepsTables w k [] (subTables w k d) decl.onRefusal
        stepsTables w k refT (subTables w k d) decl.steps
      | .error _ => []
    | none => []

/-- `derivedTables w k a`: the subset of `k.tuple` (in tuple order) that `a` can mutate. -/
def derivedTables (w : World) (k : Kind) (a : Arm) : List String :=
  match a.read with
  | .ok decl =>
    let subT := subTables w k (k.subarms.length + 1)
    let refT := stepsTables w k [] subT decl.onRefusal
    let raw := stepsTables w k refT subT decl.steps
    k.tuple.filter (raw.contains ·)
  | .error _ => []

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

def subCost (w : World) (k : Kind) (observe : Bool) :
    Nat → List (String × Int) → String → Cost
  | 0, _, _ => costZero
  | d + 1, env, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refC := fun e =>
          if decl.onRefusal.isEmpty then
            if observe then costZero else (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)
          else stepsCost w observe (fun _ => costZero) (subCost w k observe d) e decl.onRefusal
        stepsCost w observe refC (subCost w k observe d) env decl.steps
      | .error _ => costZero
    | none => costZero

/-- `derivedCost w k a observe`: static upper bound `(bytes, steps, descriptors)` of `a`. -/
def derivedCost (w : World) (k : Kind) (a : Arm) (observe : Bool := false) : Cost :=
  match a.read with
  | .ok decl =>
    let subC := subCost w k observe (k.subarms.length + 1)
    let refC := fun e =>
      if decl.onRefusal.isEmpty then
        if observe then costZero else (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)
      else stepsCost w observe (fun _ => costZero) subC e decl.onRefusal
    stepsCost w observe refC subC [] decl.steps
  | .error _ => costZero

def subFuel (w : World) (k : Kind) : Nat → List (String × Int) → String → Nat
  | 0, _, _ => 1
  | d + 1, env, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub =>
      match sub.read with
      | .ok decl =>
        let refF := fun e =>
          if decl.onRefusal.isEmpty then 1
          else stepsFuel w (fun _ => 1) (subFuel w k d) e decl.onRefusal
        stepsFuel w refF (subFuel w k d) env decl.steps
      | .error _ => 1
    | none => 1

/-- `derivedFuel w k a`: explicit interpreter fuel bound synthesized from `a`'s step structure. -/
def derivedFuel (w : World) (k : Kind) (a : Arm) : Nat :=
  match a.read with
  | .ok decl =>
    let subF := subFuel w k (k.subarms.length + 1)
    let refF := fun e =>
      if decl.onRefusal.isEmpty then 1
      else stepsFuel w (fun _ => 1) subF e decl.onRefusal
    stepsFuel w refF subF [] decl.steps
  | .error _ => 1

/-! ## 3. Universal `Step` / `List Step` Structural Induction Lemmas -/

theorem stepsTables_append (w : World) (k : Kind) (refT : List String)
    (subT : String → List String) (xs ys : List Step) :
    stepsTables w k refT subT (xs ++ ys) =
      stepsTables w k refT subT xs ++ stepsTables w k refT subT ys := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp [stepsTables, ih, List.append_assoc]

theorem stepsWrites_append (w : World) (refW : List String)
    (subW : String → List String) (xs ys : List Step) :
    stepsWrites w refW subW (xs ++ ys) =
      stepsWrites w refW subW xs ++ stepsWrites w refW subW ys := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp [stepsWrites, ih, List.append_assoc]

theorem stepsHolds_append (refH : List String)
    (subH : String → List String) (xs ys : List Step) :
    stepsHolds refH subH (xs ++ ys) =
      stepsHolds refH subH xs ++ stepsHolds refH subH ys := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp [stepsHolds, ih, List.append_assoc]

theorem casesTables_mem (w : World) (k : Kind) (refT : List String)
    (subT : String → List String)
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) {t : String} (ht : t ∈ stepsTables w k refT subT ss) :
    t ∈ casesTables w k refT subT cs := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesTables, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl ht
    · exact Or.inr (ih htl)

theorem clausesTables_mem (w : World) (k : Kind) (refT : List String)
    (subT : String → List String)
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) {t : String} (ht : t ∈ stepsTables w k refT subT ss) :
    t ∈ clausesTables w k refT subT cl := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesTables, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl ht
    · exact Or.inr (ih htl)

theorem casesWrites_mem (w : World) (refW : List String)
    (subW : String → List String)
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) {f : String} (hf : f ∈ stepsWrites w refW subW ss) :
    f ∈ casesWrites w refW subW cs := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesWrites, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl hf
    · exact Or.inr (ih htl)

theorem clausesWrites_mem (w : World) (refW : List String)
    (subW : String → List String)
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) {f : String} (hf : f ∈ stepsWrites w refW subW ss) :
    f ∈ clausesWrites w refW subW cl := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesWrites, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl hf
    · exact Or.inr (ih htl)

theorem casesHolds_mem (refH : List String)
    (subH : String → List String)
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) {h : String} (hh : h ∈ stepsHolds refH subH ss) :
    h ∈ casesHolds refH subH cs := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesHolds, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl hh
    · exact Or.inr (ih htl)

theorem clausesHolds_mem (refH : List String)
    (subH : String → List String)
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) {h : String} (hh : h ∈ stepsHolds refH subH ss) :
    h ∈ clausesHolds refH subH cl := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesHolds, List.mem_append]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Or.inl hh
    · exact Or.inr (ih htl)

theorem casesNext_mem (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool)
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) :
    (∀ p ∈ (stepsNext k refN subN hasNext ss).1, p ∈ (casesNext k refN subN hasNext cs).1) ∧
    ((stepsNext k refN subN hasNext ss).2 = true → (casesNext k refN subN hasNext cs).2 = true) := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesNext, joinNext, List.mem_append, Bool.or_eq_true]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact ⟨fun _ hp => Or.inl hp, fun h => Or.inl h⟩
    · obtain ⟨ih1, ih2⟩ := ih htl
      exact ⟨fun p hp => Or.inr (ih1 p hp), fun h => Or.inr (ih2 h)⟩

theorem clausesNext_mem (k : Kind) (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool) (hasNext : Bool)
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) :
    (∀ p ∈ (stepsNext k refN subN hasNext ss).1, p ∈ (clausesNext k refN subN hasNext cl).1) ∧
    ((stepsNext k refN subN hasNext ss).2 = true → (clausesNext k refN subN hasNext cl).2 = true) := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesNext, joinNext, List.mem_append, Bool.or_eq_true]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact ⟨fun _ hp => Or.inl hp, fun h => Or.inl h⟩
    · obtain ⟨ih1, ih2⟩ := ih htl
      exact ⟨fun p hp => Or.inr (ih1 p hp), fun h => Or.inr (ih2 h)⟩

theorem casesCost_mem (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int))
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) :
    CostLe (stepsCost w observe refC subC env ss) (casesCost w observe refC subC env cs) := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesCost]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact costLe_max_left _ _
    · exact costLe_trans (ih htl) (costLe_max_right _ _)

theorem clausesCost_mem (w : World) (observe : Bool)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (env : List (String × Int))
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) :
    CostLe (stepsCost w observe refC subC env ss) (clausesCost w observe refC subC env cl) := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesCost]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact costLe_max_left _ _
    · exact costLe_trans (ih htl) (costLe_max_right _ _)

theorem casesFuel_mem (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int))
    {cs : List (Option (List Val) × List Step)} {opt : Option (List Val)} {ss : List Step}
    (hm : (opt, ss) ∈ cs) :
    stepsFuel w refF subF env ss ≤ casesFuel w refF subF env cs := by
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨o, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [casesFuel]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem clausesFuel_mem (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int))
    {cl : List (Expr × List Step)} {e : Expr} {ss : List Step}
    (hm : (e, ss) ∈ cl) :
    stepsFuel w refF subF env ss ≤ clausesFuel w refF subF env cl := by
  induction cl with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨c, s⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    simp only [clausesFuel]
    rcases hm with ⟨rfl, rfl⟩ | htl
    · exact Nat.le_trans (Nat.le_refl _) (Nat.le_max_left _ _)
    · exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem stepFuel_pos (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) (s : Step) :
    0 < stepFuel w refF subF env s := by
  cases s <;> simp [stepFuel] <;> omega

theorem stepsFuel_pos (w : World)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (env : List (String × Int)) (ss : List Step) :
    0 < stepsFuel w refF subF env ss := by
  cases ss with
  | nil => simp [stepsFuel]
  | cons s rest =>
    have := stepFuel_pos w refF subF env s
    simp only [stepsFuel]
    omega

/-! ## 4. Operational Helper Lemmas on `pend`, `bindOuts`, `put`, `flush`, and Terminals -/

theorem except_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem pend_ok_eq {st st' : St} {pairs : List (String × Expr)}
    (h : pend st pairs = .ok st') :
    st' = { st with pending := st.pending ++ pairs } := by
  unfold pend at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; exact h.symm

local macro "except_step " h:ident : tactic =>
  `(tactic| ((try simp only [bind, Except.bind] at ($h)); split at ($h); · exact absurd $h (by simp)))

theorem bindOuts_go_props (st st' : St) (outs : List (Option String))
    (vars : List String) (rs : List Val)
    (h : bindOuts.go st outs vars rs = .ok st') :
    st'.pending = st.pending ∧ st'.next = st.next ∧
    st'.nextDone = st.nextDone ∧ st'.loopWork = st.loopWork ∧
    ∀ c, c ∉ outs.filterMap id → stobj st' c = stobj st c := by
  induction outs generalizing st vars rs with
  | nil =>
    cases rs <;> simp [bindOuts.go] at h <;> subst h <;>
      exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons o os ih =>
    cases o with
    | some s =>
      cases rs with
      | nil => simp [bindOuts.go] at h
      | cons r rs' =>
        simp only [bindOuts.go] at h
        obtain ⟨hp, hn, hnd, hlw, hst⟩ := ih (setStobj st s r) vars rs' h
        refine ⟨hp, hn, hnd, hlw, fun c hc => ?_⟩
        have hc1 : c ≠ s := fun heq => hc (by simp [List.filterMap, heq])
        have hc2 : c ∉ os.filterMap id := fun hm => hc (by simp [List.filterMap, hm])
        rw [hst c hc2, stobj_setStobj_ne st s c r (Ne.symm hc1)]
    | none =>
      cases vars with
      | nil =>
        cases rs with
        | nil => simp [bindOuts.go] at h
        | cons r rs' =>
          simp only [bindOuts.go] at h
          obtain ⟨hp, hn, hnd, hlw, hst⟩ := ih st [] rs' h
          refine ⟨hp, hn, hnd, hlw, fun c hc => hst c (by simpa [List.filterMap] using hc)⟩
      | cons v vs' =>
        cases rs with
        | nil => simp [bindOuts.go] at h
        | cons r rs' =>
          simp only [bindOuts.go] at h
          obtain ⟨hp, hn, hnd, hlw, hst⟩ := ih { st with vars := (v, r) :: st.vars } vs' rs' h
          refine ⟨hp, hn, hnd, hlw, fun c hc => hst c (by simpa [List.filterMap] using hc)⟩

theorem bindOuts_props (st st' : St) (outs : List (Option String))
    (vars : List String) (res : Val)
    (h : bindOuts st outs vars res = .ok st') :
    st'.pending = st.pending ∧ st'.next = st.next ∧
    st'.nextDone = st.nextDone ∧ st'.loopWork = st.loopWork ∧
    ∀ c, c ∉ outs.filterMap id → stobj st' c = stobj st c := by
  unfold bindOuts at h
  split at h
  · rename_i s
    simp only [Except.ok.injEq] at h; subst h
    refine ⟨rfl, rfl, rfl, rfl, fun c hc => ?_⟩
    have hc1 : c ≠ s := fun heq => hc (by simp [List.filterMap, heq])
    exact stobj_setStobj_ne st s c res (Ne.symm hc1)
  · split at h <;>
      (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  · exact bindOuts_go_props st st' outs vars res.toList h

theorem put_loopWork (w : World) (f : Frame) (st st' : St) (pairs : List (String × Val))
    (h : put w f st pairs = .ok st') :
    st'.loopWork = st.loopWork := by
  unfold put at h
  except_step h; except_step h; except_step h; except_step h; except_step h; except_step h
  except_step h
  split at h
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

theorem flush_props (w : World) (f : Frame) (st st' : St)
    (h : flush w f st = .ok st') :
    st'.pending = [] ∧ st'.next = none ∧
    (st.pending = [] ∧ st.next = none → ∀ c, stobj st' c = stobj st c) ∧
    (∀ c, c ≠ f.kind.name → c ≠ "FN2-MACHINES" → c ≠ "FN2-CONTROL" →
      stobj st' c = stobj st c) := by
  have hfr := fun c h1 h2 h3 => (flush_frame w f st st' h c h1 h2 h3).1
  refine ⟨?_, ?_, ?_, hfr⟩
  · unfold flush at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' (split at h <;> try (simp only [reduceCtorEq] at h; done))
    all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
  · unfold flush at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' (split at h <;> try (simp only [reduceCtorEq] at h; done))
    all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)
  · rintro ⟨hpend, hnext⟩ c
    unfold flush at h
    simp only [hpend, hnext, List.mapM_nil, List.isEmpty_nil, if_true,
      bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl

theorem foldlM_col_preserve (w : World) (kname : String) (slot : Val)
    (readCol : Val → Val) (col : String)
    (hset : ∀ v t t' n, n ≠ col → callFn w (kname ++ "-SET-" ++ n) [slot, v, t] = .ok t' →
      readCol t' = readCol t)
    (ps : List (String × Val)) (hcol : ∀ p ∈ ps, p.1 ≠ col)
    (tbl tbl' : Val)
    (hf : ps.foldlM (fun t (n, v) => callFn w (kname ++ "-SET-" ++ n) [slot, v, t]) tbl = .ok tbl') :
    readCol tbl' = readCol tbl := by
  induction ps generalizing tbl with
  | nil => simp [List.foldlM, pure, Except.pure] at hf; subst hf; rfl
  | cons p ps ih =>
    obtain ⟨n, v⟩ := p
    simp only [List.foldlM_cons] at hf
    obtain ⟨t1, ht1, hrest⟩ := except_bind_ok hf
    have hn : n ≠ col := hcol (n, v) List.mem_cons_self
    have h1 := hset v tbl t1 n hn ht1
    have h2 := ih (fun q hq => hcol q (List.mem_cons_of_mem _ hq)) t1 hrest
    exact h2.trans h1

/-- `put` preserves any column `col` of `f.kind.name` not appearing in `pairs`. -/
theorem put_col_preserve (w : World) (f : Frame) (st st' : St) (pairs : List (String × Val))
    (readCol : Val → Val) (col : String)
    (hne1 : f.kind.name ≠ "FN2-MACHINES") (hne2 : f.kind.name ≠ "FN2-CONTROL")
    (hset : ∀ slot v t t' n, n ≠ col →
      callFn w (f.kind.name ++ "-SET-" ++ n) [slot, v, t] = .ok t' → readCol t' = readCol t)
    (hcol : ∀ p ∈ pairs, p.1 ≠ col)
    (tbl tbl' : Val) (ht : stobj st f.kind.name = .ok tbl)
    (hp : put w f st pairs = .ok st')
    (ht' : stobj st' f.kind.name = .ok tbl') :
    readCol tbl' = readCol tbl := by
  unfold put at hp
  except_step hp; rename_i slot hslot
  except_step hp; rename_i id hid
  except_step hp; rename_i table htable
  except_step hp; rename_i dir hdir
  except_step hp; rename_i ctrl hctrl
  except_step hp; rename_i rows hrows
  except_step hp; rename_i drows hdrows
  have htbl_eq : tbl = table := by
    rw [ht] at htable; exact Except.ok.inj htable
  subst htbl_eq
  split at hp
  · except_step hp; rename_i table' hfold_own
    except_step hp; rename_i dir' hfold_dir
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    rw [stobj_setStobj_ne _ _ _ _ hne1.symm,
        stobj_setStobj_same st f.kind.name table' tbl ht] at ht'
    simp only [Except.ok.injEq] at ht'
    subst ht'
    exact foldlM_col_preserve w f.kind.name slot readCol col (hset slot)
      (pairs.filter fun p => !directoryFields.contains p.1)
      (fun p hp_mem => hcol p (List.mem_filter.mp hp_mem).1) tbl table' hfold_own
  · except_step hp; except_step hp
    simp only [pure, Except.pure, Except.ok.injEq] at hp
    subst hp
    rw [stobj_setStobj_ne st "FN2-CONTROL" f.kind.name _ hne2.symm, ht] at ht'
    simp only [Except.ok.injEq] at ht'
    subst ht'; rfl

/-- `chargeResult` produces a 4-tuple prefix whose `.toInt` values are `b + lb`, `s + ls`, `d + ld`. -/
theorem chargeResult_extract (f : Frame) (st : St) (b s d r v : Val)
    (h : chargeResult f st b s d r = .ok (.done v)) :
    extractCharge v = costAdd (b.toInt, s.toInt, d.toInt) st.loopWork := by
  rcases st with ⟨stobjs, vars, pending, next, nextDone, woken, lb, ls, ld⟩
  unfold chargeResult at h
  obtain ⟨t, _, h⟩ := except_bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Res.done.injEq] at h
  subst h
  have hadd : ∀ (x : Val) (n : Int), (if n = 0 then x else Val.int (x.toInt + n)).toInt = x.toInt + n := by
    intro x n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, Val.toInt]
  simp [extractCharge, costAdd, Val.ofList, Val.toList, hadd]

/-! ## 5. Inductive Step-Execution Trace Semantics & Universal Composition Theorems -/

/-- An execution trace of a path through `List Step` in environment `env`,
    recording `hasNext` at entry, whether `.next` was executed, the resulting phase `endPhase`,
    the accumulated `loopWork` + terminal `charge`, the tables mutated `touched`,
    the non-phase columns written `written`, and the interpreter steps `fuelUsed`. -/
inductive StepsExec (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step) :
    List (String × Int) → Bool → List Step →
    Cost → List String → List String → Option String → Nat → Prop where
  | let_step {env hasNext v e rest c ts ws ph fu}
      (hrest : StepsExec w k observe refSteps subSteps
        (match boundExpr w env e with | some b => (v, b) :: env | none => env)
        hasNext rest c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.let_ v e :: rest)
        c ts ws ph (1 + fu)
  | set_step {env hasNext pairs rest c ts ws ph fu}
      (hrest : StepsExec w k observe refSteps subSteps env hasNext rest c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.set pairs :: rest)
        c ((if pairs.isEmpty then [] else [k.name, "FN2-MACHINES", "FN2-CONTROL"]) ++ ts)
        (pairs.map (·.1) ++ ws) ph (1 + fu)
  | next_step {env hasNext phExpr pChosen rest c ts ws ph fu}
      (hp : pChosen ∈ nextExprPhases k phExpr)
      (hrest : StepsExec w k observe refSteps subSteps env true rest c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.next phExpr :: rest)
        c ([k.name, "FN2-MACHINES", "FN2-CONTROL"] ++ ts) ws (some (ph.getD pChosen)) (1 + fu)
  | wakeRow_step {env hasNext e rest c ts ws ph fu}
      (hrest : StepsExec w k observe refSteps subSteps env hasNext rest c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.wakeRow e :: rest)
        c (["FN2-MACHINES", "FN2-CONTROL"] ++ ts) ws ph (1 + fu)
  | repeat_step {env hasNext n body until_ rest passes cBody cRest tsBody tsRest wsBody wsRest ph fuBody fuRest}
      (hpasses : 0 ≤ passes ∧ passes ≤ max 0 ((boundExpr w env n).getD 0))
      (hper : 0 ≤ (repeatPassBound w body).1 ∧
              0 ≤ (repeatPassBound w body).2.1 ∧
              0 ≤ (repeatPassBound w body).2.2)
      (hbody : StepsExec w k observe refSteps subSteps [] false body
        cBody tsBody wsBody none fuBody)
      (hrest : StepsExec w k observe refSteps subSteps env hasNext rest
        cRest tsRest wsRest ph fuRest) :
      StepsExec w k observe refSteps subSteps env hasNext (.repeat_ n body until_ :: rest)
        (costAdd (costScale passes (repeatPassBound w body)) cRest)
        (tsBody ++ tsRest) (wsBody ++ wsRest) ph
        (1 + passes.toNat + 1 + fuBody + 1 + fuRest)
  | if_true {env hasNext cond a b rest c ts ws ph fu}
      (ha : StepsExec w k observe refSteps subSteps env hasNext a c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.if_ cond a b :: rest)
        c ts ws ph (1 + fu)
  | if_false {env hasNext cond a b rest c ts ws ph fu}
      (hb : StepsExec w k observe refSteps subSteps env hasNext b c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.if_ cond a b :: rest)
        c ts ws ph (1 + fu)
  | cond_branch {env hasNext clauses e ss rest c ts ws ph fu}
      (hmem : (e, ss) ∈ clauses)
      (hss : StepsExec w k observe refSteps subSteps env hasNext ss c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.cond clauses :: rest)
        c ts ws ph (1 + fu)
  | case_branch {env hasNext key arms opt ss rest c ts ws ph fu}
      (hmem : (opt, ss) ∈ arms)
      (hss : StepsExec w k observe refSteps subSteps env hasNext ss c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.case_ key arms :: rest)
        c ts ws ph (1 + fu)
  | do_accept {env hasNext vars call ag acc wh el cases rest c ts ws ph fu}
      (hrest : StepsExec w k observe refSteps subSteps env hasNext rest c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext
        (.do_ vars call ag acc wh el cases :: rest)
        c (opTables w call.op ++ ts) ws ph (1 + fu)
  | do_case {env hasNext vars call ag acc wh el cases opt ss rest c ts ws ph fu}
      (hmem : (opt, ss) ∈ cases)
      (hss : StepsExec w k observe refSteps subSteps env hasNext ss c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext
        (.do_ vars call ag acc wh el cases :: rest)
        c (opTables w call.op ++ ts) ws ph (1 + fu)
  | issue_ok {env hasNext call ok refused rest c ts ws ph fu}
      (hok : StepsExec w k observe refSteps subSteps env hasNext ok c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext
        (.issue call ok refused :: rest)
        c (opTables w call.op ++ ts) ws ph (1 + fu)
  | charge_term {env hasNext b s d r rest c}
      (hc : CostLe c (boundOpt w env b 0, boundOpt w env s 0, boundOpt w env d 0)) :
      StepsExec w k observe refSteps subSteps env hasNext (.charge b s d r :: rest)
        c [] [] none 1
  | idle_term {env hasNext rest c}
      (hc : CostLe c (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)) :
      StepsExec w k observe refSteps subSteps env hasNext (.idle :: rest)
        c [] [] none 1
  | yield_term {env hasNext rest c}
      (hc : CostLe c (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)) :
      StepsExec w k observe refSteps subSteps env hasNext (.yield :: rest)
        c [] [] none 1
  | wait_term {env hasNext b s rest c}
      (hc : CostLe c (boundOpt w env b 0, boundOpt w env s (constInt w "*FN2-WORK-MAILBOX*" 2), 1)) :
      StepsExec w k observe refSteps subSteps env hasNext (.wait b s :: rest)
        c [k.name, "FN2-MACHINES", "FN2-CONTROL"] ["PENDING", "WAIT-REASON"] none 1
  | halt_term {env hasNext rest c}
      (hc : CostLe c (0, constInt w "*FN2-WORK-MAILBOX*" 2, 0)) :
      StepsExec w k observe refSteps subSteps env hasNext (.halt :: rest)
        c [k.name, "FN2-MACHINES", "FN2-CONTROL"] ["STOPPED", "WAIT-REASON"] none 1
  | park_term {env hasNext wait arg pk s keys rest c}
      (hc : CostLe c (0, boundOpt w env s (constInt w "*FN2-WORK-MAILBOX*" 2), 0)) :
      StepsExec w k observe refSteps subSteps env hasNext (.park wait arg pk s keys :: rest)
        c (parkTables w k wait pk) (parkWrites w wait) none 1
  | stop_term {env hasNext reason s rest c}
      (hc : CostLe c (if observe then costZero else (0, boundOpt w env s (constInt w "*FN2-WORK-EMPTY*" 1), 0))) :
      StepsExec w k observe refSteps subSteps env hasNext (.stop reason s :: rest)
        c ["FN2-CONTROL"] [] none 1
  | wake_term {env hasNext rest} :
      StepsExec w k observe refSteps subSteps env hasNext (.wake :: rest)
        costZero [] [] none 1
  | nowake_term {env hasNext rest} :
      StepsExec w k observe refSteps subSteps env hasNext (.nowake :: rest)
        costZero [] [] none 1
  | repeatNext_term {env hasNext rest} :
      StepsExec w k observe refSteps subSteps env hasNext (.repeatNext :: rest)
        costZero [] [] none 1
  | goto_term {env hasNext name rest c ts ws ph fu}
      (hsub : StepsExec w k observe refSteps subSteps env hasNext (subSteps name) c ts ws ph fu) :
      StepsExec w k observe refSteps subSteps env hasNext (.goto name :: rest)
        c ts ws ph (1 + fu)

/-! ### 5.1 Structural Induction Theorem 1: `stepsExec_charge_le_cost` & `runArm_charge_le_cost` -/

theorem stepsExec_charge_le_cost (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step)
    (refC : List (String × Int) → Cost)
    (subC : List (String × Int) → String → Cost)
    (hsubC : ∀ env name,
      CostLe (stepsCost w observe refC subC env (subSteps name)) (subC env name))
    {env : List (String × Int)} {hasNext : Bool} {steps : List Step}
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe refSteps subSteps env hasNext steps c ts ws ph fu) :
    CostLe c (stepsCost w observe refC subC env steps) := by
  induction hexec with
  | let_step _ ih =>
    simp only [stepsCost, stepCost]
    exact costLe_trans ih (costLe_max_right _ _)
  | set_step _ ih =>
    simp only [stepsCost, stepCost]
    exact costLe_trans ih (costLe_max_right _ _)
  | next_step _ _ ih =>
    simp only [stepsCost, stepCost]
    exact costLe_trans ih (costLe_max_right _ _)
  | wakeRow_step _ ih =>
    simp only [stepsCost, stepCost]
    exact costLe_trans ih (costLe_max_right _ _)
  | repeat_step hpasses hper _ _ _ ihRest =>
    simp only [stepsCost, stepCost]
    exact costLe_add (costLe_scale hpasses.2 hper) ihRest
  | if_true _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (costLe_max_left _ _)
  | if_false _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (costLe_max_right _ _)
  | cond_branch hmem _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (clausesCost_mem w observe refC subC _ hmem)
  | case_branch hmem _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (casesCost_mem w observe refC subC _ hmem)
  | do_accept _ ih =>
    simp only [stepsCost]
    exact costLe_trans ih (costLe_max_right _ _)
  | do_case hmem _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    refine costLe_trans ?_ (costLe_max_right _ _)
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (casesCost_mem w observe refC subC _ hmem)
  | issue_ok _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    refine costLe_trans ?_ (costLe_max_right _ _)
    exact costLe_trans ih (costLe_max_left _ _)
  | charge_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | idle_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | yield_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | wait_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | halt_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | park_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | stop_term hc =>
    simp only [stepsCost, stepCost]
    exact costLe_trans hc (costLe_max_left _ _)
  | wake_term =>
    simp only [stepsCost, stepCost]
    exact costLe_max_left _ _
  | nowake_term =>
    simp only [stepsCost, stepCost]
    exact costLe_max_left _ _
  | repeatNext_term =>
    simp only [stepsCost, stepCost]
    exact costLe_max_left _ _
  | goto_term _ ih =>
    simp only [stepsCost, stepCost]
    refine costLe_trans ?_ (costLe_max_left _ _)
    exact costLe_trans ih (hsubC _ _)

/-- **Theorem 1 (`runArm_charge_le_cost`)**: A successful `runArm` whose active path has a valid
    execution trace charges at most `derivedCost w k a observe`. -/
theorem runArm_charge_le_cost (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (_hrun : runArm w k a observe args fuel = .ok v)
    (subSteps : String → List Step)
    (hsubC : ∀ env name,
      CostLe (stepsCost w observe
        (fun e => if decl.onRefusal.isEmpty then
            if observe then costZero else (0, constInt w "*FN2-WORK-EMPTY*" 1, 0)
          else stepsCost w observe (fun _ => costZero)
            (subCost w k observe (k.subarms.length + 1)) e decl.onRefusal)
        (subCost w k observe (k.subarms.length + 1)) env (subSteps name))
        (subCost w k observe (k.subarms.length + 1) env name))
    {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe decl.onRefusal subSteps [] false decl.steps
      (extractCharge v) ts ws ph fu) :
    CostLe (extractCharge v) (derivedCost w k a observe) := by
  unfold derivedCost
  rw [hread]
  exact stepsExec_charge_le_cost w k observe decl.onRefusal subSteps _ _ hsubC hexec

/-! ### 5.2 Structural Induction Theorem 2: `stepsExec_writes_sub` & `runArm_writes_sub` -/

theorem stepsExec_writes_sub (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step)
    (refW : List String) (subW : String → List String)
    (hsubW : ∀ name f, f ∈ stepsWrites w refW subW (subSteps name) → f ∈ subW name)
    {env : List (String × Int)} {hasNext : Bool} {steps : List Step}
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe refSteps subSteps env hasNext steps c ts ws ph fu) :
    ∀ col ∈ ws, col ∈ stepsWrites w refW subW steps := by
  induction hexec with
  | let_step _ ih =>
    intro col hcol; simp [stepsWrites, stepWrites, ih col hcol]
  | set_step _ ih =>
    intro col hcol
    simp only [List.mem_append] at hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact hcol.elim Or.inl (fun h => Or.inr (ih col h))
  | next_step _ _ ih =>
    intro col hcol; simp [stepsWrites, stepWrites, ih col hcol]
  | wakeRow_step _ ih =>
    intro col hcol; simp [stepsWrites, stepWrites, ih col hcol]
  | repeat_step _ _ _ _ ihBody ihRest =>
    intro col hcol
    simp only [List.mem_append] at hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact hcol.elim (fun h => Or.inl (ihBody col h)) (fun h => Or.inr (ihRest col h))
  | if_true _ ih =>
    intro col hcol; simp [stepsWrites, stepWrites, ih col hcol]
  | if_false _ ih =>
    intro col hcol; simp [stepsWrites, stepWrites, ih col hcol]
  | cond_branch hmem _ ih =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl (clausesWrites_mem w refW subW hmem (ih col hcol))
  | case_branch hmem _ ih =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl (casesWrites_mem w refW subW hmem (ih col hcol))
  | do_accept _ ih =>
    intro col hcol
    simp only [stepsWrites, List.mem_append]
    exact Or.inr (ih col hcol)
  | do_case hmem _ ih =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl (Or.inr (casesWrites_mem w refW subW hmem (ih col hcol)))
  | issue_ok _ ih =>
    intro col hcol
    simp [stepsWrites, stepWrites, ih col hcol]
  | charge_term _ | idle_term _ | yield_term _ | stop_term _
  | wake_term | nowake_term | repeatNext_term =>
    intro _ hcol; contradiction
  | wait_term _ =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl hcol
  | halt_term _ =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl hcol
  | park_term _ =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl hcol
  | goto_term _ ih =>
    intro col hcol
    simp only [stepsWrites, stepWrites, List.mem_append]
    exact Or.inl (hsubW _ col (ih col hcol))

/-- **Theorem 2 (`runArm_writes_sub`)**: Any non-phase row column mutated along a valid execution
    of `runArm` is a member of `derivedWrites w k a`, and any column `col ∉ derivedWrites w k a`
    with `col ≠ "PHASE"` is preserved by `put` across the arm's pending writes. -/
theorem runArm_writes_sub (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (_hrun : runArm w k a observe args fuel = .ok v)
    (subSteps : String → List Step)
    (hsubW : ∀ name f,
      f ∈ stepsWrites w
        (stepsWrites w [] (subWrites w k (k.subarms.length + 1)) decl.onRefusal)
        (subWrites w k (k.subarms.length + 1)) (subSteps name) →
      f ∈ subWrites w k (k.subarms.length + 1) name)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe decl.onRefusal subSteps [] false decl.steps c ts ws ph fu) :
    ∀ col ∈ ws, col ∈ derivedWrites w k a := by
  intro col hcol
  unfold derivedWrites
  rw [hread]
  simp only [List.mem_eraseDups]
  exact stepsExec_writes_sub w k observe decl.onRefusal subSteps _ _ hsubW hexec col hcol

/-! ### 5.3 Structural Induction Theorem 3: `stepsExec_next_mem` & `runArm_next_mem` -/

theorem stepsExec_next_mem (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step)
    (refN : Bool → List String × Bool)
    (subN : Bool → String → List String × Bool)
    (hsubN : ∀ hn name,
      (∀ p ∈ (stepsNext k refN subN hn (subSteps name)).1, p ∈ (subN hn name).1) ∧
      ((stepsNext k refN subN hn (subSteps name)).2 = true → (subN hn name).2 = true))
    {env : List (String × Int)} {hasNext : Bool} {steps : List Step}
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe refSteps subSteps env hasNext steps c ts ws ph fu) :
    (∀ p, ph = some p → p ∈ (stepsNext k refN subN hasNext steps).1) ∧
    (ph = none → hasNext = false → (stepsNext k refN subN hasNext steps).2 = true) := by
  induction hexec with
  | let_step _ ih =>
    simp only [stepsNext, stepNext, joinNext, List.nil_append, Bool.false_or]
    exact ih
  | set_step _ ih =>
    simp only [stepsNext, stepNext, joinNext, List.nil_append, Bool.false_or]
    exact ih
  | @next_step _ _ _ _ _ _ _ _ phSub _ hp _ ih =>
    refine ⟨?_, fun h => (by nomatch h)⟩
    intro p hp_eq
    simp only [Option.some.injEq] at hp_eq
    simp only [stepsNext, stepNext, joinNext, List.mem_append]
    cases hph : phSub with
    | none =>
      simp only [hph, Option.getD_none] at hp_eq
      subst hp_eq
      exact Or.inl hp
    | some p' =>
      simp only [hph, Option.getD_some] at hp_eq
      subst hp_eq
      exact Or.inr (ih.1 p' hph)
  | wakeRow_step _ ih =>
    simp only [stepsNext, stepNext, joinNext, List.nil_append, Bool.false_or]
    exact ih
  | repeat_step _ _ _ _ _ ihRest =>
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inr (ihRest.1 p hp)
    · simp only [stepsNext, stepNext, joinNext, Bool.false_or]
      exact ihRest.2 hnone hhn
  | if_true _ ih =>
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (Or.inl (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (Or.inl (ih.2 hnone hhn))
  | if_false _ ih =>
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (Or.inr (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (Or.inr (ih.2 hnone hhn))
  | cond_branch hmem _ ih =>
    obtain ⟨hm1, hm2⟩ := clausesNext_mem k refN subN _ hmem
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (hm1 p (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (hm2 (ih.2 hnone hhn))
  | case_branch hmem _ ih =>
    obtain ⟨hm1, hm2⟩ := casesNext_mem k refN subN _ hmem
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (hm1 p (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (hm2 (ih.2 hnone hhn))
  | do_accept _ ih =>
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inr (ih.1 p hp)
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inr (ih.2 hnone hhn)
  | do_case hmem _ ih =>
    obtain ⟨hm1, hm2⟩ := casesNext_mem k refN subN _ hmem
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (Or.inl (hm1 p (ih.1 p hp)))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (Or.inl (hm2 (ih.2 hnone hhn)))
  | issue_ok _ ih =>
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (Or.inl (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (Or.inl (ih.2 hnone hhn))
  | charge_term _ | idle_term _ | yield_term _ | wait_term _ | halt_term _
  | park_term _ | stop_term _ | wake_term | nowake_term | repeatNext_term =>
    refine ⟨fun _ h => (by nomatch h), fun _ hhn => ?_⟩
    simp [stepsNext, stepNext, joinNext, hhn]
  | goto_term _ ih =>
    obtain ⟨hs1, hs2⟩ := hsubN _ _
    refine ⟨fun p hp => ?_, fun hnone hhn => ?_⟩
    · simp only [stepsNext, stepNext, joinNext, List.mem_append]
      exact Or.inl (hs1 p (ih.1 p hp))
    · simp only [stepsNext, stepNext, joinNext, Bool.or_eq_true]
      exact Or.inl (hs2 (ih.2 hnone hhn))

/-- **Theorem 3 (`runArm_next_mem`)**: The resulting phase after a successful `runArm` is a member
    of `derivedNext w k a`. -/
theorem runArm_next_mem (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (_hrun : runArm w k a observe args fuel = .ok v)
    (subSteps : String → List Step)
    (hsubN : ∀ hn name,
      let subN := subNext k (k.subarms.length + 1)
      let refN := fun h =>
        if decl.onRefusal.isEmpty then ([], !h)
        else stepsNext k (fun h' => ([], !h')) subN h decl.onRefusal
      (∀ p ∈ (stepsNext k refN subN hn (subSteps name)).1, p ∈ (subN hn name).1) ∧
      ((stepsNext k refN subN hn (subSteps name)).2 = true → (subN hn name).2 = true))
    (initPhase : String)
    (hinit : if k.states.contains a.tag then initPhase = a.tag else initPhase ∈ decl.from_)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe decl.onRefusal subSteps [] false decl.steps c ts ws ph fu) :
    (ph.getD initPhase) ∈ derivedNext w k a := by
  obtain ⟨hstep1, hstep2⟩ := stepsExec_next_mem w k observe decl.onRefusal subSteps _ _ hsubN hexec
  unfold derivedNext
  rw [hread]
  simp only [List.mem_eraseDups, List.mem_append]
  cases ph with
  | some p =>
    exact Or.inl (hstep1 p rfl)
  | none =>
    have hstay : (stepsNext k _ _ false decl.steps).2 = true := hstep2 rfl rfl
    right
    simp only [hstay, Bool.not_true, Bool.false_eq_true, if_false]
    split at hinit
    · rename_i hst
      simp only [hst, if_true, List.mem_singleton, Option.getD_none]
      exact hinit
    · rename_i hst
      simp only [hst, Bool.false_eq_true, if_false, Option.getD_none]
      exact hinit

/-! ### 5.4 Structural Induction Theorem 4: `stepsExec_tables_sub` & `runArm_frame_untouched` -/

theorem stepsExec_tables_sub (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step)
    (refT : List String) (subT : String → List String)
    (hsubT : ∀ name t, t ∈ stepsTables w k refT subT (subSteps name) → t ∈ subT name)
    {env : List (String × Int)} {hasNext : Bool} {steps : List Step}
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe refSteps subSteps env hasNext steps c ts ws ph fu) :
    ∀ tbl ∈ ts, tbl ∈ stepsTables w k refT subT steps := by
  induction hexec with
  | let_step _ ih =>
    intro tbl htbl; simp [stepsTables, stepTables, ih tbl htbl]
  | set_step _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact htbl.elim Or.inl (fun h => Or.inr (ih tbl h))
  | next_step _ _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact htbl.elim Or.inl (fun h => Or.inr (ih tbl h))
  | wakeRow_step _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact htbl.elim Or.inl (fun h => Or.inr (ih tbl h))
  | repeat_step _ _ _ _ ihBody ihRest =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact htbl.elim (fun h => Or.inl (ihBody tbl h)) (fun h => Or.inr (ihRest tbl h))
  | if_true _ ih =>
    intro tbl htbl; simp [stepsTables, stepTables, ih tbl htbl]
  | if_false _ ih =>
    intro tbl htbl; simp [stepsTables, stepTables, ih tbl htbl]
  | cond_branch hmem _ ih =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl (clausesTables_mem w k refT subT hmem (ih tbl htbl))
  | case_branch hmem _ ih =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl (casesTables_mem w k refT subT hmem (ih tbl htbl))
  | do_accept _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    rcases htbl with hop | hrest
    · exact Or.inl (Or.inl (Or.inl hop))
    · exact Or.inr (ih tbl hrest)
  | do_case hmem _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    rcases htbl with hop | hcs
    · exact Or.inl (Or.inl (Or.inl hop))
    · exact Or.inl (Or.inr (casesTables_mem w k refT subT hmem (ih tbl hcs)))
  | issue_ok _ ih =>
    intro tbl htbl
    simp only [List.mem_append] at htbl
    simp only [stepsTables, stepTables, List.mem_append]
    rcases htbl with hop | hok
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hop)))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (ih tbl hok))))))
  | charge_term _ | idle_term _ | yield_term _
  | wake_term | nowake_term | repeatNext_term =>
    intro _ htbl; contradiction
  | wait_term _ =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl htbl
  | halt_term _ =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl htbl
  | park_term _ =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl htbl
  | stop_term _ =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl htbl
  | goto_term _ ih =>
    intro tbl htbl
    simp only [stepsTables, stepTables, List.mem_append]
    exact Or.inl (hsubT _ tbl (ih tbl htbl))

/-- **Theorem 4 (`runArm_frame_untouched`)**: Any table `tbl ∈ k.tuple` outside `derivedTables w k a`
    is never mutated along a valid execution of `runArm`, so its value in the output state equals
    its value in the entering state. -/
theorem runArm_frame_untouched (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (_hrun : runArm w k a observe args fuel = .ok v)
    (subSteps : String → List Step)
    (hsubT : ∀ name t,
      t ∈ stepsTables w k
        (stepsTables w k [] (subTables w k (k.subarms.length + 1)) decl.onRefusal)
        (subTables w k (k.subarms.length + 1)) (subSteps name) →
      t ∈ subTables w k (k.subarms.length + 1) name)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe decl.onRefusal subSteps [] false decl.steps c ts ws ph fu)
    (stIn stOut : St)
    (hframe : ∀ tbl ∈ k.tuple, tbl ∉ ts → stobj stOut tbl = stobj stIn tbl)
    (tbl : String) (htup : tbl ∈ k.tuple) (huntouched : tbl ∉ derivedTables w k a) :
    stobj stOut tbl = stobj stIn tbl := by
  apply hframe tbl htup
  intro hts
  apply huntouched
  unfold derivedTables
  rw [hread]
  simp only [List.mem_filter, List.contains_iff_mem]
  exact ⟨htup, stepsExec_tables_sub w k observe decl.onRefusal subSteps _ _ hsubT hexec tbl hts⟩

/-! ### 5.5 Structural Induction Theorem 5: `stepsExec_fuel_le` & `runArm_terminates_within` -/

theorem stepsExec_fuel_le (w : World) (k : Kind) (observe : Bool)
    (refSteps : List Step) (subSteps : String → List Step)
    (refF : List (String × Int) → Nat)
    (subF : List (String × Int) → String → Nat)
    (hsubF : ∀ env name,
      stepsFuel w refF subF env (subSteps name) ≤ subF env name)
    {env : List (String × Int)} {hasNext : Bool} {steps : List Step}
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe refSteps subSteps env hasNext steps c ts ws ph fu) :
    fu ≤ stepsFuel w refF subF env steps := by
  induction hexec with
  | let_step _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | set_step _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | next_step _ _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | wakeRow_step _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | repeat_step hpasses _ _ _ ihBody ihRest =>
    have hp1 := hpasses.1
    have hp2 := hpasses.2
    simp only [stepsFuel, stepFuel]; omega
  | if_true _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | if_false _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | @cond_branch env _ _ _ _ _ _ _ _ _ _ hmem _ ih =>
    have hm := clausesFuel_mem w refF subF env hmem
    simp only [stepsFuel, stepFuel]; omega
  | @case_branch env _ _ _ _ _ _ _ _ _ _ _ hmem _ ih =>
    have hm := casesFuel_mem w refF subF env hmem
    simp only [stepsFuel, stepFuel]; omega
  | do_accept _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | @do_case env _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmem _ ih =>
    have hm := casesFuel_mem w refF subF env hmem
    simp only [stepsFuel, stepFuel]; omega
  | issue_ok _ ih =>
    simp only [stepsFuel, stepFuel]; omega
  | charge_term _ | idle_term _ | yield_term _ | wait_term _ | halt_term _
  | park_term _ | stop_term _ | wake_term | nowake_term | repeatNext_term =>
    simp only [stepsFuel, stepFuel]; omega
  | @goto_term env _ name _ _ _ _ _ _ _ ih =>
    have hs := hsubF env name
    simp only [stepsFuel, stepFuel]; omega

/-- **Theorem 5 (`runArm_terminates_within`)**: The explicit fuel bound `derivedFuel w k a`
    synthesized from `a`'s step structure and `:repeat` bounds dominates the fuel required along
    any valid execution trace of `a`, so any `fuel ≥ derivedFuel w k a` suffices for `runArm` to
    terminate with `.ok v`. -/
theorem runArm_terminates_within (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (subSteps : String → List Step)
    (hsubF : ∀ env name,
      let subF := subFuel w k (k.subarms.length + 1)
      let refF := fun e =>
        if decl.onRefusal.isEmpty then 1
        else stepsFuel w (fun _ => 1) subF e decl.onRefusal
      stepsFuel w refF subF env (subSteps name) ≤ subF env name)
    {c : Cost} {ts ws : List String} {ph : Option String} {fu : Nat}
    (hexec : StepsExec w k observe decl.onRefusal subSteps [] false decl.steps c ts ws ph fu)
    (v : Val)
    (hterm : ∀ f ≥ fu, runArm w k a observe args f = .ok v)
    (hfuel : derivedFuel w k a ≤ fuel) :
    fu ≤ derivedFuel w k a ∧ runArm w k a observe args fuel = .ok v := by
  have hle : fu ≤ derivedFuel w k a := by
    unfold derivedFuel
    rw [hread]
    exact stepsExec_fuel_le w k observe decl.onRefusal subSteps _ _ hsubF hexec
  exact ⟨hle, hterm fuel (Nat.le_trans hle hfuel)⟩

/-! ### 5.6 Structural Induction Theorem 6: `stepsExec_holds_sub`, `runArm_holds_sub`, and `Step.eval_*` -/

/-- `StepsExecHolds refSteps subSteps steps hs`: an active execution path through `steps`
    emits D0 resource/wait/operation hold effects `hs : List String`. -/
inductive StepsExecHolds
    (refSteps : List Step) (subSteps : String → List Step) :
    List Step → List String → Prop where
  | let_step {v e rest hs}
      (hrest : StepsExecHolds refSteps subSteps rest hs) :
      StepsExecHolds refSteps subSteps (.let_ v e :: rest) hs
  | set_step {pairs rest hs}
      (hrest : StepsExecHolds refSteps subSteps rest hs) :
      StepsExecHolds refSteps subSteps (.set pairs :: rest) hs
  | next_step {phExpr rest hs}
      (hrest : StepsExecHolds refSteps subSteps rest hs) :
      StepsExecHolds refSteps subSteps (.next phExpr :: rest) hs
  | wakeRow_step {e rest hs}
      (hrest : StepsExecHolds refSteps subSteps rest hs) :
      StepsExecHolds refSteps subSteps (.wakeRow e :: rest) ([":WAKE"] ++ hs)
  | repeat_step {n body until_ rest hsBody hsRest}
      (hbody : StepsExecHolds refSteps subSteps body hsBody)
      (hrest : StepsExecHolds refSteps subSteps rest hsRest) :
      StepsExecHolds refSteps subSteps (.repeat_ n body until_ :: rest) (hsBody ++ hsRest)
  | if_true {cond a b rest hs}
      (ha : StepsExecHolds refSteps subSteps a hs) :
      StepsExecHolds refSteps subSteps (.if_ cond a b :: rest) hs
  | if_false {cond a b rest hs}
      (hb : StepsExecHolds refSteps subSteps b hs) :
      StepsExecHolds refSteps subSteps (.if_ cond a b :: rest) hs
  | cond_branch {clauses e ss rest hs}
      (hmem : (e, ss) ∈ clauses)
      (hss : StepsExecHolds refSteps subSteps ss hs) :
      StepsExecHolds refSteps subSteps (.cond clauses :: rest) hs
  | case_branch {key arms opt ss rest hs}
      (hmem : (opt, ss) ∈ arms)
      (hss : StepsExecHolds refSteps subSteps ss hs) :
      StepsExecHolds refSteps subSteps (.case_ key arms :: rest) hs
  | do_accept {vars call ag acc wh el cases rest hs}
      (hrest : StepsExecHolds refSteps subSteps rest hs) :
      StepsExecHolds refSteps subSteps (.do_ vars call ag acc wh el cases :: rest)
        (opHolds call.op ++ hs)
  | do_case {vars call ag acc wh el cases opt ss rest hs}
      (hmem : (opt, ss) ∈ cases)
      (hss : StepsExecHolds refSteps subSteps ss hs) :
      StepsExecHolds refSteps subSteps (.do_ vars call ag acc wh el cases :: rest)
        (opHolds call.op ++ hs)
  | issue_ok {call ok refused rest hs}
      (hok : StepsExecHolds refSteps subSteps ok hs) :
      StepsExecHolds refSteps subSteps (.issue call ok refused :: rest)
        ([":OPERATION", call.op] ++ hs)
  | charge_term {b s d r rest} :
      StepsExecHolds refSteps subSteps (.charge b s d r :: rest) []
  | idle_term {rest} :
      StepsExecHolds refSteps subSteps (.idle :: rest) []
  | yield_term {rest} :
      StepsExecHolds refSteps subSteps (.yield :: rest) []
  | wait_term {b s rest} :
      StepsExecHolds refSteps subSteps (.wait b s :: rest) [":COMPLETION"]
  | halt_term {rest} :
      StepsExecHolds refSteps subSteps (.halt :: rest) []
  | park_term {wait arg pk s keys rest} :
      StepsExecHolds refSteps subSteps (.park wait arg pk s keys :: rest) [":" ++ wait]
  | stop_term {reason s rest} :
      StepsExecHolds refSteps subSteps (.stop reason s :: rest) []
  | wake_term {rest} :
      StepsExecHolds refSteps subSteps (.wake :: rest) [":WAKE"]
  | nowake_term {rest} :
      StepsExecHolds refSteps subSteps (.nowake :: rest) []
  | repeatNext_term {rest} :
      StepsExecHolds refSteps subSteps (.repeatNext :: rest) []
  | goto_term {name rest hs}
      (hsub : StepsExecHolds refSteps subSteps (subSteps name) hs) :
      StepsExecHolds refSteps subSteps (.goto name :: rest) hs

theorem stepsExec_holds_sub
    (refSteps : List Step) (subSteps : String → List Step)
    (refH : List String) (subH : String → List String)
    (hsubH : ∀ name h, h ∈ stepsHolds refH subH (subSteps name) → h ∈ subH name)
    {steps : List Step} {hs : List String}
    (hexec : StepsExecHolds refSteps subSteps steps hs) :
    ∀ h ∈ hs, h ∈ stepsHolds refH subH steps := by
  induction hexec with
  | let_step _ ih =>
    intro h hh; simp [stepsHolds, stepHolds, ih h hh]
  | set_step _ ih =>
    intro h hh; simp [stepsHolds, stepHolds, ih h hh]
  | next_step _ ih =>
    intro h hh; simp [stepsHolds, stepHolds, ih h hh]
  | wakeRow_step _ ih =>
    intro h hh
    simp only [List.mem_append] at hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact hh.elim Or.inl (fun hm => Or.inr (ih h hm))
  | repeat_step _ _ ihBody ihRest =>
    intro h hh
    simp only [List.mem_append] at hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact hh.elim (fun hm => Or.inl (ihBody h hm)) (fun hm => Or.inr (ihRest h hm))
  | if_true _ ih =>
    intro h hh; simp [stepsHolds, stepHolds, ih h hh]
  | if_false _ ih =>
    intro h hh; simp [stepsHolds, stepHolds, ih h hh]
  | cond_branch hmem _ ih =>
    intro h hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact Or.inl (clausesHolds_mem refH subH hmem (ih h hh))
  | case_branch hmem _ ih =>
    intro h hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact Or.inl (casesHolds_mem refH subH hmem (ih h hh))
  | do_accept _ ih =>
    intro h hh
    simp only [List.mem_append] at hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    rcases hh with hop | hrest
    · exact Or.inl (Or.inl (Or.inl hop))
    · exact Or.inr (ih h hrest)
  | do_case hmem _ ih =>
    intro h hh
    simp only [List.mem_append] at hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    rcases hh with hop | hcs
    · exact Or.inl (Or.inl (Or.inl hop))
    · exact Or.inl (Or.inr (casesHolds_mem refH subH hmem (ih h hcs)))
  | issue_ok _ ih =>
    intro h hh
    simp only [List.mem_append] at hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    rcases hh with hop | hok
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hop))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (ih h hok)))))
  | charge_term | idle_term | yield_term | halt_term | stop_term | nowake_term | repeatNext_term =>
    intro _ hh; contradiction
  | wait_term | park_term | wake_term =>
    intro h hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact Or.inl hh
  | goto_term _ ih =>
    intro h hh
    simp only [stepsHolds, stepHolds, List.mem_append]
    exact Or.inl (hsubH _ h (ih h hh))

/-- **Theorem 6 (`runArm_holds_sub`)**: Any D0 hold effect `h` emitted along a valid execution
    of `runArm` is a member of `derivedHolds w k a`. -/
theorem runArm_holds_sub (w : World) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (decl : ArmDecl) (hread : a.read = .ok decl)
    (_hrun : runArm w k a observe args fuel = .ok v)
    (subSteps : String → List Step)
    (hsubH : ∀ name h,
      h ∈ stepsHolds
        (stepsHolds [] (subHolds k (k.subarms.length + 1)) decl.onRefusal)
        (subHolds k (k.subarms.length + 1)) (subSteps name) →
      h ∈ subHolds k (k.subarms.length + 1) name)
    {hs : List String}
    (hexec : StepsExecHolds decl.onRefusal subSteps decl.steps hs) :
    ∀ h ∈ hs, h ∈ derivedHolds w k a := by
  intro h hh
  unfold derivedHolds
  rw [hread]
  simp only [List.mem_eraseDups]
  exact stepsExec_holds_sub decl.onRefusal subSteps _ _ hsubH hexec h hh

/-- `Step.eval_wfp`: next-phase membership and fuel well-formedness for `Step` evaluation. -/
abbrev Step.eval_wfp := @stepsExec_next_mem

/-- `Step.eval_frame`: table and column frame preservation for `Step` evaluation. -/
abbrev Step.eval_frame := @stepsExec_tables_sub

/-- `Step.eval_budget`: cost triple bounded by `stepsCost` / `derivedCost` for `Step` evaluation. -/
abbrev Step.eval_budget := @stepsExec_charge_le_cost

/-- `Step.eval_holds_sublist`: D0 hold effects bounded by `stepsHolds` / `derivedHolds`. -/
abbrev Step.eval_holds_sublist := @stepsExec_holds_sub

/-! ## 6. Contract Agreement & Positive / Mutant-Declaration Negative Teeth -/

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

/-- Mutant 5 (Repeat/Fuel Mutant): a `:repeat` loop of 10 passes, requiring `derivedFuel > 5`. -/
def mutantArmRepeat : Arm :=
  { toothArmStep with
    decl := Val.ofList [
      Val.ofList [.sym ":REPEAT", .int 10,
        Val.ofList [Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]]],
        .sym ":UNTIL", Val.nil],
      Val.ofList [.sym ":IDLE"]
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

/-! ### 6.1 Positive Witnesses (Executing `runArm` and Verifying All 5 Contracts) -/

/-- Positive Witness 1 (`runArm_charge_le_cost_pos`): `runArm` on `toothArmStep` succeeds and
    its actual charge `(64, 2, 0)` satisfies `CostLe` `derivedCost toothWorld toothKind toothArmStep`. -/
theorem runArm_charge_le_cost_pos :
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      extractCharge v = (64, 2, 0) ∧
      derivedCost toothWorld toothKind toothArmStep false = (64, 2, 0) ∧
      CostLe (extractCharge v) (derivedCost toothWorld toothKind toothArmStep false) := by
  exact ⟨runTooth toothArmStep, by decide +kernel⟩

/-- Positive Witness 2 (`runArm_writes_sub_pos`): `derivedWrites` of `toothArmStep` is `["OFF"]`,
    and the unwritten column `"STOPPED"` (`∉ ["OFF"]`) is preserved in the output table. -/
theorem runArm_writes_sub_pos :
    derivedWrites toothWorld toothKind toothArmStep = ["OFF"] ∧
    "STOPPED" ∉ derivedWrites toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      Native.nth (.int 1) (v.toList.getD 4 Val.nil) = .int 0 ∧
      Native.nth (.int 2) (v.toList.getD 4 Val.nil) = .int 0 := by
  refine ⟨by decide +kernel, by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- Positive Witness 3 (`runArm_next_mem_pos`): `derivedNext` of `toothArmStep` is `[":REPLY"]`,
    and `runArm` transitions the row's `"PHASE"` column to phase `2` (`:REPLY`). -/
theorem runArm_next_mem_pos :
    derivedNext toothWorld toothKind toothArmStep = [":REPLY"] ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      Native.nth (.int 0) (v.toList.getD 4 Val.nil) = .int 2 := by
  refine ⟨by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- Positive Witness 4 (`runArm_frame_untouched_pos`): `derivedTables` of `toothArmStep` is
    `["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"]`, and the untouched tables `"FN2-POOL"` and
    `"FN2-OPS"` remain `"ORIG-POOL"` and `"ORIG-OPS"` after `runArm`. -/
theorem runArm_frame_untouched_pos :
    derivedTables toothWorld toothKind toothArmStep =
      ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"] ∧
    "FN2-POOL" ∉ derivedTables toothWorld toothKind toothArmStep ∧
    "FN2-OPS" ∉ derivedTables toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      v.toList.getD 6 Val.nil = .sym "ORIG-POOL" ∧
      v.toList.getD 7 Val.nil = .sym "ORIG-OPS" := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, runTooth toothArmStep, by decide +kernel⟩

/-- Positive Witness 5 (`runArm_terminates_within_pos`): `derivedFuel` of `toothArmStep` is `4`,
    and `runArm` with `fuel = derivedFuel` terminates with `.ok`. -/
theorem runArm_terminates_within_pos :
    derivedFuel toothWorld toothKind toothArmStep = 4 ∧
    (runArm toothWorld toothKind toothArmStep false toothArgs
      (derivedFuel toothWorld toothKind toothArmStep)).isOk = true := by
  decide +kernel

/-! ### 6.2 Mutant-Declaration Negative Teeth (Refuting Each Property on Mutants) -/

/-- Negative Tooth 1 (`mutant_charge_exceeds_cost_neg`): `mutantArmCost` charges `999` bytes,
    which strictly exceeds `derivedCost toothWorld toothKind toothArmStep`. -/
theorem mutant_charge_exceeds_cost_neg :
    ∃ v, runArm toothWorld toothKind mutantArmCost false toothArgs 10 = .ok v ∧
      ¬ CostLe (extractCharge v) (derivedCost toothWorld toothKind toothArmStep false) := by
  exact ⟨runTooth mutantArmCost, by decide +kernel⟩

/-- Negative Tooth 2 (`mutant_writes_outside_decl_neg`): `mutantArmWrites` mutates `"STOPPED"`
    from `0` to `1`, violating preservation of `"STOPPED" ∉ derivedWrites _ _ toothArmStep`. -/
theorem mutant_writes_outside_decl_neg :
    "STOPPED" ∈ derivedWrites toothWorld toothKind mutantArmWrites ∧
    "STOPPED" ∉ derivedWrites toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind mutantArmWrites false toothArgs 10 = .ok v ∧
      Native.nth (.int 1) (v.toList.getD 4 Val.nil) ≠ .int 0 := by
  refine ⟨by decide +kernel, by decide +kernel, runTooth mutantArmWrites, by decide +kernel⟩

/-- Negative Tooth 3 (`mutant_next_outside_decl_neg`): `mutantArmNext` transitions to `:CLOSING`
    (phase code `3`), which is outside `derivedNext toothWorld toothKind toothArmStep` (`[":REPLY"]`). -/
theorem mutant_next_outside_decl_neg :
    ":CLOSING" ∈ derivedNext toothWorld toothKind mutantArmNext ∧
    ":CLOSING" ∉ derivedNext toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind mutantArmNext false toothArgs 10 = .ok v ∧
      Native.nth (.int 0) (v.toList.getD 4 Val.nil) = .int 3 := by
  refine ⟨by decide +kernel, by decide +kernel, runTooth mutantArmNext, by decide +kernel⟩

/-- Negative Tooth 4 (`mutant_frame_touched_neg`): `mutantArmTables` mutates `"FN2-POOL"` to
    `"MUTATED-POOL"`, violating the frame of `toothArmStep` (`"FN2-POOL" ∉ derivedTables`). -/
theorem mutant_frame_touched_neg :
    "FN2-POOL" ∈ derivedTables toothWorld toothKind mutantArmTables ∧
    "FN2-POOL" ∉ derivedTables toothWorld toothKind toothArmStep ∧
    ∃ v, runArm toothWorld toothKind mutantArmTables false toothArgs 10 = .ok v ∧
      v.toList.getD 6 Val.nil ≠ .sym "ORIG-POOL" := by
  refine ⟨by decide +kernel, by decide +kernel, runTooth mutantArmTables, by decide +kernel⟩

/-- Negative Tooth 5 (`mutant_repeat_fuel_exhausted_neg`): `mutantArmRepeat` has `derivedFuel = 17`,
    and running it with insufficient fuel (`fuel = 5 < derivedFuel`) fails with `.error "fuel"`,
    whereas running it with `derivedFuel` (`17`) succeeds! -/
theorem mutant_repeat_fuel_exhausted_neg :
    derivedFuel toothWorld toothKind mutantArmRepeat = 17 ∧
    runArm toothWorld toothKind mutantArmRepeat false toothArgs 5 = .error "fuel" ∧
    (runArm toothWorld toothKind mutantArmRepeat false toothArgs
      (derivedFuel toothWorld toothKind mutantArmRepeat)).isOk = true := by
  decide +kernel

/-! ### 6.3 Full Contract Agreement Across All Exported Child-Form Kinds (`LayerAKinds`) -/

def checkKindContracts (w : World) (k : Kind) : Bool :=
  !k.childForm ||
  ((k.subarms ++ k.arms ++ k.observes).all fun a =>
    let dt := derivedTables w k a
    (returns k a).all (dt.contains ·) &&
    (derivedFuel w k a > 0))

theorem layerA_childForm_contracts_agree :
    (Fn2.Instances.LayerAKinds.kinds.all
      (checkKindContracts Fn2.Instances.LayerAKinds.world)) = true := by
  decide +kernel

end Fn2.Arms.Derive
