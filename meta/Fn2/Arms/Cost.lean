import Fn2.Arms
import Fn2.ArmsLemmas
import Fn2.Arms.Bound

/-!
# Fn2.Arms.Cost: the derived charge of an arm, and its soundness for the interpreter

`derivedCost w k a` is a static `(bytes, steps, descriptors)` bound read off `a`'s declaration, or
`none` where the declaration admits no bound (an expression `ival` does not bound, a `:wake` in a run
arm, a refusal or sub-arm cycle that adds work on every turn). `runArm_charge_le_cost` proves that
every run of the interpreter charges at most that bound.
-/

namespace Fn2.Arms.Cost
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Bound

abbrev Cost := Int × Int × Int

def costZero : Cost := (0, 0, 0)
def costAdd (a b : Cost) : Cost := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)
def costMax (a b : Cost) : Cost := (max a.1 b.1, max a.2.1 b.2.1, max a.2.2 b.2.2)
def costScale (n : Int) (c : Cost) : Cost := (n * c.1, n * c.2.1, n * c.2.2)
/-- The componentwise positive part. -/
def cpos (c : Cost) : Cost := (max 0 c.1, max 0 c.2.1, max 0 c.2.2)

def CostLe (a b : Cost) : Prop := a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2

instance : DecidableRel CostLe := fun a b =>
  inferInstanceAs (Decidable (a.1 ≤ b.1 ∧ a.2.1 ≤ b.2.1 ∧ a.2.2 ≤ b.2.2))

/-- The charge triple a run arm's value carries: its first three results, read as integers. -/
def extractCharge (v : Val) : Cost :=
  let xs := v.toList
  ((xs.getD 0 Val.nil).toInt, (xs.getD 1 Val.nil).toInt, (xs.getD 2 Val.nil).toInt)

section
variable (w : World) (k : Kind)

/-- A constant's integer reading, when the world printed it. -/
def constHi (name : String) : Option Int :=
  (w.consts.find? (·.1 == name)).map (·.2.toInt)

/-- The upper end of an optional expression's interval, or `d` when the expression is absent. -/
def hiOpt (senv : SEnv) (e : Option Expr) (d : Option Int) : Option Int :=
  match e with
  | some x => (ival w k senv x).map (·.2)
  | none => d

/-- A `:repeat` pass's bound as the interpreter adds it per pass: one step plus the declared
bounds of the pass's calls; `none` where a call has no declared bound (the interpreter refuses). -/
def passBound (body : List Step) : Option Cost :=
  (body.flatMap Step.calls).foldlM (init := ((0 : Int), (1 : Int), (0 : Int))) fun acc op =>
    match w.ops.find? (·.name == op) with
    | some o => match o.bound with
      | some b => some (costAdd acc b)
      | none => none
    | none => none

/-- Variables a step binds to values the analysis does not bound. -/
def kill (xs : List String) (senv : SEnv) : SEnv := xs.map (·, none) ++ senv

def issueVars : List String := ["FN2-ISSUE-CODE", "FN2-ISSUE-OP", "FN2-ISSUE-OPGEN"]

/-- The static environment after a step, for the steps after it. -/
def stepEnv (senv : SEnv) : Step → SEnv
  | .let_ v e => (v, ival w k senv e) :: senv
  | .do_ vars _ _ _ _ _ _ => kill vars senv
  | _ => senv

def termC (b s d : Option Int) : Option Cost := do
  pure (← b, ← s, ← d)

mutual
/-- A step's charge bound (`refC`: the arm's refusal, `subC`: the sub-arms). -/
def stepCost (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv) :
    Step → Option Cost
  | .let_ _ _ | .set _ | .next _ | .wakeRow _ => some costZero
  | .repeatNext | .wake | .nowake => none
  | .repeat_ n body _ => do
    let b ← ival w k senv n
    let per ← passBound w body
    pure (costScale (max 0 b.2) (cpos per))
  | .do_ vars _ _ _ _ _ cases => do
    let cc ← casesCost refC subC (kill vars senv) cases
    let r ← refC
    pure (costMax cc r)
  | .issue _ ok refused => do
    let senv' := kill issueVars senv
    let cOk ← stepsCost refC subC senv' ok (some costZero)
    let mb ← constHi w "*FN2-WORK-MAILBOX*"
    let r ← refC
    let cEx ← stepsCost refC subC senv' refused (some (0, mb, 0))
    let cRef ← stepsCost refC subC senv' refused (some (costMax (0, mb, 0) r))
    pure (costMax cOk (costMax cEx cRef))
  | .if_ _ a b => do
    pure (costMax (← stepsCost refC subC senv a (some costZero))
      (← stepsCost refC subC senv b (some costZero)))
  | .cond clauses => clausesCost refC subC senv clauses
  | .case_ _ arms => casesCost refC subC senv arms
  | .charge b s d _ => termC (hiOpt w k senv b (some 0)) (hiOpt w k senv s (some 0))
      (hiOpt w k senv d (some 0))
  | .idle | .yield => termC (some 0) (constHi w "*FN2-WORK-EMPTY*") (some 0)
  | .wait b s => termC (hiOpt w k senv b (some 0))
      (hiOpt w k senv s (constHi w "*FN2-WORK-MAILBOX*")) (some 1)
  | .halt => termC (some 0) (constHi w "*FN2-WORK-MAILBOX*") (some 0)
  | .park _ _ _ s _ => termC (some 0) (hiOpt w k senv s (constHi w "*FN2-WORK-MAILBOX*")) (some 0)
  | .stop _ s => termC (some 0) (hiOpt w k senv s (constHi w "*FN2-WORK-EMPTY*")) (some 0)
  | .goto name => subC name

/-- A path's charge bound; `kont` bounds what runs after the path's last step (the interpreter's
`refused ++ ...` continuations of `:issue`). -/
def stepsCost (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv) :
    List Step → Option Cost → Option Cost
  | [], kont => kont
  | s :: rest, kont => do
    let c ← stepCost refC subC senv s
    let r ← stepsCost refC subC (stepEnv w k senv s) rest kont
    pure (match s with
      | .repeat_ _ _ _ => costAdd c r
      | _ => costMax c r)

def casesCost (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv) :
    List (Option (List Val) × List Step) → Option Cost
  | [] => some costZero
  | (_, ss) :: cs => do
    pure (costMax (← stepsCost refC subC senv ss (some costZero)) (← casesCost refC subC senv cs))

def clausesCost (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv) :
    List (Expr × List Step) → Option Cost
  | [] => some costZero
  | (_, ss) :: cs => do
    pure (costMax (← stepsCost refC subC senv ss (some costZero)) (← clausesCost refC subC senv cs))
end

/-- The stop the interpreter takes when an unrouted answer has no refusal to go to, or a
`defcost :faults` code stops the kind: `(0, *FN2-WORK-EMPTY*, 0)`. -/
def stopBase : Option Cost := termC (some 0) (constHi w "*FN2-WORK-EMPTY*") (some 0)

/-- The refusal's bound, from any state: one unfolding over the stop, then checked to be a
post-fixpoint (a refusal that re-enters itself after adding work has none). -/
def refCost (subC : String → Option Cost) (R : List Step) : Option Cost := do
  let base ← stopBase w
  if R.isEmpty then pure base else
  let c0 ← stepsCost w k (some base) subC [] R (some costZero)
  let rc := costMax base c0
  let c1 ← stepsCost w k (some rc) subC [] R (some costZero)
  if decide (CostLe c1 rc) then pure rc else none

/-- The sub-arms' bounds, unfolded `d` times. -/
def subCostN : Nat → String → Option Cost
  | 0, _ => some costZero
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub => match sub.read with
      | .ok decl => do
        let rc ← refCost w k (subCostN d) decl.onRefusal
        stepsCost w k (some rc) (subCostN d) [] decl.steps (some costZero)
      | .error _ => some costZero
    | none => some costZero

/-- `subC` bounds every sub-arm: a post-fixpoint of the sub-arm cost, checked per sub-arm. -/
def subOK (subC : String → Option Cost) : Bool :=
  k.subarms.all fun s =>
    match k.subarms.find? (·.tag == s.tag) with
    | some sub => match sub.read with
      | .ok decl =>
        match refCost w k subC decl.onRefusal with
        | some rc => match stepsCost w k (some rc) subC [] decl.steps (some costZero), subC s.tag with
          | some c, some c' => decide (CostLe c c')
          | _, _ => false
        | none => false
      | .error _ => true
    | none => true

/-- **The derived charge bound of a run arm.** -/
def derivedCost (a : Arm) : Option Cost :=
  match a.read with
  | .ok decl =>
    let subC := subCostN w k (k.subarms.length + 1)
    if subOK w k subC then do
      let rc ← refCost w k subC decl.onRefusal
      stepsCost w k (some rc) subC [] decl.steps (some costZero)
    else none
  | .error _ => none

end

/-! ## Lemmas: the cost algebra -/

theorem costLe_refl (a : Cost) : CostLe a a := ⟨Int.le_refl _, Int.le_refl _, Int.le_refl _⟩

theorem costLe_trans {a b c : Cost} (h1 : CostLe a b) (h2 : CostLe b c) : CostLe a c :=
  ⟨Int.le_trans h1.1 h2.1, Int.le_trans h1.2.1 h2.2.1, Int.le_trans h1.2.2 h2.2.2⟩

theorem costLe_max_left (a b : Cost) : CostLe a (costMax a b) := by
  unfold CostLe costMax; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega

theorem costLe_max_right (a b : Cost) : CostLe b (costMax a b) := by
  unfold CostLe costMax; refine ⟨?_, ?_, ?_⟩ <;> simp only <;> omega

/-- The step a path's bound is built from: a charge below `L⁺ + c` is below `L⁺ + d` for `c ≤ d`. -/
theorem le_addL {x c d : Cost} (L : Cost) (h : CostLe x (costAdd (cpos L) c)) (hcd : CostLe c d) :
    CostLe x (costAdd (cpos L) d) := by
  unfold CostLe costAdd cpos at *; obtain ⟨a1, a2, a3⟩ := h; obtain ⟨b1, b2, b3⟩ := hcd
  simp only at *; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem cpos_nonneg_le (c : Cost) (L : Cost) {x : Cost} (h : CostLe x c) :
    CostLe x (costAdd (cpos L) c) := by
  unfold CostLe costAdd cpos at *; obtain ⟨a1, a2, a3⟩ := h
  simp only at *; refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Lemmas: the interpreter's state through a step -/

local macro "except_step " h:ident : tactic =>
  `(tactic| ((try simp only [bind, Except.bind] at ($h)); split at ($h); · exact absurd $h (by simp)))

theorem put_shape (w : World) (f : Frame) (st st' : St) (pairs : List (String × Val))
    (h : put w f st pairs = .ok st') : st'.vars = st.vars ∧ st'.loopWork = st.loopWork := by
  unfold put at h
  except_step h; except_step h; except_step h; except_step h; except_step h; except_step h
  except_step h
  split at h
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem flush_shape (w : World) (f : Frame) (st st' : St) (h : flush w f st = .ok st') :
    st'.vars = st.vars ∧ st'.loopWork = st.loopWork := by
  unfold flush at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try (simp only [reduceCtorEq] at h; done))
  all_goals
    simp only [Except.ok.injEq] at h; subst h
    first
      | exact ⟨rfl, rfl⟩
      | (rename_i hput; have hs := put_shape w f _ _ _ hput; exact ⟨hs.1, hs.2⟩)

theorem pend_shape {st st' : St} {pairs : List (String × Expr)} (h : pend st pairs = .ok st') :
    st'.vars = st.vars ∧ st'.loopWork = st.loopWork := by
  unfold pend at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem bindOuts_go_shape (st st' : St) (outs : List (Option String))
    (vars : List String) (rs : List Val) (h : bindOuts.go st outs vars rs = .ok st') :
    st'.loopWork = st.loopWork ∧
    ∃ pre, st'.vars = pre ++ st.vars ∧ ∀ p ∈ pre, p.1 ∈ vars := by
  induction outs generalizing st vars rs with
  | nil =>
    cases rs <;> simp [bindOuts.go] at h <;> subst h <;> exact ⟨rfl, [], rfl, by simp⟩
  | cons o os ih =>
    cases o with
    | some s =>
      cases rs with
      | nil => simp [bindOuts.go] at h
      | cons r rs' =>
        simp only [bindOuts.go] at h
        obtain ⟨hl, pre, hv, hp⟩ := ih _ vars rs' h
        exact ⟨hl, pre, hv, hp⟩
    | none =>
      cases vars with
      | nil =>
        cases rs with
        | nil => simp [bindOuts.go] at h
        | cons r rs' =>
          simp only [bindOuts.go] at h
          exact ih st [] rs' h
      | cons v vs' =>
        cases rs with
        | nil => simp [bindOuts.go] at h
        | cons r rs' =>
          simp only [bindOuts.go] at h
          obtain ⟨hl, pre, hv, hp⟩ := ih _ vs' rs' h
          refine ⟨hl, pre ++ [(v, r)], by simp [hv], fun p hm => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hm
          rcases hm with hm | hm
          · exact List.mem_cons_of_mem _ (hp p hm)
          · subst hm; exact List.mem_cons_self

theorem bindOuts_shape (st st' : St) (outs : List (Option String))
    (vars : List String) (res : Val) (h : bindOuts st outs vars res = .ok st') :
    st'.loopWork = st.loopWork ∧
    ∃ pre, st'.vars = pre ++ st.vars ∧ ∀ p ∈ pre, p.1 ∈ vars := by
  unfold bindOuts at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, [], rfl, by simp⟩
  · split at h
    · simp only [Except.ok.injEq] at h; subst h
      exact ⟨rfl, [(_, res)], rfl, by simp⟩
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, [], rfl, by simp⟩
  · exact bindOuts_go_shape st st' outs vars res.toList h

/-! ## Lemmas: the static environment -/

theorem senvFind_cons_ne (senv : SEnv) (x y : String) (b : Option Bnd) (h : y ≠ x) :
    senvFind ((x, b) :: senv) y = senvFind senv y := by
  unfold senvFind
  have : (x == y) = false := by simp [Ne.symm h]
  simp [this]

theorem senvFind_cons_eq (senv : SEnv) (x : String) (b : Option Bnd) :
    senvFind ((x, b) :: senv) x = b := by
  unfold senvFind; simp

theorem envGet_cons_ne (vars : Env) (x y : String) (v : Val) (h : y ≠ x) :
    Env.get? ((x, v) :: vars) y = vars.get? y := by
  unfold Env.get?
  have : (x == y) = false := by simp [Ne.symm h]
  simp [this]

theorem envGet_cons_eq (vars : Env) (x : String) (v : Val) :
    Env.get? ((x, v) :: vars) x = some v := by
  unfold Env.get?; simp

theorem envOK_let (senv : SEnv) (vars : Env) (x : String) (v : Val) (b : Option Bnd)
    (hok : EnvOK senv vars) (hb : ∀ bb, b = some bb → InB v.toInt bb) :
    EnvOK ((x, b) :: senv) ((x, v) :: vars) := by
  intro y bb hy
  by_cases hyx : y = x
  · subst hyx
    rw [senvFind_cons_eq] at hy
    exact ⟨v, envGet_cons_eq _ _ _, hb bb hy⟩
  · rw [senvFind_cons_ne _ _ _ _ hyx] at hy
    obtain ⟨v', hv', hin⟩ := hok y bb hy
    exact ⟨v', by rw [envGet_cons_ne _ _ _ _ hyx]; exact hv', hin⟩

theorem senvFind_kill (xs : List String) (senv : SEnv) (y : String) (bb : Bnd)
    (h : senvFind (kill xs senv) y = some bb) : y ∉ xs ∧ senvFind senv y = some bb := by
  induction xs with
  | nil => exact ⟨by simp, h⟩
  | cons x xs ih =>
    simp only [kill, List.map_cons, List.cons_append] at h
    by_cases hyx : y = x
    · subst hyx; rw [senvFind_cons_eq] at h; cases h
    · rw [senvFind_cons_ne _ _ _ _ hyx] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by simp [hyx, h1], h2⟩

theorem envGet_append_notin (pre vars : Env) (y : String) (h : ∀ p ∈ pre, p.1 ≠ y) :
    Env.get? (pre ++ vars) y = vars.get? y := by
  unfold Env.get?
  rw [List.find?_append]
  have : pre.find? (·.1 == y) = none := by
    rw [List.find?_eq_none]; intro p hp; simpa using h p hp
  simp [this]

theorem envOK_kill (xs : List String) (senv : SEnv) (pre vars : Env)
    (hok : EnvOK senv vars) (hpre : ∀ p ∈ pre, p.1 ∈ xs) :
    EnvOK (kill xs senv) (pre ++ vars) := by
  intro y bb hy
  obtain ⟨hyn, hy'⟩ := senvFind_kill xs senv y bb hy
  obtain ⟨v, hv, hin⟩ := hok y bb hy'
  refine ⟨v, ?_, hin⟩
  rw [envGet_append_notin]
  · exact hv
  · intro p hp heq; exact hyn (heq ▸ hpre p hp)

theorem envOK_nil (vars : Env) : EnvOK [] vars := by
  intro y bb h; simp [senvFind] at h

/-! ## Lemmas: terminals -/

theorem chargeResult_extract (f : Frame) (st : St) (b s d r v : Val)
    (h : chargeResult f st b s d r = .ok (.done v)) :
    extractCharge v = costAdd (b.toInt, s.toInt, d.toInt) st.loopWork := by
  rcases st with ⟨stobjs, vars, pending, next, nextDone, woken, lb, ls, ld⟩
  unfold chargeResult at h
  obtain ⟨t, _, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Res.done.injEq] at h
  subst h
  have hadd : ∀ (x : Val) (n : Int),
      (if n = 0 then x else Val.int (x.toInt + n)).toInt = x.toInt + n := by
    intro x n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, Val.toInt]
  simp [extractCharge, costAdd, Val.ofList, Val.toList, hadd]

theorem charge_le (f : Frame) (st : St) (b s d r v : Val) (hb hs hd : Int)
    (h : chargeResult f st b s d r = .ok (.done v))
    (h1 : b.toInt ≤ hb) (h2 : s.toInt ≤ hs) (h3 : d.toInt ≤ hd) :
    CostLe (extractCharge v) (costAdd (cpos st.loopWork) (hb, hs, hd)) := by
  rw [chargeResult_extract f st b s d r v h]
  unfold CostLe costAdd cpos; simp only; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem const_hi (n : String) (v : Val) (h : const w n = .ok v) : constHi w n = some v.toInt := by
  unfold const at h; unfold constHi
  split at h
  · rename_i p hp; cases h; rw [hp]; rfl
  · cases h

theorem termC_some {b s d : Option Int} {c : Cost} (h : termC b s d = some c) :
    ∃ x y z, b = some x ∧ s = some y ∧ d = some z ∧ c = (x, y, z) := by
  unfold termC at h
  cases b <;> cases s <;> cases d <;> simp [bind, pure] at h ⊢
  exact h.symm

theorem hiOpt_sound (k : Kind) (senv : SEnv) (st : St) (e : Option Expr) (dflt v : Val)
    (d : Option Int) (h : Int) (hok : EnvOK senv st.vars) (hev : evOpt w k st e dflt = .ok v)
    (hh : hiOpt w k senv e d = some h) (hd : ∀ x, d = some x → dflt.toInt ≤ x) :
    v.toInt ≤ h := by
  cases e with
  | none =>
    simp [evOpt] at hev; subst hev
    simp [hiOpt] at hh; exact hd h hh
  | some x =>
    simp only [hiOpt] at hh
    obtain ⟨b, hb, rfl⟩ := map_some hh
    exact (ev_sound w k senv st x v b hok hev hb).2

/-- The interpreter's per-pass bound is `passBound`. -/
theorem passBound_eq (ops : List String) (acc per : Cost)
    (h : ops.foldlM (m := Except String) (init := acc) (fun (b, s, d) op => do
          match (← findOp w op).bound with
          | some (b', s', d') => pure (b + b', s + s', d + d')
          | none => throw s!"{op}'s declared cost has no static bound") = .ok per) :
    ops.foldlM (init := acc) (fun acc op =>
      match w.ops.find? (·.name == op) with
      | some o => match o.bound with
        | some b => some (costAdd acc b)
        | none => none
      | none => none) = some per := by
  induction ops generalizing acc with
  | nil => simp [List.foldlM, pure, Except.pure] at h ⊢; exact h
  | cons op ops ih =>
    simp only [List.foldlM_cons] at h ⊢
    obtain ⟨acc', h1, h2⟩ := bind_ok h
    obtain ⟨o, ho, h1⟩ := bind_ok h1
    unfold findOp at ho
    split at ho
    · rename_i o' hfind
      cases ho
      rw [hfind]
      simp only
      split at h1
      · rename_i b' s' d' hb
        simp [hb, pure, Except.pure] at h1 ⊢
        subst h1
        exact ih _ h2
      · simp [throw, throwThe, MonadExceptOf.throw] at h1
    · cases ho

theorem findM_mem {α : Type} (p : α → Except String Bool) (l : List α) (x : α)
    (h : l.findM? p = .ok (some x)) : x ∈ l := by
  induction l with
  | nil => simp [List.findM?, pure, Except.pure] at h
  | cons a l ih =>
    simp only [List.findM?] at h
    obtain ⟨b, _, h⟩ := bind_ok h
    cases b
    · exact List.mem_cons_of_mem _ (ih h)
    · simp [pure, Except.pure] at h; subst h; exact List.mem_cons_self

theorem casesCost_mem (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv)
    (cs : List (Option (List Val) × List Step)) (opt : Option (List Val)) (ss : List Step) (C : Cost)
    (hmem : (opt, ss) ∈ cs) (h : casesCost w k refC subC senv cs = some C) :
    ∃ c, stepsCost w k refC subC senv ss (some costZero) = some c ∧ CostLe c C := by
  induction cs generalizing C with
  | nil => cases hmem
  | cons p cs ih =>
    obtain ⟨o, ss'⟩ := p
    simp only [casesCost] at h
    cases h1 : stepsCost w k refC subC senv ss' (some costZero) <;> simp [h1, bind] at h
    rename_i c1
    cases h2 : casesCost w k refC subC senv cs <;> simp [h2] at h
    rename_i c2
    subst h
    rcases List.mem_cons.mp hmem with hm | hm
    · cases hm; exact ⟨c1, h1, costLe_max_left _ _⟩
    · obtain ⟨c, hc, hle⟩ := ih c2 hm h2
      exact ⟨c, hc, costLe_trans hle (costLe_max_right _ _)⟩

theorem clausesCost_mem (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv)
    (cs : List (Expr × List Step)) (e : Expr) (ss : List Step) (C : Cost)
    (hmem : (e, ss) ∈ cs) (h : clausesCost w k refC subC senv cs = some C) :
    ∃ c, stepsCost w k refC subC senv ss (some costZero) = some c ∧ CostLe c C := by
  induction cs generalizing C with
  | nil => cases hmem
  | cons p cs ih =>
    obtain ⟨o, ss'⟩ := p
    simp only [clausesCost] at h
    cases h1 : stepsCost w k refC subC senv ss' (some costZero) <;> simp [h1, bind] at h
    rename_i c1
    cases h2 : clausesCost w k refC subC senv cs <;> simp [h2] at h
    rename_i c2
    subst h
    rcases List.mem_cons.mp hmem with hm | hm
    · cases hm; exact ⟨c1, h1, costLe_max_left _ _⟩
    · obtain ⟨c, hc, hle⟩ := ih c2 hm h2
      exact ⟨c, hc, costLe_trans hle (costLe_max_right _ _)⟩

end Fn2.Arms.Cost
