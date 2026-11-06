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

/-- How a step's bound composes with the rest of its path: a `:repeat`'s work adds to whatever
follows; any other step's bound is an alternative to it. -/
def combine (s : Step) (c r : Cost) : Cost :=
  match s with
  | .repeat_ _ _ _ => costAdd c r
  | _ => costMax c r

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
    let cEx ← stepsCost refC subC senv' refused (some (costMax (0, mb, 0) costZero))
    let cRef ← stepsCost refC subC senv' refused (some (costMax (costMax (0, mb, 0) costZero) r))
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
    pure (combine s c r)

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

set_option autoImplicit false
variable (w : World)

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

theorem casesCost_mem (k : Kind) (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv)
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

theorem clausesCost_mem (k : Kind) (refC : Option Cost) (subC : String → Option Cost) (senv : SEnv)
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

theorem run_nil_ne (f : Frame) (fuel : Nat) (st : St) (r : Res) : run w f fuel st [] ≠ .ok r := by
  cases fuel <;> simp [run]

theorem run_stop_le (f : Frame) (hobs : f.observe = false) (k : Kind) (hk : f.kind = k)
    (m : Nat) (st : St) (reason : String) (s : Option Expr) (rest : List Step) (v : Val)
    (senv : SEnv) (hS : Int) (hok : EnvOK senv st.vars)
    (h : run w f (m + 1) st (.stop reason s :: rest) = .ok (.done v))
    (hh : hiOpt w k senv s (constHi w "*FN2-WORK-EMPTY*") = some hS) :
    CostLe (extractCharge v) (costAdd (cpos st.loopWork) (0, hS, 0)) := by
  subst hk
  simp only [run] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨st1, hst1, h⟩ := bind_ok h
  obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 hst1
  obtain ⟨c1, _, h⟩ := bind_ok h
  unfold stopEnd at h
  rw [hobs] at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h <;>
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨c2, _, h⟩ := bind_ok h
    obtain ⟨e, he, h⟩ := bind_ok h
    obtain ⟨sv, hsv, h⟩ := bind_ok h
    have hst : (setStobj st1 "FN2-CONTROL" c2).loopWork = st.loopWork := by
      simp [setStobj, hl1]
    have hok1 : EnvOK senv (setStobj st1 "FN2-CONTROL" c2).vars := by
      simp only [setStobj]; rw [hv1]; exact hok
    have := charge_le f _ _ _ _ _ v 0 hS 0 h (by simp [Val.toInt])
      (hiOpt_sound w f.kind senv _ s e sv _ hS hok1 hsv hh
        (fun x hx => by rw [const_hi w _ e he] at hx; cases hx; exact Int.le_refl _))
      (by simp [Val.toInt])
    rwa [hst] at this

theorem obind {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => simp [bind] at h
  | some a => exact ⟨a, rfl, h⟩

theorem refCost_spec (k : Kind) (subC : String → Option Cost) (R : List Step) (rc : Cost)
    (h : refCost w k subC R = some rc) :
    ∃ e, constHi w "*FN2-WORK-EMPTY*" = some e ∧ CostLe (0, e, 0) rc ∧
      (R ≠ [] → ∃ c1, stepsCost w k (some rc) subC [] R (some costZero) = some c1 ∧
        CostLe c1 rc) := by
  unfold refCost stopBase at h
  obtain ⟨base, hb, h⟩ := obind h
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hb
  cases hx; cases hz
  refine ⟨y, hy, ?_, ?_⟩
  · cases R with
    | nil => simp [pure] at h; subst h; exact costLe_refl _
    | cons s R =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
      obtain ⟨c0, _, h⟩ := obind h
      obtain ⟨c1, _, h⟩ := obind h
      split at h
      · simp [pure] at h; subst h; exact costLe_max_left _ _
      · cases h
  · intro hne
    cases R with
    | nil => exact absurd rfl hne
    | cons s R =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h
      obtain ⟨c0, _, h⟩ := obind h
      obtain ⟨c1, hc1, h⟩ := obind h
      split at h
      · rename_i hle
        simp [pure] at h; subst h
        exact ⟨c1, hc1, of_decide_eq_true hle⟩
      · cases h

theorem faultRoute_cases (answers : Answers) (faults : List Val) (code : Val) (R : List Step) :
    faultRoute answers faults code R = R ∨
      faultRoute answers faults code R = [.stop "MACHINE-PHASE" none] := by
  have hite : ∀ (c : Bool) (a b : List Step),
      (if c = true then a else b) = b ∨ (if c = true then a else b) = a := by
    intro c a b; cases c <;> simp
  unfold faultRoute; dsimp only; exact hite _ _ _

theorem bindOuts_nil_vars (st st' : St) (outs : List (Option String)) (res : Val)
    (h : bindOuts st outs [] res = .ok st') : st'.vars = st.vars ∧ st'.loopWork = st.loopWork := by
  obtain ⟨hl, pre, hv, hp⟩ := bindOuts_shape st st' outs [] res h
  have : pre = [] := by
    cases pre with
    | nil => rfl
    | cons p _ => exact absurd (hp p List.mem_cons_self) (by simp)
  subst this; exact ⟨by simpa using hv, hl⟩

theorem subOK_spec (k : Kind) (subC : String → Option Cost) (hsub : subOK w k subC = true)
    (name : String) (sub : Arm) (d : ArmDecl)
    (hf : k.subarms.find? (·.tag == name) = some sub) (hd : sub.read = .ok d) :
    ∃ rc c c', refCost w k subC d.onRefusal = some rc ∧
      stepsCost w k (some rc) subC [] d.steps (some costZero) = some c ∧
      subC name = some c' ∧ CostLe c c' := by
  have hmem := List.mem_of_find?_eq_some hf
  have htag : sub.tag = name := by simpa using List.find?_some hf
  unfold subOK at hsub
  have := List.all_eq_true.mp hsub sub hmem
  rw [htag, hf] at this
  simp only [hd] at this
  split at this
  · rename_i rc hrc
    split at this
    · rename_i c c' h1 h2
      exact ⟨rc, c, c', hrc, h1, h2, of_decide_eq_true this⟩
    · cases this
  · cases this

theorem loop_arith (l p m nb : Int) (hm0 : 0 ≤ m) (hm : m ≤ nb) :
    max 0 (l + m * p) ≤ max 0 l + nb * max 0 p := by
  have h1 : m * p ≤ m * max 0 p := Int.mul_le_mul_of_nonneg_left (by omega) hm0
  have h2 : m * max 0 p ≤ nb * max 0 p := Int.mul_le_mul_of_nonneg_right hm (by omega)
  have h3 : 0 ≤ nb * max 0 p := Int.mul_nonneg (by omega) (by omega)
  generalize m * p = a at *
  generalize m * max 0 p = b at *
  generalize nb * max 0 p = c at *
  omega

theorem rep_le (x L per r : Cost) (m nb : Int) (hm0 : 0 ≤ m) (hm : m ≤ nb)
    (h : CostLe x (costAdd (cpos (L.1 + m * per.1, L.2.1 + m * per.2.1, L.2.2 + m * per.2.2)) r)) :
    CostLe x (costAdd (cpos L) (costAdd (costScale nb (cpos per)) r)) := by
  have a1 := loop_arith L.1 per.1 m nb hm0 hm
  have a2 := loop_arith L.2.1 per.2.1 m nb hm0 hm
  have a3 := loop_arith L.2.2 per.2.2 m nb hm0 hm
  unfold CostLe costAdd cpos costScale at *
  obtain ⟨h1, h2, h3⟩ := h
  simp only at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

set_option hygiene false in
/-- The common tail of a `:do`, after its call: the answer routing (used by the cost proof). -/
local macro "do_tail_cost" : tactic => `(tactic| (
  split at hrun
  · exact viaRest _ hok2 hl2 hrun
  · split at hrun
    · obtain ⟨code, _, hrun⟩ := bind_ok hrun
      repeat' split at hrun
      all_goals first
        | exact viaRest _ hok2 hl2 hrun
        | (rename_i hfind; exact viaCase _ hok2 hl2 _ _ (List.mem_of_find?_eq_some hfind) hrun)
        | exact viaRef _ hl2 _ (Or.inr ⟨_, rfl⟩) hrun
        | (rcases faultRoute_cases _ op.faults code f.refusal with he | he <;> rw [he] at hrun
           · exact viaRef _ hl2 _ (Or.inl rfl) hrun
           · exact viaRef _ hl2 _ (Or.inr ⟨_, rfl⟩) hrun)
    · obtain ⟨_, hth, _⟩ := bind_ok hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hth))

/-- **Soundness of the charge bound over the interpreter (`run_charge_le`)**: a path `xs`, run with
whatever `X` follows it, charges at most the frame's loop work so far (its positive part) plus
`stepsCost` of `xs`, whose continuation bound `kont` bounds `X`. -/
theorem run_charge_le (k : Kind) (subC : String → Option Cost) (hsub : subOK w k subC = true) :
    ∀ (fuel : Nat) (f : Frame) (st : St) (xs X : List Step) (senv : SEnv) (rc kont C : Cost)
      (v : Val),
      f.kind = k → f.observe = false → refCost w k subC f.refusal = some rc →
      run w f fuel st (xs ++ X) = .ok (.done v) →
      EnvOK senv st.vars →
      stepsCost w k (some rc) subC senv xs (some kont) = some C →
      (∀ fuel', fuel' ≤ fuel → ∀ st' v', run w f fuel' st' X = .ok (.done v') →
        CostLe (extractCharge v') (costAdd (cpos st'.loopWork) kont)) →
      CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
  intro f st xs X senv rc kont C v hk hobs hrc hrun hok hC hX
  cases fuel with
  | zero => cases xs <;> cases X <;> simp [run] at hrun
  | succ n =>
  obtain ⟨eE, heE, hbase, hRc⟩ := refCost_spec w k subC f.refusal rc hrc
  -- a branch run at `n`: no continuation
  have branch : ∀ (st' : St) (ss : List Step) (senv' : SEnv) (cb : Cost) (v' : Val),
      run w f n st' ss = .ok (.done v') → EnvOK senv' st'.vars →
      stepsCost w k (some rc) subC senv' ss (some costZero) = some cb →
      CostLe (extractCharge v') (costAdd (cpos st'.loopWork) cb) := by
    intro st' ss senv' cb v' h1 h2 h3
    exact ih n (Nat.lt_succ_self n) f st' ss [] senv' rc costZero cb v' hk hobs hrc
      (by simpa using h1) h2 h3 (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
  -- the refusal, from any state, at any fuel up to `n`
  have hR : ∀ m, m ≤ n → ∀ (st' : St) (v' : Val), run w f m st' f.refusal = .ok (.done v') →
      CostLe (extractCharge v') (costAdd (cpos st'.loopWork) rc) := by
    intro m hm st' v' h1
    by_cases hne : f.refusal = []
    · rw [hne] at h1; exact absurd h1 (run_nil_ne w _ _ _ _)
    obtain ⟨c1, hc1, hle⟩ := hRc hne
    exact le_addL st'.loopWork
      (ih m (Nat.lt_succ_of_le hm) f st' f.refusal [] [] rc costZero c1 v' hk hobs hrc
        (by simpa using h1) (envOK_nil _) hc1 (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _)))
      hle
  -- a single stop with no steps expression
  have hStop : ∀ (st' : St) (r : String) (v' : Val),
      run w f n st' [.stop r none] = .ok (.done v') →
      CostLe (extractCharge v') (costAdd (cpos st'.loopWork) rc) := by
    intro st' r v' h1
    cases n with
    | zero => simp [run] at h1
    | succ m =>
      exact le_addL st'.loopWork
        (run_stop_le w f hobs k hk m st' r none [] v' [] eE (envOK_nil _) h1 (by simp [hiOpt, heE]))
        hbase
  -- the rest of the path, with its continuation, at `n`
  have cont : ∀ (st' : St) (rest : List Step) (senv' : SEnv) (cr : Cost) (v' : Val),
      run w f n st' (rest ++ X) = .ok (.done v') → EnvOK senv' st'.vars →
      stepsCost w k (some rc) subC senv' rest (some kont) = some cr →
      CostLe (extractCharge v') (costAdd (cpos st'.loopWork) cr) := by
    intro st' rest senv' cr v' h1 h2 h3
    exact ih n (Nat.lt_succ_self n) f st' rest X senv' rc kont cr v' hk hobs hrc h1 h2 h3
      (fun m hm => hX m (Nat.le_succ_of_le hm))
  cases xs with
  | nil =>
    simp only [stepsCost] at hC; cases hC
    exact hX (n + 1) (Nat.le_refl _) st v (by simpa using hrun)
  | cons s rest =>
  rw [List.cons_append] at hrun
  simp only [stepsCost] at hC
  obtain ⟨c, hc, hC⟩ := obind hC
  obtain ⟨r, hr, hC⟩ := obind hC
  have hC2 : combine s c r = C := Option.some.inj hC
  clear hC
  subst hk
  cases s with
  | let_ x e =>
    simp only [run] at hrun
    obtain ⟨xv, hxv, hrun⟩ := bind_ok hrun
    have hok' : EnvOK (stepEnv w f.kind senv (.let_ x e)) (({ st with vars := (x, xv) :: st.vars } : St).vars) :=
      envOK_let senv st.vars x xv _ hok (fun bb hbb => ev_sound w f.kind senv st e xv bb hok hxv hbb)
    exact le_addL st.loopWork (cont { st with vars := (x, xv) :: st.vars } rest _ r v hrun hok' hr) (by rw [← hC2]; exact costLe_max_right _ _)
  | set pairs =>
    simp only [run] at hrun
    obtain ⟨st', hst', hrun⟩ := bind_ok hrun
    obtain ⟨hv, hl⟩ := pend_shape hst'
    have := cont st' rest senv r v hrun (by rw [hv]; exact hok) hr
    rw [hl] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_right _ _)
  | next ph =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · obtain ⟨_, _, hrun⟩ := bind_ok hrun
      exact le_addL st.loopWork (cont { st with next := some ph } rest senv r v hrun hok hr) (by rw [← hC2]; exact costLe_max_right _ _)
  | wakeRow e =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    have h1 := cont _ rest senv r v hrun (by exact hok) hr
    exact le_addL st.loopWork h1 (by rw [← hC2]; exact costLe_max_right _ _)
  | if_ cnd a b =>
    simp only [run] at hrun
    obtain ⟨cv, _, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨ca, hca, hc⟩ := obind hc
    obtain ⟨cb, hcb, hc⟩ := obind hc
    simp only [pure, Option.some.injEq] at hc; subst hc
    have hcC' : CostLe (costMax ca cb) C := by rw [← hC2]; exact costLe_max_left _ _
    split at hrun
    · exact le_addL st.loopWork (branch st a senv ca v hrun hok hca)
        (costLe_trans (costLe_max_left _ _) hcC')
    · exact le_addL st.loopWork (branch st b senv cb v hrun hok hcb)
        (costLe_trans (costLe_max_right _ _) hcC')
  | cond clauses =>
    simp only [run] at hrun
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    rcases o with _ | ⟨e, ss⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · have hmem := findM_mem _ _ _ ho
      obtain ⟨cs, hcs, hle⟩ := clausesCost_mem w f.kind _ _ _ _ _ _ _ hmem hc
      exact le_addL st.loopWork (branch st ss senv cs v hrun hok hcs)
        (costLe_trans hle ((by rw [← hC2]; exact costLe_max_left _ _)))
  | case_ key arms =>
    simp only [run] at hrun
    obtain ⟨kv, _, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    split at hrun
    · rename_i cs ss hfind
      have hmem := List.mem_of_find?_eq_some hfind
      obtain ⟨cb, hcb, hle⟩ := casesCost_mem w f.kind _ _ _ _ _ _ _ hmem hc
      exact le_addL st.loopWork (branch st ss senv cb v hrun hok hcb)
        (costLe_trans hle ((by rw [← hC2]; exact costLe_max_left _ _)))
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | stop reason se =>
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hx; cases hz
    exact le_addL st.loopWork (run_stop_le w f hobs f.kind rfl n st reason se (rest ++ X) v senv y hok
      hrun hy) ((by rw [← hC2]; exact costLe_max_left _ _))
  | charge b sE d rE =>
    simp only [run] at hrun
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 hst1
    have hok1 : EnvOK senv st1.vars := hv1 ▸ hok
    obtain ⟨bv, hbv, hrun⟩ := bind_ok hrun
    obtain ⟨sv, hsv, hrun⟩ := bind_ok hrun
    obtain ⟨dv, hdv, hrun⟩ := bind_ok hrun
    obtain ⟨rv, _, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    have h0 : ∀ q, some (0 : Int) = some q → (Val.int 0).toInt ≤ q := by
      intro q hq; cases hq; exact Int.le_refl _
    have := charge_le f st1 bv sv dv rv v x y z hrun
      (hiOpt_sound w f.kind senv st1 b _ bv _ x hok1 hbv hx h0)
      (hiOpt_sound w f.kind senv st1 sE _ sv _ y hok1 hsv hy h0)
      (hiOpt_sound w f.kind senv st1 d _ dv _ z hok1 hdv hz h0)
    rw [hl1] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
  | idle =>
    simp only [run] at hrun
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    obtain ⟨_, hl1⟩ := flush_shape w f st st1 hst1
    obtain ⟨ev, hev, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hx; cases hz
    rw [const_hi w _ ev hev] at hy; cases hy
    have := charge_le f st1 _ _ _ _ v 0 ev.toInt 0 hrun (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    rw [hl1] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
  | yield =>
    simp only [run] at hrun
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    obtain ⟨_, hl1⟩ := flush_shape w f st st1 hst1
    obtain ⟨ev, hev, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hx; cases hz
    rw [const_hi w _ ev hev] at hy; cases hy
    have := charge_le f st1 _ _ _ _ v 0 ev.toInt 0 hrun (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    rw [hl1] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
  | wait b sE =>
    simp only [run] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st0, hst0, hrun⟩ := bind_ok hrun
    obtain ⟨hv0, hl0⟩ := pend_shape hst0
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    obtain ⟨hv1, hl1⟩ := flush_shape w f st0 st1 hst1
    have hok1 : EnvOK senv st1.vars := by rw [hv1, hv0]; exact hok
    obtain ⟨bv, hbv, hrun⟩ := bind_ok hrun
    obtain ⟨mv, hmv, hrun⟩ := bind_ok hrun
    obtain ⟨sv, hsv, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hz
    have h0 : ∀ q, some (0 : Int) = some q → (Val.int 0).toInt ≤ q := by
      intro q hq; cases hq; exact Int.le_refl _
    have hm : ∀ q, constHi w "*FN2-WORK-MAILBOX*" = some q → mv.toInt ≤ q := by
      intro q hq; rw [const_hi w _ mv hmv] at hq; cases hq; exact Int.le_refl _
    have := charge_le f st1 bv sv _ _ v x y 1 hrun
      (hiOpt_sound w f.kind senv st1 b _ bv _ x hok1 hbv hx h0)
      (hiOpt_sound w f.kind senv st1 sE _ sv _ y hok1 hsv hy hm) (Int.le_refl _)
    rw [hl1, hl0] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
  | halt =>
    simp only [run] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st0, hst0, hrun⟩ := bind_ok hrun
    obtain ⟨_, hl0⟩ := pend_shape hst0
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    obtain ⟨_, hl1⟩ := flush_shape w f st0 st1 hst1
    obtain ⟨mv, hmv, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hx; cases hz
    rw [const_hi w _ mv hmv] at hy; cases hy
    have := charge_le f st1 _ _ _ _ v 0 mv.toInt 0 hrun (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    rw [hl1, hl0] at this
    exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
  | wake => simp [stepCost] at hc
  | nowake => simp [stepCost] at hc
  | repeatNext => simp [stepCost] at hc
  | goto name =>
    simp only [run] at hrun
    obtain ⟨st1, hst1, hrun⟩ := bind_ok hrun
    split at hrun
    · rename_i sub hfind
      obtain ⟨y, hy, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hy; subst hy
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨reads, _, hrun⟩ := bind_ok hrun
      obtain ⟨d, hd, hrun⟩ := bind_ok hrun
      obtain ⟨rc', c1, c', hrc', hc1, hc', hle⟩ := subOK_spec w f.kind subC hsub name sub d hfind hd
      simp only [stepCost] at hc
      rw [hc'] at hc; cases hc
      have := ih n (Nat.lt_succ_self n) { f with refusal := d.onRefusal } _ d.steps [] [] rc' costZero
        c1 v rfl hobs hrc' (by simpa using hrun) (envOK_nil _) hc1
        (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
      have h2 : CostLe (extractCharge v) c1 := by
        unfold CostLe costAdd cpos at this; unfold CostLe; simpa using this
      exact le_addL st.loopWork (cpos_nonneg_le c1 st.loopWork h2)
        (costLe_trans hle (by rw [← hC2]; exact costLe_max_left _ _))
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | park wt arg pk sE keys =>
    simp only [run] at hrun
    obtain ⟨mb, hmb, hrun⟩ := bind_ok hrun
    simp only [stepCost] at hc
    obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := termC_some hc
    cases hx; cases hz
    have fin : ∀ (st' : St) (sv : Val), st'.vars = st.vars → st'.loopWork = st.loopWork →
        evOpt w f.kind st' sE mb = .ok sv →
        chargeResult f st' (.int 0) sv (.int 0) Val.nil = .ok (.done v) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro st' sv hv hl hsv hch
      have hm : ∀ q, constHi w "*FN2-WORK-MAILBOX*" = some q → mb.toInt ≤ q := by
        intro q hq; rw [const_hi w _ mb hmb] at hq; cases hq; exact Int.le_refl _
      have := charge_le f st' _ sv _ _ v 0 y 0 hch (Int.le_refl _)
        (hiOpt_sound w f.kind senv st' sE mb sv _ y (hv ▸ hok) hsv hy hm) (Int.le_refl _)
      rw [hl] at this
      exact le_addL st.loopWork this (by rw [← hC2]; exact costLe_max_left _ _)
    have via : ∀ (o : Op × Val) (st1 st2 : St) (sv : Val), flush w f st = .ok st1 →
        bindOuts st1 o.1.stobjsOut [] o.2 = .ok st2 →
        evOpt w f.kind st2 sE mb = .ok sv →
        chargeResult f st2 (.int 0) sv (.int 0) Val.nil = .ok (.done v) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro o st1 st2 sv h1 h2 h3 h4
      obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 h1
      obtain ⟨hv2, hl2⟩ := bindOuts_nil_vars st1 st2 _ _ h2
      exact fin st2 sv (hv2.trans hv1) (hl2.trans hl1) h3 h4
    split at hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, _, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
      exact via o st1 st2 sv h1 h2 h3 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, _, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
      exact via o st1 st2 sv h1 h2 h3 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, _, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
      exact via o st1 st2 sv h1 h2 h3 hrun
    · split at hrun
      · obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        obtain ⟨hv0, hl0⟩ := pend_shape h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        obtain ⟨hv1, hl1⟩ := flush_shape w f st0 st1 h1
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
        exact fin _ sv (by simp only [setStobj]; exact hv1.trans hv0)
          (by simp only [setStobj]; exact hl1.trans hl0) h3 hrun
      · obtain ⟨_, h, _⟩ := bind_ok hrun
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at hrun
      · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        obtain ⟨o, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
        exact via o st1 st2 sv h1 h2 h3 hrun
      · obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        obtain ⟨hv0, hl0⟩ := pend_shape h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        obtain ⟨hv1, hl1⟩ := flush_shape w f st0 st1 h1
        obtain ⟨sv, h3, hrun⟩ := bind_ok hrun
        exact fin _ sv (hv1.trans hv0) (hl1.trans hl0) h3 hrun
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | do_ vars cl acceptGiven accept when_ else_ cases =>
    simp only [stepCost] at hc
    obtain ⟨cc, hcc, hc⟩ := obind hc
    obtain ⟨rc', hrc', hc⟩ := obind hc
    cases hrc'
    replace hc := (Option.some.inj hc).symm
    have hcC : CostLe (costMax cc rc) C := by rw [← hc, ← hC2]; exact costLe_max_left _ _
    have hrC : CostLe r C := by rw [← hC2]; exact costLe_max_right _ _
    have toC : ∀ (st2 : St) x, st2.loopWork = st.loopWork → CostLe x (costMax cc rc) →
        CostLe (extractCharge v) (costAdd (cpos st2.loopWork) x) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro st2 x hl2 hx hv; rw [hl2] at hv; exact le_addL _ hv (costLe_trans hx hcC)
    have viaRest : ∀ st2 : St, EnvOK (kill vars senv) st2.vars → st2.loopWork = st.loopWork →
        run w f n st2 (rest ++ X) = .ok (.done v) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro st2 hok2 hl2 hrr
      have := cont st2 rest (kill vars senv) r v hrr hok2 hr
      rw [hl2] at this; exact le_addL _ this hrC
    have viaCase : ∀ st2 : St, EnvOK (kill vars senv) st2.vars → st2.loopWork = st.loopWork →
        ∀ opt ss, (opt, ss) ∈ cases → run w f n st2 ss = .ok (.done v) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro st2 hok2 hl2 opt ss hmem hrr
      obtain ⟨cb, hcb, hle⟩ := casesCost_mem w f.kind _ _ _ _ _ _ _ hmem hcc
      exact toC st2 cb hl2 (costLe_trans hle (costLe_max_left _ _)) (branch st2 ss _ cb v hrr hok2 hcb)
    have viaRef : ∀ st2 : St, st2.loopWork = st.loopWork → ∀ ss,
        (ss = f.refusal ∨ ∃ rs, ss = [.stop rs none]) →
        run w f n st2 ss = .ok (.done v) →
        CostLe (extractCharge v) (costAdd (cpos st.loopWork) C) := by
      intro st2 hl2 ss hss hrr
      rcases hss with rfl | ⟨rs, rfl⟩
      · exact toC st2 rc hl2 (costLe_max_right _ _) (hR n (Nat.le_refl _) st2 v hrr)
      · exact toC st2 rc hl2 (costLe_max_right _ _) (hStop st2 rs v hrr)
    rw [run] at hrun
    dsimp only at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 h1
    obtain ⟨op, _, hrun⟩ := bind_ok hrun
    rcases when_ with _ | e
    · dsimp only at hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      rw [if_neg (by decide)] at hrun
      obtain ⟨o, _, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨hl2', pre, hv2, hpre⟩ := bindOuts_shape st1 st2 _ _ _ h2
      have hok2 : EnvOK (kill vars senv) st2.vars := by
        rw [hv2]; exact envOK_kill vars senv pre _ (hv1 ▸ hok) hpre
      have hl2 : st2.loopWork = st.loopWork := hl2'.trans hl1
      do_tail_cost
    · dsimp only at hrun
      obtain ⟨wv, _, hrun⟩ := bind_ok hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      split at hrun
      · obtain ⟨vs, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        simp only [pure, Except.pure, Except.ok.injEq] at h2; subst h2
        have hok2 : EnvOK (kill vars senv) ({ st1 with vars := vars.zip vs ++ st1.vars } : St).vars :=
          envOK_kill vars senv _ _ (hv1 ▸ hok) (fun p hp => (List.of_mem_zip hp).1)
        have hl2 : ({ st1 with vars := vars.zip vs ++ st1.vars } : St).loopWork = st.loopWork := hl1
        do_tail_cost
      · obtain ⟨o, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨hl2', pre, hv2, hpre⟩ := bindOuts_shape st1 st2 _ _ _ h2
        have hok2 : EnvOK (kill vars senv) st2.vars := by
          rw [hv2]; exact envOK_kill vars senv pre _ (hv1 ▸ hok) hpre
        have hl2 : st2.loopWork = st.loopWork := hl2'.trans hl1
        do_tail_cost
  | issue cl ok refused =>
    simp only [stepCost] at hc
    obtain ⟨cOk, hcOk, hc⟩ := obind hc
    obtain ⟨mb, hmb, hc⟩ := obind hc
    obtain ⟨rc', hrc', hc⟩ := obind hc
    cases hrc'
    obtain ⟨cEx, hcEx, hc⟩ := obind hc
    obtain ⟨cRef, hcRef, hc⟩ := obind hc
    replace hc := (Option.some.inj hc).symm
    have hcC : CostLe c C := by rw [← hC2]; exact costLe_max_left _ _
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 h1
    obtain ⟨⟨op, rr⟩, _, hrun⟩ := bind_ok hrun
    obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
    obtain ⟨hl2', pre, hv2, hpre⟩ := bindOuts_shape st1 st2 _ _ _ h2
    have hok2 : EnvOK (kill issueVars senv) st2.vars := by
      rw [hv2]; exact envOK_kill issueVars senv pre _ (hv1 ▸ hok) hpre
    have hl2 : st2.loopWork = st.loopWork := hl2'.trans hl1
    obtain ⟨code, _, hrun⟩ := bind_ok hrun
    -- a single terminal whose bound is `(0, *FN2-WORK-MAILBOX*, 0)`
    have hOne : ∀ (t : Step), stepsCost w f.kind (some rc) subC [] [t] (some costZero) =
          some (costMax (0, mb, 0) costZero) →
        ∀ m, m ≤ n → ∀ (st' : St) (v' : Val), run w f m st' [t] = .ok (.done v') →
        CostLe (extractCharge v') (costAdd (cpos st'.loopWork) (costMax (0, mb, 0) costZero)) := by
      intro t ht m hm st' v' h
      exact ih m (Nat.lt_succ_of_le hm) f st' [t] [] [] rc costZero _ v' rfl hobs hrc
        (by simpa using h) (envOK_nil _) ht (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
    have hpark : stepsCost w f.kind (some rc) subC [] [.park "OPERATION" none none none]
        (some costZero) = some (costMax (0, mb, 0) costZero) := by
      simp [stepsCost, stepCost, termC, hiOpt, hmb, combine, bind, pure]
    have hhalt : stepsCost w f.kind (some rc) subC [] [.halt] (some costZero) =
        some (costMax (0, mb, 0) costZero) := by
      simp [stepsCost, stepCost, termC, hmb, combine, bind, pure]
    split at hrun
    · rw [hc] at hcC
      exact le_addL _ (hl2 ▸ branch st2 ok _ cOk v hrun hok2 hcOk)
        (costLe_trans (costLe_max_left _ _) hcC)
    split at hrun
    · rw [hc] at hcC
      have := ih n (Nat.lt_succ_self n) f st2 refused [.park "OPERATION" none none none]
        (kill issueVars senv) rc _ cEx v rfl hobs hrc hrun hok2 hcEx (hOne _ hpark)
      exact le_addL _ (hl2 ▸ this)
        (costLe_trans (costLe_trans (costLe_max_left _ _) (costLe_max_right _ _)) hcC)
    · rw [hc] at hcC
      have hXr : ∀ fuel', fuel' ≤ n → ∀ (st' : St) (v' : Val),
          run w f fuel' st' (if f.refusal.isEmpty = true then [Step.halt] else f.refusal) =
            .ok (.done v') →
          CostLe (extractCharge v')
            (costAdd (cpos st'.loopWork) (costMax (costMax (0, mb, 0) costZero) rc)) := by
        intro m hm st' v' h
        split at h
        · exact le_addL _ (hOne _ hhalt m hm st' v' h) (costLe_max_left _ _)
        · exact le_addL _ (hR m hm st' v' h) (costLe_max_right _ _)
      have := ih n (Nat.lt_succ_self n) f st2 refused _ (kill issueVars senv) rc _ cRef v rfl hobs
        hrc hrun hok2 hcRef hXr
      exact le_addL _ (hl2 ▸ this)
        (costLe_trans (costLe_trans (costLe_max_right _ _) (costLe_max_right _ _)) hcC)
  | repeat_ nE body until_ =>
    simp only [stepCost] at hc
    obtain ⟨b, hb, hc⟩ := obind hc
    obtain ⟨per', hper', hc⟩ := obind hc
    replace hc := (Option.some.inj hc).symm
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hv1, hl1⟩ := flush_shape w f st st1 h1
    obtain ⟨nv, hnv, hrun⟩ := bind_ok hrun
    obtain ⟨lp, _, hrun⟩ := bind_ok hrun
    obtain ⟨per, hper, hrun⟩ := bind_ok hrun
    have hp : passBound w body = some per := passBound_eq w _ _ _ hper
    have hpp : per' = per := (Option.some.inj (hp ▸ hper')).symm
    subst hpp
    have hin := ev_sound w f.kind senv st1 nE nv b (hv1 ▸ hok) hnv hb
    have hk : ((nv.nfix : Nat) : Int) ≤ max 0 b.2 := by
      unfold Val.nfix; have := hin.2; omega
    have hm0 : (0 : Int) ≤ ((nv.nfix - lp.2 : Nat) : Int) := by omega
    have hm : ((nv.nfix - lp.2 : Nat) : Int) ≤ max 0 b.2 := by omega
    have := cont _ rest senv r v hrun (by exact hv1 ▸ hok) hr
    have h2 := rep_le (extractCharge v) st1.loopWork per' r _ _ hm0 hm this
    rw [hl1] at h2
    rw [← hC2, hc]
    exact h2

/-- **Theorem (`runArm_charge_le_cost`)**: when a run arm's declaration has a derived charge
bound `C`, every successful run of the interpreter on that arm, on any arguments and at any fuel,
returns a charge (its first three results) at most `C` in each dimension. No hypothesis is about
the run: `derivedCost w k a = some C` is computed from the declaration alone. -/
theorem runArm_charge_le_cost (k : Kind) (a : Arm) (args : List Val) (fuel : Nat) (v : Val)
    (C : Cost) (hC : derivedCost w k a = some C)
    (hrun : runArm w k a false args fuel = .ok v) :
    CostLe (extractCharge v) C := by
  unfold derivedCost at hC
  split at hC
  · rename_i decl hread
    dsimp only at hC
    split at hC
    · rename_i hsub
      obtain ⟨rc, hrc, hC⟩ := obind hC
      simp only [runArm, Bool.false_eq_true, if_false] at hrun
      split at hrun
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
      split at hrun
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨reads, _, hrun⟩ := bind_ok hrun
      obtain ⟨d, hd, hrun⟩ := bind_ok hrun
      rw [hread] at hd; cases hd
      obtain ⟨res, hres, hrun⟩ := bind_ok hrun
      cases res with
      | again _ => simp [throw, throwThe, MonadExceptOf.throw] at hrun
      | done v' =>
        simp only [pure, Except.pure, Except.ok.injEq] at hrun; subst hrun
        have := run_charge_le w k _ hsub fuel _ _ decl.steps [] [] rc costZero C v' rfl rfl hrc
          (by simpa using hres) (envOK_nil _) hC (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
        unfold CostLe costAdd cpos at this; unfold CostLe; simpa using this
    · cases hC
  · cases hC

end Fn2.Arms.Cost
