import Fn2.Arms
import Fn2.ArmsLemmas
import Fn2.Arms.Cost
import Fn2.Arms.Frame

/-!
# Fn2.Arms.Inv: an invariant of the children, carried over the interpreter

`run_inv` is the one strong induction over `Fn2.Arms.run` that the column and phase contracts
share. A contract names what a path may do (`Prims`: which pending fields, which phase forms,
which operations, whether it may rewrite the directory outside the checked write); `admSteps`
checks a declaration against it syntactically, every branch; `Sem` says what each primitive does
to a predicate `Good` of the children (the flush, a call, the control, the directory). Then every
result of a run whose steps, refusal and sub-arms are admissible returns children satisfying
`Good`, when it started from children satisfying `Good`.
-/

namespace Fn2.Arms.Inv
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Bound Fn2.Arms.Cost Fn2.Arms.Frame

set_option autoImplicit false

/-- What a contract lets a path do. -/
structure Prims where
  /-- a field the path may leave pending for the checked write -/
  pairOK : String → Bool
  /-- a phase form the path may declare -/
  nextOK : Expr → Bool
  /-- an operation the path may call (its `stobjs-out` replace children) -/
  opOK : String → Bool
  /-- the path may rewrite the directory outside the checked write (`:wake-row`, `(:park :pool)`) -/
  dirOK : Bool
  /-- a sub-arm the path may enter (`:goto`) -/
  gotoOK : String → Bool

section
variable (w : World) (P : Prims)

def admPark (wait : String) (pk : Option String) : Bool :=
  match wait with
  | "OPERATION" => P.opOK "FN2-MACHINE-PARK"
  | "ADMISSION" => P.opOK "FN2-MACHINE-PARK-ADMISSION"
  | "TAKEN" => P.opOK ("FN2-MACHINE-PARK-TAKEN-" ++ pk.getD "")
  | "POOL" => P.pairOK "CURSOR" && P.dirOK
  | other =>
    match w.waits.find? (·.kind == other) with
    | some ⟨_, some parker⟩ => P.opOK parker
    | some ⟨_, none⟩ => P.pairOK "WAIT-REASON"
    | none => true

mutual
/-- A step within the contract (sub-arms are checked once, by `admSubs`). -/
def admStep : Step → Bool
  | .let_ _ _ | .charge _ _ _ _ | .idle | .yield | .wake | .nowake | .repeatNext | .stop _ _ => true
  | .goto name => P.gotoOK name
  | .set pairs => pairs.all (P.pairOK ·.1)
  | .next ph => P.nextOK ph
  | .wakeRow _ => P.dirOK
  | .repeat_ _ body _ => admSteps body
  | .do_ _ c _ _ _ _ cases => P.opOK c.op && admCases cases
  | .issue c ok refused => P.opOK c.op && admSteps ok && admSteps refused &&
      P.opOK "FN2-MACHINE-PARK" && P.pairOK "STOPPED" && P.pairOK "WAIT-REASON"
  | .if_ _ a b => admSteps a && admSteps b
  | .cond clauses => admClauses clauses
  | .case_ _ arms => admCases arms
  | .wait _ _ => P.pairOK "PENDING" && P.pairOK "WAIT-REASON"
  | .halt => P.pairOK "STOPPED" && P.pairOK "WAIT-REASON"
  | .park wt _ pk _ _ => admPark w P wt pk

def admSteps : List Step → Bool
  | [] => true
  | s :: ss => admStep s && admSteps ss

def admCases : List (Option (List Val) × List Step) → Bool
  | [] => true
  | (_, ss) :: cs => admSteps ss && admCases cs

def admClauses : List (Expr × List Step) → Bool
  | [] => true
  | (_, ss) :: cs => admSteps ss && admClauses cs
end

mutual
/-- The sub-arms a step can enter directly. -/
def gotosStep : Step → List String
  | .goto name => [name]
  | .repeat_ _ body _ => gotosSteps body
  | .do_ _ _ _ _ _ _ cases => gotosCases cases
  | .issue _ ok refused => gotosSteps ok ++ gotosSteps refused
  | .if_ _ a b => gotosSteps a ++ gotosSteps b
  | .cond clauses => gotosClauses clauses
  | .case_ _ arms => gotosCases arms
  | _ => []

def gotosSteps : List Step → List String
  | [] => []
  | s :: ss => gotosStep s ++ gotosSteps ss

def gotosCases : List (Option (List Val) × List Step) → List String
  | [] => []
  | (_, ss) :: cs => gotosSteps ss ++ gotosCases cs

def gotosClauses : List (Expr × List Step) → List String
  | [] => []
  | (_, ss) :: cs => gotosSteps ss ++ gotosClauses cs
end

/-- The sub-arms reachable from `start` through `:goto`, `n` rounds deep. -/
def reachSubs (k : Kind) (start : List String) : Nat → List String
  | 0 => start
  | n + 1 =>
    let R := reachSubs k start n
    (R ++ (k.subarms.filter (R.contains ·.tag)).flatMap fun s => match s.read with
      | .ok d => gotosSteps d.steps ++ gotosSteps d.onRefusal
      | .error _ => []).eraseDups

/-- The sub-arms an arm can enter (a candidate the admissibility check confirms: a `:goto`
outside it is refused by `gotoOK`). -/
def armReach (k : Kind) (a : Arm) : List String :=
  match a.read with
  | .ok d => reachSubs k (gotosSteps d.steps ++ gotosSteps d.onRefusal) (k.subarms.length + 1)
  | .error _ => []

/-- Every sub-arm of `k` the contract lets a path enter (its steps and its refusal) is within it. -/
def admSubs (k : Kind) : Bool :=
  k.subarms.all fun s => !P.gotoOK s.tag || match s.read with
    | .ok d => admSteps w P d.steps && admSteps w P d.onRefusal
    | .error _ => true

/-- An arm's steps, its refusal and every sub-arm of its kind are within the contract. -/
def admArm (k : Kind) (a : Arm) : Bool :=
  match a.read with
  | .ok d => admSteps w P d.steps && admSteps w P d.onRefusal && admSubs w P k
  | .error _ => false

theorem admSteps_append (a b : List Step) :
    admSteps w P (a ++ b) = (admSteps w P a && admSteps w P b) := by
  induction a with
  | nil => simp [admSteps]
  | cons s a ih => simp [admSteps, ih, Bool.and_assoc]

theorem admCases_mem (cs : List (Option (List Val) × List Step)) (opt : Option (List Val))
    (ss : List Step) (hm : (opt, ss) ∈ cs) (h : admCases w P cs = true) : admSteps w P ss = true := by
  induction cs with
  | nil => simp at hm
  | cons c cs ih =>
    obtain ⟨o, s⟩ := c
    simp only [admCases, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with he | he
    · cases he; exact h.1
    · exact ih he h.2

theorem admClauses_mem (cs : List (Expr × List Step)) (e : Expr) (ss : List Step)
    (hm : (e, ss) ∈ cs) (h : admClauses w P cs = true) : admSteps w P ss = true := by
  induction cs with
  | nil => simp at hm
  | cons c cs ih =>
    obtain ⟨o, s⟩ := c
    simp only [admClauses, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with he | he
    · cases he; exact h.1
    · exact ih he h.2

theorem admPark_other (wt : String) (pk : Option String)
    (h1 : wt = "OPERATION" → False) (h2 : wt = "ADMISSION" → False) (h3 : wt = "TAKEN" → False)
    (h4 : wt = "POOL" → False) :
    admPark w P wt pk = match w.waits.find? (·.kind == wt) with
      | some ⟨_, some parker⟩ => P.opOK parker
      | some ⟨_, none⟩ => P.pairOK "WAIT-REASON"
      | none => true := by
  unfold admPark
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd rfl h4
  · rfl

/-! ## The semantic side -/

/-- The pending fields and the phase form are within the contract. -/
def PendOK (st : St) : Prop :=
  (∀ p ∈ st.pending, P.pairOK p.1 = true) ∧ (∀ ph, st.next = some ph → P.nextOK ph = true)

theorem pendOK_clean (st : St) (h1 : st.pending = []) (h2 : st.next = none) : PendOK P st :=
  ⟨by simp [h1], by simp [h2]⟩

/-- `Good` survives any change confined to the children `T`. -/
def Keeps (Good : (String → Except String Val) → Prop) (T : List String) : Prop :=
  ∀ st st' : St, (∀ nn, nn ∉ T → stobj st' nn = stobj st nn) → Good (stobj st) → Good (stobj st')

/-- What each primitive of the interpreter does to `Good`, within the contract. -/
structure Sem (k : Kind) (Good : (String → Except String Val) → Prop) : Prop where
  flush : ∀ (f : Frame) (st st' : St), f.kind = k → Arms.flush w f st = .ok st' → PendOK P st →
    Good (stobj st) → Good (stobj st')
  /-- a call of an operation the contract admits, bound, keeps `Good` (`call_of_keeps`: when
  `Good` survives any change to the call's `stobjs-out`) -/
  call : ∀ op, P.opOK op = true → ∀ (st st2 : St) (c : Call) (o : Op × Val) (vars : List String),
    c.op = op → callOp w k st c = .ok o → bindOuts st o.1.stobjsOut vars o.2 = .ok st2 →
    Good (stobj st) → Good (stobj st2)
  ctl : Keeps Good ["FN2-CONTROL"]
  dir : P.dirOK = true → Keeps Good ["FN2-MACHINES", "FN2-CONTROL"]

/-- A call keeps `Good` when `Good` survives any change confined to the call's `stobjs-out`. -/
theorem call_of_keeps (k : Kind) (Good : (String → Except String Val) → Prop) (op : String)
    (hk : Keeps Good (opTables w op)) :
    ∀ (st st2 : St) (c : Call) (o : Op × Val) (vars : List String),
      c.op = op → callOp w k st c = .ok o → bindOuts st o.1.stobjsOut vars o.2 = .ok st2 →
      Good (stobj st) → Good (stobj st2) := by
  intro st st2 c o vars hc h1 h2 hg
  obtain ⟨_, _, hf⟩ := call_frame w k st st2 c o vars h1 h2
  subst hc
  exact hk st st2 hf hg

/-- A result whose children satisfy `Good`. -/
def InvRes (Good : (String → Except String Val) → Prop) (f : Frame) : Res → Prop
  | .done v => ∃ stF, Outs f stF v ∧ Good (stobj stF)
  | .again st' => Good (stobj st')

theorem invRes_of_frame (Good : (String → Except String Val) → Prop) (f : Frame) (st : St)
    (r : Res) (h : FrameRes f [] st r) (hg : Good (stobj st)) : InvRes Good f r := by
  cases r with
  | done v =>
    obtain ⟨stF, ho, hf⟩ := h
    refine ⟨stF, ho, ?_⟩
    have : stobj stF = stobj st := funext fun n => hf n (by simp)
    rw [this]; exact hg
  | again st' =>
    have : stobj st' = stobj st := funext fun n => h n (by simp)
    show Good (stobj st')
    rw [this]; exact hg

theorem keeps_apply {Good : (String → Except String Val) → Prop} {T : List String}
    (hK : Keeps Good T) (st st' : St) (h : ∀ nn, nn ∉ T → stobj st' nn = stobj st nn)
    (hg : Good (stobj st)) : Good (stobj st') := hK st st' h hg

/-- Rewriting the directory and the control (`:wake-row`, `(:park :pool)`). -/
theorem good_dirctl (k : Kind) (Good : (String → Except String Val) → Prop) (hS : Sem w P k Good)
    (hd : P.dirOK = true) (st : St) (a b : Val) (hg : Good (stobj st)) :
    Good (stobj (setStobj (setStobj st "FN2-MACHINES" a) "FN2-CONTROL" b)) := by
  refine hS.dir hd st _ (fun nn hn => ?_) hg
  have h1 : "FN2-CONTROL" ≠ nn := fun e => hn (by simp [← e])
  have h2 : "FN2-MACHINES" ≠ nn := fun e => hn (by simp [← e])
  rw [stobj_setStobj_ne _ _ _ _ h1, stobj_setStobj_ne _ _ _ _ h2]

set_option hygiene false in
local macro "do_tail_inv" : tactic => `(tactic| (
  split at hrun
  · exact viaRest _ hP2 hG2 hrun
  · split at hrun
    · obtain ⟨code, _, hrun⟩ := bind_ok hrun
      repeat' split at hrun
      all_goals first
        | exact viaRest _ hP2 hG2 hrun
        | (rename_i hfind; exact viaCase _ hP2 hG2 _ _ (List.mem_of_find?_eq_some hfind) hrun)
        | exact viaRef _ hP2 hG2 _ (Or.inr ⟨_, rfl⟩) hrun
        | (rcases faultRoute_cases _ op.faults code f.refusal with he | he <;> rw [he] at hrun
           · exact viaRef _ hP2 hG2 _ (Or.inl rfl) hrun
           · exact viaRef _ hP2 hG2 _ (Or.inr ⟨_, rfl⟩) hrun)
    · obtain ⟨_, hth, _⟩ := bind_ok hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hth))

/-- A `:do`'s call: the operation `findOp` named, its results bound by its `stobjs-out`. -/
theorem callDo (k : Kind) (Good : (String → Except String Val) → Prop) (hS : Sem w P k Good)
    (cl : Call) (op : Op) (st1 st2 : St) (o : Op × Val) (vars : List String) {f : Frame}
    (hop : P.opOK cl.op = true) (hfo : w.ops.find? (·.name == cl.op) = some op) (hk : f.kind = k)
    (ho : callOp w f.kind st1 cl = .ok o) (h2 : bindOuts st1 op.stobjsOut vars o.2 = .ok st2)
    (hg1 : Good (stobj st1)) : Good (stobj st2) := by
  have he : o.1 = op := by
    have := callOp_op w f.kind st1 cl o ho
    rw [hfo] at this; cases this; rfl
  exact hS.call cl.op hop st1 st2 cl o vars rfl (hk ▸ ho) (he ▸ h2) hg1

/-- **The invariant over the interpreter (`run_inv`)**: a run of admissible steps, under an
admissible refusal and admissible sub-arms, from children satisfying `Good` and pending writes
within the contract, ends with children satisfying `Good`. -/
theorem run_inv (k : Kind) (Good : (String → Except String Val) → Prop) (hS : Sem w P k Good)
    (hsub : admSubs w P k = true) :
    ∀ (fuel : Nat) (f : Frame) (st : St) (ss : List Step) (r : Res),
      f.kind = k → admSteps w P f.refusal = true → admSteps w P ss = true →
      run w f fuel st ss = .ok r → PendOK P st → Good (stobj st) → InvRes Good f r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
  intro f st ss r hk hR hss hrun hP hG
  cases fuel with
  | zero => cases ss <;> simp [run] at hrun
  | succ n =>
  cases ss with
  | nil => simp [run] at hrun
  | cons s rest =>
  simp only [admSteps, Bool.and_eq_true] at hss
  obtain ⟨hs, hrest⟩ := hss
  have go : ∀ (st' : St) (ss' : List Step) (r' : Res), admSteps w P ss' = true →
      run w f n st' ss' = .ok r' → PendOK P st' → Good (stobj st') → InvRes Good f r' :=
    fun st' ss' r' h1 h2 h3 h4 => ih n (Nat.lt_succ_self n) f st' ss' r' hk hR h1 h2 h3 h4
  have hfl : ∀ st1 : St, flush w f st = .ok st1 → Good (stobj st1) ∧ PendOK P st1 := by
    intro st1 h1
    obtain ⟨c1, c2⟩ := flush_clean w f st st1 h1
    exact ⟨hS.flush f st st1 hk h1 hP hG, pendOK_clean P st1 c1 c2⟩
  have hflP : ∀ st0 st1 : St, flush w f st0 = .ok st1 → st0.stobjs = st.stobjs → PendOK P st0 →
      Good (stobj st1) := by
    intro st0 st1 h1 hs0 hP0
    have hg0 : Good (stobj st0) := by
      have : stobj st0 = stobj st := funext (stobj_of_stobjs st st0 hs0)
      rw [this]; exact hG
    exact hS.flush f st0 st1 hk h1 hP0 hg0
  subst hk
  cases s with
  | let_ x e =>
    simp only [run] at hrun
    obtain ⟨xv, _, hrun⟩ := bind_ok hrun
    exact go _ rest r hrest hrun hP hG
  | set pairs =>
    simp only [run] at hrun
    obtain ⟨st', hst', hrun⟩ := bind_ok hrun
    unfold pend at hst'
    split at hst'
    · simp at hst'
    simp only [Except.ok.injEq] at hst'; subst hst'
    simp only [admStep, List.all_eq_true] at hs
    refine go _ rest r hrest hrun ⟨fun p hp => ?_, hP.2⟩ hG
    rcases List.mem_append.mp hp with h | h
    · exact hP.1 p h
    · exact hs p h
  | next ph =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    simp only [admStep] at hs
    refine go _ rest r hrest hrun ⟨hP.1, fun p hp => ?_⟩ hG
    simp only [Option.some.injEq] at hp; subst hp; exact hs
  | wakeRow e =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨rv, _, hrun⟩ := bind_ok hrun
    simp only [admStep] at hs
    exact go _ rest r hrest hrun hP (good_dirctl w P f.kind Good hS hs st _ _ hG)
  | if_ cnd a b =>
    simp only [admStep, Bool.and_eq_true] at hs
    simp only [run] at hrun
    obtain ⟨cv, _, hrun⟩ := bind_ok hrun
    split at hrun
    · exact go st a r hs.1 hrun hP hG
    · exact go st b r hs.2 hrun hP hG
  | cond clauses =>
    simp only [admStep] at hs
    simp only [run] at hrun
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    rcases o with _ | ⟨e, ss⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · exact go st ss r (admClauses_mem w P clauses e ss (findM_mem _ _ _ ho) hs) hrun hP hG
  | case_ key arms =>
    simp only [admStep] at hs
    simp only [run] at hrun
    obtain ⟨kv, _, hrun⟩ := bind_ok hrun
    split at hrun
    · rename_i cs ss hfind
      exact go st ss r (admCases_mem w P arms cs ss (List.mem_of_find?_eq_some hfind) hs) hrun hP hG
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | stop reason se =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    have hg1 := (hfl st1 h1).1
    obtain ⟨c1, _, hrun⟩ := bind_ok hrun
    have hfin : ∀ c2, (∀ r', stopEnd w f (setStobj st1 "FN2-CONTROL" c2) se = .ok r' →
        InvRes Good f r') := by
      intro c2 r' he
      have hg2 : Good (stobj (setStobj st1 "FN2-CONTROL" c2)) := by
        refine hS.ctl st1 _ (fun nn hn => ?_) hg1
        exact stobj_setStobj_ne _ _ _ _ (fun e => hn (by simp [← e]))
      unfold stopEnd at he
      split at he
      · obtain ⟨nv, _, he⟩ := bind_ok he
        exact invRes_of_frame Good f _ r' (outs_wake f _ _ r' he) hg2
      · obtain ⟨e, _, he⟩ := bind_ok he
        obtain ⟨sv, _, he⟩ := bind_ok he
        exact invRes_of_frame Good f _ r' (outs_charge f _ _ _ _ _ r' he) hg2
    split at hrun <;>
    · obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨c2, _, hrun⟩ := bind_ok hrun
      exact hfin c2 r hrun
  | charge b sE d rE =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) (hfl st1 h1).1
  | idle =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) (hfl st1 h1).1
  | yield =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) (hfl st1 h1).1
  | wait b sE =>
    simp only [admStep, Bool.and_eq_true] at hs
    simp only [run] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
    unfold pend at h0
    split at h0
    · simp at h0
    simp only [Except.ok.injEq] at h0; subst h0
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    refine invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) (hflP _ st1 h1 rfl ⟨?_, hP.2⟩)
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hP.1 p h
    · simp at h; rcases h with h | h <;> simp [h, hs.1, hs.2]
  | halt =>
    simp only [admStep, Bool.and_eq_true] at hs
    simp only [run] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
    unfold pend at h0
    split at h0
    · simp at h0
    simp only [Except.ok.injEq] at h0; subst h0
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    refine invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) (hflP _ st1 h1 rfl ⟨?_, hP.2⟩)
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hP.1 p h
    · simp at h; rcases h with h | h <;> simp [h, hs.1, hs.2]
  | wake =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact invRes_of_frame Good f _ r (outs_wake f _ _ r hrun) (hfl st1 h1).1
  | nowake =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact invRes_of_frame Good f _ r (outs_wake f _ _ r hrun) (hfl st1 h1).1
  | repeatNext =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun; subst hrun
    exact (hfl st1 h1).1
  | goto name =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    have hg1 := (hfl st1 h1).1
    split at hrun
    · rename_i sub hfind
      obtain ⟨y, hy, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hy; subst hy
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨reads, _, hrun⟩ := bind_ok hrun
      obtain ⟨d, hd, hrun⟩ := bind_ok hrun
      have hmem := List.mem_of_find?_eq_some hfind
      have htag : sub.tag = name := by simpa using List.find?_some hfind
      simp only [admStep] at hs
      have hall := List.all_eq_true.mp hsub sub hmem
      rw [htag, hs, hd] at hall
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hall
      have := ih n (Nat.lt_succ_self n) { f with refusal := d.onRefusal } _ d.steps r rfl hall.2
        hall.1 hrun (pendOK_clean P _ rfl rfl) hg1
      cases r with
      | done v => obtain ⟨stF, ho, hf⟩ := this; exact ⟨stF, ho, hf⟩
      | again st' => exact this
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | park wt arg pk sE keys =>
    simp only [run] at hrun
    obtain ⟨mb, _, hrun⟩ := bind_ok hrun
    simp only [admStep] at hs
    have via : ∀ (c : Call) (o : Op × Val) (st1 st2 : St) (sv : Val),
        P.opOK c.op = true → flush w f st = .ok st1 → callOp w f.kind st1 c = .ok o →
        bindOuts st1 o.1.stobjsOut [] o.2 = .ok st2 →
        chargeResult f st2 (.int 0) sv (.int 0) Val.nil = .ok r → InvRes Good f r := by
      intro c o st1 st2 sv hok h1 h2 h3 h4
      exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r h4)
        (hS.call c.op hok st1 st2 c o [] rfl h2 h3 (hfl st1 h1).1)
    split at hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (by simpa [admPark] using hs) h1 ho h2 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (by simpa [admPark] using hs) h1 ho h2 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (by simpa [admPark] using hs) h1 ho h2 hrun
    · split at hrun
      · simp only [admPark, Bool.and_eq_true] at hs
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        unfold pend at h0
        split at h0
        · simp at h0
        simp only [Except.ok.injEq] at h0; subst h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        have hg1 := hflP _ st1 h1 rfl ⟨fun p hp => by
          rcases List.mem_append.mp hp with h | h
          · exact hP.1 p h
          · simp at h; simp [h, hs.1], hP.2⟩
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨rv, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun)
          (good_dirctl w P f.kind Good hS hs.2 st1 _ _ hg1)
      · obtain ⟨_, h, _⟩ := bind_ok hrun
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i h1' h2' h3' h4'
      rw [admPark_other w P wt pk h1' h2' h3' h4'] at hs
      split at hrun
      · rename_i hw
        rw [hw] at hs
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        obtain ⟨o, ho, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨sv, _, hrun⟩ := bind_ok hrun
        exact via _ o st1 st2 sv hs h1 ho h2 hrun
      · rename_i hw
        rw [hw] at hs
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        unfold pend at h0
        split at h0
        · simp at h0
        simp only [Except.ok.injEq] at h0; subst h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        have hg1 := hflP _ st1 h1 rfl ⟨fun p hp => by
          rcases List.mem_append.mp hp with h | h
          · exact hP.1 p h
          · simp at h; simp [h, hs], hP.2⟩
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        exact invRes_of_frame Good f _ r (outs_charge f _ _ _ _ _ r hrun) hg1
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | do_ vars cl acceptGiven accept when_ else_ cases =>
    simp only [admStep, Bool.and_eq_true] at hs
    obtain ⟨hop, hcs⟩ := hs
    have viaRest : ∀ st2 : St, PendOK P st2 → Good (stobj st2) →
        run w f n st2 rest = .ok r → InvRes Good f r :=
      fun st2 hP2 hG2 h => go st2 rest r hrest h hP2 hG2
    have viaCase : ∀ st2 : St, PendOK P st2 → Good (stobj st2) →
        ∀ opt ss, (opt, ss) ∈ cases → run w f n st2 ss = .ok r → InvRes Good f r :=
      fun st2 hP2 hG2 opt ss hm h => go st2 ss r (admCases_mem w P cases opt ss hm hcs) h hP2 hG2
    have viaRef : ∀ st2 : St, PendOK P st2 → Good (stobj st2) →
        ∀ ss, (ss = f.refusal ∨ ∃ rs, ss = [.stop rs none]) → run w f n st2 ss = .ok r →
        InvRes Good f r := by
      intro st2 hP2 hG2 ss hss h
      rcases hss with rfl | ⟨rs, rfl⟩
      · exact go st2 _ r hR h hP2 hG2
      · exact go st2 _ r rfl h hP2 hG2
    rw [run] at hrun
    dsimp only at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hg1, hp1⟩ := hfl st1 h1
    obtain ⟨op, hop', hrun⟩ := bind_ok hrun
    have hfo := findOp_spec w _ op hop'
    rcases when_ with _ | e
    · dsimp only at hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      rw [if_neg (by decide)] at hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨hp2, hn2, _⟩ := bind_frame w cl.op op st1 st2 vars _ hfo h2
      have hP2 : PendOK P st2 := by unfold PendOK; rw [hp2, hn2]; exact hp1
      have hG2 : Good (stobj st2) := callDo w P f.kind Good hS cl op st1 st2 o vars hop hfo rfl ho h2 hg1
      do_tail_inv
    · dsimp only at hrun
      obtain ⟨wv, _, hrun⟩ := bind_ok hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      split at hrun
      · obtain ⟨vs, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        simp only [pure, Except.pure, Except.ok.injEq] at h2; subst h2
        have hP2 : PendOK P ({ st1 with vars := vars.zip vs ++ st1.vars } : St) := hp1
        have hG2 : Good (stobj ({ st1 with vars := vars.zip vs ++ st1.vars } : St)) := hg1
        do_tail_inv
      · obtain ⟨o, ho, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨hp2, hn2, _⟩ := bind_frame w cl.op op st1 st2 vars _ hfo h2
        have hP2 : PendOK P st2 := by unfold PendOK; rw [hp2, hn2]; exact hp1
        have hG2 : Good (stobj st2) := callDo w P f.kind Good hS cl op st1 st2 o vars hop hfo rfl ho h2 hg1
        do_tail_inv
  | issue cl ok refused =>
    simp only [admStep, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨⟨⟨hop, hok⟩, hrf⟩, hpark⟩, hst⟩, hwr⟩ := hs
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hg1, hp1⟩ := hfl st1 h1
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
    obtain ⟨hp2, hn2, _⟩ := call_frame w f.kind st1 st2 cl o _ ho h2
    have hP2 : PendOK P st2 := by unfold PendOK; rw [hp2, hn2]; exact hp1
    have hG2 : Good (stobj st2) := hS.call cl.op hop st1 st2 cl o _ rfl ho h2 hg1
    obtain ⟨code, _, hrun⟩ := bind_ok hrun
    split at hrun
    · exact go st2 ok r hok hrun hP2 hG2
    split at hrun
    · refine go st2 _ r ?_ hrun hP2 hG2
      rw [admSteps_append]
      simp [hrf, admSteps, admStep, admPark, hpark]
    · refine go st2 _ r ?_ hrun hP2 hG2
      rw [admSteps_append]
      split
      · simp [hrf, admSteps, admStep, hst, hwr]
      · simp [hrf, hR]
  | repeat_ nE body until_ =>
    simp only [admStep] at hs
    have hloop : ∀ m, m ≤ n → ∀ (kk : Nat) (s0 : St) (out : St × Nat),
        run.loop w f body until_ m kk s0 = .ok out → Good (stobj s0) → Good (stobj out.1) := by
      intro m
      induction m with
      | zero => intro _ kk s0 out h; unfold run.loop at h; nomatch h
      | succ m' ihm =>
        intro hm kk s0 out h hg0
        cases kk with
        | zero =>
          unfold run.loop at h
          simp only [Except.ok.injEq] at h; subst h; exact hg0
        | succ kk' =>
          unfold run.loop at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨reads, _, h⟩ := bind_ok h
          obtain ⟨uv, _, h⟩ := bind_ok h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hg0
          · obtain ⟨res, hres, h⟩ := bind_ok h
            cases res with
            | done _ => simp [throw, throwThe, MonadExceptOf.throw] at h
            | again st' =>
              have hpass := ih m' (by omega) f
                ({ stobjs := s0.stobjs, vars := reads ++ f.base } : St) (body ++ [.repeatNext])
                (.again st') rfl hR (by rw [admSteps_append]; simp [hs, admSteps, admStep]) hres
                (pendOK_clean P _ rfl rfl) hg0
              exact ihm (by omega) kk' { s0 with stobjs := st'.stobjs } out h hpass
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    have hg1 := (hfl st1 h1).1
    obtain ⟨nv, _, hrun⟩ := bind_ok hrun
    obtain ⟨lp, hlp, hrun⟩ := bind_ok hrun
    obtain ⟨per, _, hrun⟩ := bind_ok hrun
    have hfl' := hloop n (Nat.le_refl _) _ st1 lp hlp hg1
    exact go _ rest r hrest hrun ⟨by simp, hP.2⟩ hfl'

/-- The children an arm is called with (its arguments after the formals), as a state. -/
def startSt (k : Kind) (observe : Bool) (args : List Val) : St :=
  { stobjs := k.tuple.zip (args.drop (if observe then 10 else 5)), vars := [] }

/-- **`runArm_inv`**: an admissible arm, run from children satisfying `Good`, returns the tuple's
children (as its last results) from a state whose children satisfy `Good`. -/
theorem runArm_inv (k : Kind) (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat) (v : Val)
    (Good : (String → Except String Val) → Prop) (hS : Sem w P k Good)
    (hadm : admArm w P k a = true)
    (hG0 : Good (stobj (startSt k observe args)))
    (hrun : runArm w k a observe args fuel = .ok v) :
    ∃ stF pre ts, v = Val.ofList (pre ++ ts) ∧ k.tuple.mapM (stobj stF) = .ok ts ∧
      Good (stobj stF) := by
  unfold admArm at hadm
  split at hadm
  · rename_i decl hread
    simp only [Bool.and_eq_true] at hadm
    obtain ⟨⟨hst, hrf⟩, hsub⟩ := hadm
    cases observe
    all_goals
      simp only [runArm, startSt, Bool.false_eq_true, if_false, if_true] at hrun hG0
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
        have := run_inv w P k Good hS hsub fuel _ _ decl.steps (.done v') rfl hrf hst hres
          (pendOK_clean P _ rfl rfl) hG0
        obtain ⟨stF, ⟨pre, ts, hv, hts⟩, hg⟩ := this
        exact ⟨stF, pre, ts, hv, hts, hg⟩
  · cases hadm

end

end Fn2.Arms.Inv
