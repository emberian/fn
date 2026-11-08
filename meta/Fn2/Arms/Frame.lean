module

public import Fn2.Arms
public import Fn2.ArmsLemmas
public import Fn2.Arms.Cost
public import Fn2.Pathway
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.Frame: the children an arm can change, and its frame theorem

`derivedTables w k a` is the set of the tuple's children (stobjs) that `a`'s declaration can
write, read off the declaration (`none` where a refusal or sub-arm admits no closed set).
`runArm_frame` proves that a child outside it comes out of every run exactly as it went in.
-/

namespace Fn2.Arms.Frame
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Bound Fn2.Arms.Cost

set_option autoImplicit false

section
variable (w : World) (k : Kind)

/-- The children a declared operation's call can replace (its `stobjs-out`). -/
def opTables (name : String) : List String :=
  match w.ops.find? (·.name == name) with
  | some o => o.stobjsOut.filterMap id
  | none => []

/-- The kind's table, the directory and the control: what the checked write can change. -/
def writeTables : List String := [k.name, "FN2-MACHINES", "FN2-CONTROL"]

def parkTables (wait : String) (pk : Option String) : List String :=
  match wait with
  | "OPERATION" => opTables w "FN2-MACHINE-PARK"
  | "ADMISSION" => opTables w "FN2-MACHINE-PARK-ADMISSION"
  | "TAKEN" => opTables w ("FN2-MACHINE-PARK-TAKEN-" ++ pk.getD "")
  | "POOL" => writeTables k
  | other =>
    match w.waits.find? (·.kind == other) with
    | some ⟨_, some parker⟩ => opTables w parker
    | some ⟨_, none⟩ => writeTables k
    | none => []

mutual
def stepT (refT : List String) (subT : String → List String) : Step → List String
  | .let_ _ _ | .charge _ _ _ _ | .idle | .yield | .wake | .nowake | .repeatNext => []
  | .set pairs => if pairs.isEmpty then [] else writeTables k
  | .next _ => writeTables k
  | .wakeRow _ => ["FN2-MACHINES", "FN2-CONTROL"]
  | .repeat_ _ body _ => stepsT refT subT body
  | .do_ _ c _ _ _ _ cases => opTables w c.op ++ "FN2-CONTROL" :: refT ++ casesT refT subT cases
  | .issue c ok refused =>
    opTables w c.op ++ stepsT refT subT ok ++ stepsT refT subT refused ++
      opTables w "FN2-MACHINE-PARK" ++ writeTables k ++ refT
  | .if_ _ a b => stepsT refT subT a ++ stepsT refT subT b
  | .cond clauses => clausesT refT subT clauses
  | .case_ _ arms => casesT refT subT arms
  | .wait _ _ | .halt => writeTables k
  | .park wt _ pk _ _ => parkTables w k wt pk
  | .stop _ _ => ["FN2-CONTROL"]
  | .goto name => subT name

def stepsT (refT : List String) (subT : String → List String) : List Step → List String
  | [] => []
  | s :: ss => stepT refT subT s ++ stepsT refT subT ss

def casesT (refT : List String) (subT : String → List String) :
    List (Option (List Val) × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsT refT subT ss ++ casesT refT subT cs

def clausesT (refT : List String) (subT : String → List String) :
    List (Expr × List Step) → List String
  | [] => []
  | (_, ss) :: cs => stepsT refT subT ss ++ clausesT refT subT cs
end

def subset (a b : List String) : Bool := a.all (b.contains ·)

/-- The refusal's children, closed under its own re-entry (a checked post-fixpoint). -/
def refTables (subT : String → List String) (R : List Step) : Option (List String) :=
  let r0 := stepsT w k [] subT R
  if subset (stepsT w k r0 subT R) r0 then some r0 else none

def subTablesN : Nat → String → List String
  | 0, _ => []
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub => match sub.read with
      | .ok decl =>
        let r := (refTables w k (subTablesN d) decl.onRefusal).getD []
        stepsT w k r (subTablesN d) decl.steps
      | .error _ => []
    | none => []

/-- `subT` covers every sub-arm (a checked post-fixpoint). -/
def subOKT (subT : String → List String) : Bool :=
  k.subarms.all fun s =>
    match k.subarms.find? (·.tag == s.tag) with
    | some sub => match sub.read with
      | .ok decl => match refTables w k subT decl.onRefusal with
        | some r => subset (stepsT w k r subT decl.steps) (subT s.tag)
        | none => false
      | .error _ => true
    | none => true

/-- **The children an arm can change.** -/
def derivedTables (a : Arm) : Option (List String) :=
  match a.read with
  | .ok decl =>
    let subT := subTablesN w k (k.subarms.length + 1)
    if subOKT w k subT then
      match refTables w k subT decl.onRefusal with
      | some r => some (stepsT w k r subT decl.steps)
      | none => none
    else none
  | .error _ => none

end

variable (w : World)

/-! ## The frame of the interpreter's steps -/

/-- What a result shows of the children: the tuple's values, after the result values. -/
def Outs (f : Frame) (stF : St) (v : Val) : Prop :=
  ∃ pre ts, v = Val.ofList (pre ++ ts) ∧ f.kind.tuple.mapM (stobj stF) = .ok ts

/-- A result keeps every child outside `T` as it was in `st`. -/
def FrameRes (f : Frame) (T : List String) (st : St) : Res → Prop
  | .done v => ∃ stF, Outs f stF v ∧ ∀ n, n ∉ T → stobj stF n = stobj st n
  | .again st' => ∀ n, n ∉ T → stobj st' n = stobj st n

/-- Nothing is pending, or the checked write's children are all in `T`. -/
def Pinv (k : Kind) (T : List String) (st : St) : Prop :=
  (st.pending = [] ∧ st.next = none) ∨ (∀ t ∈ writeTables k, t ∈ T)

theorem frameRes_trans (f : Frame) (T : List String) (st st1 : St) (r : Res)
    (h : FrameRes f T st1 r) (h1 : ∀ n, n ∉ T → stobj st1 n = stobj st n) : FrameRes f T st r := by
  cases r with
  | done v =>
    obtain ⟨stF, ho, hf⟩ := h
    exact ⟨stF, ho, fun n hn => (hf n hn).trans (h1 n hn)⟩
  | again st' => exact fun n hn => (h n hn).trans (h1 n hn)

theorem stobj_of_stobjs (st st' : St) (h : st'.stobjs = st.stobjs) (n : String) :
    stobj st' n = stobj st n := by
  simp only [stobj, h]

theorem bindOuts_go_stobj (st st' : St) (outs : List (Option String))
    (vars : List String) (rs : List Val) (h : bindOuts.go st outs vars rs = .ok st') :
    st'.pending = st.pending ∧ st'.next = st.next ∧
    ∀ c, c ∉ outs.filterMap id → stobj st' c = stobj st c := by
  induction outs generalizing st vars rs with
  | nil =>
    cases rs <;> simp [bindOuts.go] at h <;> subst h <;> exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons o os ih =>
    cases o with
    | some s =>
      cases rs with
      | nil => simp [bindOuts.go] at h
      | cons r rs' =>
        simp only [bindOuts.go] at h
        obtain ⟨hp, hn, hst⟩ := ih (setStobj st s r) vars rs' h
        refine ⟨hp, hn, fun c hc => ?_⟩
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
          obtain ⟨hp, hn, hst⟩ := ih st [] rs' h
          exact ⟨hp, hn, fun c hc => hst c (by simpa [List.filterMap] using hc)⟩
      | cons v vs' =>
        cases rs with
        | nil => simp [bindOuts.go] at h
        | cons r rs' =>
          simp only [bindOuts.go] at h
          obtain ⟨hp, hn, hst⟩ := ih { st with vars := (v, r) :: st.vars } vs' rs' h
          exact ⟨hp, hn, fun c hc => hst c (by simpa [List.filterMap] using hc)⟩

theorem bindOuts_stobj (st st' : St) (outs : List (Option String))
    (vars : List String) (res : Val) (h : bindOuts st outs vars res = .ok st') :
    st'.pending = st.pending ∧ st'.next = st.next ∧
    ∀ c, c ∉ outs.filterMap id → stobj st' c = stobj st c := by
  unfold bindOuts at h
  split at h
  · rename_i s
    simp only [Except.ok.injEq] at h; subst h
    refine ⟨rfl, rfl, fun c hc => ?_⟩
    have hc1 : c ≠ s := fun heq => hc (by simp [List.filterMap, heq])
    exact stobj_setStobj_ne st s c res (Ne.symm hc1)
  · split at h <;>
      (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩)
  · exact bindOuts_go_stobj st st' outs vars res.toList h

theorem flush_clean (f : Frame) (st st' : St) (h : flush w f st = .ok st') :
    st'.pending = [] ∧ st'.next = none := by
  unfold flush at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try (simp only [reduceCtorEq] at h; done))
  all_goals (simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem flush_same (f : Frame) (st st' : St) (h : flush w f st = .ok st')
    (hc : st.pending = [] ∧ st.next = none) : st'.stobjs = st.stobjs := by
  unfold flush at h
  simp only [hc.1, hc.2, List.mapM_nil, List.isEmpty_nil, if_true,
    bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
  subst h; rfl

/-- A flush keeps every child outside `T` when the path's pending writes are covered by `T`. -/
theorem flush_T (k : Kind) (f : Frame) (hk : f.kind = k) (T : List String) (st st' : St)
    (hP : Pinv k T st) (h : flush w f st = .ok st') :
    (∀ n, n ∉ T → stobj st' n = stobj st n) ∧ st'.pending = [] ∧ st'.next = none := by
  refine ⟨fun n hn => ?_, flush_clean w f st st' h⟩
  rcases hP with hc | hK
  · exact stobj_of_stobjs st st' (flush_same w f st st' h hc) n
  · subst hk
    exact (flush_frame w f st st' h n (fun e => hn (e ▸ hK _ (by simp [writeTables])))
      (fun e => hn (e ▸ hK _ (by simp [writeTables])))
      (fun e => hn (e ▸ hK _ (by simp [writeTables])))).1

theorem outs_charge (f : Frame) (st : St) (b s d r : Val) (res : Res)
    (h : chargeResult f st b s d r = .ok res) : FrameRes f [] st res := by
  unfold chargeResult at h
  obtain ⟨t, ht, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨st, ⟨_, t, rfl, ht⟩, fun _ _ => rfl⟩

theorem outs_wake (f : Frame) (st : St) (v : Val) (res : Res)
    (h : wakeResult f st v = .ok res) : FrameRes f [] st res := by
  unfold wakeResult at h
  obtain ⟨t, ht, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨st, ⟨[v], t, rfl, ht⟩, fun _ _ => rfl⟩

theorem frameRes_nil (f : Frame) (T : List String) (st : St) (r : Res) (h : FrameRes f [] st r) :
    FrameRes f T st r := by
  cases r with
  | done v => obtain ⟨stF, ho, hf⟩ := h; exact ⟨stF, ho, fun n _ => hf n (by simp)⟩
  | again st' => exact fun n _ => h n (by simp)

theorem mem_casesT (k : Kind) (refT : List String) (subT : String → List String)
    (cs : List (Option (List Val) × List Step)) (opt : Option (List Val)) (ss : List Step)
    (hm : (opt, ss) ∈ cs) : ∀ t ∈ stepsT w k refT subT ss, t ∈ casesT w k refT subT cs := by
  induction cs with
  | nil => cases hm
  | cons p cs ih =>
    obtain ⟨o, ss'⟩ := p
    intro t ht
    simp only [casesT, List.mem_append]
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact Or.inl ht
    · exact Or.inr (ih h t ht)

theorem mem_clausesT (k : Kind) (refT : List String) (subT : String → List String)
    (cs : List (Expr × List Step)) (e : Expr) (ss : List Step)
    (hm : (e, ss) ∈ cs) : ∀ t ∈ stepsT w k refT subT ss, t ∈ clausesT w k refT subT cs := by
  induction cs with
  | nil => cases hm
  | cons p cs ih =>
    obtain ⟨o, ss'⟩ := p
    intro t ht
    simp only [clausesT, List.mem_append]
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact Or.inl ht
    · exact Or.inr (ih h t ht)

theorem subset_spec {a b : List String} (h : subset a b = true) : ∀ t ∈ a, t ∈ b := by
  intro t ht
  have := List.all_eq_true.mp h t ht
  simpa using this

theorem refTables_spec (k : Kind) (subT : String → List String) (R : List Step) (refT : List String)
    (h : refTables w k subT R = some refT) :
    ∀ t ∈ stepsT w k refT subT R, t ∈ refT := by
  unfold refTables at h
  dsimp only at h
  split at h
  · rename_i hs
    simp only [Option.some.injEq] at h; subst h
    exact subset_spec hs
  · cases h

theorem subOKT_spec (k : Kind) (subT : String → List String) (hsub : subOKT w k subT = true)
    (name : String) (sub : Arm) (d : ArmDecl)
    (hf : k.subarms.find? (·.tag == name) = some sub) (hd : sub.read = .ok d) :
    ∃ r, refTables w k subT d.onRefusal = some r ∧
      ∀ t ∈ stepsT w k r subT d.steps, t ∈ subT name := by
  have hmem := List.mem_of_find?_eq_some hf
  have htag : sub.tag = name := by simpa using List.find?_some hf
  unfold subOKT at hsub
  have := List.all_eq_true.mp hsub sub hmem
  rw [htag, hf] at this
  simp only [hd] at this
  split at this
  · rename_i r hr
    exact ⟨r, hr, subset_spec this⟩
  · cases this

theorem run_stop_frame (k : Kind) (f : Frame) (hk : f.kind = k) (T : List String)
    (hT : "FN2-CONTROL" ∈ T) (m : Nat) (st : St) (reason : String) (s : Option Expr)
    (rest : List Step) (r : Res) (hP : Pinv k T st)
    (h : run w f (m + 1) st (.stop reason s :: rest) = .ok r) : FrameRes f T st r := by
  simp only [run] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨st1, h1, h⟩ := bind_ok h
  obtain ⟨hf1, _⟩ := flush_T w k f hk T st st1 hP h1
  obtain ⟨c1, _, h⟩ := bind_ok h
  have hfin : ∀ c2, (∀ r', stopEnd w f (setStobj st1 "FN2-CONTROL" c2) s = .ok r' →
      FrameRes f T st r') := by
    intro c2 r' he
    have h2 : ∀ n, n ∉ T → stobj (setStobj st1 "FN2-CONTROL" c2) n = stobj st n := by
      intro n hn
      have hne : "FN2-CONTROL" ≠ n := fun e => hn (e ▸ hT)
      rw [stobj_setStobj_ne _ _ _ _ hne]
      exact hf1 n hn
    unfold stopEnd at he
    split at he
    · obtain ⟨nv, _, he⟩ := bind_ok he
      exact frameRes_trans f T st _ r' (frameRes_nil f T _ r' (outs_wake f _ _ r' he)) h2
    · obtain ⟨e, _, he⟩ := bind_ok he
      obtain ⟨sv, _, he⟩ := bind_ok he
      exact frameRes_trans f T st _ r' (frameRes_nil f T _ r' (outs_charge f _ _ _ _ _ r' he)) h2
  split at h <;>
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨c2, _, h⟩ := bind_ok h
    exact hfin c2 r h

theorem parkTables_other (k : Kind) (wt : String) (pk : Option String)
    (h1 : wt = "OPERATION" → False) (h2 : wt = "ADMISSION" → False) (h3 : wt = "TAKEN" → False)
    (h4 : wt = "POOL" → False) :
    parkTables w k wt pk = match w.waits.find? (·.kind == wt) with
      | some ⟨_, some parker⟩ => opTables w parker
      | some ⟨_, none⟩ => writeTables k
      | none => [] := by
  unfold parkTables
  split
  · exact absurd rfl h1
  · exact absurd rfl h2
  · exact absurd rfl h3
  · exact absurd rfl h4
  · rfl

theorem callOp_op (k : Kind) (st : St) (c : Call) (o : Op × Val) (h : callOp w k st c = .ok o) :
    w.ops.find? (·.name == c.op) = some o.1 := by
  unfold callOp at h
  obtain ⟨op, hop, h⟩ := bind_ok h
  have hfo : w.ops.find? (·.name == c.op) = some op := by
    unfold findOp at hop
    split at hop
    · rename_i o' hf; cases hop; exact hf
    · cases hop
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact hfo
  · obtain ⟨_, h', _⟩ := bind_ok h
    simp [throw, throwThe, MonadExceptOf.throw] at h'

/-- After a call and its binding, every child outside the call's `stobjs-out` is as it was. -/
theorem call_frame (k : Kind) (st st2 : St) (c : Call) (o : Op × Val) (vars : List String)
    (h1 : callOp w k st c = .ok o) (h2 : bindOuts st o.1.stobjsOut vars o.2 = .ok st2) :
    st2.pending = st.pending ∧ st2.next = st.next ∧
    ∀ nn, nn ∉ opTables w c.op → stobj st2 nn = stobj st nn := by
  obtain ⟨hp, hn, hs⟩ := bindOuts_stobj st st2 _ vars _ h2
  refine ⟨hp, hn, fun nn hnn => hs nn ?_⟩
  unfold opTables at hnn
  rw [callOp_op w k st c o h1] at hnn
  exact hnn

theorem findOp_spec (n : String) (op : Op) (h : findOp w n = .ok op) :
    w.ops.find? (·.name == n) = some op := by
  unfold findOp at h
  split at h
  · rename_i o' hf; cases h; exact hf
  · cases h

theorem bind_frame (c : String) (op : Op) (st st2 : St) (vars : List String) (res : Val)
    (hfo : w.ops.find? (·.name == c) = some op) (h2 : bindOuts st op.stobjsOut vars res = .ok st2) :
    st2.pending = st.pending ∧ st2.next = st.next ∧
    ∀ nn, nn ∉ opTables w c → stobj st2 nn = stobj st nn := by
  obtain ⟨hp, hn, hs⟩ := bindOuts_stobj st st2 _ vars _ h2
  refine ⟨hp, hn, fun nn hnn => hs nn ?_⟩
  unfold opTables at hnn; rw [hfo] at hnn; exact hnn

set_option hygiene false in
local macro "do_tail_frame" : tactic => `(tactic| (
  split at hrun
  · exact viaRest _ hP2 hf2 hrun
  · split at hrun
    · obtain ⟨code, _, hrun⟩ := bind_ok hrun
      repeat' split at hrun
      all_goals first
        | exact viaRest _ hP2 hf2 hrun
        | (rename_i hfind; exact viaCase _ hP2 hf2 _ _ (List.mem_of_find?_eq_some hfind) hrun)
        | exact viaRef _ hP2 hf2 _ (Or.inr ⟨_, rfl⟩) hrun
        | (rcases faultRoute_cases _ op.faults code f.refusal with he | he <;> rw [he] at hrun
           · exact viaRef _ hP2 hf2 _ (Or.inl rfl) hrun
           · exact viaRef _ hP2 hf2 _ (Or.inr ⟨_, rfl⟩) hrun)
    · obtain ⟨_, hth, _⟩ := bind_ok hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hth))

/-- **The frame over the interpreter (`run_frame`)**: a path whose tables (with its refusal's and
its sub-arms') lie in `T`, run with a continuation that keeps the frame, keeps every child outside
`T`. -/
theorem run_frame (k : Kind) (subT : String → List String) (hsub : subOKT w k subT = true)
    (T : List String) :
    ∀ (fuel : Nat) (f : Frame) (st : St) (xs X : List Step) (refT : List String) (r : Res),
      f.kind = k → refTables w k subT f.refusal = some refT →
      run w f fuel st (xs ++ X) = .ok r →
      (∀ t ∈ stepsT w k refT subT xs, t ∈ T) → Pinv k T st →
      (∀ fuel', fuel' ≤ fuel → ∀ st' r', run w f fuel' st' X = .ok r' → Pinv k T st' →
        FrameRes f T st' r') →
      FrameRes f T st r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
  intro f st xs X refT r hk hrefT hrun hxs hP hX
  cases fuel with
  | zero => cases xs <;> cases X <;> simp [run] at hrun
  | succ n =>
  have hRclosed := refTables_spec w k subT f.refusal refT hrefT
  have branch : ∀ (st' : St) (ss : List Step) (r' : Res), run w f n st' ss = .ok r' →
      (∀ t ∈ stepsT w k refT subT ss, t ∈ T) → Pinv k T st' → FrameRes f T st' r' := by
    intro st' ss r' h1 h2 h3
    exact ih n (Nat.lt_succ_self n) f st' ss [] refT r' hk hrefT (by simpa using h1) h2 h3
      (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
  have hR : (∀ t ∈ refT, t ∈ T) → ∀ m, m ≤ n → ∀ (st' : St) (r' : Res),
      run w f m st' f.refusal = .ok r' → Pinv k T st' → FrameRes f T st' r' := by
    intro hrefTT m hm st' r' h1 h3
    exact ih m (Nat.lt_succ_of_le hm) f st' f.refusal [] refT r' hk hrefT (by simpa using h1)
      (fun t ht => hrefTT t (hRclosed t ht)) h3 (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
  have hStop : "FN2-CONTROL" ∈ T → ∀ (st' : St) (rs : String) (r' : Res),
      run w f n st' [.stop rs none] = .ok r' → Pinv k T st' → FrameRes f T st' r' := by
    intro hctlT st' rs r' h1 h3
    cases n with
    | zero => simp [run] at h1
    | succ m => exact run_stop_frame w k f hk T hctlT m st' rs none [] r' h3 h1
  have cont : ∀ (st' : St) (rest : List Step) (r' : Res), run w f n st' (rest ++ X) = .ok r' →
      (∀ t ∈ stepsT w k refT subT rest, t ∈ T) → Pinv k T st' → FrameRes f T st' r' := by
    intro st' rest r' h1 h2 h3
    exact ih n (Nat.lt_succ_self n) f st' rest X refT r' hk hrefT h1 h2 h3
      (fun m hm => hX m (Nat.le_succ_of_le hm))
  cases xs with
  | nil => exact hX (n + 1) (Nat.le_refl _) st r (by simpa using hrun) hP
  | cons s rest =>
  rw [List.cons_append] at hrun
  have hs : ∀ t ∈ stepT w k refT subT s, t ∈ T := fun t ht => hxs t (by simp [stepsT, ht])
  have hrest : ∀ t ∈ stepsT w k refT subT rest, t ∈ T := fun t ht => hxs t (by simp [stepsT, ht])
  have hK : ∀ t ∈ writeTables k, t ∈ T → True := fun _ _ _ => trivial
  clear hK
  subst hk
  cases s with
  | let_ x e =>
    simp only [run] at hrun
    obtain ⟨xv, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (cont _ rest r hrun hrest hP) (fun _ _ => rfl)
  | set pairs =>
    simp only [run] at hrun
    obtain ⟨st', hst', hrun⟩ := bind_ok hrun
    unfold pend at hst'
    split at hst'
    · simp at hst'
    simp only [Except.ok.injEq] at hst'; subst hst'
    have hP' : Pinv f.kind T { st with pending := st.pending ++ pairs } := by
      by_cases he : pairs = []
      · subst he; simpa [Pinv] using hP
      · right; intro t ht; apply hs; simp [stepT, he, ht]
    exact frameRes_trans f T st _ r (cont _ rest r hrun hrest hP') (fun _ _ => rfl)
  | next ph =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    have hP' : Pinv f.kind T { st with next := some ph } := Or.inr (fun t ht => hs t (by simpa [stepT] using ht))
    exact frameRes_trans f T st _ r (cont _ rest r hrun hrest hP') (fun _ _ => rfl)
  | wakeRow e =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨rv, _, hrun⟩ := bind_ok hrun
    have hm : "FN2-MACHINES" ∈ T := hs _ (by simp [stepT])
    have hctlT : "FN2-CONTROL" ∈ T := hs _ (by simp [stepT])
    have h1 := cont _ rest r hrun hrest (by exact hP)
    refine frameRes_trans f T st _ r h1 (fun nn hn => ?_)
    have hn1 : "FN2-CONTROL" ≠ nn := fun e => hn (e ▸ hctlT)
    have hn2 : "FN2-MACHINES" ≠ nn := fun e => hn (e ▸ hm)
    show stobj (setStobj (setStobj st "FN2-MACHINES" rv.car) "FN2-CONTROL" rv.cdr.car) nn = _
    rw [stobj_setStobj_ne _ _ _ _ hn1, stobj_setStobj_ne _ _ _ _ hn2]
  | if_ cnd a b =>
    simp only [run] at hrun
    obtain ⟨cv, _, hrun⟩ := bind_ok hrun
    split at hrun
    · exact branch st a r hrun (fun t ht => hs t (by simp [stepT, ht])) hP
    · exact branch st b r hrun (fun t ht => hs t (by simp [stepT, ht])) hP
  | cond clauses =>
    simp only [run] at hrun
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    rcases o with _ | ⟨e, ss⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · exact branch st ss r hrun (fun t ht => hs t (by
        simpa [stepT] using mem_clausesT w f.kind refT subT clauses e ss (findM_mem _ _ _ ho) t ht)) hP
  | case_ key arms =>
    simp only [run] at hrun
    obtain ⟨kv, _, hrun⟩ := bind_ok hrun
    split at hrun
    · rename_i cs ss hfind
      exact branch st ss r hrun (fun t ht => hs t (by
        simpa [stepT] using mem_casesT w f.kind refT subT arms cs ss (List.mem_of_find?_eq_some hfind) t ht)) hP
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | stop reason se => exact run_stop_frame w f.kind f rfl T (hs _ (by simp [stepT])) n st reason se _ r hP hrun
  | charge b sE d rE =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun))
      (flush_T w f.kind f rfl T st st1 hP h1).1
  | idle =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun))
      (flush_T w f.kind f rfl T st st1 hP h1).1
  | yield =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun))
      (flush_T w f.kind f rfl T st st1 hP h1).1
  | wait b sE =>
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
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun))
      (flush_T w f.kind f rfl T _ st1 (Or.inr (fun t ht => hs t (by simpa [stepT] using ht))) h1).1
  | halt =>
    simp only [run] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
    unfold pend at h0
    split at h0
    · simp at h0
    simp only [Except.ok.injEq] at h0; subst h0
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun))
      (flush_T w f.kind f rfl T _ st1 (Or.inr (fun t ht => hs t (by simpa [stepT] using ht))) h1).1
  | wake =>
    simp only [run] at hrun
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_wake f _ _ r hrun))
      (flush_T w f.kind f rfl T st st1 hP h1).1
  | nowake =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨_, _, hrun⟩ := bind_ok hrun
    exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_wake f _ _ r hrun))
      (flush_T w f.kind f rfl T st st1 hP h1).1
  | repeatNext =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    simp only [pure, Except.pure, Except.ok.injEq] at hrun; subst hrun
    exact (flush_T w f.kind f rfl T st st1 hP h1).1
  | goto name =>
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hf1, hc1⟩ := flush_T w f.kind f rfl T st st1 hP h1
    split at hrun
    · rename_i sub hfind
      obtain ⟨y, hy, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hy; subst hy
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨_, _, hrun⟩ := bind_ok hrun
      obtain ⟨reads, _, hrun⟩ := bind_ok hrun
      obtain ⟨d, hd, hrun⟩ := bind_ok hrun
      obtain ⟨r', hr', hstT⟩ := subOKT_spec w f.kind subT hsub name sub d hfind hd
      have hsubT : ∀ t ∈ subT name, t ∈ T := fun t ht => hs t (by simpa [stepT] using ht)
      have := ih n (Nat.lt_succ_self n) { f with refusal := d.onRefusal } _ d.steps [] r' r rfl hr'
        (by simpa using hrun) (fun t ht => hsubT t (hstT t ht))
        (Or.inl ⟨rfl, rfl⟩) (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
      refine frameRes_trans _ T st _ r ?_ hf1
      cases r with
      | done v => obtain ⟨stF, ho, hf⟩ := this; exact ⟨stF, ho, fun nn hn => hf nn hn⟩
      | again st' => exact fun nn hn => this nn hn
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | park wt arg pk sE keys =>
    simp only [run] at hrun
    obtain ⟨mb, _, hrun⟩ := bind_ok hrun
    have hpk : ∀ t ∈ parkTables w f.kind wt pk, t ∈ T := fun t ht => hs t (by simpa [stepT] using ht)
    have via : ∀ (c : Call) (o : Op × Val) (st1 st2 : St) (sv : Val),
        (∀ t ∈ opTables w c.op, t ∈ T) → flush w f st = .ok st1 → callOp w f.kind st1 c = .ok o →
        bindOuts st1 o.1.stobjsOut [] o.2 = .ok st2 →
        chargeResult f st2 (.int 0) sv (.int 0) Val.nil = .ok r → FrameRes f T st r := by
      intro c o st1 st2 sv hT h1 h2 h3 h4
      obtain ⟨hf1, _⟩ := flush_T w f.kind f rfl T st st1 hP h1
      obtain ⟨_, _, hf2⟩ := call_frame w f.kind st1 st2 c o [] h2 h3
      exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r h4))
        (fun nn hn => (hf2 nn (fun hm => hn (hT nn hm))).trans (hf1 nn hn))
    have hK : (∀ t ∈ writeTables f.kind, t ∈ parkTables w f.kind wt pk) → ∀ (st0 st1 : St),
        st0.stobjs = st.stobjs → flush w f st0 = .ok st1 →
        ∀ nn, nn ∉ T → stobj st1 nn = stobj st nn := by
      intro hw st0 st1 hs0 h1 nn hn
      rw [← stobj_of_stobjs st st0 hs0 nn]
      exact (flush_T w f.kind f rfl T st0 st1 (Or.inr (fun t ht => hpk t (hw t ht))) h1).1 nn hn
    split at hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (fun t ht => hpk t (by simpa [parkTables] using ht)) h1 ho h2 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (fun t ht => hpk t (by simpa [parkTables] using ht)) h1 ho h2 hrun
    · obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
      obtain ⟨o, ho, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨sv, _, hrun⟩ := bind_ok hrun
      exact via _ o st1 st2 sv (fun t ht => hpk t (by simpa [parkTables] using ht)) h1 ho h2 hrun
    · split at hrun
      · obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        unfold pend at h0
        split at h0
        · simp at h0
        simp only [Except.ok.injEq] at h0; subst h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        have hf1 := hK (fun t ht => by simpa [parkTables] using ht) _ st1 (by rfl) h1
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨rv, _, hrun⟩ := bind_ok hrun
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        have hm : "FN2-MACHINES" ∈ T := hpk _ (by simp [parkTables, writeTables])
        have hctlT : "FN2-CONTROL" ∈ T := hpk _ (by simp [parkTables, writeTables])
        refine frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun)) ?_
        intro nn hn
        have hn1 : "FN2-CONTROL" ≠ nn := fun e => hn (e ▸ hctlT)
        have hn2 : "FN2-MACHINES" ≠ nn := fun e => hn (e ▸ hm)
        rw [stobj_setStobj_ne _ _ _ _ hn1, stobj_setStobj_ne _ _ _ _ hn2]
        exact hf1 nn hn
      · obtain ⟨_, h, _⟩ := bind_ok hrun
        simp [throw, throwThe, MonadExceptOf.throw] at h
    · split at hrun
      · rename_i hw
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        obtain ⟨o, ho, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨sv, _, hrun⟩ := bind_ok hrun
        have hpt := parkTables_other w f.kind wt pk (by assumption) (by assumption) (by assumption)
          (by assumption)
        rw [hw] at hpt
        exact via _ o st1 st2 sv (fun t ht => hpk t (by rw [hpt]; exact ht)) h1 ho h2 hrun
      · rename_i hw
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        obtain ⟨st0, h0, hrun⟩ := bind_ok hrun
        unfold pend at h0
        split at h0
        · simp at h0
        simp only [Except.ok.injEq] at h0; subst h0
        obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
        have hpt := parkTables_other w f.kind wt pk (by assumption) (by assumption) (by assumption)
          (by assumption)
        rw [hw] at hpt
        have hf1 := hK (fun t ht => by rw [hpt]; exact ht) _ st1 (by rfl) h1
        obtain ⟨_, _, hrun⟩ := bind_ok hrun
        exact frameRes_trans f T st _ r (frameRes_nil f T _ r (outs_charge f _ _ _ _ _ r hrun)) hf1
      · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | do_ vars cl acceptGiven accept when_ else_ cases =>
    have hop : ∀ t ∈ opTables w cl.op, t ∈ T := fun t ht => hs t (by simp [stepT, ht])
    have hcT : ∀ t ∈ casesT w f.kind refT subT cases, t ∈ T :=
      fun t ht => hs t (by simp [stepT, ht])
    have viaRest : ∀ st2 : St, Pinv f.kind T st2 → (∀ nn, nn ∉ T → stobj st2 nn = stobj st nn) →
        run w f n st2 (rest ++ X) = .ok r → FrameRes f T st r :=
      fun st2 hP2 hf2 h => frameRes_trans f T st st2 r (cont st2 rest r h hrest hP2) hf2
    have viaCase : ∀ st2 : St, Pinv f.kind T st2 → (∀ nn, nn ∉ T → stobj st2 nn = stobj st nn) →
        ∀ opt ss, (opt, ss) ∈ cases → run w f n st2 ss = .ok r → FrameRes f T st r :=
      fun st2 hP2 hf2 opt ss hm h => frameRes_trans f T st st2 r
        (branch st2 ss r h (fun t ht => hcT t (mem_casesT w f.kind refT subT cases opt ss hm t ht)) hP2) hf2
    have viaRef : ∀ st2 : St, Pinv f.kind T st2 → (∀ nn, nn ∉ T → stobj st2 nn = stobj st nn) →
        ∀ ss, (ss = f.refusal ∨ ∃ rs, ss = [.stop rs none]) → run w f n st2 ss = .ok r →
        FrameRes f T st r := by
      intro st2 hP2 hf2 ss hss h
      rcases hss with rfl | ⟨rs, rfl⟩
      · exact frameRes_trans f T st st2 r
          (hR (fun t ht => hs t (by simp [stepT, ht])) n (Nat.le_refl _) st2 r h hP2) hf2
      · exact frameRes_trans f T st st2 r (hStop (hs _ (by simp [stepT])) st2 rs r h hP2) hf2
    rw [run] at hrun
    dsimp only at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hf1, hc1⟩ := flush_T w f.kind f rfl T st st1 hP h1
    obtain ⟨op, hop', hrun⟩ := bind_ok hrun
    have hfo := findOp_spec w _ op hop'
    rcases when_ with _ | e
    · dsimp only at hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      rw [if_neg (by decide)] at hrun
      obtain ⟨o, _, hrun⟩ := bind_ok hrun
      obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
      obtain ⟨hp2, hn2, hs2⟩ := bind_frame w cl.op op st1 st2 vars _ hfo h2
      have hP2 : Pinv f.kind T st2 := Or.inl ⟨hp2.trans hc1.1, hn2.trans hc1.2⟩
      have hf2 : ∀ nn, nn ∉ T → stobj st2 nn = stobj st nn :=
        fun nn hn => (hs2 nn (fun hm => hn (hop nn hm))).trans (hf1 nn hn)
      do_tail_frame
    · dsimp only at hrun
      obtain ⟨wv, _, hrun⟩ := bind_ok hrun
      obtain ⟨skip, hskip, hrun⟩ := bind_ok hrun
      simp only [pure, Except.pure, Except.ok.injEq] at hskip; subst hskip
      split at hrun
      · obtain ⟨vs, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        simp only [pure, Except.pure, Except.ok.injEq] at h2; subst h2
        have hP2 : Pinv f.kind T ({ st1 with vars := vars.zip vs ++ st1.vars } : St) := Or.inl hc1
        have hf2 : ∀ nn, nn ∉ T → stobj ({ st1 with vars := vars.zip vs ++ st1.vars } : St) nn =
            stobj st nn := hf1
        do_tail_frame
      · obtain ⟨o, _, hrun⟩ := bind_ok hrun
        obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
        obtain ⟨hp2, hn2, hs2⟩ := bind_frame w cl.op op st1 st2 vars _ hfo h2
        have hP2 : Pinv f.kind T st2 := Or.inl ⟨hp2.trans hc1.1, hn2.trans hc1.2⟩
        have hf2 : ∀ nn, nn ∉ T → stobj st2 nn = stobj st nn :=
          fun nn hn => (hs2 nn (fun hm => hn (hop nn hm))).trans (hf1 nn hn)
        do_tail_frame
  | issue cl ok refused =>
    have mem : ∀ t, t ∈ stepT w f.kind refT subT (.issue cl ok refused) → t ∈ T := hs
    simp only [stepT, List.mem_append, List.mem_cons] at mem
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hf1, hc1⟩ := flush_T w f.kind f rfl T st st1 hP h1
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    obtain ⟨st2, h2, hrun⟩ := bind_ok hrun
    obtain ⟨hp2, hn2, hs2⟩ := call_frame w f.kind st1 st2 cl o _ ho h2
    have hP2 : Pinv f.kind T st2 := Or.inl ⟨hp2.trans hc1.1, hn2.trans hc1.2⟩
    have hf2 : ∀ nn, nn ∉ T → stobj st2 nn = stobj st nn :=
      fun nn hn => (hs2 nn (fun hm => hn (mem nn (by simp [hm])))).trans (hf1 nn hn)
    obtain ⟨code, _, hrun⟩ := bind_ok hrun
    have hrefd : ∀ t ∈ stepsT w f.kind refT subT refused, t ∈ T := fun t ht => mem t (by simp [ht])
    have hOne : ∀ (t : Step), (∀ x ∈ stepsT w f.kind refT subT [t], x ∈ T) →
        ∀ m, m ≤ n → ∀ (st' : St) (r' : Res), run w f m st' [t] = .ok r' → Pinv f.kind T st' →
        FrameRes f T st' r' := by
      intro t ht m hm st' r' h hP'
      exact ih m (Nat.lt_succ_of_le hm) f st' [t] [] refT r' rfl hrefT (by simpa using h) ht hP'
        (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
    split at hrun
    · exact frameRes_trans f T st st2 r (branch st2 ok r hrun (fun t ht => mem t (by simp [ht])) hP2) hf2
    split at hrun
    · have := ih n (Nat.lt_succ_self n) f st2 refused [.park "OPERATION" none none none] refT r rfl hrefT
        hrun hrefd hP2 (fun m hm st' r' h hP' => hOne _ (fun x hx => mem x (by
          simp [stepsT, stepT, parkTables] at hx; simp [hx])) m hm st' r' h hP')
      exact frameRes_trans f T st st2 r this hf2
    · have hXr : ∀ fuel', fuel' ≤ n → ∀ (st' : St) (r' : Res),
          run w f fuel' st' (if f.refusal.isEmpty = true then [Step.halt] else f.refusal) = .ok r' →
          Pinv f.kind T st' → FrameRes f T st' r' := by
        intro m hm st' r' h hP'
        split at h
        · exact hOne _ (fun x hx => mem x (by simp [stepsT, stepT] at hx; simp [hx])) m hm st' r' h hP'
        · exact hR (fun t ht => mem t (by simp [ht])) m hm st' r' h hP'
      exact frameRes_trans f T st st2 r
        (ih n (Nat.lt_succ_self n) f st2 refused _ refT r rfl hrefT hrun hrefd hP2 hXr) hf2
  | repeat_ nE body until_ =>
    have hbody : ∀ t ∈ stepsT w f.kind refT subT body, t ∈ T := fun t ht => hs t (by simpa [stepT] using ht)
    have hloop : ∀ m, m ≤ n → ∀ (kk : Nat) (s0 : St) (out : St × Nat),
        run.loop w f body until_ m kk s0 = .ok out → ∀ nn, nn ∉ T → stobj out.1 nn = stobj s0 nn := by
      intro m
      induction m with
      | zero => intro _ kk s0 out h; unfold run.loop at h; nomatch h
      | succ m' ihm =>
        intro hm kk s0 out h
        cases kk with
        | zero =>
          unfold run.loop at h
          simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ _; rfl
        | succ kk' =>
          unfold run.loop at h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨reads, _, h⟩ := bind_ok h
          obtain ⟨uv, _, h⟩ := bind_ok h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; intro _ _; rfl
          · obtain ⟨res, hres, h⟩ := bind_ok h
            cases res with
            | done _ => simp [throw, throwThe, MonadExceptOf.throw] at h
            | again st' =>
              have hX1 : ∀ fuel', fuel' ≤ m' → ∀ (st'' : St) (r'' : Res),
                  run w f fuel' st'' [.repeatNext] = .ok r'' → Pinv f.kind T st'' →
                  FrameRes f T st'' r'' := by
                intro m'' _ st'' r'' h'' hP''
                cases m'' with
                | zero => simp [run] at h''
                | succ m3 =>
                  simp only [run] at h''
                  obtain ⟨st4, h4, h''⟩ := bind_ok h''
                  simp only [pure, Except.pure, Except.ok.injEq] at h''; subst h''
                  exact (flush_T w f.kind f rfl T st'' st4 hP'' h4).1
              have hpass := ih m' (by omega) f
                ({ stobjs := s0.stobjs, vars := reads ++ f.base } : St) body [.repeatNext] refT
                (.again st') rfl hrefT hres hbody (Or.inl ⟨rfl, rfl⟩) hX1
              have hnext := ihm (by omega) kk' { s0 with stobjs := st'.stobjs } out h
              intro nn hn
              exact (hnext nn hn).trans (hpass nn hn)
    simp only [run] at hrun
    obtain ⟨st1, h1, hrun⟩ := bind_ok hrun
    obtain ⟨hf1, hc1⟩ := flush_T w f.kind f rfl T st st1 hP h1
    obtain ⟨nv, _, hrun⟩ := bind_ok hrun
    obtain ⟨lp, hlp, hrun⟩ := bind_ok hrun
    obtain ⟨per, _, hrun⟩ := bind_ok hrun
    have hfl := hloop n (Nat.le_refl _) _ st1 lp hlp
    refine frameRes_trans f T st _ r (cont _ rest r hrun hrest ?_)
      (fun nn hn => (hfl nn hn).trans (hf1 nn hn))
    rcases hP with ⟨_, hnx⟩ | hK
    · exact Or.inl ⟨rfl, hnx⟩
    · exact Or.inr hK

theorem mapM_spec (g : String → Except String Val) :
    ∀ (l : List String) (ts : List Val), l.mapM g = .ok ts →
      ts.length = l.length ∧ ∀ i (hi : i < l.length), ∃ x, ts[i]? = some x ∧ g l[i] = .ok x := by
  intro l
  induction l with
  | nil => intro ts h; simp [pure, Except.pure] at h; subst h; simp
  | cons a l ih =>
    intro ts h
    simp only [List.mapM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨ts', hts', h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨hl, hi⟩ := ih ts' hts'
    refine ⟨by simp [hl], fun i hi' => ?_⟩
    cases i with
    | zero => exact ⟨x, rfl, hx⟩
    | succ i => exact hi i (by simpa using hi')

theorem stobj_zip (l : List String) (vs : List Val) (hnd : l.Nodup) (vars : Env) :
    ∀ i (hi : i < l.length) (hv : i < vs.length),
      stobj ({ stobjs := l.zip vs, vars } : St) l[i] = .ok vs[i] := by
  induction l generalizing vs with
  | nil => intro i hi; simp at hi
  | cons a l ih =>
    intro i hi hv
    cases vs with
    | nil => simp at hv
    | cons v vs =>
      rw [List.nodup_cons] at hnd
      cases i with
      | zero => simp [stobj]
      | succ i =>
        have h1 := ih vs hnd.2 i (by simpa using hi) (by simpa using hv)
        have hil : i < l.length := by simpa using hi
        have hne : (a == l[i]) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; exact hnd.1 (he ▸ List.getElem_mem hil)
        simpa [stobj, hne] using h1

/-- **Theorem (`runArm_frame`)**: when an arm's declaration has derived children `D` (and the
kind's tuple names each child once), every successful run of the interpreter returns the tuple's
children as its last results, and each child outside `D` is returned exactly as it was passed in. -/
theorem runArm_frame (k : Kind) (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat) (v : Val)
    (D : List String) (hD : derivedTables w k a = some D) (hnd : k.tuple.Nodup)
    (hrun : runArm w k a observe args fuel = .ok v) :
    ∃ pre ts, v.toList = pre ++ ts ∧ ts.length = k.tuple.length ∧
      ∀ i (hi : i < k.tuple.length), k.tuple[i] ∉ D →
        ts[i]? = (args.drop (if observe then 10 else 5))[i]? := by
  unfold derivedTables at hD
  split at hD
  · rename_i decl hread
    dsimp only at hD
    split at hD
    · rename_i hsub
      split at hD
      · rename_i refT hrefT
        simp only [Option.some.injEq] at hD; subst hD
        have key : ∀ (names : List String), names.length = (if observe then 10 else 5) →
            ∀ (stobjs : List (String × Val)) (base : Env) (reads : Env) (v' : Val),
            args.length = names.length + k.tuple.length →
            stobjs = k.tuple.zip (args.drop names.length) →
            run w { kind := k, observe, refusal := decl.onRefusal, base } fuel
              { stobjs, vars := reads ++ base } decl.steps = .ok (.done v') →
            ∃ pre ts, v'.toList = pre ++ ts ∧ ts.length = k.tuple.length ∧
              ∀ i (hi : i < k.tuple.length), k.tuple[i] ∉ stepsT w k refT
                (subTablesN w k (k.subarms.length + 1)) decl.steps →
                ts[i]? = (args.drop (if observe then 10 else 5))[i]? := by
          intro names hnl stobjs base reads v' hlen hst hres
          have hfr := run_frame w k _ hsub (stepsT w k refT (subTablesN w k (k.subarms.length + 1))
            decl.steps) fuel _ _ decl.steps [] refT (.done v') rfl hrefT
            (by simpa using hres) (fun t ht => ht) (Or.inl ⟨rfl, rfl⟩)
            (fun _ _ _ _ h => absurd h (run_nil_ne w _ _ _ _))
          obtain ⟨stF, ⟨pre, ts, hv, hts⟩, hf⟩ := hfr
          obtain ⟨htl, hti⟩ := mapM_spec _ _ _ hts
          refine ⟨pre, ts, by rw [hv]; exact Pathway.toList_ofList _, htl, fun i hi hnot => ?_⟩
          obtain ⟨x, hx, hgx⟩ := hti i hi
          rw [hx]
          have h2 := hf _ hnot
          rw [hgx] at h2
          have hdl : i < (args.drop names.length).length := by simp; omega
          have h3 := stobj_zip k.tuple (args.drop names.length) hnd (reads ++ base) i hi hdl
          rw [← hst] at h3
          rw [h3] at h2
          cases h2
          rw [← hnl]
          simp [List.getElem?_eq_getElem hdl]
        cases observe
        all_goals
          simp only [runArm, Bool.false_eq_true, if_false, if_true] at hrun
          split at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          split at hrun
          · simp [throw, throwThe, MonadExceptOf.throw] at hrun
          rename_i hlen
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
            exact key _ (by simp) _ _ _ _ (by simpa using hlen) rfl hres
      · cases hD
    · cases hD
  · cases hD

end Fn2.Arms.Frame

end
