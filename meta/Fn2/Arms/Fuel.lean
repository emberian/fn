module

public import Fn2.Arms
public import Fn2.ArmsLemmas
public import Fn2.Arms.Bound
public import Fn2.Arms.Cost
public import Fn2.Arms.Frame
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.Fuel: a fuel bound read off a declaration, and fuel adequacy over the interpreter

`derivedFuel w k a` bounds the fuel `runArm` needs for arm `a`: one unit per step of the longest
path, a sub-arm's bound where a path enters it (the `:goto` graph must be acyclic: a cycle gives
`none`), the arm's refusal where a path can reach it (a refusal that can re-enter itself gives
`none`), and for a `:repeat` its count's static upper bound times its pass's bound.
-/

namespace Fn2.Arms.Fuel
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Bound Fn2.Arms.Cost

set_option autoImplicit false

def omax (a b : Option Nat) : Option Nat := do pure (max (← a) (← b))

section
variable (w : World) (k : Kind)

/-- The static upper bound of a `:repeat`'s pass count (`nfix` of its count expression). -/
def repCount (n : Expr) : Option Nat := (ival w k [] n).map fun b => b.2.toNat

mutual
/-- The fuel a path needs after a step's own unit, given what the rest of the path needs. -/
def stepFuel (refF : Option Nat) (subF : String → Option Nat) (restF : Option Nat) :
    Step → Option Nat
  | .let_ _ _ | .set _ | .next _ | .wakeRow _ => restF
  | .charge _ _ _ _ | .idle | .yield | .wait _ _ | .halt | .park _ _ _ _ _ | .stop _ _
  | .wake | .nowake | .repeatNext => some 0
  | .goto name => subF name
  | .if_ _ a b => omax (stepsFuel refF subF a (some 1)) (stepsFuel refF subF b (some 1))
  | .cond clauses => clausesFuel refF subF clauses
  | .case_ _ arms => casesFuel refF subF arms
  | .do_ _ _ _ _ _ _ cases =>
    omax restF (omax (casesFuel refF subF cases)
      (if cases.any (·.1.isNone) then some 0 else omax refF (some 1)))
  | .issue _ ok refused =>
    omax (stepsFuel refF subF ok (some 1))
      (omax (stepsFuel refF subF refused (some 1)) (stepsFuel refF subF refused (omax (some 1) refF)))
  | .repeat_ n body _ => do
    let K ← repCount w k n
    let P ← stepsFuel refF subF body (some 1)
    omax restF (some (K + max P 1))

def stepsFuel (refF : Option Nat) (subF : String → Option Nat) :
    List Step → Option Nat → Option Nat
  | [], kont => kont
  | s :: rest, kont => (stepFuel refF subF (stepsFuel refF subF rest kont) s).map (· + 1)

def casesFuel (refF : Option Nat) (subF : String → Option Nat) :
    List (Option (List Val) × List Step) → Option Nat
  | [] => some 0
  | (_, ss) :: cs => omax (stepsFuel refF subF ss (some 1)) (casesFuel refF subF cs)

def clausesFuel (refF : Option Nat) (subF : String → Option Nat) :
    List (Expr × List Step) → Option Nat
  | [] => some 0
  | (_, ss) :: cs => omax (stepsFuel refF subF ss (some 1)) (clausesFuel refF subF cs)
end

/-- The refusal's fuel (at least 1); its own steps may not reach the refusal again. -/
def refFuel (subF : String → Option Nat) (R : List Step) : Option Nat :=
  if R.isEmpty then some 1 else (stepsFuel w k none subF R (some 1)).map (max 1)

/-- The sub-arms' fuel, `d` levels of `:goto` deep (`none` past the depth: a cycle). -/
def subFuelN : Nat → String → Option Nat
  | 0, _ => none
  | d + 1, name =>
    match k.subarms.find? (·.tag == name) with
    | some sub => match sub.read with
      | .ok decl => do
        let rf ← refFuel w k (subFuelN d) decl.onRefusal
        stepsFuel w k (some rf) (subFuelN d) decl.steps (some 1)
      | .error _ => none
    | none => none

/-- **The fuel an arm needs** (`none` where no bound is derived: a `:goto` cycle, a refusal
that can re-enter itself, a `:repeat` count without a static bound). -/
def derivedFuel (a : Arm) : Option Nat :=
  match a.read with
  | .ok decl => do
    let subF := subFuelN w k (k.subarms.length + 1)
    let rf ← refFuel w k subF decl.onRefusal
    stepsFuel w k (some rf) subF decl.steps (some 1)
  | .error _ => none

end

/-! ## Fuel adequacy over the interpreter -/

theorem bind_tail {ε α β : Type} {m : Except ε α} {g g' : α → Except ε β} {r : β}
    (h : (m >>= g) = .ok r) (hg : ∀ x, m = .ok x → g x = .ok r → g' x = .ok r) :
    (m >>= g') = .ok r := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok x => exact hg x rfl h

theorem omax_some {a b : Option Nat} {M : Nat} (h : omax a b = some M) :
    ∃ x y, a = some x ∧ b = some y ∧ M = max x y := by
  cases a <;> cases b <;> simp [omax, bind, Option.bind, pure] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem map_succ_some {a : Option Nat} {F : Nat} (h : a.map (· + 1) = some F) :
    ∃ G, a = some G ∧ F = G + 1 := by
  cases a <;> simp at h; exact ⟨_, rfl, h.symm⟩

section
variable (w : World) (k : Kind)

/-- `X` returns, at every fuel from `K` on, whatever it returns at any fuel. -/
def AdqX (f : Frame) (X : List Step) (K : Nat) : Prop :=
  ∀ (a b : Nat) (st : St) (r : Res), run w f a st X = .ok r → K ≤ b → run w f b st X = .ok r

def RefOK (refF : Option Nat) (f : Frame) : Prop :=
  ∀ RF, refF = some RF → 1 ≤ RF ∧ AdqX w f f.refusal RF

def SubOK (subF : String → Option Nat) : Prop :=
  ∀ name SF, subF name = some SF → ∀ sub, k.subarms.find? (·.tag == name) = some sub →
    ∀ d, sub.read = .ok d → ∀ f : Frame, f.kind = k → f.refusal = d.onRefusal → AdqX w f d.steps SF

theorem adqX_mono (f : Frame) (X : List Step) (K K' : Nat) (h : AdqX w f X K) (hK : K ≤ K') :
    AdqX w f X K' := fun a b st r h1 h2 => h a b st r h1 (by omega)

theorem adqX_nil (f : Frame) (K : Nat) : AdqX w f [] K := fun a _ st r h _ => by
  cases a <;> simp [run] at h

/-- A step that ends its path without running another: its result does not depend on fuel. -/
theorem adqX_term (f : Frame) (t : Step) (L : List Step)
    (ht : ∀ n m st, run w f (n + 1) st (t :: L) = run w f (m + 1) st (t :: L)) :
    AdqX w f (t :: L) 1 := by
  intro a b st r h hb
  cases a with
  | zero => simp [run] at h
  | succ a =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [← ht a b st]; exact h

theorem casesFuel_mem (refF : Option Nat) (subF : String → Option Nat)
    (cs : List (Option (List Val) × List Step)) (C : Nat) (h : casesFuel w k refF subF cs = some C)
    (opt : Option (List Val)) (ss : List Step) (hm : (opt, ss) ∈ cs) :
    ∃ G, stepsFuel w k refF subF ss (some 1) = some G ∧ G ≤ C := by
  induction cs generalizing C with
  | nil => simp at hm
  | cons c cs ih =>
    obtain ⟨o, s⟩ := c
    simp only [casesFuel] at h
    obtain ⟨x, y, hx, hy, rfl⟩ := omax_some h
    rcases List.mem_cons.mp hm with he | he
    · cases he; exact ⟨x, hx, by omega⟩
    · obtain ⟨G, hG, hle⟩ := ih y hy he; exact ⟨G, hG, by omega⟩

theorem clausesFuel_mem (refF : Option Nat) (subF : String → Option Nat)
    (cs : List (Expr × List Step)) (C : Nat) (h : clausesFuel w k refF subF cs = some C)
    (e : Expr) (ss : List Step) (hm : (e, ss) ∈ cs) :
    ∃ G, stepsFuel w k refF subF ss (some 1) = some G ∧ G ≤ C := by
  induction cs generalizing C with
  | nil => simp at hm
  | cons c cs ih =>
    obtain ⟨o, s⟩ := c
    simp only [clausesFuel] at h
    obtain ⟨x, y, hx, hy, rfl⟩ := omax_some h
    rcases List.mem_cons.mp hm with he | he
    · cases he; exact ⟨x, hx, by omega⟩
    · obtain ⟨G, hG, hle⟩ := ih y hy he; exact ⟨G, hG, by omega⟩

set_option hygiene false in
local macro "peel" : tactic => `(tactic| (refine bind_tail hrun (fun _ _ hrun => ?_)))

set_option hygiene false in
local macro "adq_tail" : tactic => `(tactic| (
  rcases hA : op.answers with _ | _ | l
  · simp only [hA] at hrun ⊢; exact viaRest _ hrun
  all_goals
    simp only [hA] at hrun ⊢
    first
    | (obtain ⟨_, hth, _⟩ := bind_ok hrun; simp [throw, throwThe, MonadExceptOf.throw] at hth)
    | (peel
       split at hrun
       · rename_i hin; try rw [if_pos hin]
         exact viaRest _ hrun
       · rename_i hin; try rw [if_neg hin]
         split at hrun
         · rename_i hfind; try rw [hfind]
           exact viaCase _ _ _ (List.mem_of_find?_eq_some hfind) hrun
         · rename_i hf1; try rw [hf1]
           split at hrun
           · rename_i hfind; try rw [hfind]
             exact viaCase _ _ _ (List.mem_of_find?_eq_some hfind) hrun
           · rename_i hf2; try rw [hf2]
             obtain ⟨h1b, href⟩ := hno hf2
             split at hrun
             · rename_i hne; try rw [if_pos hne]
               rcases faultRoute_cases _ _ _ f.refusal with he | he <;> rw [he] at hrun <;> (try rw [he])
               · exact href _ hrun
               · exact viaStop _ _ h1b hrun
             · rename_i hne; try rw [if_neg hne]
               exact viaStop _ _ h1b hrun)))

set_option maxHeartbeats 1000000 in
/-- **Fuel adequacy (`run_adq`)**: a path whose derived fuel is `F` (with its continuation `X`
adequate from `K`), and that returns `r` at some fuel, returns `r` at every fuel from `F` on. -/
theorem run_adq (subF : String → Option Nat) (hsub : SubOK w k subF) :
    ∀ (a : Nat) (f : Frame) (refF : Option Nat) (ss X : List Step) (kont : Option Nat) (F b : Nat)
      (st : St) (r : Res),
      f.kind = k → RefOK w refF f → stepsFuel w k refF subF ss kont = some F →
      (∀ K, kont = some K → AdqX w f X K) →
      run w f a st (ss ++ X) = .ok r → F ≤ b → run w f b st (ss ++ X) = .ok r := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
  intro f refF ss X kont F b st r hk hR hF hX hrun hb
  cases ss with
  | nil =>
    simp only [stepsFuel] at hF
    simpa using hX F hF a b st r (by simpa using hrun) hb
  | cons s rest =>
  cases a with
  | zero => simp [run] at hrun
  | succ a' =>
  simp only [stepsFuel] at hF
  obtain ⟨G, hG, rfl⟩ := map_succ_some hF
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hb' : G ≤ b' := by omega
  rw [List.cons_append] at hrun ⊢
  -- a path that ends without the continuation
  have go : ∀ (f' : Frame) (st' : St) (ss' : List Step) (r' : Res) (G' : Nat), f'.kind = k →
      RefOK w refF f' → stepsFuel w k refF subF ss' (some 1) = some G' → G' ≤ b' →
      run w f' a' st' ss' = .ok r' → run w f' b' st' ss' = .ok r' := by
    intro f' st' ss' r' G' hk' hR' h1 h2 h3
    simpa using ih a' (Nat.lt_succ_self a') f' refF ss' [] (some 1) G' b' st' r' hk' hR' h1
      (fun K _ => adqX_nil w f' K) (by simpa using h3) h2
  -- the rest of the path, with the continuation
  have cont : ∀ (st' : St) (r' : Res), (∀ R', stepsFuel w k refF subF rest kont = some R' → R' ≤ b') →
      (∃ R', stepsFuel w k refF subF rest kont = some R') →
      run w f a' st' (rest ++ X) = .ok r' → run w f b' st' (rest ++ X) = .ok r' := by
    intro st' r' hle ⟨R', hR'⟩ h3
    exact ih a' (Nat.lt_succ_self a') f refF rest X kont R' b' st' r' hk hR hR' hX h3 (hle R' hR')
  have term : ∀ (t : Step) (L : List Step),
      (∀ n m st, run w f (n + 1) st (t :: L) = run w f (m + 1) st (t :: L)) →
      run w f (a' + 1) st (t :: L) = .ok r → run w f (b' + 1) st (t :: L) = .ok r :=
    fun t L ht h => by rw [← ht a' b' st]; exact h
  cases s with
  | let_ x e =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    peel
    exact cont _ _ (fun R' h => by rw [hG] at h; cases h; exact hb') ⟨G, hG⟩ hrun
  | set pairs =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    peel
    exact cont _ _ (fun R' h => by rw [hG] at h; cases h; exact hb') ⟨G, hG⟩ hrun
  | next ph =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    rename_i hc
    try rw [if_neg hc]
    peel
    exact cont _ _ (fun R' h => by rw [hG] at h; cases h; exact hb') ⟨G, hG⟩ hrun
  | wakeRow e =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    split at hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    rename_i hc
    try rw [if_neg hc]
    peel; peel; peel; peel; peel
    exact cont _ _ (fun R' h => by rw [hG] at h; cases h; exact hb') ⟨G, hG⟩ hrun
  | if_ c x y =>
    simp only [stepFuel] at hG
    obtain ⟨gx, gy, hx, hy, rfl⟩ := omax_some hG
    simp only [run] at hrun ⊢
    peel
    split at hrun
    · rename_i hc; try rw [if_pos hc]
      exact go f _ _ _ gx hk hR hx (by omega) hrun
    · rename_i hc; try rw [if_neg hc]
      exact go f _ _ _ gy hk hR hy (by omega) hrun
  | cond clauses =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    obtain ⟨o, ho, hrun⟩ := bind_ok hrun
    rw [ho]
    simp only [except_ok_bind]
    rcases o with _ | ⟨e, ss⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · obtain ⟨G', h1, h2⟩ := clausesFuel_mem w k refF subF clauses G hG e ss
        (Cost.findM_mem _ _ _ ho)
      exact go f _ _ _ G' hk hR h1 (by omega) hrun
  | case_ key arms =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    peel
    split at hrun
    · rename_i cs ss hfind
      obtain ⟨G', h1, h2⟩ := casesFuel_mem w k refF subF arms G hG cs ss
        (List.mem_of_find?_eq_some hfind)
      exact go f _ _ _ G' hk hR h1 (by omega) hrun
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | goto name =>
    simp only [stepFuel] at hG
    simp only [run] at hrun ⊢
    peel
    split at hrun
    · rename_i sub hfind
      simp only [except_pure_bind] at hrun ⊢
      peel; peel; peel
      obtain ⟨d, hd, hrun⟩ := bind_ok hrun
      rw [hd]
      simp only [except_ok_bind] at hrun ⊢
      rw [hk] at hfind
      exact hsub name G hG sub hfind d hd { f with refusal := d.onRefusal } hk rfl _ _ _ _ hrun hb'
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | repeatNext => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | charge _ _ _ _ => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | idle => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | yield => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | wait _ _ => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | halt => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | park _ _ _ _ _ => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | stop _ _ => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | wake => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | nowake => exact term _ _ (fun _ _ _ => by simp only [run]) hrun
  | do_ vars cl acceptGiven accept when_ else_ cases =>
    simp only [stepFuel] at hG
    obtain ⟨gr, g2, hgr, hg2, rfl⟩ := omax_some hG
    obtain ⟨gc, g3, hgc, hg3, rfl⟩ := omax_some hg2
    have hbr : gr ≤ b' := Nat.le_trans (Nat.le_max_left _ _) hb'
    have hbc : gc ≤ b' := Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hb'
    have hb3 : g3 ≤ b' := Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hb'
    have viaRest : ∀ st2, run w f a' st2 (rest ++ X) = .ok r → run w f b' st2 (rest ++ X) = .ok r :=
      fun st2 h => cont st2 r (fun R' h' => by rw [hgr] at h'; cases h'; exact hbr) ⟨gr, hgr⟩ h
    have viaCase : ∀ st2 opt ss, (opt, ss) ∈ cases → run w f a' st2 ss = .ok r →
        run w f b' st2 ss = .ok r := by
      intro st2 opt ss hm h
      obtain ⟨G', h1, h2⟩ := casesFuel_mem w k refF subF cases gc hgc opt ss hm
      exact go f _ _ _ G' hk hR h1 (Nat.le_trans h2 hbc) h
    have hno : cases.find? (·.1.isNone) = none → 1 ≤ b' ∧ ∀ st2, run w f a' st2 f.refusal = .ok r →
        run w f b' st2 f.refusal = .ok r := by
      intro hnone
      have hany : cases.any (·.1.isNone) = false := by
        rw [List.any_eq_false]; intro x hx hxn
        exact absurd hxn (by simpa using List.find?_eq_none.mp hnone x hx)
      rw [hany] at hg3
      simp only [Bool.false_eq_true, if_false] at hg3
      obtain ⟨RF, one, hRF, hone, rfl⟩ := omax_some hg3
      cases hone
      obtain ⟨_, hA⟩ := hR RF hRF
      have h1 : RF ≤ b' := Nat.le_trans (Nat.le_max_left _ _) hb3
      exact ⟨Nat.le_trans (Nat.le_max_right _ _) hb3, fun st2 h => hA a' b' st2 r h h1⟩
    have viaStop : ∀ st2 rs, 1 ≤ b' → run w f a' st2 [.stop rs none] = .ok r →
        run w f b' st2 [.stop rs none] = .ok r := fun st2 rs h1 h =>
      go f _ _ _ 1 hk hR (by simp [stepsFuel, stepFuel]) h1 h
    have viaCase2 : ∀ st2 (p : Option (List Val) × List Step → Bool) opt ss,
        cases.find? p = some (opt, ss) → run w f a' st2 ss = .ok r → run w f b' st2 ss = .ok r :=
      fun st2 p opt ss hf h => viaCase st2 opt ss (List.mem_of_find?_eq_some hf) h
    rcases vars with _ | ⟨v, tl⟩
    all_goals
      simp only [run] at hrun ⊢
      peel
      obtain ⟨op, hop, hrun⟩ := bind_ok hrun
      rw [hop]; simp only [except_ok_bind] at hrun ⊢
    all_goals rcases when_ with _ | e
    all_goals rcases hA : op.answers with _ | _ | l
    all_goals simp only [hA] at hrun ⊢
    all_goals repeat' (first
      | (refine viaRest _ ?_; exact hrun)
      | (refine viaCase2 _ _ _ _ ?_ ?_ <;> first | exact hrun | assumption)
      | (obtain ⟨_, hth, _⟩ := bind_ok hrun; simp [throw, throwThe, MonadExceptOf.throw] at hth; done)
      | peel
      | (split at hrun <;> rename_i hh2 <;> split <;> rename_i hh1 <;>
          (try first | contradiction | (rw [hh1] at hh2; cases hh2)))
      | (split <;> rename_i hh1 <;> simp only [hh1, ↓reduceIte] at hrun))
    all_goals
      have hq : cases.find? (·.1.isNone) = none := by assumption
      obtain ⟨h1b, href⟩ := hno hq
      first
      | (rcases faultRoute_cases _ _ _ f.refusal with he | he <;> rw [he] at hrun ⊢
         · refine href _ ?_; exact hrun
         · refine viaStop _ _ h1b ?_; exact hrun)
      | (refine viaStop _ _ h1b ?_; exact hrun)
  | issue cl ok refused =>
    simp only [stepFuel] at hG
    obtain ⟨g1, g23, h1, h23, rfl⟩ := omax_some hG
    obtain ⟨g2, g3, h2, h3, rfl⟩ := omax_some h23
    simp only [run] at hrun ⊢
    peel; peel; peel; peel
    split at hrun
    · rename_i hok; try rw [if_pos hok]
      exact go f _ _ _ g1 hk hR h1 (by omega) hrun
    · rename_i hok; try rw [if_neg hok]
      split at hrun
      · rename_i hex; try rw [if_pos hex]
        exact ih a' (Nat.lt_succ_self a') f refF refused _ (some 1) g2 b' _ r hk hR h2
          (fun K hK => by
            cases hK
            exact adqX_term w f _ _ (fun _ _ _ => by simp only [run]))
          hrun (by omega)
      · rename_i hex; try rw [if_neg hex]
        refine ih a' (Nat.lt_succ_self a') f refF refused _ _ g3 b' _ r hk hR h3 (fun K hK => ?_)
          hrun (by omega)
        cases hRF : refF with
        | none => rw [hRF] at hK; simp [omax, bind, Option.bind] at hK
        | some RF =>
          rw [hRF] at hK
          simp only [omax, bind, Option.bind, pure, Option.some.injEq] at hK
          subst hK
          obtain ⟨_, hA⟩ := hR RF hRF
          split
          · exact adqX_mono w f _ 1 _ (adqX_term w f _ _ (fun _ _ _ => by simp only [run]))
              (by omega)
          · exact adqX_mono w f _ RF _ hA (by omega)
  | repeat_ nE body until_ =>
    simp only [stepFuel] at hG
    obtain ⟨Kc, hKc, hG⟩ := Option.bind_eq_some_iff.mp hG
    obtain ⟨P, hP, hG⟩ := Option.bind_eq_some_iff.mp hG
    obtain ⟨gr, gl, hgr, hgl, rfl⟩ := omax_some hG
    simp only [Option.some.injEq] at hgl; subst hgl
    have hpass : ∀ c d (s0 : St) (res : Res), c < a' + 1 → P ≤ d →
        run w f c s0 (body ++ [.repeatNext]) = .ok res →
        run w f d s0 (body ++ [.repeatNext]) = .ok res := fun c d s0 res hc hd h =>
      ih c hc f refF body [.repeatNext] (some 1) P d s0 res hk hR hP
        (fun K hK => by cases hK; exact adqX_term w f _ _ (fun _ _ _ => by simp only [run])) h hd
    have hloop : ∀ (kk c d : Nat) (s0 : St) (out : St × Nat), c ≤ a' → kk + max P 1 ≤ d →
        run.loop w f body until_ c kk s0 = .ok out → run.loop w f body until_ d kk s0 = .ok out := by
      intro kk
      induction kk with
      | zero =>
        intro c d s0 out hc hd h
        cases c with
        | zero => unfold run.loop at h; nomatch h
        | succ c =>
          obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          unfold run.loop at h ⊢; exact h
      | succ kk ihk =>
        intro c d s0 out hc hd h
        cases c with
        | zero => unfold run.loop at h; nomatch h
        | succ c =>
          obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
          unfold run.loop at h ⊢
          refine bind_tail h (fun _ _ h => ?_)
          refine bind_tail h (fun _ _ h => ?_)
          refine bind_tail h (fun _ _ h => ?_)
          refine bind_tail h (fun _ _ h => ?_)
          split at h
          · rename_i hu; try rw [if_pos hu]
            exact h
          · rename_i hu; try rw [if_neg hu]
            obtain ⟨res, hres, h⟩ := bind_ok h
            rw [hpass c d _ res (by omega) (by omega) hres]
            simp only [except_ok_bind] at h ⊢
            cases res with
            | done _ => simp [throw, throwThe, MonadExceptOf.throw] at h
            | again st' => exact ihk c d _ out (by omega) (by omega) h
    simp only [run] at hrun ⊢
    peel
    obtain ⟨nv, hnv, hrun⟩ := bind_ok hrun
    rw [hnv]; simp only [except_ok_bind] at hrun ⊢
    have hkk : nv.nfix ≤ Kc := by
      unfold repCount at hKc
      obtain ⟨bnd, hbnd, rfl⟩ := Option.map_eq_some_iff.mp hKc
      rw [← hk] at hbnd
      have := ev_sound w f.kind [] _ nE nv bnd (fun x b h => by simp [senvFind] at h) hnv hbnd
      simp only [Val.nfix, InB] at this ⊢
      omega
    obtain ⟨lp, hlp, hrun⟩ := bind_ok hrun
    rw [hloop _ a' b' _ lp (Nat.le_refl _) (by omega) hlp]
    simp only [except_ok_bind] at hrun ⊢
    peel
    exact cont _ _ (fun R' h => by rw [hgr] at h; cases h; omega) ⟨gr, hgr⟩ hrun

end

end Fn2.Arms.Fuel

end
