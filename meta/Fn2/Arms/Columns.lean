import Fn2.Arms.Inv
import Fn2.Arms.Derive

/-!
# Fn2.Arms.Columns: the columns an arm writes and the phases it reaches, over the interpreter

Two contracts read off a declaration and proved over every run of `Fn2.Arms.run`:

* `runArm_writes_sub`: a column outside `checkedWrites` (and other than `PHASE`) reads back, at
  every slot, as it was passed in;
* `runArm_next_mem`: the `PHASE` column at every slot is either as it was passed in or the value
  of a phase in `checkedNext`.

Both are instances of `Inv.runArm_inv`. What they need of the world is `TableFacts`: a column's
setter leaves every other column's getter as it was and makes its own getter read either the old
value or the written one. It is a property of the world's table accessors (the generated ones are
`UPDATE-NTH-ARRAY` and `NTH` over list-valued stobjs, `tableFacts_of_layout`), never of a run.
-/

namespace Fn2.Arms.Columns
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Bound Fn2.Arms.Cost Fn2.Arms.Frame Fn2.Arms.Inv Fn2.Arms.Derive

set_option autoImplicit false

section
variable (w : World) (k : Kind)

/-- Column `c` of `k` at slot (or, for a directory field, id) `s`, read from children `S`
through the world's getter. -/
def colGet (S : String → Except String Val) (c : String) (s : Val) : Except String Val :=
  if directoryFields.contains c then do callFn w ("FN2-MACHINES-" ++ c) [s, ← S "FN2-MACHINES"]
  else do callFn w (k.name ++ "-" ++ c) [s, ← S k.name]

/-- **What the column contracts need of the world**: a setter of one column leaves every other
column of the same table, at every slot, as it was; its own column reads back either as it was
or as the value written. -/
structure TableFacts : Prop where
  own : ∀ n c, n ∈ ownCols k → c ∈ ownCols k → ∀ (s v t t' s' : Val),
    callFn w (k.name ++ "-SET-" ++ n) [s, v, t] = .ok t' →
    callFn w (k.name ++ "-" ++ c) [s', t'] = callFn w (k.name ++ "-" ++ c) [s', t] ∨
      (n = c ∧ callFn w (k.name ++ "-" ++ c) [s', t'] = .ok v)
  dir : ∀ n c, n ∈ dirCols k → c ∈ dirCols k → ∀ (s v t t' s' : Val),
    callFn w ("FN2-MACHINES-SET-" ++ n) [s, v, t] = .ok t' →
    callFn w ("FN2-MACHINES-" ++ c) [s', t'] = callFn w ("FN2-MACHINES-" ++ c) [s', t] ∨
      (n = c ∧ callFn w ("FN2-MACHINES-" ++ c) [s', t'] = .ok v)

/-- The kind's shape the contracts read: its tuple names each child once and holds its table and
the directory, and its table is neither the directory nor the control. -/
def kindShape : Bool :=
  decide k.tuple.Nodup && k.tuple.contains k.name && k.tuple.contains "FN2-MACHINES" &&
  k.name != "FN2-MACHINES" && k.name != "FN2-CONTROL"

/-- `v` fits column `c`'s declared type (the checked write's test). -/
def colFits (c : String) (v : Val) : Prop :=
  match k.columns.find? (·.1 == c) with
  | some (_, ty) => ty.fits v = true
  | none => False

/-- Every value the `PHASE` column's type admits is the value of one of the kind's states. -/
def phasesCover : Bool :=
  match k.columns.find? (·.1 == "PHASE") with
  | some (_, .enum n) => (List.range n).all fun i => k.states.any fun p => k.phases.contains (p, (i : Int))
  | _ => false

/-! ## The contracts as checked derivations -/

def primsW (W R : List String) : Prims where
  pairOK n := n == "PHASE" || W.contains n
  nextOK _ := true
  opOK op := (opWrites w k op).all fun n => n == "PHASE" || W.contains n
  dirOK := (dirCols k).all W.contains
  gotoOK := R.contains

/-- **The columns an arm can write** (`PHASE` aside): `derivedWrites`, checked against every step,
refusal and sub-arm (`none` where the check fails). -/
def checkedWrites (a : Arm) : Option (List String) :=
  let W := derivedWrites w k a
  if admArm w (primsW w k W (armReach k a)) k a then some W else none

def primsN (D R : List String) : Prims where
  pairOK n := n != "PHASE" || k.states.all D.contains
  nextOK ph := (nextExprPhases k ph).all D.contains
  opOK op := !(opTables w op).contains k.name
  dirOK := true
  gotoOK := R.contains

/-- **The phases an arm can move a row to**: `derivedNext`, checked against every step, refusal
and sub-arm (`none` where the check fails). -/
def checkedNext (a : Arm) : Option (List String) :=
  let D := derivedNext w k a
  if admArm w (primsN w k D (armReach k a)) k a then some D else none

end

/-! ## Reading a column -/

section
variable (w : World) (k : Kind)

theorem colGet_own (S : String → Except String Val) (c : String) (s t : Val)
    (hc : directoryFields.contains c = false) (ht : S k.name = .ok t) :
    colGet w k S c s = callFn w (k.name ++ "-" ++ c) [s, t] := by
  simp only [colGet, hc, Bool.false_eq_true, if_false, ht, except_ok_bind]

theorem colGet_dir (S : String → Except String Val) (c : String) (s d : Val)
    (hc : directoryFields.contains c = true) (hd : S "FN2-MACHINES" = .ok d) :
    colGet w k S c s = callFn w ("FN2-MACHINES-" ++ c) [s, d] := by
  simp only [colGet, hc, if_true, hd, except_ok_bind]

theorem colGet_congr_own (S S' : String → Except String Val) (c : String)
    (hc : directoryFields.contains c = false) (h : S' k.name = S k.name) (s : Val) :
    colGet w k S' c s = colGet w k S c s := by
  simp only [colGet, hc, Bool.false_eq_true, if_false, h]

theorem colGet_congr_dir (S S' : String → Except String Val) (c : String)
    (hc : directoryFields.contains c = true) (h : S' "FN2-MACHINES" = S "FN2-MACHINES") (s : Val) :
    colGet w k S' c s = colGet w k S c s := by
  simp only [colGet, hc, if_true, h]

theorem kindShape_spec (h : kindShape k = true) :
    k.tuple.Nodup ∧ k.name ∈ k.tuple ∧ "FN2-MACHINES" ∈ k.tuple ∧
      k.name ≠ "FN2-MACHINES" ∧ k.name ≠ "FN2-CONTROL" := by
  simp only [kindShape, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem,
    bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem mem_ownCols (c : String) (hc : c ∈ k.columns.map Prod.fst)
    (hd : directoryFields.contains c = false) : c ∈ ownCols k := by
  simp only [ownCols, List.mem_filter, hd, Bool.not_false, and_true]; exact hc

theorem mem_dirCols (c : String) (hc : c ∈ k.columns.map Prod.fst)
    (hd : directoryFields.contains c = true) : c ∈ dirCols k := by
  simp only [dirCols, List.mem_filter, hd, and_true]; exact hc

/-- A fold of setters over pairs of one table: a column's getter reads as before or as a value
the fold wrote to it. -/
theorem fold_get (get : Val → Val → Except String Val)
    (set : String → Val → Val → Val → Except String Val) (C : List String) (c : String)
    (H : ∀ n, n ∈ C → ∀ (s v t t' s' : Val), set n s v t = .ok t' →
      get s' t' = get s' t ∨ (n = c ∧ get s' t' = .ok v)) (slot : Val) :
    ∀ (ps : List (String × Val)) (t t' : Val), (∀ p ∈ ps, p.1 ∈ C) →
      ps.foldlM (fun t (p : String × Val) => set p.1 slot p.2 t) t = .ok t' →
      ∀ s', get s' t' = get s' t ∨ ∃ v, (c, v) ∈ ps ∧ get s' t' = .ok v := by
  intro ps
  induction ps with
  | nil =>
    intro t t' _ h s'
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact Or.inl rfl
  | cons p ps ih =>
    intro t t' hC h s'
    simp only [List.foldlM_cons] at h
    obtain ⟨t1, h1, h⟩ := bind_ok h
    rcases ih t1 t' (fun q hq => hC q (List.mem_cons_of_mem _ hq)) h s' with he | ⟨v, hv, he⟩
    · rcases H p.1 (hC p (List.mem_cons_self ..)) slot p.2 t t1 s' h1 with h2 | ⟨hpc, h2⟩
      · exact Or.inl (he.trans h2)
      · exact Or.inr ⟨p.2, by rw [← hpc]; exact List.mem_cons_self .., he.trans h2⟩
    · exact Or.inr ⟨v, List.mem_cons_of_mem _ hv, he⟩

theorem fold_eta (g : Val → String × Val → Except String Val) (ps : List (String × Val)) (t : Val) :
    ps.foldlM (fun t (n, v) => g t (n, v)) t = ps.foldlM g t := rfl

end

/-! ## The checked write and the flush, column by column -/

theorem fits_mem (k : Kind) (n : String) (v : Val)
    (h : (match k.columns.find? (·.1 == n) with
      | some (_, ty) => ty.fits v
      | none => false) = true) :
    n ∈ k.columns.map Prod.fst ∧ colFits k n v := by
  unfold colFits
  cases hq : k.columns.find? (·.1 == n) with
  | none => rw [hq] at h; cases h
  | some q =>
    obtain ⟨q1, ty⟩ := q
    rw [hq] at h
    refine ⟨List.mem_map.mpr ⟨(q1, ty), List.mem_of_find?_eq_some hq, ?_⟩, by simp only; exact h⟩
    simpa using List.find?_some hq

section
variable (w : World)

/-- **The checked write, per column**: a column reads at every slot as before, or as a value the
write carried for it, which fits the column's type. -/
theorem put_col (k : Kind) (TF : TableFacts w k) (hshape : kindShape k = true) (f : Frame)
    (hk : f.kind = k) (st st' : St) (pairs : List (String × Val)) (h : put w f st pairs = .ok st')
    (c : String) (hc : c ∈ k.columns.map Prod.fst) (s : Val) :
    colGet w k (stobj st') c s = colGet w k (stobj st) c s ∨
      ∃ v, (c, v) ∈ pairs ∧ colFits k c v ∧ colGet w k (stobj st') c s = .ok v := by
  obtain ⟨_, _, _, hnM, hnC⟩ := kindShape_spec k hshape
  subst hk
  unfold put at h
  obtain ⟨slot, _, h⟩ := bind_ok h
  obtain ⟨id, _, h⟩ := bind_ok h
  obtain ⟨table, ht, h⟩ := bind_ok h
  obtain ⟨dir, hd, h⟩ := bind_ok h
  obtain ⟨control, _, h⟩ := bind_ok h
  obtain ⟨rows, _, h⟩ := bind_ok h
  obtain ⟨drows, _, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · rename_i hpass
    simp only [Bool.and_eq_true, List.all_eq_true] at hpass
    have hfits := hpass.2
    obtain ⟨table', ht', h⟩ := bind_ok h
    obtain ⟨dir', hd', h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have hfitsOf : ∀ p ∈ pairs, p.1 ∈ f.kind.columns.map Prod.fst ∧ colFits f.kind p.1 p.2 :=
      fun p hp => fits_mem f.kind p.1 p.2 (hfits p hp)
    have hM : stobj (setStobj (setStobj st f.kind.name table') "FN2-MACHINES" dir') "FN2-MACHINES" =
        .ok dir' := by
      apply stobj_setStobj_same
      rw [stobj_setStobj_ne _ _ _ _ hnM]; exact hd
    have hT : stobj (setStobj (setStobj st f.kind.name table') "FN2-MACHINES" dir') f.kind.name =
        .ok table' := by
      rw [stobj_setStobj_ne _ _ _ _ (Ne.symm hnM)]
      exact stobj_setStobj_same _ _ _ _ ht
    cases hdc : directoryFields.contains c
    · rw [colGet_own w _ _ c s table' hdc hT, colGet_own w _ _ c s table hdc ht]
      have := fold_get (fun s t => callFn w (f.kind.name ++ "-" ++ c) [s, t])
        (fun n s v t => callFn w (f.kind.name ++ "-SET-" ++ n) [s, v, t]) (ownCols f.kind) c
        (fun n hn s v t t' s' h => TF.own n c hn (mem_ownCols _ c hc hdc) s v t t' s' h) slot
        (pairs.filter fun p => !directoryFields.contains p.1) table table'
        (fun p hp => by
          simp only [List.mem_filter, Bool.not_eq_true'] at hp
          exact mem_ownCols _ _ (hfitsOf p hp.1).1 hp.2) ht' s
      rcases this with he | ⟨v, hv, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨v, (List.mem_filter.mp hv).1, (hfitsOf _ (List.mem_filter.mp hv).1).2, he⟩
    · rw [colGet_dir w _ _ c s dir' hdc hM, colGet_dir w _ _ c s dir hdc hd]
      have := fold_get (fun s t => callFn w ("FN2-MACHINES-" ++ c) [s, t])
        (fun n s v t => callFn w ("FN2-MACHINES-SET-" ++ n) [s, v, t]) (dirCols f.kind) c
        (fun n hn s v t t' s' h => TF.dir n c hn (mem_dirCols _ c hc hdc) s v t t' s' h) id
        (pairs.filter fun p => directoryFields.contains p.1) dir dir'
        (fun p hp => by
          simp only [List.mem_filter] at hp
          exact mem_dirCols _ _ (hfitsOf p hp.1).1 hp.2) hd' s
      rcases this with he | ⟨v, hv, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨v, (List.mem_filter.mp hv).1, (hfitsOf _ (List.mem_filter.mp hv).1).2, he⟩
  · obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨c2, _, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    left
    cases hdc : directoryFields.contains c
    · exact colGet_congr_own w _ _ _ c hdc (stobj_setStobj_ne _ _ _ _ (Ne.symm hnC)) s
    · exact colGet_congr_dir w _ _ _ c hdc (stobj_setStobj_ne _ _ _ _ (by decide)) s

theorem mapM_mem {α β : Type} (g : α → Except String β) :
    ∀ (l : List α) (res : List β), l.mapM g = .ok res → ∀ y ∈ res, ∃ x ∈ l, g x = .ok y := by
  intro l
  induction l with
  | nil => intro res h y hy; simp [pure, Except.pure] at h; subst h; simp at hy
  | cons a l ih =>
    intro res h y hy
    simp only [List.mapM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_ok h
    obtain ⟨xs, hxs, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    rcases List.mem_cons.mp hy with he | he
    · exact ⟨a, List.mem_cons_self .., he ▸ hx⟩
    · obtain ⟨x', hx', hg⟩ := ih xs hxs y he
      exact ⟨x', List.mem_cons_of_mem _ hx', hg⟩

/-- **The flush, per column**: a column reads as before, or as a fitting value that came from a
pending field of that name or, for `PHASE`, from the path's phase form. -/
theorem flush_col (k : Kind) (TF : TableFacts w k) (hshape : kindShape k = true) (f : Frame)
    (hk : f.kind = k) (st st' : St) (h : flush w f st = .ok st')
    (c : String) (hc : c ∈ k.columns.map Prod.fst) (s : Val) :
    colGet w k (stobj st') c s = colGet w k (stobj st) c s ∨
      ∃ v, colFits k c v ∧ colGet w k (stobj st') c s = .ok v ∧
        ((∃ e, (c, e) ∈ st.pending) ∨
         (c = "PHASE" ∧ ∃ ph t, st.next = some ph ∧ readNext w k ph = .ok t ∧
            t.eval w.fns (st.vars ++ st.stobjs) = .ok v)) := by
  unfold flush at h
  obtain ⟨pairs, hpairs, h⟩ := bind_ok h
  have hsrc : ∀ y ∈ pairs, ∃ e, (y.1, e) ∈ st.pending := by
    intro y hy
    obtain ⟨x, hx, hg⟩ := mapM_mem _ _ _ hpairs y hy
    obtain ⟨xv, _, hg⟩ := bind_ok hg
    simp only [pure, Except.pure, Except.ok.injEq] at hg; subst hg
    exact ⟨x.2, hx⟩
  have key : ∀ (pairs2 : List (String × Val)) (y st'' : St),
      (∀ z ∈ pairs2, (∃ e, (z.1, e) ∈ st.pending) ∨
        (z.1 = "PHASE" ∧ ∃ ph t, st.next = some ph ∧ readNext w k ph = .ok t ∧
          t.eval w.fns (st.vars ++ st.stobjs) = .ok z.2)) →
      (y = st ∨ put w f st pairs2 = .ok y) → st''.stobjs = y.stobjs →
      colGet w k (stobj st'') c s = colGet w k (stobj st) c s ∨
        ∃ v, colFits k c v ∧ colGet w k (stobj st'') c s = .ok v ∧
          ((∃ e, (c, e) ∈ st.pending) ∨
           (c = "PHASE" ∧ ∃ ph t, st.next = some ph ∧ readNext w k ph = .ok t ∧
              t.eval w.fns (st.vars ++ st.stobjs) = .ok v)) := by
    intro pairs2 y st'' hsrc2 hy hs
    have : stobj st'' = stobj y := funext (stobj_of_stobjs y st'' hs)
    rw [this]
    rcases hy with rfl | hy
    · exact Or.inl rfl
    · rcases put_col w k TF hshape f hk st y pairs2 hy c hc s with he | ⟨v, hv, hfit, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨v, hfit, he, hsrc2 _ hv⟩
  dsimp only at h
  split at h
  · rename_i ph hnx
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨v, hv, h⟩ := bind_ok h
    have hs2 : ∀ z ∈ pairs ++ [("PHASE", v)], (∃ e, (z.1, e) ∈ st.pending) ∨
        (z.1 = "PHASE" ∧ ∃ ph t, st.next = some ph ∧ readNext w k ph = .ok t ∧
          t.eval w.fns (st.vars ++ st.stobjs) = .ok z.2) := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Or.inl (hsrc z hz)
      · simp only [List.mem_singleton] at hz; subst hz
        exact Or.inr ⟨rfl, ph, t, hnx, hk ▸ ht, hv⟩
    obtain ⟨y0, hy0, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at hy0; subst hy0
    split at h
    · obtain ⟨y, hy, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hy h; subst hy h
      exact key _ _ _ hs2 (Or.inl rfl) rfl
    · obtain ⟨y, hy, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact key _ _ _ hs2 (Or.inr hy) rfl
  · have hs2 : ∀ z ∈ pairs, (∃ e, (z.1, e) ∈ st.pending) ∨
        (z.1 = "PHASE" ∧ ∃ ph t, st.next = some ph ∧ readNext w k ph = .ok t ∧
          t.eval w.fns (st.vars ++ st.stobjs) = .ok z.2) := fun z hz => Or.inl (hsrc z hz)
    obtain ⟨y0, hy0, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at hy0; subst hy0
    split at h
    · obtain ⟨y, hy, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at hy h; subst hy h
      exact key _ _ _ hs2 (Or.inl rfl) rfl
    · obtain ⟨y, hy, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact key _ _ _ hs2 (Or.inr hy) rfl

end

/-! ## The column contract (`runArm_writes_sub`) -/

section
variable (w : World)

/-- The children a result returns, as a state. -/
def tupleSt (k : Kind) (ts : List Val) : St := { stobjs := k.tuple.zip ts, vars := [] }

/-- Every column outside `W` (and other than `PHASE`) reads, at every slot, as in `S0`. -/
def GoodW (k : Kind) (W : List String) (S0 S : String → Except String Val) : Prop :=
  ∀ c ∈ k.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s, colGet w k S c s = colGet w k S0 c s

theorem semW (k : Kind) (W R : List String) (TF : TableFacts w k) (hshape : kindShape k = true)
    (S0 : String → Except String Val) : Sem w (primsW w k W R) k (GoodW w k W S0) := by
  obtain ⟨_, _, _, hnM, hnC⟩ := kindShape_spec k hshape
  have okW : ∀ c, c ≠ "PHASE" → c ∉ W → (c == "PHASE" || W.contains c) = false := by
    intro c h1 h2; simp [h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f st st' hk h hP hG c hc hph hW s
    rcases flush_col w k TF hshape f hk st st' h c hc s with he | ⟨v, _, _, hsrc⟩
    · exact he.trans (hG c hc hph hW s)
    · rcases hsrc with ⟨e, he⟩ | ⟨hph', _⟩
      · have := hP.1 _ he
        simp only [primsW] at this
        rw [okW c hph hW] at this; cases this
      · exact absurd hph' hph
  · intro op hop st st' hkeep hG c hc hph hW s
    simp only [primsW, List.all_eq_true] at hop
    refine Eq.trans ?_ (hG c hc hph hW s)
    cases hdc : directoryFields.contains c
    · refine colGet_congr_own w k _ _ c hdc (hkeep _ fun hm => ?_) s
      have := hop c (by simp [opWrites, hm, mem_ownCols k c hc hdc])
      rw [okW c hph hW] at this; cases this
    · refine colGet_congr_dir w k _ _ c hdc (hkeep _ fun hm => ?_) s
      have := hop c (by simp [opWrites, hm, mem_dirCols k c hc hdc])
      rw [okW c hph hW] at this; cases this
  · intro st st' hkeep hG c hc hph hW s
    refine Eq.trans ?_ (hG c hc hph hW s)
    cases hdc : directoryFields.contains c
    · exact colGet_congr_own w k _ _ c hdc (hkeep _ (by simp [hnC])) s
    · exact colGet_congr_dir w k _ _ c hdc (hkeep _ (by simp)) s
  · intro hd st st' hkeep hG c hc hph hW s
    simp only [primsW, List.all_eq_true] at hd
    refine Eq.trans ?_ (hG c hc hph hW s)
    cases hdc : directoryFields.contains c
    · exact colGet_congr_own w k _ _ c hdc (hkeep _ (by simp [hnC, hnM])) s
    · have := hd c (mem_dirCols k c hc hdc)
      simp only [List.contains_iff_mem] at this
      exact absurd this hW

/-- A child of the tuple reads the same from the run's final state and from the returned values. -/
theorem tuple_transfer (k : Kind) (hnd : k.tuple.Nodup) (stF : St) (ts : List Val)
    (hts : k.tuple.mapM (stobj stF) = .ok ts) (n : String) (hn : n ∈ k.tuple) :
    stobj (tupleSt k ts) n = stobj stF n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
  obtain ⟨htl, hti⟩ := mapM_spec _ _ _ hts
  obtain ⟨x, hx, hgx⟩ := hti i hi
  rw [hgx]
  have hil : i < ts.length := by omega
  simp only [tupleSt]
  rw [stobj_zip k.tuple ts hnd [] i hi hil]
  rw [List.getElem?_eq_getElem hil] at hx
  cases hx; rfl

/-- **Theorem (`runArm_writes_sub`)**: when an arm's written columns are `W` (`checkedWrites`), the
world's table accessors keep other columns (`TableFacts`) and the kind has the shape the
contract reads, every successful run returns the tuple's children as its last results, and every
column outside `W` other than `PHASE` reads back, at every slot, exactly as it was passed in. -/
theorem runArm_writes_sub (k : Kind) (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat)
    (v : Val) (W : List String) (hW : checkedWrites w k a = some W) (TF : TableFacts w k)
    (hshape : kindShape k = true) (hrun : runArm w k a observe args fuel = .ok v) :
    ∃ pre ts, v = Val.ofList (pre ++ ts) ∧ ts.length = k.tuple.length ∧
      ∀ c ∈ k.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s,
        colGet w k (stobj (tupleSt k ts)) c s = colGet w k (stobj (Inv.startSt k observe args)) c s := by
  unfold checkedWrites at hW
  dsimp only at hW
  split at hW
  · rename_i hadm
    simp only [Option.some.injEq] at hW; subst hW
    obtain ⟨hnd, hmk, hmm, _, _⟩ := kindShape_spec k hshape
    obtain ⟨stF, pre, ts, hv, hts, hg⟩ := runArm_inv w _ k a observe args fuel v _
      (semW w k _ _ TF hshape (stobj (Inv.startSt k observe args))) hadm
      (fun _ _ _ _ _ => rfl) hrun
    refine ⟨pre, ts, hv, (mapM_spec _ _ _ hts).1, fun c hc hph hW s => ?_⟩
    refine Eq.trans ?_ (hg c hc hph hW s)
    cases hdc : directoryFields.contains c
    · exact colGet_congr_own w k _ _ c hdc (tuple_transfer k hnd stF ts hts _ hmk) s
    · exact colGet_congr_dir w k _ _ c hdc (tuple_transfer k hnd stF ts hts _ hmm) s
  · cases hW

end

/-! ## The phase contract (`runArm_next_mem`) -/

section
variable (w : World)

theorem eval_if (fns : Fns) (env : Env) (c a b : Term) (v : Val)
    (h : Term.eval fns env (.app "IF" [c, a, b]) = .ok v) :
    Term.eval fns env a = .ok v ∨ Term.eval fns env b = .ok v := by
  simp only [Term.eval] at h
  obtain ⟨cv, _, h⟩ := bind_ok h
  split at h
  · exact Or.inl h
  · exact Or.inr h

theorem phasesCover_spec (k : Kind) (h : phasesCover k = true) (v : Val) (hv : colFits k "PHASE" v) :
    ∃ p ∈ k.states, ∃ i, (p, i) ∈ k.phases ∧ v = .int i := by
  unfold phasesCover at h
  unfold colFits at hv
  split at h
  · rename_i q n hq
    rw [hq] at hv
    simp only [ColType.fits] at hv
    cases v with
    | int i =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      simp only [List.all_eq_true, List.mem_range, List.any_eq_true, List.contains_iff_mem] at h
      obtain ⟨p, hp, hmem⟩ := h i.toNat (by omega)
      refine ⟨p, hp, i, ?_, rfl⟩
      have : ((i.toNat : Nat) : Int) = i := by omega
      rw [this] at hmem; exact hmem
    | _ => simp at hv
  · simp at h

/-- The `:case` chain of a phase form: its value is the value of one arm's form. -/
theorem readNextF_go_sound (rn : Expr → Except String Term) (n : Expr) (key : Term)
    (env : Env) (v : Val) :
    ∀ (l : List Val) (t : Term), readNextF.go rn n key l = .ok t →
      t.eval w.fns env = .ok v →
      ∃ a ∈ l, ∃ t', rn a.cdr.car = .ok t' ∧ t'.eval w.fns env = .ok v := by
  intro l
  induction l with
  | nil => intro t h; simp [readNextF.go, throw, throwThe, MonadExceptOf.throw] at h
  | cons a more ih =>
    intro t h hv
    unfold readNextF.go at h
    obtain ⟨e, he, h⟩ := bind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨a, List.mem_cons_self .., e, he, hv⟩
    · obtain ⟨g, hg, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      rcases eval_if _ _ _ _ _ _ hv with h1 | h1
      · exact ⟨a, List.mem_cons_self .., e, he, h1⟩
      · obtain ⟨a', ha', t', ht', h2⟩ := ih g hg h1
        exact ⟨a', List.mem_cons_of_mem _ ha', t', ht', h2⟩

/-- **The phase reader is sound for `nextExprPhases`**: a fitting value of a phase form is the
value of a phase the analysis lists. -/
theorem nextPhases_sound (k : Kind) (hpc : phasesCover k = true)
    (d : Expr → Except String Term) (hd : ∀ x, ∃ e, d x = .error e) :
    ∀ (n : Nat) (ph : Expr) (t : Term) (env : Env) (v : Val),
      fixN n (readNextF w k) d ph = .ok t → t.eval w.fns env = .ok v → colFits k "PHASE" v →
      ∃ p ∈ fixN n (nextExprPhasesF k) (fun _ => []) ph, ∃ i, (p, i) ∈ k.phases ∧ v = .int i := by
  intro n
  induction n with
  | zero =>
    intro ph t env v h
    obtain ⟨e, he⟩ := hd ph
    simp only [fixN, he] at h; cases h
  | succ n ih =>
    intro ph t env v h hv hfit
    simp only [fixN] at h ⊢
    unfold readNextF at h
    split at h
    · rename_i p
      split at h
      · rename_i q i hq
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Term.eval, Except.ok.injEq] at hv; subst hv
        have he : q = p := by simpa using List.find?_some hq
        have hmem := List.mem_of_find?_eq_some hq
        have hany : k.phases.any (·.1 == p) = true :=
          List.any_eq_true.mpr ⟨(q, i), hmem, by simp [he]⟩
        refine ⟨p, by simp [nextExprPhasesF, hany], i, ?_, rfl⟩
        rw [← he]; exact hmem
      · rename_i hnone
        split at h
        · rename_i hrow
          obtain ⟨p', hp', i, hi, hvi⟩ := phasesCover_spec k hpc v hfit
          have hany : k.phases.any (·.1 == p) = false := by
            rw [List.any_eq_false]; intro x hx hxp
            simp only [beq_iff_eq] at hxp
            have := List.find?_eq_none.mp hnone x hx
            simp [hxp] at this
          refine ⟨p', ?_, i, hi, hvi⟩
          simp only [nextExprPhasesF, hany, Bool.false_eq_true, if_false]
          rw [if_pos (by simpa using hrow)]; exact hp'
        · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i rest
      split at h
      · rename_i e a b hl
        obtain ⟨te, _, h⟩ := bind_ok h
        obtain ⟨ta, hta, h⟩ := bind_ok h
        obtain ⟨tb, htb, h⟩ := bind_ok h
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [nextExprPhasesF, hl, List.mem_append]
        rcases eval_if _ _ _ _ _ _ hv with h1 | h1
        · obtain ⟨p, hp, i, hi, hvi⟩ := ih a ta env v hta h1 hfit
          exact ⟨p, Or.inl hp, i, hi, hvi⟩
        · obtain ⟨p, hp, i, hi, hvi⟩ := ih b tb env v htb h1 hfit
          exact ⟨p, Or.inr hp, i, hi, hvi⟩
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rename_i rest
      obtain ⟨key, _, h⟩ := bind_ok h
      obtain ⟨a, ha, t', ht', h2⟩ := readNextF_go_sound w _ _ key env v _ t h hv
      obtain ⟨p, hp, i, hi, hvi⟩ := ih _ t' env v ht' h2 hfit
      refine ⟨p, ?_, i, hi, hvi⟩
      simp only [nextExprPhasesF, List.mem_flatMap]
      exact ⟨a, ha, hp⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The `PHASE` column at every slot reads as in `S0` or as the value of a phase in `D`. -/
def GoodN (k : Kind) (D : List String) (S0 S : String → Except String Val) : Prop :=
  ∀ s, colGet w k S "PHASE" s = colGet w k S0 "PHASE" s ∨
    ∃ p ∈ D, ∃ i, (p, i) ∈ k.phases ∧ colGet w k S "PHASE" s = .ok (.int i)

theorem phase_col (k : Kind) (hpc : phasesCover k = true) : "PHASE" ∈ k.columns.map Prod.fst := by
  unfold phasesCover at hpc
  split at hpc
  · rename_i q n hq
    have he : q = "PHASE" := by simpa using List.find?_some hq
    exact List.mem_map.mpr ⟨_, List.mem_of_find?_eq_some hq, he⟩
  · cases hpc

theorem semN (k : Kind) (D R : List String) (TF : TableFacts w k) (hshape : kindShape k = true)
    (hpc : phasesCover k = true) (S0 : String → Except String Val) :
    Sem w (primsN w k D R) k (GoodN w k D S0) := by
  obtain ⟨_, _, _, hnM, hnC⟩ := kindShape_spec k hshape
  have hdc : directoryFields.contains "PHASE" = false := by decide
  have hcol := phase_col k hpc
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f st st' hk h hP hG s
    rcases flush_col w k TF hshape f hk st st' h "PHASE" hcol s with he | ⟨v, hfit, he, hsrc⟩
    · rw [he]; exact hG s
    · right
      rcases hsrc with ⟨e, hmem⟩ | ⟨_, ph, t, hnx, ht, hev⟩
      · have := hP.1 _ hmem
        simp only [primsN, bne_self_eq_false, Bool.false_or, List.all_eq_true,
          List.contains_iff_mem] at this
        obtain ⟨p, hp, i, hi, hvi⟩ := phasesCover_spec k hpc v hfit
        exact ⟨p, this p hp, i, hi, hvi ▸ he⟩
      · have := hP.2 ph hnx
        simp only [primsN, List.all_eq_true, List.contains_iff_mem] at this
        obtain ⟨p, hp, i, hi, hvi⟩ := nextPhases_sound w k hpc _ (fun _ => ⟨_, rfl⟩) readDepth ph t
          _ v ht hev hfit
        exact ⟨p, this p hp, i, hi, hvi ▸ he⟩
  · intro op hop st st' hkeep hG s
    simp only [primsN, Bool.not_eq_true'] at hop
    rw [colGet_congr_own w k _ _ _ hdc (hkeep _ (fun hm => by simp [hm] at hop)) s]
    exact hG s
  · intro st st' hkeep hG s
    rw [colGet_congr_own w k _ _ _ hdc (hkeep _ (by simp [hnC])) s]
    exact hG s
  · intro _ st st' hkeep hG s
    rw [colGet_congr_own w k _ _ _ hdc (hkeep _ (by simp [hnC, hnM])) s]
    exact hG s

/-- **Theorem (`runArm_next_mem`)**: when an arm's reachable phases are `D` (`checkedNext`), the
world's table accessors keep other columns (`TableFacts`), the kind has the contract's shape and
every value its `PHASE` type admits is a state's (`phasesCover`), every successful run returns the
tuple's children as its last results, and the `PHASE` column at every slot reads back either as
it was passed in or as the value of a phase in `D`. -/
theorem runArm_next_mem (k : Kind) (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat)
    (v : Val) (D : List String) (hD : checkedNext w k a = some D) (TF : TableFacts w k)
    (hshape : kindShape k = true) (hpc : phasesCover k = true)
    (hrun : runArm w k a observe args fuel = .ok v) :
    ∃ pre ts, v = Val.ofList (pre ++ ts) ∧ ts.length = k.tuple.length ∧
      ∀ s, colGet w k (stobj (tupleSt k ts)) "PHASE" s =
          colGet w k (stobj (Inv.startSt k observe args)) "PHASE" s ∨
        ∃ p ∈ D, ∃ i, (p, i) ∈ k.phases ∧ colGet w k (stobj (tupleSt k ts)) "PHASE" s = .ok (.int i) := by
  unfold checkedNext at hD
  dsimp only at hD
  split at hD
  · rename_i hadm
    simp only [Option.some.injEq] at hD; subst hD
    obtain ⟨hnd, hmk, _, _, _⟩ := kindShape_spec k hshape
    obtain ⟨stF, pre, ts, hv, hts, hg⟩ := runArm_inv w _ k a observe args fuel v _
      (semN w k _ _ TF hshape hpc (stobj (Inv.startSt k observe args))) hadm
      (fun _ => Or.inl rfl) hrun
    refine ⟨pre, ts, hv, (mapM_spec _ _ _ hts).1, fun s => ?_⟩
    have hdc : directoryFields.contains "PHASE" = false := by decide
    rw [colGet_congr_own w k _ _ _ hdc (tuple_transfer k hnd stF ts hts _ hmk) s]
    exact hg s
  · cases hD

end

/-! ## The world's table accessors: the list-valued layouts satisfy `TableFacts` -/

section
variable (w : World)

/-- Accessors over a layout: column `c` is index `idx c`, read by `G` and written by `U`, where a
write to one index leaves every other index and makes its own read either as before or the value
written. Then the accessors keep the columns' frame (one field of `TableFacts`). -/
theorem facts_of (C : List String) (gn sn : String → String) (idx : String → Nat)
    (G : Nat → Val → Val → Val) (U : Nat → Val → Val → Val → Val)
    (hG : ∀ c ∈ C, ∀ s t, callFn w (gn c) [s, t] = .ok (G (idx c) s t))
    (hU : ∀ c ∈ C, ∀ s v t, callFn w (sn c) [s, v, t] = .ok (U (idx c) s v t))
    (hinj : ∀ a ∈ C, ∀ b ∈ C, idx a = idx b → a = b)
    (hne : ∀ i j s s' v t, i ≠ j → G i s' (U j s v t) = G i s' t)
    (hsame : ∀ i s s' v t, G i s' (U i s v t) = G i s' t ∨ G i s' (U i s v t) = v) :
    ∀ n c, n ∈ C → c ∈ C → ∀ (s v t t' s' : Val), callFn w (sn n) [s, v, t] = .ok t' →
      callFn w (gn c) [s', t'] = callFn w (gn c) [s', t] ∨
        (n = c ∧ callFn w (gn c) [s', t'] = .ok v) := by
  intro n c hn hc s v t t' s' h
  rw [hU n hn] at h
  simp only [Except.ok.injEq] at h; subst h
  rw [hG c hc, hG c hc]
  by_cases hnc : n = c
  · subst hnc
    rcases hsame (idx n) s s' v t with h | h
    · left; rw [h]
    · right; exact ⟨rfl, by rw [h]⟩
  · left
    rw [hne (idx c) (idx n) s s' v t (fun he => hnc (hinj n hn c hc he.symm))]

/-- The flat layout: a column is one field of the table (`NTH i`, `UPDATE-NTH i`). -/
theorem flat_ne (i j : Nat) (s s' v t : Val) (h : i ≠ j) :
    Native.nth (.int i) (Native.updateNth (.int j) v t) = Native.nth (.int i) t :=
  nth_updateNth_ne i j v t h

/-- The stobj-array layout the generator emits: column `i` is an array field, read by
`(NTH s (NTH i st))` and written by `UPDATE-NTH-ARRAY i s v st`. -/
def arrGet (i : Nat) (s t : Val) : Val := Native.nth s (Native.nth (.int i) t)

def arrSet (i : Nat) (s v t : Val) : Val :=
  Native.updateNth (.int i) (Native.updateNth s v (Native.nth (.int i) t)) t

theorem arr_ne (i j : Nat) (s s' v t : Val) (h : i ≠ j) : arrGet i s' (arrSet j s v t) = arrGet i s' t := by
  simp only [arrGet, arrSet, nth_updateNth_ne i j _ _ h]

theorem arr_same (i : Nat) (s s' v t : Val) :
    arrGet i s' (arrSet i s v t) = arrGet i s' t ∨ arrGet i s' (arrSet i s v t) = v := by
  simp only [arrGet, arrSet, nth_updateNth_same]
  simp only [Native.nth, Native.updateNth]
  by_cases h : s'.nfix = s.nfix
  · right; rw [h, nthN_updateNthN_same]
  · left; rw [nthN_updateNthN_ne _ _ _ _ h]

end

/-! ## Teeth -/

section
open Fn2.Arms.Derive

def toothIdx (c : String) : Nat :=
  if c == "PHASE" then 0 else if c == "STOPPED" then 1 else if c == "OFF" then 2 else 0

theorem tooth_tableFacts : TableFacts toothWorld toothKind := by
  have hown : ownCols toothKind = ["PHASE", "STOPPED", "OFF"] := by decide
  have hdir : dirCols toothKind = ["WAIT-REASON"] := by decide
  refine ⟨?_, ?_⟩
  · exact facts_of toothWorld _ (fun c => toothKind.name ++ "-" ++ c)
      (fun c => toothKind.name ++ "-SET-" ++ c) toothIdx
      (fun i _ t => Native.nth (.int i) t) (fun i _ v t => Native.updateNth (.int i) v t)
      (by rw [hown]; intro c hc s t; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> exact callFn_of_fns _ _ _ _ (by decide) rfl)
      (by rw [hown]; intro c hc s v t; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl <;> exact callFn_of_fns _ _ _ _ (by decide) rfl)
      (by rw [hown]; decide)
      (fun i j s s' v t h => flat_ne i j s s' v t h)
      (fun i s s' v t => Or.inr (nth_updateNth_same i v t))
  · exact facts_of toothWorld _ (fun c => "FN2-MACHINES-" ++ c) (fun c => "FN2-MACHINES-SET-" ++ c)
      (fun _ => 0) (fun i _ t => Native.nth (.int i) t) (fun i _ v t => Native.updateNth (.int i) v t)
      (by rw [hdir]; intro c hc s t; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          subst hc; exact callFn_of_fns _ _ _ _ (by decide) rfl)
      (by rw [hdir]; intro c hc s v t; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          subst hc; exact callFn_of_fns _ _ _ _ (by decide) rfl)
      (by rw [hdir]; decide)
      (fun i j s s' v t h => flat_ne i j s s' v t h)
      (fun i s s' v t => Or.inr (nth_updateNth_same i v t))

/-- The returned children of a tooth run, as a state. -/
def toothOut (a : Arm) : St := tupleSt toothKind ((runTooth a).toList.drop 4)

/-- Positive witness for `runArm_writes_sub`: every antecedent holds for `toothArmStep` (written
columns `["OFF"]`), and its run returns `STOPPED` at slot 0 as it was passed in (`0`). -/
theorem runArm_writes_sub_pos :
    checkedWrites toothWorld toothKind toothArmStep = some ["OFF"] ∧ kindShape toothKind = true ∧
    TableFacts toothWorld toothKind ∧
    runArm toothWorld toothKind toothArmStep false toothArgs 10 = .ok (runTooth toothArmStep) ∧
    colGet toothWorld toothKind (stobj (toothOut toothArmStep)) "STOPPED" (.int 0) = .ok (.int 0) ∧
    colGet toothWorld toothKind (stobj (Inv.startSt toothKind false toothArgs)) "STOPPED" (.int 0) =
      .ok (.int 0) :=
  ⟨by decide +kernel, by decide +kernel, tooth_tableFacts, by decide +kernel, by decide +kernel,
   by decide +kernel⟩

/-- Tooth: `mutantArmWrites` writes `STOPPED` (outside `["OFF"]`); its checked writes include it,
and its run returns `STOPPED` changed, which the conclusion for `["OFF"]` forbids. -/
theorem runArm_writes_sub_mutant :
    (checkedWrites toothWorld toothKind mutantArmWrites).map (·.contains "STOPPED") = some true ∧
    colGet toothWorld toothKind (stobj (toothOut mutantArmWrites)) "STOPPED" (.int 0) ≠
      colGet toothWorld toothKind (stobj (Inv.startSt toothKind false toothArgs)) "STOPPED" (.int 0) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A world whose `OFF` setter also clears `STOPPED`: it fails `TableFacts`. -/
def leakyWorld : World :=
  { toothWorld with
    fns := fun f args => match f, args with
      | "FN2-ECHO-SET-OFF", [_, v, t] =>
        some (Native.updateNth (.int 1) (.int 7) (Native.updateNth (.int 2) v t))
      | f, args => toothFns f args }

def runLeaky : Val :=
  match runArm leakyWorld toothKind toothArmStep false toothArgs 10 with
  | .ok v => v
  | .error _ => Val.nil

/-- Hypothesis-removal witness for `TableFacts`: in `leakyWorld` the derivation and its check are
unchanged (`["OFF"]`), the run succeeds, and `STOPPED` comes back changed; without the world fact
the conclusion fails. -/
theorem runArm_writes_sub_needs_tableFacts :
    checkedWrites leakyWorld toothKind toothArmStep = some ["OFF"] ∧
    ∃ v, runArm leakyWorld toothKind toothArmStep false toothArgs 10 = .ok v ∧
      colGet leakyWorld toothKind (stobj (tupleSt toothKind (v.toList.drop 4))) "STOPPED" (.int 0) ≠
        colGet leakyWorld toothKind (stobj (Inv.startSt toothKind false toothArgs)) "STOPPED" (.int 0) :=
  ⟨by decide +kernel, runLeaky, by decide +kernel⟩

/-- Positive witness for `runArm_next_mem`: every antecedent holds for `toothArmStep` (phases
`[":REPLY"]`), and its run leaves slot 0 in phase 2, the value of `:REPLY`. -/
theorem runArm_next_mem_pos :
    checkedNext toothWorld toothKind toothArmStep = some [":REPLY"] ∧ phasesCover toothKind = true ∧
    (":REPLY", (2 : Int)) ∈ toothKind.phases ∧
    colGet toothWorld toothKind (stobj (toothOut toothArmStep)) "PHASE" (.int 0) = .ok (.int 2) ∧
    colGet toothWorld toothKind (stobj (Inv.startSt toothKind false toothArgs)) "PHASE" (.int 0) =
      .ok (.int 1) :=
  ⟨by decide +kernel, by decide +kernel, by decide, by decide +kernel, by decide +kernel⟩

/-- Tooth: `mutantArmNext` moves slot 0 to phase 3 (`:CLOSING`): neither the phase it was passed in
(1) nor the value of any phase in `toothArmStep`'s `[":REPLY"]`; its own checked phases follow. -/
theorem runArm_next_mem_mutant :
    (checkedNext toothWorld toothKind mutantArmNext).map (·.contains ":CLOSING") = some true ∧
    colGet toothWorld toothKind (stobj (toothOut mutantArmNext)) "PHASE" (.int 0) = .ok (.int 3) ∧
    ∀ p ∈ [":REPLY"], ∀ i, (p, i) ∈ toothKind.phases → i ≠ 3 := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro p hp i hi
  simp only [List.mem_singleton] at hp; subst hp
  simp [toothKind] at hi; omega

end

end Fn2.Arms.Columns
