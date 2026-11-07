import Fn2.Arms.Core

/-!
# Fn2.Arms.CorePhase: a core-only operation's call, child by child

An operation with no `:child` is called in the core face through its adapter (`Fn2.Arms.Core`):
the interpreter passes every child of the core (`actuals` over `expandF`/`expandS`), the adapter
assembles them into the core (`collapse`), calls the operation's translation and splits the core
it returns back into children (`spread`), which `bindOuts` binds. This file follows one child
through that: what the operation's translation keeps of the core's child `K` (a projection fact,
`Fn2.Instances.LayerAPres`), the call keeps of the child `K` the arm sees. `keepsPhase_of_pres`
states it for the `PHASE` column, the fact `Fn2.Arms.Columns.primsN` reads.
-/

namespace Fn2.Arms.CorePhase
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Core Fn2.Arms.Bound Fn2.Arms.Frame

set_option autoImplicit false

section
variable (w : World) (k : Kind) (st : St)

theorem actuals_cons (f : String) (fs : List String) (s : Option String) (ss : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (args : List Val)
    (h : actuals w k st (f :: fs) (s :: ss) pos keys = .ok args) :
    ∃ v rest pos', args = v :: rest ∧ actuals w k st fs ss pos' keys = .ok rest ∧
      (∀ c, s = some c → stobj st c = .ok v ∧ pos' = pos) := by
  cases s with
  | some c =>
    simp only [actuals] at h
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨rest, hr, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨v, rest, pos, h.symm, hr, fun c' hc => by cases hc; exact ⟨hv, rfl⟩⟩
  | none =>
    simp only [actuals] at h
    repeat' (first | split at h | (simp only [ite_true, ite_false] at h))
    all_goals first
      | (obtain ⟨v, _, h⟩ := bind_ok h
         obtain ⟨rest, hr, h⟩ := bind_ok h
         simp only [pure, Except.pure, Except.ok.injEq] at h
         exact ⟨v, rest, _, h.symm, hr, fun _ hc => by cases hc⟩)
      | (obtain ⟨v, hv, _⟩ := bind_ok h
         simp [throw, throwThe, MonadExceptOf.throw] at hv)

theorem actuals_prefix (ts fs : List String) (ss : List (Option String)) (pos : List Expr)
    (keys : List (String × Expr)) (args : List Val)
    (h : actuals w k st (ts ++ fs) (ts.map some ++ ss) pos keys = .ok args) :
    ∃ vs rest, ts.mapM (stobj st) = .ok vs ∧ actuals w k st fs ss pos keys = .ok rest ∧
      args = vs ++ rest := by
  induction ts generalizing args with
  | nil => exact ⟨[], args, rfl, by simpa using h, rfl⟩
  | cons t ts ih =>
    obtain ⟨v, rest, pos', rfl, hr, hc⟩ := actuals_cons w k st _ _ _ _ _ _ _ h
    obtain ⟨hv, rfl⟩ := hc t rfl
    obtain ⟨vs, rest', hm, hr', rfl⟩ := ih rest hr
    refine ⟨v :: vs, rest', ?_, hr', rfl⟩
    simp [List.mapM_cons, hv, hm, bind, Except.bind, pure, Except.pure]

theorem mapM_length {xs : List String} {vs : List Val}
    (h : xs.mapM (stobj st) = .ok vs) : vs.length = xs.length := by
  induction xs generalizing vs with
  | nil => simp [List.mapM_nil, pure, Except.pure] at h; subst h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨v, _, h⟩ := bind_ok h
    obtain ⟨vs', hv', h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h; simp [ih hv']

/-- **The core the adapter assembles is the arm's children**: at the operation's core formal,
the adapter passes `Val.ofList` of the children the interpreter reads from the arm's state. -/
theorem core_arg (tuple : List String) : ∀ (fs : List String) (sin : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) (args acts : List Val),
    fs.length = sin.length →
    actuals w k st (expandF tuple fs sin) (expandS tuple sin) pos keys = .ok args →
    collapse tuple.length sin args = some acts →
    ∀ j : Nat, sin[j]? = some (some "FN2-CORE") →
      ∃ vs, tuple.mapM (stobj st) = .ok vs ∧ acts[j]? = some (Val.ofList vs)
  | [], [], _, _, _, _, _, _, _, j, hj => by simp at hj
  | [], _ :: _, _, _, _, _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => by simp at hl
  | f :: fs, s :: ss, pos, keys, args, acts, hl, ha, hc, j, hj => by
    by_cases hs : s = some "FN2-CORE"
    · subst hs
      have ha' : actuals w k st (tuple ++ expandF tuple fs ss) (tuple.map some ++ expandS tuple ss)
          pos keys = .ok args := by simpa [expandF, expandS] using ha
      obtain ⟨vs, rest, hm, hr, rfl⟩ := actuals_prefix w k st tuple _ _ pos keys args ha'
      have hlen := mapM_length st hm
      simp only [collapse, beq_self_eq_true, if_true, List.length_append, hlen] at hc
      rw [if_neg (by omega)] at hc
      rw [List.take_left' hlen, List.drop_left' hlen] at hc
      cases j with
      | zero =>
        refine ⟨vs, hm, ?_⟩
        cases h' : collapse tuple.length ss rest <;> simp [h'] at hc
        subst hc; rfl
      | succ j =>
        cases h' : collapse tuple.length ss rest with
        | none => simp [h'] at hc
        | some acts' =>
          simp [h'] at hc; subst hc
          exact core_arg tuple fs ss pos keys rest acts' (by simpa using hl) hr h' j (by simpa using hj)
    · have ha' : actuals w k st (f :: expandF tuple fs ss) (s :: expandS tuple ss) pos keys = .ok args := by
        simpa [expandF, expandS, hs] using ha
      obtain ⟨v, rest, pos', rfl, hr, _⟩ := actuals_cons w k st _ _ _ _ _ _ _ ha'
      have hb : (s == some "FN2-CORE") = false := by simpa using hs
      simp only [collapse, hb, Bool.false_eq_true, if_false] at hc
      cases j with
      | zero => simp at hj; exact absurd hj hs
      | succ j =>
        cases h' : collapse tuple.length ss rest with
        | none => simp [h'] at hc
        | some acts' =>
          simp [h'] at hc; subst hc
          exact core_arg tuple fs ss pos' keys rest acts' (by simpa using hl) hr h' j (by simpa using hj)

/-- After binding, a child bound at output position `p` (and at no later output) reads the
`p`-th result. -/
theorem go_bound : ∀ (outs : List (Option String)) (vars : List String) (rs : List Val) (st st' : St)
    (p : Nat) (c : String), bindOuts.go st outs vars rs = .ok st' → outs[p]? = some (some c) →
    c ∉ (outs.drop (p + 1)).filterMap id → (∃ v, stobj st c = .ok v) →
    ∃ r, rs[p]? = some r ∧ stobj st' c = .ok r
  | [], _, _, _, _, _, _, _, hp, _, _ => by simp at hp
  | o :: os, vars, rs, st, st', p, c, h, hp, hn, hv => by
    cases rs with
    | nil => cases o <;> (try cases vars) <;> simp [bindOuts.go] at h
    | cons r rs' =>
      cases p with
      | zero =>
        simp at hp; subst hp
        simp only [bindOuts.go] at h
        obtain ⟨_, _, hst⟩ := bindOuts_go_stobj _ _ _ _ _ h
        obtain ⟨v, hv⟩ := hv
        refine ⟨r, rfl, ?_⟩
        rw [hst c (by simpa using hn)]
        exact stobj_setStobj_same st c r v hv
      | succ p =>
        simp only [List.getElem?_cons_succ] at hp
        have hn' : c ∉ (os.drop (p + 1)).filterMap id := by simpa using hn
        cases o with
        | some s =>
          simp only [bindOuts.go] at h
          have hv' : ∃ v, stobj (setStobj st s r) c = .ok v := by
            by_cases hcs : s = c
            · subst hcs; exact ⟨r, stobj_setStobj_same st s r _ hv.choose_spec⟩
            · rw [stobj_setStobj_ne st s c r hcs]; exact hv
          obtain ⟨r', h1, h2⟩ := go_bound os vars rs' _ st' p c h hp hn' hv'
          exact ⟨r', by simpa using h1, h2⟩
        | none =>
          cases vars with
          | nil =>
            simp only [bindOuts.go] at h
            obtain ⟨r', h1, h2⟩ := go_bound os [] rs' st st' p c h hp hn' hv
            exact ⟨r', by simpa using h1, h2⟩
          | cons v vs =>
            simp only [bindOuts.go] at h
            obtain ⟨r', h1, h2⟩ := go_bound os vs rs' _ st' p c h hp hn' (by simpa [stobj] using hv)
            exact ⟨r', by simpa using h1, h2⟩

theorem nth_int_eq (n : Nat) (l : Val) : Native.nth (Val.int n) l = (l.toList[n]?).getD Val.nil := by
  show Native.nthN n l = _
  induction n generalizing l with
  | zero => cases l <;> rfl
  | succ n ih =>
    cases l with
    | cons a d => simp only [Native.nthN, Val.toList, List.getElem?_cons_succ]; exact ih d
    | _ => rfl

theorem bindOuts_go_of_long (st : St) (outs : List (Option String)) (vars : List String) (res : Val)
    (h : 2 ≤ outs.length) : bindOuts st outs vars res = bindOuts.go st outs vars res.toList := by
  unfold bindOuts
  split
  · simp at h
  · simp at h
  · rfl


theorem mapM_get : ∀ (l : List String) (vs : List Val) (i : Nat) (c : String),
    l.mapM (stobj st) = .ok vs → l[i]? = some c → ∃ x, vs[i]? = some x ∧ stobj st c = .ok x
  | [], _, _, _, _, hc => by simp at hc
  | x :: l, vs, i, c, h, hc => by
    simp only [List.mapM_cons] at h
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨vs', hv', h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases i with
    | zero => simp at hc; subst hc; exact ⟨v, rfl, hv⟩
    | succ i => simpa using mapM_get l vs' i c hv' (by simpa using hc)

theorem not_mem_drop_of_nodup {l : List String} (hnd : l.Nodup) {i : Nat} {c : String}
    (hc : l[i]? = some c) : c ∉ l.drop (i + 1) := by
  intro hm
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hc
  have hmt : c ∈ l.take (i + 1) := by
    rw [List.getElem?_eq_getElem hi] at hc
    cases hc
    exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
  have := List.take_append_drop (i + 1) l
  rw [← this] at hnd
  exact (List.nodup_append.mp hnd).2.2 c hmt c hm rfl

theorem flat_core (f : Option String × Val → List Val)
    (hf : ∀ v, f (none, v) = [v]) (hc : ∀ v, f (some "FN2-CORE", v) = v.toList) :
    ∀ (r : Nat) (L : List Val) (n : Nat) (x : Val),
    (((List.replicate r none ++ [some "FN2-CORE"]).zip L).flatMap f)[r + n]? = some x →
      ∃ c, L[r]? = some c ∧ c.toList[n]? = some x
  | 0, [], n, x, h => by simp at h
  | 0, c :: L, n, x, h => by
    refine ⟨c, rfl, ?_⟩
    simpa [hc] using h
  | r + 1, [], n, x, h => by simp at h
  | r + 1, a :: L, n, x, h => by
    have h' : (((List.replicate r none ++ [some "FN2-CORE"]).zip L).flatMap f)[r + n]? = some x := by
      simp only [List.replicate_succ, List.cons_append, List.zip_cons_cons, List.flatMap_cons, hf] at h
      rw [show r + 1 + n = (r + n) + 1 by omega] at h
      simpa using h
    obtain ⟨c, h1, h2⟩ := flat_core f hf hc r L n x h'
    exact ⟨c, by simpa using h1, h2⟩

/-- **A core-only operation's call keeps the kind's `PHASE` column when its translation keeps the
column of the core's child**: `hpres` is the projection fact of the operation's translation (the
`PHASE` column, index 0 of the child at `iK`, of the returned core is that of the core passed),
the rest is the shape of the call (each discharged by evaluation for a named operation). -/
theorem keepsPhase_of_pres (w : World) (tuple : List String) (k : Kind) (o : Op)
    (j r iK : Nat)
    (hfind : (coreWorld w tuple).ops.find? (·.name == o.name) = some (coreOp tuple o))
    (hcallee : o.callee = none) (hcf : o.coreFormals.isEmpty = false)
    (hlen : o.coreFormals.length = o.coreIn.length)
    (hnat : nativeCallNames.contains (adapterName o.name) = false)
    (hend : (adapterName o.name).endsWith "@CORE" = true)
    (hadapt : w.ops.find? (fun o' => adapterName o'.name == adapterName o.name) = some o)
    (hj : o.coreIn[j]? = some (some "FN2-CORE"))
    (hout : o.coreOut = List.replicate r none ++ [some "FN2-CORE"])
    (hK : tuple[iK]? = some k.name) (hnd : tuple.Nodup) (hlong : 2 ≤ tuple.length)
    (hget : ∀ s t, callFn (coreWorld w tuple) (k.name ++ "-" ++ "PHASE") [s, t] =
      .ok (Native.nth s (Native.nth (Val.int 0) t)))
    (hdc : directoryFields.contains "PHASE" = false)
    (hpres : ∀ acts v, w.fns o.name acts = some v →
      Native.nth (Val.int 0) (Native.nth (Val.int iK)
          (if r = 0 then v else Native.nth (Val.int r) v)) =
        Native.nth (Val.int 0) (Native.nth (Val.int iK) (acts.getD j Val.nil))) :
    Columns.KeepsPhase (coreWorld w tuple) k o.name := by
  intro st st2 c o2 vars hc hcall hbind s
  -- the call through the adapter
  simp only [Arms.callOp] at hcall
  obtain ⟨op, hop, hcall⟩ := bind_ok hcall
  have hop' : op = coreOp tuple o := by
    rw [hc] at hop; unfold findOp at hop; rw [hfind] at hop; cases hop; rfl
  subst hop'
  simp only [coreOp, hcallee, hcf, Bool.false_eq_true, if_false] at hcall hbind
  obtain ⟨callee, hce, hcall⟩ := bind_ok hcall
  simp only [pure, Except.pure, Except.ok.injEq] at hce; subst hce
  obtain ⟨keys, _, hcall⟩ := bind_ok hcall
  obtain ⟨args, hargs, hcall⟩ := bind_ok hcall
  obtain ⟨res, hres, hcall⟩ := bind_ok hcall
  simp only [pure, Except.pure, Except.ok.injEq] at hcall; subst hcall
  simp only at hbind
  -- the adapter: collapse, the translation, spread
  unfold callFn at hres
  rw [nativeCall_none _ _ hnat] at hres
  simp only [coreWorld, coreFns, hend, if_true] at hres
  rw [hadapt] at hres
  simp only at hres
  cases hcol : collapse tuple.length o.coreIn args with
  | none => simp [hcol] at hres
  | some acts =>
    cases hv : w.fns o.name acts with
    | none => simp [hcol, hv] at hres
    | some v =>
      simp only [hcol, hv, Option.map_some] at hres
      cases hres
      -- the child the arm passed
      obtain ⟨vs, hm, hacts⟩ := core_arg (coreWorld w tuple) k st tuple _ _ _ _ _ _ hlen hargs hcol j hj
      obtain ⟨x0, hx0, hst0⟩ := mapM_get st tuple vs iK k.name hm hK
      -- the child bound
      rw [hout] at hbind
      have hexp : expandS tuple (List.replicate r none ++ [some "FN2-CORE"]) =
          List.replicate r none ++ tuple.map some := by
        simp [expandS, List.flatMap_append, List.flatMap_replicate]
      rw [hexp, bindOuts_go_of_long _ _ _ _ (by simp; omega)] at hbind
      have hp : (List.replicate r none ++ tuple.map some)[r + iK]? = some (some k.name) := by
        rw [List.getElem?_append_right (by simp)]; simp [hK]
      have hlater : k.name ∉ ((List.replicate r none ++ tuple.map some).drop (r + iK + 1)).filterMap id := by
        rw [show r + iK + 1 = (List.replicate r (none : Option String)).length + (iK + 1) by simp; omega,
          List.drop_append, ← List.map_drop]
        have := not_mem_drop_of_nodup hnd hK
        simpa [List.filterMap_map, ← List.map_drop] using this
      obtain ⟨x, hx, hst2⟩ := go_bound _ _ _ _ _ _ _ hbind hp hlater ⟨x0, hst0⟩
      -- x is the K-th child of the returned core
      have hxv : Native.nth (Val.int iK) (if r = 0 then v else Native.nth (Val.int r) v) = x := by
        unfold spread at hx
        split at hx
        · rename_i _ hs
          have hr0 : r = 0 := by
            rcases r with _ | r
            · rfl
            · simp [List.replicate_succ] at hs
          subst hr0
          simp only [if_true, Nat.zero_add] at hx ⊢
          rw [nth_int_eq, hx]; rfl
        · rename_i hs2
          rw [toList_ofList'] at hx
          obtain ⟨c, hc1, hc2⟩ := flat_core _ (fun _ => by simp) (fun _ => by simp) r v.toList iK x hx
          have hcv : Native.nth (Val.int r) v = c := by rw [nth_int_eq, hc1]; rfl
          by_cases hr : r = 0
          · subst hr; exact absurd rfl (hs2 (some "FN2-CORE"))
          · rw [if_neg hr, hcv, nth_int_eq, hc2]; rfl
      have hold : Native.nth (Val.int iK) (acts.getD j Val.nil) = x0 := by
        rw [List.getD_eq_getElem?_getD, hacts]
        simp only [Option.getD_some]
        rw [nth_int_eq, toList_ofList', hx0]; rfl
      have hfact := hpres acts v hv
      rw [hxv, hold] at hfact
      simp only [Columns.colGet, hdc, Bool.false_eq_true, if_false, hst2, hst0, bind, Except.bind, hget,
        hfact]

theorem adapter_inj (a b : String) (h : a ++ "@CORE" = b ++ "@CORE") : a = b := by
  have := congrArg String.toList h
  simp only [String.toList_append] at this
  exact String.toList_inj.mp (List.append_cancel_right this)

theorem adapter_beq (a b : String) : (adapterName a == adapterName b) = (a == b) := by
  unfold adapterName
  by_cases h : a = b
  · subst h; simp
  · have : a ++ "@CORE" ≠ b ++ "@CORE" := fun e => h (adapter_inj a b e)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem coreOp_name (tuple : List String) (o : Op) : (coreOp tuple o).name = o.name := by
  unfold coreOp; split
  · rfl
  · split <;> rfl

/-- The shape `keepsPhase_of_pres` asks of a core-only operation, as one test: no `:child`, its
core face's formals, its core formal at `j`, its outputs `r` values then the core, the kind's
child at `iK` of a layout naming each child once. -/
def opShape (tuple : List String) (k : Kind) (o : Op) (j r iK : Nat) : Bool :=
  o.callee.isNone && !o.coreFormals.isEmpty && o.coreFormals.length == o.coreIn.length &&
  !nativeCallNames.contains (adapterName o.name) && (adapterName o.name).endsWith "@CORE" &&
  o.coreIn[j]? == some (some "FN2-CORE") && o.coreOut == List.replicate r none ++ [some "FN2-CORE"] &&
  tuple[iK]? == some k.name && decide tuple.Nodup && decide (2 ≤ tuple.length) &&
  !directoryFields.contains "PHASE"

/-- **`keepsPhase_of_pres` for the operation the world names `n`**, its shape checked by `opShape`. -/
theorem keepsPhase_named (w : World) (tuple : List String) (k : Kind) (n : String) (o : Op)
    (j r iK : Nat) (ho : w.ops.find? (·.name == n) = some o)
    (hshape : opShape tuple k o j r iK = true)
    (hget : ∀ s t, callFn (coreWorld w tuple) (k.name ++ "-" ++ "PHASE") [s, t] =
      .ok (Native.nth s (Native.nth (Val.int 0) t)))
    (hpres : ∀ acts v, w.fns n acts = some v →
      Native.nth (Val.int 0) (Native.nth (Val.int iK)
          (if r = 0 then v else Native.nth (Val.int r) v)) =
        Native.nth (Val.int 0) (Native.nth (Val.int iK) (acts.getD j Val.nil))) :
    Columns.KeepsPhase (coreWorld w tuple) k n := by
  have hn : o.name = n := by
    have := List.find?_some ho
    simpa using this
  subst hn
  simp only [opShape, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hshape
  have hfind : (coreWorld w tuple).ops.find? (·.name == o.name) = some (coreOp tuple o) := by
    simp only [coreWorld, List.find?_map]
    have : ((fun x => x.name == o.name) ∘ coreOp tuple) = (fun x => x.name == o.name) := by
      funext x; simp [coreOp_name]
    rw [this, ho]; rfl
  have hadapt : w.ops.find? (fun o' => adapterName o'.name == adapterName o.name) = some o := by
    have : (fun o' : Op => adapterName o'.name == adapterName o.name) = (fun o' => o'.name == o.name) := by
      funext x; exact adapter_beq _ _
    rw [this, ho]
  exact keepsPhase_of_pres w tuple k o j r iK hfind h1 (by simpa using h2) (by simpa using h3) h4 h5
    hadapt h6 h7 h8 h9 h10 hget h11 hpres

/-- `keepsPhase_named` with the operation found by name in the test itself (`decide` evaluates it). -/
theorem keepsPhase_found (w : World) (tuple : List String) (k : Kind) (n : String) (j r iK : Nat)
    (hshape : (match w.ops.find? (·.name == n) with
      | some o => opShape tuple k o j r iK
      | none => false) = true)
    (hget : ∀ s t, callFn (coreWorld w tuple) (k.name ++ "-" ++ "PHASE") [s, t] =
      .ok (Native.nth s (Native.nth (Val.int 0) t)))
    (hpres : ∀ acts v, w.fns n acts = some v →
      Native.nth (Val.int 0) (Native.nth (Val.int iK)
          (if r = 0 then v else Native.nth (Val.int r) v)) =
        Native.nth (Val.int 0) (Native.nth (Val.int iK) (acts.getD j Val.nil))) :
    Columns.KeepsPhase (coreWorld w tuple) k n := by
  cases ho : w.ops.find? (·.name == n) with
  | none => rw [ho] at hshape; cases hshape
  | some o =>
    rw [ho] at hshape
    exact keepsPhase_named w tuple k n o j r iK ho hshape hget hpres

end

end Fn2.Arms.CorePhase
