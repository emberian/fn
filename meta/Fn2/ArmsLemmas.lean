import Fn2.Arms

/-!
# Fn2.ArmsLemmas: the generic lemmas PW3 rewrites by (LEAN-METATHEORY §9.3)

Proved once, over any printed `World`, for the interpreter of `Fn2.Arms` and ACL2's list-valued
stobjs (a stobj is a true list of fields, an array field the list of its elements):

* **evaluation**: `Except` binds of a value, `truthy` through `if`, a call of a translated
  function through its dispatch equation (`callFn_of_fns`);
* **the checked write**: `natLt` and `ColType.fits` as the ACL2 tests the generator writes
  (`(natp x)`, `(< x rows)`, `(unsigned-byte-p w v)` over the primitives), and the write itself:
  on a passing check `put` writes the table by slot and the directory by id through the setters,
  on a failing one it records `:machine-write` and writes nothing (`put_pass`, `put_fail`);
* **the row read**: `rowReads` is the column readers applied to the slot (the kind's table) or
  the id (the directory), in column order (`rowReads_eq`);
* **list-valued stobjs**: a field written by `UPDATE-NTH` at an index reads back at that index
  and leaves every other index as it was (`nthN_updateNthN_same`, `nthN_updateNthN_ne`), and
  for an array field inside a stobj (`nth_updateNth_nest_same`, `_ne_field`, `_ne_slot`);
* **the frame**: `setStobj` changes one child (`stobj_setStobj_same`, `stobj_setStobj_ne`); the
  checked write changes only the kind's table, the directory and the control (`put_frame`), and
  `flush` the same (`flush_frame`).

These hold for either subject of PW3 (§9.6): the child function's interpreter run, and the core
face that `fn2-turn` calls, whose stobj-let reads children out of `fn2-core` and writes them back
through the same list-valued fields.
-/

namespace Fn2.Arms
open Fn2.ACL2

/-! ### Evaluation -/

@[simp] theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

@[simp] theorem except_pure_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (pure a >>= f : Except ε β) = f a := rfl

@[simp] theorem except_map_ok {ε α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

@[simp] theorem Val.truthy_ite (p : Prop) [Decidable p] (a b : Val) :
    (if p then a else b).truthy = if p then a.truthy else b.truthy := by
  split <;> rfl

@[simp] theorem Val.truthy_nil : Val.nil.truthy = false := rfl
@[simp] theorem Val.truthy_t : Val.t.truthy = true := rfl
@[simp] theorem Val.truthy_ofBool (b : Bool) : (Val.ofBool b).truthy = b := by
  cases b <;> rfl

/-- A call of a translated function: no native answers its name, the dispatch does. -/
theorem callFn_of_fns (w : World) (f : String) (args : List Val) (v : Val)
    (hn : nativeCallNames.contains f = false) (hf : w.fns f args = some v) :
    callFn w f args = .ok v := by
  simp [callFn, nativeCall_none f args hn, hf]

/-! ### The checked write's tests, as the ACL2 tests over the primitives -/

theorem not_decide_lt_zero (x : Int) : (!decide (x < 0)) = decide (0 ≤ x) := by
  cases h : decide (0 ≤ x) <;> simp_all <;> omega

theorem natLt_eq_true_iff (a b : Val) :
    natLt a b = true ↔ ∃ x y : Int, a = .int x ∧ b = .int y ∧ 0 ≤ x ∧ x < y := by
  cases a <;> cases b <;> simp [natLt]

/-- `natLt` is ACL2's `(and (natp x) (< x rows))`: `natp` as `(integerp x)` and `(not (< x 0))`,
`<` with its completion (a non-number is 0), so a non-integer bound fails for a natural `x`. -/
theorem natLt_eq_acl2 (a b : Val) :
    natLt a b = ((Prim.integerp a).truthy && !(Prim.lt a (.int 0)).truthy && (Prim.lt a b).truthy) := by
  cases a <;> cases b <;> simp [natLt, Prim.integerp, Prim.lt, Val.isInt, Val.toInt, Val.ofBool]  <;>
    rw [not_decide_lt_zero]

theorem fits_uw_eq_true_iff (w : Nat) (v : Val) :
    ColType.fits (.uw w) v = true ↔ ∃ i : Int, v = .int i ∧ 0 ≤ i ∧ i < 2 ^ w := by
  cases v <;> simp [ColType.fits]

theorem fits_enum_eq_true_iff (n : Nat) (v : Val) :
    ColType.fits (.enum n) v = true ↔ ∃ i : Int, v = .int i ∧ 0 ≤ i ∧ i < n := by
  cases v <;> simp [ColType.fits]

theorem Native.expt_two (w : Nat) : Native.expt (.int 2) (.int w) = .int (2 ^ w) := by
  cases w with
  | zero => rfl
  | succ k =>
    simp only [Native.expt, Val.toInt]
    have h2 : (0 : Int) < ((k + 1 : Nat) : Int) := by omega
    simp only [show ((k + 1 : Nat) : Int) ≠ 0 by omega, if_false, show (2 : Int) ≠ 0 by omega, h2, if_true]
    simp

/-- A column of width `w` fits exactly what ACL2's `(unsigned-byte-p w v)` accepts:
`(integerp v)`, `(not (< v 0))`, `(< v (expt 2 w))`. -/
theorem fits_uw_eq_acl2 (w : Nat) (v : Val) :
    ColType.fits (.uw w) v = ((Prim.integerp v).truthy && !(Prim.lt v (.int 0)).truthy &&
      (Prim.lt v (Native.expt (.int 2) (.int w))).truthy) := by
  rw [Native.expt_two]
  cases v <;> simp [ColType.fits, Prim.integerp, Prim.lt, Val.isInt, Val.toInt, Val.ofBool]  <;>
    rw [not_decide_lt_zero]

/-- An enum column of `n` tags fits `(natp v)` and `(< v n)`. -/
theorem fits_enum_eq_acl2 (n : Nat) (v : Val) :
    ColType.fits (.enum n) v = ((Prim.integerp v).truthy && !(Prim.lt v (.int 0)).truthy &&
      (Prim.lt v (.int n)).truthy) := by
  cases v <;> simp [ColType.fits, Prim.integerp, Prim.lt, Val.isInt, Val.toInt, Val.ofBool]  <;>
    rw [not_decide_lt_zero]

/-! ### List-valued stobjs -/

theorem nthN_updateNthN_same (n : Nat) (v l : Val) :
    Native.nthN n (Native.updateNthN n v l) = v := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => simp [Native.updateNthN, Native.nthN, ih]

theorem nthN_atom (n : Nat) (l : Val) (h : l.isCons = false) : Native.nthN n l = Val.nil := by
  cases l <;> simp_all [Val.isCons, Native.nthN]

theorem nthN_updateNthN_ne (m n : Nat) (v l : Val) (h : m ≠ n) :
    Native.nthN m (Native.updateNthN n v l) = Native.nthN m l := by
  induction n generalizing m l with
  | zero =>
    cases m with
    | zero => exact absurd rfl h
    | succ m =>
      simp only [Native.updateNthN, Native.nthN]
      cases l <;> simp [Val.cdr, Native.nthN, Val.nil]
  | succ n ih =>
    cases m with
    | zero => cases l <;> simp [Native.updateNthN, Native.nthN, Val.car, Val.nil]
    | succ m =>
      have := ih m l.cdr (by omega)
      cases l <;> simp_all [Native.updateNthN, Native.nthN, Val.cdr, Val.nil]

theorem nth_updateNth_same (i : Nat) (v l : Val) :
    Native.nth (.int i) (Native.updateNth (.int i) v l) = v := by
  simp [Native.nth, Native.updateNth, Val.nfix, Val.toInt, nthN_updateNthN_same]

theorem nth_updateNth_ne (i j : Nat) (v l : Val) (h : i ≠ j) :
    Native.nth (.int i) (Native.updateNth (.int j) v l) = Native.nth (.int i) l := by
  simp [Native.nth, Native.updateNth, Val.nfix, Val.toInt, nthN_updateNthN_ne i j v l h]

/-- A stobj's array field `f` written at slot `s` (ACL2's `UPDATE-NTH-ARRAY f s v stobj`, the body
of every generated column updater) reads back `v` at `(f, s)`. -/
theorem nth_updateNth_nest_same (f s : Nat) (v st : Val) :
    Native.nth (.int s) (Native.nth (.int f)
      (Native.updateNth (.int f) (Native.updateNth (.int s) v (Native.nth (.int f) st)) st)) = v := by
  rw [nth_updateNth_same, nth_updateNth_same]

theorem nth_updateNth_nest_ne_field (f g s t : Nat) (v st : Val) (h : g ≠ f) :
    Native.nth (.int t) (Native.nth (.int g)
      (Native.updateNth (.int f) (Native.updateNth (.int s) v (Native.nth (.int f) st)) st)) =
      Native.nth (.int t) (Native.nth (.int g) st) := by
  rw [nth_updateNth_ne g f _ _ h]

theorem nth_updateNth_nest_ne_slot (f s t : Nat) (v st : Val) (h : t ≠ s) :
    Native.nth (.int t) (Native.nth (.int f)
      (Native.updateNth (.int f) (Native.updateNth (.int s) v (Native.nth (.int f) st)) st)) =
      Native.nth (.int t) (Native.nth (.int f) st) := by
  rw [nth_updateNth_same, nth_updateNth_ne t s _ _ h]

/-- Writes to distinct logical fields commute, including on incomplete lists. -/
theorem updateNthN_commute (i j : Nat) (v w st : Val) (h : i ≠ j) :
    Native.updateNthN i v (Native.updateNthN j w st) =
      Native.updateNthN j w (Native.updateNthN i v st) := by
  induction i generalizing j st with
  | zero => cases j with
    | zero => exact (h rfl).elim
    | succ j => rfl
  | succ i ih => cases j with
    | zero => rfl
    | succ j =>
      exact congrArg (Val.cons st.car) (ih j st.cdr (by omega))

theorem updateNth_commute (i j : Nat) (v w st : Val) (h : i ≠ j) :
    Native.updateNth (.int i) v (Native.updateNth (.int j) w st) =
      Native.updateNth (.int j) w (Native.updateNth (.int i) v st) := by
  simpa [Native.updateNth, Val.nfix, Val.toInt] using updateNthN_commute i j v w st h

/-- A simultaneous batch of column writes has no dependency between distinct
array fields; the slot and values may be arbitrary ACL2 values. -/
theorem updateNth_array_commute (i j : Nat) (slot v w st : Val) (h : i ≠ j) :
    Native.updateNth (.int i)
      (Native.updateNth slot v (Native.nth (.int i)
        (Native.updateNth (.int j) (Native.updateNth slot w (Native.nth (.int j) st)) st)))
      (Native.updateNth (.int j) (Native.updateNth slot w (Native.nth (.int j) st)) st) =
    Native.updateNth (.int j)
      (Native.updateNth slot w (Native.nth (.int j)
        (Native.updateNth (.int i) (Native.updateNth slot v (Native.nth (.int i) st)) st)))
      (Native.updateNth (.int i) (Native.updateNth slot v (Native.nth (.int i) st)) st) := by
  rw [nth_updateNth_ne i j _ _ h, nth_updateNth_ne j i _ _ (Ne.symm h)]
  exact updateNth_commute i j _ _ st h

/-! ### The frame of the interpreter's state -/

theorem find_set_ne (l : List (String × Val)) (n n' : String) (v : Val) (h : n ≠ n') :
    (l.map fun p => if p.1 == n then (n, v) else p).find? (·.1 == n') = l.find? (·.1 == n') := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hp : p.1 = n
    · have e1 : (p.1 == n) = true := by simp [hp]
      have e2 : (n == n') = false := by simp [h]
      have e3 : (p.1 == n') = false := by simp [hp, h]
      simp only [e1, if_true, e2, e3, ih]
    · have e1 : (p.1 == n) = false := by simp [hp]
      simp only [e1, Bool.false_eq_true, if_false]
      cases (p.1 == n') <;> first | rfl | exact ih

theorem find_set_same (l : List (String × Val)) (n : String) (v : Val) :
    (l.map fun p => if p.1 == n then (n, v) else p).find? (·.1 == n) =
      (l.find? (·.1 == n)).map fun _ => (n, v) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases hp : p.1 = n
    · have e1 : (p.1 == n) = true := by simp [hp]
      simp [e1]
    · have e1 : (p.1 == n) = false := by simp [hp]
      simp only [e1, Bool.false_eq_true, if_false, ih]

theorem stobj_setStobj_ne (st : St) (n n' : String) (v : Val) (h : n ≠ n') :
    stobj (setStobj st n v) n' = stobj st n' := by
  simp only [stobj, setStobj, find_set_ne _ _ _ _ h]

theorem stobj_setStobj_same (st : St) (n : String) (v w : Val) (h : stobj st n = .ok w) :
    stobj (setStobj st n v) n = .ok v := by
  simp only [stobj, setStobj, find_set_same] at h ⊢
  cases hf : st.stobjs.find? (·.1 == n) with
  | none => simp [hf] at h
  | some p => rfl

/-- The checked write, passing: the pending fields go to the kind's table by slot and the
directory fields to the directory by id, through the generated setters, nothing else. -/
theorem put_pass (w : World) (f : Frame) (st : St) (pairs : List (String × Val))
    (slot id table dir control rows drows : Val)
    (hslot : var st "SLOT" = .ok slot) (hid : var st "ID" = .ok id)
    (ht : stobj st f.kind.name = .ok table) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hrows : callFn w (f.kind.name ++ "-ROWS") [table] = .ok rows)
    (hdrows : callFn w "FN2-MACHINES-ROWS" [dir] = .ok drows)
    (hpass : (natLt slot rows && ((pairs.filter fun p => directoryFields.contains p.1).isEmpty ||
        natLt id drows) && pairs.all fun (n, v) => match f.kind.columns.find? (·.1 == n) with
          | some (_, ty) => ty.fits v
          | none => false) = true) :
    put w f st pairs = (do
      let table ← (pairs.filter fun p => !directoryFields.contains p.1).foldlM
        (fun t (n, v) => callFn w (f.kind.name ++ "-SET-" ++ n) [slot, v, t]) table
      let dir ← (pairs.filter fun p => directoryFields.contains p.1).foldlM
        (fun d (n, v) => callFn w ("FN2-MACHINES-SET-" ++ n) [id, v, d]) dir
      pure (setStobj (setStobj st f.kind.name table) "FN2-MACHINES" dir)) := by
  simp only [put, hslot, hid, ht, hd, hc, hrows, hdrows, except_ok_bind]
  split
  · rfl
  · rename_i hn; exact (hn hpass).elim

/-- The checked write, failing: `:machine-write` recorded in the control, nothing written. -/
theorem put_fail (w : World) (f : Frame) (st : St) (pairs : List (String × Val))
    (slot id table dir control rows drows : Val)
    (hslot : var st "SLOT" = .ok slot) (hid : var st "ID" = .ok id)
    (ht : stobj st f.kind.name = .ok table) (hd : stobj st "FN2-MACHINES" = .ok dir)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hrows : callFn w (f.kind.name ++ "-ROWS") [table] = .ok rows)
    (hdrows : callFn w "FN2-MACHINES-ROWS" [dir] = .ok drows)
    (hfail : (natLt slot rows && ((pairs.filter fun p => directoryFields.contains p.1).isEmpty ||
        natLt id drows) && pairs.all fun (n, v) => match f.kind.columns.find? (·.1 == n) with
          | some (_, ty) => ty.fits v
          | none => false) = false) :
    put w f st pairs = (do
      let r ← const w "*FN2-STOP-REASON-MACHINE-WRITE*"
      let control ← callFn w "FN2-CONTROL-RECORD-STOP" [r, control]
      pure (setStobj st "FN2-CONTROL" control)) := by
  simp only [put, hslot, hid, ht, hd, hc, hrows, hdrows, except_ok_bind]
  split
  · rename_i hy; exact absurd (hy.symm.trans hfail) (by simp)
  · rfl

/-- One `Except` step of a hypothesis `h : (do let x ← e; k x) = .ok r`: the error case is
absurd, the value case continues with `x` named. -/
local macro "except_step " h:ident : tactic =>
  `(tactic| ((try simp only [bind, Except.bind] at ($h)); split at ($h); · exact absurd $h (by simp)))

/-- The frame of the checked write: a child other than the kind's table, the directory and the
control leaves it as it entered, and the bindings, the pending fields and the phase form are
untouched (the flush clears them, not the write). -/
theorem put_frame (w : World) (f : Frame) (st st' : St) (pairs : List (String × Val))
    (h : put w f st pairs = .ok st') (c : String) (h1 : c ≠ f.kind.name)
    (h2 : c ≠ "FN2-MACHINES") (h3 : c ≠ "FN2-CONTROL") :
    stobj st' c = stobj st c ∧ st'.vars = st.vars ∧ st'.pending = st.pending ∧ st'.next = st.next := by
  unfold put at h
  except_step h; except_step h; except_step h; except_step h; except_step h; except_step h
  except_step h
  split at h
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    refine ⟨?_, rfl, rfl, rfl⟩
    rw [stobj_setStobj_ne _ _ _ _ (Ne.symm h2), stobj_setStobj_ne _ _ _ _ (Ne.symm h1)]
  · except_step h; except_step h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨stobj_setStobj_ne _ _ _ _ (Ne.symm h3), rfl, rfl, rfl⟩

/-- The frame of a flush: the checked write's frame; the bindings are untouched. -/
theorem flush_frame (w : World) (f : Frame) (st st' : St) (h : flush w f st = .ok st')
    (c : String) (h1 : c ≠ f.kind.name) (h2 : c ≠ "FN2-MACHINES") (h3 : c ≠ "FN2-CONTROL") :
    stobj st' c = stobj st c ∧ st'.vars = st.vars := by
  unfold flush at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h <;> try (simp only [reduceCtorEq] at h; done))
  all_goals
    simp only [Except.ok.injEq] at h; subst h
    first
      | exact ⟨rfl, rfl⟩
      | (have := put_frame w f _ _ _ ‹put w f st _ = Except.ok _› c h1 h2 h3
         exact ⟨this.1, this.2.1⟩)

/-! ### The row read -/

theorem rowReads_mapM (w : World) (k : Kind) (id slot table dir : Val) (read : String → Val)
    (cs : List (String × ColType))
    (hread : ∀ c ∈ cs.map (·.1),
      callFn w (if directoryFields.contains c then "FN2-MACHINES-" ++ c else k.name ++ "-" ++ c)
        (if directoryFields.contains c then [id, dir] else [slot, table]) = .ok (read c)) :
    (cs.mapM fun (c, _) => do
      let v ← if directoryFields.contains c then callFn w ("FN2-MACHINES-" ++ c) [id, dir]
              else callFn w (k.name ++ "-" ++ c) [slot, table]
      pure ("ROW-" ++ c, v)) = (.ok (cs.map fun (c, _) => ("ROW-" ++ c, read c)) : Except String Env) := by
  induction cs with
  | nil => rfl
  | cons p cs ih =>
    obtain ⟨c, ty⟩ := p
    have hc := hread c (by simp)
    have hrest := ih (fun c' hc' => hread c' (by simp [hc']))
    rw [List.mapM_cons, hrest]
    by_cases hdir : directoryFields.contains c = true
    · simp only [hdir, if_true] at hc ⊢; rw [hc]; rfl
    · simp only [hdir, Bool.false_eq_true, if_false] at hc ⊢; rw [hc]; rfl

/-- `rowReads` is the column readers, in column order: the kind's own columns by slot from its
table, the directory's (`READY-PREV READY-NEXT WAIT-REASON`) by id from `fn2-machines`. -/
theorem rowReads_eq (w : World) (k : Kind) (stobjs : List (String × Val)) (id slot table dir : Val)
    (ht : stobjs.find? (·.1 == k.name) = some (k.name, table))
    (hd : stobjs.find? (·.1 == "FN2-MACHINES") = some ("FN2-MACHINES", dir))
    (read : String → Val)
    (hread : ∀ c ∈ k.columns.map (·.1),
      callFn w (if directoryFields.contains c then "FN2-MACHINES-" ++ c else k.name ++ "-" ++ c)
        (if directoryFields.contains c then [id, dir] else [slot, table]) = .ok (read c)) :
    rowReads w k stobjs id slot = .ok (k.columns.map fun (c, _) => ("ROW-" ++ c, read c)) := by
  simp only [rowReads, ht, hd]
  exact rowReads_mapM w k id slot table dir read k.columns hread


/-- Appending the child bindings cannot shadow an already-bound local variable. -/
theorem env_get_append_of_some (front back : Env) (name : String) (value : Val)
    (h : front.get? name = some value) : (front ++ back).get? name = some value := by
  cases hf : front.find? (·.1 == name) <;> simp_all [Env.get?, List.find?_append]

theorem var_env_bound (st : St) (name : String) (value : Val)
    (h : var st name = .ok value) : (st.vars ++ st.stobjs).get? name = some value := by
  apply env_get_append_of_some
  cases hv : st.vars.get? name <;> simp_all [var]

theorem var_setStobj (st : St) (child name : String) (value : Val) :
    var (setStobj st child value) name = var st name := by rfl

/-- A flush with no pending fields or phase is the identity in every world. -/
theorem flush_empty (w : World) (f : Frame) (st : St)
    (hp : st.pending = []) (hn : st.next = none) : flush w f st = .ok st := by
  cases st
  simp_all [flush]
  rfl

/-- A global stop flushes first, records its reason, and charges the declared empty work. -/
theorem run_stop_global (w : World) (f : Frame) (st : St) (fuel : Nat)
    (reason : String) (control reasonCode empty stopped : Val)
    (hp : st.pending = []) (hn : st.next = none)
    (hc : stobj st "FN2-CONTROL" = .ok control)
    (hi : f.kind.stops.idxOf? reason = none)
    (hr : const w ("*FN2-STOP-REASON-" ++ reason ++ "*") = .ok reasonCode)
    (he : const w "*FN2-WORK-EMPTY*" = .ok empty)
    (ho : f.observe = false)
    (hs : callFn w "FN2-CONTROL-RECORD-STOP" [reasonCode,control] = .ok stopped) :
    run w f (fuel+1) st [.stop reason none] =
    chargeResult f (setStobj st "FN2-CONTROL" stopped) (.int 0) empty (.int 0) Val.nil := by
  simp only [run, hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    flush_empty w f st hp hn, hc, hi, hr, he, hs, except_ok_bind, stopEnd, ho, evOpt]
  rfl

/-- An open-answer operation follows its accepted continuation or the declared stop. -/
theorem run_do_accept_stop (w : World) (f : Frame) (st sf : St) (fuel : Nat)
    (v reason : String) (c : Call) (accept : List Val) (rest : List Step) (op : Op) (r code : Val)
    (hp : st.pending = []) (hn : st.next = none)
    (hfind : findOp w c.op = .ok op)
    (hcall : callOp w f.kind st c = .ok (op,r))
    (hbind : bindOuts st op.stobjsOut [v] r = .ok sf)
    (hanswers : op.answers = .open_)
    (hcode : var sf v = .ok code)
    (href : f.refusal = [.stop reason none]) :
    run w f (fuel+1) st (.do_ [v] c true accept none [] [] :: rest) =
      if codeIn code accept then run w f fuel sf rest
      else run w f fuel sf [.stop reason none] := by
  simp only [run, flush_empty w f st hp hn, hfind, hcall, hbind, hanswers, hcode,
    href, except_ok_bind, Bool.false_eq_true, ↓reduceIte, List.find?_nil,
    List.isEmpty_cons, Bool.not_false, faultRoute, Bool.false_and]
  rfl

end Fn2.Arms
