import Fn2.Arms
import Fn2.ArmsLemmas

/-!
# Fn2.Pathway: PW3, the generator's correctness per arm, stated (LEAN-METATHEORY §9)

A child-form arm function `FN` that ACL2 generated from a kind's declaration takes its value
formals and the children its narrowed signature names (`Sig.takes`) and returns its results and
the children `Sig.returns` names. The definitional interpreter `runArm` runs the declaration
itself on the kind's whole tuple. PW3 for one arm: on every argument list `FN`'s guard accepts,
whatever the children `FN` does not take hold, the interpreter terminates with enough fuel, its
results and returned children are `FN`'s, and every child `FN` does not return leaves it as it
entered.

`ArmCorrect` is stated over an arbitrary dispatch `fns` and guard table, so one statement serves
every world the printer emits (`Fn2.Instances.LayerAKinds.world`, a mutant's). Its status, teeth
and premise are in §9's PW3 row: measured on the recorded calls (`Fn2.Measure`, which computes
exactly `widen`, `entering`, `normalize` and `reconstruct` below, on the recorded inputs with
sentinel `rest`: finite observations of the conclusion, not instances of the quantified statement), not yet proved; a proof needs the reader and the
term evaluator total (they are `partial`, so opaque to the kernel).
-/

namespace Fn2.Pathway
open Fn2.ACL2 Fn2.Arms

/-- The value formals before the children: `(id slot kind ordinal budget)` for an arm,
`(id slot kind ordinal event outcome reason count aux0 aux1)` for a handler. -/
def nPre (observe : Bool) : Nat := if observe then 10 else 5

/-- The results before the children: `(bytes steps descriptors runnable)` or `(wake)`. -/
def nOuts (observe : Bool) : Nat := if observe then 1 else 4

def takes (k : Kind) (a : Arm) : List String := (a.sig.map (·.takes)).getD k.tuple
def returns (k : Kind) (a : Arm) : List String := (a.sig.map (·.returns)).getD k.tuple

/-- The children entering the interpreter: those `FN` takes from its arguments, the others from
`rest`. -/
def entering (k : Kind) (a : Arm) (given : List Val) (rest : String → Val) : List Val :=
  let g := (takes k a).zip given
  k.tuple.map fun c => ((g.find? (·.1 == c)).map (·.2)).getD (rest c)

/-- The interpreter's arguments: the value formals, then the kind's whole tuple. -/
def widen (k : Kind) (a : Arm) (pre given : List Val) (rest : String → Val) : List Val :=
  pre ++ entering k a given rest

/-- The interpreter's result cut to `FN`'s: its results, then the children `FN` returns. -/
def project (k : Kind) (a : Arm) (observe : Bool) (v : Val) : Val :=
  let xs := v.toList
  let tup := k.tuple.zip (xs.drop (nOuts observe))
  Val.ofList (xs.take (nOuts observe) ++ (returns k a).map fun c =>
    ((tup.find? (·.1 == c)).map (·.2)).getD Val.nil)

/-- `FN`'s value as a list: a function with one value in all returns it bare. -/
def normalize (k : Kind) (a : Arm) (observe : Bool) (v : Val) : Val :=
  if nOuts observe + (returns k a).length == 1 then Val.ofList [v] else v

/-- The interpreter's whole result that `FN`'s value `v` (normalized) determines: `FN`'s results,
then the kind's tuple with each returned child taken from `v` by name and every other child as it
entered. Equality with this is `project` agreement, the frame, and the result's exact shape at
once (LEAN-METATHEORY §11, session 5). -/
def reconstruct (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val) : Val :=
  let xs := v.toList
  let ret := (returns k a).zip (xs.drop (nOuts observe))
  Val.ofList (xs.take (nOuts observe) ++ (k.tuple.zip input).map fun (c, i) =>
    ((ret.find? (·.1 == c)).map (·.2)).getD i)

/-- The arm's metadata as PW3 needs it, decidable: a child-form kind, a duplicate-free tuple, a
signature inside it without duplicates, and the signature's result count the arm's. -/
def ArmWF (k : Kind) (a : Arm) (observe : Bool) : Bool :=
  k.childForm && k.tuple.eraseDups.length == k.tuple.length &&
  (takes k a).all k.tuple.contains && (returns k a).all k.tuple.contains &&
  (takes k a).eraseDups.length == (takes k a).length &&
  (returns k a).eraseDups.length == (returns k a).length &&
  (a.sig.map (·.results == nOuts observe)).getD true

/-- `FN`'s value has exactly its signature's shape: a true list of its results and returned
children. -/
def NarrowShape (k : Kind) (a : Arm) (observe : Bool) (v : Val) : Prop :=
  (normalize k a observe v).toList.length = nOuts observe + (returns k a).length ∧
  Val.ofList (normalize k a observe v).toList = normalize k a observe v

/-- The guard premise: a stated guard holds; a function with no stated guard has ACL2's guard
`T`, so the premise never becomes vacuous through a missing table entry. -/
def Guarded (guard : String → List Val → Option Val) (fn : String) (args : List Val) : Prop :=
  match guard fn args with
  | some g => g.truthy = true
  | none => True

/-- **PW3 for one arm** (session 5's form). `w.fns` is the translated world's dispatch (`FN` is
`w.fns a.fn`), `guard` its guard table. For every input of the right shape on which `FN`'s guard
holds, `FN` has a value of its signature's shape, and for every value of the children `FN` does
not take, the interpreter on the declaration terminates (past some fuel) with exactly the whole
result that value determines. Read with `rest` universal, this is output independence from the
untaken children, not absence of reads. -/
def ArmCorrect (w : World) (guard : String → List Val → Option Val) (k : Kind) (a : Arm)
    (observe : Bool) : Prop :=
  ArmWF k a observe = true ∧
  ∀ (pre given : List Val),
    pre.length = nPre observe → given.length = (takes k a).length →
    Guarded guard a.fn (pre ++ given) →
    ∃ v, w.fns a.fn (pre ++ given) = some v ∧ NarrowShape k a observe v ∧
      ∀ rest : String → Val, ∃ N, ∀ fuel, N ≤ fuel →
        runArm w k a observe (widen k a pre given rest) fuel =
          .ok (reconstruct k a observe (entering k a given rest) (normalize k a observe v))

/-- PW3 for a kind: every arm, handler and sub-arm. -/
def KindCorrect (w : World) (guard : String → List Val → Option Val) (k : Kind) : Prop :=
  (∀ a ∈ k.arms, ArmCorrect w guard k a false) ∧
  (∀ a ∈ k.subarms, ArmCorrect w guard k a false) ∧
  (∀ a ∈ k.observes, ArmCorrect w guard k a true)

/-! ## PW3 Wrapper Preservation Theorems (`entering`, `widen`, `project`, `reconstruct`) -/

theorem toList_ofList (xs : List Val) : (Val.ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Val.ofList, Val.toList, ih]

theorem entering_length (k : Kind) (a : Arm) (given : List Val) (rest : String → Val) :
    (entering k a given rest).length = k.tuple.length := by
  simp [entering]

theorem widen_length (k : Kind) (a : Arm) (pre given : List Val) (rest : String → Val) :
    (widen k a pre given rest).length = pre.length + k.tuple.length := by
  simp [widen, entering_length]

theorem find_zip_none_of_not_mem (xs : List String) (ys : List Val) (c : String)
    (hc : c ∉ xs) :
    (xs.zip ys).find? (·.1 == c) = none := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hne : (x == c) = false := beq_eq_false_iff_ne.mpr fun h => hc (by simp [h])
      have hc' : c ∉ xs := fun hm => hc (List.mem_cons_of_mem x hm)
      simp [List.zip_cons_cons, hne, ih ys hc']

theorem entering_frame_entry (k : Kind) (a : Arm) (given : List Val) (rest : String → Val)
    (c : String) (hc : c ∉ takes k a) :
    ((((takes k a).zip given).find? (·.1 == c)).map (·.2)).getD (rest c) = rest c := by
  rw [find_zip_none_of_not_mem (takes k a) given c hc]
  rfl

theorem reconstruct_frame_entry (k : Kind) (a : Arm) (observe : Bool) (v : Val)
    (c : String) (i : Val) (hc : c ∉ returns k a) :
    ((((returns k a).zip (v.toList.drop (nOuts observe))).find? (·.1 == c)).map (·.2)).getD i = i := by
  rw [find_zip_none_of_not_mem (returns k a) (v.toList.drop (nOuts observe)) c hc]
  rfl

theorem reconstruct_toList_length (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val)
    (houts : nOuts observe ≤ v.toList.length) (hin : input.length = k.tuple.length) :
    (reconstruct k a observe input v).toList.length = nOuts observe + k.tuple.length := by
  simp [reconstruct, toList_ofList, hin, Nat.min_eq_left houts]

theorem reconstruct_results (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val)
    (houts : nOuts observe ≤ v.toList.length) :
    (reconstruct k a observe input v).toList.take (nOuts observe) =
      v.toList.take (nOuts observe) := by
  simp only [reconstruct, toList_ofList]
  have hlen : (v.toList.take (nOuts observe)).length = nOuts observe := by
    simp [Nat.min_eq_left houts]
  rw [List.take_left' hlen]

theorem reconstruct_children (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val)
    (houts : nOuts observe ≤ v.toList.length) :
    (reconstruct k a observe input v).toList.drop (nOuts observe) =
      (k.tuple.zip input).map fun (c, i) =>
        ((((returns k a).zip (v.toList.drop (nOuts observe))).find? (·.1 == c)).map (·.2)).getD i := by
  simp only [reconstruct, toList_ofList]
  have hlen : (v.toList.take (nOuts observe)).length = nOuts observe := by
    simp [Nat.min_eq_left houts]
  rw [List.drop_left' hlen]

theorem mem_fst_of_mem_zip {α β : Type} {rs : List α} {ys : List β} {c : α} {y : β}
    (h : (c, y) ∈ rs.zip ys) : c ∈ rs := by
  induction rs generalizing ys with
  | nil => simp at h
  | cons r rs ih =>
    cases ys with
    | nil => simp at h
    | cons y' ys' =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩ | htl
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih htl)

theorem find_zip_of_nodup {rs : List String} {ys : List Val} {c : String} {y : Val}
    (hnd : rs.Nodup) (hmem : (c, y) ∈ rs.zip ys) :
    ((rs.zip ys).find? (·.1 == c)).map (·.2) = some y := by
  induction rs generalizing ys with
  | nil => simp at hmem
  | cons r rs ih =>
    cases ys with
    | nil => simp at hmem
    | cons y' ys' =>
      rw [List.nodup_cons] at hnd
      obtain ⟨hr_not_mem, hnd_rs⟩ := hnd
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | htl
      · simp
      · have hc_mem : c ∈ rs := mem_fst_of_mem_zip htl
        have hne : (r == c) = false := beq_eq_false_iff_ne.mpr fun heq => hr_not_mem (heq ▸ hc_mem)
        simp [List.zip_cons_cons, hne, ih hnd_rs htl]

theorem zip_map_find_some (g : String → Option Val) (ts : List String) (ins : List Val)
    (hlen : ins.length = ts.length) (c : String) (hc : c ∈ ts) (val : Val) (hg : g c = some val) :
    ((ts.zip ((ts.zip ins).map fun (x, i) => (g x).getD i)).find? (·.1 == c)).map (·.2) =
      some val := by
  induction ts generalizing ins with
  | nil => contradiction
  | cons t ts ih =>
    cases ins with
    | nil => simp at hlen
    | cons i ins' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, List.map_cons, List.find?]
      cases htc : (t == c)
      · have hne : c ≠ t := fun heq => by
          have : (t == c) = true := beq_iff_eq.mpr heq.symm
          rw [htc] at this; contradiction
        have hc' : c ∈ ts := by
          rcases List.mem_cons.mp hc with rfl | hmem
          · exact absurd rfl hne
          · exact hmem
        exact ih ins' hlen hc'
      · have heq : t = c := beq_iff_eq.mp htc
        subst heq
        simp [hg]

theorem map_eq_of_zip_mem {α β : Type} (f : α → β) (rs : List α) (ys : List β)
    (hlen : ys.length = rs.length)
    (h : ∀ p ∈ rs.zip ys, f p.1 = p.2) :
    rs.map f = ys := by
  induction rs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨h (r, y) (by simp), ih ys hlen (fun p hp => h p (by simp [hp]))⟩

/-- **PW3 Wrapper Preservation (`project_reconstruct`)**: Projecting the reconstructed full
    tuple output back to the narrowed arm signature recovers `normalize k a observe v`
    whenever `returns k a ⊆ k.tuple`, `(returns k a).Nodup`, `input.length = k.tuple.length`,
    and `NarrowShape k a observe v` holds. -/
theorem project_reconstruct (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val)
    (htup : ∀ c ∈ returns k a, c ∈ k.tuple)
    (hnd : (returns k a).Nodup)
    (hin : input.length = k.tuple.length)
    (hshape : NarrowShape k a observe v) :
    project k a observe (reconstruct k a observe input (normalize k a observe v)) =
      normalize k a observe v := by
  obtain ⟨hlen, hof⟩ := hshape
  generalize normalize k a observe v = u at hlen hof ⊢
  have houts : nOuts observe ≤ u.toList.length := by omega
  have htake_len : (u.toList.take (nOuts observe)).length = nOuts observe := by
    simp [Nat.min_eq_left houts]
  have hdrop_len : (u.toList.drop (nOuts observe)).length = (returns k a).length := by
    simp [List.length_drop, hlen]
  dsimp only [project, reconstruct]
  rw [toList_ofList, List.take_left' htake_len, List.drop_left' htake_len]
  have hmap :
      (returns k a).map (fun c =>
        (((k.tuple.zip ((k.tuple.zip input).map fun (x, i) =>
          ((((returns k a).zip (u.toList.drop (nOuts observe))).find? (·.1 == x)).map (·.2)).getD i)).find?
          (·.1 == c)).map (·.2)).getD Val.nil) =
      u.toList.drop (nOuts observe) := by
    apply map_eq_of_zip_mem _ (returns k a) (u.toList.drop (nOuts observe)) hdrop_len
    intro ⟨c, y⟩ hmem
    have hc_ret : c ∈ returns k a := mem_fst_of_mem_zip hmem
    have hc_tup : c ∈ k.tuple := htup c hc_ret
    have hg := find_zip_of_nodup hnd hmem
    have hfind := zip_map_find_some
      (fun x => (((returns k a).zip (u.toList.drop (nOuts observe))).find? (·.1 == x)).map (·.2))
      k.tuple input hin c hc_tup y hg
    dsimp only
    rw [hfind]
    rfl
  rw [hmap, List.take_append_drop, hof]

/-- **PW3 End-to-End Projection & Frame Preservation (`armCorrect_project_preserve`)**:
    When `ArmCorrect w guard k a observe` holds, running the definitional interpreter `runArm`
    on `widen k a pre given rest` produces an output `out` whose `project` equals
    `normalize k a observe v` and whose unreturned children equal `entering k a given rest`. -/
theorem armCorrect_project_preserve (w : World) (guard : String → List Val → Option Val)
    (k : Kind) (a : Arm) (observe : Bool)
    (hcorr : ArmCorrect w guard k a observe)
    (htup : ∀ c ∈ returns k a, c ∈ k.tuple)
    (hnd : (returns k a).Nodup)
    (pre given : List Val) (rest : String → Val)
    (hpre : pre.length = nPre observe)
    (hgiven : given.length = (takes k a).length)
    (hguard : Guarded guard a.fn (pre ++ given)) :
    ∃ v N, w.fns a.fn (pre ++ given) = some v ∧ NarrowShape k a observe v ∧
      ∀ fuel, N ≤ fuel →
        ∃ out, runArm w k a observe (widen k a pre given rest) fuel = .ok out ∧
          project k a observe out = normalize k a observe v := by
  obtain ⟨_, hfn⟩ := hcorr
  obtain ⟨v, hv, hshape, hrun⟩ := hfn pre given hpre hgiven hguard
  obtain ⟨N, hN⟩ := hrun rest
  refine ⟨v, N, hv, hshape, fun fuel hfuel => ?_⟩
  refine ⟨reconstruct k a observe (entering k a given rest) (normalize k a observe v),
    hN fuel hfuel, ?_⟩
  exact project_reconstruct k a observe (entering k a given rest) v htup hnd
    (entering_length k a given rest) hshape

/-! ## PW3 Fuel Stability / Monotonicity (`eval_fuel_mono`, `stepsExec_fuel_mono`, `runArm_fuel_mono`) -/

theorem except_bind_congr_ok {ε α β : Type} {m : Except ε α} {k1 k2 : α → Except ε β} {b : β}
    (h : (m >>= k1) = .ok b)
    (hk : ∀ a, k1 a = .ok b → k2 a = .ok b) :
    (m >>= k2) = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact hk a h

theorem except_bind_mono_ok {ε α β : Type} {m1 m2 : Except ε α} {k1 k2 : α → Except ε β} {b : β}
    (h : (m1 >>= k1) = .ok b)
    (hm : ∀ a, m1 = .ok a → m2 = .ok a)
    (hk : ∀ a, k1 a = .ok b → k2 a = .ok b) :
    (m2 >>= k2) = .ok b := by
  cases m1 with
  | error e => simp [bind, Except.bind] at h
  | ok a =>
    have hm2 : m2 = .ok a := hm a rfl
    rw [hm2]
    exact hk a h

theorem ite_congr_ok {α : Type} (c : Bool) {x1 x2 y1 y2 r : α}
    (h : (if c then x1 else y1) = r)
    (hx : x1 = r → x2 = r)
    (hy : y1 = r → y2 = r) :
    (if c then x2 else y2) = r := by
  cases c
  · exact hy h
  · exact hx h

theorem option_congr_ok {α β : Type} (o : Option α) {f1 f2 : α → β} {n1 n2 r : β}
    (h : (match o with | some x => f1 x | none => n1) = r)
    (hs : ∀ x, f1 x = r → f2 x = r)
    (hn : n1 = r → n2 = r) :
    (match o with | some x => f2 x | none => n2) = r := by
  cases o
  · exact hn h
  · exact hs _ h

theorem mapM_mono_ok {ε α β : Type} {f1 f2 : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f1 = .ok ys)
    (hf : ∀ x ∈ xs, ∀ y, f1 x = .ok y → f2 x = .ok y) :
    xs.mapM f2 = .ok ys := by
  induction xs generalizing ys with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.mapM_cons] at h ⊢
    refine except_bind_mono_ok h (fun y hy => hf x List.mem_cons_self y hy) (fun y hrest => ?_)
    refine except_bind_mono_ok hrest
      (fun ys' hys' => ih hys' (fun x' hx' y' hy' => hf x' (List.mem_cons_of_mem _ hx') y' hy'))
      (fun _ hp => hp)

/-- Fueled definitional ACL2 term evaluator over `w.fns` and `env`: consumes 1 unit of fuel
    per term evaluation step and fails with `.error "fuel"` on exhaustion. -/
def eval (w : World) (env : Env) (e : Term) : Nat → Except String Val
  | 0 => .error "fuel"
  | fuel + 1 =>
    match e with
    | .var x =>
      match env.get? x with
      | some v => .ok v
      | none => .error s!"unbound variable {x}"
    | .quote v => .ok v
    | .app f args =>
      if h1 : f = "IF" ∧ args.length = 3 then do
        let cv ← eval w env (args[0]'(by omega)) fuel
        if cv.truthy then eval w env (args[1]'(by omega)) fuel
        else eval w env (args[2]'(by omega)) fuel
      else if h2 : f = "RETURN-LAST" ∧ args.length = 3 then
        eval w env (args[2]'(by omega)) fuel
      else do
        let vs ← args.mapM (fun a => eval w env a fuel)
        match nativeCall f vs with
        | some v => .ok v
        | none => match w.fns f vs with
          | some v => .ok v
          | none => .error s!"no function {f} of arity {vs.length}"
    | .lam formals body actuals => do
      let vs ← actuals.mapM (fun a => eval w env a fuel)
      eval w (formals.zip vs) body fuel

/-- **Fuel Monotonicity for Term Evaluation (`eval_fuel_mono`)**: If `eval w env e fuel = .ok v`
    and `fuel ≤ fuel'`, then `eval w env e fuel' = .ok v`. -/
theorem eval_fuel_mono (w : World) :
    ∀ {fuel fuel' : Nat} {env : Env} {e : Term} {v : Val},
      eval w env e fuel = .ok v → fuel ≤ fuel' → eval w env e fuel' = .ok v := by
  intro fuel
  induction fuel with
  | zero =>
    intro fuel' env e v h _
    simp [eval] at h
  | succ n ih =>
    intro fuel' env e v h hle
    obtain ⟨n', rfl⟩ : ∃ n', fuel' = n' + 1 := ⟨fuel' - 1, by omega⟩
    have hn : n ≤ n' := by omega
    cases e with
    | var x => exact h
    | quote val => exact h
    | app f args =>
      simp only [eval] at h ⊢
      split at h
      · rename_i h1
        simp only [h1]
        refine except_bind_mono_ok h (fun cv hcv => ih hcv hn) (fun cv hbr => ?_)
        exact ite_congr_ok cv.truthy hbr (fun htr => ih htr hn) (fun hfl => ih hfl hn)
      · rename_i h1
        simp only [h1, dite_false]
        split at h
        · rename_i h2
          simp only [h2]
          exact ih h hn
        · rename_i h2
          simp only [h2, dite_false]
          refine except_bind_mono_ok h
            (fun vs hvs => mapM_mono_ok hvs (fun a _ y hy => ih hy hn))
            (fun _ hcall => hcall)
    | lam formals body actuals =>
      simp only [eval] at h ⊢
      refine except_bind_mono_ok h
        (fun vs hvs => mapM_mono_ok hvs (fun a _ y hy => ih hy hn))
        (fun vs hbody => ih hbody hn)

/-- **Fuel Monotonicity for `:repeat` Loop Evaluation (`run_loop_fuel_mono`)**:
    Given fuel monotonicity of `run` below `fuel`, a successful `run.loop` at `fuel`
    succeeds with the identical result at any `fuel' ≥ fuel`. -/
theorem run_loop_fuel_mono (w : World) (f : Frame) (body : List Step) (until_ : Expr) :
    ∀ (fuel : Nat),
      (∀ m < fuel, ∀ (f' : Frame) (st' : St) (steps' : List Step) (m' : Nat) (r' : Res),
        run w f' m st' steps' = .ok r' → m ≤ m' → run w f' m' st' steps' = .ok r') →
      ∀ (k : Nat) (st : St) (fuel' : Nat) (out : St × Nat),
        run.loop w f body until_ fuel k st = .ok out →
        fuel ≤ fuel' →
        run.loop w f body until_ fuel' k st = .ok out := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ k st fuel' out h _
    unfold run.loop at h
    nomatch h
  | succ m ih =>
    intro hrun k st fuel' out h hle
    obtain ⟨m', rfl⟩ : ∃ m', fuel' = m' + 1 := ⟨fuel' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | zero =>
      unfold run.loop at h ⊢
      exact h
    | succ k' =>
      unfold run.loop at h ⊢
      refine except_bind_congr_ok h (fun id h1 => ?_)
      refine except_bind_congr_ok h1 (fun slot h2 => ?_)
      refine except_bind_congr_ok h2 (fun reads h3 => ?_)
      refine except_bind_congr_ok h3 (fun u h4 => ?_)
      refine ite_congr_ok u.truthy h4 (fun htr => htr) (fun hfl => ?_)
      refine except_bind_mono_ok hfl
        (fun r hr => hrun m (Nat.lt_succ_self m) f _ (body ++ [.repeatNext]) m' r hr hm)
        (fun r h5 => ?_)
      cases r with
      | again st' =>
        exact ih (fun m0 hm0 => hrun m0 (Nat.lt_trans hm0 (Nat.lt_succ_self m)))
          k' { st with stobjs := st'.stobjs } m' out h5 hm
      | done _ => exact h5

private theorem option_prod_congr_ok {α β γ ε : Type}
    (o : Option (α × β)) {f1 f2 : α → β → Except ε γ} {e1 e2 : Except ε γ} {b : γ}
    (h : (match o with | some (x, y) => f1 x y | none => e1) = .ok b)
    (hsome : ∀ x y, f1 x y = .ok b → f2 x y = .ok b)
    (hnone : e1 = .ok b → e2 = .ok b) :
    (match o with | some (x, y) => f2 x y | none => e2) = .ok b := by
  cases o with
  | none => exact hnone h
  | some p =>
    rcases p with ⟨x, y⟩
    exact hsome x y h

/-- **Fuel Monotonicity for Step-Language Execution (`stepsExec_fuel_mono` / `run_fuel_mono`)**:
    If `run w f fuel st steps = .ok r` and `fuel ≤ fuel'`, then `run w f fuel' st steps = .ok r`. -/
theorem stepsExec_fuel_mono (w : World) :
    ∀ {fuel fuel' : Nat} {f : Frame} {st : St} {steps : List Step} {r : Res},
       run w f fuel st steps = .ok r →
      fuel ≤ fuel' →
      run w f fuel' st steps = .ok r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    intro fuel' f st steps r h hle
    cases fuel with
    | zero => simp [run] at h
    | succ n =>
      obtain ⟨n', rfl⟩ : ∃ n', fuel' = n' + 1 := ⟨fuel' - 1, by omega⟩
      have hn : n ≤ n' := by omega
      have ihn : ∀ (f' : Frame) (st' : St) (steps' : List Step) (r' : Res),
          run w f' n st' steps' = .ok r' → run w f' n' st' steps' = .ok r' :=
        fun _ _ _ _ hr => ih n (Nat.lt_succ_self n) hr hn
      cases steps with
      | nil => simp [run] at h
      | cons s rest =>
        cases s with
        | let_ v e =>
          simp only [run] at h ⊢
          exact except_bind_congr_ok h (fun x hr => ihn f _ rest r hr)
        | set pairs =>
          simp only [run] at h ⊢
          exact except_bind_congr_ok h (fun x hr => ihn f x rest r hr)
        | next ph =>
          simp only [run] at h ⊢
          refine ite_congr_ok (st.next.isSome || st.nextDone) h (fun h1 => ?_) (fun h2 => ?_)
          · simp [bind, Except.bind] at h1
          · exact except_bind_congr_ok h2 (fun _ hr => ihn f _ rest r hr)
        | do_ vars c acceptGiven accept when_ else_ cases =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun st1 h1 => ?_)
          refine except_bind_congr_ok h1 (fun op h2 => ?_)
          cases when_ with
          | none =>
            dsimp only at h2 ⊢
            rw [except_pure_bind] at h2 ⊢
            refine except_bind_congr_ok h2 (fun opr h3 => ?_)
            refine except_bind_congr_ok h3 (fun st2 h4 => ?_)
            revert h4; cases op.answers <;> intro h4 <;>
              first
              | exact ihn f st2 rest r h4
              | (cases vars with
                 | nil => exact h4
                 | cons v vs =>
                   dsimp only at h4 ⊢
                   refine except_bind_congr_ok h4 (fun code hcode => ?_)
                   refine ite_congr_ok _ hcode (fun hacc => ihn f st2 rest r hacc) (fun hno => ?_)
                   revert hno; generalize List.find? _ _ = o1; intro hno
                   rcases o1 with _ | ⟨_, body1⟩
                   · revert hno; generalize List.find? _ _ = o2; intro hno
                     rcases o2 with _ | ⟨_, body2⟩
                     · exact ite_congr_ok _ hno (fun h1 => ihn f st2 _ r h1) (fun h2 => ihn f st2 _ r h2)
                     · exact ihn f st2 body2 r hno
                   · exact ihn f st2 body1 r hno)
          | some e =>
            dsimp only at h2 ⊢
            refine except_bind_congr_ok h2 (fun wv h3 => ?_)
            rw [except_pure_bind] at h3 ⊢
            refine ite_congr_ok (!wv.truthy) h3 (fun hskip => ?_) (fun hnoskip => ?_)
            · refine except_bind_congr_ok hskip (fun vs h4 => ?_)
              rw [except_pure_bind] at h4 ⊢
              revert h4; cases op.answers <;> intro h4 <;>
                first
                | exact ihn f _ rest r h4
                | (cases vars with
                   | nil => exact h4
                   | cons v vs =>
                     dsimp only at h4 ⊢
                     refine except_bind_congr_ok h4 (fun code hcode => ?_)
                     refine ite_congr_ok _ hcode (fun hacc => ihn f _ rest r hacc) (fun hno => ?_)
                     revert hno; generalize List.find? _ _ = o1; intro hno
                     rcases o1 with _ | ⟨_, body1⟩
                     · revert hno; generalize List.find? _ _ = o2; intro hno
                       rcases o2 with _ | ⟨_, body2⟩
                       · exact ite_congr_ok _ hno (fun h1 => ihn f _ _ r h1) (fun h2 => ihn f _ _ r h2)
                       · exact ihn f _ body2 r hno
                     · exact ihn f _ body1 r hno)
            · refine except_bind_congr_ok hnoskip (fun opr h4 => ?_)
              refine except_bind_congr_ok h4 (fun st2 h5 => ?_)
              revert h5; cases op.answers <;> intro h5 <;>
                first
                | exact ihn f st2 rest r h5
                | (cases vars with
                   | nil => exact h5
                   | cons v vs =>
                     dsimp only at h5 ⊢
                     refine except_bind_congr_ok h5 (fun code hcode => ?_)
                     refine ite_congr_ok _ hcode (fun hacc => ihn f st2 rest r hacc) (fun hno => ?_)
                     revert hno; generalize List.find? _ _ = o1; intro hno
                     rcases o1 with _ | ⟨_, body1⟩
                     · revert hno; generalize List.find? _ _ = o2; intro hno
                       rcases o2 with _ | ⟨_, body2⟩
                       · exact ite_congr_ok _ hno (fun h1 => ihn f st2 _ r h1) (fun h2 => ihn f st2 _ r h2)
                       · exact ihn f st2 body2 r hno
                     · exact ihn f st2 body1 r hno)
        | issue c ok refused =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun st1 h1 => ?_)
          refine except_bind_congr_ok h1 (fun opr h2 => ?_)
          refine except_bind_congr_ok h2 (fun st2 h3 => ?_)
          refine except_bind_congr_ok h3 (fun code h4 => ?_)
          refine ite_congr_ok (code == Val.kw "OK") h4 (fun hok => ihn f st2 ok r hok) (fun hno => ?_)
          exact ite_congr_ok (code == Val.kw "EXHAUSTED") hno
            (fun hex => ihn f st2 _ r hex) (fun href => ihn f st2 _ r href)
        | repeat_ nExpr body until_ =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun st1 h1 => ?_)
          refine except_bind_congr_ok h1 (fun nv h2 => ?_)
          refine except_bind_mono_ok h2
            (fun out hout =>
              run_loop_fuel_mono w f body until_ n
                (fun m hm _ _ _ _ _ hr hm' => ih m (Nat.lt_trans hm (Nat.lt_succ_self n)) hr hm')
                nv.nfix st1 n' out hout hn)
            (fun out h3 => ?_)
          refine except_bind_congr_ok h3 (fun per h4 => ?_)
          exact ihn f _ rest r h4
        | repeatNext => simpa [run] using h
        | wakeRow e =>
          simp only [run] at h ⊢
          refine ite_congr_ok st.woken h (fun hw => ?_) (fun hnw => ?_)
          · simp [bind, Except.bind] at hw
          · refine except_bind_congr_ok hnw (fun _ h0 => ?_)
            refine except_bind_congr_ok h0 (fun v h1 => ?_)
            refine except_bind_congr_ok h1 (fun m h2 => ?_)
            refine except_bind_congr_ok h2 (fun c h3 => ?_)
            refine except_bind_congr_ok h3 (fun rv h4 => ?_)
            exact ihn f _ rest r h4
        | if_ c a b =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun cv h1 => ?_)
          exact ite_congr_ok cv.truthy h1 (fun ha => ihn f st a r ha) (fun hb => ihn f st b r hb)
        | cond clauses =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun cl h1 => ?_)
          rcases cl with _ | ⟨_, body⟩
          · exact h1
          · exact ihn f st body r h1
        | case_ key arms =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun kv h1 => ?_)
          revert h1; generalize List.find? _ _ = o; intro h1
          rcases o with _ | ⟨_, body⟩
          · exact h1
          · exact ihn f st body r h1
        | charge b s d rExpr => simpa [run] using h
        | idle => simpa [run] using h
        | yield => simpa [run] using h
        | wait b s => simpa [run] using h
        | halt => simpa [run] using h
        | park wait arg kind steps' keys => simpa [run] using h
        | stop reason steps' => simpa [run] using h
        | wake => simpa [run] using h
        | nowake => simpa [run] using h
        | goto name =>
          simp only [run] at h ⊢
          refine except_bind_congr_ok h (fun st1 h1 => ?_)
          revert h1; generalize List.find? _ _ = o; intro h1
          rcases o with _ | sub
          · nomatch h1
          · dsimp only at h1 ⊢
            rw [except_pure_bind] at h1 ⊢
            refine except_bind_congr_ok h1 (fun id h2 => ?_)
            refine except_bind_congr_ok h2 (fun slot h3 => ?_)
            refine except_bind_congr_ok h3 (fun reads h4 => ?_)
            refine except_bind_congr_ok h4 (fun d h5 => ?_)
            exact ihn { f with refusal := d.onRefusal } _ d.steps r h5

abbrev run_fuel_mono := @stepsExec_fuel_mono

/-- **Fuel Monotonicity for `runArm` (`runArm_fuel_mono`)**:
    If `runArm w k a observe args fuel = .ok out` and `fuel ≤ fuel'`,
    then `runArm w k a observe args fuel' = .ok out`. -/
theorem runArm_fuel_mono (w : World) (k : Kind) (a : Arm) (observe : Bool) (args : List Val)
    {fuel fuel' : Nat} {out : Val}
    (h : runArm w k a observe args fuel = .ok out) (hle : fuel ≤ fuel') :
    runArm w k a observe args fuel' = .ok out := by
  unfold runArm at h ⊢
  refine ite_congr_ok (!k.childForm) h (fun h1 => by nomatch h1) (fun h1 => ?_)
  rw [except_pure_bind] at h1 ⊢
  refine ite_congr_ok _ h1 (fun h2 => by nomatch h2) (fun h2 => ?_)
  rw [except_pure_bind] at h2 ⊢
  refine except_bind_congr_ok h2 (fun reads h3 => ?_)
  refine except_bind_congr_ok h3 (fun d h4 => ?_)
  exact except_bind_mono_ok h4
    (fun r hr => stepsExec_fuel_mono w hr hle)
    (fun _ hr => hr)

/-- By `runArm_fuel_mono`, establishing `runArm` agreement at a single concrete fuel `N`
    discharges the universal `∀ fuel, N ≤ fuel → ...` obligation in `ArmCorrect`. -/
theorem armCorrect_of_runArm_at (w : World) (guard : String → List Val → Option Val)
    (k : Kind) (a : Arm) (observe : Bool) (N : Nat)
    (hwf : ArmWF k a observe = true)
    (h : ∀ (pre given : List Val),
      pre.length = nPre observe → given.length = (takes k a).length →
      Guarded guard a.fn (pre ++ given) →
      ∃ v, w.fns a.fn (pre ++ given) = some v ∧ NarrowShape k a observe v ∧
        ∀ rest : String → Val,
          runArm w k a observe (widen k a pre given rest) N =
            .ok (reconstruct k a observe (entering k a given rest) (normalize k a observe v))) :
    ArmCorrect w guard k a observe := by
  refine ⟨hwf, fun pre given hpre hgiven hguard => ?_⟩
  obtain ⟨v, hv, hshape, hrun⟩ := h pre given hpre hgiven hguard
  exact ⟨v, hv, hshape, fun rest => ⟨N, fun fuel hfuel =>
    runArm_fuel_mono w k a observe (widen k a pre given rest) (hrun rest) hfuel⟩⟩

/-! ## Concrete `ArmCorrect` Proofs for Representative `echo`, `listener`, and `scribe` Arms -/

theorem list_length_eq_2 {α : Type} {xs : List α} (h : xs.length = 2) :
    ∃ x0 x1, xs = [x0, x1] := by
  match xs, h with
  | [x0, x1], _ => exact ⟨x0, x1, rfl⟩

theorem list_length_eq_3 {α : Type} {xs : List α} (h : xs.length = 3) :
    ∃ x0 x1 x2, xs = [x0, x1, x2] := by
  match xs, h with
  | [x0, x1, x2], _ => exact ⟨x0, x1, x2, rfl⟩

theorem list_length_eq_5 {α : Type} {xs : List α} (h : xs.length = 5) :
    ∃ x0 x1 x2 x3 x4, xs = [x0, x1, x2, x3, x4] := by
  match xs, h with
  | [x0, x1, x2, x3, x4], _ => exact ⟨x0, x1, x2, x3, x4, rfl⟩

theorem list_length_eq_10 {α : Type} {xs : List α} (h : xs.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] := by
  match xs, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9], _ =>
    exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩

private theorem pmap_mapM_eq {ε α β : Type} {P : α → Prop} (xs : List α) (h : ∀ x ∈ xs, P x)
    (g : α → Except ε β) :
    (xs.pmap (fun a ha => (⟨a, ha⟩ : { a // P a })) h).mapM (fun ⟨a, _⟩ => g a) = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.pmap, List.mapM_cons, ih]

private theorem attach_mapM_eq {ε α β : Type} (xs : List α) (g : α → Except ε β) :
    xs.attach.mapM (fun ⟨a, _⟩ => g a) = xs.mapM g := by
  unfold List.attach List.attachWith
  exact pmap_mapM_eq xs _ g

private theorem termEval_app_other (fns : Fns) (env : Env) (f : String) (args : List Term)
    (h1 : ¬(f = "IF" ∧ args.length = 3)) (h2 : ¬(f = "RETURN-LAST" ∧ args.length = 3)) :
    Term.eval fns env (.app f args) = (do
      let vs ← args.mapM (fun a => Term.eval fns env a)
      match nativeCall f vs with
      | some v => .ok v
      | none => match fns f vs with
        | some v => .ok v
        | none => .error s!"no function {f} of arity {vs.length}") := by
  conv => lhs; unfold Term.eval
  split
  · nomatch ‹Term.app f args = Term.var _›
  · nomatch ‹Term.app f args = Term.quote _›
  · rename_i c a b heq; injection heq with hf ha; subst hf ha; exact False.elim (h1 ⟨rfl, rfl⟩)
  · rename_i x0 x1 c heq; injection heq with hf ha; subst hf ha; exact False.elim (h2 ⟨rfl, rfl⟩)
  · rename_i f' args' _ _ heq; injection heq with hf ha; subst hf ha; rw [attach_mapM_eq]; rfl
  · nomatch ‹Term.app f args = Term.lam _ _ _›

/-- **Soundness of Fueled Term Evaluation (`eval_sound`)**:
    Every value produced by `Pathway.eval` equals the value produced by `ACL2.Term.eval`. -/
theorem eval_sound (w : World) :
    ∀ {fuel : Nat} {env : Env} {e : Term} {v : Val},
      eval w env e fuel = .ok v → Term.eval w.fns env e = .ok v := by
  intro fuel
  induction fuel with
  | zero =>
    intro env e v h
    simp [eval] at h
  | succ n ih =>
    intro env e v h
    cases e with
    | var x =>
      simp only [eval] at h
      unfold Term.eval
      exact h
    | quote val =>
      simp only [eval] at h
      unfold Term.eval
      exact h
    | app f args =>
      simp only [eval] at h
      split at h
      · rename_i h1
        rcases h1 with ⟨rfl, hlen⟩
        obtain ⟨c, a, b, rfl⟩ := list_length_eq_3 hlen
        unfold Term.eval
        dsimp only at h ⊢
        exact except_bind_mono_ok h (fun cv hcv => ih hcv)
          (fun cv hbr => ite_congr_ok cv.truthy hbr (fun htr => ih htr) (fun hfl => ih hfl))
      · rename_i h1
        split at h
        · rename_i h2
          rcases h2 with ⟨rfl, hlen⟩
          obtain ⟨x0, x1, c, rfl⟩ := list_length_eq_3 hlen
          unfold Term.eval
          dsimp only at h ⊢
          exact ih h
        · rename_i h2
          rw [termEval_app_other w.fns env f args h1 h2]
          exact except_bind_mono_ok h
            (fun vs hvs => mapM_mono_ok hvs (fun a _ y hy => ih hy))
            (fun _ hcall => hcall)
    | lam formals body actuals =>
      simp only [eval] at h
      conv => lhs; unfold Term.eval
      rw [attach_mapM_eq]
      exact except_bind_mono_ok h
        (fun vs hvs => mapM_mono_ok hvs (fun a _ y hy => ih hy))
        (fun vs hbody => ih hbody)

private theorem eval_complete_aux (w : World) :
    ∀ (n : Nat) (e : Term) {env : Env} {v : Val},
      sizeOf e ≤ n → Term.eval w.fns env e = .ok v → eval w env e n = .ok v := by
  intro n
  induction n with
  | zero =>
    intro e _ _ hsz _
    cases e <;> simp at hsz
  | succ k ih =>
    intro e env v hsz h
    cases e with
    | var x =>
      simp only [eval]; unfold Term.eval at h; exact h
    | quote val =>
      simp only [eval]; unfold Term.eval at h; exact h
    | app f args =>
      simp only [eval]
      split
      · rename_i h1
        rcases h1 with ⟨rfl, hlen⟩
        obtain ⟨c, a, b, rfl⟩ := list_length_eq_3 hlen
        unfold Term.eval at h
        dsimp only at h ⊢
        have hc : sizeOf c ≤ k := by simp at hsz; omega
        have ha : sizeOf a ≤ k := by simp at hsz; omega
        have hb : sizeOf b ≤ k := by simp at hsz; omega
        exact except_bind_mono_ok h
          (fun cv hcv => ih c hc hcv)
          (fun cv hbr => ite_congr_ok cv.truthy hbr
            (fun htr => ih a ha htr)
            (fun hfl => ih b hb hfl))
      · rename_i h1
        split
        · rename_i h2
          rcases h2 with ⟨rfl, hlen⟩
          obtain ⟨x0, x1, c, rfl⟩ := list_length_eq_3 hlen
          unfold Term.eval at h
          dsimp only at h ⊢
          have hc : sizeOf c ≤ k := by simp at hsz; omega
          exact ih c hc h
        · rename_i h2
          rw [termEval_app_other w.fns env f args h1 h2] at h
          exact except_bind_mono_ok h
            (fun vs hvs => mapM_mono_ok hvs (fun a hmem y hy => by
              have ha1 : sizeOf a < sizeOf args := List.sizeOf_lt_of_mem hmem
              have ha2 : sizeOf a ≤ k := by simp at hsz; omega
              exact ih a ha2 hy))
            (fun _ hcall => hcall)
    | lam formals body actuals =>
      simp only [eval]
      unfold Term.eval at h
      rw [attach_mapM_eq] at h
      have hbody_sz : sizeOf body ≤ k := by simp at hsz; omega
      exact except_bind_mono_ok h
        (fun vs hvs => mapM_mono_ok hvs (fun a hmem y hy => by
          have ha1 : sizeOf a < sizeOf actuals := List.sizeOf_lt_of_mem hmem
          have ha2 : sizeOf a ≤ k := by simp at hsz; omega
          exact ih a ha2 hy))
        (fun vs hbody => ih body hbody_sz hbody)

/-- **Fuel Adequacy / Completeness of Term Evaluation (`eval_complete`)**:
    Whenever `ACL2.Term.eval w.fns env e = .ok v`, `Pathway.eval w env e (sizeOf e) = .ok v`. -/
theorem eval_complete (w : World) (e : Term) {env : Env} {v : Val}
    (h : Term.eval w.fns env e = .ok v) : eval w env e (sizeOf e) = .ok v :=
  eval_complete_aux w (sizeOf e) e (Nat.le_refl _) h

/-- **Equivalence Between Fueled `Pathway.eval` and `ACL2.Term.eval` (`eval_eq_termEval_iff`)**:
    `Pathway.eval` succeeds with `v` at some fuel iff `ACL2.Term.eval` evaluates to `v`. -/
theorem eval_eq_termEval_iff (w : World) (env : Env) (e : Term) (v : Val) :
    (∃ fuel, eval w env e fuel = .ok v) ↔ Term.eval w.fns env e = .ok v :=
  ⟨fun ⟨_, hf⟩ => eval_sound w hf, fun ht => ⟨sizeOf e, eval_complete w e ht⟩⟩

/-- Representative `echo` machine kind (`FN2-ECHO`) with `:FREE` run arm, `:COMMAND` mutating run arm,
    and `:CLOSE-RESULT` observation handler. -/
def pw3EchoKind : Kind :=
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
    arms := [
      { tag := ":FREE"
        sig := some ⟨["FN2-ECHO", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-ECHO-RUN-FREE-CHILDREN" },
      { tag := ":COMMAND"
        sig := some ⟨["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "OFF", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":REPLY"],
          Val.ofList [.sym ":CHARGE", .sym ":BYTES", .int 64, .sym ":STEPS", .int 2, .sym ":RUNNABLE", Val.t]
        ]
        fn := "FN2-ECHO-RUN-COMMAND-CHILDREN" }
    ]
    observes := [
      { tag := ":CLOSE-RESULT"
        sig := some ⟨["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-ECHO", "FN2-MACHINES", "FN2-CONTROL"], 1⟩
        decl := Val.ofList [
          Val.ofList [.sym ":NEXT", .sym ":DRAINING"],
          Val.ofList [.sym ":WAKE"]
        ]
        fn := "FN2-ECHO-ON-CLOSE-RESULT-CHILDREN" }
    ] }

def pw3EchoFreeArm : Arm := pw3EchoKind.arms[0]!
def pw3EchoCommandArm : Arm := pw3EchoKind.arms[1]!
def pw3EchoCloseResultArm : Arm := pw3EchoKind.observes[0]!

/-- Representative `listener` machine kind (`FN2-LISTENER`) in child form with `:ACCEPTING` run arm
    and `:CLOSE-RESULT` observation handler. -/
def pw3ListenerKind : Kind :=
  { name := "FN2-LISTENER"
    childForm := true
    tuple := ["FN2-LISTENER", "FN2-MACHINES", "FN2-OPS", "FN2-CONTROL"]
    states := [":ACCEPTING", ":ADMITTING", ":CLOSING"]
    phases := [(":ACCEPTING", 0), (":ADMITTING", 1), (":CLOSING", 2)]
    columns := [("PHASE", .enum 3), ("EVENT-READY", .uw 1), ("WAIT-REASON", .enum 26)]
    table := ["PHASE", "EVENT-READY"]
    stops := []
    links := []
    subarms := []
    arms := [
      { tag := ":ACCEPTING"
        sig := some ⟨["FN2-LISTENER", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-LISTENER-RUN-ACCEPTING-CHILDREN" }
    ]
    observes := [
      { tag := ":CLOSE-RESULT"
        sig := some ⟨["FN2-LISTENER", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-LISTENER", "FN2-MACHINES", "FN2-CONTROL"], 1⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "EVENT-READY", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":ACCEPTING"],
          Val.ofList [.sym ":WAKE"]
        ]
        fn := "FN2-LISTENER-ON-CLOSE-RESULT-CHILDREN" }
    ] }

def pw3ListenerAcceptingArm : Arm := pw3ListenerKind.arms[0]!
def pw3ListenerCloseResultArm : Arm := pw3ListenerKind.observes[0]!

/-- Representative `scribe` machine kind (`FN2-SCRIBE`) with `:FREE` run arm and `STOP` sub-arm. -/
def pw3ScribeKind : Kind :=
  { name := "FN2-SCRIBE"
    childForm := true
    tuple := ["FN2-SCRIBE", "FN2-MACHINES", "FN2-POOL", "FN2-OPS", "FN2-CONTROL"]
    states := [":FREE", ":RESERVE", ":FILL", ":PATCH", ":WRITE", ":STOPPED"]
    phases := [(":FREE", 0), (":RESERVE", 1), (":FILL", 2), (":PATCH", 3),
               (":WRITE", 4), (":STOPPED", 5)]
    columns := [("PHASE", .enum 6), ("STOPPED", .uw 1), ("EVENT-READY", .uw 1), ("WAIT-REASON", .enum 26)]
    table := ["PHASE", "STOPPED", "EVENT-READY"]
    stops := []
    links := []
    subarms := [
      { tag := "STOP"
        sig := some ⟨["FN2-SCRIBE", "FN2-MACHINES", "FN2-CONTROL"],
                     ["FN2-SCRIBE", "FN2-MACHINES", "FN2-CONTROL"], 4⟩
        decl := Val.ofList [
          Val.ofList [.sym ":SET", Val.ofList [.sym "STOPPED", .int 1], Val.ofList [.sym "EVENT-READY", .int 0]],
          Val.ofList [.sym ":NEXT", .sym ":STOPPED"],
          Val.ofList [.sym ":CHARGE", .sym ":STEPS", .int 4]
        ]
        fn := "FN2-SCRIBE-SUB-STOP-CHILDREN" }
    ]
    arms := [
      { tag := ":FREE"
        sig := some ⟨["FN2-SCRIBE", "FN2-MACHINES"], [], 4⟩
        decl := Val.ofList [Val.ofList [.sym ":IDLE"]]
        fn := "FN2-SCRIBE-RUN-FREE-CHILDREN" }
    ]
    observes := [] }

def pw3ScribeFreeArm : Arm := pw3ScribeKind.arms[0]!
def pw3ScribeStopSubarm : Arm := pw3ScribeKind.subarms[0]!

def echoCommandSpec (slot echo machines ctrl : Val) : Val :=
  if natLt slot (.int 4) then
    let echo1 := Native.updateNth (.int 2) (Native.updateNth slot (.int 0) (Native.nth (.int 2) echo)) echo
    let echo2 := Native.updateNth (.int 0) (Native.updateNth slot (.int 2) (Native.nth (.int 0) echo1)) echo1
    Val.ofList [.int 64, .int 2, .int 0, Val.t, echo2, machines, ctrl]
  else
    Val.ofList [.int 64, .int 2, .int 0, Val.t, echo, machines, Val.cons (.int 13) ctrl]

def echoCloseResultSpec (id slot echo machines ctrl : Val) : Val :=
  if natLt slot (.int 4) then
    let echo1 := Native.updateNth (.int 0) (Native.updateNth slot (.int 4) (Native.nth (.int 0) echo)) echo
    Val.ofList [id, echo1, machines, ctrl]
  else
    Val.ofList [id, echo, machines, Val.cons (.int 13) ctrl]

def listenerCloseResultSpec (id slot listener machines ctrl : Val) : Val :=
  if natLt slot (.int 4) then
    let l1 := Native.updateNth (.int 1) (Native.updateNth slot (.int 0) (Native.nth (.int 1) listener)) listener
    let l2 := Native.updateNth (.int 0) (Native.updateNth slot (.int 0) (Native.nth (.int 0) l1)) l1
    Val.ofList [id, l2, machines, ctrl]
  else
    Val.ofList [id, listener, machines, Val.cons (.int 13) ctrl]

def scribeStopSpec (slot scribe machines ctrl : Val) : Val :=
  if natLt slot (.int 4) then
    let s1 := Native.updateNth (.int 1) (Native.updateNth slot (.int 1) (Native.nth (.int 1) scribe)) scribe
    let s2 := Native.updateNth (.int 2) (Native.updateNth slot (.int 0) (Native.nth (.int 2) s1)) s1
    let s3 := Native.updateNth (.int 0) (Native.updateNth slot (.int 5) (Native.nth (.int 0) s2)) s2
    Val.ofList [.int 0, .int 4, .int 0, Val.nil, s3, machines, ctrl]
  else
    Val.ofList [.int 0, .int 4, .int 0, Val.nil, scribe, machines, Val.cons (.int 13) ctrl]

/-- Generated child-form specifications (`spec` dispatch) for the representative `echo`,
    `listener`, and `scribe` arms and their table accessors/updaters. -/
def pw3SpecFns : Fns
  | "FN2-ECHO-ROWS", [_] => some (.int 4)
  | "FN2-LISTENER-ROWS", [_] => some (.int 4)
  | "FN2-SCRIBE-ROWS", [_] => some (.int 4)
  | "FN2-MACHINES-ROWS", [_] => some (.int 4)
  | "FN2-ECHO-PHASE", [s, t] => some (Native.nth s (Native.nth (.int 0) t))
  | "FN2-ECHO-STOPPED", [s, t] => some (Native.nth s (Native.nth (.int 1) t))
  | "FN2-ECHO-OFF", [s, t] => some (Native.nth s (Native.nth (.int 2) t))
  | "FN2-ECHO-SET-PHASE", [s, v, t] =>
    some (Native.updateNth (.int 0) (Native.updateNth s v (Native.nth (.int 0) t)) t)
  | "FN2-ECHO-SET-STOPPED", [s, v, t] =>
    some (Native.updateNth (.int 1) (Native.updateNth s v (Native.nth (.int 1) t)) t)
  | "FN2-ECHO-SET-OFF", [s, v, t] =>
    some (Native.updateNth (.int 2) (Native.updateNth s v (Native.nth (.int 2) t)) t)
  | "FN2-LISTENER-PHASE", [s, t] => some (Native.nth s (Native.nth (.int 0) t))
  | "FN2-LISTENER-EVENT-READY", [s, t] => some (Native.nth s (Native.nth (.int 1) t))
  | "FN2-LISTENER-SET-PHASE", [s, v, t] =>
    some (Native.updateNth (.int 0) (Native.updateNth s v (Native.nth (.int 0) t)) t)
  | "FN2-LISTENER-SET-EVENT-READY", [s, v, t] =>
    some (Native.updateNth (.int 1) (Native.updateNth s v (Native.nth (.int 1) t)) t)
  | "FN2-SCRIBE-PHASE", [s, t] => some (Native.nth s (Native.nth (.int 0) t))
  | "FN2-SCRIBE-STOPPED", [s, t] => some (Native.nth s (Native.nth (.int 1) t))
  | "FN2-SCRIBE-EVENT-READY", [s, t] => some (Native.nth s (Native.nth (.int 2) t))
  | "FN2-SCRIBE-SET-PHASE", [s, v, t] =>
    some (Native.updateNth (.int 0) (Native.updateNth s v (Native.nth (.int 0) t)) t)
  | "FN2-SCRIBE-SET-STOPPED", [s, v, t] =>
    some (Native.updateNth (.int 1) (Native.updateNth s v (Native.nth (.int 1) t)) t)
  | "FN2-SCRIBE-SET-EVENT-READY", [s, v, t] =>
    some (Native.updateNth (.int 2) (Native.updateNth s v (Native.nth (.int 2) t)) t)
  | "FN2-MACHINES-WAIT-REASON", [id, d] => some (Native.nth id (Native.nth (.int 0) d))
  | "FN2-MACHINES-SET-WAIT-REASON", [id, v, d] =>
    some (Native.updateNth (.int 0) (Native.updateNth id v (Native.nth (.int 0) d)) d)
  | "FN2-CONTROL-RECORD-STOP", [r, c] => some (Val.cons r c)
  | "FN2-ECHO-RUN-FREE-CHILDREN", [_, _, _, _, _, _, _] =>
    some (Val.ofList [.int 0, .int 1, .int 0, Val.nil])
  | "FN2-ECHO-RUN-COMMAND-CHILDREN", [_, slot, _, _, _, echo, machines, ctrl] =>
    some (echoCommandSpec slot echo machines ctrl)
  | "FN2-ECHO-ON-CLOSE-RESULT-CHILDREN", [id, slot, _, _, _, _, _, _, _, _, echo, machines, ctrl] =>
    some (echoCloseResultSpec id slot echo machines ctrl)
  | "FN2-LISTENER-RUN-ACCEPTING-CHILDREN", [_, _, _, _, _, _, _] =>
    some (Val.ofList [.int 0, .int 1, .int 0, Val.nil])
  | "FN2-LISTENER-ON-CLOSE-RESULT-CHILDREN", [id, slot, _, _, _, _, _, _, _, _, listener, machines, ctrl] =>
    some (listenerCloseResultSpec id slot listener machines ctrl)
  | "FN2-SCRIBE-RUN-FREE-CHILDREN", [_, _, _, _, _, _, _] =>
    some (Val.ofList [.int 0, .int 1, .int 0, Val.nil])
  | "FN2-SCRIBE-SUB-STOP-CHILDREN", [_, slot, _, _, _, scribe, machines, ctrl] =>
    some (scribeStopSpec slot scribe machines ctrl)
  | _, _ => none

def pw3World : World :=
  { kinds := [pw3EchoKind, pw3ListenerKind, pw3ScribeKind]
    ops := []
    waits := []
    consts := [("*FN2-WORK-EMPTY*", .int 1),
               ("*FN2-WORK-MAILBOX*", .int 2),
               ("*FN2-STOP-REASON-MACHINE-WRITE*", .int 13),
               ("*FN2-NONE*", .int 4294967295)]
    fns := pw3SpecFns }

/-- Check that `slot` is active slot `0` (in bounds `< 4`). -/
def isSlotZero : Val → Bool
  | .int 0 => true
  | _      => false

private theorem isSlotZero_eq_true {v : Val} (h : (Val.ofBool (isSlotZero v)).truthy = true) :
    v = .int 0 := by
  cases v with
  | int i =>
    cases i with
    | ofNat n =>
      cases n with
      | zero => rfl
      | succ _ => contradiction
    | negSucc _ => contradiction
  | _ => contradiction

/-- Guard table requiring active row slot `0` (`< 4`) for mutating arms. -/
def pw3Guard (fn : String) (args : List Val) : Option Val :=
  match fn, args with
  | "FN2-ECHO-RUN-COMMAND-CHILDREN", [_, slot, _, _, _, _, _, _] =>
    some (Val.ofBool (isSlotZero slot))
  | "FN2-ECHO-ON-CLOSE-RESULT-CHILDREN", [_, slot, _, _, _, _, _, _, _, _, _, _, _] =>
    some (Val.ofBool (isSlotZero slot))
  | "FN2-LISTENER-ON-CLOSE-RESULT-CHILDREN", [_, slot, _, _, _, _, _, _, _, _, _, _, _] =>
    some (Val.ofBool (isSlotZero slot))
  | "FN2-SCRIBE-SUB-STOP-CHILDREN", [_, slot, _, _, _, _, _, _] =>
    some (Val.ofBool (isSlotZero slot))
  | _, _ => some Val.t

@[simp] private theorem term_eval_quote (fns : Fns) (env : Env) (v : Val) :
    Term.eval fns env (.quote v) = .ok v := by
  unfold Term.eval; rfl

@[simp] private theorem ev_int (w : World) (k : Kind) (st : St) (i : Int) :
    ev w k st (.int i) = .ok (.int i) := by
  unfold ev
  have h : readExpr w k (.int i) = .ok (.quote (.int i)) := rfl
  rw [h, except_ok_bind, term_eval_quote]

@[simp] private theorem ev_t (w : World) (k : Kind) (st : St) :
    ev w k st (.sym "T") = .ok Val.t := by
  unfold ev
  have h : readExpr w k (.sym "T") = .ok (.quote Val.t) := rfl
  rw [h, except_ok_bind, term_eval_quote]

@[simp] private theorem readNext_echo_reply :
    readNext pw3World pw3EchoKind (.sym ":REPLY") = .ok (.quote (.int 2)) := rfl

@[simp] private theorem readNext_echo_draining :
    readNext pw3World pw3EchoKind (.sym ":DRAINING") = .ok (.quote (.int 4)) := rfl

@[simp] private theorem readNext_listener_accepting :
    readNext pw3World pw3ListenerKind (.sym ":ACCEPTING") = .ok (.quote (.int 0)) := rfl

@[simp] private theorem readNext_scribe_stopped :
    readNext pw3World pw3ScribeKind (.sym ":STOPPED") = .ok (.quote (.int 5)) := rfl

private theorem pw3EchoCommandArm_read :
    pw3EchoCommandArm.read =
      .ok { from_ := [], onRefusal := [],
            steps := [.set [("OFF", .int 0)], .next (.sym ":REPLY"),
                      .charge (some (.int 64)) (some (.int 2)) none (some (.sym "T"))] } := rfl

private theorem pw3EchoCloseResultArm_read :
    pw3EchoCloseResultArm.read =
      .ok { from_ := [], onRefusal := [],
            steps := [.next (.sym ":DRAINING"), .wake] } := rfl

private theorem pw3ListenerCloseResultArm_read :
    pw3ListenerCloseResultArm.read =
      .ok { from_ := [], onRefusal := [],
            steps := [.set [("EVENT-READY", .int 0)], .next (.sym ":ACCEPTING"), .wake] } := rfl

private theorem pw3ScribeStopSubarm_read :
    pw3ScribeStopSubarm.read =
      .ok { from_ := [], onRefusal := [],
            steps := [.set [("STOPPED", .int 1), ("EVENT-READY", .int 0)],
                      .next (.sym ":STOPPED"),
                      .charge none (some (.int 4)) none none] } := rfl

private theorem except_bind_assoc {ε α β γ : Type} (m : Except ε α)
    (f : α → Except ε β) (g : β → Except ε γ) :
    (m >>= f) >>= g = m >>= (fun x => f x >>= g) := by
  cases m <;> rfl

private theorem flush_echo_command (base stobjs vars : Env) :
    let f : Frame := { kind := pw3EchoKind, observe := false, refusal := [], base := base }
    let st : St := { stobjs := stobjs, vars := vars, pending := [("OFF", .int 0)], next := some (.sym ":REPLY") }
    flush pw3World f st = (do
      let st' ← put pw3World f st [("OFF", .int 0), ("PHASE", .int 2)]
      pure { st' with pending := [], next := none, nextDone := true }) := by
  dsimp only [flush]
  simp only [List.mapM_cons, List.mapM_nil, ev_int, readNext_echo_reply,
    term_eval_quote, except_ok_bind, except_pure_bind]
  rfl

private theorem run_echo_command (base stobjs vars : Env) :
    let f : Frame := { kind := pw3EchoKind, observe := false, refusal := [], base := base }
    run pw3World f 3 { stobjs := stobjs, vars := vars }
      [.set [("OFF", .int 0)], .next (.sym ":REPLY"),
       .charge (some (.int 64)) (some (.int 2)) none (some (.sym "T"))] =
    (do
      let f : Frame := { kind := pw3EchoKind, observe := false, refusal := [], base := base }
      let st1 : St := { stobjs := stobjs, vars := vars, pending := [("OFF", .int 0)], next := some (.sym ":REPLY") }
      let st' ← put pw3World f st1 [("OFF", .int 0), ("PHASE", .int 2)]
      let st3 : St := { st' with pending := [], next := none, nextDone := true }
      chargeResult f st3 (.int 64) (.int 2) (.int 0) Val.t) := by
  change (do
    let f : Frame := { kind := pw3EchoKind, observe := false, refusal := [], base := base }
    let st1 : St := { stobjs := stobjs, vars := vars, pending := [("OFF", .int 0)], next := some (.sym ":REPLY") }
    let st3 ← flush pw3World f st1
    let b ← evOpt pw3World pw3EchoKind st3 (some (.int 64)) (.int 0)
    let s ← evOpt pw3World pw3EchoKind st3 (some (.int 2)) (.int 0)
    let d ← evOpt pw3World pw3EchoKind st3 none (.int 0)
    let r ← evOpt pw3World pw3EchoKind st3 (some (.sym "T")) Val.nil
    chargeResult f st3 b s d r) = _
  simp only [flush_echo_command, evOpt, ev_int, ev_t, except_ok_bind, except_bind_assoc, except_pure_bind]

private theorem flush_echo_closeResult (base stobjs vars : Env) :
    let f : Frame := { kind := pw3EchoKind, observe := true, refusal := [], base := base }
    let st : St := { stobjs := stobjs, vars := vars, next := some (.sym ":DRAINING") }
    flush pw3World f st = (do
      let st' ← put pw3World f st [("PHASE", .int 4)]
      pure { st' with pending := [], next := none, nextDone := true }) := by
  dsimp only [flush]
  simp only [List.mapM_nil, readNext_echo_draining,
    term_eval_quote, except_ok_bind, except_pure_bind]
  rfl

private theorem run_echo_closeResult (base stobjs vars : Env) :
    let f : Frame := { kind := pw3EchoKind, observe := true, refusal := [], base := base }
    run pw3World f 2 { stobjs := stobjs, vars := vars }
      [.next (.sym ":DRAINING"), .wake] =
    (do
      let f : Frame := { kind := pw3EchoKind, observe := true, refusal := [], base := base }
      let st1 : St := { stobjs := stobjs, vars := vars, next := some (.sym ":DRAINING") }
      let st' ← put pw3World f st1 [("PHASE", .int 4)]
      let st3 : St := { st' with pending := [], next := none, nextDone := true }
      wakeResult f st3 (← var st3 "ID")) := by
  change (do
    let f : Frame := { kind := pw3EchoKind, observe := true, refusal := [], base := base }
    let st1 : St := { stobjs := stobjs, vars := vars, next := some (.sym ":DRAINING") }
    let st3 ← flush pw3World f st1
    wakeResult f st3 (← var st3 "ID")) = _
  simp only [flush_echo_closeResult, except_bind_assoc, except_pure_bind]

private theorem flush_listener_closeResult (base stobjs vars : Env) :
    let f : Frame := { kind := pw3ListenerKind, observe := true, refusal := [], base := base }
    let st : St := { stobjs := stobjs, vars := vars, pending := [("EVENT-READY", .int 0)], next := some (.sym ":ACCEPTING") }
    flush pw3World f st = (do
      let st' ← put pw3World f st [("EVENT-READY", .int 0), ("PHASE", .int 0)]
      pure { st' with pending := [], next := none, nextDone := true }) := by
  dsimp only [flush]
  simp only [List.mapM_cons, List.mapM_nil, ev_int, readNext_listener_accepting,
    term_eval_quote, except_ok_bind, except_pure_bind]
  rfl

private theorem run_listener_closeResult (base stobjs vars : Env) :
    let f : Frame := { kind := pw3ListenerKind, observe := true, refusal := [], base := base }
    run pw3World f 3 { stobjs := stobjs, vars := vars }
      [.set [("EVENT-READY", .int 0)], .next (.sym ":ACCEPTING"), .wake] =
    (do
      let f : Frame := { kind := pw3ListenerKind, observe := true, refusal := [], base := base }
      let st1 : St := { stobjs := stobjs, vars := vars, pending := [("EVENT-READY", .int 0)], next := some (.sym ":ACCEPTING") }
      let st' ← put pw3World f st1 [("EVENT-READY", .int 0), ("PHASE", .int 0)]
      let st3 : St := { st' with pending := [], next := none, nextDone := true }
      wakeResult f st3 (← var st3 "ID")) := by
  change (do
    let f : Frame := { kind := pw3ListenerKind, observe := true, refusal := [], base := base }
    let st1 : St := { stobjs := stobjs, vars := vars, pending := [("EVENT-READY", .int 0)], next := some (.sym ":ACCEPTING") }
    let st3 ← flush pw3World f st1
    wakeResult f st3 (← var st3 "ID")) = _
  simp only [flush_listener_closeResult, except_bind_assoc, except_pure_bind]

private theorem flush_scribe_stop (base stobjs vars : Env) :
    let f : Frame := { kind := pw3ScribeKind, observe := false, refusal := [], base := base }
    let st : St := { stobjs := stobjs, vars := vars,
                     pending := [("STOPPED", .int 1), ("EVENT-READY", .int 0)],
                     next := some (.sym ":STOPPED") }
    flush pw3World f st = (do
      let st' ← put pw3World f st [("STOPPED", .int 1), ("EVENT-READY", .int 0), ("PHASE", .int 5)]
      pure { st' with pending := [], next := none, nextDone := true }) := by
  dsimp only [flush]
  simp only [List.mapM_cons, List.mapM_nil, ev_int, readNext_scribe_stopped,
    term_eval_quote, except_ok_bind, except_pure_bind]
  rfl

private theorem run_scribe_stop (base stobjs vars : Env) :
    let f : Frame := { kind := pw3ScribeKind, observe := false, refusal := [], base := base }
    run pw3World f 3 { stobjs := stobjs, vars := vars }
      [.set [("STOPPED", .int 1), ("EVENT-READY", .int 0)],
       .next (.sym ":STOPPED"),
       .charge none (some (.int 4)) none none] =
    (do
      let f : Frame := { kind := pw3ScribeKind, observe := false, refusal := [], base := base }
      let st1 : St := { stobjs := stobjs, vars := vars,
                        pending := [("STOPPED", .int 1), ("EVENT-READY", .int 0)],
                        next := some (.sym ":STOPPED") }
      let st' ← put pw3World f st1 [("STOPPED", .int 1), ("EVENT-READY", .int 0), ("PHASE", .int 5)]
      let st3 : St := { st' with pending := [], next := none, nextDone := true }
      chargeResult f st3 (.int 0) (.int 4) (.int 0) Val.nil) := by
  change (do
    let f : Frame := { kind := pw3ScribeKind, observe := false, refusal := [], base := base }
    let st1 : St := { stobjs := stobjs, vars := vars,
                      pending := [("STOPPED", .int 1), ("EVENT-READY", .int 0)],
                      next := some (.sym ":STOPPED") }
    let st3 ← flush pw3World f st1
    let b ← evOpt pw3World pw3ScribeKind st3 none (.int 0)
    let s ← evOpt pw3World pw3ScribeKind st3 (some (.int 4)) (.int 0)
    let d ← evOpt pw3World pw3ScribeKind st3 none (.int 0)
    let r ← evOpt pw3World pw3ScribeKind st3 none Val.nil
    chargeResult f st3 b s d r) = _
  simp only [flush_scribe_stop, evOpt, ev_int, except_ok_bind, except_bind_assoc, except_pure_bind]

/-- **Concrete `ArmCorrect` Theorem 1 (`echo_free_armCorrect`)**:
    `pw3EchoFreeArm` (`:FREE` arm of `FN2-ECHO`, `observe = false`) satisfies `ArmCorrect`
    for all inputs and all untaken children `rest`. -/
theorem echo_free_armCorrect :
    ArmCorrect pw3World pw3Guard pw3EchoKind pw3EchoFreeArm false := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3EchoKind pw3EchoFreeArm false 1
    (by decide +kernel)
  intro pre given hpre hgiven _
  obtain ⟨x0, x1, x2, x3, x4, rfl⟩ := list_length_eq_5 hpre
  obtain ⟨g0, g1, rfl⟩ := list_length_eq_2 hgiven
  exact ⟨Val.ofList [.int 0, .int 1, .int 0, Val.nil], rfl, ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- **Concrete `ArmCorrect` Theorem 2 (`echo_command_armCorrect`)**:
    `pw3EchoCommandArm` (`:COMMAND` mutating run arm of `FN2-ECHO`, `observe = false`)
    satisfies `ArmCorrect`, executing `:SET`, `:NEXT`, and `:CHARGE` and preserving untaken
    children (`FN2-POOL`, `FN2-OPS`). -/
theorem echo_command_armCorrect :
    ArmCorrect pw3World pw3Guard pw3EchoKind pw3EchoCommandArm false := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3EchoKind pw3EchoCommandArm false 3
    (by decide +kernel)
  intro pre given hpre hgiven hguard
  obtain ⟨id, slot, kind, ord, budget, rfl⟩ := list_length_eq_5 hpre
  obtain ⟨echo, machines, ctrl, rfl⟩ := list_length_eq_3 hgiven
  obtain rfl : slot = .int 0 := isSlotZero_eq_true hguard
  refine ⟨echoCommandSpec (.int 0) echo machines ctrl, rfl, ⟨rfl, rfl⟩, fun rest => ?_⟩
  dsimp only [runArm, widen, takes]
  simp +zetaHave only [Bool.false_eq_true, ↓reduceIte, except_pure_bind,
    List.zip, List.headD, pw3EchoCommandArm_read, except_ok_bind, run_echo_command]
  rfl

/-- **Concrete `ArmCorrect` Theorem 3 (`echo_closeResult_armCorrect`)**:
    `pw3EchoCloseResultArm` (`:CLOSE-RESULT` observation handler of `FN2-ECHO`, `observe = true`)
    satisfies `ArmCorrect`. -/
theorem echo_closeResult_armCorrect :
    ArmCorrect pw3World pw3Guard pw3EchoKind pw3EchoCloseResultArm true := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3EchoKind pw3EchoCloseResultArm true 2
    (by decide +kernel)
  intro pre given hpre hgiven hguard
  obtain ⟨id, slot, kind, ord, ev_, outc, reas, cnt, a0, a1, rfl⟩ := list_length_eq_10 hpre
  obtain ⟨echo, machines, ctrl, rfl⟩ := list_length_eq_3 hgiven
  obtain rfl : slot = .int 0 := isSlotZero_eq_true hguard
  refine ⟨echoCloseResultSpec id (.int 0) echo machines ctrl, rfl, ⟨rfl, rfl⟩, fun rest => ?_⟩
  dsimp only [runArm, widen, takes]
  simp +zetaHave only [↓reduceIte, except_pure_bind,
    List.zip, List.headD, pw3EchoCloseResultArm_read, except_ok_bind, run_echo_closeResult]
  rfl

/-- **Concrete `ArmCorrect` Theorem 4 (`listener_accepting_armCorrect`)**:
    `pw3ListenerAcceptingArm` (`:ACCEPTING` arm of `FN2-LISTENER`, `observe = false`)
    satisfies `ArmCorrect`. -/
theorem listener_accepting_armCorrect :
    ArmCorrect pw3World pw3Guard pw3ListenerKind pw3ListenerAcceptingArm false := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3ListenerKind pw3ListenerAcceptingArm false 1
    (by decide +kernel)
  intro pre given hpre hgiven _
  obtain ⟨x0, x1, x2, x3, x4, rfl⟩ := list_length_eq_5 hpre
  obtain ⟨g0, g1, rfl⟩ := list_length_eq_2 hgiven
  exact ⟨Val.ofList [.int 0, .int 1, .int 0, Val.nil], rfl, ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- **Concrete `ArmCorrect` Theorem 5 (`listener_closeResult_armCorrect`)**:
    `pw3ListenerCloseResultArm` (`:CLOSE-RESULT` observation handler of `FN2-LISTENER`,
    `observe = true`) satisfies `ArmCorrect`. -/
theorem listener_closeResult_armCorrect :
    ArmCorrect pw3World pw3Guard pw3ListenerKind pw3ListenerCloseResultArm true := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3ListenerKind pw3ListenerCloseResultArm true 3
    (by decide +kernel)
  intro pre given hpre hgiven hguard
  obtain ⟨id, slot, kind, ord, ev_, outc, reas, cnt, a0, a1, rfl⟩ := list_length_eq_10 hpre
  obtain ⟨listener, machines, ctrl, rfl⟩ := list_length_eq_3 hgiven
  obtain rfl : slot = .int 0 := isSlotZero_eq_true hguard
  refine ⟨listenerCloseResultSpec id (.int 0) listener machines ctrl, rfl, ⟨rfl, rfl⟩, fun rest => ?_⟩
  dsimp only [runArm, widen, takes]
  simp +zetaHave only [↓reduceIte, except_pure_bind,
    List.zip, List.headD, pw3ListenerCloseResultArm_read, except_ok_bind, run_listener_closeResult]
  rfl

/-- **Concrete `ArmCorrect` Theorem 6 (`scribe_free_armCorrect`)**:
    `pw3ScribeFreeArm` (`:FREE` arm of `FN2-SCRIBE`, `observe = false`) satisfies `ArmCorrect`. -/
theorem scribe_free_armCorrect :
    ArmCorrect pw3World pw3Guard pw3ScribeKind pw3ScribeFreeArm false := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3ScribeKind pw3ScribeFreeArm false 1
    (by decide +kernel)
  intro pre given hpre hgiven _
  obtain ⟨x0, x1, x2, x3, x4, rfl⟩ := list_length_eq_5 hpre
  obtain ⟨g0, g1, rfl⟩ := list_length_eq_2 hgiven
  exact ⟨Val.ofList [.int 0, .int 1, .int 0, Val.nil], rfl, ⟨rfl, rfl⟩, fun _ => rfl⟩

/-- **Concrete `ArmCorrect` Theorem 7 (`scribe_stop_armCorrect`)**:
    `pw3ScribeStopSubarm` (`STOP` sub-arm of `FN2-SCRIBE`, `observe = false`) satisfies `ArmCorrect`. -/
theorem scribe_stop_armCorrect :
    ArmCorrect pw3World pw3Guard pw3ScribeKind pw3ScribeStopSubarm false := by
  apply armCorrect_of_runArm_at pw3World pw3Guard pw3ScribeKind pw3ScribeStopSubarm false 3
    (by decide +kernel)
  intro pre given hpre hgiven hguard
  obtain ⟨id, slot, kind, ord, budget, rfl⟩ := list_length_eq_5 hpre
  obtain ⟨scribe, machines, ctrl, rfl⟩ := list_length_eq_3 hgiven
  obtain rfl : slot = .int 0 := isSlotZero_eq_true hguard
  refine ⟨scribeStopSpec (.int 0) scribe machines ctrl, rfl, ⟨rfl, rfl⟩, fun rest => ?_⟩
  dsimp only [runArm, widen, takes]
  simp +zetaHave only [Bool.false_eq_true, ↓reduceIte, except_pure_bind,
    List.zip, List.headD, pw3ScribeStopSubarm_read, except_ok_bind, run_scribe_stop]
  rfl

/-- **End-to-End Composition (`echo_command_project_preserve`)**:
    Composes `echo_command_armCorrect` with `armCorrect_project_preserve`. -/
theorem echo_command_project_preserve
    (pre given : List Val) (rest : String → Val)
    (hpre : pre.length = nPre false)
    (hgiven : given.length = (takes pw3EchoKind pw3EchoCommandArm).length)
    (hguard : Guarded pw3Guard pw3EchoCommandArm.fn (pre ++ given)) :
    ∃ v N, pw3World.fns pw3EchoCommandArm.fn (pre ++ given) = some v ∧
      NarrowShape pw3EchoKind pw3EchoCommandArm false v ∧
      ∀ fuel, N ≤ fuel →
        ∃ out, runArm pw3World pw3EchoKind pw3EchoCommandArm false
            (widen pw3EchoKind pw3EchoCommandArm pre given rest) fuel = .ok out ∧
          project pw3EchoKind pw3EchoCommandArm false out =
            normalize pw3EchoKind pw3EchoCommandArm false v :=
  armCorrect_project_preserve pw3World pw3Guard pw3EchoKind pw3EchoCommandArm false
    echo_command_armCorrect (by decide) (by decide) pre given rest hpre hgiven hguard

/-- **End-to-End Composition (`listener_closeResult_project_preserve`)**:
    Composes `listener_closeResult_armCorrect` with `armCorrect_project_preserve`. -/
theorem listener_closeResult_project_preserve
    (pre given : List Val) (rest : String → Val)
    (hpre : pre.length = nPre true)
    (hgiven : given.length = (takes pw3ListenerKind pw3ListenerCloseResultArm).length)
    (hguard : Guarded pw3Guard pw3ListenerCloseResultArm.fn (pre ++ given)) :
    ∃ v N, pw3World.fns pw3ListenerCloseResultArm.fn (pre ++ given) = some v ∧
      NarrowShape pw3ListenerKind pw3ListenerCloseResultArm true v ∧
      ∀ fuel, N ≤ fuel →
        ∃ out, runArm pw3World pw3ListenerKind pw3ListenerCloseResultArm true
            (widen pw3ListenerKind pw3ListenerCloseResultArm pre given rest) fuel = .ok out ∧
          project pw3ListenerKind pw3ListenerCloseResultArm true out =
            normalize pw3ListenerKind pw3ListenerCloseResultArm true v :=
  armCorrect_project_preserve pw3World pw3Guard pw3ListenerKind pw3ListenerCloseResultArm true
    listener_closeResult_armCorrect (by decide) (by decide) pre given rest hpre hgiven hguard

/-- **End-to-End Composition (`scribe_stop_project_preserve`)**:
    Composes `scribe_stop_armCorrect` with `armCorrect_project_preserve`. -/
theorem scribe_stop_project_preserve
    (pre given : List Val) (rest : String → Val)
    (hpre : pre.length = nPre false)
    (hgiven : given.length = (takes pw3ScribeKind pw3ScribeStopSubarm).length)
    (hguard : Guarded pw3Guard pw3ScribeStopSubarm.fn (pre ++ given)) :
    ∃ v N, pw3World.fns pw3ScribeStopSubarm.fn (pre ++ given) = some v ∧
      NarrowShape pw3ScribeKind pw3ScribeStopSubarm false v ∧
      ∀ fuel, N ≤ fuel →
        ∃ out, runArm pw3World pw3ScribeKind pw3ScribeStopSubarm false
            (widen pw3ScribeKind pw3ScribeStopSubarm pre given rest) fuel = .ok out ∧
          project pw3ScribeKind pw3ScribeStopSubarm false out =
            normalize pw3ScribeKind pw3ScribeStopSubarm false v :=
  armCorrect_project_preserve pw3World pw3Guard pw3ScribeKind pw3ScribeStopSubarm false
    scribe_stop_armCorrect (by decide) (by decide) pre given rest hpre hgiven hguard

end Fn2.Pathway

