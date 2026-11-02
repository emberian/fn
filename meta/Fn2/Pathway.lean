import Fn2.Arms

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

end Fn2.Pathway

