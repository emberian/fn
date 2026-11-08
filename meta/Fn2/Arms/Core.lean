module

public import Fn2.Arms.Columns
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String

@[expose] public section

/-!
# Fn2.Arms.Core: core-form kinds, run through their core face

A **core-form** kind (`fn2-conn`, `fn2-cns`, `fn2-txn`, `fn2-upload`, `fn2-ctl`, the listener) is
one whose arms the generator expands over `fn2-core` (`machine-arms.lisp`, mode `:core`): the arm
function is `(FN id budget fn2-core)` (a handler `(FN id event outcome reason count aux0 aux1
fn2-core)`), its operations are called over the core, its batched write is `K-PUT-CORE` (through
the field set's `K-WRITE+F...` function), its stop `fn2-core-stop`. These are the generator's
child-form constructs lifted by `stobj-let` (ACL2's own definitions: `fn2-core-stop` is
`fn2-control-record-stop` on the core's control child; `K-PUT-CORE` the checked write of the
kind's table and the directory; an operation's `:core` face the `stobj-let` of its `:child`'s
children), plus operations that exist **only** over the core (no `:child`: `fn2-cns-commit-op`,
`fn2-conn-run-answer`, ...).

`fn2-core`'s logical value is the list of its children in field order (`coreTuple`, printed from
`*fn2-core-children*`). So this file runs a core-form arm as the interpreter's child form over
**all** of the core's children (`coreKind`), in a world (`coreWorld`) where an operation with no
`:child` is called through an adapter that assembles the core from the children, applies the
operation's translation, and splits the returned core back (`coreFns`). `runCore` is the arm
function's entry: the kind's snapshot read code (else the core stops with `:machine-phase`,
`:machine-observation` for a handler, and the run charges `*fn2-work-empty*`), the row's slot
from the directory, the kind's index constants for `KIND` and `ORDINAL`, then the run, and the
children reassembled into the core it returns.

Why this and not an emitter that prints core-form kinds in child form: those kinds call
operations that have no child form at all, so no child-form function of them exists to print;
the generator's core mode is the same step language over the same primitives lifted through the
core, which is what this file states. Where the core mode's own checks differ from the child
form's (`K-PUT-CORE` also refuses a write when the row's id is no longer a row of the kind; a
`:goto` re-reads the snapshot code), the measure compares the two on ACL2's recorded calls.

The contracts proved over `runArm` (`runArm_charge_le_cost`, `runArm_frame`,
`runArm_writes_sub`, `runArm_next_mem`) carry to `runCore` (`runCore_charge_le_cost`,
`runCore_frame`, `runCore_writes_sub`, `runCore_next_mem`), each about every successful run.
-/

namespace Fn2.Arms.Core
open Fn2.ACL2 Fn2.Arms Fn2.Arms.Cost Fn2.Arms.Frame Fn2.Arms.Columns

set_option autoImplicit false

/-! ## The core face -/

/-- The name an operation without a `:child` is called by in the core face. -/
def adapterName (f : String) : String := f ++ "@CORE"

/-- An operation's formals (or stobj signature) with the core expanded to its children. -/
def expandF (tuple : List String) (formals : List String) (sin : List (Option String)) :
    List String :=
  (formals.zip sin).flatMap fun (f, s) => if s == some "FN2-CORE" then tuple else [f]

def expandS (tuple : List String) (sig : List (Option String)) : List (Option String) :=
  sig.flatMap fun s => if s == some "FN2-CORE" then tuple.map some else [s]

/-- The operation's actuals from the adapter's: the children at the core's place assembled into
the core (its logical value is their list). -/
def collapse (n : Nat) : List (Option String) → List Val → Option (List Val)
  | [], [] => some []
  | s :: ss, args =>
    if s == some "FN2-CORE" then
      if args.length < n then none
      else (collapse n ss (args.drop n)).map (Val.ofList (args.take n) :: ·)
    else match args with
      | a :: as => (collapse n ss as).map (a :: ·)
      | [] => none
  | [], _ :: _ => none

/-- The operation's results with the returned core split into its children. -/
def spread (sout : List (Option String)) (res : Val) : Val :=
  match sout with
  | [_] => res
  | _ => Val.ofList ((sout.zip res.toList).flatMap fun (s, r) =>
      if s == some "FN2-CORE" then r.toList else [r])

/-- The translated functions, each operation without a `:child` through its adapter, and each
other function over `fn2-core` (a link's core-mode live test and readers, `(… fn2-core)`, which
return no stobj) with its trailing children assembled into the core. -/
def coreFns (w : World) (tuple : List String) : Fns := fun f args =>
  if f.endsWith "@CORE" then
    match w.ops.find? (fun o => adapterName o.name == f) with
    | some o => match collapse tuple.length o.coreIn args with
      | some actuals => (w.fns o.name actuals).map (spread o.coreOut)
      | none => none
    | none =>
      if args.length < tuple.length then none
      else
        let n := args.length - tuple.length
        w.fns (String.ofList (f.toList.take (f.length - 5))) (args.take n ++ [Val.ofList (args.drop n)])
  else w.fns f args

/-- An operation as the core face calls it: through its `:child` when it has one (the
generator's `:core` face of a `:child` is the `stobj-let` of its children), else through its
adapter over every child of the core. -/
def coreOp (tuple : List String) (o : Op) : Op :=
  match o.callee with
  | some _ => o
  | none =>
    if o.coreFormals.isEmpty then o
    else { o with callee := some (adapterName o.name),
                  formals := expandF tuple o.coreFormals o.coreIn,
                  stobjsIn := expandS tuple o.coreIn,
                  stobjsOut := expandS tuple o.coreOut }

/-- The world of the core face. -/
def coreWorld (w : World) (tuple : List String) : World :=
  { w with ops := w.ops.map (coreOp tuple), fns := coreFns w tuple }

/-- A core-form kind over the core's children. -/
def coreKind (k : Kind) (tuple : List String) : Kind :=
  { k with tuple := tuple, childForm := true, core := true }

/-! ## The arm function's entry -/

/-- The arm function's leading formals: `(id budget)` for an arm, `(id event outcome reason
count aux0 aux1)` for a handler. -/
def nCore (observe : Bool) : Nat := if observe then 7 else 2

/-- The results before the core: `(bytes steps descriptors runnable)` or `(wake)`. -/
def nRes (observe : Bool) : Nat := if observe then 1 else 4

/-- `fn2-core-stop`: the core's control child records the stop. -/
def coreStop (w : World) (tuple : List String) (reason : Val) (kids : List Val) :
    Except String (List Val) := do
  let i := tuple.idxOf "FN2-CONTROL"
  let c ← callFn w "FN2-CONTROL-RECORD-STOP" [reason, kids.getD i Val.nil]
  pure (kids.set i c)

/-- The refused entry (the snapshot read code is not `:ok`): the core stops, the arm charges
`*fn2-work-empty*` (a handler answers no wake). -/
def refusedEntry (w : World) (tuple : List String) (observe : Bool) (kids : List Val) :
    Except String Val := do
  let reason ← const w (if observe then "*FN2-STOP-REASON-MACHINE-OBSERVATION*"
    else "*FN2-STOP-REASON-MACHINE-PHASE*")
  let kids' ← coreStop w tuple reason kids
  if observe then pure (Val.ofList [← const w "*FN2-NONE*", Val.ofList kids'])
  else pure (Val.ofList [.int 0, ← const w "*FN2-WORK-EMPTY*", .int 0, Val.nil, Val.ofList kids'])

/-- The kind's admission ordinal (`*K-ADMISSION-ORDINAL*`), `0` for a kind with none (as the
generator's face passes it). -/
def ordOf (w : World) (k : Kind) : Val :=
  match const w ("*" ++ k.name ++ "-ADMISSION-ORDINAL*") with
  | .ok v => v
  | .error _ => .int 0

/-- The child-form run's results reassembled: the leading results, then the core. -/
def finish (observe : Bool) (tuple : List String) (v : Val) : Except String Val :=
  if v.toList.length = nRes observe + tuple.length then
    .ok (Val.ofList (v.toList.take (nRes observe) ++ [Val.ofList (v.toList.drop (nRes observe))]))
  else .error s!"a result of {v.toList.length} values"

/-- The run of a core-form arm, handler or sub-arm on its function's arguments `args` (the leading
formals, then `fn2-core`). The value is the function's `mv` list, ending in the core. -/
def runCore (w : World) (tuple : List String) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat := 100000) : Except String Val :=
  if args.length ≠ nCore observe + 1 then
    .error s!"{a.fn}: {args.length} arguments for {nCore observe + 1} formals"
  else if (args.getLastD Val.nil).toList.length ≠ tuple.length then
    .error s!"{a.fn}: a core of {(args.getLastD Val.nil).toList.length} children, the layout {tuple.length}"
  else do
    let code ← callFn w (k.name ++ "-SNAPSHOT-READ-CODE") [args.headD Val.nil, args.getLastD Val.nil]
    if code == Val.sym ":OK" then do
      let slot ← callFn w "FN2-MACHINE-SLOT" [args.headD Val.nil, args.getLastD Val.nil]
      let kind ← const w ("*" ++ k.name ++ "-KIND*")
      let v ← runArm (coreWorld w tuple) (coreKind k tuple) a observe
        ([args.headD Val.nil, slot, kind, ordOf w k] ++ (args.take (nCore observe)).drop 1 ++
          (args.getLastD Val.nil).toList) fuel
      finish observe tuple v
    else refusedEntry w tuple observe (args.getLastD Val.nil).toList

/-! ## The shape of a run -/

theorem toList_ofList' (xs : List Val) : (Val.ofList xs).toList = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Val.ofList, Val.toList, ih]

theorem bind_ok' {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A successful run of `runCore`: the core's children have the layout's length, and the run is
either the refused entry or the interpreter's child-form run over them, its result reassembled. -/
theorem runCore_cases (w : World) (tuple : List String) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val)
    (hrun : runCore w tuple k a observe args fuel = .ok v) :
    args.length = nCore observe + 1 ∧ (args.getLastD Val.nil).toList.length = tuple.length ∧
    (refusedEntry w tuple observe (args.getLastD Val.nil).toList = .ok v ∨
     ∃ pre v0, pre.length = (if observe then 10 else 5) ∧
       runArm (coreWorld w tuple) (coreKind k tuple) a observe
         (pre ++ (args.getLastD Val.nil).toList) fuel = .ok v0 ∧
       v0.toList.length = nRes observe + tuple.length ∧
       v = Val.ofList (v0.toList.take (nRes observe) ++ [Val.ofList (v0.toList.drop (nRes observe))])) := by
  unfold runCore at hrun
  by_cases hl : args.length ≠ nCore observe + 1
  · rw [if_pos hl] at hrun; cases hrun
  rw [if_neg hl] at hrun
  by_cases hk : (args.getLastD Val.nil).toList.length ≠ tuple.length
  · rw [if_pos hk] at hrun; cases hrun
  rw [if_neg hk] at hrun
  refine ⟨by simpa using hl, by simpa using hk, ?_⟩
  obtain ⟨code, _, hrun⟩ := bind_ok' hrun
  by_cases hc : (code == Val.sym ":OK") = true
  · rw [if_pos hc] at hrun
    obtain ⟨slot, _, hrun⟩ := bind_ok' hrun
    obtain ⟨kind, _, hrun⟩ := bind_ok' hrun
    obtain ⟨v0, hv0, hrun⟩ := bind_ok' hrun
    unfold finish at hrun
    by_cases hx : v0.toList.length = nRes observe + tuple.length
    · rw [if_pos hx] at hrun
      simp only [Except.ok.injEq] at hrun
      refine Or.inr ⟨_, _, ?_, hv0, hx, hrun.symm⟩
      have hl' : args.length = nCore observe + 1 := by simpa using hl
      cases observe <;> simp [nCore] at hl' ⊢ <;> omega
    · rw [if_neg hx] at hrun; cases hrun
  · rw [if_neg hc] at hrun
    exact Or.inl hrun

/-- The refused entry's value: the leading results, then the core with only its control child
replaced. -/
theorem refusedEntry_shape (w : World) (tuple : List String) (observe : Bool) (kids : List Val)
    (v : Val) (h : refusedEntry w tuple observe kids = .ok v) :
    ∃ c pre, v.toList = pre ++ [Val.ofList (kids.set (tuple.idxOf "FN2-CONTROL") c)] ∧
      pre.length = nRes observe ∧
      (observe = false → ∃ e, const w "*FN2-WORK-EMPTY*" = .ok e ∧
        pre = [.int 0, e, .int 0, Val.nil]) := by
  unfold refusedEntry at h
  obtain ⟨r, _, h⟩ := bind_ok' h
  obtain ⟨kids', hks, h⟩ := bind_ok' h
  unfold coreStop at hks
  obtain ⟨c, _, hks⟩ := bind_ok' hks
  simp only [pure, Except.pure, Except.ok.injEq] at hks
  subst hks
  cases observe
  · simp only [Bool.false_eq_true, if_false] at h
    obtain ⟨e, he, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨c, _, by simp [toList_ofList'], by simp [nRes], fun _ => ⟨e, he, rfl⟩⟩
  · simp only [if_true] at h
    obtain ⟨e, _, h⟩ := bind_ok' h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨c, [e], by simp [toList_ofList'], by simp [nRes], fun h => by cases h⟩

theorem getElem_idxOf' (l : List String) (x : String) (i : Nat) (hi : i < l.length)
    (h : l.idxOf x = i) : l[i] = x := by
  induction l generalizing i with
  | nil => simp at hi
  | cons y l ih =>
    rw [List.idxOf_cons] at h
    by_cases hy : y = x
    · subst hy; simp at h; subst h; simp
    · have hb : (y == x) = false := by simp [hy]
      simp only [hb, cond_false] at h
      cases i with
      | zero => omega
      | succ j => simpa using ih j (by simpa using hi) (by omega)

theorem getD_take_append (xs : List Val) (y d : Val) (n i : Nat) (hi : i < n) (hn : n ≤ xs.length) :
    (xs.take n ++ [y]).getD i d = xs.getD i d := by
  have h1 : i < (xs.take n).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  simp [hi]

/-! ## The contracts, for core-form kinds -/

/-- **Theorem (`runCore_charge_le_cost`)**: when a core-form arm has the derived charge bound `C`
over the core face, and `C` covers the refused entry's `*fn2-work-empty*` steps, every successful
run of the arm function charges at most `C`. -/
theorem runCore_charge_le_cost (w : World) (tuple : List String) (k : Kind) (a : Arm)
    (args : List Val) (fuel : Nat) (v : Val) (C : Cost)
    (hC : derivedCost (coreWorld w tuple) (coreKind k tuple) a = some C)
    (hE : ∀ e, const w "*FN2-WORK-EMPTY*" = .ok e → CostLe (0, e.toInt, 0) C)
    (hrun : runCore w tuple k a false args fuel = .ok v) :
    CostLe (extractCharge v) C := by
  obtain ⟨_, _, hr | ⟨pre, v0, _, hv0, hlen, hv⟩⟩ := runCore_cases w tuple k a false args fuel v hrun
  · obtain ⟨c, pre, hvl, _, hpre⟩ := refusedEntry_shape w tuple false _ v hr
    obtain ⟨e, he, rfl⟩ := hpre rfl
    have := hE e he
    simp only [extractCharge, hvl]
    simpa [Val.toInt] using this
  · have h := runArm_charge_le_cost (coreWorld w tuple) (coreKind k tuple) a _ fuel v0 C hC hv0
    have hl4 : 3 < v0.toList.length := by simp [nRes] at hlen; omega
    subst hv
    simp only [extractCharge, toList_ofList'] at h ⊢
    have e0 := getD_take_append v0.toList (Val.ofList (v0.toList.drop 4)) Val.nil 4 0 (by omega) (by omega)
    have e1 := getD_take_append v0.toList (Val.ofList (v0.toList.drop 4)) Val.nil 4 1 (by omega) (by omega)
    have e2 := getD_take_append v0.toList (Val.ofList (v0.toList.drop 4)) Val.nil 4 2 (by omega) (by omega)
    simp only [nRes, Bool.false_eq_true, if_false]
    rw [e0, e1, e2]; exact h

/-- **Theorem (`runCore_frame`)**: when a core-form arm has the derived children `D` over the core
face (and the layout names each child once), every successful run returns the core as its last
result, with every child outside `D` other than the control (which the refused entry's stop
writes) exactly as it was passed in. -/
theorem runCore_frame (w : World) (tuple : List String) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val) (D : List String)
    (hD : derivedTables (coreWorld w tuple) (coreKind k tuple) a = some D) (hnd : tuple.Nodup)
    (hrun : runCore w tuple k a observe args fuel = .ok v) :
    ∃ pre core', v.toList = pre ++ [core'] ∧ pre.length = nRes observe ∧
      core'.toList.length = tuple.length ∧
      ∀ i (hi : i < tuple.length), tuple[i] ∉ D → tuple[i] ≠ "FN2-CONTROL" →
        core'.toList[i]? = (args.getLastD Val.nil).toList[i]? := by
  obtain ⟨_, hk, hr | ⟨pre, v0, hpre, hv0, hlen, hv⟩⟩ := runCore_cases w tuple k a observe args fuel v hrun
  · obtain ⟨c, pre, hvl, hpl, _⟩ := refusedEntry_shape w tuple observe _ v hr
    refine ⟨pre, _, hvl, hpl, by rw [toList_ofList', List.length_set]; exact hk, fun i hi _ hc => ?_⟩
    rw [toList_ofList', List.getElem?_set]
    have hne : tuple.idxOf "FN2-CONTROL" ≠ i := by
      intro he; apply hc
      have hlt : tuple.idxOf "FN2-CONTROL" < tuple.length := he ▸ hi
      have := getElem_idxOf' tuple "FN2-CONTROL" _ hlt rfl
      simpa [he] using this
    simp [hne]
  · obtain ⟨pre0, ts, hvs, hts, hfr⟩ :=
      runArm_frame (coreWorld w tuple) (coreKind k tuple) a observe _ fuel v0 D hD hnd hv0
    have hp0 : pre0.length = nRes observe := by
      have := congrArg List.length hvs
      simp [coreKind] at hts
      simp only [List.length_append] at this; omega
    subst hv
    refine ⟨v0.toList.take (nRes observe), Val.ofList (v0.toList.drop (nRes observe)),
      by simp [toList_ofList'], by simp [List.length_take]; omega, ?_, fun i hi hD' _ => ?_⟩
    · simp [toList_ofList', hvs, hp0, coreKind] at hts ⊢; omega
    · have h := hfr i (by simpa [coreKind] using hi) (by simpa [coreKind] using hD')
      have hd : (v0.toList.drop (nRes observe)) = ts := by rw [hvs, ← hp0]; simp
      have hdrop : (pre ++ (args.getLastD Val.nil).toList).drop (if observe then 10 else 5) =
          (args.getLastD Val.nil).toList := by rw [← hpre]; simp
      have h' : ts[i]? = (args.getLastD Val.nil).toList[i]? := by
        have e : ((pre ++ (args.getLastD Val.nil).toList).drop (if observe then 10 else 5))[i]? =
            (args.getLastD Val.nil).toList[i]? := by rw [hdrop]
        exact h.trans e
      rw [toList_ofList', hd]
      exact h'

/-- The core's children as a state (`fn2-core`'s value is their list in field order). -/
def coreSt (tuple : List String) (core : Val) : St := { stobjs := tuple.zip core.toList, vars := [] }

theorem find_zip_set (l : List String) (vs : List Val) (x n : String) (c : Val) (hn : n ≠ x) :
    (l.zip (vs.set (l.idxOf x) c)).find? (·.1 == n) = (l.zip vs).find? (·.1 == n) := by
  induction l generalizing vs with
  | nil => simp
  | cons y l ih =>
    cases vs with
    | nil => simp
    | cons v vs =>
      rw [List.idxOf_cons]
      by_cases hy : y = x
      · subst hy
        have hb : (y == n) = false := by simp [Ne.symm hn]
        simp [hb]
      · have hb : (y == x) = false := by simp [hy]
        simp only [hb, cond_false, List.set_cons_succ, List.zip_cons_cons, List.find?_cons]
        split <;> simp_all

/-- The refused entry's stop changes only the control child. -/
theorem coreSt_set_control (tuple : List String) (kids : List Val) (c : Val) (n : String)
    (hn : n ≠ "FN2-CONTROL") :
    stobj (coreSt tuple (Val.ofList (kids.set (tuple.idxOf "FN2-CONTROL") c))) n =
      stobj (coreSt tuple (Val.ofList kids)) n := by
  simp only [stobj, coreSt, toList_ofList', find_zip_set tuple kids _ n c hn]

theorem ofList_toList_of_len (tuple : List String) (v : Val) (kids : List Val) (h : v.toList = kids) :
    stobj (coreSt tuple v) = stobj (coreSt tuple (Val.ofList kids)) := by
  funext n; simp [coreSt, toList_ofList', h]

/-- The main branch's children: the core `runCore` returns holds the child-form run's tuple, and
the core it was passed is the state the child-form run started from. -/
theorem runCore_main (tuple : List String) (k : Kind) (observe : Bool)
    (args pre ts pre0 : List Val) (v0 : Val)
    (hpre : pre.length = (if observe then 10 else 5)) (hvs : v0 = Val.ofList (pre0 ++ ts))
    (hts : ts.length = tuple.length) (hlen : v0.toList.length = nRes observe + tuple.length) :
    Val.ofList (v0.toList.take (nRes observe) ++ [Val.ofList (v0.toList.drop (nRes observe))]) =
        Val.ofList (pre0 ++ [Val.ofList ts]) ∧
      stobj (coreSt tuple (Val.ofList ts)) =
        stobj (tupleSt (coreKind k tuple) ts) ∧
      stobj (coreSt tuple (args.getLastD Val.nil)) =
        stobj (Inv.startSt (coreKind k tuple) observe (pre ++ (args.getLastD Val.nil).toList)) := by
  have hp0 : pre0.length = nRes observe := by
    rw [hvs, toList_ofList', List.length_append] at hlen; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hvs, toList_ofList', ← hp0]; simp
  · funext n; simp [coreSt, tupleSt, coreKind, toList_ofList']
  · funext n
    have hdrop : (pre ++ (args.getLastD Val.nil).toList).drop (if observe then 10 else 5) =
        (args.getLastD Val.nil).toList := by rw [← hpre]; simp
    simp only [coreSt, Inv.startSt, coreKind, hdrop]

/-- **Theorem (`runCore_writes_sub`)**: when a core-form arm has the checked written columns `W`
over the core face (and the world's setters keep the columns' frame), every successful run
returns a core whose kind table reads back, at every column outside `W` other than `PHASE` and
at every slot, as in the core it was passed. -/
theorem runCore_writes_sub (w : World) (tuple : List String) (k : Kind) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val) (W : List String)
    (hW : checkedWrites (coreWorld w tuple) (coreKind k tuple) a = some W)
    (TF : TableFacts (coreWorld w tuple) (coreKind k tuple))
    (hshape : kindShape (coreKind k tuple) = true)
    (hrun : runCore w tuple k a observe args fuel = .ok v) :
    ∃ pre core', v.toList = pre ++ [core'] ∧
      ∀ c ∈ k.columns.map Prod.fst, c ≠ "PHASE" → c ∉ W → ∀ s,
        colGet (coreWorld w tuple) (coreKind k tuple) (stobj (coreSt tuple core')) c s =
          colGet (coreWorld w tuple) (coreKind k tuple) (stobj (coreSt tuple (args.getLastD Val.nil))) c s := by
  obtain ⟨hnd, hmk, hmm, hmd, hmc⟩ := kindShape_spec (coreKind k tuple) hshape
  obtain ⟨_, _, hr | ⟨pre, v0, hpre, hv0, hlen, hv⟩⟩ := runCore_cases w tuple k a observe args fuel v hrun
  · obtain ⟨c, pre, hvl, _, _⟩ := refusedEntry_shape w tuple observe _ v hr
    refine ⟨pre, _, hvl, fun col _ _ _ s => ?_⟩
    have hk : k.name ≠ "FN2-CONTROL" := by simpa [coreKind] using hmc
    rw [ofList_toList_of_len (tuple := tuple) (args.getLastD Val.nil) _ rfl]
    unfold colGet
    rw [coreSt_set_control tuple _ c "FN2-MACHINES" (by decide)]
    simp only [coreKind] at *
    rw [coreSt_set_control tuple _ c k.name hk]
  · obtain ⟨pre0, ts, hvs, hts, hcols⟩ :=
      runArm_writes_sub (coreWorld w tuple) (coreKind k tuple) a observe _ fuel v0 W hW TF hshape hv0
    obtain ⟨e1, e2, e3⟩ := runCore_main tuple k observe args pre ts pre0 v0 hpre hvs
      (by simpa [coreKind] using hts) hlen
    refine ⟨pre0, Val.ofList ts, by rw [hv, e1, toList_ofList'], fun col hc hp hw s => ?_⟩
    rw [e2, e3]
    exact hcols col (by simpa [coreKind] using hc) hp hw s

/-- **Theorem (`runCore_next_mem`)**: when a core-form arm has the checked phases `D` over the core
face (the world's setters keep the columns' frame, and every phase value is a state's), every
successful run returns a core in which each row's `PHASE` reads back as passed in or as the
value of one of `D`. -/
theorem runCore_next_mem (w : World) (tuple : List String) (k : Kind) (PK : List String)
    (hPK : ∀ op ∈ PK, KeepsPhase (coreWorld w tuple) (coreKind k tuple) op) (a : Arm) (observe : Bool)
    (args : List Val) (fuel : Nat) (v : Val) (D : List String)
    (hD : checkedNextP (coreWorld w tuple) (coreKind k tuple) PK a = some D)
    (TF : TableFacts (coreWorld w tuple) (coreKind k tuple))
    (hshape : kindShape (coreKind k tuple) = true) (hpc : phasesCover (coreKind k tuple) = true)
    (hrun : runCore w tuple k a observe args fuel = .ok v) :
    ∃ pre core', v.toList = pre ++ [core'] ∧
      ∀ s, colGet (coreWorld w tuple) (coreKind k tuple) (stobj (coreSt tuple core')) "PHASE" s =
          colGet (coreWorld w tuple) (coreKind k tuple) (stobj (coreSt tuple (args.getLastD Val.nil))) "PHASE" s ∨
        ∃ p ∈ D, ∃ i, (p, i) ∈ k.phases ∧
          colGet (coreWorld w tuple) (coreKind k tuple) (stobj (coreSt tuple core')) "PHASE" s = .ok (.int i) := by
  obtain ⟨hnd, hmk, hmm, hmd, hmc⟩ := kindShape_spec (coreKind k tuple) hshape
  obtain ⟨_, _, hr | ⟨pre, v0, hpre, hv0, hlen, hv⟩⟩ := runCore_cases w tuple k a observe args fuel v hrun
  · obtain ⟨c, pre, hvl, _, _⟩ := refusedEntry_shape w tuple observe _ v hr
    refine ⟨pre, _, hvl, fun s => Or.inl ?_⟩
    have hk : k.name ≠ "FN2-CONTROL" := by simpa [coreKind] using hmc
    rw [ofList_toList_of_len (tuple := tuple) (args.getLastD Val.nil) _ rfl]
    unfold colGet
    rw [coreSt_set_control tuple _ c "FN2-MACHINES" (by decide)]
    simp only [coreKind] at *
    rw [coreSt_set_control tuple _ c k.name hk]
  · obtain ⟨pre0, ts, hvs, hts, hph⟩ :=
      runArm_next_memP (coreWorld w tuple) (coreKind k tuple) PK hPK a observe _ fuel v0 D hD TF hshape hpc hv0
    obtain ⟨e1, e2, e3⟩ := runCore_main tuple k observe args pre ts pre0 v0 hpre hvs
      (by simpa [coreKind] using hts) hlen
    refine ⟨pre0, Val.ofList ts, by rw [hv, e1, toList_ofList'], fun s => ?_⟩
    rw [e2, e3]
    simpa [coreKind] using hph s

end Fn2.Arms.Core

end
