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

end Fn2.Pathway
