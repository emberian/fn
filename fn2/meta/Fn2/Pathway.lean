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
exactly `widen`, `project` and `frameKept` below), not yet proved; a proof needs the reader and the
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

/-- Every child `FN` does not return leaves the interpreter as it entered. -/
def frameKept (k : Kind) (a : Arm) (observe : Bool) (input : List Val) (v : Val) : Prop :=
  ∀ c ∈ k.tuple, c ∉ returns k a →
    ∀ i, k.tuple.idxOf? c = some i → (v.toList.drop (nOuts observe))[i]? = input[i]?

/-- **PW3 for one arm.** `fns` and `guard` are the translated world's dispatch and guards
(`FN` is `fns a.fn`). -/
def ArmCorrect (w : World) (guard : String → List Val → Option Val) (k : Kind) (a : Arm)
    (observe : Bool) : Prop :=
  ∀ (pre given : List Val) (rest : String → Val),
    pre.length = nPre observe → given.length = (takes k a).length →
    ((guard a.fn (pre ++ given)).getD Val.nil).truthy = true →
    ∃ v, w.fns a.fn (pre ++ given) = some v ∧
      ∃ N, ∀ fuel, N ≤ fuel → ∃ r,
        runArm w k a observe (widen k a pre given rest) fuel = .ok r ∧
        project k a observe r = normalize k a observe v ∧
        frameKept k a observe (entering k a given rest) r

/-- PW3 for a kind: every arm, handler and sub-arm. -/
def KindCorrect (w : World) (guard : String → List Val → Option Val) (k : Kind) : Prop :=
  (∀ a ∈ k.arms, ArmCorrect w guard k a false) ∧
  (∀ a ∈ k.subarms, ArmCorrect w guard k a false) ∧
  (∀ a ∈ k.observes, ArmCorrect w guard k a true)

end Fn2.Pathway
