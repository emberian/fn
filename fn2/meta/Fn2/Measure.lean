import Fn2.ACL2.Read
import Fn2.Arms
import Fn2.Instances.LayerAKinds

/-!
# Fn2.Measure: the translated kinds against the simulator's recorded calls

LEAN-METATHEORY §-1 item 3. Input: the recorder's lines (`fn2/meta/emit/record-arms.lsp`), each
`(FN (ARG ...) (RESULT ...))`, one call ACL2 executed while the A4 smoke's echo and scribe
scenarios ran, with the logical values of its arguments and results. For each call, two Lean
computations on the same arguments:

* **interp**: the definitional interpreter (`Fn2.Arms.runArm`) on the arm's declaration, its
  expressions and operations translated from the world;
* **generated**: the translation of the function ACL2 generated for that arm (`FN` itself, read
  from its translated body like every other function);
* **guard**: the translation of `FN`'s guard (the children's well-formedness, the slot and id
  bounds) on the recorded arguments, which ACL2's guard-verified caller established.

Each is equal to the recorded result or a named difference (the first result position that
differs; for a child, the first field and element). Performance is printed, never a gate.
-/

namespace Fn2.Measure
open Fn2.ACL2 Fn2.Arms

/-- Equality without recursion along a list's spine (records hold long arrays). -/
partial def same (a b : Val) : Bool := Id.run do
  let mut x := a
  let mut y := b
  while x.isCons && y.isCons do
    if !same x.car y.car then return false
    x := x.cdr
    y := y.cdr
  return x == y

def listOf (v : Val) : Array Val := Id.run do
  let mut out := #[]
  let mut cur := v
  while cur.isCons do
    out := out.push cur.car
    cur := cur.cdr
  return out

/-- The first difference between two results, named by position, field and element. -/
def diff (names : List String) (got want : Val) : String := Id.run do
  let g := listOf got
  let w := listOf want
  if g.size != w.size then return s!"result length {g.size}, recorded {w.size}"
  for i in [0:g.size] do
    if !same g[i]! w[i]! then
      let pos := names.getD i s!"#{i}"
      let gf := listOf g[i]!
      let wf := listOf w[i]!
      if g[i]!.isCons && w[i]!.isCons && gf.size == wf.size then
        for j in [0:gf.size] do
          if !same gf[j]! wf[j]! then
            let ge := listOf gf[j]!
            let we := listOf wf[j]!
            if gf[j]!.isCons && wf[j]!.isCons && ge.size == we.size then
              for k in [0:ge.size] do
                if !same ge[k]! we[k]! then
                  return s!"{pos} field {j} element {k}: {ge[k]!} (recorded {we[k]!})"
            return s!"{pos} field {j}: {(toString gf[j]!).take 120} (recorded {(toString wf[j]!).take 120})"
      return s!"{pos}: {(toString g[i]!).take 160} (recorded {(toString w[i]!).take 160})"
  return "equal"

structure Tally where
  calls : Nat := 0
  interpEq : Nat := 0
  genEq : Nat := 0
  guardT : Nat := 0
  firstInterp : Option String := none
  firstGen : Option String := none

def findArm (w : World) (fn : String) : Option (Kind × Arm × Bool) := Id.run do
  for k in w.kinds do
    for a in k.arms do
      if a.fn == fn then return some (k, a, false)
    for a in k.subarms do
      if a.fn == fn then return some (k, a, false)
    for a in k.observes do
      if a.fn == fn then return some (k, a, true)
  return none

def main (args : List String) : IO UInt32 := do
  let path := args.headD "build/lean-meta/arms-record.sexp"
  let w := Fn2.Instances.LayerAKinds.world
  let text ← IO.FS.readFile path
  let mut tallies : Std.HashMap String Tally := {}
  let mut order : Array String := #[]
  let mut lines := 0
  let t0 ← IO.monoMsNow
  for line in text.splitOn "\n" do
    if line.trim.isEmpty then continue
    lines := lines + 1
    let rec_ ← match Read.parse line with
      | .ok v => pure v
      | .error e => do IO.eprintln s!"unreadable record line {lines}: {e}"; return 2
    let rec_ := Read.expandRle rec_
    let fn := match rec_.car with | .sym s => s | _ => "?"
    let argv := (listOf (rec_.cdr.car)).toList
    let want := rec_.cdr.cdr.car
    let some (k, a, observe) := findArm w fn
      | do IO.eprintln s!"{fn}: no arm in the translated kinds"; return 2
    let nOuts := if observe then 1 else 4
    let nPre := if observe then 10 else 5
    -- a narrowed function takes and returns a subset of the kind's tuple (Fn2.Arms.Sig)
    let takes := (a.sig.map (·.takes)).getD k.tuple
    let returns := (a.sig.map (·.returns)).getD k.tuple
    let given := takes.zip (argv.drop nPre)
    let full := argv.take nPre ++ k.tuple.map fun c => ((given.find? (·.1 == c)).map (·.2)).getD Val.nil
    let project (v : Val) : Val :=
      let xs := (listOf v).toList
      let tup := k.tuple.zip (xs.drop nOuts)
      Val.ofList (xs.take nOuts ++ returns.map fun c => ((tup.find? (·.1 == c)).map (·.2)).getD Val.nil)
    let bare := nOuts + returns.length == 1
    let names := (if observe then ["wake"] else ["bytes", "steps", "descriptors", "runnable"]) ++ returns
    let interp := match runArm w k a observe full with
      | .ok v => let p := project v; if same p want then none else some (diff names p want)
      | .error e => some s!"error: {e}"
    let gen := match w.fns fn argv with
      | some v => let p := if bare then Val.ofList [v] else v
        if same p want then none else some (diff names p want)
      | none => some "no translated function"
    let guard := match Fn2.Instances.LayerAWorld.guardOf fn argv with
      | some v => v.truthy
      | none => false
    let t := (tallies.get? fn).getD {}
    if !(tallies.contains fn) then order := order.push fn
    tallies := tallies.insert fn
      { calls := t.calls + 1,
        interpEq := t.interpEq + (if interp.isNone then 1 else 0),
        genEq := t.genEq + (if gen.isNone then 1 else 0),
        guardT := t.guardT + (if guard then 1 else 0),
        firstInterp := t.firstInterp <|> interp,
        firstGen := t.firstGen <|> gen }
  let t1 ← IO.monoMsNow
  let mut calls := 0
  let mut ie := 0
  let mut ge := 0
  let mut gt := 0
  IO.println s!"MEASURE {path}: {lines} recorded calls, {order.size} arm functions, {t1 - t0} ms"
  for fn in order.qsort (· < ·) do
    let t := (tallies.get? fn).getD {}
    calls := calls + t.calls
    ie := ie + t.interpEq
    ge := ge + t.genEq
    gt := gt + t.guardT
    IO.println s!"  {fn}: calls {t.calls} interp= {t.interpEq} generated= {t.genEq} guard-true {t.guardT}"
    if let some d := t.firstInterp then IO.println s!"    interp differs: {d}"
    if let some d := t.firstGen then IO.println s!"    generated differs: {d}"
  IO.println s!"MEASURE TOTAL calls {calls} interp-equal {ie} generated-equal {ge} guard-true {gt}"
  return (if ie == calls && ge == calls then 0 else 1)

end Fn2.Measure

def main (args : List String) : IO UInt32 := Fn2.Measure.main args
