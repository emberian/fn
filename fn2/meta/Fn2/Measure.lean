import Fn2.ACL2.Read
import Fn2.Arms
import Fn2.Pathway
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
  bounds) on the recorded arguments, which ACL2's guard-verified caller established;
* **frame**: a child-form function takes and returns only the children its paths touch
  (`fn2-arms-child-sigs`); the interpreter runs on the kind's whole tuple, so every child the
  function does not return must leave the interpreter as it entered. A child the function takes
  enters with its recorded value; a child it does not take enters as a sentinel symbol no
  operation accepts, so a declaration that reads or writes it differs (in the results or here).

The interpreter's arguments and result go through `Fn2.Pathway`'s `widen` and `project`, the maps
PW3 is stated with, so each recorded call is one instance of `Fn2.Pathway.ArmCorrect`.

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
  frameOk : Nat := 0
  firstFrame : Option String := none
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
  -- the reader over every expression of every child-form kind, exercised or not
  let mut exprs := 0
  let mut refusals : Array String := #[]
  for k in w.kinds do
    if !k.childForm then continue
    for a in k.subarms ++ k.arms ++ k.observes do
      exprs := exprs + ((a.onRefusal ++ a.steps).flatMap Step.exprs).length
    refusals := refusals ++ (readKind w k).toArray
  IO.println s!"READ {exprs} expressions of the child-form kinds, {refusals.size} refused"
  for r in refusals do IO.println s!"  refused: {r}"
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
    let nOuts := Fn2.Pathway.nOuts observe
    let nPre := Fn2.Pathway.nPre observe
    -- a narrowed function takes and returns a subset of the kind's tuple (Fn2.Arms.Sig)
    let takes := Fn2.Pathway.takes k a
    let returns := Fn2.Pathway.returns k a
    let sentinel (c : String) : Val := .sym s!"FN2-META-UNTAKEN-{c}"
    let entering := Fn2.Pathway.entering k a (argv.drop nPre) sentinel
    let full := Fn2.Pathway.widen k a (argv.take nPre) (argv.drop nPre) sentinel
    let project := Fn2.Pathway.project k a observe
    let names := (if observe then ["wake"] else ["bytes", "steps", "descriptors", "runnable"]) ++ returns
    let ran := runArm w k a observe full
    let interp := match ran with
      | .ok v => let p := project v; if same p want then none else some (diff names p want)
      | .error e => some s!"error: {e}"
    -- the frame: every child outside the function's returns leaves as it entered
    let frame : Option String := match ran with
      | .ok v =>
        let outs := ((listOf v).toList.drop nOuts)
        let bad := (k.tuple.zip (entering.zip outs)).filter fun (c, i, o) =>
          !(returns.contains c) && !(same i o)
        match bad.head? with
        | none => none
        | some (c, i, o) =>
          some s!"{c} (not returned{if takes.contains c then "" else ", not taken"}) changed: {(toString o).take 120} (entered {(toString i).take 60})"
      | .error e => some s!"error: {e}"
    let gen := match w.fns fn argv with
      | some v => let p := Fn2.Pathway.normalize k a observe v
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
        frameOk := t.frameOk + (if frame.isNone then 1 else 0),
        firstFrame := t.firstFrame <|> frame,
        firstInterp := t.firstInterp <|> interp,
        firstGen := t.firstGen <|> gen }
  let t1 ← IO.monoMsNow
  let mut calls := 0
  let mut ie := 0
  let mut ge := 0
  let mut gt := 0
  let mut fo := 0
  IO.println s!"MEASURE {path}: {lines} recorded calls, {order.size} arm functions, {t1 - t0} ms"
  for fn in order.qsort (· < ·) do
    let t := (tallies.get? fn).getD {}
    calls := calls + t.calls
    ie := ie + t.interpEq
    ge := ge + t.genEq
    gt := gt + t.guardT
    fo := fo + t.frameOk
    IO.println s!"  {fn}: calls {t.calls} interp= {t.interpEq} generated= {t.genEq} guard-true {t.guardT} frame-kept {t.frameOk}"
    if let some d := t.firstInterp then IO.println s!"    interp differs: {d}"
    if let some d := t.firstGen then IO.println s!"    generated differs: {d}"
    if let some d := t.firstFrame then IO.println s!"    frame differs: {d}"
  IO.println s!"MEASURE TOTAL calls {calls} interp-equal {ie} generated-equal {ge} guard-true {gt} frame-kept {fo}"
  return (if ie == calls && ge == calls && gt == calls && fo == calls && refusals.isEmpty then 0 else 1)

end Fn2.Measure

def main (args : List String) : IO UInt32 := Fn2.Measure.main args
