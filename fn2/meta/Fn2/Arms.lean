import Fn2.ACL2.Val

/-!
# Fn2.Arms: the step language of `defmachine`, and its definitional interpreter

MACHINE-FORM §6.2's step language as a Lean inductive, and a definitional interpreter for it in
**child form** (§6.5 P3): an arm runs over its kind's table and the core children its operations
take, never `fn2-core`. The interpreter's state is the tuple of children (each a `Val`, the
stobj's logical value); its result is the arm function's `mv` list, `(bytes steps descriptors
runnable . tuple)` for a run arm and `(wake . tuple)` for a handler, so it compares directly with
what ACL2 returns.

What is ACL2's and what is this file's:
* every expression is a **translated ACL2 term** (`Fn2.ACL2.Term`), produced by ACL2 itself from
  the declaration (the generator's expression rewrite `fn2-arms-expr`, then `translate`), and every
  operation an arm calls is a translated ACL2 function (the generated `Fn2.Instances.*World`);
* the **control** of the step language (the order of writes, the checked batch write, answer
  routing, the issue's three outcomes, the terminals, sub-arms and loops) is this file's, written
  from MACHINE-FORM §6.2-6.10 and the generator `machine-arms.lisp`, and is the subject the
  measure tests: equal results against ACL2's own generated arm functions on the simulator's
  recorded calls, or a named difference.

The interpreter is total (fuel): `run` decreases its fuel on every step, sub-arm and loop pass,
and fuel exhaustion is an error, never a value.
-/

namespace Fn2.Arms
open Fn2.ACL2

/-- A call of a declared operation: positional arguments, then `:FORMAL E` keywords. -/
structure Call where
  op : String
  args : List Term
  keys : List (String × Term)
  deriving Inhabited, Repr

/-- MACHINE-FORM §6.2: everything an arm may say. A `:case` arm whose codes are `none` is the
`:otherwise` arm. -/
inductive Step where
  | let_ (v : String) (e : Term)
  | set (pairs : List (String × Term))
  | next (phase : Term)
  | do_ (vars : List String) (call : Call) (acceptGiven : Bool) (accept : List Val)
        (when_ : Option Term) (else_ : List Term) (cases : List (Option (List Val) × List Step))
  | issue (call : Call) (ok refused : List Step)
  | repeat_ (n : Term) (body : List Step) (until_ : Term)
  | wakeRow (e : Term)
  | if_ (c : Term) (a b : List Step)
  | cond (clauses : List (Term × List Step))
  | case_ (key : Term) (arms : List (Option (List Val) × List Step))
  | charge (bytes steps descriptors runnable : Option Term)
  | wait (bytes steps : Option Term)
  | park (wait : String) (arg : Option Term) (kind : Option String) (steps : Option Term)
  | stop (reason : String) (steps : Option Term)
  | halt | idle | yield | wake | nowake
  | goto (name : String)
  /-- the end of a `:repeat` pass (the generator's `:repeat-next`); never written by a kind -/
  | repeatNext
  deriving Inhabited, Repr

/-- What the generator narrowed a child-form function to (machine-arms.lisp, `fn2-arms-child-sigs`):
the children it takes (after its value formals), the children it returns (after its `results`
values). A function with one result in all returns it bare, not as an `mv` list. -/
structure Sig where
  takes : List String
  returns : List String
  results : Nat
  deriving Inhabited, Repr

/-- One arm, handler or sub-arm, with the name of the child-form function ACL2 generated for it
and, when the generator narrowed it, its signature. -/
structure Arm where
  tag : String
  sig : Option Sig
  from_ : List String
  onRefusal : List Step
  steps : List Step
  fn : String
  deriving Inhabited, Repr

/-- A column's carrier, for the checked write: an unsigned width, or an enum's tag count. -/
inductive ColType
  | uw (width : Nat)
  | enum (count : Nat)
  deriving DecidableEq, Inhabited, Repr

def ColType.fits : ColType → Val → Bool
  | .uw w, .int i => 0 ≤ i && i < 2 ^ w
  | .enum n, .int i => 0 ≤ i && i < n
  | _, _ => false

/-- A kind declared in the step language. `childForm` is false for a kind whose arms the world
defines only over `fn2-core` (the listener, whose registry arms wait behind P4): its arms are
printed as terms and refused by the interpreter by name. -/
structure Kind where
  name : String
  childForm : Bool
  tuple : List String
  states : List String
  columns : List (String × ColType)
  table : List String
  stops : List String
  subarms : List Arm
  arms : List Arm
  observes : List Arm
  deriving Inhabited, Repr

inductive Answers
  | none
  | open_
  | list (codes : List Val)
  deriving Inhabited, Repr

structure Op where
  name : String
  callee : Option String
  formals : List String
  stobjsIn : List (Option String)
  stobjsOut : List (Option String)
  answers : Answers
  deriving Inhabited, Repr

structure Wait where
  kind : String
  park : Option String
  deriving Inhabited, Repr

/-- Everything the interpreter reads: the kinds and operations ACL2 printed, its constants, and
the translated functions. -/
structure World where
  kinds : List Kind
  ops : List Op
  waits : List Wait
  consts : List (String × Int)
  fns : Fns

/-- The row-control fields that live in the directory `fn2-machines` (P1). -/
def directoryFields : List String := ["READY-PREV", "READY-NEXT", "WAIT-REASON"]

/-- The interpreter's state on one path. -/
structure St where
  stobjs : List (String × Val)
  vars : Env
  pending : List (String × Val) := []
  next : Option Val := none
  nextDone : Bool := false
  woken : Bool := false

/-- A path's end: a result (the arm function's `mv` list) or the end of a `:repeat` pass. -/
inductive Res
  | done (v : Val)
  | again (st : St)

/-- What is fixed while one arm function runs. -/
structure Frame where
  kind : Kind
  observe : Bool
  refusal : List Step
  base : Env

section
variable (w : World)

def const (n : String) : Except String Val :=
  match w.consts.find? (·.1 == n) with
  | some (_, v) => .ok (.int v)
  | none => .error s!"no constant {n}"

def callFn (f : String) (args : List Val) : Except String Val :=
  match nativeCall f args with
  | some v => .ok v
  | none => match w.fns f args with
    | some v => .ok v
    | none => .error s!"no function {f}/{args.length}"

def ev (st : St) (t : Term) : Except String Val := t.eval w.fns (st.vars ++ st.stobjs)

def evOpt (st : St) (t : Option Term) (dflt : Val) : Except String Val :=
  match t with
  | some t => ev w st t
  | none => .ok dflt

def stobj (st : St) (n : String) : Except String Val :=
  match st.stobjs.find? (·.1 == n) with
  | some (_, v) => .ok v
  | none => .error s!"no child {n} in the arm's tuple"

def setStobj (st : St) (n : String) (v : Val) : St :=
  { st with stobjs := st.stobjs.map fun p => if p.1 == n then (n, v) else p }

def var (st : St) (n : String) : Except String Val :=
  match st.vars.get? n with
  | some v => .ok v
  | none => .error s!"unbound {n}"

/-- The row as the arm sees it at entry: `ROW-F` for every column, read from the kind's table by
slot or from the directory by id. -/
def rowReads (k : Kind) (stobjs : List (String × Val)) (id slot : Val) : Except String Env := do
  let table ← match stobjs.find? (·.1 == k.name) with
    | some (_, v) => pure v
    | none => throw "no table"
  let dir ← match stobjs.find? (·.1 == "FN2-MACHINES") with
    | some (_, v) => pure v
    | none => throw "no directory"
  k.columns.mapM fun (c, _) => do
    let v ← if directoryFields.contains c then callFn w ("FN2-MACHINES-" ++ c) [id, dir]
            else callFn w (k.name ++ "-" ++ c) [slot, table]
    pure ("ROW-" ++ c, v)

/-- `K-PUT-CHILDREN`: one checked write of the pending fields (and the phase), the kind's table by
slot and the directory by id; a slot outside the table, an id outside the directory (when a
directory field is written) or a value wider than its column stops the core with
`:machine-write` and writes nothing. -/
def put (f : Frame) (st : St) (pairs : List (String × Val)) : Except String St := do
  let k := f.kind
  let slot ← var st "SLOT"
  let id ← var st "ID"
  let table ← stobj st k.name
  let dir ← stobj st "FN2-MACHINES"
  let control ← stobj st "FN2-CONTROL"
  let own := pairs.filter fun p => !directoryFields.contains p.1
  let dirp := pairs.filter fun p => directoryFields.contains p.1
  let rows ← callFn w (k.name ++ "-ROWS") [table]
  let drows ← callFn w "FN2-MACHINES-ROWS" [dir]
  let natLt (a b : Val) : Bool := match a, b with
    | .int x, .int y => 0 ≤ x && x < y
    | _, _ => false
  let fits := pairs.all fun (n, v) => match k.columns.find? (·.1 == n) with
    | some (_, ty) => ty.fits v
    | none => false
  if natLt slot rows && (dirp.isEmpty || natLt id drows) && fits then
    let table ← own.foldlM (fun t (n, v) => callFn w (k.name ++ "-SET-" ++ n) [slot, v, t]) table
    let dir ← dirp.foldlM (fun d (n, v) => callFn w ("FN2-MACHINES-SET-" ++ n) [id, v, d]) dir
    pure (setStobj (setStobj st k.name table) "FN2-MACHINES" dir)
  else
    let r ← const w "*FN2-STOP-REASON-MACHINE-WRITE*"
    let control ← callFn w "FN2-CONTROL-RECORD-STOP" [r, control]
    pure (setStobj st "FN2-CONTROL" control)

/-- Write the pending fields and the path's phase before an operation call or a terminal. -/
def flush (f : Frame) (st : St) : Except String St := do
  let pairs := st.pending ++ (match st.next with | some n => [("PHASE", n)] | none => [])
  let st' ← if pairs.isEmpty then pure st else put w f st pairs
  pure { st' with pending := [], next := none, nextDone := st.nextDone || st.next.isSome }

def pend (st : St) (pairs : List (String × Val)) : Except String St :=
  if pairs.any (fun p => st.pending.any (·.1 == p.1)) then
    .error s!"a field is written twice before the next operation"
  else .ok { st with pending := st.pending ++ pairs }

/-- The actuals of a call: positional arguments fill the leading value formals, the stobj formals
take the tuple's children, the owner triple `okind oslot ogen` comes from the row (`KIND`, `ID`,
`ROW-GENERATION`), and any other formal is a `:FORMAL E` keyword. -/
def actuals (st : St) (formals : List String) (stobjsIn : List (Option String))
    (pos : List Term) (keys : List (String × Term)) : Except String (List Val) :=
  match formals, stobjsIn with
  | [], _ => if pos.isEmpty then .ok [] else .error "too many arguments"
  | _ :: fs, some s :: ss => do
    let v ← stobj st s
    let rest ← actuals st fs ss pos keys
    pure (v :: rest)
  | fm :: fs, _ :: ss => do
    match pos with
    | p :: ps =>
      let v ← ev w st p
      let rest ← actuals st fs ss ps keys
      pure (v :: rest)
    | [] =>
      let v ← match keys.find? (·.1 == ":" ++ fm) with
        | some (_, e) => ev w st e
        | none =>
          if fm == "OKIND" then var st "KIND"
          else if fm == "OSLOT" then var st "ID"
          else if fm == "OGEN" then var st "ROW-GENERATION"
          else throw s!"no argument for the formal {fm}"
      let rest ← actuals st fs ss [] keys
      pure (v :: rest)
  | _ :: _, [] => .error "stobjs-in shorter than formals"

/-- Bind a call's results: stobj outputs replace the tuple's children, the others bind `vars`. -/
def bindOuts (st : St) (outs : List (Option String)) (vars : List String) (res : Val) :
    Except String St :=
  match outs with
  | [some s] => .ok (setStobj st s res)
  | [none] => match vars with
    | v :: _ => .ok { st with vars := (v, res) :: st.vars }
    | [] => .ok st
  | _ =>
    let rec go (st : St) : List (Option String) → List String → List Val → Except String St
      | [], _, _ => .ok st
      | some s :: os, vs, r :: rs => go (setStobj st s r) os vs rs
      | none :: os, v :: vs, r :: rs => go { st with vars := (v, r) :: st.vars } os vs rs
      | none :: os, [], _ :: rs => go st os [] rs
      | _, _, [] => .error "fewer results than outputs"
    go st outs vars res.toList

def findOp (n : String) : Except String Op :=
  match w.ops.find? (·.name == n) with
  | some o => .ok o
  | none => .error s!"no declared operation {n}"

/-- Call a declared operation through its `:child`, returning the raw result. -/
def callOp (st : St) (c : Call) : Except String (Op × Val) := do
  let op ← findOp w c.op
  let callee ← match op.callee with
    | some f => pure f
    | none => throw s!"{c.op} names no :child (not in child form)"
  let args ← actuals w st op.formals op.stobjsIn c.args c.keys
  let r ← callFn w callee args
  pure (op, r)

def tupleVals (f : Frame) (st : St) : Except String (List Val) :=
  f.kind.tuple.mapM (stobj st)

def chargeResult (f : Frame) (st : St) (b s d r : Val) : Except String Res := do
  let t ← tupleVals f st
  pure (.done (Val.ofList ([b, s, d, r] ++ t)))

def wakeResult (f : Frame) (st : St) (v : Val) : Except String Res := do
  let t ← tupleVals f st
  pure (.done (Val.ofList (v :: t)))

/-- A stop's ending: a handler answers no wake; a run arm charges the stop's steps. -/
def stopEnd (f : Frame) (st : St) (steps : Option Term) : Except String Res := do
  if f.observe then wakeResult f st (← const w "*FN2-NONE*")
  else chargeResult f st (.int 0) (← evOpt w st steps (← const w "*FN2-WORK-EMPTY*")) (.int 0) Val.nil

def codeIn (code : Val) (codes : List Val) : Bool := codes.contains code

/-- The interpreter: run a path's steps to its terminal. -/
def run (f : Frame) : Nat → St → List Step → Except String Res
  | 0, _, _ => .error "fuel"
  | _ + 1, _, [] => .error "a path ends without a terminal"
  | fuel + 1, st, s :: rest =>
    match s with
    | .let_ v e => do
      let x ← ev w st e
      run f fuel { st with vars := (v, x) :: st.vars } rest
    | .set pairs => do
      let vs ← pairs.mapM fun (n, e) => do pure (n, ← ev w st e)
      run f fuel (← pend st vs) rest
    | .next ph => do
      if st.next.isSome || st.nextDone then throw "a path has two :next steps"
      let p ← ev w st ph
      run f fuel { st with next := some p } rest
    | .do_ vars c acceptGiven accept when_ else_ cases => do
      let st ← flush w f st
      let op ← findOp w c.op
      let skip ← match when_ with
        | some e => do pure !(← ev w st e).truthy
        | none => pure false
      let st ← if skip then do
          let vs ← else_.mapM (ev w st)
          pure { st with vars := vars.zip vs ++ st.vars }
        else do
          let (_, r) ← callOp w st c
          bindOuts st op.stobjsOut vars r
      match op.answers with
      | .none => run f fuel st rest
      | answers => do
        let code ← match vars with
          | v :: _ => var st v
          | [] => throw ":do of an operation with answers binds no code"
        let caseCodes := cases.flatMap fun (cs, _) => cs.getD []
        let ok := Val.kw "OK"
        let acc := if acceptGiven then accept
          else match answers with
            | .list l => if caseCodes.contains ok || !l.contains ok then [] else [ok]
            | _ => if caseCodes.contains ok then [] else [ok]
        if codeIn code acc then run f fuel st rest
        else match cases.find? (fun (cs, _) => match cs with
            | some l => codeIn code l
            | none => false) with
          | some (_, steps) => run f fuel st steps
          | none => match cases.find? (·.1.isNone) with
            | some (_, steps) => run f fuel st steps
            | none =>
              if !f.refusal.isEmpty then run f fuel st f.refusal
              else run f fuel st [.stop "MACHINE-CONTRACT" none]
    | .issue c ok refused => do
      let st ← flush w f st
      let (op, r) ← callOp w st c
      let st ← bindOuts st op.stobjsOut ["FN2-ISSUE-CODE", "FN2-ISSUE-OP", "FN2-ISSUE-OPGEN"] r
      let code ← var st "FN2-ISSUE-CODE"
      if code == Val.kw "OK" then run f fuel st ok
      else if code == Val.kw "EXHAUSTED" then
        run f fuel st (refused ++ [.park "OPERATION" none none none])
      else run f fuel st (refused ++ (if f.refusal.isEmpty then [.halt] else f.refusal))
    | .repeat_ n body until_ => do
      let st ← flush w f st
      let k := (← ev w st n).nfix
      let rec loop : Nat → Nat → St → Except String St
        | 0, _, st => .ok st
        | _, 0, st => .ok st
        | fuel' + 1, k + 1, st => do
          let id ← var st "ID"
          let slot ← var st "SLOT"
          let reads ← rowReads w f.kind st.stobjs id slot
          let pass : St := { stobjs := st.stobjs, vars := reads ++ f.base }
          if (← ev w pass until_).truthy then pure st
          else match ← run f fuel' pass (body ++ [.repeatNext]) with
            | .again st' => loop fuel' k { st with stobjs := st'.stobjs }
            | .done _ => throw "a :repeat pass ended in a terminal"
      let st' ← loop fuel k st
      run f fuel { st with stobjs := st'.stobjs, pending := [] } rest
    | .repeatNext => do
      let st ← flush w f st
      pure (.again st)
    | .wakeRow e => do
      if st.woken then throw "a path wakes at most one row"
      let v ← ev w st e
      let r ← callFn w "FN2-MACHINES-WAKE-ROW" [v, ← stobj st "FN2-MACHINES", ← stobj st "FN2-CONTROL"]
      let st := setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car
      run f fuel { st with woken := true } rest
    | .if_ c a b => do
      if (← ev w st c).truthy then run f fuel st a else run f fuel st b
    | .cond clauses => do
      match ← clauses.findM? (fun (c, _) => do pure (← ev w st c).truthy) with
      | some (_, steps) => run f fuel st steps
      | none => throw ":cond without a true clause"
    | .case_ key arms => do
      let kv ← ev w st key
      match arms.find? (fun (cs, _) => match cs with
          | some l => codeIn kv l
          | none => true) with
      | some (_, steps) => run f fuel st steps
      | none => throw ":case without :otherwise"
    | .charge b s d r => do
      let st ← flush w f st
      chargeResult f st (← evOpt w st b (.int 0)) (← evOpt w st s (.int 0))
        (← evOpt w st d (.int 0)) (← evOpt w st r Val.nil)
    | .idle => do
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-EMPTY*") (.int 0) Val.nil
    | .yield => do
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-EMPTY*") (.int 0) Val.t
    | .wait b s => do
      let st ← pend st [("PENDING", .int 1), ("WAIT-REASON", ← const w "*FN2-WAIT-COMPLETION*")]
      let st ← flush w f st
      chargeResult f st (← evOpt w st b (.int 0)) (← evOpt w st s (← const w "*FN2-WORK-MAILBOX*"))
        (.int 1) Val.nil
    | .halt => do
      let st ← pend st [("STOPPED", .int 1), ("WAIT-REASON", ← const w "*FN2-WAIT-NONE*")]
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-MAILBOX*") (.int 0) Val.nil
    | .park wait arg kind steps => do
      let mailbox ← const w "*FN2-WORK-MAILBOX*"
      let viaOp (st : St) (op : String) (args : List Term) : Except String Res := do
        let st ← flush w f st
        let (o, r) ← callOp w st ⟨op, args, []⟩
        let st ← bindOuts st o.stobjsOut [] r
        chargeResult f st (.int 0) (← evOpt w st steps mailbox) (.int 0) Val.nil
      match wait with
      | "OPERATION" => viaOp st "FN2-MACHINE-PARK" [.var "ID"]
      | "ADMISSION" => viaOp st "FN2-MACHINE-PARK-ADMISSION" ([.var "ID"] ++ arg.toList)
      | "TAKEN" => viaOp st ("FN2-MACHINE-PARK-TAKEN-" ++ kind.getD "") [.var "ID"]
      | "POOL" => do
        let cls ← match arg with
          | some a => ev w st a
          | none => throw "(:park :pool) without a class"
        let st ← pend st [("CURSOR", cls)]
        let st ← flush w f st
        let r ← callFn w "FN2-MACHINES-PARK-POOL"
          [← var st "ID", ← stobj st "FN2-MACHINES", ← stobj st "FN2-CONTROL"]
        let st := setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car
        chargeResult f st (.int 0) (← evOpt w st steps mailbox) (.int 0) Val.nil
      | other => match w.waits.find? (·.kind == other) with
        | some ⟨_, some parker⟩ => viaOp st parker [.var "ID"]
        | some ⟨_, none⟩ => do
          let st ← pend st [("WAIT-REASON", ← const w ("*FN2-WAIT-" ++ other ++ "*"))]
          let st ← flush w f st
          chargeResult f st (.int 0) (← evOpt w st steps mailbox) (.int 0) Val.nil
        | none => throw s!"(:park :{other}) names no declared wait kind"
    | .stop reason steps => do
      if st.next.isSome then throw "a stop follows a :next"
      let st ← flush w f st
      let control ← stobj st "FN2-CONTROL"
      let control ← match f.kind.stops.idxOf? reason with
        | some i => callFn w "FN2-CONTROL-RECORD-KIND-STOP" [← var st "KIND", .int i, control]
        | none => do
          callFn w "FN2-CONTROL-RECORD-STOP" [← const w ("*FN2-STOP-REASON-" ++ reason ++ "*"), control]
      stopEnd w f (setStobj st "FN2-CONTROL" control) steps
    | .wake => do
      let st ← flush w f st
      wakeResult f st (← var st "ID")
    | .nowake => do
      let st ← flush w f st
      wakeResult f st (← const w "*FN2-NONE*")
    | .goto name => do
      let st ← flush w f st
      let sub ← match f.kind.subarms.find? (·.tag == name) with
        | some a => pure a
        | none => throw s!"no sub-arm {name}"
      let reads ← rowReads w f.kind st.stobjs (← var st "ID") (← var st "SLOT")
      run { f with refusal := sub.onRefusal } fuel
        { stobjs := st.stobjs, vars := reads ++ f.base } sub.steps

/-- Run one arm (or handler) of `k` on the arguments of its child-form function, in that
function's formal order: `(id slot kind ordinal budget . tuple)` for an arm, `(id slot kind
ordinal event outcome reason count aux0 aux1 . tuple)` for a handler. The value is the function's
`mv` list. -/
def runArm (k : Kind) (a : Arm) (observe : Bool) (args : List Val) (fuel : Nat := 100000) :
    Except String Val := do
  if !k.childForm then
    throw s!"{k.name} is in core form (its arms take fn2-core); the interpreter runs child form only"
  let names := if observe then ["ID", "SLOT", "KIND", "ORDINAL", "EVENT", "OUTCOME", "REASON",
      "COUNT", "AUX0", "AUX1"] else ["ID", "SLOT", "KIND", "ORDINAL", "BUDGET"]
  if args.length != names.length + k.tuple.length then
    throw s!"{a.fn}: {args.length} arguments for {names.length + k.tuple.length} formals"
  let base := names.zip (args.take names.length)
  let stobjs := k.tuple.zip (args.drop names.length)
  let id := args.headD Val.nil
  let slot := (args.drop 1).headD Val.nil
  let reads ← rowReads w k stobjs id slot
  let f : Frame := { kind := k, observe, refusal := a.onRefusal, base }
  match ← run w f fuel { stobjs, vars := reads ++ base } a.steps with
  | .done v => pure v
  | .again _ => throw ":repeat-next outside a :repeat"

end

end Fn2.Arms
