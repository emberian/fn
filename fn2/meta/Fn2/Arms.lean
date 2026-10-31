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
* every expression is **the declaration's own S-expression** (`Expr`, as written in `defmachine`),
  read into an ACL2 term by this file's reader (`readExpr`), written from ACL2's definitions of the
  arm vocabulary's macros and MACHINE-FORM §6.3, independently of the generator's rewrite
  (`fn2-arms-expr`, then `translate`), so a defect in that rewrite is not shared (LEAN-METATHEORY
  §12, decision 7); every function an expression or arm calls is a translated ACL2 function (the
  generated `Fn2.Instances.*World`);
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

/-- An expression of the step language as the declaration writes it (an ACL2 S-expression),
read by `readExpr` when the arm runs. -/
abbrev Expr := Val

/-- `(QUOTE v)`, for the expressions the interpreter writes itself. -/
def Expr.q (v : Val) : Expr := Val.ofList [.sym "QUOTE", v]

/-- A call of a declared operation: positional arguments, then `:FORMAL E` keywords. -/
structure Call where
  op : String
  args : List Expr
  keys : List (String × Expr)
  deriving Inhabited, Repr

/-- MACHINE-FORM §6.2: everything an arm may say. A `:case` arm whose codes are `none` is the
`:otherwise` arm. -/
inductive Step where
  | let_ (v : String) (e : Expr)
  | set (pairs : List (String × Expr))
  /-- a phase form: a phase keyword, `(:if E N N)` or `(:case V ((CODE ...) N) ... (:otherwise N))` -/
  | next (phase : Expr)
  | do_ (vars : List String) (call : Call) (acceptGiven : Bool) (accept : List Val)
        (when_ : Option Expr) (else_ : List Expr) (cases : List (Option (List Val) × List Step))
  | issue (call : Call) (ok refused : List Step)
  | repeat_ (n : Expr) (body : List Step) (until_ : Expr)
  | wakeRow (e : Expr)
  | if_ (c : Expr) (a b : List Step)
  | cond (clauses : List (Expr × List Step))
  | case_ (key : Expr) (arms : List (Option (List Val) × List Step))
  | charge (bytes steps descriptors runnable : Option Expr)
  | wait (bytes steps : Option Expr)
  | park (wait : String) (arg : Option Expr) (kind : Option String) (steps : Option Expr)
  | stop (reason : String) (steps : Option Expr)
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

/-- One arm, handler or sub-arm: its declaration as the kind writes it (`decl`, the entry after
its tag: `:from`, `:on-refusal`, then the steps), the name of the child-form function ACL2
generated for it and, when the generator narrowed it, its signature. -/
structure Arm where
  tag : String
  sig : Option Sig
  decl : Val
  fn : String
  deriving Inhabited, Repr

/-- A true list (no dotted tail). -/
def _root_.Fn2.ACL2.Val.properList : Val → Bool
  | .cons _ d => d.properList
  | v => v == Val.nil

/-- ACL2's `eqlablep` on the subset: an integer, a symbol or a character. -/
def _root_.Fn2.ACL2.Val.eqlable : Val → Bool
  | .int _ | .sym _ | .chr _ => true
  | _ => false

/-! ### The step reader

`readSteps` reads an arm's steps from the declaration's S-expression, as MACHINE-FORM §6.2 writes
them, so the printer's and the emitter's decoders are not on the interpreter's path (Astra session
5: the declaration decoding was the part still shared after decision 7). -/

/-- A plist's value for `key` (`(K1 V1 K2 V2 ...)`), as the generator's `fn2-arm-get`. -/
def plistGet (key : String) : List Val → Option Val
  | .sym k :: v :: rest => if k == key then some v else plistGet key rest
  | _ :: _ :: rest => plistGet key rest
  | _ => none

def plistHas (key : String) : List Val → Bool
  | .sym k :: _ :: rest => k == key || plistHas key rest
  | _ :: _ :: rest => plistHas key rest
  | _ => false

def symName : Val → Except String String
  | .sym n => .ok n
  | v => .error s!"expected a symbol, got {v.render}"

/-- A call `(OP a ... :FORMAL e ...)`: positional arguments until the first keyword. -/
def readCall (c : Val) : Except String Call := do
  let xs := c.toList
  let op ← symName (xs.headD Val.nil)
  let args := xs.tail
  let isKw (v : Val) : Bool := match v with | .sym n => n.startsWith ":" | _ => false
  let pos := args.takeWhile (!isKw ·)
  let rec pairs : List Val → Except String (List (String × Expr))
    | [] => pure []
    | .sym k :: v :: rest => do pure ((k, v) :: (← pairs rest))
    | xs => throw s!"a call's keyword arguments are pairs: {(Val.ofList xs).render}"
  pure ⟨op, pos, ← pairs (args.drop pos.length)⟩

def readCodes (cs : Val) : Option (List Val) :=
  if cs == .sym ":OTHERWISE" then none else some cs.toList

def stepOpt (key : String) (pl : List Val) : Option Expr := plistGet key pl

partial def readSteps (ss : Val) : Except String (List Step) := do
  if !ss.properList then throw s!"steps with a dotted tail: {ss.render}"
  ss.toList.mapM readStep
where
  readStep (s : Val) : Except String Step := do
    if !s.properList then throw s!"a step with a dotted tail: {s.render}"
    let xs := s.toList
    let h ← symName (xs.headD Val.nil)
    let a := xs.tail
    let one : Except String Val := match a with
      | [x] => pure x
      | _ => throw s!"{h} takes one argument: {s.render}"
    match h with
    | ":LET" => match a with
      | [.sym v, e] => pure (.let_ v e)
      | _ => throw s!"(:let VAR E): {s.render}"
    | ":SET" => do
      let ps ← a.mapM fun p => match p.toList with
        | [.sym f, e] => pure (f, e)
        | _ => throw s!"(:set (FIELD E) ...): {s.render}"
      pure (.set ps)
    | ":NEXT" => do pure (.next (← one))
    | ":DO" => match a with
      | vars :: call :: opts => do
        let vs ← vars.toList.mapM symName
        let c ← readCall call
        let when_ := match plistGet ":WHEN" opts with
          | some w => if w == Val.nil then none else some w
          | none => none
        let cases ← ((plistGet ":CASE" opts).getD Val.nil).toList.mapM fun c => do
          pure (readCodes c.car, ← readSteps c.cdr)
        pure (.do_ vs c (plistHas ":ACCEPT" opts) ((plistGet ":ACCEPT" opts).getD Val.nil).toList
          when_ ((plistGet ":ELSE" opts).getD Val.nil).toList cases)
      | _ => throw s!"(:do VARS CALL ...): {s.render}"
    | ":ISSUE" => match a with
      | call :: opts => do
        pure (.issue (← readCall call) (← readSteps ((plistGet ":OK" opts).getD Val.nil))
          (← readSteps ((plistGet ":REFUSED" opts).getD Val.nil)))
      | _ => throw s!"(:issue CALL ...): {s.render}"
    | ":REPEAT" => match a with
      | n :: body :: opts => do
        let some u := plistGet ":UNTIL" opts | throw s!":repeat without :until: {s.render}"
        pure (.repeat_ n (← readSteps body) u)
      | _ => throw s!"(:repeat N STEPS :until E): {s.render}"
    | ":WAKE-ROW" => do pure (.wakeRow (← one))
    | ":IF" => match a with
      | [c, x, y] => do pure (.if_ c (← readSteps x) (← readSteps y))
      | _ => throw s!"(:if E STEPS STEPS): {s.render}"
    | ":COND" => do
      pure (.cond (← a.mapM fun c => do pure (c.car, ← readSteps c.cdr)))
    | ":CASE" => match a with
      | key :: arms => do
        pure (.case_ key (← arms.mapM fun c => do pure (readCodes c.car, ← readSteps c.cdr)))
      | _ => throw s!"(:case V ...): {s.render}"
    | ":CHARGE" => pure (.charge (stepOpt ":BYTES" a) (stepOpt ":STEPS" a)
        (stepOpt ":DESCRIPTORS" a) (stepOpt ":RUNNABLE" a))
    | ":WAIT" => match a with
      | .sym ":COMPLETION" :: pl => pure (.wait (stepOpt ":BYTES" pl) (stepOpt ":STEPS" pl))
      | _ => throw s!"(:wait :completion ...): {s.render}"
    | ":PARK" => match a with
      | .sym w :: rest =>
        let wait := (w.drop 1).toString
        if w == ":TAKEN" then match rest with
          | .sym kind :: pl => pure (.park wait none (some kind) (stepOpt ":STEPS" pl))
          | _ => throw s!"(:park :taken KIND ...): {s.render}"
        else if w == ":ADMISSION" || w == ":POOL" then match rest with
          | arg :: pl => pure (.park wait (some arg) none (stepOpt ":STEPS" pl))
          | _ => throw s!"(:park {w} ARG ...): {s.render}"
        else pure (.park wait none none (stepOpt ":STEPS" rest))
      | _ => throw s!"(:park WAIT ...): {s.render}"
    | ":STOP" => match a with
      | .sym r :: pl => pure (.stop (r.drop 1).toString (stepOpt ":STEPS" pl))
      | _ => throw s!"(:stop REASON ...): {s.render}"
    | ":HALT" => pure .halt
    | ":IDLE" => pure .idle
    | ":YIELD" => pure .yield
    | ":WAKE" => pure .wake
    | ":NOWAKE" => pure .nowake
    | ":GOTO" => do pure (.goto (← symName (← one)))
    | _ => throw s!"unknown step {s.render}"

/-- An arm's declaration read: `:from` and `:on-refusal` (in any order, as `fn2-arms-options`
reads them), then the steps. -/
structure ArmDecl where
  from_ : List String
  onRefusal : List Step
  steps : List Step

partial def Arm.read (a : Arm) : Except String ArmDecl := do
  let rec opts : Val → Except String (List String × Val × Val)
    | .cons (.sym ":FROM") (.cons f rest) => do
      let (_, r, ss) ← opts rest
      pure (← f.toList.mapM symName, r, ss)
    | .cons (.sym ":ON-REFUSAL") (.cons r rest) => do
      let (fr, _, ss) ← opts rest
      pure (fr, r, ss)
    | ss => pure ([], Val.nil, ss)
  let (fr, r, ss) ← opts a.decl
  pure ⟨fr, ← readSteps r, ← readSteps ss⟩

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
  /-- each phase's value, from the kind's state constants -/
  phases : List (String × Int)
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
  consts : List (String × Val)
  fns : Fns

/-- The row-control fields that live in the directory `fn2-machines` (P1). -/
def directoryFields : List String := ["READY-PREV", "READY-NEXT", "WAIT-REASON"]

/-- The interpreter's state on one path. -/
structure St where
  stobjs : List (String × Val)
  vars : Env
  /-- pending writes, as expressions: the generator evaluates them inside the checked write, at flush -/
  pending : List (String × Expr) := []
  /-- the path's phase form, read and evaluated at flush -/
  next : Option Expr := none
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
  | some (_, v) => .ok v
  | none => .error s!"no constant {n}"

def callFn (f : String) (args : List Val) : Except String Val :=
  match nativeCall f args with
  | some v => .ok v
  | none => match w.fns f args with
    | some v => .ok v
    | none => .error s!"no function {f}/{args.length}"

/-! ### The expression reader (decision 7)

`readExpr k x` reads a step-language expression of kind `k` into an ACL2 term, from ACL2's own
definitions of the vocabulary (`*fn2-arm-primitives*`, `*fn2-arm-control*`, `member-eq`; ACL2's
`axioms.lisp`) and MACHINE-FORM §6.3, never from the generator's output:
* a number, string, character, keyword, `T`, `NIL` or `(QUOTE v)` is itself;
* `ROW-SLOT` is the arm's `SLOT` formal; `*K-KIND*` and `*K-ADMISSION-ORDINAL*` are the `KIND` and
  `ORDINAL` formals (the child-form convention for index-time constants); another `*C*` is the
  constant's printed value; every other symbol is a variable (`ROW-F`, a formal, a `:let`);
* the macros as ACL2 defines them: `+ *` (right-associated; empty `0`/`1`, unary `(+ 0 x)`/
  `(* 1 x)`), `-` (one or two arguments), `1+ 1-`, `< <= > >=`, `= /= eq eql` (as `EQUAL`), `not
  null`, `and or`, `cond` (clauses of one or two forms), `case` (clauses `(keys form)`, keys
  eqlable atoms or lists of them, `otherwise`/`t` last, a `nil` key clause dropped unread, a
  compound key bound once), `logand logior` (empty `-1`/`0`, unary the argument, else
  right-associated), `mv` (two or more values, a list), `prog2$` (two forms, the second's value),
  `member-eq` (`MEMBER-EQUAL`);
* a function of the vocabulary (`vocabularyFns`, with its arity) is a call;
* `(OP a ...)` for a declared pure operation (its `:child` returns no child, its stobj formals
  trailing, as the generator appends them) is a call of the `:child` with the positional
  arguments and then the kind's children by name;
* anything else, an application with a dotted tail, or a wrong arity is refused by name. -/

/-- The functions of the arm vocabulary with their arities; the printer roots each in the closure. -/
def vocabularyFns : List (String × Nat) :=
  [("NFIX", 1), ("IFIX", 1), ("ZP", 1), ("ZIP", 1), ("NATP", 1), ("POSP", 1), ("INTEGERP", 1),
   ("UNSIGNED-BYTE-P", 2), ("FLOOR", 2), ("MOD", 2), ("ASH", 2), ("MIN", 2), ("MAX", 2),
   ("BINARY-+", 2), ("BINARY-*", 2), ("UNARY--", 1)]

private def tIf (c a b : Term) : Term := .app "IF" [c, a, b]
private def tNot (a : Term) : Term := tIf a (.quote Val.nil) (.quote Val.t)

/-- The free variables of a term (a closed `LAMBDA`'s are its actuals'). -/
partial def termFreeVars : Term → List String
  | .var x => [x]
  | .quote _ => []
  | .app _ as => as.flatMap termFreeVars
  | .lam _ _ as => as.flatMap termFreeVars

partial def readExpr (k : Kind) (x : Expr) : Except String Term := do
  let rd := readExpr k
  let rds (xs : List Val) : Except String (List Term) := xs.mapM rd
  let foldR (f : String) (xs : List Val) : Except String Term := do
    let ts ← rds xs
    pure ((ts.dropLast).foldr (fun a acc => .app f [a, acc]) ts.getLast!)
  let arity (f : String) (args : List Val) (n : Nat) : Except String Unit :=
    if args.length == n then pure () else throw s!"{f} takes {n} arguments: {x.render}"
  match x with
  | .int _ | .str _ | .chr _ => pure (.quote x)
  | .sym n =>
    if n == "T" || n == "NIL" || n.startsWith ":" then pure (.quote x)
    else if n == "ROW-SLOT" then pure (.var "SLOT")
    else if n == "*" ++ k.name ++ "-KIND*" then pure (.var "KIND")
    else if n == "*" ++ k.name ++ "-ADMISSION-ORDINAL*" then pure (.var "ORDINAL")
    else if n.length > 2 && n.startsWith "*" && n.endsWith "*" then
      match w.consts.find? (·.1 == n) with
      | some (_, v) => pure (.quote v)
      | none => throw s!"the constant {n} was not printed"
    else pure (.var n)
  | .cons (.sym f) rest =>
    if !rest.properList then throw s!"an application with a dotted tail: {x.render}"
    let args := rest.toList
    match f with
    | "QUOTE" => do arity f args 1; pure (.quote args.head!)
    | "IF" => do arity f args 3; pure (.app "IF" (← rds args))
    | "+" => match args with
      | [] => pure (.quote (.int 0))
      | [a] => do pure (.app "BINARY-+" [.quote (.int 0), ← rd a])
      | _ => foldR "BINARY-+" args
    | "*" => match args with
      | [] => pure (.quote (.int 1))
      | [a] => do pure (.app "BINARY-*" [.quote (.int 1), ← rd a])
      | _ => foldR "BINARY-*" args
    | "-" => match args with
      | [a] => do pure (.app "UNARY--" [← rd a])
      | [a, b] => do pure (.app "BINARY-+" [← rd a, .app "UNARY--" [← rd b]])
      | _ => throw s!"- takes one or two arguments: {x.render}"
    | "1+" => do arity f args 1; pure (.app "BINARY-+" [.quote (.int 1), ← rd args.head!])
    | "1-" => do arity f args 1; pure (.app "BINARY-+" [.quote (.int (-1)), ← rd args.head!])
    | "<" => do arity f args 2; pure (.app "<" (← rds args))
    | ">" => do arity f args 2; let ts ← rds args; pure (.app "<" [ts[1]!, ts[0]!])
    | "<=" => do arity f args 2; let ts ← rds args; pure (tNot (.app "<" [ts[1]!, ts[0]!]))
    | ">=" => do arity f args 2; let ts ← rds args; pure (tNot (.app "<" [ts[0]!, ts[1]!]))
    | "=" | "EQ" | "EQL" | "EQUAL" => do arity f args 2; pure (.app "EQUAL" (← rds args))
    | "/=" => do arity f args 2; pure (tNot (.app "EQUAL" (← rds args)))
    | "NOT" | "NULL" => do arity f args 1; pure (tNot (← rd args.head!))
    | "AND" => match args with
      | [] => pure (.quote Val.t)
      | _ => do
        let ts ← rds args
        pure ((ts.dropLast).foldr (fun a acc => tIf a acc (.quote Val.nil)) ts.getLast!)
    | "OR" => match args with
      | [] => pure (.quote Val.nil)
      | _ => do
        let ts ← rds args
        pure ((ts.dropLast).foldr (fun a acc => tIf a a acc) ts.getLast!)
    | "COND" => do
      let cls ← args.mapM fun c =>
        if !c.properList then throw s!"a cond clause with a dotted tail: {c.render}"
        else match c.toList with
        | [t] => do let tt ← rd t; pure (tt, tt)
        | [t, e] => do pure (← rd t, ← rd e)
        | _ => throw s!"a cond clause has one or two forms: {c.render}"
      pure (cls.foldr (fun (t, e) acc => tIf t e acc) (.quote Val.nil))
    | "CASE" => do
      let some keyX := args.head? | throw s!"case without a key: {x.render}"
      let keyT ← rd keyX
      -- a compound key is bound once, as ACL2's case binds it
      let bound := !keyX matches .sym _
      let key : Term := if bound then .var "CASE-DO-NOT-USE-ELSEWHERE" else keyT
      let rec go : List Val → Except String Term
        | [] => pure (.quote Val.nil)
        | a :: more => do
          if !a.properList || a.toList.length != 2 then
            throw s!"a case clause is (keys form): {a.render}"
          let keys := a.car
          if keys == .sym "OTHERWISE" || keys == Val.t then
            if more.isEmpty then rd a.cdr.car else throw s!"otherwise is not last: {x.render}"
          else if keys == Val.nil then go more
          else if keys.isCons then
            if !(keys.properList && keys.toList.all Val.eqlable) then
              throw s!"case keys are eqlable atoms: {keys.render}"
            pure (tIf (.app "MEMBER-EQUAL" [key, .quote keys]) (← rd a.cdr.car) (← go more))
          else if keys.eqlable then
            pure (tIf (.app "EQUAL" [key, .quote keys]) (← rd a.cdr.car) (← go more))
          else throw s!"a case key is an eqlable atom: {keys.render}"
      let body ← go args.tail
      if bound then
        let fv := ((termFreeVars body).filter (· != "CASE-DO-NOT-USE-ELSEWHERE")).eraseDups
        pure (.lam ("CASE-DO-NOT-USE-ELSEWHERE" :: fv) body (keyT :: fv.map Term.var))
      else pure body
    | "LOGAND" | "LOGIOR" => match args with
      | [] => pure (.quote (.int (if f == "LOGAND" then -1 else 0)))
      | [a] => rd a
      | _ => foldR ("BINARY-" ++ f) args
    | "MV" => do
      if args.length < 2 then throw s!"mv takes two or more values: {x.render}"
      let ts ← rds args
      pure (ts.foldr (fun a acc => .app "CONS" [a, acc]) (.quote Val.nil))
    | "PROG2$" => do arity f args 2; let ts ← rds args; pure ts[1]!
    | "MEMBER-EQ" | "MEMBER-EQUAL" => do arity f args 2; pure (.app "MEMBER-EQUAL" (← rds args))
    | _ =>
      match vocabularyFns.find? (·.1 == f) with
      | some (_, n) => do arity f args n; pure (.app f (← rds args))
      | none => match w.ops.find? (·.name == f) with
        | some { callee := some callee, formals, stobjsIn, stobjsOut, .. } => do
          if !stobjsOut.all (·.isNone) then throw s!"{f} returns a child; it is not a pure operation"
          let vals := stobjsIn.takeWhile (·.isNone)
          let kids := stobjsIn.drop vals.length
          if !kids.all (·.isSome) || formals.length != stobjsIn.length then
            throw s!"{f}'s stobj formals are not trailing"
          arity f args vals.length
          let kidNames := kids.filterMap id
          for c in kidNames do
            if !k.tuple.contains c then throw s!"{f} takes {c}, outside {k.name}'s tuple"
          pure (.app callee ((← rds args) ++ kidNames.map Term.var))
        | _ => throw s!"{f} is neither in the arm vocabulary nor a declared pure operation: {x.render}"
  | _ => throw s!"not an expression: {x.render}"

/-- A phase form: a phase keyword, `(:if E N N)`, `(:case V ((CODE ...) N) ... (:otherwise N))`. -/
partial def readNext (k : Kind) (n : Expr) : Except String Term := do
  match n with
  | .sym p =>
    match k.phases.find? (·.1 == p) with
    | some (_, v) => pure (.quote (.int v))
    | none => throw s!":next names {p}, not a phase of {k.name}"
  | .cons (.sym ":IF") rest => match rest.toList with
    | [e, a, b] => do pure (tIf (← readExpr w k e) (← readNext k a) (← readNext k b))
    | _ => throw s!"malformed :next {n.render}"
  | .cons (.sym ":CASE") rest => do
    let key ← readExpr w k rest.car
    let rec go : List Val → Except String Term
      | [] => throw s!"a :next :case needs an :otherwise: {n.render}"
      | a :: more => do
        let e ← readNext k a.cdr.car
        if a.car == .sym ":OTHERWISE" then pure e
        else pure (tIf (.app "MEMBER-EQUAL" [key, .quote a.car]) e (← go more))
    go rest.cdr.toList
  | _ => throw s!"malformed :next {n.render}"

/-- Every expression and phase form of a path, unexercised branches included (`true`: a phase
form), so the reader can be run over a whole kind before any arm runs. -/
partial def Step.exprs : Step → List (Bool × Expr)
  | .let_ _ e | .wakeRow e => [(false, e)]
  | .set ps => ps.map ((false, ·.2))
  | .next n => [(true, n)]
  | .do_ _ c _ _ w el cs =>
    callExprs c ++ (w.toList ++ el).map ((false, ·)) ++ cs.flatMap fun (_, ss) => ss.flatMap Step.exprs
  | .issue c ok rf => callExprs c ++ (ok ++ rf).flatMap Step.exprs
  | .repeat_ n b u => [(false, n), (false, u)] ++ b.flatMap Step.exprs
  | .if_ c a b => (false, c) :: (a ++ b).flatMap Step.exprs
  | .cond cl => cl.flatMap fun (c, ss) => (false, c) :: ss.flatMap Step.exprs
  | .case_ key arms => (false, key) :: arms.flatMap fun (_, ss) => ss.flatMap Step.exprs
  | .charge a b c d => [a, b, c, d].flatMap fun o => o.toList.map ((false, ·))
  | .wait a b => [a, b].flatMap fun o => o.toList.map ((false, ·))
  | .park _ a _ st => [a, st].flatMap fun o => o.toList.map ((false, ·))
  | .stop _ st => st.toList.map ((false, ·))
  | _ => []
where callExprs (c : Call) : List (Bool × Expr) := (c.args ++ c.keys.map (·.2)).map ((false, ·))

/-- The reader over every expression of a kind's arms, handlers and sub-arms: the refusals, by
arm and expression. -/
def readKind (k : Kind) : List String :=
  (k.subarms ++ k.arms ++ k.observes).flatMap fun a =>
    match a.read with
    | .error m => [s!"{a.fn}: {m}"]
    | .ok d => ((d.onRefusal ++ d.steps).flatMap Step.exprs).filterMap fun (ph, e) =>
      match (if ph then readNext w k e else readExpr w k e) with
      | .ok _ => none
      | .error m => some s!"{a.fn}: {m}"

def ev (k : Kind) (st : St) (e : Expr) : Except String Val := do
  (← readExpr w k e).eval w.fns (st.vars ++ st.stobjs)

def evOpt (k : Kind) (st : St) (e : Option Expr) (dflt : Val) : Except String Val :=
  match e with
  | some e => ev w k st e
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

/-- Write the pending fields and the path's phase before an operation call or a terminal; their
terms are evaluated here, as the generator's checked write evaluates them. -/
def flush (f : Frame) (st : St) : Except String St := do
  let pairs ← st.pending.mapM fun (n, e) => do pure (n, ← ev w f.kind st e)
  let pairs ← match st.next with
    | some n => do pure (pairs ++ [("PHASE", ← (← readNext w f.kind n).eval w.fns (st.vars ++ st.stobjs))])
    | none => pure pairs
  let st' ← if pairs.isEmpty then pure st else put w f st pairs
  pure { st' with pending := [], next := none, nextDone := st.nextDone || st.next.isSome }

def pend (st : St) (pairs : List (String × Expr)) : Except String St :=
  if pairs.any (fun p => st.pending.any (·.1 == p.1)) then
    .error s!"a field is written twice before the next operation"
  else .ok { st with pending := st.pending ++ pairs }

/-- The actuals of a call: positional arguments fill the leading value formals, the stobj formals
take the tuple's children, the owner triple `okind oslot ogen` comes from the row (`KIND`, `ID`,
`ROW-GENERATION`), and any other formal is a `:FORMAL E` keyword. -/
def actuals (k : Kind) (st : St) (formals : List String) (stobjsIn : List (Option String))
    (pos : List Expr) (keys : List (String × Expr)) : Except String (List Val) :=
  match formals, stobjsIn with
  | [], _ => if pos.isEmpty then .ok [] else .error "too many arguments"
  | _ :: fs, some s :: ss => do
    let v ← stobj st s
    let rest ← actuals k st fs ss pos keys
    pure (v :: rest)
  | fm :: fs, _ :: ss => do
    match pos with
    | p :: ps =>
      let v ← ev w k st p
      let rest ← actuals k st fs ss ps keys
      pure (v :: rest)
    | [] =>
      let v ← match keys.find? (·.1 == ":" ++ fm) with
        | some (_, e) => ev w k st e
        | none =>
          if fm == "OKIND" then var st "KIND"
          else if fm == "OSLOT" then var st "ID"
          else if fm == "OGEN" then var st "ROW-GENERATION"
          else throw s!"no argument for the formal {fm}"
      let rest ← actuals k st fs ss [] keys
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
def callOp (k : Kind) (st : St) (c : Call) : Except String (Op × Val) := do
  let op ← findOp w c.op
  let callee ← match op.callee with
    | some f => pure f
    | none => throw s!"{c.op} names no :child (not in child form)"
  let args ← actuals w k st op.formals op.stobjsIn c.args c.keys
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
def stopEnd (f : Frame) (st : St) (steps : Option Expr) : Except String Res := do
  if f.observe then wakeResult f st (← const w "*FN2-NONE*")
  else chargeResult f st (.int 0) (← evOpt w f.kind st steps (← const w "*FN2-WORK-EMPTY*")) (.int 0) Val.nil

def codeIn (code : Val) (codes : List Val) : Bool := codes.contains code

/-- The interpreter: run a path's steps to its terminal. -/
def run (f : Frame) : Nat → St → List Step → Except String Res
  | 0, _, _ => .error "fuel"
  | _ + 1, _, [] => .error "a path ends without a terminal"
  | fuel + 1, st, s :: rest =>
    match s with
    | .let_ v e => do
      let x ← ev w f.kind st e
      run f fuel { st with vars := (v, x) :: st.vars } rest
    | .set pairs => do run f fuel (← pend st pairs) rest
    | .next ph => do
      if st.next.isSome || st.nextDone then throw "a path has two :next steps"
      run f fuel { st with next := some ph } rest
    | .do_ vars c acceptGiven accept when_ else_ cases => do
      let st ← flush w f st
      let op ← findOp w c.op
      let skip ← match when_ with
        | some e => do pure !(← ev w f.kind st e).truthy
        | none => pure false
      let st ← if skip then do
          let vs ← else_.mapM (ev w f.kind st)
          pure { st with vars := vars.zip vs ++ st.vars }
        else do
          let (_, r) ← callOp w f.kind st c
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
      let (op, r) ← callOp w f.kind st c
      let st ← bindOuts st op.stobjsOut ["FN2-ISSUE-CODE", "FN2-ISSUE-OP", "FN2-ISSUE-OPGEN"] r
      let code ← var st "FN2-ISSUE-CODE"
      if code == Val.kw "OK" then run f fuel st ok
      else if code == Val.kw "EXHAUSTED" then
        run f fuel st (refused ++ [.park "OPERATION" none none none])
      else run f fuel st (refused ++ (if f.refusal.isEmpty then [.halt] else f.refusal))
    | .repeat_ n body until_ => do
      let st0 := st
      let st ← flush w f st
      let k := (← ev w f.kind st n).nfix
      let rec loop : Nat → Nat → St → Except String St
        | 0, _, _ => .error "fuel"
        | _, 0, st => .ok st
        | fuel' + 1, k + 1, st => do
          let id ← var st "ID"
          let slot ← var st "SLOT"
          let reads ← rowReads w f.kind st.stobjs id slot
          let pass : St := { stobjs := st.stobjs, vars := reads ++ f.base }
          if (← ev w f.kind pass until_).truthy then pure st
          else match ← run f fuel' pass (body ++ [.repeatNext]) with
            | .again st' => loop fuel' k { st with stobjs := st'.stobjs }
            | .done _ => throw "a :repeat pass ended in a terminal"
      let st' ← loop fuel k st
      -- the generator's continuation keeps a :next declared before the loop (written again at
      -- the path's terminal) and clears only the pending fields
      run f fuel { st with stobjs := st'.stobjs, pending := [], next := st0.next,
                           nextDone := st0.nextDone } rest
    | .repeatNext => do
      let st ← flush w f st
      pure (.again st)
    | .wakeRow e => do
      if st.woken then throw "a path wakes at most one row"
      let v ← ev w f.kind st e
      let r ← callFn w "FN2-MACHINES-WAKE-ROW" [v, ← stobj st "FN2-MACHINES", ← stobj st "FN2-CONTROL"]
      let st := setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car
      run f fuel { st with woken := true } rest
    | .if_ c a b => do
      if (← ev w f.kind st c).truthy then run f fuel st a else run f fuel st b
    | .cond clauses => do
      match ← clauses.findM? (fun (c, _) => do pure (← ev w f.kind st c).truthy) with
      | some (_, steps) => run f fuel st steps
      | none => throw ":cond without a true clause"
    | .case_ key arms => do
      let kv ← ev w f.kind st key
      match arms.find? (fun (cs, _) => match cs with
          | some l => codeIn kv l
          | none => true) with
      | some (_, steps) => run f fuel st steps
      | none => throw ":case without :otherwise"
    | .charge b s d r => do
      let st ← flush w f st
      chargeResult f st (← evOpt w f.kind st b (.int 0)) (← evOpt w f.kind st s (.int 0))
        (← evOpt w f.kind st d (.int 0)) (← evOpt w f.kind st r Val.nil)
    | .idle => do
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-EMPTY*") (.int 0) Val.nil
    | .yield => do
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-EMPTY*") (.int 0) Val.t
    | .wait b s => do
      let st ← pend st [("PENDING", Expr.q (.int 1)), ("WAIT-REASON", Expr.q (← const w "*FN2-WAIT-COMPLETION*"))]
      let st ← flush w f st
      chargeResult f st (← evOpt w f.kind st b (.int 0)) (← evOpt w f.kind st s (← const w "*FN2-WORK-MAILBOX*"))
        (.int 1) Val.nil
    | .halt => do
      let st ← pend st [("STOPPED", Expr.q (.int 1)), ("WAIT-REASON", Expr.q (← const w "*FN2-WAIT-NONE*"))]
      let st ← flush w f st
      chargeResult f st (.int 0) (← const w "*FN2-WORK-MAILBOX*") (.int 0) Val.nil
    | .park wait arg kind steps => do
      let mailbox ← const w "*FN2-WORK-MAILBOX*"
      let viaOp (st : St) (op : String) (args : List Expr) : Except String Res := do
        let st ← flush w f st
        let (o, r) ← callOp w f.kind st ⟨op, args, []⟩
        let st ← bindOuts st o.stobjsOut [] r
        chargeResult f st (.int 0) (← evOpt w f.kind st steps mailbox) (.int 0) Val.nil
      match wait with
      | "OPERATION" => viaOp st "FN2-MACHINE-PARK" [.sym "ID"]
      | "ADMISSION" => viaOp st "FN2-MACHINE-PARK-ADMISSION" ([.sym "ID"] ++ arg.toList)
      | "TAKEN" => viaOp st ("FN2-MACHINE-PARK-TAKEN-" ++ kind.getD "") [.sym "ID"]
      | "POOL" => do
        let cls ← match arg with
          | some a => pure a
          | none => throw "(:park :pool) without a class"
        let st ← pend st [("CURSOR", cls)]
        let st ← flush w f st
        let r ← callFn w "FN2-MACHINES-PARK-POOL"
          [← var st "ID", ← stobj st "FN2-MACHINES", ← stobj st "FN2-CONTROL"]
        let st := setStobj (setStobj st "FN2-MACHINES" r.car) "FN2-CONTROL" r.cdr.car
        chargeResult f st (.int 0) (← evOpt w f.kind st steps mailbox) (.int 0) Val.nil
      | other => match w.waits.find? (·.kind == other) with
        | some ⟨_, some parker⟩ => viaOp st parker [.sym "ID"]
        | some ⟨_, none⟩ => do
          let st ← pend st [("WAIT-REASON", Expr.q (← const w ("*FN2-WAIT-" ++ other ++ "*")))]
          let st ← flush w f st
          chargeResult f st (.int 0) (← evOpt w f.kind st steps mailbox) (.int 0) Val.nil
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
      if st.woken then throw "the path already woke a row (:wake-row); a path wakes at most one row"
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
      let d ← sub.read
      run { f with refusal := d.onRefusal } fuel
        { stobjs := st.stobjs, vars := reads ++ f.base } d.steps

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
  let d ← a.read
  let f : Frame := { kind := k, observe, refusal := d.onRefusal, base }
  match ← run w f fuel { stobjs, vars := reads ++ base } d.steps with
  | .done v => pure v
  | .again _ => throw ":repeat-next outside a :repeat"

end

end Fn2.Arms
