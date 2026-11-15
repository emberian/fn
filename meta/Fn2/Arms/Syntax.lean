module

public import Fn2.ACL2.Val

@[expose] public section

namespace Fn2.Arms.Syntax
open Fn2.ACL2

deriving instance DecidableEq for Except

/-- The declaration reader has its own syntax alphabet. Data symbols are never
unqualified: this projection visits only positions designated by the grammar.
The name environment makes the projection injective on the names it uses. -/
structure Projected where
  value : Val
  names : List (String × String) := []
  deriving Inhabited

def keep (v : Val) : Projected := ⟨v, []⟩
def list (xs : List Projected) : Projected :=
  ⟨Val.ofList (xs.map (·.value)), xs.flatMap (·.names)⟩
def proper : Val → Bool
  | .cons _ d => proper d
  | v => v == Val.nil

def items (v : Val) : Except String (List Val) :=
  if proper v then pure v.toList else throw "syntax has a dotted list"

def name (v : Val) : Except String Projected := do
  let .sym encoded := v | throw "syntax name is not a symbol"
  let n ←
    if encoded.startsWith "ACL2::" then pure (encoded.drop 6).toString
    else if encoded.startsWith "COMMON-LISP::" then pure (encoded.drop 13).toString
    else throw "syntax name lacks its home package"
  if n == "NIL" || n == "T" || n.startsWith ":" then
    throw "syntax name aliases a self-evaluating symbol"
  pure ⟨.sym n, [(encoded, n)]⟩

/-- These are the COMMON-LISP operators of the supported expression grammar,
not a census of ACL2's imports. ACL2 names cannot impersonate them. -/
def clOperators : List String :=
  ["QUOTE", "IF", "+", "*", "-", "1+", "1-", "<", ">", "<=", ">=", "=", "EQ",
   "EQL", "EQUAL", "/=", "NOT", "NULL", "AND", "OR", "COND", "CASE", "LOGAND", "LOGIOR",
   "INTEGERP", "FLOOR", "MOD", "ASH", "MIN", "MAX"]

def operator (v : Val) : Except String String := do
  let .sym encoded := v | throw "expression operator is not a symbol"
  if encoded == ":LIVE" || encoded == ":READ" then return encoded
  if encoded.startsWith "COMMON-LISP::" then
    let n := (encoded.drop 13).toString
    if clOperators.contains n then return n
    throw "COMMON-LISP operator is outside the arm grammar"
  if encoded.startsWith "ACL2::" then
    let n := (encoded.drop 6).toString
    if clOperators.contains n || n.startsWith ":" then throw "operator has the wrong home package"
    return n
  throw "operator lacks its home package"

def withHead (h : String) (xs : List Projected) : Projected := list (keep (.sym h) :: xs)

def expression : Nat → Val → Except String Projected
  | 0, _ => throw "expression projection exhausted its syntax budget"
  | fuel + 1, x => do
    match x with
    | .int _ | .str _ | .chr _ => return keep x
    | .sym n =>
      if n == "NIL" || n == "T" || n.startsWith ":" then return keep x
      name x
    | .cons h tail =>
      let f ← operator h
      let args ← items tail
      if f == "QUOTE" then
        match args with
        | [v] => return withHead f [keep v]
        | _ => throw "QUOTE requires one data object"
      if f == ":LIVE" || f == ":READ" then
        return withHead f (← args.mapM name)
      if f == "CASE" then
        let key :: clauses := args | throw "CASE requires a key"
        let key ← expression fuel key
        let clauses ← clauses.mapM fun clause => do
          let [codes, body] ← items clause | throw "CASE clause requires keys and a form"
          -- OTHERWISE is grammar, all other keys remain exact data.
          let codes := if codes == .sym "COMMON-LISP::OTHERWISE" then .sym "OTHERWISE" else codes
          return list [keep codes, ← expression fuel body]
        return withHead f (key :: clauses)
      if f == "COND" then
        let clauses ← args.mapM fun clause => do
          let forms ← items clause
          return list (← forms.mapM (expression fuel))
        return withHead f clauses
      return withHead f (← args.mapM (expression fuel))

/-- Calls have expression arguments and keyword/formal separators. -/
def call (fuel : Nat) (v : Val) : Except String Projected := do
  let h :: args ← items v | throw "empty operation call"
  let f ← operator h
  return withHead f (← args.mapM (expression fuel))

def phase : Nat → Val → Except String Projected
  | 0, _ => throw "phase projection exhausted its syntax budget"
  | fuel + 1, x => do
    match x with
    | .sym n => if n.startsWith ":" then return keep x else name x
    | _ =>
      let h :: args ← items x | throw "empty phase form"
      if h == .sym ":IF" then
        let [e, a, b] := args | throw "phase :IF requires three forms"
        return withHead ":IF" [← expression fuel e, ← phase fuel a, ← phase fuel b]
      if h == .sym ":CASE" then
        let key :: clauses := args | throw "phase :CASE requires a key"
        let clauses ← clauses.mapM fun clause => do
          let [codes, body] ← items clause | throw "phase clause requires keys and a form"
          return list [keep codes, ← phase fuel body]
        return withHead ":CASE" ((← expression fuel key) :: clauses)
      throw "unknown phase form"

/-- A plist projection chooses the grammar for each value, never its keys. -/
def plist (project : String → Val → Except String Projected) : List Val →
    Except String (List Projected)
  | [] => pure []
  | .sym k :: v :: rest => do
    if !k.startsWith ":" then throw "syntax option is not a keyword"
    return keep (.sym k) :: (← project k v) :: (← plist project rest)
  | _ => throw "syntax options are not pairs"

mutual
  def steps : Nat → Val → Except String Projected
    | 0, _ => throw "step projection exhausted its syntax budget"
    | fuel + 1, v => do return list (← (← items v).mapM (step fuel))

  def step : Nat → Val → Except String Projected
    | 0, _ => throw "step projection exhausted its syntax budget"
    | fuel + 1, v => do
      let .sym h :: args ← items v | throw "step lacks a keyword head"
      let expr := expression fuel
      let block := steps fuel
      let branches (cs : Val) : Except String Projected := do
        return list (← (← items cs).mapM fun c => do
          let codes :: body ← items c | throw "empty case branch"
          let body ← block (Val.ofList body)
          return ⟨.cons codes body.value, body.names⟩)
      let options := plist fun key value =>
        if key == ":CASE" then branches value
        else if key == ":OK" || key == ":REFUSED" then block value
        else if key == ":WHEN" then expr value
        else if key == ":ELSE" then do return list (← (← items value).mapM expr)
        else pure (keep value)
      match h, args with
      | ":LET", [n, e] => return withHead h [← name n, ← expr e]
      | ":SET", pairs =>
        let pairs ← pairs.mapM fun p => do
          let [n, e] ← items p | throw "SET requires field/expression pairs"
          return list [← name n, ← expr e]
        return withHead h pairs
      | ":NEXT", [p] => return withHead h [← phase fuel p]
      | ":DO", vars :: c :: opts =>
        return withHead h (list (← (← items vars).mapM name) :: (← call fuel c) :: (← options opts))
      | ":ISSUE", c :: opts => return withHead h ((← call fuel c) :: (← options opts))
      | ":REPEAT", n :: body :: opts =>
        return withHead h ((← expr n) :: (← block body) ::
          (← plist (fun key value => if key == ":UNTIL" then expr value else pure (keep value)) opts))
      | ":WAKE-ROW", [e] => return withHead h [← expr e]
      | ":IF", [e, a, b] => return withHead h [← expr e, ← block a, ← block b]
      | ":COND", clauses =>
        let clauses ← clauses.mapM fun c => do
          let e :: body ← items c | throw "empty COND branch"
          let e ← expr e
          let body ← block (Val.ofList body)
          return ⟨.cons e.value body.value, e.names ++ body.names⟩
        return withHead h clauses
      | ":CASE", key :: clauses =>
        let cs ← branches (Val.ofList clauses)
        let key ← expr key
        return ⟨.cons (.sym h) (.cons key.value cs.value), key.names ++ cs.names⟩
      | ":CHARGE", opts => return withHead h (← plist (fun _ => expr) opts)
      | ":WAIT", wait :: opts => return withHead h (keep wait :: (← plist (fun _ => expr) opts))
      | ":PARK", wait :: rest =>
        if wait == .sym ":TAKEN" then
          let kind :: opts := rest | throw "PARK TAKEN requires a kind"
          return withHead h (keep wait :: (← name kind) :: (← plist (fun _ => expr) opts))
        else if wait == .sym ":ADMISSION" || wait == .sym ":POOL" then
          let arg :: opts := rest | throw "PARK requires an argument"
          return withHead h (keep wait :: (← expr arg) :: (← plist (fun _ => expr) opts))
        else return withHead h (keep wait :: (← plist (fun _ => expr) rest))
      | ":STOP", reason :: opts => return withHead h (keep reason :: (← plist (fun _ => expr) opts))
      | ":GOTO", [n] => return withHead h [← name n]
      | ":REFUSE", [e] => return withHead h [← expr e]
      | ":COMMIT", succ :: opts =>
        let opts ← plist (fun key value =>
          if [":DEPENDENCIES", ":UNCHANGED", ":ACCEPTED", ":REFUSED", ":UNCERTAIN"].contains key then block value
          else if key == ":WORKSPACE" then do return list (← (← items value).mapM expr)
          else if key == ":TICKET" then name value
          else if key == ":WHY" then if value == Val.nil then pure (keep value) else name value
          else if key == ":BYTES" then expr value
          else pure (keep value)) opts
        return withHead h ((← expr succ) :: opts)
      | ":HALT", [] | ":IDLE", [] | ":YIELD", [] | ":WAKE", [] | ":NOWAKE", [] => return keep v
      | _, _ => throw "unsupported step syntax"
end

def declaration : Nat → Val → Except String Projected
  | 0, _ => throw "declaration projection exhausted its syntax budget"
  | fuel + 1, v => do
    match v with
    | .cons (.sym ":FROM") (.cons phases rest) =>
      let rest ← declaration fuel rest
      return ⟨.cons (.sym ":FROM") (.cons phases rest.value), rest.names⟩
    | .cons (.sym ":ON-REFUSAL") (.cons refusal rest) =>
      let single := match refusal.car with | .sym n => n.startsWith ":" | _ => false
      let refusal ← if single then step fuel refusal else steps fuel refusal
      let rest ← declaration fuel rest
      return ⟨.cons (.sym ":ON-REFUSAL") (.cons refusal.value rest.value), refusal.names ++ rest.names⟩
    | _ => steps fuel v

/-- A repeated internal name denotes the same canonical symbol everywhere.
Old unqualified declarations are rejected by `name`/`operator`, not accepted as
another external representation. -/
def finish (p : Projected) : Except String Val :=
  if p.names.all (fun (encoded, n) => p.names.all (fun (other, m) => n != m || encoded == other))
  then pure p.value else throw "distinct package symbols collide in declaration syntax"

def readDeclaration (fuel : Nat) (v : Val) : Except String Val := do finish (← declaration fuel v)
def readStep (fuel : Nat) (v : Val) : Except String Val := do finish (← step fuel v)
def readSteps (fuel : Nat) (v : Val) : Except String Val := do finish (← steps fuel v)

/-- Both canonical projections and the independent expansion must succeed;
matching errors never count as agreement. -/
def expansionAgrees (fuel : Nat) (word expansion : Val)
    (run : Val → Except String (List Val)) : Bool :=
  match readStep fuel word, readSteps fuel expansion with
  | .ok w, .ok e => match run w with
    | .ok result => decide (result = e.toList)
    | .error _ => false
  | _, _ => false

theorem expansionAgrees_sound {fuel : Nat} {word expansion : Val}
    {run : Val → Except String (List Val)}
    (h : expansionAgrees fuel word expansion run = true) :
    ∃ w e, readStep fuel word = .ok w ∧ readSteps fuel expansion = .ok e ∧
      run w = .ok e.toList := by
  cases hw : readStep fuel word with
  | error err => simp [expansionAgrees, hw] at h
  | ok w =>
    cases he : readSteps fuel expansion with
    | error err => simp [expansionAgrees, hw, he] at h
    | ok e =>
      cases hr : run w with
      | error err => simp [expansionAgrees, hw, he, hr] at h
      | ok result =>
        have same : result = e.toList := by simpa [expansionAgrees, hw, he, hr] using h
        exact ⟨w, e, rfl, rfl, same ▸ hr⟩

end Fn2.Arms.Syntax

end
