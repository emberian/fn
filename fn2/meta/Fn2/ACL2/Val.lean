/-!
# Fn2.ACL2.Val: ACL2's universe and the primitives of fn2's closed subset

The shallow embedding of LEAN-METATHEORY §-1 item 2 reads ACL2 terms into Lean functions over
`Val`, a Lean model of the ACL2 objects the subset can produce: integers, symbols (by their
printed name in the `ACL2` package, so `NIL`, `T`, `:OK`, `FN2-NONE`), strings, characters and
conses. A stobj is its logical value: a true list of its fields, an array field the list of its
elements (ACL2's own logical definition of every stobj accessor, which the emitter translates
like any other function).

Rationals and complex numbers are outside the subset: the closure of every translated operation
reaches the reciprocal, `NUMERATOR` and `DENOMINATOR` only through `FLOOR`, `MOD`, `EVENP` and
`NONNEGATIVE-INTEGER-QUOTIENT`, which are native here (`Native`), so no translated body can build a
non-integer number. `EXPT` with a negative exponent and a base other than 0, 1 or -1 is the one
native operation whose ACL2 value is not an integer; it is outside the subset and returns 0 here
(the native agrees with ACL2's definition exactly where that value is an integer).

The primitives are ACL2's (`*primitive-formals-and-guards*`) with ACL2's completions: a non-number
argument of arithmetic is 0, `CAR` of an atom is `NIL`. Guards are not checked by these
definitions; a translated function's guard is a separate term (`Fn2.ACL2.Fn.guard`), a precondition.
-/

namespace Fn2.ACL2

/-- An ACL2 object of the subset. A symbol is its printed name relative to the `ACL2` package. -/
inductive Val where
  | int (i : Int)
  | sym (name : String)
  | str (s : String)
  | chr (c : Char)
  | cons (a d : Val)
  deriving DecidableEq, Inhabited, Hashable

namespace Val

def nil : Val := .sym "NIL"
def t : Val := .sym "T"
def kw (s : String) : Val := .sym (":" ++ s)
def ofBool (b : Bool) : Val := if b then t else nil
def ofNat (n : Nat) : Val := .int n

/-- ACL2's truth: everything but `NIL`. -/
def truthy : Val → Bool
  | .sym "NIL" => false
  | _ => true

def isNil (v : Val) : Bool := !v.truthy

/-- `FIX` and `IFIX` agree on the subset's numbers (integers only). -/
def toInt : Val → Int
  | .int i => i
  | _ => 0

def nfix (v : Val) : Nat := v.toInt.toNat

def car : Val → Val
  | .cons a _ => a
  | _ => nil

def cdr : Val → Val
  | .cons _ d => d
  | _ => nil

def isCons : Val → Bool
  | .cons _ _ => true
  | _ => false

def isInt : Val → Bool
  | .int _ => true
  | _ => false

/-- A Lean list as an ACL2 true list. -/
def ofList : List Val → Val
  | [] => nil
  | x :: xs => .cons x (ofList xs)

/-- The elements of an ACL2 list (its cars up to the final atom). -/
def toList : Val → List Val
  | .cons a d => a :: toList d
  | _ => []

/-- `ACL2-COUNT`, the measure ACL2 admits most recursions with. -/
def acl2Count : Val → Nat
  | .int i => i.natAbs
  | .cons a d => 1 + acl2Count a + acl2Count d
  | .str s => s.length
  | _ => 0

/-- The printed form, as ACL2 prints it (integers, symbols, strings, lists). -/
partial def render : Val → String
  | .int i => toString i
  | .sym s => s
  | .str s => "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""
  | .chr c => "#\\" ++ c.toString
  | v@(.cons _ _) =>
    let rec go (acc : List String) : Val → List String × Option Val
      | .cons a d => go (render a :: acc) d
      | .sym "NIL" => (acc.reverse, none)
      | x => (acc.reverse, some x)
    let (xs, tail) := go [] v
    "(" ++ " ".intercalate xs ++ (match tail with | some x => " . " ++ render x | none => "") ++ ")"

instance : Repr Val := ⟨fun v _ => Std.Format.text v.render⟩
instance : ToString Val := ⟨Val.render⟩

end Val

/-! ## The primitives (ACL2's, with completions) -/

namespace Prim
open Val

def equal (a b : Val) : Val := ofBool (a == b)
def lt (a b : Val) : Val := ofBool (a.toInt < b.toInt)
def plus (a b : Val) : Val := .int (a.toInt + b.toInt)
def times (a b : Val) : Val := .int (a.toInt * b.toInt)
def neg (a : Val) : Val := .int (- a.toInt)
def consp (a : Val) : Val := ofBool a.isCons
def integerp (a : Val) : Val := ofBool a.isInt
def acl2Numberp (a : Val) : Val := ofBool a.isInt
def symbolp : Val → Val
  | .sym _ => Val.t
  | _ => Val.nil
def stringp : Val → Val
  | .str _ => Val.t
  | _ => Val.nil
def characterp : Val → Val
  | .chr _ => Val.t
  | _ => Val.nil
/-- `RATIONALP`: on the subset's numbers, `INTEGERP`. -/
def rationalp (a : Val) : Val := ofBool a.isInt
/-- `COERCE` to `'LIST` (a string's characters) or `'STRING` (a character list's string; a
non-character is `(code-char 0)`, as `MAKE-CHARACTER-LIST`). -/
def coerce (x y : Val) : Val :=
  match y with
  | .sym "LIST" => match x with
    | .str s => Val.ofList (s.toList.map Val.chr)
    | _ => Val.nil
  | _ => .str (String.ofList (x.toList.map fun | .chr c => c | _ => Char.ofNat 0))

end Prim

/-! ## The native built-ins

Each is an ACL2 function with a logical definition in ACL2's ground-zero world, replaced here by a
Lean definition that is meant to compute the same value on every argument (for `EXPT`, every
argument on which ACL2's value is an integer). They are the subset's only trusted semantics beyond
the primitives; the emitter cuts the closure at them and records their names in the generated
file. Proving each one equal to the translation of its ACL2 definition is owed (LEAN-METATHEORY
§10, the pathway). -/

namespace Native
open Val

/-- Two's-complement bitwise operations over `Int`, through `Nat` on the complement. -/
def bitop (f : Bool → Bool → Bool) (a b : Int) : Int :=
  -- the sign bits combine like any other bit; ACL2's logand etc. are the infinite-precision ops
  let sa := decide (a < 0)
  let sb := decide (b < 0)
  let na : Nat := if sa then (-a - 1).toNat else a.toNat
  let nb : Nat := if sb then (-b - 1).toNat else b.toNat
  -- bit i of a is (testBit na i) xor sa
  let sr := f sa sb
  let width := max (Nat.log2 na) (Nat.log2 nb) + 2
  let r : Nat := (List.range width).foldl (fun acc i =>
    let ba := na.testBit i != sa
    let bb := nb.testBit i != sb
    let br := f ba bb
    if br != sr then acc ||| (1 <<< i) else acc) 0
  if sr then -(r : Int) - 1 else r

def logand (a b : Val) : Val :=
  let x := a.toInt; let y := b.toInt
  if 0 ≤ x ∧ 0 ≤ y then .int (x.toNat &&& y.toNat) else .int (bitop (· && ·) x y)
def logior (a b : Val) : Val :=
  let x := a.toInt; let y := b.toInt
  if 0 ≤ x ∧ 0 ≤ y then .int (x.toNat ||| y.toNat) else .int (bitop (· || ·) x y)
def logxor (a b : Val) : Val :=
  let x := a.toInt; let y := b.toInt
  if 0 ≤ x ∧ 0 ≤ y then .int (x.toNat ^^^ y.toNat) else .int (bitop (· != ·) x y)
def logeqv (a b : Val) : Val := .int (- (logxor a b).toInt - 1)
def lognot (a : Val) : Val := .int (- a.toInt - 1)
def logorc1 (a b : Val) : Val := logior (lognot a) b

/-- `FLOOR` on the subset's numbers: a zero divisor gives 0 (ACL2: `(/ i 0)` is 0). -/
def floor (a b : Val) : Val :=
  let j := b.toInt
  if j = 0 then .int 0 else .int (Int.fdiv a.toInt j)
/-- `MOD`: `(- x (* y (floor x y)))`. -/
def mod (a b : Val) : Val :=
  .int (a.toInt - b.toInt * (floor a b).toInt)
/-- `EVENP`: `(integerp (* x (/ 2)))`; a non-number is 0, which is even. -/
def evenp (a : Val) : Val := ofBool (a.toInt % 2 == 0)
/-- `NONNEGATIVE-INTEGER-QUOTIENT`. -/
def niq (i j : Val) : Val :=
  match i, j with
  | .int a, .int b => if b ≤ 0 ∨ a < 0 then .int 0 else .int (a / b)
  | _, _ => .int 0
/-- `EXPT` on the integer domain (see the module note). -/
def expt (r i : Val) : Val :=
  let e := i.toInt
  let b := r.toInt
  if e = 0 then .int 1
  else if b = 0 then .int 0
  else if 0 < e then .int (b ^ e.toNat)
  else if b = 1 then .int 1
  else if b = -1 then .int (if e % 2 == 0 then 1 else -1)
  else .int 0

def len (l : Val) : Val := .int (go 0 l)
where go (n : Nat) : Val → Nat
  | .cons _ d => go (n + 1) d
  | _ => n

def nthN : Nat → Val → Val
  | _, .int _ | _, .sym _ | _, .str _ | _, .chr _ => Val.nil
  | 0, .cons a _ => a
  | n + 1, .cons _ d => nthN n d

def nth (n l : Val) : Val := nthN n.nfix l

/-- `UPDATE-NTH` without recursion along the spine (stobj arrays are long lists). -/
def updateNthIter (n : Nat) (v l : Val) : Val := Id.run do
  let mut pre : Array Val := #[]
  let mut cur := l
  for _ in [0:n] do
    pre := pre.push cur.car
    cur := cur.cdr
  let mut out := Val.cons v cur.cdr
  for x in pre.reverse do
    out := .cons x out
  return out

@[implemented_by updateNthIter]
def updateNthN : Nat → Val → Val → Val
  | 0, v, l => .cons v l.cdr
  | n + 1, v, l => .cons l.car (updateNthN n v l.cdr)

def updateNth (k v l : Val) : Val := updateNthN k.nfix v l

def memberEqual (x l : Val) : Val :=
  match l with
  | .cons a d => if x == a then l else memberEqual x d
  | _ => Val.nil

/-- The names this module implements, in ACL2's spelling: the emitter neither translates nor
refuses them. `IF` and `RETURN-LAST` are special forms of the translation (lazy branches; the
third argument). -/
def names : List String :=
  ["IF", "RETURN-LAST", "EQUAL", "CONS", "CAR", "CDR", "CONSP", "INTEGERP", "ACL2-NUMBERP",
   "RATIONALP", "COERCE", "SYMBOLP", "STRINGP", "CHARACTERP", "<", "BINARY-+", "BINARY-*", "UNARY--",
   "BINARY-LOGAND", "BINARY-LOGIOR", "BINARY-LOGXOR", "BINARY-LOGEQV", "LOGNOT", "LOGORC1",
   "FLOOR", "MOD", "EVENP", "NONNEGATIVE-INTEGER-QUOTIENT", "EXPT", "LEN", "NTH", "MV-NTH",
   "UPDATE-NTH", "MEMBER-EQUAL", "ACL2-COUNT"]

end Native

/-- The native built-ins by ACL2 name (arity checked), for the term evaluator. -/
def nativeCall (f : String) (args : List Val) : Option Val :=
  open Prim Native in
  match f, args with
  | "EQUAL", [a, b] => some (equal a b)
  | "CONS", [a, b] => some (.cons a b)
  | "CAR", [a] => some a.car
  | "CDR", [a] => some a.cdr
  | "CONSP", [a] => some (consp a)
  | "INTEGERP", [a] => some (integerp a)
  | "ACL2-NUMBERP", [a] => some (acl2Numberp a)
  | "RATIONALP", [a] => some (rationalp a)
  | "COERCE", [a, b] => some (coerce a b)
  | "SYMBOLP", [a] => some (symbolp a)
  | "STRINGP", [a] => some (stringp a)
  | "CHARACTERP", [a] => some (characterp a)
  | "<", [a, b] => some (lt a b)
  | "BINARY-+", [a, b] => some (plus a b)
  | "BINARY-*", [a, b] => some (times a b)
  | "UNARY--", [a] => some (neg a)
  | "BINARY-LOGAND", [a, b] => some (logand a b)
  | "BINARY-LOGIOR", [a, b] => some (logior a b)
  | "BINARY-LOGXOR", [a, b] => some (logxor a b)
  | "BINARY-LOGEQV", [a, b] => some (logeqv a b)
  | "LOGNOT", [a] => some (lognot a)
  | "LOGORC1", [a, b] => some (logorc1 a b)
  | "FLOOR", [a, b] => some (floor a b)
  | "MOD", [a, b] => some (mod a b)
  | "EVENP", [a] => some (evenp a)
  | "NONNEGATIVE-INTEGER-QUOTIENT", [a, b] => some (niq a b)
  | "EXPT", [a, b] => some (expt a b)
  | "LEN", [a] => some (len a)
  | "NTH", [a, b] => some (nth a b)
  | "MV-NTH", [a, b] => some (nth a b)
  | "UPDATE-NTH", [a, b, c] => some (updateNth a b c)
  | "MEMBER-EQUAL", [a, b] => some (memberEqual a b)
  | "ACL2-COUNT", [a] => some (.int a.acl2Count)
  | _, _ => none

/-! ## Translated terms, deep

ACL2's translated term language: a variable, a quoted constant, a call of a function symbol, or a
call of a closed `LAMBDA`. Registry data (step-language expressions, capacities, initial values)
is carried as `Term`; operation bodies are carried shallowly (generated `def`s). -/

inductive Term where
  | var (name : String)
  | quote (v : Val)
  | app (fn : String) (args : List Term)
  | lam (formals : List String) (body : Term) (actuals : List Term)
  deriving Inhabited, Repr

/-- The functions a term may call: natives first, then the translated operations. -/
abbrev Fns := String → List Val → Option Val

abbrev Env := List (String × Val)

def Env.get? (env : Env) (x : String) : Option Val := (env.find? (·.1 == x)).map (·.2)

/-- Evaluate a translated term. `IF` is lazy; `RETURN-LAST` is its third argument (ACL2's
logical meaning of `mbe`, `prog2$` and their kin). -/
partial def Term.eval (fns : Fns) (env : Env) : Term → Except String Val
  | .var x => match env.get? x with
    | some v => .ok v
    | none => .error s!"unbound variable {x}"
  | .quote v => .ok v
  | .app "IF" [c, a, b] => do
    let cv ← Term.eval fns env c
    if cv.truthy then Term.eval fns env a else Term.eval fns env b
  | .app "RETURN-LAST" [_, _, c] => Term.eval fns env c
  | .app f args => do
    let vs ← args.mapM (Term.eval fns env)
    match nativeCall f vs with
    | some v => .ok v
    | none => match fns f vs with
      | some v => .ok v
      | none => .error s!"no function {f} of arity {vs.length}"
  | .lam formals body actuals => do
    let vs ← actuals.mapM (Term.eval fns env)
    Term.eval fns (formals.zip vs) body

end Fn2.ACL2
