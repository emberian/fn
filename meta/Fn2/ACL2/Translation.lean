import Fn2.Pathway

/-! Per-emission translation validation. The dispatch is a parameter, not an
axiom: each generated body equation is checked by Lean. ACL2 independently
checks the same body against its live world. These are two kernels and an
explicit object correspondence, not an import of ACL2 proofs into Lean. -/
namespace Fn2.ACL2.Translation
open Fn2.ACL2

/-- Exact export atoms. No printed-symbol guessing or newline normalization. -/
inductive Object where
  | integer (n : Int)
  | rational (numerator : Int) (denominator : Nat)
  | complex (real imag : Object)
  | symbol (packageName name : List Nat)
  | character (code : Nat)
  | string (codes : List Nat)
  | cons (car cdr : Object)
  deriving DecidableEq, Repr

/-- A checked body equation is universally quantified over its actual values.
The callee dispatch is explicit so closure certificates compose. -/
def BodyCorrect (fns : Fns) (formals : List String) (body : Term)
    (emitted : List Val → Option Val) : Prop :=
  ∀ args, args.length = formals.length →
    ∃ result, emitted args = some result ∧
      body.eval fns (formals.zip args) = .ok result

/-- The exact manifest compared by a certificate includes layout order and the
constrained and selected names of every attachment; equality is kernel checked. -/
structure Manifest where
  layout : List String
  attachments : List (String × String)
  deriving DecidableEq

def accepts (expected candidate : Manifest) : Bool := decide (candidate = expected)

theorem accepts_iff (expected candidate : Manifest) :
    accepts expected candidate = true ↔ candidate = expected := by
  simp [accepts]

theorem rejects_changed_manifest (expected candidate : Manifest)
    (changed : candidate ≠ expected) : accepts expected candidate = false := by
  simp [accepts, changed]

end Fn2.ACL2.Translation

namespace Fn2.ACL2.Translation
open Fn2.ACL2

def codeString (codes : List Nat) : Option String :=
  if codes.all (· < 256) then some (String.ofList (codes.map Char.ofNat)) else none

/-- The explicitly supported ACL2 package correspondence. The canonical object
retains both names; this adapter is only for the existing Val presentation. -/
def Object.name? : Object → Option String
  | .symbol p n => do
    let p ← codeString p
    let n ← codeString n
    if p == "KEYWORD" then some (":" ++ n)
    else if p == "ACL2" || p == "COMMON-LISP" then some n else none
  | _ => none

def Object.value? : Object → Option Val
  | .integer n => some (.int n)
  | .rational _ _ | .complex _ _ => none
  | .symbol p n => (Object.symbol p n).name? |>.map Val.sym
  | .character n => if n < 256 then some (.chr (Char.ofNat n)) else none
  | .string cs => (codeString cs).map Val.str
  | .cons a d => do pure (.cons (← a.value?) (← d.value?))

def Object.list? : Object → Option (List Object)
  | .cons a d => (Object.list? d).map (a :: ·)
  | .symbol p n => if p == [67,79,77,77,79,78,45,76,73,83,80] && n == [78,73,76]
      then some [] else none
  | _ => none

/-- Read the complete quoted ACL2 core layout, preserving field order. -/
def readCoreLayout (x : Object) : Option (List String) := do
  let xs ← x.list?
  match xs with
  | [q, rows] =>
    if q.name? != some "QUOTE" then none else do
      let rows ← rows.list?
      rows.mapM fun row => do
        let fields ← row.list?
        match fields with
        | [_, child] => child.name?
        | _ => none
  | _ => none

/-- Independent reader of ACL2's translated term grammar. The finite syntax
budget is checked by the generated decoding theorem, never inferred from runs. -/
def readTerm : Nat → Object → Option Term
  | 0, _ => none
  | fuel + 1, x =>
    match x with
    | .symbol _ _ => x.name? |>.map Term.var
    | _ => do
      let xs ← x.list?
      let h ← xs.head?
      let args := xs.drop 1
      match h.name? with
      | some "QUOTE" => match args with
        | [v] => v.value? |>.map Term.quote
        | _ => none
      | some f => do pure (.app f (← args.mapM (readTerm fuel)))
      | none => do
        let hs ← h.list?
        match hs with
        | [l, fs, body] =>
          if l.name? != some "LAMBDA" then none else do
            let fs ← fs.list?
            pure (.lam (← fs.mapM Object.name?) (← readTerm fuel body)
              (← args.mapM (readTerm fuel)))
        | _ => none

/-- Evaluation starts from the canonical object, not an emitter's claimed AST. -/
def evalExport (syntaxFuel : Nat) (body : Object) (fns : Fns) (env : Env) : Except String Val :=
  match readTerm syntaxFuel body with
  | some term => Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ env term syntaxFuel
  | none => .error "unsupported canonical body"

end Fn2.ACL2.Translation

namespace Fn2.ACL2.Translation
open Fn2.ACL2
abbrev eval (fns : Fns) (env : Env) (e : Term) (fuel : Nat) :=
  Fn2.Pathway.eval ⟨[], [], [], [], fns⟩ env e fuel

/-- Compose a checked canonical decode with a body-evaluation certificate without
normalizing the concrete interpreter during proof search. -/
theorem evalExport_of_decoded_by_definition {fuel : Nat} {body : Object} {term : Term}
    {fns : Fns} {env : Env} {v : Val}
    (decoded : readTerm fuel body = some term)
    (evaluated : eval fns env term fuel = .ok v) :
    evalExport fuel body fns env = .ok v := by
  simpa only [evalExport, decoded] using evaluated

theorem eval_args_nil (fns : Fns) (env : Env) (fuel : Nat) :
    ([] : List Term).mapM (fun t => eval fns env t fuel) = .ok [] := rfl

theorem eval_args_cons {fns : Fns} {env : Env} {fuel : Nat}
    {t : Term} {ts : List Term} {v : Val} {vs : List Val}
    (h : eval fns env t fuel = .ok v)
    (hs : ts.mapM (fun t => eval fns env t fuel) = .ok vs) :
    (t :: ts).mapM (fun t => eval fns env t fuel) = .ok (v :: vs) := by
  simp only [List.mapM_cons, h, hs, Fn2.Arms.except_ok_bind]
  rfl

theorem eval_app {fns : Fns} {env : Env} {fuel : Nat}
    {f : String} {args : List Term} {vs : List Val} {v : Val}
    (hi : f ≠ "IF") (hr : f ≠ "RETURN-LAST")
    (ha : args.mapM (fun t => eval fns env t fuel) = .ok vs)
    (hc : (match nativeCall f vs with
      | some x => Except.ok x
      | none => match fns f vs with
        | some x => Except.ok x
        | none => .error s!"no function {f} of arity {vs.length}") = .ok v) :
    eval fns env (.app f args) (fuel + 1) = .ok v := by
  simp only [eval, Fn2.Pathway.eval, hi, hr, false_and, ↓reduceDIte]
  change (do let xs ← args.mapM (fun t => eval fns env t fuel)
             match nativeCall f xs with
             | some x => .ok x
             | none => match fns f xs with
               | some x => .ok x
               | none => .error s!"no function {f} of arity {xs.length}") = .ok v
  rw [ha]
  exact hc

theorem eval_if {fns : Fns} {env : Env} {fuel : Nat}
    {c a b : Term} {vc va vb : Val}
    (hc : eval fns env c fuel = .ok vc)
    (ha : eval fns env a fuel = .ok va)
    (hb : eval fns env b fuel = .ok vb) :
    eval fns env (.app "IF" [c,a,b]) (fuel + 1) =
      .ok (if vc.truthy then va else vb) := by
  change (do let cv ← eval fns env c fuel
             if cv.truthy then eval fns env a fuel else eval fns env b fuel) = _
  rw [hc]
  change (if vc.truthy then eval fns env a fuel else eval fns env b fuel) = _
  split <;> simp_all

/-- RETURN-LAST evaluates only its logical final argument, with one syntax step. -/
theorem eval_return_last {fns : Fns} {env : Env} {fuel : Nat}
    {a b c : Term} {v : Val} (hc : eval fns env c fuel = .ok v) :
    eval fns env (.app "RETURN-LAST" [a,b,c]) (fuel + 1) = .ok v := by
  exact hc

theorem eval_lam {fns : Fns} {env : Env} {fuel : Nat}
    {formals : List String} {body : Term} {actuals : List Term} {vs : List Val} {v : Val}
    (ha : actuals.mapM (fun t => eval fns env t fuel) = .ok vs)
    (hb : eval fns (formals.zip vs) body fuel = .ok v) :
    eval fns env (.lam formals body actuals) (fuel + 1) = .ok v := by
  change (do let xs ← actuals.mapM (fun t => eval fns env t fuel)
             eval fns (formals.zip xs) body fuel) = _
  rw [ha]
  exact hb

end Fn2.ACL2.Translation
