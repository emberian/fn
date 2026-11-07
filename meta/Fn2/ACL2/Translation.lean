import Fn2.ACL2.Val

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
