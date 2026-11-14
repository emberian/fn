module

public import Fn2.ACL2.Translation

@[expose] public section

namespace Fn2.ACL2.Translation

/-- A canonical logical definition. Attachments need a separate refinement;
there is deliberately no executable dispatch field here. -/
structure CanonicalDefinition where
  formals : List String
  body : Object
  syntaxFuel : Nat

abbrev CanonicalProgram := String → Option CanonicalDefinition
abbrev CallDomain := String → List Val → Prop

/-- Pointwise correspondence without importing a separate arithmetic library. -/
inductive RelatedArgs {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : RelatedArgs R [] []
  | cons {a b as bs} (head : R a b) (tail : RelatedArgs R as bs) :
      RelatedArgs R (a :: as) (b :: bs)

/-! Finite evaluation through canonical bodies, with a domain obligation at
EVERY reached function and primitive call. Unlike `evalExport`, a user call
cannot be answered by an arbitrary `Fns` oracle. Only the selected IF branch
is evaluated. Primitive correspondence is a separate required certificate. -/
mutual
inductive CanonicalEval (program : CanonicalProgram)
    (domain primitiveDomain : CallDomain) : Env → Term → Val → Prop where
  | quote {env v} : CanonicalEval program domain primitiveDomain env (.quote v) v
  | var {env name v} (lookup : env.get? name = some v) :
      CanonicalEval program domain primitiveDomain env (.var name) v
  | if_true {env c a b cv v}
      (condition : CanonicalEval program domain primitiveDomain env c cv)
      (truth : cv.truthy = true)
      (selected : CanonicalEval program domain primitiveDomain env a v) :
      CanonicalEval program domain primitiveDomain env (.app "IF" [c,a,b]) v
  | if_false {env c a b cv v}
      (condition : CanonicalEval program domain primitiveDomain env c cv)
      (truth : cv.truthy = false)
      (selected : CanonicalEval program domain primitiveDomain env b v) :
      CanonicalEval program domain primitiveDomain env (.app "IF" [c,a,b]) v
  | return_last {env a b c v}
      (selected : CanonicalEval program domain primitiveDomain env c v) :
      CanonicalEval program domain primitiveDomain env (.app "RETURN-LAST" [a,b,c]) v
  | lam {env formals body actuals values v}
      (arguments : CanonicalEvalArgs program domain primitiveDomain env actuals values)
      (arity : values.length = formals.length)
      (evaluated : CanonicalEval program domain primitiveDomain (formals.zip values) body v) :
      CanonicalEval program domain primitiveDomain env (.lam formals body actuals) v
  | primitive {env name actuals values v}
      (notIf : name ≠ "IF") (notReturnLast : name ≠ "RETURN-LAST")
      (arguments : CanonicalEvalArgs program domain primitiveDomain env actuals values)
      (admitted : primitiveDomain name values)
      (evaluated : nativeCall name values = some v) :
      CanonicalEval program domain primitiveDomain env (.app name actuals) v
  | call {env name actuals values definition body v}
      (notIf : name ≠ "IF") (notReturnLast : name ≠ "RETURN-LAST")
      (arguments : CanonicalEvalArgs program domain primitiveDomain env actuals values)
      (notNative : nativeCall name values = none)
      (resolved : program name = some definition)
      (admitted : domain name values)
      (arity : values.length = definition.formals.length)
      (decoded : readTerm definition.syntaxFuel definition.body = some body)
      (evaluated : CanonicalEval program domain primitiveDomain (definition.formals.zip values) body v) :
      CanonicalEval program domain primitiveDomain env (.app name actuals) v

inductive CanonicalEvalArgs (program : CanonicalProgram)
    (domain primitiveDomain : CallDomain) : Env → List Term → List Val → Prop where
  | nil {env} : CanonicalEvalArgs program domain primitiveDomain env [] []
  | cons {env term terms value values}
      (head : CanonicalEval program domain primitiveDomain env term value)
      (tail : CanonicalEvalArgs program domain primitiveDomain env terms values) :
      CanonicalEvalArgs program domain primitiveDomain env (term :: terms) (value :: values)
end

/-- The entry body is read from the named canonical record. A finite derivation
includes every reached callee, even in a recursive component. -/
def CanonicalExportEval (program : CanonicalProgram) (domain primitiveDomain : CallDomain)
    (name : String) (values : List Val) (v : Val) : Prop :=
  ∃ definition body, program name = some definition ∧ domain name values ∧
    values.length = definition.formals.length ∧
    readTerm definition.syntaxFuel definition.body = some body ∧
    CanonicalEval program domain primitiveDomain (definition.formals.zip values) body v

/-- A separately exported guard, kept distinct from the logical body. The
packet emitter must bind both records to the same canonical function subject. -/
structure CanonicalGuard where
  formals : List String
  guard : Object
  syntaxFuel : Nat

abbrev CanonicalGuards := String → Option CanonicalGuard

/-- Guard admission uses a finite canonical derivation, including every reached
callee and primitive domain. An emitted dispatch equation cannot answer a guard.
This is a domain layer, not ACL2 primitive or executable correspondence. -/
def CanonicalGuardEval (program : CanonicalProgram) (guards : CanonicalGuards)
    (domain primitiveDomain : CallDomain) (name : String) (values : List Val) : Prop :=
  ∃ definition guard term result,
    program name = some definition ∧ guards name = some guard ∧
    guard.formals = definition.formals ∧ values.length = definition.formals.length ∧
    readTerm guard.syntaxFuel guard.guard = some term ∧
    CanonicalEval program domain primitiveDomain (guard.formals.zip values) term result ∧
    result.truthy = true

/-- Every admitted call satisfies its exact canonical guard. Nonempty root
admission and invariant preservation remain separate obligations. -/
def DomainRespectsGuards (program : CanonicalProgram) (guards : CanonicalGuards)
    (domain primitiveDomain : CallDomain) : Prop :=
  ∀ name values, domain name values →
    CanonicalGuardEval program guards domain primitiveDomain name values

/-- Reuse a callee's body evaluation, not merely its emitted dispatch equation. -/
theorem canonical_call_of_export {program domain primitiveDomain env name actuals values v}
    (notIf : name ≠ "IF") (notReturnLast : name ≠ "RETURN-LAST")
    (arguments : CanonicalEvalArgs program domain primitiveDomain env actuals values)
    (notNative : nativeCall name values = none)
    (callee : CanonicalExportEval program domain primitiveDomain name values v) :
    CanonicalEval program domain primitiveDomain env (.app name actuals) v := by
  obtain ⟨definition, body, resolved, admitted, arity, decoded, evaluated⟩ := callee
  exact .call notIf notReturnLast arguments notNative resolved admitted arity decoded evaluated

/-- A guarded body certificate joins the closed canonical evaluation with the
concrete emitted dispatch and its existing canonical-body interpreter equation.
This is still not primitive/ACL2 correspondence: that has its own obligation. -/
def CanonicalBodyCorrect (program : CanonicalProgram) (domain primitiveDomain : CallDomain)
    (emitted : Fns) (name : String) (post : List Val → Val → Prop) : Prop :=
  ∀ values, domain name values → ∃ definition v,
    program name = some definition ∧ values.length = definition.formals.length ∧
    CanonicalExportEval program domain primitiveDomain name values v ∧
    emitted name values = some v ∧
    evalExport definition.syntaxFuel definition.body emitted (definition.formals.zip values) = .ok v ∧
    post values v

/-- A native call is adequate only when its canonical object interpretation
agrees on every admitted represented input. No missing primitive defaults true. -/
def PrimitiveCorrespondence (canonical : String → List Object → Option Object)
    (primitiveDomain : CallDomain) : Prop :=
  ∀ name objects values, RelatedArgs (fun o v => o.value? = some v) objects values →
    primitiveDomain name values → ∀ result, nativeCall name values = some result →
      ∃ objectResult, canonical name objects = some objectResult ∧ objectResult.value? = some result

/-- Integer decoding has a unique canonical constructor; arithmetic-domain
proofs cannot silently identify a rational or a different object with an integer. -/
theorem object_of_value_integer {object : Object} {i : Int}
    (represented : object.value? = some (.int i)) : object = .integer i := by
  cases object with
  | integer n => simpa only [Object.value?, Option.some.injEq, Val.int.injEq, Object.integer.injEq] using represented
  | rational n d => cases represented
  | complex re im => cases represented
  | symbol p n =>
      cases hn : (Object.symbol p n).name? <;> simp [Object.value?, hn] at represented
  | character n =>
      simp only [Object.value?] at represented
      split at represented <;> cases represented
  | string cs =>
      cases hs : codeString cs <;> simp [Object.value?, hs] at represented
  | cons a d =>
      cases ha : a.value? <;> cases hd : d.value? <;>
        simp [Object.value?, ha, hd] at represented

/-- Guarded composition uses only the taken branch; it need not certify an
unreachable rational-producing expression in the other branch. -/
theorem eval_if_true {fns : Fns} {env : Env} {fuel : Nat} {c a b : Term} {cv v : Val}
    (condition : eval fns env c fuel = .ok cv) (truth : cv.truthy = true)
    (selected : eval fns env a fuel = .ok v) :
    eval fns env (.app "IF" [c,a,b]) (fuel+1) = .ok v := by
  change (do let x ← eval fns env c fuel
             if x.truthy then eval fns env a fuel else eval fns env b fuel) = _
  rw [condition]
  change (if cv.truthy then eval fns env a fuel else eval fns env b fuel) = _
  simpa only [truth, ↓reduceIte] using selected

theorem eval_if_false {fns : Fns} {env : Env} {fuel : Nat} {c a b : Term} {cv v : Val}
    (condition : eval fns env c fuel = .ok cv) (truth : cv.truthy = false)
    (selected : eval fns env b fuel = .ok v) :
    eval fns env (.app "IF" [c,a,b]) (fuel+1) = .ok v := by
  change (do let x ← eval fns env c fuel
             if x.truthy then eval fns env a fuel else eval fns env b fuel) = _
  rw [condition]
  change (if cv.truthy then eval fns env a fuel else eval fns env b fuel) = _
  simpa only [truth, Bool.false_eq_true, ↓reduceIte] using selected

end Fn2.ACL2.Translation
end
