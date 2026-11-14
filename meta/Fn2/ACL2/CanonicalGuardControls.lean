module
public import Fn2.ACL2.CanonicalEvaluationControls
@[expose] public section
namespace Fn2.ACL2.Translation.GuardControls
open DomainControls

def integerGuard : CanonicalGuard :=
  ⟨["X"], .cons (.symbol [67,79,77,77,79,78,45,76,73,83,80] [73,78,84,69,71,69,82,80])
    (.cons (.symbol [65,67,76,50] [88])
      (.symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76])), 8⟩

def guards : CanonicalGuards
  | "FN2-TV-BUMP" => some integerGuard
  | "FN2-TV-TWICE-BUMP" => some integerGuard
  | _ => none

-- This fixture checks guard evaluation. Arithmetic body correspondence remains
-- in DomainControls; this separate primitive domain is not a composed claim.
def guardPrimitives (name : String) (values : List Val) : Prop :=
  name = "INTEGERP" ∧ ∃ x : Int, values = [.int x]

theorem integer_guard_decoded : readTerm 8 integerGuard.guard =
    some (.app "INTEGERP" [.var "X"]) := rfl

theorem integer_guard_evaluates (x : Int) :
    CanonicalEval program domain guardPrimitives [("X", .int x)]
      (.app "INTEGERP" [.var "X"]) Val.t := by
  exact .primitive (by decide +kernel) (by decide +kernel)
    (.cons (.var rfl) .nil) ⟨rfl, x, rfl⟩ rfl

theorem domain_respects_guards : DomainRespectsGuards program guards domain guardPrimitives := by
  intro name values admitted
  obtain ⟨choice, x, rfl⟩ := admitted
  rcases choice with rfl | rfl
  · exact ⟨bumpDefinition, integerGuard, .app "INTEGERP" [.var "X"], Val.t,
      rfl, rfl, rfl, rfl, integer_guard_decoded, integer_guard_evaluates x, rfl⟩
  · exact ⟨twiceDefinition, integerGuard, .app "INTEGERP" [.var "X"], Val.t,
      rfl, rfl, rfl, rfl, integer_guard_decoded, integer_guard_evaluates x, rfl⟩

theorem positive : domain "FN2-TV-BUMP" [.int 4] ∧
    CanonicalGuardEval program guards domain guardPrimitives "FN2-TV-BUMP" [.int 4] :=
  ⟨⟨Or.inl rfl, 4, rfl⟩, domain_respects_guards _ _ ⟨Or.inl rfl, 4, rfl⟩⟩

def renamedGuards : CanonicalGuards := fun _ => some { integerGuard with formals := ["Y"] }

theorem wrong_formals_rejected :
    ¬ CanonicalGuardEval program renamedGuards domain guardPrimitives "FN2-TV-BUMP" [.int 4] := by
  rintro ⟨definition, guard, term, result, resolved, selected, matched, rest⟩
  have hd : definition = bumpDefinition := by simpa [program] using resolved.symm
  have hg : guard = { integerGuard with formals := ["Y"] } := by
    simpa [renamedGuards] using selected.symm
  subst definition
  subst guard
  have : (["Y"] : List String) = ["X"] := matched
  contradiction

def falseGuard : CanonicalGuard :=
  ⟨["X"], .cons (.symbol [67,79,77,77,79,78,45,76,73,83,80] [81,85,79,84,69])
    (.cons (.symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76])
      (.symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76])), 8⟩
def falseGuards : CanonicalGuards := fun _ => some falseGuard

theorem changed_guard_rejected :
    ¬ CanonicalGuardEval program falseGuards domain guardPrimitives "FN2-TV-BUMP" [.int 4] := by
  rintro ⟨definition, guard, term, result, resolved, selected, matched, arity,
    decoded, evaluated, truth⟩
  have hg : guard = falseGuard := by simpa [falseGuards] using selected.symm
  subst guard
  have ht : some (.quote Val.nil) = some term := decoded
  cases Option.some.inj ht
  cases evaluated
  cases truth

#print axioms domain_respects_guards
#print axioms positive
#print axioms wrong_formals_rejected
#print axioms changed_guard_rejected
end Fn2.ACL2.Translation.GuardControls
end
