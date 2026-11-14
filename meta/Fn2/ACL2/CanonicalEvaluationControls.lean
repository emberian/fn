module
public import Fn2.ACL2.CanonicalEvaluation
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.Translation.DomainControls
set_option maxRecDepth 10000
def bumpDefinition : CanonicalDefinition := ⟨["X"], (.cons (.symbol [65, 67, 76, 50] [66, 73, 78, 65, 82, 89, 45, 43]) (.cons (.symbol [65, 67, 76, 50] [88]) (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [81, 85, 79, 84, 69]) (.cons (.integer (1)) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))), 16⟩
def twiceDefinition : CanonicalDefinition := ⟨["X"], (.cons (.cons (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [76, 65, 77, 66, 68, 65]) (.cons (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 86, 45, 66, 85, 77, 80]) (.cons (.symbol [65, 67, 76, 50] [89]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76])))) (.cons (.cons (.symbol [65, 67, 76, 50] [70, 78, 50, 45, 84, 86, 45, 66, 85, 77, 80]) (.cons (.symbol [65, 67, 76, 50] [88]) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))) (.symbol [67, 79, 77, 77, 79, 78, 45, 76, 73, 83, 80] [78, 73, 76]))), 16⟩

def bumpTerm : Term := .app "BINARY-+" [.var "X", .quote (.int 1)]
def twiceTerm : Term := .lam ["Y"] (.app "FN2-TV-BUMP" [.var "Y"]) [.app "FN2-TV-BUMP" [.var "X"]]
theorem bump_decoded : readTerm 16 bumpDefinition.body = some bumpTerm := rfl
theorem twice_decoded : readTerm 16 twiceDefinition.body = some twiceTerm := rfl

def program : CanonicalProgram
  | "FN2-TV-BUMP" => some bumpDefinition
  | "FN2-TV-TWICE-BUMP" => some twiceDefinition
  | _ => none

def domain (name : String) (args : List Val) : Prop :=
  (name = "FN2-TV-BUMP" ∨ name = "FN2-TV-TWICE-BUMP") ∧ ∃ x : Int, args = [.int x]
def primitiveDomain (name : String) (args : List Val) : Prop :=
  name = "BINARY-+" ∧ ∃ x y : Int, args = [.int x, .int y]
def canonicalPrimitive : String → List Object → Option Object
  | "BINARY-+", [.integer x, .integer y] => some (.integer (x+y))
  | _, _ => none

theorem addition_correspondence : PrimitiveCorrespondence canonicalPrimitive primitiveDomain := by
  intro name objects values represented admitted result evaluated
  obtain ⟨rfl, x, y, rfl⟩ := admitted
  cases represented with
  | cons hx rest =>
    cases rest with
    | cons hy tail =>
      cases tail
      cases object_of_value_integer hx
      cases object_of_value_integer hy
      change some (.int (x+y)) = some result at evaluated
      exact ⟨.integer (x+y), rfl, evaluated⟩

theorem bump_evaluates (x : Int) :
    CanonicalExportEval program domain primitiveDomain "FN2-TV-BUMP" [.int x] (.int (x+1)) := by
  refine ⟨bumpDefinition, bumpTerm, rfl, ⟨Or.inl rfl, x, rfl⟩, rfl, bump_decoded, ?_⟩
  exact .primitive (by decide) (by decide)
    (.cons (.var rfl) (.cons .quote .nil)) ⟨rfl, x, 1, rfl⟩ rfl

theorem twice_evaluates (x : Int) :
    CanonicalExportEval program domain primitiveDomain "FN2-TV-TWICE-BUMP" [.int x] (.int ((x+1)+1)) := by
  refine ⟨twiceDefinition, twiceTerm, rfl, ⟨Or.inr rfl, x, rfl⟩, rfl, twice_decoded, ?_⟩
  apply CanonicalEval.lam (values := [.int (x+1)])
  · exact .cons (canonical_call_of_export (by decide) (by decide)
      (.cons (.var rfl) .nil) (nativeCall_none _ _ (by decide +kernel)) (bump_evaluates x)) .nil
  · rfl
  · exact canonical_call_of_export (by decide) (by decide)
      (.cons (.var rfl) .nil) (nativeCall_none _ _ (by decide +kernel)) (bump_evaluates (x+1))

def emitted : Fns
  | "FN2-TV-BUMP", [.int x] => some (.int (x+1))
  | "FN2-TV-TWICE-BUMP", [.int x] => some (.int ((x+1)+1))
  | _, _ => none

theorem bump_body (fns : Fns) (x : Int) :
    evalExport 16 bumpDefinition.body fns [("X",.int x)] = .ok (.int (x+1)) := rfl

theorem twice_body (x : Int) :
    evalExport 16 twiceDefinition.body emitted [("X",.int x)] = .ok (.int ((x+1)+1)) := rfl

theorem twice_correct : CanonicalBodyCorrect program domain primitiveDomain emitted
    "FN2-TV-TWICE-BUMP" (fun _ result => ∃ n : Int, result = .int n) := by
  intro values admitted
  obtain ⟨_, x, rfl⟩ := admitted
  exact ⟨twiceDefinition, .int ((x+1)+1), rfl, rfl, twice_evaluates x, rfl,
    twice_body x, (x+1)+1, rfl⟩

theorem positive : domain "FN2-TV-TWICE-BUMP" [.int 4] ∧
    CanonicalExportEval program domain primitiveDomain "FN2-TV-TWICE-BUMP" [.int 4] (.int 6) ∧
    emitted "FN2-TV-TWICE-BUMP" [.int 4] = some (.int 6) :=
  ⟨⟨Or.inr rfl, 4, rfl⟩, twice_evaluates 4, rfl⟩

theorem input_domain_required : ¬ domain "FN2-TV-BUMP" [Val.nil] := by
  simp [domain, Val.nil]

def mutant : Fns
  | "FN2-TV-BUMP", [x] => some x
  | "FN2-TV-TWICE-BUMP", [.int x] => some (.int ((x+1)+1))
  | _, _ => none

theorem changed_callee_rejected : ¬ CanonicalBodyCorrect program domain primitiveDomain mutant
    "FN2-TV-BUMP" (fun _ result => ∃ n : Int, result = .int n) := by
  intro claimed
  obtain ⟨definition, v, resolved, _, _, dispatched, evaluated, _⟩ :=
    claimed [.int 4] ⟨Or.inl rfl, 4, rfl⟩
  have hd : definition = bumpDefinition := by simpa [program] using resolved.symm
  subst definition
  have hv : v = .int 5 := Except.ok.inj (evaluated.symm.trans (bump_body mutant 4))
  simp [mutant, hv] at dispatched

/-- The caller dispatch stays correct while its callee is changed. -/
theorem changed_composed_callee_rejected : ¬ CanonicalBodyCorrect program domain primitiveDomain mutant
    "FN2-TV-TWICE-BUMP" (fun _ result => ∃ n : Int, result = .int n) := by
  intro claimed
  obtain ⟨definition, v, resolved, _, _, dispatched, evaluated, _⟩ :=
    claimed [.int 4] ⟨Or.inr rfl, 4, rfl⟩
  have hd : definition = twiceDefinition := by simpa [program] using resolved.symm
  subst definition
  have actual : evalExport 16 twiceDefinition.body mutant [("X",.int 4)] = .ok (.int 4) := rfl
  have hv : v = .int 4 := Except.ok.inj (evaluated.symm.trans actual)
  simp [mutant, hv] at dispatched

/-- Removing the primitive-domain premise admits a represented NIL input:
native completion returns 1 but the canonical integer model refuses it. -/
def canonicalNil : Object := .symbol [67,79,77,77,79,78,45,76,73,83,80] [78,73,76]
theorem omitted_primitive_domain_rejected :
    RelatedArgs (fun o v => o.value? = some v) [canonicalNil, .integer 1] [Val.nil, .int 1] ∧
    nativeCall "BINARY-+" [Val.nil, .int 1] = some (.int 1) ∧
    ¬ (∃ result, canonicalPrimitive "BINARY-+" [canonicalNil, .integer 1] = some result ∧
                 result.value? = some (.int 1)) := by
  refine ⟨.cons rfl (.cons rfl .nil), rfl, ?_⟩
  rintro ⟨result, impossible, _⟩
  cases impossible

#print axioms addition_correspondence
#print axioms twice_correct
#print axioms positive
#print axioms input_domain_required
#print axioms changed_callee_rejected
#print axioms changed_composed_callee_rejected
#print axioms omitted_primitive_domain_rejected
end Fn2.ACL2.Translation.DomainControls
end
