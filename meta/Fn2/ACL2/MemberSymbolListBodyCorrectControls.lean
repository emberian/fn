module
public import Fn2.ACL2.MemberSymbolListBodyCorrect
@[expose] public section
namespace Fn2.ACL2.MemberSymbolListBodyCorrectControls
open Fn2.ACL2.Translation Fn2.Instances.LayerAWorld
open MemberSymbolListBodyCorrect

def literals : Val := Val.ofList [.sym ":SIZE", .sym ":FULL"]

/-- The actual helper has guard T: non-symbol RC must remain admitted. -/
theorem nonsymbol_positive :
    domain "MEMBER-EQ-EXEC" [.int 7, literals] ∧
    CanonicalExportEval MemberExecEvaluation.program domain primitiveDomain
      "MEMBER-EQ-EXEC" [.int 7, literals] Val.nil := by
  refine ⟨⟨[":SIZE", ":FULL"], rfl⟩, ?_⟩
  exact closed_evaluation (.int 7) [":SIZE", ":FULL"]

theorem cons_key_positive :
    domain "MEMBER-EQ-EXEC" [.cons (.int 1) Val.nil, literals] ∧
    CanonicalExportEval MemberExecEvaluation.program domain primitiveDomain
      "MEMBER-EQ-EXEC" [.cons (.int 1) Val.nil, literals] Val.nil := by
  exact ⟨⟨[":SIZE", ":FULL"], rfl⟩,
    closed_evaluation (.cons (.int 1) Val.nil) [":SIZE", ":FULL"]⟩

theorem nonsymbol_element_refused :
    ¬ domain "MEMBER-EQ-EXEC" [.int 7, Val.ofList [.int 7]] := by
  rintro ⟨names, h⟩
  cases names with
  | nil => cases h
  | cons name tail => cases h

theorem improper_list_refused :
    ¬ domain "MEMBER-EQ-EXEC" [.int 7, .cons (.sym ":SIZE") (.int 4)] := by
  rintro ⟨names, h⟩
  cases names with
  | nil => cases h
  | cons name tail =>
    cases tail with
    | nil => cases h
    | cons next rest => cases h

def changedDispatch (name : String) (values : List Val) : Option Val :=
  if name = "MEMBER-EQ-EXEC" then some Val.t else fns name values

theorem changed_body_correct_refused :
    ¬ CanonicalBodyCorrect MemberExecEvaluation.program domain primitiveDomain
      changedDispatch "MEMBER-EQ-EXEC" result := by
  intro h
  obtain ⟨definition, value, _, _, _, dispatched, _, post⟩ :=
    h [.int 7, literals] ⟨[":SIZE", ":FULL"], rfl⟩
  have valueT : value = Val.t := Option.some.inj dispatched.symm
  obtain ⟨key, names, inputs, output⟩ := post
  have pair := List.cons.inj inputs
  have tail := List.cons.inj pair.2
  have actual : Native.memberEqual key (Val.ofList (names.map Val.sym)) = Val.nil := by
    rw [← pair.1, ← tail.1]
    rfl
  have impossible : Val.nil = Val.t := actual.symm.trans (output.symm.trans valueT)
  exact (by decide : Val.nil ≠ Val.t) impossible

#print axioms nonsymbol_positive
#print axioms cons_key_positive
#print axioms nonsymbol_element_refused
#print axioms improper_list_refused
#print axioms changed_body_correct_refused
end Fn2.ACL2.MemberSymbolListBodyCorrectControls
end
