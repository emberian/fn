module
public import Fn2.ACL2.MemberBodyCorrect
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.MemberBodyCorrectControls
open Fn2.ACL2.Translation Fn2.Instances.LayerAWorld
open MemberExecEvaluation MemberBodyCorrect

/-- The acceptance-list shape used by generated CNS :do routing. This proves
its MEMBER call composition, not that an unqualified CNS packet has this site. -/
def accepted : Val := Val.ofList [.sym ":OK", .sym ":RETIRED"]
def acceptanceCall : Term := .app "MEMBER-EQ-EXEC" [.var "STATUS", .quote accepted]

theorem acceptance_call (status : String) :
    ∃ value,
      CanonicalEval program domain primitiveDomain [("STATUS", .sym status)] acceptanceCall value ∧
      eval fns [("STATUS", .sym status)] acceptanceCall 33 = .ok value ∧
      MemberBodyCorrect.result [.sym status, accepted] value := by
  apply canonical_call_correct (name := "MEMBER-EQ-EXEC")
    (values := [.sym status, accepted]) (fuel := 32)
  · decide
  · decide
  · rfl
  · exact .cons (.var rfl) (.cons (.quote) .nil)
  · rfl
  · exact ⟨[.sym ":OK", .sym ":RETIRED"], rfl⟩
  · exact body_correct

theorem actual_dispatch : fns "MEMBER-EQ-EXEC" [.sym ":OK", accepted] = some accepted := by
  rw [«MEMBER-EQ-EXEC».fns_eq, emitted_eq_native]
  rfl

/-- Mutation changes only the concrete MEMBER dispatch result. -/
def changedDispatch (name : String) (values : List Val) : Option Val :=
  if name = "MEMBER-EQ-EXEC" then some Val.nil else fns name values

theorem changed_dispatch_refused :
    changedDispatch "MEMBER-EQ-EXEC" [.sym ":OK", accepted] ≠
      fns "MEMBER-EQ-EXEC" [.sym ":OK", accepted] := by
  rw [actual_dispatch]
  decide

theorem changed_body_correct_refused :
    ¬ CanonicalBodyCorrect program domain primitiveDomain changedDispatch
      "MEMBER-EQ-EXEC" MemberBodyCorrect.result := by
  intro h
  obtain ⟨definition, value, _, _, _, dispatched, _, post⟩ :=
    h [.sym ":OK", accepted] ⟨[.sym ":OK", .sym ":RETIRED"], rfl⟩
  have valueNil : value = Val.nil := Option.some.inj dispatched.symm
  obtain ⟨key, xs, inputs, valueResult⟩ := post
  have same : Native.memberEqual (.sym key) (Val.ofList xs) = accepted := by
    have pair := List.cons.inj inputs
    have tail := List.cons.inj pair.2
    rw [← pair.1, ← tail.1]
    rfl
  have impossible : accepted = Val.nil := same.symm.trans (valueResult.symm.trans valueNil)
  cases impossible

#print axioms changed_body_correct_refused
#print axioms acceptance_call
#print axioms actual_dispatch
#print axioms changed_dispatch_refused
end Fn2.ACL2.MemberBodyCorrectControls
end
