module
public import Fn2.ACL2.PrimitiveMemberSymbols
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveMemberSymbolsControls
open PrimitiveMemberSymbols

def sizeObject : Object := .symbol [75,69,89,87,79,82,68] [83,73,90,69]
def fullObject : Object := .symbol [75,69,89,87,79,82,68] [70,85,76,76]
def literals : Object := MemberExecEvaluation.objects [sizeObject, fullObject]

theorem represented :
    RelatedArgs (fun object name => object.value? = some (.sym name))
      [sizeObject, fullObject] [":SIZE", ":FULL"] := .cons rfl (.cons rfl .nil)

/-- Matching the second element returns that exact suffix, not a Boolean. -/
theorem actual_suffix :
    memberObject fullObject literals = MemberExecEvaluation.objects [fullObject] ∧
    (memberObject fullObject literals).value? = some (Val.ofList [.sym ":FULL"]) := by
  constructor <;> decide +kernel

theorem arbitrary_integer_key :
    memberObject (.integer 7) literals = PrimitiveSymbols.canonicalNil ∧
    (memberObject (.integer 7) literals).value? = some Val.nil := by
  constructor <;> decide +kernel

/-- Former lossy printed-name collision cannot turn ACL2 :SIZE into KEYWORD SIZE. -/
def wrongPackage : Object := .symbol [65,67,76,50] [58,83,73,90,69]
theorem wrong_package_refused :
    memberObject wrongPackage literals = PrimitiveSymbols.canonicalNil ∧
    wrongPackage.value? = some (.sym "ACL2:::SIZE") := by
  constructor <;> decide +kernel

theorem boolean_instead_of_suffix_refused :
    (memberObject fullObject literals).value? ≠ some Val.t := by decide +kernel

theorem unrepresented_key_refused :
    ¬ ∃ value, (Object.rational 1 2).value? = some value := by
  rintro ⟨value, h⟩
  cases h

/-- The consumer theorem uses the actual emitted function and logical native call. -/
theorem actual_logic_exec_suffix :
    (memberObject fullObject (MemberExecEvaluation.objects [sizeObject, fullObject])).value? =
      some (Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC» (.sym ":FULL")
        (Val.ofList [Val.sym ":SIZE", Val.sym ":FULL"])) ∧
    nativeCall "MEMBER-EQUAL" [.sym ":FULL", Val.ofList [Val.sym ":SIZE", Val.sym ":FULL"]] =
      some (Fn2.Instances.LayerAWorld.«MEMBER-EQ-EXEC» (.sym ":FULL")
        (Val.ofList [Val.sym ":SIZE", Val.sym ":FULL"])) :=
  canonical_member_emitted (key := fullObject) (value := .sym ":FULL") (by rfl) represented

#print axioms actual_suffix
#print axioms arbitrary_integer_key
#print axioms wrong_package_refused
#print axioms boolean_instead_of_suffix_refused
#print axioms unrepresented_key_refused
#print axioms actual_logic_exec_suffix
end Fn2.ACL2.Translation.PrimitiveMemberSymbolsControls
end
