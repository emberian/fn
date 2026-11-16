module
public import Fn2.ACL2.MemberSymbolListEvaluation
public import Fn2.ACL2.PrimitiveSymbols
import all Fn2.Instances.LayerAWorld.S25_d2to3
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveMemberSymbols
open Fn2.Instances.LayerAWorld

/-- ACL2 MEMBER-EQUAL's canonical object model compares object identity and
returns the original suffix. No decoded Val comparison implements this model. -/
def memberObject (key : Object) : Object → Object
  | .cons head tail => if key = head then .cons head tail else memberObject key tail
  | _ => PrimitiveSymbols.canonicalNil

private theorem symbol_equality {key head : Object} {value : Val} {name : String}
    (keyRep : key.value? = some value) (headRep : head.value? = some (.sym name)) :
    (key = head) ↔ (value = .sym name) := by
  constructor
  · intro same
    rw [same] at keyRep
    exact Option.some.inj (keyRep.symm.trans headRep)
  · intro same
    have keySymbol := keyRep.trans (congrArg some same)
    exact Option.some.inj ((object_value_symbol_roundtrip keySymbol).symm.trans
      (object_value_symbol_roundtrip headRep))

/-- Each literal is represented with its exact package/name; the entire proper
list is constructed from those objects, with canonical COMMON-LISP NIL. -/
theorem literal_list_represented {literals : List Object} {names : List String}
    (represented : RelatedArgs (fun object name => object.value? = some (.sym name)) literals names) :
    (MemberExecEvaluation.objects literals).value? = some (Val.ofList (names.map Val.sym)) := by
  induction represented with
  | nil => rfl
  | @cons head name tail names headRep tailRep ih =>
    simp only [MemberExecEvaluation.objects, Object.value?, headRep, ih, List.map,
      Val.ofList]
    rfl

/-- Whole canonical suffix correspondence on the actual literal-list domain.
The key is arbitrary but must retain its caller's representation premise. -/
theorem canonical_member {key : Object} {value : Val}
    (keyRep : key.value? = some value) {literals : List Object} {names : List String}
    (represented : RelatedArgs (fun object name => object.value? = some (.sym name)) literals names) :
    (memberObject key (MemberExecEvaluation.objects literals)).value? =
      some (Native.memberEqual value (Val.ofList (names.map Val.sym))) := by
  induction represented with
  | nil => rfl
  | @cons head name tail names headRep tailRep ih =>
    have reflection := symbol_equality keyRep headRep
    by_cases same : value = .sym name
    · have objectSame := reflection.mpr same
      simpa [memberObject, MemberExecEvaluation.objects, objectSame,
        Native.memberEqual, Val.ofList, same] using
        literal_list_represented (.cons headRep tailRep)
    · have objectDifferent : key ≠ head := fun h => same (reflection.mp h)
      simpa [memberObject, MemberExecEvaluation.objects, objectDifferent,
        Native.memberEqual, Val.ofList, same] using ih

/-- The same canonical suffix represents BOTH the logical MEMBER-EQUAL native
call and the actual emitted MEMBER-EQ-EXEC result. This is the helper's local
logic/exec seam; packet identity and whole caller composition remain required. -/
theorem canonical_member_emitted {key : Object} {value : Val}
    (keyRep : key.value? = some value) {literals : List Object} {names : List String}
    (represented : RelatedArgs (fun object name => object.value? = some (.sym name)) literals names) :
    (memberObject key (MemberExecEvaluation.objects literals)).value? =
      some («MEMBER-EQ-EXEC» value (Val.ofList (names.map Val.sym))) ∧
    nativeCall "MEMBER-EQUAL" [value, Val.ofList (names.map Val.sym)] =
      some («MEMBER-EQ-EXEC» value (Val.ofList (names.map Val.sym))) := by
  rw [MemberSymbolListEvaluation.emitted_eq_native]
  exact ⟨canonical_member keyRep represented, rfl⟩

#print axioms literal_list_represented
#print axioms canonical_member
#print axioms canonical_member_emitted
end Fn2.ACL2.Translation.PrimitiveMemberSymbols
end
