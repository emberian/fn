module
public import Fn2.ACL2.PrimitiveSymbols
import all Init.Data.String.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveSymbolControls
open PrimitiveSymbols

/-- These are distinct ACL2 symbols, not alternate spellings of one imported
symbol. The legacy Val adapter erases this distinction. -/
def keywordSize : Object := .symbol [75,69,89,87,79,82,68] [83,73,90,69]
def acl2ColonSize : Object := .symbol [65,67,76,50] [58,83,73,90,69]
theorem distinct_objects : keywordSize ≠ acl2ColonSize := by decide
/-- The old syntactic-name adapter really did identify these symbols. It must
remain unavailable as a data decoder. -/
theorem old_adapter_collision :
    keywordSize.name? = acl2ColonSize.name? := by decide

theorem repaired_presentations :
    keywordSize.value? = some (.sym ":SIZE") ∧
    acl2ColonSize.value? = some (.sym "ACL2:::SIZE") := by decide

theorem actual_equal_agrees :
    equalObjects "EQUAL" [keywordSize, acl2ColonSize] = some canonicalNil ∧
    nativeCall "EQUAL" [.sym ":SIZE", .sym "ACL2:::SIZE"] = some Val.nil ∧
    canonicalNil.value? = some Val.nil := by decide

/-- No caller premise can hide a package collision: the checked decoder itself
has a unique inverse for every accepted symbolic value. -/
theorem symbol_objects_injective {p n q m : List Nat} {encoded : String}
    (left : (Object.symbol p n).value? = some (.sym encoded))
    (right : (Object.symbol q m).value? = some (.sym encoded)) :
    Object.symbol p n = Object.symbol q m := by
  exact Option.some.inj ((symbol_value_roundtrip left).symm.trans
    (symbol_value_roundtrip right))

theorem nil_packages_remain_distinct :
    canonicalNil.value? = some Val.nil ∧
    (Object.symbol [65,67,76,50] [78,73,76]).value? = some (.sym "ACL2::NIL") ∧
    (Object.symbol [75,69,89,87,79,82,68] [78,73,76]).value? = some (.sym ":NIL") ∧
    (Val.sym "ACL2::NIL").truthy = true ∧
    (Val.sym ":NIL").truthy = true := by decide

/-- Separators inside names cannot redirect the fixed package prefix. -/
theorem embedded_separators_remain_distinct :
    (Object.symbol [65,67,76,50] [67,79,77,77,79,78,45,76,73,83,80,58,58,84]).value? =
      some (.sym "ACL2::COMMON-LISP::T") ∧
    canonicalTrue.value? = some Val.t := by decide

#print axioms symbol_objects_injective
#print axioms actual_equal_agrees
end Fn2.ACL2.Translation.PrimitiveSymbolControls
end
