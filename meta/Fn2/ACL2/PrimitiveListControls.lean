module
public import Fn2.ACL2.PrimitiveLists

@[expose] public section
namespace Fn2.ACL2.Translation.PrimitiveLists

def pairObject : Object := .cons (.integer 11) (.cons (.integer 22) objectNil)
def pairValue : Val := .cons (.int 11) (.cons (.int 22) Val.nil)
def paddedObject : Object := .cons (.integer 11) (.cons (.integer 22)
  (.cons objectNil (.cons (.integer 99) objectNil)))
def paddedValue : Val := .cons (.int 11) (.cons (.int 22)
  (.cons Val.nil (.cons (.int 99) Val.nil)))

theorem list_positive :
    RelatedArgs (fun (o : Object) (v : Val) => o.value? = some v)
      [.integer 3, .integer 99, pairObject] [.int 3, .int 99, pairValue] ∧
    listDomain "UPDATE-NTH" [.int 3, .int 99, pairValue] ∧
    listObjects "UPDATE-NTH" [.integer 3, .integer 99, pairObject] = some paddedObject ∧
    paddedObject.value? = some paddedValue ∧
    nativeCall "UPDATE-NTH" [.int 3, .int 99, pairValue] = some paddedValue ∧
    nativeCall "NTH" [.int 2, paddedValue] = some Val.nil ∧
    nativeCall "NTH" [.int 0, paddedValue] = some (.int 11) :=
  ⟨.cons rfl (.cons rfl (.cons rfl .nil)),
    Or.inr ⟨rfl, 3, .int 99, pairValue, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- Nat index is an actual premise: native ACL2 completion sends a negative
index to zero, whereas this partial canonical call interface refuses it. -/
theorem negative_index_domain_required :
    RelatedArgs (fun (o : Object) (v : Val) => o.value? = some v)
      [.integer (-1), pairObject] [.int (-1), pairValue] ∧
    ¬ listDomain "NTH" [.int (-1), pairValue] ∧
    nativeCall "NTH" [.int (-1), pairValue] = some (.int 11) ∧
    listObjects "NTH" [.integer (-1), pairObject] = none := by
  refine ⟨.cons rfl (.cons rfl .nil), ?_, rfl, rfl⟩
  rintro (⟨_, index, value, h⟩ | ⟨impossible, _⟩)
  · have impossible := congrArg (fun xs => (xs[0]!).toInt) h
    simp [Val.toInt] at impossible
  · exact (by decide : ("NTH" : String) ≠ "UPDATE-NTH") impossible

/-- Representation of inserted data cannot be dropped: a rational object
remains unsupported after insertion even when every list index is natural. -/
theorem inserted_representation_required :
    pairObject.value? = some pairValue ∧
    (Object.rational 1 2).value? = none ∧
    (objectUpdateNth 1 (.rational 1 2) pairObject).value? = none ∧
    nativeCall "UPDATE-NTH" [.int 1, .int 0, pairValue] =
      some (.cons (.int 11) (.cons (.int 0) Val.nil)) := ⟨rfl,rfl,rfl,rfl⟩

/-- The target update is retained but an unrelated sibling is corrupted. -/
def clobberedLists : String → List Object → Option Object
  | "UPDATE-NTH", [.integer index, inserted, object] =>
      if 0 ≤ index then some (objectUpdateNth 0 (.integer 999)
        (objectUpdateNth index.toNat inserted object)) else none
  | name, args => listObjects name args

theorem sibling_corruption_rejected : ¬ PrimitiveCorrespondence clobberedLists listDomain := by
  intro claimed
  obtain ⟨result, actual, represented⟩ := claimed "UPDATE-NTH"
    [.integer 1, .integer 99, pairObject] [.int 1, .int 99, pairValue]
    (.cons rfl (.cons rfl (.cons rfl .nil)))
    (Or.inr ⟨rfl, 1, .int 99, pairValue, rfl⟩)
    (.cons (.int 11) (.cons (.int 99) Val.nil)) rfl
  have result_eq : result = .cons (.integer 999) (.cons (.integer 99) objectNil) := by
    exact Option.some.inj actual.symm
  subst result
  cases represented

/-- Whole selected guard facts suffice for the actual read/update domains. -/
theorem guard_branches_positive :
    (Prim.integerp (.int 3)).truthy = true ∧
    (Prim.lt (.int 3) (.int 0)).truthy = false ∧
    listDomain "NTH" [.int 3, pairValue] ∧
    listDomain "UPDATE-NTH" [.int 3, .int 99, pairValue] :=
  ⟨rfl, rfl, nth_domain_of_guard_branches _ _ rfl rfl,
    update_nth_domain_of_guard_branches _ _ _ rfl rfl⟩

/-- Nonnegativity of the completed numeric value alone admits NIL. -/
theorem integer_guard_required :
    (Prim.lt Val.nil (.int 0)).truthy = false ∧
    (Prim.integerp Val.nil).truthy = false ∧
    ¬ (∃ n : Nat, Val.nil = .int n) := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨n, impossible⟩
  cases impossible

/-- An integer branch alone still admits negative indices. -/
theorem nonnegative_guard_required :
    (Prim.integerp (.int (-1))).truthy = true ∧
    (Prim.lt (.int (-1)) (.int 0)).truthy = true ∧
    ¬ (∃ n : Nat, Val.int (-1) = .int n) := by
  refine ⟨rfl, rfl, ?_⟩
  rintro ⟨n, impossible⟩
  have h := Val.int.inj impossible
  omega

#print axioms object_spine_correspondence
#print axioms nth_correspondence
#print axioms update_nth_correspondence
#print axioms list_primitive_correspondence
#print axioms list_positive
#print axioms negative_index_domain_required
#print axioms inserted_representation_required
#print axioms sibling_corruption_rejected
#print axioms natural_index_of_guard_branches
#print axioms nth_domain_of_guard_branches
#print axioms update_nth_domain_of_guard_branches
#print axioms guard_branches_positive
#print axioms integer_guard_required
#print axioms nonnegative_guard_required
end Fn2.ACL2.Translation.PrimitiveLists
end
