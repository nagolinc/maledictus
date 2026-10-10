import VcTermSortProofs.DerivedTraits

open Aeneas Aeneas.Std Result ControlFlow Error

namespace VcTermSort.Proofs

/-- Rebuild scalar list storage rather than identifying its traversal with the
    extraction model. Scalars themselves carry no recursively owned Term. -/
def compilerDerivedValueListClone {α : Type} : List α → List α
  | [] => []
  | head :: tail => head :: compilerDerivedValueListClone tail

theorem compiler_derived_value_list_clone_identity {α : Type} :
    ∀ values : List α, compilerDerivedValueListClone values = values
  | [] => by rfl
  | head :: tail => by
      simp [compilerDerivedValueListClone,
        compiler_derived_value_list_clone_identity tail]

def compilerDerivedScalarOptionClone {α : Type} : Option α → Option α
  | none => none
  | some value => some value

theorem compiler_derived_scalar_option_clone_identity {α : Type}
    (value : Option α) : compilerDerivedScalarOptionClone value = value := by
  cases value <;> rfl

/-- Int-enum descriptors preserve their immutable scalar metadata while
    reconstructing the member-list storage. -/
def compilerDerivedIntEnumDescriptorClone
    (descriptor : VcTermSort.IntEnumDescriptor) : VcTermSort.IntEnumDescriptor :=
  { «class» := descriptor.«class»,
    members := compilerDerivedValueListClone descriptor.members }

theorem compiler_derived_int_enum_descriptor_clone_identity
    (descriptor : VcTermSort.IntEnumDescriptor) :
    compilerDerivedIntEnumDescriptorClone descriptor = descriptor := by
  cases descriptor
  simp [compilerDerivedIntEnumDescriptorClone,
    compiler_derived_value_list_clone_identity]

mutual

/-- Independent structural specification of compiler-derived Term cloning.
    Every constructor is rebuilt. Recursive boxes, vectors, optional children,
    dictionary pairs, and permission-transfer receivers are traversed through
    the mutually defined storage functions below. This definition never calls
    the extraction-local identity clone model. -/
def compilerDerivedTermClone : VcTermSort.Term → VcTermSort.Term
  | .Bool value =>
      .Bool value
  | .Int value =>
      .Int value
  | .IntEnumValue descriptor value =>
      .IntEnumValue (compilerDerivedIntEnumDescriptorClone descriptor) (compilerDerivedTermClone value)
  | .IntEnumProjection value =>
      .IntEnumProjection (compilerDerivedTermClone value)
  | .IntEnumDomain value =>
      .IntEnumDomain (compilerDerivedTermClone value)
  | .IntEnumIdentity left right =>
      .IntEnumIdentity (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .String value =>
      .String value
  | .Bytes values =>
      .Bytes (compilerDerivedValueListClone values)
  | .Range values =>
      .Range (compilerDerivedValueListClone values)
  | .Unit =>
      .Unit
  | .NullReference =>
      .NullReference
  | .NominalReference symbolName className =>
      .NominalReference symbolName className
  | .ClassLiteral symbolName =>
      .ClassLiteral symbolName
  | .RuntimeClass value =>
      .RuntimeClass (compilerDerivedTermClone value)
  | .PredicateInstance symbolName arguments =>
      .PredicateInstance symbolName (compilerDerivedTermCloneList arguments)
  | .ClassSubtype actual expected =>
      .ClassSubtype (compilerDerivedTermClone actual) (compilerDerivedTermClone expected)
  | .Variable symbolName sort =>
      .Variable symbolName (compilerDerivedSortClone sort)
  | .FieldRead heap receiver field sort =>
      .FieldRead heap (compilerDerivedTermClone receiver) field (compilerDerivedSortClone sort)
  | .PermissionAtLeast mask receiver field numerator denominator =>
      .PermissionAtLeast mask (compilerDerivedTermClone receiver) field numerator denominator
  | .PermissionAtMost mask receiver field numerator denominator =>
      .PermissionAtMost mask (compilerDerivedTermClone receiver) field numerator denominator
  | .PermissionPositive mask receiver field =>
      .PermissionPositive mask (compilerDerivedTermClone receiver) field
  | .PermissionMaskValid mask field =>
      .PermissionMaskValid mask field
  | .PermissionMaskTransition before after field consumed produced =>
      .PermissionMaskTransition before after field (compilerDerivedTransferCloneList consumed) (compilerDerivedTransferCloneList produced)
  | .Not value =>
      .Not (compilerDerivedTermClone value)
  | .And values =>
      .And (compilerDerivedTermCloneList values)
  | .Or values =>
      .Or (compilerDerivedTermCloneList values)
  | .Implies left right =>
      .Implies (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .IfThenElse condition yes no =>
      .IfThenElse (compilerDerivedTermClone condition) (compilerDerivedTermClone yes) (compilerDerivedTermClone no)
  | .Equal left right =>
      .Equal (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .Less left right =>
      .Less (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .LessEqual left right =>
      .LessEqual (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .Greater left right =>
      .Greater (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .GreaterEqual left right =>
      .GreaterEqual (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .Add left right =>
      .Add (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .Subtract left right =>
      .Subtract (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .Multiply left right =>
      .Multiply (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .FloorDivideByPositive value divisor =>
      .FloorDivideByPositive (compilerDerivedTermClone value) divisor
  | .Negate value =>
      .Negate (compilerDerivedTermClone value)
  | .StringConcat values =>
      .StringConcat (compilerDerivedTermCloneList values)
  | .StringLength value =>
      .StringLength (compilerDerivedTermClone value)
  | .StringSlice value start length =>
      .StringSlice (compilerDerivedTermClone value) (compilerDerivedTermClone start) (compilerDerivedTermClone length)
  | .BytesConcat values =>
      .BytesConcat (compilerDerivedTermCloneList values)
  | .BytesLength value =>
      .BytesLength (compilerDerivedTermClone value)
  | .BytesGet value index =>
      .BytesGet (compilerDerivedTermClone value) (compilerDerivedTermClone index)
  | .Tuple values =>
      .Tuple (compilerDerivedTermCloneList values)
  | .TupleGet value index =>
      .TupleGet (compilerDerivedTermClone value) index
  | .VariadicTuple sort values =>
      .VariadicTuple (compilerDerivedSortClone sort) (compilerDerivedTermCloneList values)
  | .VariadicTupleLength value =>
      .VariadicTupleLength (compilerDerivedTermClone value)
  | .VariadicTupleGet value index =>
      .VariadicTupleGet (compilerDerivedTermClone value) (compilerDerivedTermClone index)
  | .VariadicTupleSlice value start stop step =>
      .VariadicTupleSlice (compilerDerivedTermClone value) (compilerDerivedScalarOptionClone start) (compilerDerivedScalarOptionClone stop) step
  | .List sort values =>
      .List (compilerDerivedSortClone sort) (compilerDerivedTermCloneList values)
  | .ListLength value =>
      .ListLength (compilerDerivedTermClone value)
  | .ListGet value index =>
      .ListGet (compilerDerivedTermClone value) (compilerDerivedTermClone index)
  | .ListContains value member =>
      .ListContains (compilerDerivedTermClone value) (compilerDerivedTermClone member)
  | .ListSlice value start stop step =>
      .ListSlice (compilerDerivedTermClone value) (compilerDerivedScalarOptionClone start) (compilerDerivedScalarOptionClone stop) step
  | .ListConcat left right =>
      .ListConcat (compilerDerivedTermClone left) (compilerDerivedTermClone right)
  | .ListSum value =>
      .ListSum (compilerDerivedTermClone value)
  | .ListSorted value =>
      .ListSorted (compilerDerivedTermClone value)
  | .ListComprehension binder source bindingName sort mapper filter =>
      .ListComprehension binder (compilerDerivedTermClone source) bindingName (compilerDerivedSortClone sort) (compilerDerivedTermClone mapper) (compilerDerivedTermCloneOption filter)
  | .SetComprehension binder source bindingName sort mapper filter =>
      .SetComprehension binder (compilerDerivedTermClone source) bindingName (compilerDerivedSortClone sort) (compilerDerivedTermClone mapper) (compilerDerivedTermCloneOption filter)
  | .SetLength value =>
      .SetLength (compilerDerivedTermClone value)
  | .SetContains value member =>
      .SetContains (compilerDerivedTermClone value) (compilerDerivedTermClone member)
  | .DictComprehension binder source bindingName keySort valueSort key value filter =>
      .DictComprehension binder (compilerDerivedTermClone source) bindingName (compilerDerivedSortClone keySort) (compilerDerivedSortClone valueSort) (compilerDerivedTermClone key) (compilerDerivedTermClone value) (compilerDerivedTermCloneOption filter)
  | .DictLength value =>
      .DictLength (compilerDerivedTermClone value)
  | .DictContains value key =>
      .DictContains (compilerDerivedTermClone value) (compilerDerivedTermClone key)
  | .DictGet value key =>
      .DictGet (compilerDerivedTermClone value) (compilerDerivedTermClone key)
  | .ForAll binder sort body =>
      .ForAll binder (compilerDerivedSortClone sort) (compilerDerivedTermClone body)
  | .FiniteDict keySort valueSort entries =>
      .FiniteDict (compilerDerivedSortClone keySort) (compilerDerivedSortClone valueSort) (compilerDerivedTermClonePairs entries)
  | .DictKeys sort keys =>
      .DictKeys (compilerDerivedSortClone sort) (compilerDerivedTermCloneList keys)

def compilerDerivedTransferClone :
    VcTermSort.PermissionTransferAmount → VcTermSort.PermissionTransferAmount
  | .mk receiver numerator denominator =>
      .mk (compilerDerivedTermClone receiver) numerator denominator

def compilerDerivedTermCloneList : List VcTermSort.Term → List VcTermSort.Term
  | [] => []
  | head :: tail => compilerDerivedTermClone head :: compilerDerivedTermCloneList tail

def compilerDerivedTransferCloneList :
    List VcTermSort.PermissionTransferAmount → List VcTermSort.PermissionTransferAmount
  | [] => []
  | head :: tail => compilerDerivedTransferClone head :: compilerDerivedTransferCloneList tail

def compilerDerivedTermClonePair :
    VcTermSort.Term × VcTermSort.Term → VcTermSort.Term × VcTermSort.Term
  | (key, value) => (compilerDerivedTermClone key, compilerDerivedTermClone value)

def compilerDerivedTermClonePairs :
    List (VcTermSort.Term × VcTermSort.Term) → List (VcTermSort.Term × VcTermSort.Term)
  | [] => []
  | head :: tail => compilerDerivedTermClonePair head :: compilerDerivedTermClonePairs tail

def compilerDerivedTermCloneOption : Option VcTermSort.Term → Option VcTermSort.Term
  | none => none
  | some value => some (compilerDerivedTermClone value)

end

mutual

/-- Every finite constructor and recursive storage shape is preserved by the
    independent compiler-derived clone traversal. -/
theorem compiler_derived_term_clone_identity : ∀ term : VcTermSort.Term,
    compilerDerivedTermClone term = term
  | .Bool value => by
      rfl
  | .Int value => by
      rfl
  | .IntEnumValue descriptor value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_int_enum_descriptor_clone_identity descriptor,
        compiler_derived_term_clone_identity value]
  | .IntEnumProjection value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .IntEnumDomain value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .IntEnumIdentity left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .String value => by
      rfl
  | .Bytes values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_value_list_clone_identity values]
  | .Range values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_value_list_clone_identity values]
  | .Unit => by
      rfl
  | .NullReference => by
      rfl
  | .NominalReference symbolName className => by
      rfl
  | .ClassLiteral symbolName => by
      rfl
  | .RuntimeClass value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .PredicateInstance symbolName arguments => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity arguments]
  | .ClassSubtype actual expected => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity actual,
        compiler_derived_term_clone_identity expected]
  | .Variable symbolName sort => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity sort]
  | .FieldRead heap receiver field sort => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity receiver,
        compiler_derived_sort_clone_identity sort]
  | .PermissionAtLeast mask receiver field numerator denominator => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity receiver]
  | .PermissionAtMost mask receiver field numerator denominator => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity receiver]
  | .PermissionPositive mask receiver field => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity receiver]
  | .PermissionMaskValid mask field => by
      rfl
  | .PermissionMaskTransition before after field consumed produced => by
      simp only [compilerDerivedTermClone,
        compiler_derived_transfer_clone_list_identity consumed,
        compiler_derived_transfer_clone_list_identity produced]
  | .Not value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .And values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity values]
  | .Or values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity values]
  | .Implies left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .IfThenElse condition yes no => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity condition,
        compiler_derived_term_clone_identity yes,
        compiler_derived_term_clone_identity no]
  | .Equal left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .Less left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .LessEqual left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .Greater left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .GreaterEqual left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .Add left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .Subtract left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .Multiply left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .FloorDivideByPositive value divisor => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .Negate value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .StringConcat values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity values]
  | .StringLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .StringSlice value start length => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity start,
        compiler_derived_term_clone_identity length]
  | .BytesConcat values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity values]
  | .BytesLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .BytesGet value index => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity index]
  | .Tuple values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_list_identity values]
  | .TupleGet value index => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .VariadicTuple sort values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_list_identity values]
  | .VariadicTupleLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .VariadicTupleGet value index => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity index]
  | .VariadicTupleSlice value start stop step => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_scalar_option_clone_identity start,
        compiler_derived_scalar_option_clone_identity stop]
  | .List sort values => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_list_identity values]
  | .ListLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .ListGet value index => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity index]
  | .ListContains value member => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity member]
  | .ListSlice value start stop step => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_scalar_option_clone_identity start,
        compiler_derived_scalar_option_clone_identity stop]
  | .ListConcat left right => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity left,
        compiler_derived_term_clone_identity right]
  | .ListSum value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .ListSorted value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .ListComprehension binder source bindingName sort mapper filter => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity source,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_identity mapper,
        compiler_derived_term_clone_option_identity filter]
  | .SetComprehension binder source bindingName sort mapper filter => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity source,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_identity mapper,
        compiler_derived_term_clone_option_identity filter]
  | .SetLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .SetContains value member => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity member]
  | .DictComprehension binder source bindingName keySort valueSort key value filter => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity source,
        compiler_derived_sort_clone_identity keySort,
        compiler_derived_sort_clone_identity valueSort,
        compiler_derived_term_clone_identity key,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_option_identity filter]
  | .DictLength value => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value]
  | .DictContains value key => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity key]
  | .DictGet value key => by
      simp only [compilerDerivedTermClone,
        compiler_derived_term_clone_identity value,
        compiler_derived_term_clone_identity key]
  | .ForAll binder sort body => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_identity body]
  | .FiniteDict keySort valueSort entries => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity keySort,
        compiler_derived_sort_clone_identity valueSort,
        compiler_derived_term_clone_pairs_identity entries]
  | .DictKeys sort keys => by
      simp only [compilerDerivedTermClone,
        compiler_derived_sort_clone_identity sort,
        compiler_derived_term_clone_list_identity keys]

theorem compiler_derived_transfer_clone_identity :
    ∀ amount : VcTermSort.PermissionTransferAmount,
      compilerDerivedTransferClone amount = amount
  | .mk receiver numerator denominator => by
      simp only [compilerDerivedTransferClone,
        compiler_derived_term_clone_identity receiver]

theorem compiler_derived_term_clone_list_identity :
    ∀ values : List VcTermSort.Term, compilerDerivedTermCloneList values = values
  | [] => by rfl
  | head :: tail => by
      simp only [compilerDerivedTermCloneList,
        compiler_derived_term_clone_identity head,
        compiler_derived_term_clone_list_identity tail]

theorem compiler_derived_transfer_clone_list_identity :
    ∀ values : List VcTermSort.PermissionTransferAmount,
      compilerDerivedTransferCloneList values = values
  | [] => by rfl
  | head :: tail => by
      simp only [compilerDerivedTransferCloneList,
        compiler_derived_transfer_clone_identity head,
        compiler_derived_transfer_clone_list_identity tail]

theorem compiler_derived_term_clone_pair_identity :
    ∀ entry : VcTermSort.Term × VcTermSort.Term,
      compilerDerivedTermClonePair entry = entry
  | (key, value) => by
      simp only [compilerDerivedTermClonePair,
        compiler_derived_term_clone_identity key,
        compiler_derived_term_clone_identity value]

theorem compiler_derived_term_clone_pairs_identity :
    ∀ entries : List (VcTermSort.Term × VcTermSort.Term),
      compilerDerivedTermClonePairs entries = entries
  | [] => by rfl
  | head :: tail => by
      simp only [compilerDerivedTermClonePairs,
        compiler_derived_term_clone_pair_identity head,
        compiler_derived_term_clone_pairs_identity tail]

theorem compiler_derived_term_clone_option_identity :
    ∀ value : Option VcTermSort.Term, compilerDerivedTermCloneOption value = value
  | none => by rfl
  | some value => by
      simp only [compilerDerivedTermCloneOption,
        compiler_derived_term_clone_identity value]

end

/-- The immutable extraction model agrees with the independently reconstructed
    compiler-derived traversal on every Term, including permission transitions.
    This is a semantic value theorem, not an allocation/resource-cost bound. -/
theorem term_clone_model_refines_compiler_derive (term : VcTermSort.Term) :
    VcTermSort.Term.Insts.CoreCloneClone.clone term =
      .ok (compilerDerivedTermClone term) := by
  rw [compiler_derived_term_clone_identity]
  rfl

end VcTermSort.Proofs
