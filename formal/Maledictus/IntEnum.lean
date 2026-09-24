import Maledictus.Kernel

namespace Maledictus

/-!
# Finite integer-enum value algebra

This model records the bounded algebra implemented by the production IntEnum frontend. An enum
value retains its declaring descriptor and its integer projection. Python numeric comparisons use
only the projection, while singleton identity additionally requires the same enum class.

This file proves the algebra itself. It deliberately makes no Rust/frontend correspondence claim.
-/

structure IntEnumMember where
  name : String
  value : Int
  deriving DecidableEq

structure IntEnumDescriptor where
  className : String
  members : List IntEnumMember
  deriving DecidableEq

structure IntEnumValue where
  descriptor : IntEnumDescriptor
  value : Int
  deriving DecidableEq

def intEnumMemberNamesUnique (descriptor : IntEnumDescriptor) : Prop :=
  descriptor.members.Pairwise fun left right => Not (left.name = right.name)

def intEnumMemberValuesUnique (descriptor : IntEnumDescriptor) : Prop :=
  descriptor.members.Pairwise fun left right => Not (left.value = right.value)

def validIntEnumDescriptor (descriptor : IntEnumDescriptor) : Prop :=
  Not (descriptor.className = "") /\
    Not (descriptor.members = []) /\
    intEnumMemberNamesUnique descriptor /\
    intEnumMemberValuesUnique descriptor

def intEnumInDomain (value : IntEnumValue) : Bool :=
  value.descriptor.members.any fun member => member.value == value.value

def intEnumProject (value : IntEnumValue) : Int := value.value

def intEnumNumericEqual (left right : IntEnumValue) : Bool :=
  intEnumProject left == intEnumProject right

def intEnumIdentity (left right : IntEnumValue) : Bool :=
  left.descriptor == right.descriptor &&
    left.value == right.value

def constructIntEnum? (descriptor : IntEnumDescriptor) (value : Int) : Option IntEnumValue :=
  let candidate := { descriptor, value }
  if intEnumInDomain candidate then some candidate else none

def declaredIntEnumMember
    (descriptor : IntEnumDescriptor) (member : IntEnumMember) : IntEnumValue :=
  { descriptor, value := member.value }

theorem int_enum_projection_is_numeric_carrier (value : IntEnumValue) :
    intEnumProject value = value.value := by
  rfl

theorem int_enum_numeric_equality_ignores_class
    (left right : IntEnumValue) (sameValue : left.value = right.value) :
    intEnumNumericEqual left right = true := by
  simp [intEnumNumericEqual, intEnumProject, sameValue]

theorem int_enum_cross_class_identity_is_false
    (left right : IntEnumValue)
    (differentClass : Not (left.descriptor.className = right.descriptor.className)) :
    intEnumIdentity left right = false := by
  have differentDescriptor : Not (left.descriptor = right.descriptor) := by
    intro sameDescriptor
    exact differentClass (congrArg IntEnumDescriptor.className sameDescriptor)
  simp [intEnumIdentity, differentDescriptor]

theorem int_enum_same_descriptor_value_identity_is_true
    (left right : IntEnumValue)
    (sameDescriptor : left.descriptor = right.descriptor)
    (sameValue : left.value = right.value) :
    intEnumIdentity left right = true := by
  simp [intEnumIdentity, sameDescriptor, sameValue]

theorem int_enum_cross_class_numeric_equality_does_not_imply_identity
    (left right : IntEnumValue)
    (sameValue : left.value = right.value)
    (differentClass : Not (left.descriptor.className = right.descriptor.className)) :
    intEnumNumericEqual left right = true /\ intEnumIdentity left right = false := by
  constructor
  . exact int_enum_numeric_equality_ignores_class left right sameValue
  . exact int_enum_cross_class_identity_is_false left right differentClass

theorem construct_int_enum_succeeds_exactly_in_domain
    (descriptor : IntEnumDescriptor) (value : Int) :
    (constructIntEnum? descriptor value).isSome = intEnumInDomain { descriptor, value } := by
  cases inDomain : intEnumInDomain { descriptor, value } <;>
    simp [constructIntEnum?, inDomain]

theorem declared_int_enum_member_is_in_domain
    (descriptor : IntEnumDescriptor) (member : IntEnumMember)
    (present : List.Mem member descriptor.members) :
    intEnumInDomain (declaredIntEnumMember descriptor member) = true := by
  simp [intEnumInDomain, declaredIntEnumMember]
  exact Exists.intro member (And.intro present rfl)

end Maledictus
