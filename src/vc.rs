//! Language-neutral scalar verification conditions.

use std::num::NonZeroI128;

use serde::{Deserialize, Deserializer, Serialize};

// Internally tagged enums are buffered by Serde before their variant fields
// are decoded. Decode through serde_json's arbitrary-precision Number so the
// buffer does not narrow an exact Python integer to i64/u64.
fn deserialize_optional_i128<'de, D>(deserializer: D) -> Result<Option<i128>, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<serde_json::Number>::deserialize(deserializer)?
        .map(|number| {
            number.as_i128().ok_or_else(|| {
                serde::de::Error::custom("static slice bound must be an exact i128 integer")
            })
        })
        .transpose()
}

fn deserialize_nonzero_i128<'de, D>(deserializer: D) -> Result<NonZeroI128, D::Error>
where
    D: Deserializer<'de>,
{
    let number = serde_json::Number::deserialize(deserializer)?;
    let value = number.as_i128().ok_or_else(|| {
        serde::de::Error::custom("static slice step must be an exact i128 integer")
    })?;
    NonZeroI128::new(value)
        .ok_or_else(|| serde::de::Error::custom("static slice step cannot be zero"))
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Sort {
    Bool,
    Int,
    /// Python's binary floating-point value domain. The current heap fragment treats these as
    /// opaque typed values; arithmetic is not admitted until IEEE-754 semantics are modeled.
    Float,
    String,
    Unit,
    Reference,
    Class,
    Bytes,
    Range,
    Tuple(Vec<Sort>),
    /// Python's immutable homogeneous variable-length tuple (`Tuple[T, ...]`).
    /// This remains distinct from both a fixed heterogeneous tuple and a
    /// mutable homogeneous list throughout the VC pipeline.
    VariadicTuple(Box<Sort>),
    List(Box<Sort>),
    Set(Box<Sort>),
    Dict(Box<Sort>, Box<Sort>),
    FiniteDict(Box<Sort>, Box<Sort>),
    DictKeys(Box<Sort>),
}

/// Finite contexts in which the sort checker requires a particular operand
/// sort. Keeping this as data (rather than an arbitrary string) makes every
/// core failure outcome explicit and extractable.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SortContext {
    IntEnumNumericValue,
    RuntimeClassOperand,
    SubclassActualOperand,
    SubclassExpectedOperand,
    FieldReceiver,
    PermissionReceiver,
    NotOperand,
    BooleanOperand,
    ImplicationLeftOperand,
    ImplicationRightOperand,
    ConditionalGuard,
    IntegerLeftOperand,
    IntegerRightOperand,
    FloorDivisionOperand,
    NegationOperand,
    StringConcatenationOperand,
    StringLengthOperand,
    BytesConcatenationOperand,
    BytesLengthOperand,
    BytesIndexReceiver,
    BytesIndex,
    VariadicTupleIndex,
    ListElement,
    ListIndex,
    ListMembershipValue,
    SetMembershipValue,
    DictionaryValue,
    DictionaryKey,
    DictionaryMembershipKey,
    DictionaryLookupKey,
    PermissionTransferReceiver,
    FiniteDictionaryKey,
    FiniteDictionaryValue,
    ComprehensionMapper,
    ComprehensionFilter,
    QuantifierBody,
}

impl SortContext {
    fn as_str(self) -> &'static str {
        match self {
            Self::IntEnumNumericValue => "IntEnum numeric value",
            Self::RuntimeClassOperand => "runtime-class operand",
            Self::SubclassActualOperand => "subclass actual operand",
            Self::SubclassExpectedOperand => "subclass expected operand",
            Self::FieldReceiver => "field receiver",
            Self::PermissionReceiver => "permission receiver",
            Self::NotOperand => "not operand",
            Self::BooleanOperand => "boolean operand",
            Self::ImplicationLeftOperand => "implication left operand",
            Self::ImplicationRightOperand => "implication right operand",
            Self::ConditionalGuard => "conditional guard",
            Self::IntegerLeftOperand => "integer left operand",
            Self::IntegerRightOperand => "integer right operand",
            Self::FloorDivisionOperand => "floor-division operand",
            Self::NegationOperand => "negation operand",
            Self::StringConcatenationOperand => "string concatenation operand",
            Self::StringLengthOperand => "string length operand",
            Self::BytesConcatenationOperand => "bytes concatenation operand",
            Self::BytesLengthOperand => "bytes length operand",
            Self::BytesIndexReceiver => "bytes index receiver",
            Self::BytesIndex => "bytes index",
            Self::VariadicTupleIndex => "variadic tuple index",
            Self::ListElement => "list element",
            Self::ListIndex => "list index",
            Self::ListMembershipValue => "list membership value",
            Self::SetMembershipValue => "set membership value",
            Self::DictionaryValue => "dictionary value",
            Self::DictionaryKey => "dictionary key",
            Self::DictionaryMembershipKey => "dictionary membership key",
            Self::DictionaryLookupKey => "dictionary lookup key",
            Self::PermissionTransferReceiver => "permission-transfer receiver",
            Self::FiniteDictionaryKey => "finite dictionary key",
            Self::FiniteDictionaryValue => "finite dictionary value",
            Self::ComprehensionMapper => "comprehension mapper",
            Self::ComprehensionFilter => "comprehension filter",
            Self::QuantifierBody => "quantifier body",
        }
    }
}

/// Closed, structured failure channel for the production sort checker.
/// Presentation strings are deliberately derived only at the compatibility
/// boundary in [`Term::sort`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SortError {
    IntEnumDescriptorMissingClassOrMember,
    IntEnumDescriptorMembersNotUnique,
    IntEnumProjectionRequiresValue,
    IntEnumIdentityRequiresValues,
    NominalReferenceClassEmpty,
    ClassLiteralNameEmpty,
    PredicateInstanceNameEmpty,
    PredicateInstanceArgumentsEmpty,
    PredicateArgumentSortUnsupported,
    SequenceElementSortUnsupported {
        sort: Sort,
    },
    HeapFieldSortUnsupported,
    HeapListElementSortUnsupported {
        sort: Sort,
    },
    PermissionFractionOutsideUnit {
        numerator: u32,
        denominator: u32,
    },
    PermissionTransferFractionOutsideUnit {
        numerator: u32,
        denominator: u32,
    },
    PermissionMaskFieldEmpty,
    PermissionMaskTransitionDoesNotAdvance,
    PermissionMaskTransitionFieldEmpty,
    ConditionalBranchSortMismatch {
        then_sort: Sort,
        else_sort: Sort,
    },
    EqualityOperandSortMismatch {
        left_sort: Sort,
        right_sort: Sort,
    },
    FloorDivisionDivisorNotPositive,
    TupleOperandRequired,
    TupleIndexOutsideLength {
        index: usize,
        length: usize,
    },
    VariadicTupleElementSortUnsupported {
        sort: Sort,
    },
    VariadicTupleElementSortMismatch {
        expected: Sort,
        actual: Sort,
    },
    VariadicTupleLengthOperandNotTuple {
        actual: Sort,
    },
    VariadicTupleOperandRequiredForIndex,
    VariadicTupleSliceOperandNotTuple {
        actual: Sort,
    },
    ListLengthOperandNotList {
        actual: Sort,
    },
    ListOperandRequiredForIndex,
    ListOperandRequiredForMembership,
    ListSliceOperandNotList {
        actual: Sort,
    },
    ListConcatLeftOperandNotList {
        actual: Sort,
    },
    ListConcatRightOperandNotList {
        actual: Sort,
    },
    ListConcatElementSortMismatch {
        left_element: Sort,
        right_element: Sort,
    },
    ListSumOperandNotIntegerList {
        actual: Sort,
    },
    ListSortedOperandNotIntegerList {
        actual: Sort,
    },
    ListSourceRequiredForComprehension,
    SetSourceRequiredForComprehension,
    SetComprehensionElementSortUnsupported {
        sort: Sort,
    },
    SetLengthOperandNotSet {
        actual: Sort,
    },
    SetOperandRequiredForMembership,
    DictionarySourceRequiredForComprehension,
    DictionaryComprehensionSortsUnsupported {
        key_sort: Sort,
        value_sort: Sort,
    },
    DictionaryLengthOperandNotDictionary {
        actual: Sort,
    },
    DictionaryOperandRequiredForMembership,
    DictionaryOperandRequiredForLookup,
    QuantifierBinderEmpty,
    ComprehensionBinderEmpty,
    FiniteDictionaryKeySortUnsupported {
        sort: Sort,
    },
    FiniteDictionaryValueSortUnsupported {
        sort: Sort,
    },
    DictionaryKeySortUnsupported {
        sort: Sort,
    },
    BinderSortMismatch {
        binder: String,
        actual: Sort,
        expected: Sort,
    },
    NestedBinderCapture {
        binder: String,
    },
    UnexpectedSort {
        context: SortContext,
        actual: Sort,
        expected: Sort,
    },
}

impl std::fmt::Display for SortError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::IntEnumDescriptorMissingClassOrMember => formatter.write_str(
                "IntEnum descriptor requires a class and at least one member",
            ),
            Self::IntEnumDescriptorMembersNotUnique => formatter.write_str(
                "IntEnum descriptor member names and integer values must be nonempty and unique",
            ),
            Self::IntEnumProjectionRequiresValue => formatter.write_str(
                "IntEnum projection/domain requires a descriptor-carrying IntEnum value",
            ),
            Self::IntEnumIdentityRequiresValues => formatter.write_str(
                "IntEnum identity requires two descriptor-carrying IntEnum values",
            ),
            Self::NominalReferenceClassEmpty => {
                formatter.write_str("nominal reference class cannot be empty")
            }
            Self::ClassLiteralNameEmpty => formatter.write_str("class literal name cannot be empty"),
            Self::PredicateInstanceNameEmpty => {
                formatter.write_str("predicate instance name cannot be empty")
            }
            Self::PredicateInstanceArgumentsEmpty => {
                formatter.write_str("predicate instance requires at least one argument")
            }
            Self::PredicateArgumentSortUnsupported => formatter.write_str(
                "predicate instance arguments must have a first-order scalar, reference, or class sort",
            ),
            Self::SequenceElementSortUnsupported { sort } => write!(
                formatter,
                "list element sort {sort:?} is not supported by the sequence VC"
            ),
            Self::HeapFieldSortUnsupported => formatter.write_str(
                "heap fields cannot have Unit, Class, Bytes, Range, or Tuple sort",
            ),
            Self::HeapListElementSortUnsupported { sort } => write!(
                formatter,
                "heap list field element sort {sort:?} is not supported by the sequence VC"
            ),
            Self::PermissionFractionOutsideUnit { numerator, denominator } => write!(
                formatter,
                "permission fraction {numerator}/{denominator} is outside [0, 1]"
            ),
            Self::PermissionTransferFractionOutsideUnit { numerator, denominator } => write!(
                formatter,
                "permission-transfer fraction {numerator}/{denominator} is outside [0, 1]"
            ),
            Self::PermissionMaskFieldEmpty => {
                formatter.write_str("permission-mask field cannot be empty")
            }
            Self::PermissionMaskTransitionDoesNotAdvance => {
                formatter.write_str("permission-mask transition must advance the mask")
            }
            Self::PermissionMaskTransitionFieldEmpty => {
                formatter.write_str("permission-mask transition field cannot be empty")
            }
            Self::ConditionalBranchSortMismatch { then_sort, else_sort } => write!(
                formatter,
                "conditional branches have different sorts: {then_sort:?} and {else_sort:?}"
            ),
            Self::EqualityOperandSortMismatch { left_sort, right_sort } => write!(
                formatter,
                "equality operands have different sorts: {left_sort:?} and {right_sort:?}"
            ),
            Self::FloorDivisionDivisorNotPositive => {
                formatter.write_str("floor-division divisor must be positive")
            }
            Self::TupleOperandRequired => {
                formatter.write_str("tuple indexing requires a Tuple operand")
            }
            Self::TupleIndexOutsideLength { index, length } => write!(
                formatter,
                "tuple index {index} is outside fixed tuple length {length}"
            ),
            Self::VariadicTupleElementSortUnsupported { sort } => write!(
                formatter,
                "variadic tuple element sort {sort:?} is unsupported"
            ),
            Self::VariadicTupleElementSortMismatch { expected, actual } => write!(
                formatter,
                "variadic tuple element has sort {actual:?}, expected {expected:?}"
            ),
            Self::VariadicTupleLengthOperandNotTuple { actual } => write!(
                formatter,
                "variadic tuple length operand has sort {actual:?}, expected VariadicTuple"
            ),
            Self::VariadicTupleOperandRequiredForIndex => {
                formatter.write_str("variadic tuple indexing requires a VariadicTuple operand")
            }
            Self::VariadicTupleSliceOperandNotTuple { actual } => write!(
                formatter,
                "variadic tuple slicing operand has sort {actual:?}, expected VariadicTuple"
            ),
            Self::ListLengthOperandNotList { actual } => write!(
                formatter,
                "list length operand has sort {actual:?}, expected List"
            ),
            Self::ListOperandRequiredForIndex => {
                formatter.write_str("list indexing requires a List operand")
            }
            Self::ListOperandRequiredForMembership => {
                formatter.write_str("list membership requires a List operand")
            }
            Self::ListSliceOperandNotList { actual } => write!(
                formatter,
                "list slicing operand has sort {actual:?}, expected List"
            ),
            Self::ListConcatLeftOperandNotList { actual } => write!(
                formatter,
                "left list-concatenation operand has sort {actual:?}, expected List"
            ),
            Self::ListConcatRightOperandNotList { actual } => write!(
                formatter,
                "right list-concatenation operand has sort {actual:?}, expected List"
            ),
            Self::ListConcatElementSortMismatch {
                left_element,
                right_element,
            } => write!(
                formatter,
                "list-concatenation operands have different element sorts: {left_element:?} and {right_element:?}"
            ),
            Self::ListSumOperandNotIntegerList { actual } => write!(
                formatter,
                "list sum operand has sort {actual:?}, expected List[Int]"
            ),
            Self::ListSortedOperandNotIntegerList { actual } => write!(
                formatter,
                "list sorted operand has sort {actual:?}, expected List[Int]"
            ),
            Self::ListSourceRequiredForComprehension => {
                formatter.write_str("list comprehension requires a List source")
            }
            Self::SetSourceRequiredForComprehension => {
                formatter.write_str("set comprehension requires a List source")
            }
            Self::SetComprehensionElementSortUnsupported { sort } => write!(
                formatter,
                "set-comprehension element sort {sort:?} is unsupported"
            ),
            Self::SetLengthOperandNotSet { actual } => write!(
                formatter,
                "set length operand has sort {actual:?}, expected Set"
            ),
            Self::SetOperandRequiredForMembership => {
                formatter.write_str("set membership requires a Set operand")
            }
            Self::DictionarySourceRequiredForComprehension => {
                formatter.write_str("dictionary comprehension requires a List source")
            }
            Self::DictionaryComprehensionSortsUnsupported { key_sort, value_sort } => write!(
                formatter,
                "dictionary-comprehension sorts {key_sort:?}/{value_sort:?} are unsupported"
            ),
            Self::DictionaryLengthOperandNotDictionary { actual } => write!(
                formatter,
                "dictionary length operand has sort {actual:?}, expected Dict"
            ),
            Self::DictionaryOperandRequiredForMembership => {
                formatter.write_str("dictionary membership requires a Dict operand")
            }
            Self::DictionaryOperandRequiredForLookup => {
                formatter.write_str("dictionary lookup requires a Dict operand")
            }
            Self::QuantifierBinderEmpty => formatter.write_str("quantifier binder cannot be empty"),
            Self::ComprehensionBinderEmpty => {
                formatter.write_str("comprehension binder cannot be empty")
            }
            Self::FiniteDictionaryKeySortUnsupported { sort } => write!(
                formatter,
                "finite dictionary key sort {sort:?} is unsupported"
            ),
            Self::FiniteDictionaryValueSortUnsupported { sort } => write!(
                formatter,
                "finite dictionary value sort {sort:?} is unsupported"
            ),
            Self::DictionaryKeySortUnsupported { sort } => {
                write!(formatter, "dictionary-key sort {sort:?} is unsupported")
            }
            Self::BinderSortMismatch { binder, actual, expected } => write!(
                formatter,
                "binder {binder:?} occurs with sort {actual:?}, expected {expected:?}"
            ),
            Self::NestedBinderCapture { binder } => write!(
                formatter,
                "nested binder {binder:?} captures an outer bound variable"
            ),
            Self::UnexpectedSort { context, actual, expected } => write!(
                formatter,
                "{} has sort {actual:?}, expected {expected:?}",
                context.as_str()
            ),
        }
    }
}

impl std::error::Error for SortError {}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct IntEnumDescriptor {
    pub class: String,
    pub members: Vec<(String, i64)>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct PermissionTransferAmount {
    pub receiver: Box<Term>,
    pub numerator: u32,
    pub denominator: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum Term {
    Bool {
        value: bool,
    },
    Int {
        value: i64,
    },
    IntEnumValue {
        descriptor: IntEnumDescriptor,
        value: Box<Term>,
    },
    IntEnumProjection {
        value: Box<Term>,
    },
    IntEnumDomain {
        value: Box<Term>,
    },
    IntEnumIdentity {
        left: Box<Term>,
        right: Box<Term>,
    },
    String {
        value: String,
    },
    Bytes {
        values: Vec<u8>,
    },
    Range {
        values: Vec<i64>,
    },
    Unit,
    NullReference,
    NominalReference {
        name: String,
        class: String,
    },
    ClassLiteral {
        name: String,
    },
    RuntimeClass {
        value: Box<Term>,
    },
    PredicateInstance {
        predicate: String,
        arguments: Vec<Term>,
    },
    ClassSubtype {
        actual: Box<Term>,
        expected: Box<Term>,
    },
    Variable {
        name: String,
        sort: Sort,
    },
    FieldRead {
        heap: u32,
        receiver: Box<Term>,
        field: String,
        sort: Sort,
    },
    PermissionAtLeast {
        mask: u32,
        receiver: Box<Term>,
        field: String,
        numerator: u32,
        denominator: u32,
    },
    PermissionAtMost {
        mask: u32,
        receiver: Box<Term>,
        field: String,
        numerator: u32,
        denominator: u32,
    },
    PermissionPositive {
        mask: u32,
        receiver: Box<Term>,
        field: String,
    },
    PermissionMaskValid {
        mask: u32,
        field: String,
    },
    PermissionMaskTransition {
        pre_mask: u32,
        post_mask: u32,
        field: String,
        consumed: Vec<PermissionTransferAmount>,
        produced: Vec<PermissionTransferAmount>,
    },
    Not {
        value: Box<Term>,
    },
    And {
        values: Vec<Term>,
    },
    Or {
        values: Vec<Term>,
    },
    Implies {
        left: Box<Term>,
        right: Box<Term>,
    },
    IfThenElse {
        condition: Box<Term>,
        then_value: Box<Term>,
        else_value: Box<Term>,
    },
    Equal {
        left: Box<Term>,
        right: Box<Term>,
    },
    Less {
        left: Box<Term>,
        right: Box<Term>,
    },
    LessEqual {
        left: Box<Term>,
        right: Box<Term>,
    },
    Greater {
        left: Box<Term>,
        right: Box<Term>,
    },
    GreaterEqual {
        left: Box<Term>,
        right: Box<Term>,
    },
    Add {
        left: Box<Term>,
        right: Box<Term>,
    },
    Subtract {
        left: Box<Term>,
        right: Box<Term>,
    },
    Multiply {
        left: Box<Term>,
        right: Box<Term>,
    },
    FloorDivideByPositive {
        value: Box<Term>,
        divisor: u64,
    },
    Negate {
        value: Box<Term>,
    },
    StringConcat {
        values: Vec<Term>,
    },
    StringLength {
        value: Box<Term>,
    },
    BytesConcat {
        values: Vec<Term>,
    },
    BytesLength {
        value: Box<Term>,
    },
    BytesGet {
        bytes: Box<Term>,
        index: Box<Term>,
    },
    Tuple {
        values: Vec<Term>,
    },
    TupleGet {
        tuple: Box<Term>,
        index: usize,
    },
    VariadicTuple {
        element_sort: Sort,
        values: Vec<Term>,
    },
    VariadicTupleLength {
        value: Box<Term>,
    },
    VariadicTupleGet {
        tuple: Box<Term>,
        index: Box<Term>,
    },
    /// Exact Python static slicing over an immutable homogeneous tuple.
    VariadicTupleSlice {
        source: Box<Term>,
        #[serde(default, deserialize_with = "deserialize_optional_i128")]
        lower: Option<i128>,
        #[serde(default, deserialize_with = "deserialize_optional_i128")]
        upper: Option<i128>,
        #[serde(deserialize_with = "deserialize_nonzero_i128")]
        step: NonZeroI128,
    },
    List {
        element_sort: Sort,
        values: Vec<Term>,
    },
    ListLength {
        value: Box<Term>,
    },
    ListGet {
        list: Box<Term>,
        index: Box<Term>,
    },
    ListContains {
        list: Box<Term>,
        value: Box<Term>,
    },
    /// Exact Python static-list slicing. Bounds are literal Python integers;
    /// `None` retains the sign-sensitive open-bound behavior of `slice.indices`.
    /// A zero step is structurally unrepresentable and fails during decoding.
    ListSlice {
        source: Box<Term>,
        #[serde(default, deserialize_with = "deserialize_optional_i128")]
        lower: Option<i128>,
        #[serde(default, deserialize_with = "deserialize_optional_i128")]
        upper: Option<i128>,
        #[serde(deserialize_with = "deserialize_nonzero_i128")]
        step: NonZeroI128,
    },
    ListConcat {
        left: Box<Term>,
        right: Box<Term>,
    },
    ListSum {
        source: Box<Term>,
    },
    ListSorted {
        source: Box<Term>,
    },
    /// The exact, stable-order result of Python's single-generator list
    /// comprehension.  `binder` is scoped over `mapped` and `filter`; the
    /// solver defines the result as a prefix fold over `source`.
    ListComprehension {
        id: String,
        source: Box<Term>,
        binder: String,
        element_sort: Sort,
        mapped: Box<Term>,
        filter: Option<Box<Term>>,
    },
    /// Python set-comprehension semantics represented by a stable sequence of
    /// first insertions.  Membership and cardinality are exact; source order is
    /// retained internally only to give the recursive encoding a canonical
    /// representation.
    SetComprehension {
        id: String,
        source: Box<Term>,
        binder: String,
        element_sort: Sort,
        mapped: Box<Term>,
        filter: Option<Box<Term>>,
    },
    SetLength {
        value: Box<Term>,
    },
    SetContains {
        set: Box<Term>,
        value: Box<Term>,
    },
    /// Python dictionary-comprehension semantics.  The solver folds from left
    /// to right, so later stores overwrite earlier equal keys exactly as in
    /// CPython.
    DictComprehension {
        id: String,
        source: Box<Term>,
        binder: String,
        key_sort: Sort,
        value_sort: Sort,
        key: Box<Term>,
        value: Box<Term>,
        filter: Option<Box<Term>>,
    },
    DictLength {
        value: Box<Term>,
    },
    DictContains {
        dict: Box<Term>,
        key: Box<Term>,
    },
    DictGet {
        dict: Box<Term>,
        key: Box<Term>,
    },
    ForAll {
        binder: String,
        binder_sort: Sort,
        body: Box<Term>,
    },
    FiniteDict {
        key_sort: Sort,
        value_sort: Sort,
        entries: Vec<(Term, Term)>,
    },
    DictKeys {
        key_sort: Sort,
        values: Vec<Term>,
    },
}

impl Term {
    pub fn sort(&self) -> Result<Sort, String> {
        self.sort_typed().map_err(|error| error.to_string())
    }

    /// Exact structured sort checker used by the proof extraction boundary.
    /// Every failure is one member of the closed [`SortError`] union.
    pub fn sort_typed(&self) -> Result<Sort, SortError> {
        match self {
            Self::Bool { .. } => Ok(Sort::Bool),
            Self::Int { .. } => Ok(Sort::Int),
            Self::IntEnumValue { descriptor, value } => {
                validate_int_enum_descriptor(descriptor)?;
                require_sort(value, Sort::Int, SortContext::IntEnumNumericValue)?;
                Ok(Sort::Int)
            }
            Self::IntEnumProjection { value } | Self::IntEnumDomain { value } => {
                if !matches!(value.as_ref(), Self::IntEnumValue { .. }) {
                    return Err(SortError::IntEnumProjectionRequiresValue);
                }
                value.sort_typed()?;
                Ok(if matches!(self, Self::IntEnumDomain { .. }) {
                    Sort::Bool
                } else {
                    Sort::Int
                })
            }
            Self::IntEnumIdentity { left, right } => {
                if !matches!(left.as_ref(), Self::IntEnumValue { .. })
                    || !matches!(right.as_ref(), Self::IntEnumValue { .. })
                {
                    return Err(SortError::IntEnumIdentityRequiresValues);
                }
                left.sort_typed()?;
                right.sort_typed()?;
                Ok(Sort::Bool)
            }
            Self::String { .. } => Ok(Sort::String),
            Self::Bytes { .. } => Ok(Sort::Bytes),
            Self::Range { .. } => Ok(Sort::Range),
            Self::Unit => Ok(Sort::Unit),
            Self::NullReference => Ok(Sort::Reference),
            Self::NominalReference { class, .. } => {
                if class.is_empty() {
                    Err(SortError::NominalReferenceClassEmpty)
                } else {
                    Ok(Sort::Reference)
                }
            }
            Self::ClassLiteral { name } => {
                if name.is_empty() {
                    Err(SortError::ClassLiteralNameEmpty)
                } else {
                    Ok(Sort::Class)
                }
            }
            Self::RuntimeClass { value } => {
                require_sort(value, Sort::Reference, SortContext::RuntimeClassOperand)?;
                Ok(Sort::Class)
            }
            Self::PredicateInstance {
                predicate,
                arguments,
            } => {
                if predicate.is_empty() {
                    return Err(SortError::PredicateInstanceNameEmpty);
                }
                if arguments.is_empty() {
                    return Err(SortError::PredicateInstanceArgumentsEmpty);
                }
                require_predicate_argument_sorts(arguments)?;
                Ok(Sort::Reference)
            }
            Self::ClassSubtype { actual, expected } => {
                require_sort(actual, Sort::Class, SortContext::SubclassActualOperand)?;
                require_sort(expected, Sort::Class, SortContext::SubclassExpectedOperand)?;
                Ok(Sort::Bool)
            }
            Self::Variable { sort, .. } => {
                if let Sort::List(element) = sort
                    && !is_list_element_sort(element)
                {
                    return Err(SortError::SequenceElementSortUnsupported {
                        sort: element.as_ref().clone(),
                    });
                }
                if let Sort::VariadicTuple(element) = sort
                    && !is_variadic_tuple_element_sort(element)
                {
                    return Err(SortError::VariadicTupleElementSortUnsupported {
                        sort: element.as_ref().clone(),
                    });
                }
                Ok(sort.clone())
            }
            Self::FieldRead { receiver, sort, .. } => {
                require_sort(receiver, Sort::Reference, SortContext::FieldReceiver)?;
                if matches!(
                    sort,
                    Sort::Unit
                        | Sort::Class
                        | Sort::Bytes
                        | Sort::Range
                        | Sort::Tuple(_)
                        | Sort::VariadicTuple(_)
                        | Sort::FiniteDict(_, _)
                        | Sort::DictKeys(_)
                ) {
                    Err(SortError::HeapFieldSortUnsupported)
                } else if let Sort::List(element) = sort
                    && !is_list_element_sort(element)
                {
                    Err(SortError::HeapListElementSortUnsupported {
                        sort: element.as_ref().clone(),
                    })
                } else {
                    Ok(sort.clone())
                }
            }
            Self::PermissionAtLeast {
                receiver,
                numerator,
                denominator,
                ..
            } => {
                require_sort(receiver, Sort::Reference, SortContext::PermissionReceiver)?;
                if *denominator == 0 || numerator > denominator {
                    Err(SortError::PermissionFractionOutsideUnit {
                        numerator: *numerator,
                        denominator: *denominator,
                    })
                } else {
                    Ok(Sort::Bool)
                }
            }
            Self::PermissionAtMost {
                receiver,
                numerator,
                denominator,
                ..
            } => {
                require_sort(receiver, Sort::Reference, SortContext::PermissionReceiver)?;
                if *denominator == 0 || numerator > denominator {
                    Err(SortError::PermissionFractionOutsideUnit {
                        numerator: *numerator,
                        denominator: *denominator,
                    })
                } else {
                    Ok(Sort::Bool)
                }
            }
            Self::PermissionPositive { receiver, .. } => {
                require_sort(receiver, Sort::Reference, SortContext::PermissionReceiver)?;
                Ok(Sort::Bool)
            }
            Self::PermissionMaskValid { field, .. } => {
                if field.is_empty() {
                    Err(SortError::PermissionMaskFieldEmpty)
                } else {
                    Ok(Sort::Bool)
                }
            }
            Self::PermissionMaskTransition {
                pre_mask,
                post_mask,
                field,
                consumed,
                produced,
            } => {
                if pre_mask == post_mask {
                    return Err(SortError::PermissionMaskTransitionDoesNotAdvance);
                }
                if field.is_empty() {
                    return Err(SortError::PermissionMaskTransitionFieldEmpty);
                }
                require_permission_transfer_amounts(consumed)?;
                require_permission_transfer_amounts(produced)?;
                Ok(Sort::Bool)
            }
            Self::Not { value } => {
                require_sort(value, Sort::Bool, SortContext::NotOperand)?;
                Ok(Sort::Bool)
            }
            Self::And { values } | Self::Or { values } => {
                require_all_sorts(values, Sort::Bool, SortContext::BooleanOperand)?;
                Ok(Sort::Bool)
            }
            Self::Implies { left, right } => {
                require_sort(left, Sort::Bool, SortContext::ImplicationLeftOperand)?;
                require_sort(right, Sort::Bool, SortContext::ImplicationRightOperand)?;
                Ok(Sort::Bool)
            }
            Self::IfThenElse {
                condition,
                then_value,
                else_value,
            } => {
                require_sort(condition, Sort::Bool, SortContext::ConditionalGuard)?;
                let then_sort = then_value.sort_typed()?;
                let else_sort = else_value.sort_typed()?;
                if then_sort != else_sort {
                    return Err(SortError::ConditionalBranchSortMismatch {
                        then_sort,
                        else_sort,
                    });
                }
                Ok(then_sort)
            }
            Self::Equal { left, right } => {
                let left_sort = left.sort_typed()?;
                let right_sort = right.sort_typed()?;
                if left_sort != right_sort {
                    return Err(SortError::EqualityOperandSortMismatch {
                        left_sort,
                        right_sort,
                    });
                }
                Ok(Sort::Bool)
            }
            Self::Less { left, right }
            | Self::LessEqual { left, right }
            | Self::Greater { left, right }
            | Self::GreaterEqual { left, right }
            | Self::Add { left, right }
            | Self::Subtract { left, right }
            | Self::Multiply { left, right } => {
                require_sort(left, Sort::Int, SortContext::IntegerLeftOperand)?;
                require_sort(right, Sort::Int, SortContext::IntegerRightOperand)?;
                if matches!(
                    self,
                    Self::Less { .. }
                        | Self::LessEqual { .. }
                        | Self::Greater { .. }
                        | Self::GreaterEqual { .. }
                ) {
                    Ok(Sort::Bool)
                } else {
                    Ok(Sort::Int)
                }
            }
            Self::FloorDivideByPositive { value, divisor } => {
                require_sort(value, Sort::Int, SortContext::FloorDivisionOperand)?;
                if *divisor == 0 {
                    Err(SortError::FloorDivisionDivisorNotPositive)
                } else {
                    Ok(Sort::Int)
                }
            }
            Self::Negate { value } => {
                require_sort(value, Sort::Int, SortContext::NegationOperand)?;
                Ok(Sort::Int)
            }
            Self::StringConcat { values } => {
                require_all_sorts(
                    values,
                    Sort::String,
                    SortContext::StringConcatenationOperand,
                )?;
                Ok(Sort::String)
            }
            Self::StringLength { value } => {
                require_sort(value, Sort::String, SortContext::StringLengthOperand)?;
                Ok(Sort::Int)
            }
            Self::BytesConcat { values } => {
                require_all_sorts(values, Sort::Bytes, SortContext::BytesConcatenationOperand)?;
                Ok(Sort::Bytes)
            }
            Self::BytesLength { value } => {
                require_sort(value, Sort::Bytes, SortContext::BytesLengthOperand)?;
                Ok(Sort::Int)
            }
            Self::BytesGet { bytes, index } => {
                require_sort(bytes, Sort::Bytes, SortContext::BytesIndexReceiver)?;
                require_sort(index, Sort::Int, SortContext::BytesIndex)?;
                Ok(Sort::Int)
            }
            Self::Tuple { values } => Ok(Sort::Tuple(collect_sorts(values)?)),
            Self::TupleGet { tuple, index } => {
                let Sort::Tuple(elements) = tuple.sort_typed()? else {
                    return Err(SortError::TupleOperandRequired);
                };
                elements
                    .get(*index)
                    .cloned()
                    .ok_or(SortError::TupleIndexOutsideLength {
                        index: *index,
                        length: elements.len(),
                    })
            }
            Self::VariadicTuple {
                element_sort,
                values,
            } => {
                if !is_variadic_tuple_element_sort(element_sort) {
                    return Err(SortError::VariadicTupleElementSortUnsupported {
                        sort: element_sort.clone(),
                    });
                }
                require_variadic_tuple_element_sorts(values, element_sort)?;
                Ok(Sort::VariadicTuple(Box::new(element_sort.clone())))
            }
            Self::VariadicTupleLength { value } => match value.sort_typed()? {
                Sort::VariadicTuple(_) => Ok(Sort::Int),
                actual => Err(SortError::VariadicTupleLengthOperandNotTuple { actual }),
            },
            Self::VariadicTupleGet { tuple, index } => {
                require_sort(index, Sort::Int, SortContext::VariadicTupleIndex)?;
                let Sort::VariadicTuple(element) = tuple.sort_typed()? else {
                    return Err(SortError::VariadicTupleOperandRequiredForIndex);
                };
                Ok(*element)
            }
            Self::VariadicTupleSlice { source, .. } => match source.sort_typed()? {
                actual @ Sort::VariadicTuple(_) => Ok(actual),
                actual => Err(SortError::VariadicTupleSliceOperandNotTuple { actual }),
            },
            Self::List {
                element_sort,
                values,
            } => {
                if !is_list_element_sort(element_sort) {
                    return Err(SortError::SequenceElementSortUnsupported {
                        sort: element_sort.clone(),
                    });
                }
                require_all_sorts(values, element_sort.clone(), SortContext::ListElement)?;
                Ok(Sort::List(Box::new(element_sort.clone())))
            }
            Self::ListLength { value } => match value.sort_typed()? {
                Sort::List(_) => Ok(Sort::Int),
                actual => Err(SortError::ListLengthOperandNotList { actual }),
            },
            Self::ListGet { list, index } => {
                require_sort(index, Sort::Int, SortContext::ListIndex)?;
                let Sort::List(element) = list.sort_typed()? else {
                    return Err(SortError::ListOperandRequiredForIndex);
                };
                Ok(*element)
            }
            Self::ListContains { list, value } => {
                let Sort::List(element) = list.sort_typed()? else {
                    return Err(SortError::ListOperandRequiredForMembership);
                };
                require_sort(value, *element, SortContext::ListMembershipValue)?;
                Ok(Sort::Bool)
            }
            Self::ListSlice { source, .. } => match source.sort_typed()? {
                actual @ Sort::List(_) => Ok(actual),
                actual => Err(SortError::ListSliceOperandNotList { actual }),
            },
            Self::ListConcat { left, right } => {
                let left_element = match left.sort_typed()? {
                    Sort::List(element) => element,
                    actual => {
                        return Err(SortError::ListConcatLeftOperandNotList { actual });
                    }
                };
                let right_element = match right.sort_typed()? {
                    Sort::List(element) => element,
                    actual => {
                        return Err(SortError::ListConcatRightOperandNotList { actual });
                    }
                };
                if left_element != right_element {
                    return Err(SortError::ListConcatElementSortMismatch {
                        left_element: *left_element,
                        right_element: *right_element,
                    });
                }
                Ok(Sort::List(left_element))
            }
            Self::ListSum { source } => {
                let actual = source.sort_typed()?;
                if actual == Sort::List(Box::new(Sort::Int)) {
                    Ok(Sort::Int)
                } else {
                    Err(SortError::ListSumOperandNotIntegerList { actual })
                }
            }
            Self::ListSorted { source } => {
                let actual = source.sort_typed()?;
                if actual == Sort::List(Box::new(Sort::Int)) {
                    Ok(actual)
                } else {
                    Err(SortError::ListSortedOperandNotIntegerList { actual })
                }
            }
            Self::ListComprehension {
                source,
                binder,
                element_sort,
                mapped,
                filter,
                ..
            } => {
                let Sort::List(source_element) = source.sort_typed()? else {
                    return Err(SortError::ListSourceRequiredForComprehension);
                };
                require_comprehension_body(binder, &source_element, mapped, element_sort, filter)?;
                Ok(Sort::List(Box::new(element_sort.clone())))
            }
            Self::SetComprehension {
                source,
                binder,
                element_sort,
                mapped,
                filter,
                ..
            } => {
                let Sort::List(source_element) = source.sort_typed()? else {
                    return Err(SortError::SetSourceRequiredForComprehension);
                };
                let exact_reference_identity_set = element_sort == &Sort::Reference
                    && is_exact_nominal_reference_list(source)
                    && is_reference_binder_projection(mapped, binder);
                if !is_finite_dict_key_sort(element_sort) && !exact_reference_identity_set {
                    return Err(SortError::SetComprehensionElementSortUnsupported {
                        sort: element_sort.clone(),
                    });
                }
                require_comprehension_body(binder, &source_element, mapped, element_sort, filter)?;
                Ok(Sort::Set(Box::new(element_sort.clone())))
            }
            Self::SetLength { value } => match value.sort_typed()? {
                Sort::Set(_) => Ok(Sort::Int),
                actual => Err(SortError::SetLengthOperandNotSet { actual }),
            },
            Self::SetContains { set, value } => {
                let Sort::Set(element) = set.sort_typed()? else {
                    return Err(SortError::SetOperandRequiredForMembership);
                };
                require_sort(value, *element, SortContext::SetMembershipValue)?;
                Ok(Sort::Bool)
            }
            Self::DictComprehension {
                source,
                binder,
                key_sort,
                value_sort,
                key,
                value,
                filter,
                ..
            } => {
                let Sort::List(source_element) = source.sort_typed()? else {
                    return Err(SortError::DictionarySourceRequiredForComprehension);
                };
                if !is_finite_dict_key_sort(key_sort) || !is_finite_dict_value_sort(value_sort) {
                    return Err(SortError::DictionaryComprehensionSortsUnsupported {
                        key_sort: key_sort.clone(),
                        value_sort: value_sort.clone(),
                    });
                }
                require_comprehension_body(binder, &source_element, key, key_sort, filter)?;
                require_bound_term_sort(
                    binder,
                    &source_element,
                    value,
                    value_sort,
                    SortContext::DictionaryValue,
                )?;
                Ok(Sort::Dict(
                    Box::new(key_sort.clone()),
                    Box::new(value_sort.clone()),
                ))
            }
            Self::DictLength { value } => match value.sort_typed()? {
                Sort::Dict(_, _) | Sort::FiniteDict(_, _) => Ok(Sort::Int),
                actual => Err(SortError::DictionaryLengthOperandNotDictionary { actual }),
            },
            Self::DictContains { dict, key } => {
                let Sort::Dict(expected, _) = dict.sort_typed()? else {
                    return Err(SortError::DictionaryOperandRequiredForMembership);
                };
                require_sort(key, *expected, SortContext::DictionaryMembershipKey)?;
                Ok(Sort::Bool)
            }
            Self::DictGet { dict, key } => {
                let Sort::Dict(expected, value) = dict.sort_typed()? else {
                    return Err(SortError::DictionaryOperandRequiredForLookup);
                };
                require_sort(key, *expected, SortContext::DictionaryLookupKey)?;
                Ok(*value)
            }
            Self::ForAll {
                binder,
                binder_sort,
                body,
            } => {
                if binder.is_empty() {
                    return Err(SortError::QuantifierBinderEmpty);
                }
                require_bound_term_sort(
                    binder,
                    binder_sort,
                    body,
                    &Sort::Bool,
                    SortContext::QuantifierBody,
                )?;
                Ok(Sort::Bool)
            }
            Self::FiniteDict {
                key_sort,
                value_sort,
                entries,
            } => {
                let exact_reference_keys =
                    key_sort == &Sort::Reference && all_nominal_reference_keys(entries);
                if !is_finite_dict_key_sort(key_sort) && !exact_reference_keys {
                    return Err(SortError::FiniteDictionaryKeySortUnsupported {
                        sort: key_sort.clone(),
                    });
                }
                if !is_finite_dict_value_sort(value_sort) {
                    return Err(SortError::FiniteDictionaryValueSortUnsupported {
                        sort: value_sort.clone(),
                    });
                }
                require_finite_dict_entry_sorts(entries, key_sort, value_sort)?;
                Ok(Sort::FiniteDict(
                    Box::new(key_sort.clone()),
                    Box::new(value_sort.clone()),
                ))
            }
            Self::DictKeys { key_sort, values } => {
                if !is_finite_dict_key_sort(key_sort) {
                    return Err(SortError::DictionaryKeySortUnsupported {
                        sort: key_sort.clone(),
                    });
                }
                require_all_sorts(values, key_sort.clone(), SortContext::DictionaryKey)?;
                Ok(Sort::DictKeys(Box::new(key_sort.clone())))
            }
        }
    }
}

/// Stable free-function entrypoint used by source-bound extraction tools that
/// cannot select an inherent Rust method directly. The implementation remains
/// the production [`Term::sort_typed`] method; this wrapper contains no duplicate
/// type-checking logic.
#[doc(hidden)]
pub fn term_sort_extraction_entrypoint(term: &Term) -> Result<Sort, SortError> {
    term.sort_typed()
}

fn require_predicate_argument_sorts(arguments: &[Term]) -> Result<(), SortError> {
    let mut result = Ok(());
    for argument in arguments {
        if result.is_ok() {
            result = match argument.sort_typed() {
                Ok(Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Class) => Ok(()),
                Ok(_) => Err(SortError::PredicateArgumentSortUnsupported),
                Err(error) => Err(error),
            };
        }
    }
    result
}

fn require_permission_transfer_amounts(
    amounts: &[PermissionTransferAmount],
) -> Result<(), SortError> {
    let mut result = Ok(());
    for amount in amounts {
        if result.is_ok() {
            result = match require_sort(
                &amount.receiver,
                Sort::Reference,
                SortContext::PermissionTransferReceiver,
            ) {
                Ok(()) if amount.denominator == 0 || amount.numerator > amount.denominator => {
                    Err(SortError::PermissionTransferFractionOutsideUnit {
                        numerator: amount.numerator,
                        denominator: amount.denominator,
                    })
                }
                other => other,
            };
        }
    }
    result
}

fn require_all_sorts(
    values: &[Term],
    expected: Sort,
    context: SortContext,
) -> Result<(), SortError> {
    let mut result = Ok(());
    for value in values {
        if result.is_ok() {
            result = require_sort(value, expected.clone(), context);
        }
    }
    result
}

fn collect_sorts(values: &[Term]) -> Result<Vec<Sort>, SortError> {
    let mut sorts = Vec::with_capacity(values.len());
    let mut error = None;
    for value in values {
        if error.is_none() {
            match value.sort_typed() {
                Ok(sort) => sorts.push(sort),
                Err(current) => {
                    error = Some(current);
                }
            }
        }
    }
    match error {
        Some(error) => Err(error),
        None => Ok(sorts),
    }
}

fn require_finite_dict_entry_sorts(
    entries: &[(Term, Term)],
    key_sort: &Sort,
    value_sort: &Sort,
) -> Result<(), SortError> {
    let mut result = Ok(());
    for (key, value) in entries {
        if result.is_ok() {
            result = match require_sort(key, key_sort.clone(), SortContext::FiniteDictionaryKey) {
                Ok(()) => require_sort(
                    value,
                    value_sort.clone(),
                    SortContext::FiniteDictionaryValue,
                ),
                Err(error) => Err(error),
            };
        }
    }
    result
}

fn validate_int_enum_descriptor(descriptor: &IntEnumDescriptor) -> Result<(), SortError> {
    if descriptor.class.is_empty() || descriptor.members.is_empty() {
        return Err(SortError::IntEnumDescriptorMissingClassOrMember);
    }
    let mut names = std::collections::BTreeSet::<String>::new();
    let mut values = std::collections::BTreeSet::<i64>::new();
    let mut valid = true;
    for (name, value) in &descriptor.members {
        if valid {
            valid = !name.is_empty() && names.insert(name.clone()) && values.insert(*value);
        }
    }
    if !valid {
        Err(SortError::IntEnumDescriptorMembersNotUnique)
    } else {
        Ok(())
    }
}

fn all_nominal_references(values: &[Term]) -> bool {
    let mut result = true;
    for value in values {
        if result {
            result = matches!(value, Term::NominalReference { .. });
        }
    }
    result
}

fn is_exact_nominal_reference_list(source: &Term) -> bool {
    match source {
        Term::List {
            element_sort: Sort::Reference,
            values,
        } => all_nominal_references(values),
        _ => false,
    }
}

fn is_reference_binder_projection(mapped: &Term, binder: &String) -> bool {
    match mapped {
        Term::Variable {
            name,
            sort: Sort::Reference,
        } => name == binder,
        _ => false,
    }
}

fn all_nominal_reference_keys(entries: &[(Term, Term)]) -> bool {
    let mut result = true;
    for (key, _) in entries {
        if result {
            result = matches!(key, Term::NominalReference { .. });
        }
    }
    result
}

fn is_list_element_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
    ) || matches!(sort, Sort::Tuple(elements) if all_list_element_sorts(elements))
        || matches!(sort, Sort::VariadicTuple(element) if is_list_element_sort(element))
        || matches!(sort, Sort::List(element) if is_list_element_sort(element))
        || matches!(sort, Sort::Set(element) if is_finite_dict_key_sort(element))
        || matches!(sort, Sort::Dict(key, value)
            if is_finite_dict_key_sort(key) && is_list_element_sort(value))
        || matches!(sort, Sort::FiniteDict(key, value)
            if is_finite_dict_key_sort(key) && is_list_element_sort(value))
}

fn all_list_element_sorts(elements: &[Sort]) -> bool {
    let mut result = true;
    for element in elements {
        if result {
            result = is_list_element_sort(element);
        }
    }
    result
}

fn is_variadic_tuple_element_sort(sort: &Sort) -> bool {
    is_list_element_sort(sort)
        || matches!(sort, Sort::VariadicTuple(element) if is_variadic_tuple_element_sort(element))
}

fn require_variadic_tuple_element_sorts(values: &[Term], expected: &Sort) -> Result<(), SortError> {
    let mut result = Ok(());
    for value in values {
        if result.is_ok() {
            result = match value.sort_typed() {
                Ok(actual) if &actual == expected => Ok(()),
                Ok(actual) => Err(SortError::VariadicTupleElementSortMismatch {
                    expected: expected.clone(),
                    actual,
                }),
                Err(error) => Err(error),
            };
        }
    }
    result
}

fn require_comprehension_body(
    binder: &String,
    binder_sort: &Sort,
    mapped: &Term,
    mapped_sort: &Sort,
    filter: &Option<Box<Term>>,
) -> Result<(), SortError> {
    if binder.is_empty() {
        return Err(SortError::ComprehensionBinderEmpty);
    }
    require_bound_term_sort(
        binder,
        binder_sort,
        mapped,
        mapped_sort,
        SortContext::ComprehensionMapper,
    )?;
    if let Some(filter) = filter {
        require_bound_term_sort(
            binder,
            binder_sort,
            filter,
            &Sort::Bool,
            SortContext::ComprehensionFilter,
        )?;
    }
    Ok(())
}

fn require_bound_term_sort(
    binder: &String,
    binder_sort: &Sort,
    term: &Term,
    expected: &Sort,
    context: SortContext,
) -> Result<(), SortError> {
    validate_bound_occurrences(term, binder, binder_sort)?;
    require_sort(term, expected.clone(), context)
}

fn validate_bound_occurrences(
    term: &Term,
    binder: &String,
    binder_sort: &Sort,
) -> Result<(), SortError> {
    fn one(term: &Term, binder: &String, binder_sort: &Sort) -> Result<(), SortError> {
        validate_bound_occurrences(term, binder, binder_sort)
    }
    fn two(
        left: &Term,
        right: &Term,
        binder: &String,
        binder_sort: &Sort,
    ) -> Result<(), SortError> {
        one(left, binder, binder_sort)?;
        one(right, binder, binder_sort)
    }
    fn all(terms: &[Term], binder: &String, binder_sort: &Sort) -> Result<(), SortError> {
        let mut result = Ok(());
        for term in terms {
            if result.is_ok() {
                result = one(term, binder, binder_sort);
            }
        }
        result
    }
    fn all_transfers(
        amounts: &[PermissionTransferAmount],
        binder: &String,
        binder_sort: &Sort,
    ) -> Result<(), SortError> {
        let mut result = Ok(());
        for amount in amounts {
            if result.is_ok() {
                result = one(&amount.receiver, binder, binder_sort);
            }
        }
        result
    }
    fn all_entries(
        entries: &[(Term, Term)],
        binder: &String,
        binder_sort: &Sort,
    ) -> Result<(), SortError> {
        let mut result = Ok(());
        for (key, value) in entries {
            if result.is_ok() {
                result = two(key, value, binder, binder_sort);
            }
        }
        result
    }
    match term {
        Term::Variable { name, sort } if name == binder => {
            if sort == binder_sort {
                Ok(())
            } else {
                Err(SortError::BinderSortMismatch {
                    binder: binder.clone(),
                    actual: sort.clone(),
                    expected: binder_sort.clone(),
                })
            }
        }
        Term::ForAll { binder: nested, .. }
        | Term::ListComprehension { binder: nested, .. }
        | Term::SetComprehension { binder: nested, .. }
        | Term::DictComprehension { binder: nested, .. }
            if nested == binder =>
        {
            Err(SortError::NestedBinderCapture {
                binder: binder.clone(),
            })
        }
        Term::PredicateInstance { arguments, .. }
        | Term::And { values: arguments }
        | Term::Or { values: arguments }
        | Term::StringConcat { values: arguments }
        | Term::BytesConcat { values: arguments }
        | Term::Tuple { values: arguments }
        | Term::VariadicTuple {
            values: arguments, ..
        }
        | Term::List {
            values: arguments, ..
        }
        | Term::DictKeys {
            values: arguments, ..
        } => all(arguments, binder, binder_sort),
        Term::RuntimeClass { value }
        | Term::IntEnumValue { value, .. }
        | Term::IntEnumProjection { value }
        | Term::IntEnumDomain { value }
        | Term::FieldRead {
            receiver: value, ..
        }
        | Term::PermissionAtLeast {
            receiver: value, ..
        }
        | Term::PermissionAtMost {
            receiver: value, ..
        }
        | Term::PermissionPositive {
            receiver: value, ..
        }
        | Term::Not { value }
        | Term::FloorDivideByPositive { value, .. }
        | Term::Negate { value }
        | Term::StringLength { value }
        | Term::BytesLength { value }
        | Term::TupleGet { tuple: value, .. }
        | Term::VariadicTupleLength { value }
        | Term::VariadicTupleSlice { source: value, .. }
        | Term::ListLength { value }
        | Term::ListSlice { source: value, .. }
        | Term::ListSum { source: value }
        | Term::ListSorted { source: value }
        | Term::SetLength { value }
        | Term::DictLength { value } => one(value, binder, binder_sort),
        Term::ClassSubtype {
            actual: left,
            expected: right,
        }
        | Term::Implies { left, right }
        | Term::Equal { left, right }
        | Term::Less { left, right }
        | Term::LessEqual { left, right }
        | Term::Greater { left, right }
        | Term::GreaterEqual { left, right }
        | Term::Add { left, right }
        | Term::Subtract { left, right }
        | Term::Multiply { left, right }
        | Term::IntEnumIdentity { left, right }
        | Term::BytesGet {
            bytes: left,
            index: right,
        }
        | Term::VariadicTupleGet {
            tuple: left,
            index: right,
        }
        | Term::ListGet {
            list: left,
            index: right,
        }
        | Term::ListContains {
            list: left,
            value: right,
        }
        | Term::ListConcat { left, right }
        | Term::SetContains {
            set: left,
            value: right,
        }
        | Term::DictContains {
            dict: left,
            key: right,
        }
        | Term::DictGet {
            dict: left,
            key: right,
        } => two(left, right, binder, binder_sort),
        Term::IfThenElse {
            condition,
            then_value,
            else_value,
        } => {
            one(condition, binder, binder_sort)?;
            one(then_value, binder, binder_sort)?;
            one(else_value, binder, binder_sort)
        }
        Term::PermissionMaskTransition {
            consumed, produced, ..
        } => {
            all_transfers(consumed, binder, binder_sort)?;
            all_transfers(produced, binder, binder_sort)
        }
        Term::FiniteDict { entries, .. } => all_entries(entries, binder, binder_sort),
        Term::ListComprehension {
            source,
            mapped,
            filter,
            ..
        }
        | Term::SetComprehension {
            source,
            mapped,
            filter,
            ..
        } => {
            one(source, binder, binder_sort)?;
            one(mapped, binder, binder_sort)?;
            if let Some(filter) = filter {
                one(filter, binder, binder_sort)?;
            }
            Ok(())
        }
        Term::DictComprehension {
            source,
            key,
            value,
            filter,
            ..
        } => {
            one(source, binder, binder_sort)?;
            two(key, value, binder, binder_sort)?;
            if let Some(filter) = filter {
                one(filter, binder, binder_sort)?;
            }
            Ok(())
        }
        Term::ForAll { body, .. } => one(body, binder, binder_sort),
        Term::Bool { .. }
        | Term::Int { .. }
        | Term::String { .. }
        | Term::Bytes { .. }
        | Term::Range { .. }
        | Term::Unit
        | Term::NullReference
        | Term::NominalReference { .. }
        | Term::ClassLiteral { .. }
        | Term::Variable { .. }
        | Term::PermissionMaskValid { .. } => Ok(()),
    }
}

fn is_finite_dict_key_sort(sort: &Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::String | Sort::Bytes)
        || matches!(sort, Sort::Tuple(elements) if all_finite_dict_key_sorts(elements))
        || matches!(sort, Sort::VariadicTuple(element) if is_finite_dict_key_sort(element))
}

fn all_finite_dict_key_sorts(elements: &[Sort]) -> bool {
    let mut result = true;
    for element in elements {
        if result {
            result = is_finite_dict_key_sort(element);
        }
    }
    result
}

fn is_finite_dict_value_sort(sort: &Sort) -> bool {
    matches!(
        sort,
        Sort::Bool | Sort::Int | Sort::String | Sort::Reference | Sort::Bytes
    ) || matches!(sort, Sort::Tuple(elements) if all_finite_dict_value_sorts(elements))
        || matches!(sort, Sort::VariadicTuple(element) if is_finite_dict_value_sort(element))
        || matches!(sort, Sort::List(element) if is_finite_dict_value_sort(element))
        || matches!(sort, Sort::Set(element) if is_finite_dict_key_sort(element))
        || matches!(sort, Sort::Dict(key, value)
            if is_finite_dict_key_sort(key) && is_finite_dict_value_sort(value))
        || matches!(sort, Sort::FiniteDict(key, value)
            if is_finite_dict_key_sort(key) && is_finite_dict_value_sort(value))
}

fn all_finite_dict_value_sorts(elements: &[Sort]) -> bool {
    let mut result = true;
    for element in elements {
        if result {
            result = is_finite_dict_value_sort(element);
        }
    }
    result
}

fn require_sort(term: &Term, expected: Sort, context: SortContext) -> Result<(), SortError> {
    let actual = term.sort_typed()?;
    if actual == expected {
        Ok(())
    } else {
        Err(SortError::UnexpectedSort {
            context,
            actual,
            expected,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Obligation {
    pub id: String,
    pub expectation: ObligationExpectation,
    pub assumptions: Vec<Term>,
    pub conclusion: Term,
    pub path: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ObligationExpectation {
    Prove,
    Refute,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ObligationStatus {
    Proved,
    Refuted,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ObligationResult {
    pub id: String,
    pub expectation: ObligationExpectation,
    pub status: ObligationStatus,
    pub counterexample: Option<String>,
    pub path: String,
    pub byte_offset: u32,
    pub line: u32,
    pub column: u32,
}

impl ObligationResult {
    pub fn satisfied(&self) -> bool {
        matches!(
            (self.expectation, self.status),
            (ObligationExpectation::Prove, ObligationStatus::Proved)
                | (ObligationExpectation::Refute, ObligationStatus::Refuted)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_arithmetic_over_boolean_terms() {
        let term = Term::Add {
            left: Box::new(Term::Bool { value: true }),
            right: Box::new(Term::Int { value: 1 }),
        };
        assert!(term.sort().unwrap_err().contains("expected Int"));
    }

    #[test]
    fn floor_division_requires_an_integer_and_a_positive_static_divisor() {
        assert_eq!(
            Term::FloorDivideByPositive {
                value: Box::new(Term::Int { value: -7 }),
                divisor: 2,
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert!(
            Term::FloorDivideByPositive {
                value: Box::new(Term::Int { value: 1 }),
                divisor: 0,
            }
            .sort()
            .is_err()
        );
        assert!(
            Term::FloorDivideByPositive {
                value: Box::new(Term::Bool { value: true }),
                divisor: 2,
            }
            .sort()
            .is_err()
        );
    }

    #[test]
    fn rejects_equality_between_different_sorts() {
        let term = Term::Equal {
            left: Box::new(Term::Bool { value: true }),
            right: Box::new(Term::Int { value: 1 }),
        };
        assert!(term.sort().unwrap_err().contains("different sorts"));
    }

    #[test]
    fn null_is_a_reference_value() {
        assert_eq!(Term::NullReference.sort().unwrap(), Sort::Reference);
        assert_eq!(
            Term::Equal {
                left: Box::new(Term::NullReference),
                right: Box::new(Term::Variable {
                    name: "object".to_owned(),
                    sort: Sort::Reference,
                }),
            }
            .sort()
            .unwrap(),
            Sort::Bool
        );
    }

    #[test]
    fn nominal_reference_requires_a_nonempty_class_identity() {
        assert_eq!(
            Term::NominalReference {
                name: "error".to_owned(),
                class: "AppError".to_owned(),
            }
            .sort()
            .unwrap(),
            Sort::Reference
        );
        assert!(
            Term::NominalReference {
                name: "error".to_owned(),
                class: String::new(),
            }
            .sort()
            .is_err()
        );
    }

    #[test]
    fn class_objects_are_distinct_from_runtime_references() {
        let class = Term::ClassLiteral {
            name: "Widget".to_owned(),
        };
        let object = Term::Variable {
            name: "widget".to_owned(),
            sort: Sort::Reference,
        };
        assert_eq!(class.sort().unwrap(), Sort::Class);
        assert_eq!(
            Term::RuntimeClass {
                value: Box::new(object),
            }
            .sort()
            .unwrap(),
            Sort::Class
        );
        assert_eq!(
            Term::ClassSubtype {
                actual: Box::new(class.clone()),
                expected: Box::new(class),
            }
            .sort()
            .unwrap(),
            Sort::Bool
        );
        assert!(
            Term::ClassSubtype {
                actual: Box::new(Term::NullReference),
                expected: Box::new(Term::ClassLiteral {
                    name: "Widget".to_owned(),
                }),
            }
            .sort()
            .is_err()
        );
    }

    #[test]
    fn predicate_instances_are_typed_references_keyed_by_arguments() {
        let instance = Term::PredicateInstance {
            predicate: "state".to_owned(),
            arguments: vec![
                Term::Variable {
                    name: "cell".to_owned(),
                    sort: Sort::Reference,
                },
                Term::Int { value: 12 },
            ],
        };
        assert_eq!(instance.sort().unwrap(), Sort::Reference);
        assert!(
            Term::PredicateInstance {
                predicate: String::new(),
                arguments: vec![Term::Int { value: 1 }],
            }
            .sort()
            .unwrap_err()
            .contains("name cannot be empty")
        );
        assert!(
            Term::PredicateInstance {
                predicate: "state".to_owned(),
                arguments: vec![Term::Unit],
            }
            .sort()
            .unwrap_err()
            .contains("first-order")
        );
    }

    #[test]
    fn conditional_requires_matching_branch_sorts() {
        let term = Term::IfThenElse {
            condition: Box::new(Term::Bool { value: true }),
            then_value: Box::new(Term::Int { value: 1 }),
            else_value: Box::new(Term::Bool { value: false }),
        };
        assert!(term.sort().unwrap_err().contains("different sorts"));
    }

    #[test]
    fn string_concatenation_and_length_have_distinct_checked_sorts() {
        let concatenated = Term::StringConcat {
            values: vec![
                Term::String {
                    value: "left".to_owned(),
                },
                Term::Variable {
                    name: "right".to_owned(),
                    sort: Sort::String,
                },
            ],
        };
        assert_eq!(concatenated.sort().unwrap(), Sort::String);
        assert_eq!(
            Term::StringLength {
                value: Box::new(concatenated),
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert!(
            Term::StringConcat {
                values: vec![Term::Int { value: 1 }],
            }
            .sort()
            .unwrap_err()
            .contains("expected String")
        );
    }

    #[test]
    fn bytes_concatenation_length_indexing_and_lists_are_typed() {
        let concatenated = Term::BytesConcat {
            values: vec![
                Term::Bytes { values: vec![1] },
                Term::Variable {
                    name: "tail".to_owned(),
                    sort: Sort::Bytes,
                },
            ],
        };
        assert_eq!(concatenated.sort().unwrap(), Sort::Bytes);
        assert_eq!(
            Term::BytesLength {
                value: Box::new(concatenated.clone()),
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert_eq!(
            Term::BytesGet {
                bytes: Box::new(concatenated),
                index: Box::new(Term::Int { value: 0 }),
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert_eq!(
            Term::List {
                element_sort: Sort::Bytes,
                values: vec![Term::Bytes { values: vec![1] }],
            }
            .sort()
            .unwrap(),
            Sort::List(Box::new(Sort::Bytes))
        );
        assert!(
            Term::BytesConcat {
                values: vec![Term::String {
                    value: "not bytes".to_owned(),
                }],
            }
            .sort()
            .is_err()
        );
    }

    #[test]
    fn tuple_construction_and_indexing_preserve_element_sorts() {
        let tuple = Term::Tuple {
            values: vec![
                Term::Int { value: 3 },
                Term::String {
                    value: "value".to_owned(),
                },
            ],
        };
        assert_eq!(
            tuple.sort().unwrap(),
            Sort::Tuple(vec![Sort::Int, Sort::String])
        );
        assert_eq!(
            Term::TupleGet {
                tuple: Box::new(tuple.clone()),
                index: 1,
            }
            .sort()
            .unwrap(),
            Sort::String
        );
        assert!(
            Term::TupleGet {
                tuple: Box::new(tuple),
                index: 2,
            }
            .sort()
            .unwrap_err()
            .contains("outside fixed tuple length")
        );
    }

    #[test]
    fn homogeneous_list_construction_length_and_indexing_are_typed() {
        let list = Term::List {
            element_sort: Sort::Int,
            values: vec![Term::Int { value: 3 }, Term::Int { value: 5 }],
        };
        assert_eq!(list.sort().unwrap(), Sort::List(Box::new(Sort::Int)));
        assert_eq!(
            Term::ListLength {
                value: Box::new(list.clone()),
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert_eq!(
            Term::ListGet {
                list: Box::new(list),
                index: Box::new(Term::Int { value: 1 }),
            }
            .sort()
            .unwrap(),
            Sort::Int
        );
        assert!(
            Term::List {
                element_sort: Sort::Int,
                values: vec![Term::Bool { value: true }],
            }
            .sort()
            .is_err()
        );
    }

    #[test]
    fn nested_mutable_collection_values_preserve_their_precise_sorts() {
        let inner_list = Term::List {
            element_sort: Sort::Int,
            values: vec![Term::Int { value: 1 }, Term::Int { value: 2 }],
        };
        let nested_list = Term::List {
            element_sort: Sort::List(Box::new(Sort::Int)),
            values: vec![inner_list],
        };
        assert_eq!(
            nested_list.sort_typed().unwrap(),
            Sort::List(Box::new(Sort::List(Box::new(Sort::Int))))
        );

        let nested_set_list = Term::List {
            element_sort: Sort::Set(Box::new(Sort::Int)),
            values: vec![Term::Variable {
                name: "numbers".to_owned(),
                sort: Sort::Set(Box::new(Sort::Int)),
            }],
        };
        assert_eq!(
            nested_set_list.sort_typed().unwrap(),
            Sort::List(Box::new(Sort::Set(Box::new(Sort::Int))))
        );

        let inner_dict = Term::FiniteDict {
            key_sort: Sort::Int,
            value_sort: Sort::Int,
            entries: vec![(Term::Int { value: 1 }, Term::Int { value: 2 })],
        };
        let outer_dict = Term::FiniteDict {
            key_sort: Sort::Int,
            value_sort: Sort::FiniteDict(Box::new(Sort::Int), Box::new(Sort::Int)),
            entries: vec![(Term::Int { value: 6 }, inner_dict)],
        };
        assert_eq!(
            outer_dict.sort_typed().unwrap(),
            Sort::FiniteDict(
                Box::new(Sort::Int),
                Box::new(Sort::FiniteDict(Box::new(Sort::Int), Box::new(Sort::Int)))
            )
        );
    }

    #[test]
    fn nested_mutable_collections_do_not_become_hashable_keys() {
        let invalid_dictionary = Term::FiniteDict {
            key_sort: Sort::List(Box::new(Sort::Int)),
            value_sort: Sort::Int,
            entries: vec![(
                Term::List {
                    element_sort: Sort::Int,
                    values: vec![Term::Int { value: 1 }],
                },
                Term::Int { value: 2 },
            )],
        };
        assert!(matches!(
            invalid_dictionary.sort_typed(),
            Err(SortError::FiniteDictionaryKeySortUnsupported {
                sort: Sort::List(_)
            })
        ));
    }

    #[test]
    fn bytes_and_ranges_retain_distinct_source_sorts() {
        assert_eq!(
            Term::Bytes {
                values: vec![49, 50],
            }
            .sort()
            .unwrap(),
            Sort::Bytes
        );
        assert_eq!(
            Term::Range { values: vec![1, 2] }.sort().unwrap(),
            Sort::Range
        );
        assert_ne!(Sort::Bytes, Sort::List(Box::new(Sort::Int)));
        assert_ne!(Sort::Range, Sort::List(Box::new(Sort::Int)));
        assert_ne!(Sort::Bytes, Sort::Range);
    }

    #[test]
    fn field_reads_require_references_and_preserve_the_field_sort() {
        let term = Term::FieldRead {
            heap: 0,
            receiver: Box::new(Term::Variable {
                name: "object".to_owned(),
                sort: Sort::Reference,
            }),
            field: "value".to_owned(),
            sort: Sort::Int,
        };
        assert_eq!(term.sort().unwrap(), Sort::Int);
    }

    #[test]
    fn permission_atoms_reject_invalid_fractions() {
        let term = Term::PermissionAtLeast {
            mask: 0,
            receiver: Box::new(Term::Variable {
                name: "object".to_owned(),
                sort: Sort::Reference,
            }),
            field: "value".to_owned(),
            numerator: 2,
            denominator: 1,
        };
        assert!(term.sort().unwrap_err().contains("outside [0, 1]"));
    }

    #[test]
    fn positive_permission_atoms_require_reference_receivers() {
        let term = Term::PermissionPositive {
            mask: 0,
            receiver: Box::new(Term::Int { value: 1 }),
            field: "value".to_owned(),
        };
        assert!(term.sort().unwrap_err().contains("expected Reference"));
    }

    #[test]
    fn permission_mask_transition_requires_distinct_versions_and_typed_receivers() {
        let same_version = Term::PermissionMaskTransition {
            pre_mask: 2,
            post_mask: 2,
            field: "value".to_owned(),
            consumed: Vec::new(),
            produced: Vec::new(),
        };
        assert!(same_version.sort().unwrap_err().contains("must advance"));

        let untyped_receiver = Term::PermissionMaskTransition {
            pre_mask: 2,
            post_mask: 3,
            field: "value".to_owned(),
            consumed: vec![PermissionTransferAmount {
                receiver: Box::new(Term::Int { value: 1 }),
                numerator: 1,
                denominator: 2,
            }],
            produced: Vec::new(),
        };
        assert!(
            untyped_receiver
                .sort()
                .unwrap_err()
                .contains("expected Reference")
        );
    }

    #[test]
    fn every_structured_sort_error_has_the_compatibility_text() {
        let cases = [
            (
                SortError::IntEnumDescriptorMissingClassOrMember,
                "IntEnum descriptor requires a class and at least one member",
            ),
            (
                SortError::IntEnumDescriptorMembersNotUnique,
                "IntEnum descriptor member names and integer values must be nonempty and unique",
            ),
            (
                SortError::IntEnumProjectionRequiresValue,
                "IntEnum projection/domain requires a descriptor-carrying IntEnum value",
            ),
            (
                SortError::IntEnumIdentityRequiresValues,
                "IntEnum identity requires two descriptor-carrying IntEnum values",
            ),
            (
                SortError::NominalReferenceClassEmpty,
                "nominal reference class cannot be empty",
            ),
            (
                SortError::ClassLiteralNameEmpty,
                "class literal name cannot be empty",
            ),
            (
                SortError::PredicateInstanceNameEmpty,
                "predicate instance name cannot be empty",
            ),
            (
                SortError::PredicateInstanceArgumentsEmpty,
                "predicate instance requires at least one argument",
            ),
            (
                SortError::PredicateArgumentSortUnsupported,
                "predicate instance arguments must have a first-order scalar, reference, or class sort",
            ),
            (
                SortError::SequenceElementSortUnsupported { sort: Sort::Unit },
                "list element sort Unit is not supported by the sequence VC",
            ),
            (
                SortError::HeapFieldSortUnsupported,
                "heap fields cannot have Unit, Class, Bytes, Range, or Tuple sort",
            ),
            (
                SortError::HeapListElementSortUnsupported { sort: Sort::Unit },
                "heap list field element sort Unit is not supported by the sequence VC",
            ),
            (
                SortError::PermissionFractionOutsideUnit {
                    numerator: 2,
                    denominator: 1,
                },
                "permission fraction 2/1 is outside [0, 1]",
            ),
            (
                SortError::PermissionTransferFractionOutsideUnit {
                    numerator: 3,
                    denominator: 2,
                },
                "permission-transfer fraction 3/2 is outside [0, 1]",
            ),
            (
                SortError::PermissionMaskFieldEmpty,
                "permission-mask field cannot be empty",
            ),
            (
                SortError::PermissionMaskTransitionDoesNotAdvance,
                "permission-mask transition must advance the mask",
            ),
            (
                SortError::PermissionMaskTransitionFieldEmpty,
                "permission-mask transition field cannot be empty",
            ),
            (
                SortError::ConditionalBranchSortMismatch {
                    then_sort: Sort::Int,
                    else_sort: Sort::Bool,
                },
                "conditional branches have different sorts: Int and Bool",
            ),
            (
                SortError::EqualityOperandSortMismatch {
                    left_sort: Sort::String,
                    right_sort: Sort::Bytes,
                },
                "equality operands have different sorts: String and Bytes",
            ),
            (
                SortError::FloorDivisionDivisorNotPositive,
                "floor-division divisor must be positive",
            ),
            (
                SortError::TupleOperandRequired,
                "tuple indexing requires a Tuple operand",
            ),
            (
                SortError::TupleIndexOutsideLength {
                    index: 4,
                    length: 2,
                },
                "tuple index 4 is outside fixed tuple length 2",
            ),
            (
                SortError::ListLengthOperandNotList { actual: Sort::Int },
                "list length operand has sort Int, expected List",
            ),
            (
                SortError::ListOperandRequiredForIndex,
                "list indexing requires a List operand",
            ),
            (
                SortError::ListOperandRequiredForMembership,
                "list membership requires a List operand",
            ),
            (
                SortError::ListSliceOperandNotList { actual: Sort::Bool },
                "list slicing operand has sort Bool, expected List",
            ),
            (
                SortError::ListConcatLeftOperandNotList { actual: Sort::Bool },
                "left list-concatenation operand has sort Bool, expected List",
            ),
            (
                SortError::ListConcatRightOperandNotList {
                    actual: Sort::String,
                },
                "right list-concatenation operand has sort String, expected List",
            ),
            (
                SortError::ListConcatElementSortMismatch {
                    left_element: Sort::Int,
                    right_element: Sort::Bool,
                },
                "list-concatenation operands have different element sorts: Int and Bool",
            ),
            (
                SortError::ListSumOperandNotIntegerList {
                    actual: Sort::List(Box::new(Sort::Bool)),
                },
                "list sum operand has sort List(Bool), expected List[Int]",
            ),
            (
                SortError::ListSortedOperandNotIntegerList {
                    actual: Sort::String,
                },
                "list sorted operand has sort String, expected List[Int]",
            ),
            (
                SortError::ListSourceRequiredForComprehension,
                "list comprehension requires a List source",
            ),
            (
                SortError::SetSourceRequiredForComprehension,
                "set comprehension requires a List source",
            ),
            (
                SortError::SetComprehensionElementSortUnsupported { sort: Sort::Class },
                "set-comprehension element sort Class is unsupported",
            ),
            (
                SortError::SetLengthOperandNotSet {
                    actual: Sort::Range,
                },
                "set length operand has sort Range, expected Set",
            ),
            (
                SortError::SetOperandRequiredForMembership,
                "set membership requires a Set operand",
            ),
            (
                SortError::DictionarySourceRequiredForComprehension,
                "dictionary comprehension requires a List source",
            ),
            (
                SortError::DictionaryComprehensionSortsUnsupported {
                    key_sort: Sort::Class,
                    value_sort: Sort::Unit,
                },
                "dictionary-comprehension sorts Class/Unit are unsupported",
            ),
            (
                SortError::DictionaryLengthOperandNotDictionary { actual: Sort::Bool },
                "dictionary length operand has sort Bool, expected Dict",
            ),
            (
                SortError::DictionaryOperandRequiredForMembership,
                "dictionary membership requires a Dict operand",
            ),
            (
                SortError::DictionaryOperandRequiredForLookup,
                "dictionary lookup requires a Dict operand",
            ),
            (
                SortError::QuantifierBinderEmpty,
                "quantifier binder cannot be empty",
            ),
            (
                SortError::ComprehensionBinderEmpty,
                "comprehension binder cannot be empty",
            ),
            (
                SortError::FiniteDictionaryKeySortUnsupported {
                    sort: Sort::Reference,
                },
                "finite dictionary key sort Reference is unsupported",
            ),
            (
                SortError::FiniteDictionaryValueSortUnsupported { sort: Sort::Class },
                "finite dictionary value sort Class is unsupported",
            ),
            (
                SortError::DictionaryKeySortUnsupported { sort: Sort::Bool },
                "dictionary-key sort Bool is unsupported",
            ),
            (
                SortError::BinderSortMismatch {
                    binder: "value".to_owned(),
                    actual: Sort::Int,
                    expected: Sort::Bool,
                },
                "binder \"value\" occurs with sort Int, expected Bool",
            ),
            (
                SortError::NestedBinderCapture {
                    binder: "item".to_owned(),
                },
                "nested binder \"item\" captures an outer bound variable",
            ),
            (
                SortError::UnexpectedSort {
                    context: SortContext::ConditionalGuard,
                    actual: Sort::Int,
                    expected: Sort::Bool,
                },
                "conditional guard has sort Int, expected Bool",
            ),
        ];

        for (error, expected) in cases {
            assert_eq!(error.to_string(), expected);
        }
    }

    #[test]
    fn every_sort_context_has_stable_compatibility_text() {
        let cases = [
            (SortContext::IntEnumNumericValue, "IntEnum numeric value"),
            (SortContext::RuntimeClassOperand, "runtime-class operand"),
            (
                SortContext::SubclassActualOperand,
                "subclass actual operand",
            ),
            (
                SortContext::SubclassExpectedOperand,
                "subclass expected operand",
            ),
            (SortContext::FieldReceiver, "field receiver"),
            (SortContext::PermissionReceiver, "permission receiver"),
            (SortContext::NotOperand, "not operand"),
            (SortContext::BooleanOperand, "boolean operand"),
            (
                SortContext::ImplicationLeftOperand,
                "implication left operand",
            ),
            (
                SortContext::ImplicationRightOperand,
                "implication right operand",
            ),
            (SortContext::ConditionalGuard, "conditional guard"),
            (SortContext::IntegerLeftOperand, "integer left operand"),
            (SortContext::IntegerRightOperand, "integer right operand"),
            (SortContext::FloorDivisionOperand, "floor-division operand"),
            (SortContext::NegationOperand, "negation operand"),
            (
                SortContext::StringConcatenationOperand,
                "string concatenation operand",
            ),
            (SortContext::StringLengthOperand, "string length operand"),
            (
                SortContext::BytesConcatenationOperand,
                "bytes concatenation operand",
            ),
            (SortContext::BytesLengthOperand, "bytes length operand"),
            (SortContext::BytesIndexReceiver, "bytes index receiver"),
            (SortContext::BytesIndex, "bytes index"),
            (SortContext::ListElement, "list element"),
            (SortContext::ListIndex, "list index"),
            (SortContext::ListMembershipValue, "list membership value"),
            (SortContext::SetMembershipValue, "set membership value"),
            (SortContext::DictionaryValue, "dictionary value"),
            (SortContext::DictionaryKey, "dictionary key"),
            (
                SortContext::DictionaryMembershipKey,
                "dictionary membership key",
            ),
            (SortContext::DictionaryLookupKey, "dictionary lookup key"),
            (
                SortContext::PermissionTransferReceiver,
                "permission-transfer receiver",
            ),
            (SortContext::FiniteDictionaryKey, "finite dictionary key"),
            (
                SortContext::FiniteDictionaryValue,
                "finite dictionary value",
            ),
            (SortContext::ComprehensionMapper, "comprehension mapper"),
            (SortContext::ComprehensionFilter, "comprehension filter"),
            (SortContext::QuantifierBody, "quantifier body"),
        ];

        for (context, expected) in cases {
            assert_eq!(context.as_str(), expected);
        }
    }

    #[test]
    fn compatibility_sort_renders_the_typed_failure_without_changing_it() {
        let terms = [
            Term::NominalReference {
                name: "object".to_owned(),
                class: String::new(),
            },
            Term::PermissionAtLeast {
                mask: 0,
                receiver: Box::new(Term::NullReference),
                field: "value".to_owned(),
                numerator: 2,
                denominator: 1,
            },
            Term::TupleGet {
                tuple: Box::new(Term::Tuple { values: Vec::new() }),
                index: 1,
            },
        ];

        for term in terms {
            let structured = term.sort_typed().unwrap_err();
            assert_eq!(term.sort().unwrap_err(), structured.to_string());
        }
    }
}
