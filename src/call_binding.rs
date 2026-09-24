//! Canonical, frontend-independent binding of Python call arguments.
//!
//! This module deliberately operates on values that a frontend has already evaluated.  It
//! records the source evaluation order, expands only statically known `*` values, optionally
//! injects one method receiver, and produces one binding cell per formal parameter.  Dynamic
//! iterable expansion and every `**mapping` expansion fail closed at this boundary.

/// Machine-readable identity for the shared finite Python call-binding kernel.
pub const IDENTITY: &str = "python-call-argument-binding/v3";

/// A value paired with the type known by the calling frontend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedValue<Type, Value> {
    pub type_tag: Type,
    pub value: Value,
}

impl<Type, Value> TypedValue<Type, Value> {
    pub fn new(type_tag: Type, value: Value) -> Self {
        Self { type_tag, value }
    }
}

/// One ordinary, keyword-only, or variadic formal parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FormalParameter<Type, Value> {
    pub name: String,
    pub expected_type: Type,
    pub default_value: Option<TypedValue<Type, Value>>,
}

impl<Type, Value> FormalParameter<Type, Value> {
    pub fn required(name: impl Into<String>, expected_type: Type) -> Self {
        Self {
            name: name.into(),
            expected_type,
            default_value: None,
        }
    }

    pub fn defaulted(
        name: impl Into<String>,
        expected_type: Type,
        default_value: TypedValue<Type, Value>,
    ) -> Self {
        Self {
            name: name.into(),
            expected_type,
            default_value: Some(default_value),
        }
    }
}

/// The finite signature supported by the v59 call-binding boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallSignature<Type, Value> {
    /// Parameters before `/`; they can never be supplied by name.
    pub positional_only: Vec<FormalParameter<Type, Value>>,
    /// Parameters after `/` and before `*`; they accept positions or names.
    pub positional: Vec<FormalParameter<Type, Value>>,
    pub keyword_only: Vec<FormalParameter<Type, Value>>,
    pub var_args: Option<FormalParameter<Type, Value>>,
    pub keyword_args: Option<FormalParameter<Type, Value>>,
}

impl<Type, Value> Default for CallSignature<Type, Value> {
    fn default() -> Self {
        Self {
            positional_only: Vec::new(),
            positional: Vec::new(),
            keyword_only: Vec::new(),
            var_args: None,
            keyword_args: None,
        }
    }
}

/// A source argument before fixed expansion and receiver injection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ActualItem<Type, Value> {
    Positional(TypedValue<Type, Value>),
    Named {
        name: String,
        value: TypedValue<Type, Value>,
    },
    /// A statically known finite star expansion, such as a fixed-length tuple.
    FixedStar(Vec<TypedValue<Type, Value>>),
    /// An iterable whose length or elements are not statically known.
    DynamicStar,
    /// Any `**mapping` expression.  Even a fixed mapping is outside the v59 boundary.
    KeywordMapping,
}

/// A method receiver evaluated before all explicit call arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receiver<Type, Value> {
    pub value: TypedValue<Type, Value>,
}

impl<Type, Value> Receiver<Type, Value> {
    pub fn new(value: TypedValue<Type, Value>) -> Self {
        Self { value }
    }
}

/// The origin of one expanded positional value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PositionalOrigin {
    Explicit,
    FixedStar,
    Receiver,
}

/// Stable source-order metadata for one expanded value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum EvaluationPosition {
    Receiver,
    Actual {
        item_index: usize,
        expansion_index: usize,
    },
}

/// One evaluation event.  A fixed star is evaluated once even though it contributes many values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvaluationEvent {
    Receiver,
    Positional {
        item_index: usize,
    },
    Named {
        item_index: usize,
        name: String,
    },
    FixedStar {
        item_index: usize,
        element_count: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositionalActual<Type, Value> {
    pub value: TypedValue<Type, Value>,
    pub origin: PositionalOrigin,
    pub evaluation_position: EvaluationPosition,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NamedActual<Type, Value> {
    pub name: String,
    pub value: TypedValue<Type, Value>,
    pub evaluation_position: EvaluationPosition,
}

/// Expanded arguments and the order in which their source expressions are evaluated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExpandedCall<Type, Value> {
    pub positional: Vec<PositionalActual<Type, Value>>,
    pub named: Vec<NamedActual<Type, Value>>,
    pub evaluation_order: Vec<EvaluationEvent>,
}

/// Formal parameter categories in a canonical binding environment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParameterKind {
    PositionalOnly,
    Positional,
    KeywordOnly,
    VarArgs,
    KeywordArgs,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundArgument<Type, Value> {
    SuppliedPositional(PositionalActual<Type, Value>),
    SuppliedNamed(NamedActual<Type, Value>),
    Defaulted(TypedValue<Type, Value>),
    ResidualPositionals(Vec<PositionalActual<Type, Value>>),
    ResidualKeywords(Vec<NamedActual<Type, Value>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BindingCell<Type, Value> {
    pub parameter: FormalParameter<Type, Value>,
    pub kind: ParameterKind,
    pub argument: BoundArgument<Type, Value>,
}

/// The unique formal-order environment produced by successful binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BindingEnvironment<Type, Value> {
    pub cells: Vec<BindingCell<Type, Value>>,
    pub evaluation_order: Vec<EvaluationEvent>,
}

impl<Type, Value> BindingEnvironment<Type, Value> {
    pub fn get(&self, name: &str) -> Option<&BindingCell<Type, Value>> {
        self.cells.iter().find(|cell| cell.parameter.name == name)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MalformedSignature<Type> {
    ParameterCountOverflow {
        accumulated: usize,
        contribution: usize,
    },
    EmptyParameterName,
    DuplicateParameter {
        name: String,
    },
    VariadicDefault {
        name: String,
    },
    DefaultTypeMismatch {
        parameter: String,
        expected: Type,
        actual: Type,
    },
}

/// Stable identity for each allocation whose failure is observable at the binding boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AllocationSite {
    SignatureNames,
    ExpandedPositionals,
    ExpandedNamed,
    EvaluationOrder,
    BindingCells,
    ResidualPositionals,
    ResidualKeywords,
}

/// Deterministic failures returned by the binding kernel.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingError<Type> {
    MalformedSignature(MalformedSignature<Type>),
    DynamicStarUnsupported {
        item_index: usize,
    },
    KeywordMappingUnsupported {
        item_index: usize,
    },
    SourceExpressionCountOverflow {
        item_count: usize,
        receiver_count: usize,
    },
    ExpandedArgumentCountOverflow {
        item_index: usize,
        accumulated: usize,
        contribution: usize,
    },
    AllocationFailed {
        site: AllocationSite,
        requested: usize,
    },
    DuplicateNamedArgument {
        name: String,
    },
    DuplicateBinding {
        parameter: String,
    },
    TooManyPositionals {
        expected: usize,
        actual: usize,
    },
    UnexpectedKeyword {
        name: String,
    },
    MissingRequiredArgument {
        parameter: String,
    },
    TypeMismatch {
        parameter: String,
        expected: Type,
        actual: Type,
        position: Option<EvaluationPosition>,
    },
}

pub(crate) trait BindingAllocator {
    fn allocate<T>(&mut self, site: AllocationSite, requested: usize) -> Result<Vec<T>, ()>;
}

struct SystemBindingAllocator;

impl BindingAllocator for SystemBindingAllocator {
    fn allocate<T>(&mut self, _site: AllocationSite, requested: usize) -> Result<Vec<T>, ()> {
        let mut values = Vec::new();
        match values.try_reserve_exact(requested) {
            Ok(()) => Ok(values),
            Err(_) => Err(()),
        }
    }
}

fn allocate_buffer<Type, T, Allocator>(
    allocator: &mut Allocator,
    site: AllocationSite,
    requested: usize,
) -> Result<Vec<T>, BindingError<Type>>
where
    Allocator: BindingAllocator,
{
    match allocator.allocate(site, requested) {
        Ok(values) => Ok(values),
        Err(()) => Err(BindingError::AllocationFailed { site, requested }),
    }
}

trait TypeCompatibility<Type> {
    fn accepts(&self, expected: &Type, actual: &Type) -> bool;
}

struct ExactTypeCompatibility;

impl<Type: Eq> TypeCompatibility<Type> for ExactTypeCompatibility {
    fn accepts(&self, expected: &Type, actual: &Type) -> bool {
        expected == actual
    }
}

// Aeneas 2026.08 mis-translates a negated Bool stored in loop state as Prop negation. Keeping
// this explicit total choice preserves Rust semantics while producing a well-typed Lean Bool.
#[allow(clippy::needless_bool)]
fn compatibility_mismatch<Type, Compatibility>(
    compatibility: &Compatibility,
    expected: &Type,
    actual: &Type,
) -> bool
where
    Compatibility: TypeCompatibility<Type>,
{
    if compatibility.accepts(expected, actual) {
        false
    } else {
        true
    }
}

struct CallbackTypeCompatibility<Compatible>(Compatible);

impl<Type, Compatible> TypeCompatibility<Type> for CallbackTypeCompatibility<Compatible>
where
    Compatible: Fn(&Type, &Type) -> bool,
{
    fn accepts(&self, expected: &Type, actual: &Type) -> bool {
        (self.0)(expected, actual)
    }
}

/// Bind using exact equality between expected and actual type tags.
pub fn bind_call<Type, Value>(
    signature: &CallSignature<Type, Value>,
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone + Eq,
    Value: Clone,
{
    bind_call_with_allocator(signature, items, receiver, &mut SystemBindingAllocator)
}

/// Exact-equality binding over an explicit allocation boundary.
///
/// This is the source-bound verification seam used by the all-input refinement proof.  The
/// production [`bind_call`] wrapper supplies [`SystemBindingAllocator`], while the proof treats
/// every normal typed allocator response as an explicit outcome rather than assuming allocation
/// succeeds.  The allocator remains crate-private so callers cannot bypass the system adapter's
/// `try_reserve_exact` contract.
pub(crate) fn bind_call_with_allocator<Type, Value, Allocator>(
    signature: &CallSignature<Type, Value>,
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
    allocator: &mut Allocator,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone + Eq,
    Value: Clone,
    Allocator: BindingAllocator,
{
    bind_call_with_relation(
        signature,
        items,
        receiver,
        ExactTypeCompatibility,
        allocator,
    )
}

/// Bind using a frontend-provided type compatibility relation.
///
/// `compatible(expected, actual)` is also applied to declared defaults, so an invalid imported
/// signature cannot introduce an ill-typed value through defaulting.
pub fn bind_call_with<Type, Value, Compatible>(
    signature: &CallSignature<Type, Value>,
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
    compatible: Compatible,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
    Compatible: Fn(&Type, &Type) -> bool,
{
    bind_call_with_relation(
        signature,
        items,
        receiver,
        CallbackTypeCompatibility(compatible),
        &mut SystemBindingAllocator,
    )
}

fn bind_call_with_relation<Type, Value, Compatibility, Allocator>(
    signature: &CallSignature<Type, Value>,
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
    compatibility: Compatibility,
    allocator: &mut Allocator,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
    Compatibility: TypeCompatibility<Type>,
    Allocator: BindingAllocator,
{
    let counts = validate_signature(signature, &compatibility, allocator)?;
    let expanded = expand_actual_items_with_allocator(items, receiver, allocator)?;
    bind_expanded_call_with(signature, expanded, counts, &compatibility, allocator)
}

/// Bind one already-expanded call after [`validate_signature`] has accepted the signature with
/// the same compatibility relation.
///
/// Keeping this seam after expansion makes the production parameter-binding phase independently
/// extractable without changing `bind_call_with`'s error precedence: malformed signatures still
/// fail before argument expansion, then expansion errors precede call-validation errors.
fn bind_expanded_call_with<Type, Value, Compatibility, Allocator>(
    signature: &CallSignature<Type, Value>,
    expanded: ExpandedCall<Type, Value>,
    counts: SignatureCounts,
    compatibility: &Compatibility,
    allocator: &mut Allocator,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
    Compatibility: TypeCompatibility<Type>,
    Allocator: BindingAllocator,
{
    validate_call(signature, &expanded, counts.positional_count, compatibility)?;
    canonical_environment(signature, expanded, counts, allocator)
}

/// Expand fixed stars and inject an optional receiver without performing formal binding.
pub fn expand_actual_items<Type, Value>(
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
) -> Result<ExpandedCall<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
{
    expand_actual_items_with_allocator(items, receiver, &mut SystemBindingAllocator)
}

fn expand_actual_items_with_allocator<Type, Value, Allocator>(
    items: &[ActualItem<Type, Value>],
    receiver: Option<Receiver<Type, Value>>,
    allocator: &mut Allocator,
) -> Result<ExpandedCall<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
    Allocator: BindingAllocator,
{
    let (source_count, expanded_count) = preflight_actual_items(items, receiver.is_some())?;
    let mut positional = allocate_buffer(
        allocator,
        AllocationSite::ExpandedPositionals,
        expanded_count,
    )?;
    let mut named = allocate_buffer(allocator, AllocationSite::ExpandedNamed, source_count)?;
    let mut evaluation_order =
        allocate_buffer(allocator, AllocationSite::EvaluationOrder, source_count)?;
    let mut expansion_error: Option<BindingError<Type>> = None;

    if let Some(receiver) = receiver {
        evaluation_order.push(EvaluationEvent::Receiver);
        positional.push(PositionalActual {
            value: receiver.value,
            origin: PositionalOrigin::Receiver,
            evaluation_position: EvaluationPosition::Receiver,
        });
    }

    for (item_index, item) in items.iter().enumerate() {
        if expansion_error.is_none() {
            match item {
                ActualItem::Positional(value) => {
                    evaluation_order.push(EvaluationEvent::Positional { item_index });
                    positional.push(PositionalActual {
                        value: value.clone(),
                        origin: PositionalOrigin::Explicit,
                        evaluation_position: EvaluationPosition::Actual {
                            item_index,
                            expansion_index: 0,
                        },
                    });
                }
                ActualItem::Named { name, value } => {
                    evaluation_order.push(EvaluationEvent::Named {
                        item_index,
                        name: name.clone(),
                    });
                    named.push(NamedActual {
                        name: name.clone(),
                        value: value.clone(),
                        evaluation_position: EvaluationPosition::Actual {
                            item_index,
                            expansion_index: 0,
                        },
                    });
                }
                ActualItem::FixedStar(values) => {
                    evaluation_order.push(EvaluationEvent::FixedStar {
                        item_index,
                        element_count: values.len(),
                    });
                    for (expansion_index, value) in values.iter().enumerate() {
                        positional.push(PositionalActual {
                            value: value.clone(),
                            origin: PositionalOrigin::FixedStar,
                            evaluation_position: EvaluationPosition::Actual {
                                item_index,
                                expansion_index,
                            },
                        });
                    }
                }
                ActualItem::DynamicStar => {
                    expansion_error = Some(BindingError::DynamicStarUnsupported { item_index });
                }
                ActualItem::KeywordMapping => {
                    expansion_error = Some(BindingError::KeywordMappingUnsupported { item_index });
                }
            }
        }
    }

    if let Some(error) = expansion_error {
        return Err(error);
    }

    Ok(ExpandedCall {
        positional,
        named,
        evaluation_order,
    })
}

fn preflight_actual_items<Type, Value>(
    items: &[ActualItem<Type, Value>],
    has_receiver: bool,
) -> Result<(usize, usize), BindingError<Type>> {
    let receiver_count = usize::from(has_receiver);
    let source_count = match items.len().checked_add(receiver_count) {
        Some(count) => count,
        None => {
            return Err(BindingError::SourceExpressionCountOverflow {
                item_count: items.len(),
                receiver_count,
            });
        }
    };

    let mut expanded_count = receiver_count;
    let mut preflight_error: Option<BindingError<Type>> = None;
    for (item_index, item) in items.iter().enumerate() {
        if preflight_error.is_none() {
            let contribution = match item {
                ActualItem::Positional(_) | ActualItem::Named { .. } => 1,
                ActualItem::FixedStar(values) => values.len(),
                ActualItem::DynamicStar => {
                    preflight_error = Some(BindingError::DynamicStarUnsupported { item_index });
                    0
                }
                ActualItem::KeywordMapping => {
                    preflight_error = Some(BindingError::KeywordMappingUnsupported { item_index });
                    0
                }
            };
            if preflight_error.is_none() {
                match expanded_count.checked_add(contribution) {
                    Some(count) => expanded_count = count,
                    None => {
                        preflight_error = Some(BindingError::ExpandedArgumentCountOverflow {
                            item_index,
                            accumulated: expanded_count,
                            contribution,
                        });
                    }
                }
            }
        }
    }

    match preflight_error {
        Some(error) => Err(error),
        None => Ok((source_count, expanded_count)),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SignatureCounts {
    parameter_count: usize,
    positional_count: usize,
}

fn add_parameter_count<Type>(
    accumulated: usize,
    contribution: usize,
) -> Result<usize, BindingError<Type>> {
    match accumulated.checked_add(contribution) {
        Some(count) => Ok(count),
        None => Err(BindingError::MalformedSignature(
            MalformedSignature::ParameterCountOverflow {
                accumulated,
                contribution,
            },
        )),
    }
}

fn signature_counts<Type, Value>(
    signature: &CallSignature<Type, Value>,
) -> Result<SignatureCounts, BindingError<Type>> {
    let positional_count =
        add_parameter_count(signature.positional_only.len(), signature.positional.len())?;
    let mut parameter_count = add_parameter_count(positional_count, signature.keyword_only.len())?;
    parameter_count =
        add_parameter_count(parameter_count, usize::from(signature.var_args.is_some()))?;
    parameter_count = add_parameter_count(
        parameter_count,
        usize::from(signature.keyword_args.is_some()),
    )?;
    Ok(SignatureCounts {
        parameter_count,
        positional_count,
    })
}

fn named_actual_index<Type, Value>(actuals: &[NamedActual<Type, Value>], name: &String) -> usize {
    let actual_count = actuals.len();
    let mut index = 0;
    let mut found = false;
    while index < actual_count && !found {
        found = &actuals[index].name == name;
        index += 1;
    }
    if found { index - 1 } else { actual_count }
}

fn find_named_actual<'a, Type, Value>(
    actuals: &'a [NamedActual<Type, Value>],
    name: &String,
) -> Option<&'a NamedActual<Type, Value>> {
    let index = named_actual_index(actuals, name);
    if index < actuals.len() {
        Some(&actuals[index])
    } else {
        None
    }
}

fn first_duplicate_named_actual<Type, Value>(
    actuals: &[NamedActual<Type, Value>],
) -> Option<String> {
    let mut outer_index = 0;
    let mut duplicate = None;
    while outer_index < actuals.len() && duplicate.is_none() {
        let candidate = actuals[outer_index].name.clone();
        let mut inner_index = 0;
        let mut seen = false;
        while inner_index < outer_index && !seen {
            seen = actuals[inner_index].name == candidate;
            inner_index += 1;
        }
        if seen {
            duplicate = Some(candidate);
        }
        outer_index += 1;
    }
    duplicate
}

fn first_duplicate_binding<Type, Value>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
) -> Option<BindingError<Type>>
where
    Type: Clone,
{
    let mut ordinary_position = signature.positional_only.len();
    let mut parameter_index = 0;
    let mut duplicate = false;
    while parameter_index < signature.positional.len() && !duplicate {
        let parameter = &signature.positional[parameter_index];
        duplicate = ordinary_position < call.positional.len()
            && named_actual_index(&call.named, &parameter.name) < call.named.len();
        ordinary_position += 1;
        parameter_index += 1;
    }
    if duplicate {
        Some(BindingError::DuplicateBinding {
            parameter: signature.positional[parameter_index - 1].name.clone(),
        })
    } else {
        None
    }
}

fn first_missing_required_argument<Type, Value>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
) -> Option<BindingError<Type>>
where
    Type: Clone,
{
    let mut error = first_missing_positional_only(signature, call);
    if error.is_none() {
        error = first_missing_ordinary(signature, call);
    }
    if error.is_none() {
        error = first_missing_keyword_only(signature, call);
    }
    error
}

fn first_missing_positional_only<Type, Value>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
) -> Option<BindingError<Type>>
where
    Type: Clone,
{
    let parameter_count = signature.positional_only.len();
    let mut index = 0;
    let mut is_missing = false;
    while index < parameter_count && !is_missing {
        let parameter = &signature.positional_only[index];
        is_missing = index >= call.positional.len() && parameter.default_value.is_none();
        index += 1;
    }
    if is_missing {
        Some(BindingError::MissingRequiredArgument {
            parameter: signature.positional_only[index - 1].name.clone(),
        })
    } else {
        None
    }
}

fn first_missing_ordinary<Type, Value>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
) -> Option<BindingError<Type>>
where
    Type: Clone,
{
    let positional_offset = signature.positional_only.len();
    let mut parameter_index = 0;
    let mut is_missing = false;
    while parameter_index < signature.positional.len() && !is_missing {
        let index = positional_offset + parameter_index;
        let parameter_name = signature.positional[parameter_index].name.clone();
        let has_default = signature.positional[parameter_index]
            .default_value
            .is_some();
        let named_index = named_actual_index(&call.named, &parameter_name);
        is_missing =
            index >= call.positional.len() && named_index == call.named.len() && !has_default;
        parameter_index += 1;
    }
    if is_missing {
        Some(BindingError::MissingRequiredArgument {
            parameter: signature.positional[parameter_index - 1].name.clone(),
        })
    } else {
        None
    }
}

fn first_missing_keyword_only<Type, Value>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
) -> Option<BindingError<Type>>
where
    Type: Clone,
{
    let mut keyword_index = 0;
    let mut is_missing = false;
    while keyword_index < signature.keyword_only.len() && !is_missing {
        let parameter_name = signature.keyword_only[keyword_index].name.clone();
        let has_default = signature.keyword_only[keyword_index]
            .default_value
            .is_some();
        let named_index = named_actual_index(&call.named, &parameter_name);
        is_missing = named_index == call.named.len() && !has_default;
        keyword_index += 1;
    }
    if is_missing {
        Some(BindingError::MissingRequiredArgument {
            parameter: signature.keyword_only[keyword_index - 1].name.clone(),
        })
    } else {
        None
    }
}

fn first_positional_only_type_mismatch<Type, Value, Compatibility>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let comparable_count = signature.positional_only.len().min(call.positional.len());
    let mut index = 0;
    let mut mismatch = false;
    while index < comparable_count && !mismatch {
        let parameter = &signature.positional_only[index];
        let actual = &call.positional[index];
        mismatch = compatibility_mismatch(
            compatibility,
            &parameter.expected_type,
            &actual.value.type_tag,
        );
        index += 1;
    }
    if mismatch {
        let parameter = &signature.positional_only[index - 1];
        let actual = &call.positional[index - 1];
        Some(BindingError::TypeMismatch {
            parameter: parameter.name.clone(),
            expected: parameter.expected_type.clone(),
            actual: actual.value.type_tag.clone(),
            position: Some(actual.evaluation_position),
        })
    } else {
        None
    }
}

fn first_ordinary_type_mismatch<Type, Value, Compatibility>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let positional_offset = signature.positional_only.len();
    let mut parameter_index = 0;
    let mut mismatch = false;
    let mut actual_index = 0;
    let mut supplied_by_name = false;
    while parameter_index < signature.positional.len() && !mismatch {
        let parameter = &signature.positional[parameter_index];
        let index = positional_offset + parameter_index;
        let result = ordinary_actual_mismatch(parameter, call, index, compatibility);
        mismatch = result.0;
        actual_index = result.1;
        supplied_by_name = result.2;
        parameter_index += 1;
    }
    if mismatch {
        let parameter = &signature.positional[parameter_index - 1];
        if supplied_by_name {
            let actual = &call.named[actual_index];
            Some(BindingError::TypeMismatch {
                parameter: parameter.name.clone(),
                expected: parameter.expected_type.clone(),
                actual: actual.value.type_tag.clone(),
                position: Some(actual.evaluation_position),
            })
        } else {
            let actual = &call.positional[actual_index];
            Some(BindingError::TypeMismatch {
                parameter: parameter.name.clone(),
                expected: parameter.expected_type.clone(),
                actual: actual.value.type_tag.clone(),
                position: Some(actual.evaluation_position),
            })
        }
    } else {
        None
    }
}

fn ordinary_actual_mismatch<Type, Value, Compatibility>(
    parameter: &FormalParameter<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    positional_index: usize,
    compatibility: &Compatibility,
) -> (bool, usize, bool)
where
    Compatibility: TypeCompatibility<Type>,
{
    let named_index = named_actual_index(&call.named, &parameter.name);
    if positional_index < call.positional.len() {
        (
            compatibility_mismatch(
                compatibility,
                &parameter.expected_type,
                &call.positional[positional_index].value.type_tag,
            ),
            positional_index,
            false,
        )
    } else if named_index < call.named.len() {
        (
            compatibility_mismatch(
                compatibility,
                &parameter.expected_type,
                &call.named[named_index].value.type_tag,
            ),
            named_index,
            true,
        )
    } else {
        (false, 0, false)
    }
}

fn first_keyword_only_type_mismatch<Type, Value, Compatibility>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let mut keyword_index = 0;
    let mut mismatch = false;
    let mut actual_index = call.named.len();
    while keyword_index < signature.keyword_only.len() && !mismatch {
        let parameter_name = signature.keyword_only[keyword_index].name.clone();
        let expected_type = signature.keyword_only[keyword_index].expected_type.clone();
        let candidate_index = named_actual_index(&call.named, &parameter_name);
        if candidate_index < call.named.len() {
            mismatch = compatibility_mismatch(
                compatibility,
                &expected_type,
                &call.named[candidate_index].value.type_tag,
            );
            actual_index = candidate_index;
        }
        keyword_index += 1;
    }
    if mismatch {
        let parameter = &signature.keyword_only[keyword_index - 1];
        let actual = &call.named[actual_index];
        Some(BindingError::TypeMismatch {
            parameter: parameter.name.clone(),
            expected: parameter.expected_type.clone(),
            actual: actual.value.type_tag.clone(),
            position: Some(actual.evaluation_position),
        })
    } else {
        None
    }
}

// Keeping the two conditions separate makes the first-error precedence explicit in the extracted
// control flow: keyword variadics are inspected only after positional variadics succeed.
#[allow(clippy::collapsible_if)]
fn first_variadic_type_mismatch<Type, Value, Compatibility>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    positional_count: usize,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let mut error = None;
    if let Some(parameter) = &signature.var_args {
        error =
            first_extra_positional_type_mismatch(parameter, call, positional_count, compatibility);
    }
    if error.is_none() {
        if let Some(parameter) = &signature.keyword_args {
            error = first_extra_named_type_mismatch(parameter, signature, call, compatibility);
        }
    }
    error
}

fn first_extra_positional_type_mismatch<Type, Value, Compatibility>(
    parameter: &FormalParameter<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    positional_count: usize,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let mut index = positional_count;
    let mut mismatch = false;
    while index < call.positional.len() && !mismatch {
        mismatch = compatibility_mismatch(
            compatibility,
            &parameter.expected_type,
            &call.positional[index].value.type_tag,
        );
        index += 1;
    }
    if mismatch {
        let actual = &call.positional[index - 1];
        Some(BindingError::TypeMismatch {
            parameter: parameter.name.clone(),
            expected: parameter.expected_type.clone(),
            actual: actual.value.type_tag.clone(),
            position: Some(actual.evaluation_position),
        })
    } else {
        None
    }
}

fn first_extra_named_type_mismatch<Type, Value, Compatibility>(
    parameter: &FormalParameter<Type, Value>,
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    compatibility: &Compatibility,
) -> Option<BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    let mut index = 0;
    let mut mismatch = false;
    while index < call.named.len() && !mismatch {
        let actual_name = call.named[index].name.clone();
        if !ordinary_parameter_name(signature, &actual_name) {
            mismatch = compatibility_mismatch(
                compatibility,
                &parameter.expected_type,
                &call.named[index].value.type_tag,
            );
        }
        index += 1;
    }
    if mismatch {
        let actual = &call.named[index - 1];
        Some(BindingError::TypeMismatch {
            parameter: parameter.name.clone(),
            expected: parameter.expected_type.clone(),
            actual: actual.value.type_tag.clone(),
            position: Some(actual.evaluation_position),
        })
    } else {
        None
    }
}

fn string_list_contains(names: &[String], candidate: &String) -> bool {
    let mut index = 0;
    let mut found = false;
    while index < names.len() && !found {
        found = &names[index] == candidate;
        index += 1;
    }
    found
}

fn ordinary_parameter_name<Type, Value>(
    signature: &CallSignature<Type, Value>,
    candidate: &String,
) -> bool {
    let mut index = 0;
    let mut found = false;
    while index < signature.positional.len() && !found {
        found = &signature.positional[index].name == candidate;
        index += 1;
    }
    let mut index = 0;
    while index < signature.keyword_only.len() && !found {
        found = &signature.keyword_only[index].name == candidate;
        index += 1;
    }
    found
}

fn first_unexpected_keyword<Type, Value>(
    actuals: &[NamedActual<Type, Value>],
    signature: &CallSignature<Type, Value>,
) -> usize {
    let actual_count = actuals.len();
    let mut index = 0;
    let mut found = false;
    while index < actual_count && !found {
        let actual = &actuals[index];
        found = !ordinary_parameter_name(signature, &actual.name);
        index += 1;
    }
    if found { index - 1 } else { actual_count }
}

fn validate_signature<Type, Value, Compatibility, Allocator>(
    signature: &CallSignature<Type, Value>,
    compatibility: &Compatibility,
    allocator: &mut Allocator,
) -> Result<SignatureCounts, BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
    Allocator: BindingAllocator,
{
    let counts = signature_counts(signature)?;
    let mut names = allocate_buffer(
        allocator,
        AllocationSite::SignatureNames,
        counts.parameter_count,
    )?;
    let positional_only = &signature.positional_only;
    let mut index = 0;
    let mut validation_error = None;
    while index < positional_only.len() {
        if validation_error.is_none() {
            validation_error = validate_formal_parameter(
                &positional_only[index],
                false,
                &mut names,
                compatibility,
            )
            .err();
        }
        index += 1;
    }
    if let Some(error) = validation_error {
        return Err(error);
    }
    let positional = &signature.positional;
    let mut index = 0;
    let mut validation_error = None;
    while index < positional.len() {
        if validation_error.is_none() {
            validation_error =
                validate_formal_parameter(&positional[index], false, &mut names, compatibility)
                    .err();
        }
        index += 1;
    }
    if let Some(error) = validation_error {
        return Err(error);
    }
    let keyword_only = &signature.keyword_only;
    let mut index = 0;
    let mut validation_error = None;
    while index < keyword_only.len() {
        if validation_error.is_none() {
            validation_error =
                validate_formal_parameter(&keyword_only[index], false, &mut names, compatibility)
                    .err();
        }
        index += 1;
    }
    if let Some(error) = validation_error {
        return Err(error);
    }
    if let Some(parameter) = &signature.var_args {
        validate_formal_parameter(parameter, true, &mut names, compatibility)?;
    }
    if let Some(parameter) = &signature.keyword_args {
        validate_formal_parameter(parameter, true, &mut names, compatibility)?;
    }
    Ok(counts)
}

fn validate_formal_parameter<Type, Value, Compatibility>(
    parameter: &FormalParameter<Type, Value>,
    variadic: bool,
    names: &mut Vec<String>,
    compatibility: &Compatibility,
) -> Result<(), BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    if parameter.name.is_empty() {
        return Err(BindingError::MalformedSignature(
            MalformedSignature::EmptyParameterName,
        ));
    }
    if string_list_contains(names, &parameter.name) {
        return Err(BindingError::MalformedSignature(
            MalformedSignature::DuplicateParameter {
                name: parameter.name.clone(),
            },
        ));
    }
    names.push(parameter.name.clone());
    if variadic && parameter.default_value.is_some() {
        return Err(BindingError::MalformedSignature(
            MalformedSignature::VariadicDefault {
                name: parameter.name.clone(),
            },
        ));
    }
    if let Some(default) = &parameter.default_value
        && !compatibility.accepts(&parameter.expected_type, &default.type_tag)
    {
        return Err(BindingError::MalformedSignature(
            MalformedSignature::DefaultTypeMismatch {
                parameter: parameter.name.clone(),
                expected: parameter.expected_type.clone(),
                actual: default.type_tag.clone(),
            },
        ));
    }
    Ok(())
}

// Explicit branches keep the executable binder within Charon/Aeneas's supported control-flow
// fragment; replacing them with iterator combinators would hide the same finite choice in an
// external closure.
#[allow(clippy::manual_map)]
fn validate_call<Type, Value, Compatibility>(
    signature: &CallSignature<Type, Value>,
    call: &ExpandedCall<Type, Value>,
    positional_count: usize,
    compatibility: &Compatibility,
) -> Result<(), BindingError<Type>>
where
    Type: Clone,
    Compatibility: TypeCompatibility<Type>,
{
    if let Some(name) = first_duplicate_named_actual(&call.named) {
        return Err(BindingError::DuplicateNamedArgument { name });
    }

    if let Some(error) = first_duplicate_binding(signature, call) {
        return Err(error);
    }

    if call.positional.len() > positional_count && signature.var_args.is_none() {
        return Err(BindingError::TooManyPositionals {
            expected: positional_count,
            actual: call.positional.len(),
        });
    }

    let unexpected_keyword = first_unexpected_keyword(&call.named, signature);
    if signature.keyword_args.is_none() && unexpected_keyword < call.named.len() {
        return Err(BindingError::UnexpectedKeyword {
            name: call.named[unexpected_keyword].name.clone(),
        });
    }

    if let Some(error) = first_missing_required_argument(signature, call) {
        return Err(error);
    }

    if let Some(error) = first_positional_only_type_mismatch(signature, call, compatibility) {
        return Err(error);
    }
    if let Some(error) = first_ordinary_type_mismatch(signature, call, compatibility) {
        return Err(error);
    }
    if let Some(error) = first_keyword_only_type_mismatch(signature, call, compatibility) {
        return Err(error);
    }
    if let Some(error) =
        first_variadic_type_mismatch(signature, call, positional_count, compatibility)
    {
        return Err(error);
    }
    Ok(())
}

// See `validate_call`: these explicit finite choices are part of the extracted implementation.
#[allow(clippy::manual_map)]
fn canonical_environment<Type, Value, Allocator>(
    signature: &CallSignature<Type, Value>,
    call: ExpandedCall<Type, Value>,
    counts: SignatureCounts,
    allocator: &mut Allocator,
) -> Result<BindingEnvironment<Type, Value>, BindingError<Type>>
where
    Type: Clone,
    Value: Clone,
    Allocator: BindingAllocator,
{
    let mut cells = allocate_buffer(
        allocator,
        AllocationSite::BindingCells,
        counts.parameter_count,
    )?;

    let positional_only = &signature.positional_only;
    let mut index = 0;
    let mut construction_error = None;
    while index < positional_only.len() {
        let parameter = &positional_only[index];
        if construction_error.is_none() {
            let argument = if let Some(actual) = call.positional.get(index) {
                Some(BoundArgument::SuppliedPositional(actual.clone()))
            } else if let Some(default) = &parameter.default_value {
                Some(BoundArgument::Defaulted(default.clone()))
            } else {
                None
            };
            if let Some(argument) = argument {
                cells.push(BindingCell {
                    parameter: parameter.clone(),
                    kind: ParameterKind::PositionalOnly,
                    argument,
                });
            } else {
                construction_error = Some(BindingError::MissingRequiredArgument {
                    parameter: parameter.name.clone(),
                });
            }
        }
        index += 1;
    }
    if let Some(error) = construction_error {
        return Err(error);
    }
    let positional_offset = positional_only.len();
    let positional = &signature.positional;
    let mut parameter_index = 0;
    let mut construction_error = None;
    while parameter_index < positional.len() {
        let parameter = &positional[parameter_index];
        let index = positional_offset + parameter_index;
        if construction_error.is_none() {
            let argument = if let Some(actual) = call.positional.get(index) {
                Some(BoundArgument::SuppliedPositional(actual.clone()))
            } else if let Some(actual) = find_named_actual(&call.named, &parameter.name) {
                Some(BoundArgument::SuppliedNamed(actual.clone()))
            } else if let Some(default) = &parameter.default_value {
                Some(BoundArgument::Defaulted(default.clone()))
            } else {
                None
            };
            if let Some(argument) = argument {
                cells.push(BindingCell {
                    parameter: parameter.clone(),
                    kind: ParameterKind::Positional,
                    argument,
                });
            } else {
                construction_error = Some(BindingError::MissingRequiredArgument {
                    parameter: parameter.name.clone(),
                });
            }
        }
        parameter_index += 1;
    }
    if let Some(error) = construction_error {
        return Err(error);
    }
    let keyword_only = &signature.keyword_only;
    let mut keyword_index = 0;
    let mut construction_error = None;
    while keyword_index < keyword_only.len() {
        let parameter = &keyword_only[keyword_index];
        if construction_error.is_none() {
            let argument = if let Some(actual) = find_named_actual(&call.named, &parameter.name) {
                Some(BoundArgument::SuppliedNamed(actual.clone()))
            } else if let Some(default) = &parameter.default_value {
                Some(BoundArgument::Defaulted(default.clone()))
            } else {
                None
            };
            if let Some(argument) = argument {
                cells.push(BindingCell {
                    parameter: parameter.clone(),
                    kind: ParameterKind::KeywordOnly,
                    argument,
                });
            } else {
                construction_error = Some(BindingError::MissingRequiredArgument {
                    parameter: parameter.name.clone(),
                });
            }
        }
        keyword_index += 1;
    }
    if let Some(error) = construction_error {
        return Err(error);
    }
    if let Some(parameter) = &signature.var_args {
        let residual_start = counts.positional_count;
        let residual_count = if call.positional.len() > residual_start {
            call.positional.len() - residual_start
        } else {
            0
        };
        let mut residuals = allocate_buffer(
            allocator,
            AllocationSite::ResidualPositionals,
            residual_count,
        )?;
        let mut index = residual_start;
        while index < call.positional.len() {
            residuals.push(call.positional[index].clone());
            index += 1;
        }
        cells.push(BindingCell {
            parameter: parameter.clone(),
            kind: ParameterKind::VarArgs,
            argument: BoundArgument::ResidualPositionals(residuals),
        });
    }
    if let Some(parameter) = &signature.keyword_args {
        let mut residuals = allocate_buffer(
            allocator,
            AllocationSite::ResidualKeywords,
            call.named.len(),
        )?;
        let mut index = 0;
        while index < call.named.len() {
            let actual_name = call.named[index].name.clone();
            if !ordinary_parameter_name(signature, &actual_name) {
                residuals.push(call.named[index].clone());
            }
            index += 1;
        }
        cells.push(BindingCell {
            parameter: parameter.clone(),
            kind: ParameterKind::KeywordArgs,
            argument: BoundArgument::ResidualKeywords(residuals),
        });
    }

    Ok(BindingEnvironment {
        cells,
        evaluation_order: call.evaluation_order,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::{Cell, RefCell};

    type Value = TypedValue<&'static str, i64>;
    type AllocationTrace = Vec<(AllocationSite, usize)>;
    type TestBindingResult =
        Result<BindingEnvironment<&'static str, i64>, BindingError<&'static str>>;

    struct FailingAllocator {
        fail_at: AllocationSite,
        observed: Vec<(AllocationSite, usize)>,
    }

    impl BindingAllocator for FailingAllocator {
        fn allocate<T>(&mut self, site: AllocationSite, requested: usize) -> Result<Vec<T>, ()> {
            self.observed.push((site, requested));
            if site == self.fail_at {
                Err(())
            } else {
                SystemBindingAllocator.allocate(site, requested)
            }
        }
    }

    fn bind_call_failing_at(
        signature: &CallSignature<&'static str, i64>,
        items: &[ActualItem<&'static str, i64>],
        receiver: Option<Receiver<&'static str, i64>>,
        fail_at: AllocationSite,
    ) -> (TestBindingResult, AllocationTrace) {
        let mut allocator = FailingAllocator {
            fail_at,
            observed: Vec::new(),
        };
        let result = bind_call_with_allocator(signature, items, receiver, &mut allocator);
        (result, allocator.observed)
    }

    fn int(value: i64) -> Value {
        TypedValue::new("int", value)
    }

    fn boolean(value: bool) -> Value {
        TypedValue::new("bool", i64::from(value))
    }

    fn required(name: &str, expected: &'static str) -> FormalParameter<&'static str, i64> {
        FormalParameter::required(name, expected)
    }

    fn pre_seam_bind_call_with<Compatible>(
        signature: &CallSignature<&'static str, i64>,
        items: &[ActualItem<&'static str, i64>],
        receiver: Option<Receiver<&'static str, i64>>,
        compatible: Compatible,
    ) -> Result<BindingEnvironment<&'static str, i64>, BindingError<&'static str>>
    where
        Compatible: Fn(&&'static str, &&'static str) -> bool,
    {
        let compatibility = CallbackTypeCompatibility(compatible);
        let mut allocator = SystemBindingAllocator;
        let counts = validate_signature(signature, &compatibility, &mut allocator)?;
        let expanded = expand_actual_items_with_allocator(items, receiver, &mut allocator)?;
        validate_call(
            signature,
            &expanded,
            counts.positional_count,
            &compatibility,
        )?;
        canonical_environment(signature, expanded, counts, &mut allocator)
    }

    fn assert_exact_binding_equivalence(
        signature: &CallSignature<&'static str, i64>,
        items: &[ActualItem<&'static str, i64>],
        receiver: Option<Receiver<&'static str, i64>>,
        expected: Result<BindingEnvironment<&'static str, i64>, BindingError<&'static str>>,
    ) {
        let before =
            pre_seam_bind_call_with(signature, items, receiver.clone(), |expected, actual| {
                expected == actual
            });
        let after = bind_call(signature, items, receiver);
        assert_eq!(before, expected);
        assert_eq!(after, expected);
    }

    fn supplied_value(argument: &BoundArgument<&'static str, i64>) -> i64 {
        match argument {
            BoundArgument::SuppliedPositional(actual) => actual.value.value,
            BoundArgument::SuppliedNamed(actual) => actual.value.value,
            BoundArgument::Defaulted(value) => value.value,
            BoundArgument::ResidualPositionals(_) | BoundArgument::ResidualKeywords(_) => {
                panic!("expected one ordinary value")
            }
        }
    }

    #[test]
    fn canonical_binding_uses_names_defaults_and_formal_order() {
        let signature = CallSignature {
            positional: vec![
                required("first", "int"),
                FormalParameter::defaulted("second", "int", int(7)),
            ],
            keyword_only: vec![FormalParameter::defaulted("offset", "int", int(11))],
            ..CallSignature::default()
        };
        let environment = bind_call(
            &signature,
            &[
                ActualItem::Named {
                    name: "offset".to_owned(),
                    value: int(5),
                },
                ActualItem::Named {
                    name: "first".to_owned(),
                    value: int(2),
                },
            ],
            None,
        )
        .unwrap();

        assert_eq!(
            environment
                .cells
                .iter()
                .map(|cell| cell.parameter.name.as_str())
                .collect::<Vec<_>>(),
            ["first", "second", "offset"]
        );
        assert_eq!(supplied_value(&environment.cells[0].argument), 2);
        assert_eq!(supplied_value(&environment.cells[1].argument), 7);
        assert_eq!(supplied_value(&environment.cells[2].argument), 5);
    }

    #[test]
    fn fixed_stars_expand_in_place_and_are_evaluated_once() {
        let signature = CallSignature {
            positional: ["a", "b", "c", "d"]
                .map(|name| required(name, "int"))
                .to_vec(),
            ..CallSignature::default()
        };
        let environment = bind_call(
            &signature,
            &[
                ActualItem::FixedStar(vec![int(1), int(2)]),
                ActualItem::FixedStar(vec![int(3)]),
                ActualItem::Positional(int(4)),
            ],
            None,
        )
        .unwrap();

        assert_eq!(
            environment
                .cells
                .iter()
                .map(|cell| supplied_value(&cell.argument))
                .collect::<Vec<_>>(),
            [1, 2, 3, 4]
        );
        assert_eq!(
            environment.evaluation_order,
            [
                EvaluationEvent::FixedStar {
                    item_index: 0,
                    element_count: 2,
                },
                EvaluationEvent::FixedStar {
                    item_index: 1,
                    element_count: 1,
                },
                EvaluationEvent::Positional { item_index: 2 },
            ]
        );
    }

    #[test]
    fn varargs_and_kwargs_are_exact_residuals_in_source_order() {
        let signature = CallSignature {
            positional_only: Vec::new(),
            positional: vec![required("head", "int")],
            keyword_only: vec![required("flag", "bool")],
            var_args: Some(required("rest", "int")),
            keyword_args: Some(required("named", "int")),
        };
        let environment = bind_call(
            &signature,
            &[
                ActualItem::Positional(int(1)),
                ActualItem::FixedStar(vec![int(2), int(3)]),
                ActualItem::Named {
                    name: "right".to_owned(),
                    value: int(5),
                },
                ActualItem::Named {
                    name: "flag".to_owned(),
                    value: boolean(true),
                },
                ActualItem::Named {
                    name: "left".to_owned(),
                    value: int(4),
                },
            ],
            None,
        )
        .unwrap();

        let BoundArgument::ResidualPositionals(rest) = &environment.get("rest").unwrap().argument
        else {
            panic!("rest was not a varargs cell")
        };
        assert_eq!(
            rest.iter()
                .map(|actual| actual.value.value)
                .collect::<Vec<_>>(),
            [2, 3]
        );
        let BoundArgument::ResidualKeywords(named) = &environment.get("named").unwrap().argument
        else {
            panic!("named was not a kwargs cell")
        };
        assert_eq!(
            named
                .iter()
                .map(|actual| (actual.name.as_str(), actual.value.value))
                .collect::<Vec<_>>(),
            [("right", 5), ("left", 4)]
        );
    }

    #[test]
    fn receiver_is_injected_once_before_explicit_arguments() {
        let signature = CallSignature {
            positional: vec![required("self", "Scale"), required("value", "int")],
            ..CallSignature::default()
        };
        let environment = bind_call(
            &signature,
            &[ActualItem::Positional(int(9))],
            Some(Receiver::new(TypedValue::new("Scale", 41))),
        )
        .unwrap();

        assert_eq!(supplied_value(&environment.cells[0].argument), 41);
        assert_eq!(supplied_value(&environment.cells[1].argument), 9);
        assert_eq!(
            environment.evaluation_order,
            [
                EvaluationEvent::Receiver,
                EvaluationEvent::Positional { item_index: 0 }
            ]
        );
        let receiver_count = environment
            .cells
            .iter()
            .filter(|cell| {
                matches!(
                    cell.argument,
                    BoundArgument::SuppliedPositional(PositionalActual {
                        origin: PositionalOrigin::Receiver,
                        ..
                    })
                )
            })
            .count();
        assert_eq!(receiver_count, 1);
    }

    #[test]
    fn dynamic_expansions_fail_closed_at_their_source_position() {
        let signature = CallSignature {
            positional: vec![required("value", "int")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &signature,
                &[ActualItem::Positional(int(1)), ActualItem::DynamicStar],
                None,
            ),
            Err(BindingError::DynamicStarUnsupported { item_index: 1 })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[ActualItem::KeywordMapping, ActualItem::Positional(int(1))],
                None,
            ),
            Err(BindingError::KeywordMappingUnsupported { item_index: 0 })
        );
    }

    #[test]
    fn expansion_above_the_former_limit_is_supported() {
        const ARGUMENT_COUNT: usize = 4097;
        let values = vec![int(7); ARGUMENT_COUNT];
        let expanded = expand_actual_items(&[ActualItem::FixedStar(values)], None).unwrap();

        assert_eq!(expanded.positional.len(), ARGUMENT_COUNT);
        assert_eq!(expanded.named.len(), 0);
        assert_eq!(
            expanded.evaluation_order,
            [EvaluationEvent::FixedStar {
                item_index: 0,
                element_count: ARGUMENT_COUNT,
            }]
        );
    }

    #[test]
    fn errors_are_deterministic_and_precede_type_checking() {
        let signature = CallSignature {
            positional: vec![required("value", "int")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &signature,
                &[
                    ActualItem::Positional(TypedValue::new("str", 1)),
                    ActualItem::Named {
                        name: "value".to_owned(),
                        value: int(2),
                    },
                ],
                None,
            ),
            Err(BindingError::DuplicateBinding {
                parameter: "value".to_owned(),
            })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[ActualItem::Named {
                    name: "value".to_owned(),
                    value: TypedValue::new("str", 1),
                }],
                None,
            ),
            Err(BindingError::TypeMismatch {
                parameter: "value".to_owned(),
                expected: "int",
                actual: "str",
                position: Some(EvaluationPosition::Actual {
                    item_index: 0,
                    expansion_index: 0,
                }),
            })
        );

        let method = CallSignature {
            positional: vec![required("self", "Scale")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &method,
                &[ActualItem::Named {
                    name: "self".to_owned(),
                    value: TypedValue::new("Scale", 2),
                }],
                Some(Receiver::new(TypedValue::new("Scale", 1))),
            ),
            Err(BindingError::DuplicateBinding {
                parameter: "self".to_owned(),
            })
        );
    }

    #[test]
    fn missing_unexpected_duplicate_and_excess_arguments_have_exact_errors() {
        let signature = CallSignature {
            positional: vec![required("value", "int")],
            keyword_only: vec![required("flag", "bool")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &signature,
                &[ActualItem::Named {
                    name: "value".to_owned(),
                    value: int(1),
                }],
                None,
            ),
            Err(BindingError::MissingRequiredArgument {
                parameter: "flag".to_owned(),
            })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[
                    ActualItem::Named {
                        name: "extra".to_owned(),
                        value: int(1),
                    },
                    ActualItem::Named {
                        name: "extra".to_owned(),
                        value: int(2),
                    },
                ],
                None,
            ),
            Err(BindingError::DuplicateNamedArgument {
                name: "extra".to_owned(),
            })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[
                    ActualItem::Named {
                        name: "value".to_owned(),
                        value: int(1),
                    },
                    ActualItem::Named {
                        name: "flag".to_owned(),
                        value: boolean(true),
                    },
                    ActualItem::Named {
                        name: "extra".to_owned(),
                        value: int(2),
                    },
                ],
                None,
            ),
            Err(BindingError::UnexpectedKeyword {
                name: "extra".to_owned(),
            })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[
                    ActualItem::Positional(int(1)),
                    ActualItem::Positional(int(2)),
                ],
                None,
            ),
            Err(BindingError::TooManyPositionals {
                expected: 1,
                actual: 2,
            })
        );
    }

    #[test]
    fn malformed_signatures_fail_before_argument_expansion() {
        let signature = CallSignature {
            positional: vec![required("same", "int")],
            keyword_only: vec![required("same", "int")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(&signature, &[ActualItem::DynamicStar], None),
            Err(BindingError::MalformedSignature(
                MalformedSignature::DuplicateParameter {
                    name: "same".to_owned(),
                }
            ))
        );

        let bad_default = CallSignature {
            positional: vec![FormalParameter::defaulted(
                "value",
                "int",
                TypedValue::new("str", 7),
            )],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(&bad_default, &[], None),
            Err(BindingError::MalformedSignature(
                MalformedSignature::DefaultTypeMismatch {
                    parameter: "value".to_owned(),
                    expected: "int",
                    actual: "str",
                }
            ))
        );
    }

    #[test]
    fn formal_parameter_count_above_the_former_limit_is_supported() {
        const PARAMETER_COUNT: usize = 4097;
        let signature = CallSignature {
            positional: (0..PARAMETER_COUNT)
                .map(|index| {
                    FormalParameter::defaulted(format!("parameter-{index}"), "int", int(0))
                })
                .collect(),
            ..CallSignature::default()
        };

        let environment = bind_call(&signature, &[], None).unwrap();
        assert_eq!(environment.cells.len(), PARAMETER_COUNT);
        assert_eq!(
            environment.cells.first().unwrap().parameter.name,
            "parameter-0"
        );
        assert_eq!(
            environment.cells.last().unwrap().parameter.name,
            format!("parameter-{}", PARAMETER_COUNT - 1)
        );
    }

    #[test]
    fn every_buffer_allocation_failure_is_typed_and_stops_at_its_site() {
        let ordinary = CallSignature {
            positional: vec![required("value", "int")],
            ..CallSignature::default()
        };
        let ordinary_items = [ActualItem::Positional(int(1))];
        let cases = [
            (
                AllocationSite::SignatureNames,
                &ordinary,
                ordinary_items.as_slice(),
                1,
            ),
            (
                AllocationSite::ExpandedPositionals,
                &ordinary,
                ordinary_items.as_slice(),
                1,
            ),
            (
                AllocationSite::ExpandedNamed,
                &ordinary,
                ordinary_items.as_slice(),
                1,
            ),
            (
                AllocationSite::EvaluationOrder,
                &ordinary,
                ordinary_items.as_slice(),
                1,
            ),
            (
                AllocationSite::BindingCells,
                &ordinary,
                ordinary_items.as_slice(),
                1,
            ),
        ];
        for (site, signature, items, requested) in cases {
            let (result, observed) = bind_call_failing_at(signature, items, None, site);
            assert_eq!(
                result,
                Err(BindingError::AllocationFailed { site, requested })
            );
            assert_eq!(observed.last(), Some(&(site, requested)));
            assert_eq!(observed.iter().filter(|(seen, _)| *seen == site).count(), 1);
        }

        let varargs = CallSignature {
            var_args: Some(required("rest", "int")),
            ..CallSignature::default()
        };
        let (result, observed) = bind_call_failing_at(
            &varargs,
            &ordinary_items,
            None,
            AllocationSite::ResidualPositionals,
        );
        assert_eq!(
            result,
            Err(BindingError::AllocationFailed {
                site: AllocationSite::ResidualPositionals,
                requested: 1,
            })
        );
        assert_eq!(
            observed.last(),
            Some(&(AllocationSite::ResidualPositionals, 1))
        );

        let kwargs = CallSignature {
            keyword_args: Some(required("named", "int")),
            ..CallSignature::default()
        };
        let named_items = [ActualItem::Named {
            name: "extra".to_owned(),
            value: int(1),
        }];
        let (result, observed) = bind_call_failing_at(
            &kwargs,
            &named_items,
            None,
            AllocationSite::ResidualKeywords,
        );
        assert_eq!(
            result,
            Err(BindingError::AllocationFailed {
                site: AllocationSite::ResidualKeywords,
                requested: 1,
            })
        );
        assert_eq!(
            observed.last(),
            Some(&(AllocationSite::ResidualKeywords, 1))
        );
    }

    #[test]
    fn compatibility_relation_can_accept_frontend_subtypes() {
        let signature = CallSignature {
            positional: vec![required("value", "number")],
            ..CallSignature::default()
        };
        let environment = bind_call_with(
            &signature,
            &[ActualItem::Positional(TypedValue::new("int", 4))],
            None,
            |expected, actual| *expected == "number" && *actual == "int",
        )
        .unwrap();
        assert_eq!(supplied_value(&environment.cells[0].argument), 4);
    }

    #[test]
    fn every_vararg_and_kwarg_value_is_type_checked_at_its_source_position() {
        let signature = CallSignature {
            var_args: Some(required("rest", "int")),
            keyword_args: Some(required("named", "int")),
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &signature,
                &[
                    ActualItem::FixedStar(vec![int(1), TypedValue::new("str", 2)]),
                    ActualItem::Named {
                        name: "wrong".to_owned(),
                        value: TypedValue::new("str", 3),
                    },
                ],
                None,
            ),
            Err(BindingError::TypeMismatch {
                parameter: "rest".to_owned(),
                expected: "int",
                actual: "str",
                position: Some(EvaluationPosition::Actual {
                    item_index: 0,
                    expansion_index: 1,
                }),
            })
        );
        assert_eq!(
            bind_call(
                &signature,
                &[ActualItem::Named {
                    name: "wrong".to_owned(),
                    value: TypedValue::new("str", 3),
                }],
                None,
            ),
            Err(BindingError::TypeMismatch {
                parameter: "named".to_owned(),
                expected: "int",
                actual: "str",
                position: Some(EvaluationPosition::Actual {
                    item_index: 0,
                    expansion_index: 0,
                }),
            })
        );
    }

    #[test]
    fn positional_only_names_do_not_bind_keywords_but_can_enter_kwargs() {
        let without_kwargs = CallSignature {
            positional_only: vec![required("value", "int")],
            ..CallSignature::default()
        };
        assert_eq!(
            bind_call(
                &without_kwargs,
                &[
                    ActualItem::Positional(int(1)),
                    ActualItem::Named {
                        name: "value".to_owned(),
                        value: int(2),
                    },
                ],
                None,
            ),
            Err(BindingError::UnexpectedKeyword {
                name: "value".to_owned(),
            })
        );

        let with_kwargs = CallSignature {
            positional_only: vec![required("value", "int")],
            keyword_args: Some(required("named", "int")),
            ..CallSignature::default()
        };
        let environment = bind_call(
            &with_kwargs,
            &[
                ActualItem::Positional(int(1)),
                ActualItem::Named {
                    name: "value".to_owned(),
                    value: int(2),
                },
            ],
            None,
        )
        .unwrap();
        assert_eq!(
            supplied_value(&environment.get("value").unwrap().argument),
            1
        );
        let BoundArgument::ResidualKeywords(named) = &environment.get("named").unwrap().argument
        else {
            panic!("named was not a kwargs cell")
        };
        assert_eq!(named.len(), 1);
        assert_eq!(named[0].name, "value");
        assert_eq!(named[0].value.value, 2);
    }

    #[test]
    fn extracted_binding_seam_preserves_every_error_variant_and_precedence() {
        assert_exact_binding_equivalence(
            &CallSignature {
                positional: vec![required("", "int")],
                ..CallSignature::default()
            },
            &[ActualItem::DynamicStar],
            None,
            Err(BindingError::MalformedSignature(
                MalformedSignature::EmptyParameterName,
            )),
        );
        assert_exact_binding_equivalence(
            &CallSignature {
                positional: vec![required("same", "int")],
                keyword_only: vec![required("same", "int")],
                ..CallSignature::default()
            },
            &[],
            None,
            Err(BindingError::MalformedSignature(
                MalformedSignature::DuplicateParameter {
                    name: "same".to_owned(),
                },
            )),
        );
        assert_exact_binding_equivalence(
            &CallSignature {
                var_args: Some(FormalParameter::defaulted("rest", "int", int(0))),
                ..CallSignature::default()
            },
            &[],
            None,
            Err(BindingError::MalformedSignature(
                MalformedSignature::VariadicDefault {
                    name: "rest".to_owned(),
                },
            )),
        );
        assert_exact_binding_equivalence(
            &CallSignature {
                positional: vec![FormalParameter::defaulted(
                    "value",
                    "int",
                    TypedValue::new("str", 0),
                )],
                ..CallSignature::default()
            },
            &[],
            None,
            Err(BindingError::MalformedSignature(
                MalformedSignature::DefaultTypeMismatch {
                    parameter: "value".to_owned(),
                    expected: "int",
                    actual: "str",
                },
            )),
        );

        let ordinary = CallSignature {
            positional: vec![required("value", "int")],
            ..CallSignature::default()
        };
        assert_exact_binding_equivalence(
            &ordinary,
            &[ActualItem::DynamicStar],
            None,
            Err(BindingError::DynamicStarUnsupported { item_index: 0 }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[ActualItem::KeywordMapping],
            None,
            Err(BindingError::KeywordMappingUnsupported { item_index: 0 }),
        );

        assert_exact_binding_equivalence(
            &ordinary,
            &[
                ActualItem::Named {
                    name: "value".to_owned(),
                    value: int(1),
                },
                ActualItem::Named {
                    name: "value".to_owned(),
                    value: int(2),
                },
            ],
            None,
            Err(BindingError::DuplicateNamedArgument {
                name: "value".to_owned(),
            }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[
                ActualItem::Positional(int(1)),
                ActualItem::Named {
                    name: "value".to_owned(),
                    value: int(2),
                },
            ],
            None,
            Err(BindingError::DuplicateBinding {
                parameter: "value".to_owned(),
            }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[
                ActualItem::Positional(int(1)),
                ActualItem::Positional(int(2)),
            ],
            None,
            Err(BindingError::TooManyPositionals {
                expected: 1,
                actual: 2,
            }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[ActualItem::Named {
                name: "other".to_owned(),
                value: int(1),
            }],
            None,
            Err(BindingError::UnexpectedKeyword {
                name: "other".to_owned(),
            }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[],
            None,
            Err(BindingError::MissingRequiredArgument {
                parameter: "value".to_owned(),
            }),
        );
        assert_exact_binding_equivalence(
            &ordinary,
            &[ActualItem::Positional(TypedValue::new("str", 1))],
            None,
            Err(BindingError::TypeMismatch {
                parameter: "value".to_owned(),
                expected: "int",
                actual: "str",
                position: Some(EvaluationPosition::Actual {
                    item_index: 0,
                    expansion_index: 0,
                }),
            }),
        );
    }

    #[test]
    fn extracted_binding_seam_preserves_stateful_compatibility_outcomes_and_order() {
        let signature = CallSignature {
            positional: vec![FormalParameter::defaulted("value", "number", int(7))],
            keyword_only: vec![FormalParameter::defaulted("flag", "truthy", boolean(false))],
            ..CallSignature::default()
        };
        let items = [
            ActualItem::Positional(TypedValue::new("int", 4)),
            ActualItem::Named {
                name: "flag".to_owned(),
                value: boolean(true),
            },
        ];

        for outcomes in [
            [false, false, false, false],
            [true, false, true, false],
            [true, true, false, true],
            [true, true, true, true],
        ] {
            let before_index = Cell::new(0usize);
            let before_trace = RefCell::new(Vec::new());
            let before = pre_seam_bind_call_with(&signature, &items, None, |expected, actual| {
                before_trace.borrow_mut().push((*expected, *actual));
                let index = before_index.get();
                before_index.set(index + 1);
                outcomes[index]
            });

            let after_index = Cell::new(0usize);
            let after_trace = RefCell::new(Vec::new());
            let after = bind_call_with(&signature, &items, None, |expected, actual| {
                after_trace.borrow_mut().push((*expected, *actual));
                let index = after_index.get();
                after_index.set(index + 1);
                outcomes[index]
            });

            assert_eq!(after, before);
            assert_eq!(*after_trace.borrow(), *before_trace.borrow());
            assert_eq!(after_index.get(), before_index.get());
        }
    }
}
