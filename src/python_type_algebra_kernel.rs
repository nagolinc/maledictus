//! Pure decisions for the production Python type-algebra frontend.
//!
//! This module deliberately has no parser, solver, heap, or diagnostic dependencies.  The
//! frontend constructs a checked nominal hierarchy, then delegates normalization, expansion,
//! assignability, casts, and path narrowing to these total kernels.

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Type {
    Int,
    Bool,
    Str,
    None,
    Object,
    Class(String),
    List(Box<Type>),
    Set(Box<Type>),
    Dict(Box<Type>, Box<Type>),
    FixedTuple(TypeList),
    VariadicTuple(Box<Type>),
    Union(TypeList),
}

/// Strictly-positive source-owned sequence for recursive type arms.
///
/// Keeping recursive `Type` occurrences behind this algebraic list makes the production type
/// algebra directly representable by proof assistants. `Vec` remains an ingress/egress convenience
/// at parser boundaries; it is not part of the recursive semantic domain.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) enum TypeList {
    #[default]
    Empty,
    Item(Box<Type>, Box<TypeList>),
}

impl TypeList {
    pub(crate) fn from_vec(mut types: Vec<Type>) -> Self {
        let mut result = Self::Empty;
        while let Some(ty) = types.pop() {
            result = Self::Item(Box::new(ty), Box::new(result));
        }
        result
    }

    fn into_vec(self) -> Vec<Type> {
        let mut result = Vec::new();
        let mut current = self;
        loop {
            match current {
                Self::Empty => return result,
                Self::Item(ty, tail) => {
                    result.push(*ty);
                    current = *tail;
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct NominalClass {
    pub(crate) name: String,
    pub(crate) parent: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct NominalHierarchy {
    classes: NominalClassList,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
enum NominalClassList {
    #[default]
    Empty,
    Item(Box<NominalClass>, Box<NominalClassList>),
}

impl NominalClassList {
    fn from_vec(mut classes: Vec<NominalClass>) -> Self {
        let mut result = Self::Empty;
        while let Some(class) = classes.pop() {
            result = Self::Item(Box::new(class), Box::new(result));
        }
        result
    }

    fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Item(_, tail) => 1 + tail.len(),
        }
    }
}

pub(crate) fn build_nominal_hierarchy(classes: Vec<NominalClass>) -> Option<NominalHierarchy> {
    if validate_nominal_hierarchy(&classes) {
        Some(NominalHierarchy {
            classes: NominalClassList::from_vec(classes),
        })
    } else {
        None
    }
}

/// Validates the exact nominal edges supplied by the source catalog.
///
/// `object` is the one implicit Python root which does not need its own catalog entry.  Every
/// other parent must resolve, names must be unique, and following parents must terminate.
pub(crate) fn validate_nominal_hierarchy(classes: &[NominalClass]) -> bool {
    let object_name = String::from("object");
    let mut valid = true;
    let mut index = 0_usize;
    while index < classes.len() {
        if valid {
            let name = classes[index].name.clone();
            let mut duplicate = false;
            let mut prior_index = 0_usize;
            while prior_index < index {
                if !duplicate {
                    duplicate = classes[prior_index].name == name;
                }
                prior_index += 1;
            }

            let parent = classes[index].parent.clone();
            let mut parent_resolves = parent.is_none();
            if let Some(parent_name) = parent {
                parent_resolves = parent_name == object_name;
                if !parent_resolves {
                    let mut candidate_index = 0_usize;
                    while candidate_index < classes.len() {
                        if !parent_resolves {
                            parent_resolves = classes[candidate_index].name == parent_name;
                        }
                        candidate_index += 1;
                    }
                }
            }
            let name_is_root = name == object_name;
            valid = (!name_is_root) & (!duplicate) & parent_resolves;
        }
        index += 1;
    }

    if valid {
        let mut class_index = 0_usize;
        while class_index < classes.len() {
            if valid {
                let mut current_index = Some(class_index);
                let mut steps = 0_usize;
                while let (true, Some(current)) = (valid, current_index) {
                    if steps > classes.len() {
                        valid = false;
                    } else {
                        steps += 1;
                        let parent = classes[current].parent.clone();
                        match parent {
                            Some(parent_name) if parent_name != object_name => {
                                let mut next_index = 0_usize;
                                let mut candidate_index = 0_usize;
                                while candidate_index < classes.len() {
                                    let matches_parent =
                                        classes[candidate_index].name == parent_name;
                                    let select_candidate = matches_parent as usize;
                                    next_index = select_candidate * candidate_index
                                        + (1_usize - select_candidate) * next_index;
                                    candidate_index += 1;
                                }
                                current_index = Some(next_index);
                            }
                            _ => current_index = None,
                        }
                    }
                }
            }
            class_index += 1;
        }
    }
    valid
}

/// Flattens nested unions and removes later duplicates while preserving first-seen order.
pub(crate) fn normalize_union(types: Vec<Type>) -> Type {
    normalize_type_list(TypeList::from_vec(types))
}

fn normalize_type_list(types: TypeList) -> Type {
    let reversed = flatten_union_types(types, TypeList::Empty);
    let flattened = reverse_type_list(reversed, TypeList::Empty);
    match flattened {
        TypeList::Item(only, tail) if matches!(*tail, TypeList::Empty) => *only,
        other => Type::Union(other),
    }
}

fn flatten_union_types(types: TypeList, flattened: TypeList) -> TypeList {
    match types {
        TypeList::Empty => flattened,
        TypeList::Item(ty, tail) => {
            let next = match *ty {
                Type::Union(nested) => flatten_union_types(nested, flattened),
                other => {
                    if type_list_contains(&flattened, &other) {
                        flattened
                    } else {
                        TypeList::Item(Box::new(other), Box::new(flattened))
                    }
                }
            };
            flatten_union_types(*tail, next)
        }
    }
}

fn reverse_type_list(types: TypeList, reversed: TypeList) -> TypeList {
    match types {
        TypeList::Empty => reversed,
        TypeList::Item(ty, tail) => {
            reverse_type_list(*tail, TypeList::Item(ty, Box::new(reversed)))
        }
    }
}

fn type_list_contains(types: &TypeList, expected: &Type) -> bool {
    match types {
        TypeList::Empty => false,
        TypeList::Item(ty, tail) => type_equals(ty, expected) || type_list_contains(tail, expected),
    }
}

/// Structural equality for the source type algebra.
///
/// The decision kernels call this function directly rather than relying on a compiler-generated
/// trait implementation.  Besides making the relation explicit, this keeps the source-bound
/// extraction independent of verifier support for recursive derived trait bodies.
fn type_equals(left: &Type, right: &Type) -> bool {
    match (left, right) {
        (Type::Int, Type::Int)
        | (Type::Bool, Type::Bool)
        | (Type::Str, Type::Str)
        | (Type::None, Type::None)
        | (Type::Object, Type::Object) => true,
        (Type::Class(left), Type::Class(right)) => left == right,
        (Type::List(left), Type::List(right))
        | (Type::Set(left), Type::Set(right))
        | (Type::VariadicTuple(left), Type::VariadicTuple(right)) => type_equals(left, right),
        (Type::Dict(left_key, left_value), Type::Dict(right_key, right_value)) => {
            type_equals(left_key, right_key) && type_equals(left_value, right_value)
        }
        (Type::FixedTuple(left), Type::FixedTuple(right))
        | (Type::Union(left), Type::Union(right)) => type_lists_equal(left, right),
        _ => false,
    }
}

fn type_lists_equal(left: &TypeList, right: &TypeList) -> bool {
    match (left, right) {
        (TypeList::Empty, TypeList::Empty) => true,
        (TypeList::Item(left, left_tail), TypeList::Item(right, right_tail)) => {
            type_equals(left, right) && type_lists_equal(left_tail, right_tail)
        }
        _ => false,
    }
}

/// Explicit recursive copy used by the extracted kernels.
///
/// Keeping this as a production helper avoids depending on translation of the compiler-generated
/// `Clone` implementation for a recursive enum. The ordinary Rust trait implementation remains
/// available to parser and test code outside the proof kernel.
fn clone_type(ty: &Type) -> Type {
    match ty {
        Type::Int => Type::Int,
        Type::Bool => Type::Bool,
        Type::Str => Type::Str,
        Type::None => Type::None,
        Type::Object => Type::Object,
        Type::Class(name) => Type::Class(name.clone()),
        Type::List(element) => Type::List(Box::new(clone_type(element))),
        Type::Set(element) => Type::Set(Box::new(clone_type(element))),
        Type::Dict(key, value) => {
            Type::Dict(Box::new(clone_type(key)), Box::new(clone_type(value)))
        }
        Type::FixedTuple(elements) => Type::FixedTuple(clone_type_list(elements)),
        Type::VariadicTuple(element) => Type::VariadicTuple(Box::new(clone_type(element))),
        Type::Union(elements) => Type::Union(clone_type_list(elements)),
    }
}

fn clone_type_list(types: &TypeList) -> TypeList {
    match types {
        TypeList::Empty => TypeList::Empty,
        TypeList::Item(ty, tail) => {
            TypeList::Item(Box::new(clone_type(ty)), Box::new(clone_type_list(tail)))
        }
    }
}

/// Returns the normalized top-level runtime alternatives of a type.
pub(crate) fn expand_union(ty: &Type) -> Vec<Type> {
    expand_union_list(ty).into_vec()
}

fn expand_union_list(ty: &Type) -> TypeList {
    match normalize_type_list(TypeList::Item(
        Box::new(clone_type(ty)),
        Box::new(TypeList::Empty),
    )) {
        Type::Union(types) => types,
        other => TypeList::Item(Box::new(other), Box::new(TypeList::Empty)),
    }
}

pub(crate) fn is_subclass(actual: &str, expected: &str, hierarchy: &NominalHierarchy) -> bool {
    let classes = &hierarchy.classes;
    if class_parent(actual, classes).is_none()
        || (expected != "object" && class_parent(expected, classes).is_none())
    {
        return false;
    }
    if actual == expected || expected == "object" {
        return true;
    }
    subclass_with_remaining(actual, expected, classes, classes.len())
}

fn subclass_with_remaining(
    actual: &str,
    expected: &str,
    classes: &NominalClassList,
    remaining: usize,
) -> bool {
    if remaining == 0 {
        return false;
    }
    match class_parent(actual, classes) {
        Some(Some(parent)) => {
            parent == expected || subclass_with_remaining(parent, expected, classes, remaining - 1)
        }
        Some(None) | None => false,
    }
}

fn class_parent<'a>(name: &str, classes: &'a NominalClassList) -> Option<Option<&'a str>> {
    match classes {
        NominalClassList::Empty => None,
        NominalClassList::Item(class, tail) => {
            if class.name == name {
                Some(class.parent.as_deref())
            } else {
                class_parent(name, tail)
            }
        }
    }
}

pub(crate) fn is_assignable(actual: &Type, expected: &Type, hierarchy: &NominalHierarchy) -> bool {
    if !type_is_well_formed(actual, hierarchy) || !type_is_well_formed(expected, hierarchy) {
        return false;
    }
    is_assignable_in_valid_hierarchy(actual, expected, hierarchy)
}

fn type_is_well_formed(ty: &Type, hierarchy: &NominalHierarchy) -> bool {
    match ty {
        Type::Class(name) => class_parent(name, &hierarchy.classes).is_some(),
        Type::List(element) | Type::Set(element) | Type::VariadicTuple(element) => {
            type_is_well_formed(element, hierarchy)
        }
        Type::Dict(key, value) => {
            type_is_well_formed(key, hierarchy) && type_is_well_formed(value, hierarchy)
        }
        Type::FixedTuple(elements) | Type::Union(elements) => {
            !matches!(elements, TypeList::Empty) && type_list_is_well_formed(elements, hierarchy)
        }
        Type::Int | Type::Bool | Type::Str | Type::None | Type::Object => true,
    }
}

fn type_list_is_well_formed(types: &TypeList, hierarchy: &NominalHierarchy) -> bool {
    match types {
        TypeList::Empty => true,
        TypeList::Item(ty, tail) => {
            type_is_well_formed(ty, hierarchy) && type_list_is_well_formed(tail, hierarchy)
        }
    }
}

fn is_assignable_in_valid_hierarchy(
    actual: &Type,
    expected: &Type,
    hierarchy: &NominalHierarchy,
) -> bool {
    if type_equals(actual, expected) || matches!(expected, Type::Object) {
        return true;
    }
    match (actual, expected) {
        (Type::Bool, Type::Int) => true,
        (Type::Class(actual), Type::Class(expected)) => is_subclass(actual, expected, hierarchy),
        (Type::Union(actual), expected) => every_type_assignable_to(actual, expected, hierarchy),
        (actual, Type::Union(expected)) => type_assignable_to_any(actual, expected, hierarchy),
        (Type::FixedTuple(actual), Type::FixedTuple(expected)) => {
            type_lists_assignable(actual, expected, hierarchy)
        }
        (Type::FixedTuple(actual), Type::VariadicTuple(expected)) => {
            every_type_assignable_to(actual, expected, hierarchy)
        }
        (Type::VariadicTuple(actual), Type::VariadicTuple(expected)) => {
            is_assignable_in_valid_hierarchy(actual, expected, hierarchy)
        }
        // Mutable Python containers are invariant. Exact equality was accepted above; element
        // subtyping must not widen a writable collection.
        (Type::List(_), Type::List(_))
        | (Type::Set(_), Type::Set(_))
        | (Type::Dict(_, _), Type::Dict(_, _)) => false,
        _ => false,
    }
}

fn every_type_assignable_to(
    actual: &TypeList,
    expected: &Type,
    hierarchy: &NominalHierarchy,
) -> bool {
    match actual {
        TypeList::Empty => true,
        TypeList::Item(actual, tail) => {
            is_assignable_in_valid_hierarchy(actual, expected, hierarchy)
                && every_type_assignable_to(tail, expected, hierarchy)
        }
    }
}

fn type_assignable_to_any(
    actual: &Type,
    expected: &TypeList,
    hierarchy: &NominalHierarchy,
) -> bool {
    match expected {
        TypeList::Empty => false,
        TypeList::Item(expected, tail) => {
            is_assignable_in_valid_hierarchy(actual, expected, hierarchy)
                || type_assignable_to_any(actual, tail, hierarchy)
        }
    }
}

fn type_lists_assignable(
    actual: &TypeList,
    expected: &TypeList,
    hierarchy: &NominalHierarchy,
) -> bool {
    match (actual, expected) {
        (TypeList::Empty, TypeList::Empty) => true,
        (TypeList::Item(actual, actual_tail), TypeList::Item(expected, expected_tail)) => {
            is_assignable_in_valid_hierarchy(actual, expected, hierarchy)
                && type_lists_assignable(actual_tail, expected_tail, hierarchy)
        }
        _ => false,
    }
}

/// Checks whether a cast can succeed for the modeled runtime type.
pub(crate) fn cast_compatible(
    actual: &Type,
    expected: &Type,
    hierarchy: &NominalHierarchy,
) -> bool {
    if !type_is_well_formed(actual, hierarchy) || !type_is_well_formed(expected, hierarchy) {
        return false;
    }
    match expected {
        Type::VariadicTuple(element) if type_equals(element, &Type::Object) => {
            matches!(actual, Type::FixedTuple(_) | Type::VariadicTuple(_))
        }
        _ => is_assignable(actual, expected, hierarchy),
    }
}

/// Computes a source type for one `isinstance` path, or `None` when the path is impossible.
pub(crate) fn narrow_type(
    actual: &Type,
    expected: &Type,
    positive: bool,
    hierarchy: &NominalHierarchy,
) -> Option<Type> {
    if !type_is_well_formed(actual, hierarchy) || !type_is_well_formed(expected, hierarchy) {
        return None;
    }
    let variants = expand_union_list(actual);
    let retained = narrow_variants(&variants, expected, positive, hierarchy);
    match retained {
        TypeList::Empty => None,
        other => Some(normalize_type_list(other)),
    }
}

fn narrow_variants(
    variants: &TypeList,
    expected: &Type,
    positive: bool,
    hierarchy: &NominalHierarchy,
) -> TypeList {
    match variants {
        TypeList::Empty => TypeList::Empty,
        TypeList::Item(variant, tail) => {
            let retained_tail = narrow_variants(tail, expected, positive, hierarchy);
            let inside = is_assignable(variant, expected, hierarchy);
            let contains_expected = is_assignable(expected, variant, hierarchy);
            if positive && inside {
                TypeList::Item(Box::new(clone_type(variant)), Box::new(retained_tail))
            } else if positive && contains_expected {
                TypeList::Item(Box::new(clone_type(expected)), Box::new(retained_tail))
            } else if !positive && !inside {
                TypeList::Item(Box::new(clone_type(variant)), Box::new(retained_tail))
            } else {
                retained_tail
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn types(items: Vec<Type>) -> TypeList {
        TypeList::from_vec(items)
    }

    fn type_items(types: &TypeList) -> Vec<&Type> {
        let mut items = Vec::new();
        let mut current = types;
        while let TypeList::Item(item, tail) = current {
            items.push(item.as_ref());
            current = tail;
        }
        items
    }

    fn nominal_classes() -> Vec<NominalClass> {
        vec![
            NominalClass {
                name: "Base".to_owned(),
                parent: None,
            },
            NominalClass {
                name: "Child".to_owned(),
                parent: Some("Base".to_owned()),
            },
            NominalClass {
                name: "Grandchild".to_owned(),
                parent: Some("Child".to_owned()),
            },
            NominalClass {
                name: "Other".to_owned(),
                parent: None,
            },
        ]
    }

    fn hierarchy() -> NominalHierarchy {
        build_nominal_hierarchy(nominal_classes()).unwrap()
    }

    fn validate_nominal_hierarchy_reference(classes: &[NominalClass]) -> bool {
        for (index, class) in classes.iter().enumerate() {
            if class.name == "object" {
                return false;
            }
            if classes[..index]
                .iter()
                .any(|candidate| candidate.name == class.name)
            {
                return false;
            }
            if let Some(parent) = &class.parent
                && parent != "object"
                && !classes.iter().any(|candidate| candidate.name == *parent)
            {
                return false;
            }
        }
        for class in classes {
            let mut current = Some(class.name.as_str());
            let mut steps = 0_usize;
            while let Some(name) = current {
                if steps > classes.len() {
                    return false;
                }
                steps += 1;
                current = classes
                    .iter()
                    .find(|candidate| candidate.name == name)
                    .and_then(|candidate| candidate.parent.as_deref())
                    .filter(|parent| *parent != "object");
            }
        }
        true
    }

    fn assert_validation_equivalent_for_catalogs(
        variants: &[NominalClass],
        catalog: &mut Vec<NominalClass>,
        remaining: usize,
    ) {
        assert_eq!(
            validate_nominal_hierarchy(catalog),
            validate_nominal_hierarchy_reference(catalog),
            "catalog: {catalog:#?}"
        );
        if remaining > 0 {
            for class in variants {
                catalog.push(class.clone());
                assert_validation_equivalent_for_catalogs(variants, catalog, remaining - 1);
                catalog.pop();
            }
        }
    }

    #[test]
    fn hierarchy_validation_refactor_matches_the_original_behavior() {
        let mut variants = Vec::new();
        for name in ["", "object", "A", "B"] {
            for parent in [None, Some("object"), Some("A"), Some("B"), Some("Missing")] {
                variants.push(NominalClass {
                    name: name.to_owned(),
                    parent: parent.map(str::to_owned),
                });
            }
        }
        assert_validation_equivalent_for_catalogs(&variants, &mut Vec::new(), 3);
    }

    #[test]
    fn hierarchy_validation_rejects_duplicate_unresolved_and_cyclic_edges() {
        assert!(validate_nominal_hierarchy(&nominal_classes()));
        assert!(!validate_nominal_hierarchy(&[
            NominalClass {
                name: "Item".to_owned(),
                parent: None,
            },
            NominalClass {
                name: "Item".to_owned(),
                parent: None,
            },
        ]));
        assert!(!validate_nominal_hierarchy(&[NominalClass {
            name: "Item".to_owned(),
            parent: Some("Missing".to_owned()),
        }]));
        assert!(!validate_nominal_hierarchy(&[
            NominalClass {
                name: "Left".to_owned(),
                parent: Some("Right".to_owned()),
            },
            NominalClass {
                name: "Right".to_owned(),
                parent: Some("Left".to_owned()),
            },
        ]));
    }

    #[test]
    fn subclassing_is_reflexive_transitive_and_rejects_unrelated_classes() {
        let classes = hierarchy();
        assert!(is_subclass("Child", "Child", &classes));
        assert!(is_subclass("Grandchild", "Base", &classes));
        assert!(is_subclass("Grandchild", "object", &classes));
        assert!(!is_subclass("Grandchild", "Other", &classes));
        assert!(!is_subclass("Missing", "object", &classes));
        assert!(!is_subclass("Missing", "Missing", &classes));
        assert!(!is_assignable(
            &Type::Class("Missing".to_owned()),
            &Type::Object,
            &classes,
        ));
    }

    #[test]
    fn normalization_flattens_and_deduplicates_without_reordering() {
        assert_eq!(
            normalize_union(vec![
                Type::Int,
                Type::Union(types(vec![Type::None, Type::Int])),
                Type::Str,
            ]),
            Type::Union(types(vec![Type::Int, Type::None, Type::Str]))
        );
        assert_eq!(normalize_union(vec![Type::None, Type::None]), Type::None);
    }

    #[test]
    fn recursive_type_lists_round_trip_order_and_deep_nesting() {
        let original = vec![Type::Int, Type::None, Type::Str, Type::Bool];
        let list = TypeList::from_vec(original.clone());
        let items = type_items(&list);
        assert_eq!(items.len(), original.len());
        assert_eq!(items.into_iter().cloned().collect::<Vec<_>>(), original);

        let mut deeply_nested = Type::Int;
        for _ in 0..128 {
            deeply_nested = Type::Union(types(vec![deeply_nested]));
        }
        assert_eq!(normalize_union(vec![deeply_nested]), Type::Int);
    }

    #[test]
    fn structural_assignability_preserves_python_bool_and_container_rules() {
        let classes = hierarchy();
        assert!(is_assignable(&Type::Bool, &Type::Int, &classes));
        assert!(is_assignable(
            &Type::FixedTuple(types(vec![Type::Bool, Type::Int])),
            &Type::VariadicTuple(Box::new(Type::Int)),
            &classes,
        ));
        assert!(!is_assignable(
            &Type::List(Box::new(Type::Bool)),
            &Type::List(Box::new(Type::Int)),
            &classes,
        ));
        assert!(!is_assignable(
            &Type::List(Box::new(Type::Int)),
            &Type::List(Box::new(Type::Str)),
            &classes,
        ));
    }

    #[test]
    fn casts_and_narrowing_cover_positive_and_refuted_paths() {
        let classes = hierarchy();
        let actual = Type::Union(types(vec![
            Type::Class("Child".to_owned()),
            Type::Class("Other".to_owned()),
            Type::None,
        ]));
        let base = Type::Class("Base".to_owned());
        assert_eq!(
            narrow_type(&actual, &base, true, &classes),
            Some(Type::Class("Child".to_owned()))
        );
        assert_eq!(
            narrow_type(&actual, &base, false, &classes),
            Some(Type::Union(types(vec![
                Type::Class("Other".to_owned()),
                Type::None,
            ])))
        );
        assert!(cast_compatible(
            &Type::FixedTuple(types(vec![Type::Int])),
            &Type::VariadicTuple(Box::new(Type::Object)),
            &classes,
        ));
        assert!(!cast_compatible(&Type::Str, &base, &classes));
        let invented = Type::Class("Missing".to_owned());
        assert!(!cast_compatible(
            &Type::FixedTuple(types(vec![invented.clone()])),
            &Type::VariadicTuple(Box::new(Type::Object)),
            &classes,
        ));
        assert_eq!(narrow_type(&invented, &Type::Int, false, &classes), None);
    }
}
