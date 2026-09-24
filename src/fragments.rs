//! Canonical public identities for the Python proof fragments.
//!
//! Issuance and capability discovery must use the same values. Keeping these identities in one
//! source-owned module prevents a verifier release from advertising one semantic fragment while
//! recording another in a proof response.

pub const CLOSED_TOTAL_FUNCTIONS: &str = "closed-total-functions+safe-builtin-slices/v1";
pub const CAUGHT_CALLABLE_DATACLASS_BOUNDARIES: &str = "caught-callable-dataclass-boundaries/v1";
pub const SCALAR_NAGINI_CONTRACTS: &str = "scalar-nagini-contracts/v44";
pub const NOMINAL_REFERENCE_CONTRACTS: &str = "nominal-reference-contracts/v4";
pub const HEAP_METHOD_CONTRACTS: &str = "heap-method-contracts/v76";
pub const CHECKED_EXTERNAL_SCALAR_CONTRACTS: &str = "checked-external-scalar-contracts/v26";
pub const CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS: &str =
    "checked-external-nominal-reference-contracts/v4";
pub const TRANSITIVE_SOURCE_SCALAR_CONTRACTS: &str = "transitive-source-scalar-contracts/v33";
pub const TRANSITIVE_SOURCE_CHECKED_EXTERNAL_SCALAR_CONTRACTS: &str =
    "transitive-source+checked-external-scalar-contracts/v33";
pub const TRANSITIVE_SOURCE_NOMINAL_REFERENCE_CONTRACTS: &str =
    "transitive-source-nominal-reference-contracts/v4";
pub const TRANSITIVE_SOURCE_CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS: &str =
    "transitive-source+checked-external-nominal-reference-contracts/v4";
pub const TRANSITIVE_SOURCE_HEAP_CONTRACTS: &str = "transitive-source-heap-contracts/v64";
pub const CHECKED_EXTERNAL_HEAP_CONTRACTS: &str = "checked-external-heap-contracts/v5";
pub const TRANSITIVE_SOURCE_CHECKED_EXTERNAL_HEAP_CONTRACTS: &str =
    "transitive-source+checked-external-heap-contracts/v64";
pub const DAGCERT_CLOSED_TYPED_OPERATIONS: &str = "dagcert-closed-typed-operations/v3";

pub const PYTHON_CAPABILITIES: [&str; 17] = [
    CLOSED_TOTAL_FUNCTIONS,
    CAUGHT_CALLABLE_DATACLASS_BOUNDARIES,
    SCALAR_NAGINI_CONTRACTS,
    NOMINAL_REFERENCE_CONTRACTS,
    HEAP_METHOD_CONTRACTS,
    CHECKED_EXTERNAL_SCALAR_CONTRACTS,
    CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS,
    TRANSITIVE_SOURCE_SCALAR_CONTRACTS,
    TRANSITIVE_SOURCE_CHECKED_EXTERNAL_SCALAR_CONTRACTS,
    TRANSITIVE_SOURCE_NOMINAL_REFERENCE_CONTRACTS,
    TRANSITIVE_SOURCE_CHECKED_EXTERNAL_NOMINAL_REFERENCE_CONTRACTS,
    TRANSITIVE_SOURCE_HEAP_CONTRACTS,
    CHECKED_EXTERNAL_HEAP_CONTRACTS,
    TRANSITIVE_SOURCE_CHECKED_EXTERNAL_HEAP_CONTRACTS,
    DAGCERT_CLOSED_TYPED_OPERATIONS,
    crate::mixed_language::MIXED_LANGUAGE_FRAGMENT,
    crate::call_binding::IDENTITY,
];

pub fn advertised_for_language(language: &str, fragment: &str) -> bool {
    match language {
        "python" => PYTHON_CAPABILITIES.contains(&fragment),
        "javascript" => {
            fragment == crate::typescript::JAVASCRIPT_FRAGMENT
                || fragment == crate::mixed_language::MIXED_LANGUAGE_FRAGMENT
        }
        "typescript" => {
            fragment == crate::typescript::TYPESCRIPT_FRAGMENT
                || fragment == crate::mixed_language::MIXED_LANGUAGE_FRAGMENT
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn issuance_fragments_are_language_scoped() {
        assert!(advertised_for_language("python", SCALAR_NAGINI_CONTRACTS));
        assert!(advertised_for_language(
            "javascript",
            crate::typescript::JAVASCRIPT_FRAGMENT
        ));
        assert!(advertised_for_language(
            "typescript",
            crate::typescript::TYPESCRIPT_FRAGMENT
        ));
        assert!(advertised_for_language(
            "javascript",
            crate::mixed_language::MIXED_LANGUAGE_FRAGMENT
        ));
        assert!(!advertised_for_language(
            "javascript",
            SCALAR_NAGINI_CONTRACTS
        ));
        assert!(!advertised_for_language("python", "unknown-fragment/v1"));
        assert!(!advertised_for_language(
            "unsupported-language",
            CLOSED_TOTAL_FUNCTIONS
        ));
    }
}
