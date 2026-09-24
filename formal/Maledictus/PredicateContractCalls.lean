namespace Maledictus

/-!
Model-only algebra for source well-formedness of `Fold`, `Unfold`, and `Unfolding` operands.

This is constructive documentation, not extracted frontend code and not a Rust-to-Lean refinement
proof. Production additionally resolves real Python imports, decorators, scopes, and rebindings.
-/

inductive PredicateBinding where
  | declaredPredicate
  | ordinaryCallable
  | rebound
  | unknown
  deriving DecidableEq, Repr

inductive PredicateContractKind where
  | fold
  | unfold
  | unfolding
  deriving DecidableEq, Repr

def predicateContractArity : PredicateContractKind → Nat
  | .fold | .unfold => 1
  | .unfolding => 2

def predicateContractCallValid
    (kind : PredicateContractKind)
    (argumentCount : Nat)
    (hasKeywords operandIsCall : Bool)
    (binding : PredicateBinding) : Bool :=
  argumentCount == predicateContractArity kind
    && !hasKeywords
    && operandIsCall
    && binding == .declaredPredicate

theorem declared_predicate_with_exact_shape_is_valid (kind : PredicateContractKind) :
    predicateContractCallValid kind (predicateContractArity kind) false true
      .declaredPredicate = true := by
  cases kind <;> decide

theorem ordinary_callable_is_not_a_predicate_contract_operand
    (kind : PredicateContractKind) (argumentCount : Nat)
    (hasKeywords operandIsCall : Bool) :
    predicateContractCallValid kind argumentCount hasKeywords operandIsCall
      .ordinaryCallable = false := by
  simp [predicateContractCallValid]

theorem rebound_predicate_name_is_not_trusted
    (kind : PredicateContractKind) (argumentCount : Nat)
    (hasKeywords operandIsCall : Bool) :
    predicateContractCallValid kind argumentCount hasKeywords operandIsCall .rebound = false := by
  simp [predicateContractCallValid]

theorem unknown_dynamic_operand_fails_closed
    (kind : PredicateContractKind) (argumentCount : Nat)
    (hasKeywords operandIsCall : Bool) :
    predicateContractCallValid kind argumentCount hasKeywords operandIsCall .unknown = false := by
  simp [predicateContractCallValid]

theorem noncall_operand_is_invalid
    (kind : PredicateContractKind) (binding : PredicateBinding) :
    predicateContractCallValid kind (predicateContractArity kind) false false binding = false := by
  simp [predicateContractCallValid]

end Maledictus
