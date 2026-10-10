# Closed operations with native postconditions

The Python proof fragment
`dagcert-closed-typed-operations+semantic-postconditions/v1` combines two checks
on the same requested source operation: its closed typed outcome/exception
boundary, and its native `Ensures` postconditions. Strict pinned mypy checking
still runs. A generic heap proof, an assertion-only proof, or a successful
operation-signature check is not this joint proof. Consumers must check the exact
file fragment and source identity, not only a top-level `proved` status.

Use canonical imports from `nagini_contracts.contracts` for `Ensures`, `Old`, and
`ResultT`. Place postconditions at the beginning of the operation body. These
declarations are proof obligations, not trusted assertions or extra application
preconditions. Rebound contract names, unsupported declarations, missing returns,
and unclosed exceptional paths do not acquire the joint fragment. In particular,
adding `Requires(False)` cannot make an operation's postconditions vacuously true.

## Values, outcomes, and cleanup

Closed operation inputs may expose the readable fields of source-proved frozen
value records, including nested frozen records. This permission is for reading
those projections. It does not grant ownership of arbitrary mutable state merely
because a frozen record refers to it, and does not permit assigning frozen fields.
Ordinary heap functions do not automatically receive this operation-entry rule.

`ResultT(Completed)` and `ResultT(Idle)` in a union-returning operation project the
same actual final return reference; the type argument does not create another
outcome. Guard outcome-specific fields with the corresponding runtime class test:

```python
Ensures(
    not isinstance(ResultT(Completed), Completed)
    or ResultT(Completed).value == Old(request.value)
)
```

Boolean `and`/`or` guards follow Python's left-to-right short-circuit evaluation.
A skipped operand needs no field read, but every executed operand must have the
required permission. An absent field read cannot be justified by a tautology such
as `field == field`, a guard for a different outcome, or a later `or True`.
Conditional-expression field-read guards are not covered by this rule.

Native postconditions are checked at the final function exit, after modeled
`finally` and context-manager cleanup. A cleanup return may replace the pending
return; mutation may change the returned object's contents; cleanup may throw.
These effects cannot be proved away by checking an assertion immediately before
the original `return`. Context-manager bodies and exit effects must themselves be
supported and proved or covered by explicit external contracts; this is not
blanket support for arbitrary context managers.

For operations using checked external providers, both `with provider():` and
`with provider() as value:` use the provider's checked entry/exit summaries. The
complete original operation body is verified together with its final outcome and
postconditions; context-manager statements are not replaced with success-shaped
stubs. External preconditions must hold at the actual call, and an external
exceptional exit not handled by the operation invalidates its exception closure.
Imports must resolve to the sealed provider/source closure. Merely naming an
imported module does not authorize ignoring its effects or an unknown member.

This joint external-body route currently admits finite synchronous bodies.
Loops, comprehensions, generators and asynchronous suspension are refused with
`frontend.python.dagcert.semantic-body-termination-unproved`; recursive calls
remain refused by the existing call analysis. A partial-correctness postcondition
is not a termination proof. There is no instruction-count threshold or selected
context-manager-name whitelist: admitted syntax still has to pass full native
heap verification. Missing concrete callable bindings, arbitrary module-level
execution, and application `Requires`/`Exsures` declarations are not bypasses.

Operation `if` conditions support the modeled total truth tests for `bool`, `int`,
`str`, `bytes`, `None`, and homogeneous primitive tuples. Zero and empty values are
false. User-defined `__bool__`/`__len__` methods are not silently assumed total.
This addition does not imply general float truthiness or arbitrary Python
operand-returning Boolean expressions.

## Explicit limitations

Canonical `from typing import TYPE_CHECKING` import-only module gates are treated
as runtime-false. Their runtime `else` branches are retained; rebinding the marker
or putting arbitrary statements in the type-only branch is refused. This does
not create runtime bindings for names imported only for annotations, and does not
erase or weaken unresolved source annotations. In particular, recursive mutable
JSON aliases still need a recursive type/heap model. They receive a targeted
source-located refusal instead of being misreported as ordinary bitwise OR.

Mutation of a local list retained by a heap record is refused with
`frontend.python.heap.list-mutation-heap-alias-unsupported`. Treating such a list
as a replaceable local value would miss mutation through aliases, including
mutation during cleanup. The refusal covers detected nested record captures and
supported list mutation forms. Read-only records, mutation before capture,
independent local list copies, and scalar length snapshots have positive controls.
The current contents-based representation may conservatively refuse equal-content
copies after heap capture; it does not provide general allocation-aware shared-list
mutation semantics.

Scalar `Old` rewriting supports `int`, `bool`, and `str` fields rooted in a typed
entry-state local, including paths through plain source-owned, nonoptional frozen
records such as `Old(request.narration.turn.id)`. Every hop reads the entry heap
and requires entry-state read permission; a tautology does not waive those reads.
The original root binding is retained if ordinary heap code later reassigns its
local. This does not relax the closed-operation single-assignment rule. Nested
integer and Boolean relations have both correct and opposite-predicate semantic
controls, alongside missing-permission and changed-root controls.

Nested mutable or optional receivers, descriptors, whole-object/container
snapshots such as `Old(bytes)`/`Old(tuple)`, and `Old(len(request.value))` remain
unsupported. The truthiness tests for immutable bytes and tuples instead return
the actual input length as a scalar alongside the branch result, then prove their
relationship. This is not general collection snapshot support.

## Native object indexing

Read-only `receiver[index]` on a modeled native object uses its sealed external
`__getitem__` method contract. It does not turn the object into a Python list or
assume that indexing succeeds. The receiver is evaluated once, followed by the
index once, before the method contract is applied. Exceptional receiver, index,
and method paths remain subject to the enclosing operation's exception closure.
The same checked preconditions, heap effects, and normal/exceptional summaries
used for explicit native method calls apply to this syntax.

For example, a runtime-specific contract may model `Path.parents` as returning
the actual native parent-sequence class, whose integer `__getitem__` returns a
`Path` or raises. Neither an index-validity guarantee nor a filesystem guarantee
follows from that return type. The standard-library type checker remains active.
Native contracts are explicit platform premises, not verified implementations.

This support is for read expressions whose nominal dispatch is supported by the
existing checked native-method model. It does not add source-defined indexing,
slices, item assignment/deletion, or arbitrary module initialization. In
particular, proving an expression inside an operation does not establish that
the same expression in import-time code has a closed exception boundary.
The existing canonical native import-name requirement is unchanged. A receiver
whose runtime class is not known exactly is refused if a source-owned subtype
can override its native `__getitem__` contract; selecting only the caller must
not bypass that check. This feature does not prove arbitrary behavioral
subtyping.

## Native calls and standard-library interfaces

Native method receivers and arguments may themselves be effectful expressions,
including a constructor chain or a permission-checked source field used directly
in a `with` statement. Evaluation retains each normal and exceptional path in
Python order; it does not evaluate the expression outside the verified boundary
or assume that context entry, body execution, or cleanup succeeds.
This uses the full-path expression evaluator; other statement lowerers do not
yet accept every equivalent expression. In particular, the inline context form
can prove while a chained constructor/method call assigned to a local is still
refused. That refusal is retained, not treated as proof or silently rewritten.

The native `receiver / child` form is supported for a sealed `__truediv__`
contract and a builtin string child. This covers path construction without
rewriting production code into artificial tasks. It does not add reflected
user-object dispatch or permit a nominal return contract to hide
`NotImplemented`. Signed integer literal defaults such as `buffering=-1` retain
their actual position and value; arbitrary expressions in native defaults remain
unsupported.

Partial `io` and `pathlib` effect contracts no longer replace the complete pinned
standard-library typing interfaces. Strict typing therefore retains unrelated
APIs such as `io.BytesIO` and inherited `PathLike` compatibility. This is not an
effect-contract exemption: any native call used in a semantic proof still needs
its own declared contract. The pinned typeshed interfaces check types, not
exception closure or application-specific semantic postconditions.

## Behavioral regressions

From the backend repository with its pinned mypy and solver runtime configured:

```text
cargo test --release --test dagcert_native_postconditions
cargo test --release --test dagcert_local_record_permissions
cargo test --release --test dagcert_guarded_outcome_reads
cargo test --release --test heap_future_and_operation_truthiness
cargo test --release --test heap_record_list_aliases
cargo test --release --test heap_type_only_admission
cargo test --release --test heap_old_nested_scalar_paths
cargo test --release --test external_nominal_index_reads
cargo test --release --test external_native_expression_calls
cargo test --release --test external_signed_integer_defaults
cargo test --release --test external_stdlib_type_surfaces
```

For raw Windows test executables, the pinned `libz3.dll` must be discoverable.
`MALEDICTUS_MYPY_PYTHON` selects the pinned mypy interpreter, and
`MALEDICTUS_NAGINI_CONTRACTS` selects the canonical contract-support source root.
See [backend setup](dagcert-backend.md) for packaged-runtime handling. Coordinate
builds when sharing one Cargo target directory.

The controls include true/false native value relations, outcome replacement by
`finally`, missed return/exception paths, invalid ownership and short-circuit
guards, opposite primitive-truthiness postconditions, and both true and false
claims involving unsupported shared-list aliases. A false supported relation
must fail its semantic obligation; an unsupported alias must report its precise
refusal. A refusal is not proof of the relation's negation.

The real Dagcert cleanup integration also distinguishes semantic rejection from
unsupported syntax. A supported `raise Exception()` path and a provider's
declared exceptional cleanup fail the actual `exception-undeclared` obligation.
Direct `raise BaseException()` construction currently reports
`frontend.python.heap.raise-expression-unsupported` without proof obligations;
that negative control establishes refusal, not semantic handling of
`BaseException`. Both forms of `with` have positive final-return controls, a false
final-return relation is semantically rejected, and provider preconditions are
checked at their call site.

These fragment-level tests are not a production application certificate. In
particular, they do not establish that the complete h3 worker/import/transport
closure is supported or proved, and do not establish any timing guarantee by
themselves.
