# Roadmap

Each milestone must end in a backend that either proves its advertised fragment or refuses it. A
parser crash, missing type, unresolved call, unsupported construct, or incomplete import graph is a
refusal—not a warning and not a skipped obligation.

## M0: backend and kernel boundary

- Stable JSON request/response protocol for Dagcert and other callers.
- Source-root confinement, verifier-owned file hashing, and diagnostic locations.
- Executable Rust effect kernel plus initial Lean soundness theorems.
- Honest capability discovery and nonzero refusal status.

The first Rust-to-Lean cross-model regression slice is bounded and machine-readable. It
checks the real Rust call-expansion function against Lean for every zero-, one-, and two-item list
over the declared six-form argument alphabet, with both receiver states (86 cases). Generated
witness drift fails the Rust gate; a semantic mismatch fails the Lean build. It counts as zero
implementation-refinement coverage. General call binding, unbounded lists, arbitrary values, and
frontend lowering remain explicit refinement backlog.

## M1: Python closed-world core

- Parse real Python source and construct a complete reachable call graph.
- Resolve source annotations into Maledictus types; reject `Any` and missing annotations.
- Infer all normal and exceptional exits for the supported fragment.
- Support builtin slicing and callable-valued dataclass fields without verifier crashes.
- Compare behavior against pinned positive and negative Nagini fixtures.
- Lower source classes, versioned heap fields, fractional permissions, argument-keyed predicate
  instances, fixed tuples, homogeneous list values, and nominal exception references into VC IR
  v17; the IR and
  solver primitives exist, while production Python class lowering remains in progress.

The pinned upstream suite is recorded in `conformance/nagini-v1.3.1.json`. Run its inventory with:

```text
maledictus conformance inventory --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json
```

The growing exact-diagnostic gate is recorded separately in
`conformance/scalar-fixtures-v1.json` and runs with:

```text
maledictus conformance check-scalar-suite --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json --manifest conformance/scalar-fixtures-v1.json
```

The independently pinned heap gate is recorded in `conformance/heap-fixtures-v1.json` and runs
with:

```text
maledictus conformance check-heap-suite --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json --manifest conformance/heap-fixtures-v1.json
```

Its first exact upstream matches include `issues/00071.py` (a field type derived from a typed
constructor assignment, constructor allocation from a module function, and a chained
instance-method call) and `issues/00119.py` (constructor postconditions consumed by module-level
field assertions, including the exact expected negative diagnostic).
`issues/00056.py` is also exact: optional references may both be null, while constructors may
temporarily assign null to a non-optional reference only if they prove that every such field is
non-null at normal exit. Nominal constructor parameters retain their source class and implicit
non-null premise rather than collapsing to an untyped reference.
`issues/00263.py`, `test_property_inherited.py`, and the full `test_property.py` are exact property
matches. The verifier proves
the direct-field getter body, resolves inherited property reads to that field and its `Acc`
permission, and uses a direct-return `@Pure` body as a checked result equation. Pure reads do not
consume ownership. Incompatible pure overrides and property redirects are proof failures or
explicit refusals rather than dynamically trusted descriptors. Computed getters, permission-checked
single-field setters, chained self-returning receivers, and positive-literal `//` semantics are
lowered into heap and VC obligations; getter-definition, getter-application, setter-call, write,
and postcondition failures retain their distinct upstream diagnostics.
`test_constructor.py` is also an exact match: v11 verifies a source-defined single-inheritance
layout, applies the direct base constructor contract at `super().__init__`, retains constructor
ownership for inherited and derived fields, decides `isinstance` only for freshly constructed
objects with an exact runtime class, and checks module-level field writes. It reproduces the
fixture's expected failed assertion at its original source line.
`issues/00176.py` is an exact positive match across two inherited constructor calls. Constructor
receivers may use any unannotated Python identifier (not merely the conventional `self` spelling),
and the canonical `if __name__ == "__main__": main()` entry guard is accepted only when it invokes
a verified zero-argument `None` function with no precondition.
The pinned `select/SubB.py` fixture is an exact negative behavioral-subtyping match. Heap
conformance now honors Nagini's filename-derived class selection: selected bodies and their
override obligations are proved, while unselected bodies remain modular summaries and cannot add
or hide diagnostics. Integer `+`, `-`, and `*` expressions are lowered through the same typed VC
IR in heap methods.
The v22 heap frontend accepts non-optional class-typed parameters on module functions, methods,
and constructors,
preserves source nominal method return types, uses the selected receiver's declared layout for
field permissions and call contracts, and accepts call arguments only through the proved source
subtype graph. It also uses module-function `Requires` permissions for field reads and method
calls, checks function `Ensures`, and supports immutable explicitly annotated scalar locals.
Expressions that read fields through receivers from different layouts remain an explicit refusal
rather than being lowered through an arbitrary layout.
Single inheritance includes inherited fields, methods, constructor summaries, and solver-checked
behavioral override obligations: overriding methods may neither strengthen preconditions, weaken
postconditions, nor widen their write frame. Version 10 checks nominal parameters
contravariantly and nominal returns covariantly. Multiple or dynamic bases, `super` method calls
other than the zero-argument direct-base constructor form, optional nominal method annotations,
and runtime-class tests on non-exact values remain explicit
refusals.

Version 16 adds source-ordered immutable `int`/`bool` module initialization to the heap frontend.
Initializers may use only already-bound scalar globals and total scalar expressions; calls,
references, heap reads, rebinding, explicit `global`/`nonlocal` mutation, forward references, and
partial or unsupported expressions refuse. Python lexical locals are computed for the complete
callable body before lowering, so an assignment later in a function cannot make an earlier read
silently fall through to a same-named global. Method, property, and constructor summaries capture
their declaring module's sealed environment. Inherited and imported summaries therefore retain
provider values even when a subclass or caller declares the same global name. Calls during module
initialization remain outside this fragment until the ordered module executor is implemented.

Version 17 adds the passive class/module namespace needed for definition-time Python behavior.
Docstring/pass-only classes and verified declaration-only modules are non-vacuous successes.
Immutable scalar class constants execute against the globals visible at the class statement, while
a zero-argument instance of an empty source class may be retained as an opaque passive module
binding. Such reference bindings cannot enter verified callable logic until their nominal and heap
effects are modeled. A missing direct base or class-body global becomes a located false
definedness obligation and stops later module initialization rather than being mislabeled as
unsupported syntax. This exactly matches the pinned `issues/00027.py`, `issues/00065.py`,
`test_global_definedness_10.py`, and `test_global_definedness_11.py` fixtures.

Version 18 adds typed, effect-free primitive module functions and call-time namespace resolution.
It verifies `int`/`bool` arguments and results, exact return bodies and postconditions, acyclic
transitive calls, and provider-global sealing across source imports. During module initialization,
function bodies resolve globals and callees against the current source prefix; an unavailable
transitive callee emits one located false obligation at the outer initializer and halts later
initialization. This exactly matches `test_global_definedness_4.py` without treating the later
definition as if it had existed earlier.

Version 19 executes zero-argument, heap-neutral source constructors at module scope and resolves
their transitive primitive/global dependencies against the call-time prefix. Successful calls are
represented by explicit module obligations. A missing dependency is attributed once to the outer
constructor statement and halts the namespace, so later assignments cannot repair the failure.
This exactly matches `test_global_definedness_5.py`; module-time constructor heap effects remain a
fail-closed boundary until the executor carries an explicit heap transition state.

Version 20 executes the first typed virtual-dispatch shape at module scope: one source-class
parameter, one zero-argument scalar method call, and an implicit effect-free constructor argument.
Every currently defined subtype contributes its effective override to the dispatch set. Each
override must directly return an immutable scalar already defined at that call prefix. This
exactly matches `test_global_definedness_6.py`; contracts, heap effects, nontrivial constructors,
method arguments, and general method bodies remain explicit refusal boundaries.

Version 21 evaluates source function annotations in definition order. Quoted nominal annotations
are deferred strings; bare nominal annotations require an already defined class at the function
statement. Exact scalar-literal and implicit-constructor return bodies are retained as typed finite
summaries. This exactly matches `test_global_definedness_7.py` and
`test_global_definedness_8.py`, including attribution to the function declaration.

Version 22 models `@staticmethod` as a distinct receiver kind. Static method bodies and scalar
postconditions are verified without a synthetic instance argument, instance-based calls retain
only the explicitly declared static parameters, and override compatibility rejects switching
between static and instance methods. This exactly matches
`test_behavioural_subtyping_static.py`, including the weakened-postcondition diagnostic.

Version 23 adds source-resolved class-qualified static dispatch. Direct and inherited calls use
the same verified static summary and explicit argument list as instance-based static access, while
`A.instance_method(...)` is rejected because a class object cannot supply the missing instance.
Calls compose verified pre/postconditions and permission effects rather than inlining or trusting
the callee body.

Version 24 introduces a distinct class-object sort and source-bound `@classmethod` summaries.
The implicit `cls` argument is a class object, `type(value)` produces a class object, and
`isinstance(value, cls)` lowers to nominal runtime-class subtyping rather than reference identity.
Calling an inherited classmethod through `Derived.method(...)` binds `cls` to `Derived`; a direct
`cls()` construction applies the verified constructor contract for the declared upper bound and
records the result's exact runtime-class identity. Receiver-kind changes are rejected during
behavioral-subtyping checks, and constructor/postcondition weakening used by dynamic construction
is attributed to its source clause. This exactly matches
`test_behavioural_subtyping_classmethod.py`. General class attributes, predicates, `Fold`/`Unfold`,
and arbitrary reflective class-object operations remained explicit refusal boundaries in that
version.

Version 25 adds the first source-owned predicate-resource fragment. A predicate is a separately
typed class member whose direct boolean body must frame every field read with a full
`Acc(self.field)` conjunct. Fold consumes those field locations and produces one reserved
predicate-token location; Unfold performs the inverse exchange. Every location is transferred in
one versioned permission-mask step, validity is reproved, and hidden body fields cannot be read or
written while the token is folded. Predicate overrides dispatch through the runtime receiver class.
The same slice preserves immutable inherited class constants, verifies supported
`cls.static_method(cls.constant)` calls, treats independent `cls()` results as fresh, and gives
distinct source classes distinct class-object values. It exactly matches `test_classmethod.py` and
`test_behavioural_subtyping_predicates.py`. Version 26 adds typed top-level predicate arguments,
positive literal fractional predicate bodies, argument-keyed ownership tokens, and
`Unfolding(...)` with automatic refolding. Recursive predicates, abstract predicates, and general
predicate families remain explicit refusals.
Version 27 makes modular predicate ownership fail closed. Method predicate preconditions and
non-fresh predicate postconditions refuse until caller-mask token transfer is modeled.
Constructors and direct base constructors also refuse predicate ownership taken from an existing
caller object or returned for a non-fresh object. The supported exception is a folded predicate
returned for the constructor's or dynamically constructing classmethod's fresh result.
Version 28 adds exact nominal source-constructor results as constructor field initializers. The
accepted call resolves to a verified source-owned ordinary `__init__`, has no exceptional outcome,
matches the field's nominal class exactly, and belongs to an acyclic finite constructor graph. Its
postconditions establish the fresh result before the outer field write. The frontend emits frames
for the nested result's declared fields and the outer receiver's other declared fields; the Lean
model only constructs and typechecks those frame equalities from frontend premises. Custom
`__new__` on the class or anywhere in its effective allocation chain, metaclasses, imported or
external constructors, exceptional outcomes on the constructor or a called base constructor,
nominal mismatches, and cycles must refuse. Lean does not prove semantic arbitrary-receiver
preservation or Python-to-IR correspondence for this slice; its success rule instead takes
ordinary source allocator provenance, normal-only completion, and acyclicity of the effective
inherited/explicit-`super()` dependency closure as separate frontend premises.
Version 29 adds independently lowered contextual Boolean conjunctions for pure permission/reference
contract facts. Every operand must lower to Boolean IR, source order and all heap reads are retained,
and the result is one IR `and`. Effectful operands, truthiness coercion, and expressions whose
meaning depends on Python short-circuit side effects remain fail-closed. Lean models the
pure-expression classification as a frontend premise rather than proving it from Python syntax.
Version 30 resolves nominal method returns from nonempty chains made entirely from effective typed
fields, rather than confusing a field's value class with the class that owns the selected layout.
It separately accepts one verified source property read directly from a named receiver. Every
intermediate and final reference must be non-optional, and the final value class must equal or be a
proved source subtype of the declared return. A property inside a multi-hop chain, scalar,
unresolved, call-valued, dynamic-attribute, and unverified descriptor results remain fail-closed.
Lean typechecks the field-chain IR and compatibility gate from explicit frontend resolution/subtype
premises and models the direct-property gate separately; it does not prove Python correspondence
or descriptor semantics.
Version 31 accepts only `self.field is Old(self.field)` in a normal postcondition for a direct,
non-optional effective typed reference field on a verified source-owned non-constructor instance
method. Old/current reads use distinct entry/exit heaps and independently require entry/exit mask
permission. The complete direct-plus-transitive modification set must exclude the field; method
call summaries rebind both heaps and masks at every invocation. Modified fields, constructors,
nested, property/descriptor-target, or dynamic access, calls inside `Old`, external contract-only
methods, and exception postconditions remain fail-closed. Lean constructs and typechecks the IR reads, permissions, frame,
and rebinding from frontend premises without claiming Python correspondence, permission truth,
modification-set completeness, or semantic framing.
Version 32 accepts only `Result() is self.field` or `Result() is not self.field` in a normal
postcondition for a verified
source-owned, non-constructor instance method. Both values must be non-optional references with an
exact effective-field/declared-return nominal match; method-type construction rejects
`Optional[...]` returns before this rule. The field read uses the method-exit heap and
requires exit-mask permission. The source frontend must prove a unique terminal normal return with
no executable successor and proves the selected equality or negated equality against the current
field value on every supported normal return; type compatibility without reference identity is not
enough. Call summaries rebind result, receiver,
exit heap, and exit mask. Constructors, identity inside `Exsures`, property/descriptor targets, optional or scalar
fields, nested/dynamic/call-valued targets, external contract-only methods, and unsupported control
flow remain fail-closed. Lean models this IR construction and rebinding from explicit premises,
without claiming Python correspondence, path completeness, permission truth, or provenance truth.
Version 33 permits late-bound source class names in the supported subset of method contracts and
bodies without treating them as defined before runtime. Method parsing is independent of the
definition prefix; full-module resolution must map every dependency to one canonical source class,
and the summary retains that finite dependency set. A module-initializer call requires every local
dependency in its exact class prefix, while an imported source summary requires its canonical
provider initialization to be complete. Later definitions cannot repair an earlier call, and a
never-defined, shadowed, dynamic, reflective, or unchecked-external name refuses. Bases,
decorators, class-body expressions, and bare method annotations remain eager; only the existing
quoted/deferred annotation path defers. Lean models these checks from explicit
frontend premises and does not claim Python/frontend correspondence or prove the premises.

Version 34 composes a source-ordered chain of non-optional nominal-reference
field reads and verified zero-argument source method calls, including the chain in upstream
`test_method_calls.py:58`. Each field step uses the immediately preceding reference and records a
positive read-permission obligation in that step's current mask. Each method step checks the
receiver's exact nominal class, records the summary's direct permission precondition, rebinds its
proved result/reference provenance in the call-exit heap, applies its proved exit permission
effect, and threads the returned reference, nominal class, heap, and mask into the next step.
State-preserving summaries retain the entry heap and mask; this includes verified no-write,
net-permission-neutral ordinary methods as well as applicable `@Pure` methods. State-changing
summaries advance exactly the affected versions: writes require a distinct heap and complete
modification/frame premise, while non-neutral permission effects require a distinct mask and
complete permission-transfer premise. Optional or scalar
results, calls with arguments, unresolved nominal identities, properties/descriptors, dynamic or reflective dispatch,
external contract-only summaries, fields inherited from checked-external bases, source methods whose
returned/precondition field is external-inherited, exceptional outcomes, and incomplete effects
remain fail-closed. The chain rule consumes an already verified modular summary rather than
recursively expanding its method body. The Lean model constructs and typechecks this IR trace from
explicit frontend premises; it does not prove Python correspondence, permission truth, semantic
framing, alias facts, or source-summary provenance.

`test_behavioural_subtyping.py` is now a pinned exact match with all eight expected diagnostics.
Version 11 checks fractional permission pre/postconditions in distinct masks, reports permission
failures separately from scalar contract failures, carries pass-only source exception hierarchies
and covariant `Exsures` declarations, and checks primitive literal method defaults. Non-neutral
permission summaries support calls through exact versioned permission-mask transfers. The verifier
proves that the caller has each consumed fraction, applies returned fractions in a fresh mask, and
checks that the result remains within `[0, 1]`; multiple same-field atoms on one contract side still
refuse until separating-conjunction sums are modeled.

The suite currently covers straight-line contracts, path-sensitive `if` returns, total-return
checking (including unreachable paths established by preconditions), explicit `Refute(...)`
polarity, and Nagini's function-level reporting for failed `Assert(...)` obligations in pure
functions. It also covers invariant establishment and preservation for nested scalar `while`
loops, augmented assignment, postconditions derived from loop exits, and the exact upstream
`issues/00054.py` `try/except` fixture. CI checks the pinned upstream commit before accepting the
comparison.

These loop rules establish Nagini-style partial correctness, not termination. A nonterminating
path cannot violate a normal-return postcondition, and Maledictus does not advertise a termination
proof for this fragment.

For a non-curated view, classify every fixture under a pinned tree:

```text
maledictus conformance classify-scalar --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json --root tests/functional/verification
```

The heap frontend has a separate full-tree refusal report:

```text
maledictus conformance classify-heap --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json --root tests/functional/verification
```

The nominal-reference gate covers source-class annotations, `Optional`, null identity, and typed
call preconditions:

```text
maledictus conformance check-reference-suite --suite .upstream/nagini --pin conformance/nagini-v1.3.1.json --manifest conformance/reference-fixtures-v1.json
```

Every file is reported as `matched`, `mismatched`, or `refused`. Refusals are deliberately not
passes; this report is the coverage backlog for the port.

Fixtures below Nagini's `select/` directory derive the selected symbol set exactly from the
hyphen-separated filename, matching the pinned pytest configuration. Only selected bodies produce
conformance obligations; unselected callable contracts remain modular dependencies. The special
`none.py` case may therefore contain no selected body. This zero-body result exists only inside the
pinned comparison harness and is never exposed as a non-vacuous Dagcert proof.

M1 is complete only when `capabilities` reports the exact supported Python fragment and the CLI can
issue a real `proved` response for it. The current fragment is
`closed-total-functions+safe-builtin-slices/v1`. The separate `scalar-nagini-contracts/v44` fragment
starts the functional-verification port with SMT-discharged `Requires`, `Ensures`, and assertions.
`caught-callable-dataclass-boundaries/v1` proves one exhaustive exception-closing pattern for typed
callable fields without relying on Nagini's crashing callable translation. None may be described as
general Python support.

Scalar contract v43 preserves recursively fixed tuple sorts across immutable collection
boundaries. Each tuple shape has a source-owned Z3 datatype; constructors and accessors connect
heterogeneous tuple fields to list sequences and dictionary arrays without type erasure. The
supported tranche includes tuple list elements, tuple dictionary keys and values, symbolic
tuple-set membership, and closed tuple-set literals with exact duplicate elimination. It does not
include collection mutation, `Old` snapshots, resource predicates, non-integer quantifiers, or
alias-sensitive identity.

Scalar contract v44 adds a distinct immutable `Tuple[T, ...]` sort rather than representing it as
either a fixed tuple or a `List[T]`. The VC and Z3 layers preserve its homogeneous element sort and
model symbolic length, guarded integer indexing with Python negative-index normalization, exact
literal-bound slicing (including reverse slices), equality, and source iteration. Tuple literals
cross into the variadic sort only at an explicit annotated boundary and every element is checked;
the reverse coercion and tuple-to-list coercion remain rejected. Starred loop targets are exact for
concrete tuple values and refuse when symbolic tuple width would have to be invented. This makes
the scalar backend an exact positive match for pinned fixture `issues/00115.py`; the already-exact
combined fixture count is unchanged because the heap backend previously covered it. The broader
`test_tuples.py` fixture remains refused at its independent `Union`/`cast` boundary, while
`issues/00164.py` and `issues/00196.py` remain blocked by strict-typechecking and class/Union
features. The Rust change expands `Term` from 64 to 68 constructors; formal coverage is reported
only from the regenerated source-bound Lean extraction, never inferred from these runtime tests.
The changed IR is `maledictus-scalar-vc/v27`; the checked-external, transitive-source, and combined
scalar identities advance to v26, v33, and v33 because they execute the same tuple lowering.

## M2: modules and external contracts

- Resolve source-owned imports transitively.
- Distinguish environment-owned providers from application code.
- Check explicit external contracts at the adapter boundary and retain their assumptions in the
  proof result.
- Bind every proof to the frontend, kernel, and contract hashes.

The first M2 slice is `checked-external-scalar-contracts/v16`. It checks explicit `from module
import symbol` adapter boundaries against verifier-parsed, hash-bound `@ContractOnly` scalar
contracts. Provider conformance and normal return remain visible assumptions; application adapter
bodies and call-site preconditions are proof obligations. Protocol v2 also reports the running
executable hash and compile-time frontend and kernel source-bundle hashes. General source import
resolution, provider discovery, and heap external contracts remain incomplete.

Scalar contract v21 models direct built-in and source-declared exception raises, Nagini `Exsures`,
propagation through modular source/external calls, and hierarchy-aware matching `try/except`
handlers. Exception class names and inheritance come from pass-only source declarations rather
than free-form contract strings. Imported identities retain their declaring module; two providers
cannot collapse distinct same-spelled exception classes into one type. A syntax prepass also
refuses unsupported statements and handler forms in unreachable paths instead of silently omitting
them. External contracts choose explicitly
between no exception and the finite `Exsures` union; mixing the two policies refuses.

Scalar contract v21 also introduces homogeneous immutable list values over primitive/reference
elements. `List[T]` and `list[T]` annotations, typed empty literals, nonempty literals, length,
sequence equality, and list indexing lower to Z3 sequences. Symbolic indexing forks on Python's
positive/negative bounds rule: the normal path receives the bounds fact and the complementary path
produces `IndexError`, which must be proved unreachable, declared with `Exsures`, or caught.
Indexing inside a specification refuses because it has no executable exception boundary. Mutation,
nested list elements, and alias-sensitive identity remain unsupported; this value fragment is not
represented as Python's mutable list heap model. Literal `range(...)`
values and Nagini's trigger-free `Forall` over finite known sequences are expanded exactly with a
fixed resource limit; symbolic quantification refuses. Finite `for` loops over those values are
unrolled with exact target state and `else` behavior, and static `in`/`not in` tests become finite
typed equality disjunctions. Symbolic iteration and abrupt loop control remain explicit refusals.

Scalar contract v21 preserves Python's value-returning `and`/`or` semantics and adds conditional
expressions. Index-error paths in short-circuited operands and unselected branches are guarded by
the actual evaluation condition, so a proof cannot invent eager exceptions or erase reachable
ones. Chained comparisons use the same left-to-right conditional evaluation rule. Symbolic branch
results—and statically dead branches—must have a compatible verified sort. In the immutable list-value fragment, `list_pred` is a
typed assertion that the operand is a represented homogeneous list; it does not introduce mutable
heap or permission semantics.

Version 19 exactly verifies Nagini's complete `test_slicing.py` fixture. Statically known lists,
fixed tuples, byte strings, and literal ranges retain distinct source types while constant Python
slice bounds and steps are normalized with Python's negative-index and clamping rules. `ToSeq` is
the explicit conversion to a homogeneous immutable sequence. Indexing still creates a normal path
guard and a complementary typed `IndexError` path; an uncaught reachable error maps to Nagini's
application-precondition diagnostic. Symbolic slicing and a zero step refuse rather than receiving
an invented total semantics.

Version 19 also exactly verifies Nagini's complete `test_range_step.py` fixture. A literal zero
step no longer causes a frontend refusal: executable `range` construction forks to a typed
`ValueError`, which can be caught or covered by `Exsures`; an uncaught reachable branch is an
application-precondition failure at the constructor call. The normal branch is explicitly
inconsistent and carries only a well-sorted placeholder, so it cannot fabricate a range value.
Short-circuit and conditional evaluation guards the exceptional branch. A zero-step constructor
inside a specification still refuses because no executable exception boundary exists there.

Version 20 exactly verifies Nagini's complete `test_bytes.py` fixture. Byte strings are symbolic
Z3 sequences with typed concatenation, length, truthiness, and integer indexing; indexing retains
the normal and `IndexError` branches used by other executable sequences. Constant integer
repetition and `bytes.join` over a statically shaped `List[bytes]` lower exactly. Symbolic repeat
counts and joins over a dynamically shaped list remain explicit refusal boundaries rather than
receiving an assumed length or element model.

Version 21 exactly verifies Nagini's complete `test_builtin_functions.py` fixture. Integer `abs`,
positional `min`/`max`, and nonnegative constant-exponent power up to 64 lower to existing typed VC
conditionals and multiplication; one-argument extrema require a statically shaped nonempty
`List[int]`. Symbolic exponents, negative exponents, dynamic extrema iterables, and empty extrema
refuse. The fixture's literal module-level `print` and Nagini's unboxed integer-identity
comparisons are handled only by the pinned function-comparison harness; ordinary backend
verification continues to reject executable module initialization and Python integer `is`/`is
not` rather than equating object identity with value equality.
Scalar identity v36 adds a finite source-known identity domain for aliases and fresh tuple/`range`
allocations plus canonical constant `str(int)` conversion. It proves only identities determined by
the source, keeps `is` separate from `==`, and refuses unknown parameter identity, shadowed
constructors, and implementation-dependent string interning. Two pinned identity fixtures now
match; the accompanying Lean identity algebra remains model-only and is not counted as extracted
Rust implementation refinement.

Scalar version 37 accepts module and function docstrings plus later inert string-literal
statements. Only the leading function literal is skipped before contract-prefix collection, so an
ordinary later string cannot make a late `Requires` or `Ensures` declarative. Arbitrary expression
statements do not acquire docstring semantics. Checked-external scalar advances to v21 and both
transitive scalar variants advance to v28 because they share the same source-module parser.

Version 22 exactly verifies Nagini's complete `test_post_lambda.py` fixture. The two-argument
`Ensures(ReturnType, lambda result: condition)` form checks the declared result type against the
real function annotation, requires one closed positional result binder, and lowers that binder to
the returned symbolic value on every path. The same representation is used by verified source
summaries and checked external stubs. Executable dynamic indexing of a nonempty fixed tuple creates
the same guarded normal and typed `IndexError` paths as other Python sequences. It is accepted only
when every component has one common result sort (with Python `bool`-to-`int` coercion); incompatible
components, empty tuples, and dynamic indexing in specifications refuse.

Version 23 exactly verifies Nagini's empty module and complete `test_global_vars.py` fixtures.
Immutable module initializers execute in source order and may use only already-bound globals and
already-defined, total source functions. Their inferred value sorts must match explicit
annotations. Every function receives the final immutable environment, while source-exported
summaries capture their provider's environment so an importer with a same-spelled global cannot
change the proof. Duplicate bindings, partial initializers, assignment to a function name,
explicit `global` mutation, and reads shadowed by a local assignment refuse. A literal
nonnegative `Decreases` annotation is accepted only for the already nonrecursive fragment; it does
not add an unproved termination claim or enable recursion. The same fragment accepts unique
undecorated `class Name: pass` declarations without exposing their class objects to scalar logic.
For a pass-only subclass of canonical unshadowed builtin `int`, one positional `int`/`bool`
construction preserves the exact inherited numeric value; this exactly matches issue 00261's
false assertion. Custom class behavior, other bases, class identity/annotations, keyword or
partial conversions, and module rebinding remain refusals.

The first source-DAG slice resolves conventional module names from requested `.py` paths and
recursively verifies every imported module before exporting its contracts. Refuted dependencies
cannot supply summaries, cycles refuse, and protocol v2 records every importer/provider edge and
provider hash. This slice supports absolute explicit `from module import symbol` calls in the
scalar fragment; relative imports, plain module imports, module initialization, re-exports, and
heap/object contracts remain future coverage rather than implicit assumptions. Version 4 carries
source-derived exception hierarchies through each module summary, including custom exception types
declared by checked external stubs.

`checked-external-nominal-reference-contracts/v1` is the first non-scalar external type slice. A
pass-only external class declaration establishes a module-qualified nominal identity, and
`@ContractOnly` functions may accept, return, or optionally return that type. Adapter assignments,
returns, identity assertions, and call arguments are checked against those real annotations.
Non-optional returns establish non-nullness; `Optional[T]` deliberately does not. Provider
conformance and the no-exception policy remain explicit assumptions. This slice does not yet
support fields, inheritance, mixed scalar/reference signatures, or external exceptional outcomes.
`transitive-source-nominal-reference-contracts/v1` recursively proves the same object-valued
signatures through source-owned modules before exporting them. The combined external/source
variant retains external provider assumptions while requiring every source module body to prove.

`transitive-source-heap-contracts/v48` exports source heap summaries only after applicable constructor,
method, primitive-function, field, and permission obligations prove. Importers consume the scalar field layout,
constructor pre/postconditions, typed method summaries, exact transitive write sets,
and exact `Acc` fractions.

The historical `heap-method-contracts/v48` / `transitive-source-heap-contracts/v42` slice added
closed monomorphic `Generic[T]` support. It accepts only canonical, unaliased module-level
`T = TypeVar("T")` declarations, a one-parameter `Generic[T]` class, and exactly one representable
concrete scalar or source-nominal specialization. Direct `T` field, parameter, and return
annotations are substituted before normal heap checking, including constructor argument checks;
the exact target is `issues/00266_1.py`. Type variables remain static declarations and are never
exported as runtime globals, captures, locals, or kernel terms. Bounds, constraints, variance,
defaults, aliases, rebinding, runtime use, composite or multiple specializations, unsupported
generic positions, and quoted direct `"T"` annotations fail closed. General parametric generics,
generic inheritance across independently specialized consumers, and richer typing forms remain
future work.

The same tranche removes an implicit class-context shortcut from module-function expression
lowering. Contextual expressions are attempted first, and any required heap root class must be
derived from an explicit typed receiver or class literal. No arbitrary class-catalog entry is used
as a fallback, so ambiguous wrappers refuse while supported cross-root comparisons remain valid.

Version 49/version 43 adds provider-qualified reusable canonical `@Pure` scalar functions with bounded
statement bodies: read-free scalar locals, initialized annotations, nested `if`/`else`, early
returns, a 64-path cap, all-path return checking, and `ite` result collapse. Provider callable
dependencies and immutable globals stay sealed under stable identities across source imports;
consumer shadowing, lexical parameter/local shadowing, recursion, mutable capture, and unsupported
effects fail closed. Definition-side `Assert` remains checkable, but an unsealed assertion-bearing
body is not reusable as a call summary.
Maybe-defined locals retain their exact structural-path guard and every later read emits a
definedness VC. Reachable non-Unit reusable-`@Pure` fallthrough is a
`function-totality:implicit-return[:path:i]` VC attributed to `function.not.wellformed`; ordinary
heap-function fallthrough continues to use `postcondition:implicit-return[:path:i]`.

The adjacent constructor slice executes nested and sequential read-free Boolean conditionals as
disjoint heap/mask paths. Branch bodies currently accept only `Pass` and direct current-receiver
field writes, including narrowly typed fresh `object()` initialization of an opaque reference.
Initialized fields and postconditions are checked per exit; conditional `Acc` exposure becomes a
refutable initialization-permission VC, while missing unpromised fields refuse. Ordinary-method
conditional effects, branch calls, field reads, complex receivers, and allocation provenance
beyond opaque `object()` remain future work. Typed integer unary minus and path-sensitive local
definedness complete the exact `test_definedness.py` match. These capabilities are the v49/v43
atomic heap/transitive fragment.

The corresponding constructive Lean slice is in `formal/Maledictus/HeapControl.lean`: 13 named
constructor-`if` theorems within 84 `HeapControl` theorems/lemmas and 448 formal declarations in
the release tree. It builds the branch paths, exact-sort writes, 64-path refusal, promised-missing
guarded-false VC, unpromised-missing refusal, and per-exit postcondition instances. Python AST
correspondence and frontend layout extraction remain explicit premises.

Version 50/version 44 adds bounded control flow to ordinary, nonexceptional source instance
methods returning `None`, `bool`, or `int`. It reuses the guarded heap-function executor for nested
and sequential `if`/`else`, early scalar returns, scalar locals and annotations, assertions,
permission-checked modeled field reads, and scalar writes to fields of the bound `self`. Every
actual path retains its own heap, mask, assumptions, obligations, locals, and return status; a
failed read/write VC halts only that path, non-Unit fallthrough emits a false implicit-return VC,
and postconditions are instantiated at each normal exit. Summary collection recursively unions
all conditionally written `self` fields so caller framing and override checks cannot omit a branch
effect. Calls, allocation, predicates, exceptional/static/class/property methods, foreign-receiver
effects, reference returns/writes, and more than 64 paths refuse. The constructive slice adds 9
ordinary-method theorems, bringing `HeapControl` to 93 declarations and the formal tree to 457,
with no `sorry` or `admit`.

Version 51/version 45 adds source-ordered immutable aliases of the canonical builtin `int`, `bool`,
and `object` type objects. Aliases carry class-sorted terms and count as executed module state.
Imports, declarations, and earlier assignments enter a separate bound-name prefix, preventing a
shadowed builtin spelling from being mistaken for the canonical builtin merely because its value is
outside the scalar environment. The scalar/transitive identities advance to v24/v18. Five new Lean
theorems bring `HeapControl` to 98 declarations and the formal tree to 462, with no proof holes.

Version 52 adds total compile-time selection from a finite list term by a static signed-64 integer.
It implements Python negative-index normalization in widened arithmetic and substitutes an element
only after the normalized position is proved in bounds. Symbolic elements are allowed; symbolic
indices, out-of-range positions, malformed or oversized list terms, and out-of-range integer
literals remain refusals. The scalar/transitive identities advance to v25/v19, while heap remains
v51/v45. Thirteen constructive theorems in `ConstantListIndex.lean` bring the formal tree to 475
declarations with no `sorry`, `admit`, or `axiom`.

Version 53 aligns undeclared exceptional exits with source-boundary diagnostics: ordinary uncaught
exits blame the callable declaration with `exhale.failed`, while partial-operation failures retain
their application-precondition code and operation location. Declared and caught exits are
suppressed, and identical path diagnostics are deduplicated only after every proof obligation is
retained. Scalar/transitive identities advance to v26/v20. Ten constructive theorems in
`ExceptionalExit.lean` bring the formal tree to 485 declarations without proof holes.

Version 54 preserves the declared nominal class of a class-qualified source method result when it
is assigned inside another ordinary method. A later raw-field read therefore resolves against the
selected source summary rather than losing its receiver type. Python `assert` statements in
ordinary methods are lowered at the current heap and permission-mask versions, emit their field
read obligations before the assertion VC, and refuse constructor reads of fields that have not yet
been initialized. Reassigning the same local to a scalar result clears the earlier nominal
provenance.

A source method that directly returns a verified fresh source construction may transfer
`Acc(Result().field)` only after the call rule establishes that the fresh result held zero
permission for that field in the caller's pre-mask. External allocators, custom `__new__`,
exceptional constructors, indirect return expressions, and unresolved result classes do not
receive this premise. The heap/transitive identities advance to v52/v46. The exact pinned target is
`issues/00266_3.py`; the curated conformance gate contains 72 fixtures, and broad scalar/heap union
coverage is 71 of 219 fixtures (32.4%) with zero accepted mismatches. Twenty-two constructive
theorems in `OrdinaryMethodParity.lean` bring the complete formal tree to 507 declarations without
`sorry`, `admit`, or `axiom`.

Version 55 closes the pinned-conformance source graph instead of verifying imported fixtures as
isolated files. Absolute explicit `from module import symbol` edges are resolved recursively from
the importing fixture to the nearest source provider under the pinned suite root. Every provider
body and parent package initializer must verify before the consumer can use its summary; missing,
ambiguous, symlinked, cyclic, or refuted providers fail closed. A verified intermediate module may
explicitly re-export a class, primitive function, reference-identity function, or predicate, while
the binding retains the leaf provider's canonical identity rather than acquiring a synthetic
intermediate identity. Passive immutable package metadata (`str`, `bytes`, `None`, or `Ellipsis`
literals) is accepted only as opaque initialization state and cannot enter solver terms.

The heap/transitive identities advance to v53/v47. Exact pinned `issues/00266_2.py` and the
two-provider `test_imports_2.py` now match through their real `resources` modules. The curated gate
contains 74 fixtures, broad scalar/heap union coverage is 73 of 219 fixtures (33.3%), and there are
zero accepted mismatches. The Rust gate contains 673 tests. `SourceImportClosure.lean` models the
provider-before-consumer closure, fail-closed missing/refuted/cyclic dependencies, verified export
membership, and canonical identity retention across re-exports; filesystem discovery and Python
AST correspondence remain explicit frontend premises. Its 19 constructive theorems bring the
formal tree to 526 theorem/lemma declarations without proof holes.

Version 56 adds three independently checked production/conformance slices. The scalar verifier now
models a nonempty finite dictionary literal and its zero-argument `keys()` result without
conflating that result with a `List`. Keys are statically typed, Boolean keys use Python's integer
key equivalence, duplicate keys keep their first insertion position and last value, and the
insertion-ordered view supports length, iteration, and membership. Indexing or slicing that view,
dynamic hashes, mutation, unpacking, and heterogeneous unsupported sorts refuse. The scalar,
checked-external scalar, transitive scalar, and scalar VC identities advance to v27, v17, v21,
and v18 respectively.

Pinned heap conformance now resolves explicit relative `from` imports against the importing
package, verifies the resulting provider graph with the same root, symlink, package-initializer,
cycle, and canonical-identity gates as absolute imports, and refuses beyond-top-level traversal.
Completed provider calls during module initialization remain modular: consumers receive proved
contracts rather than re-executing provider bodies as if they were local. Module-level assertions
become obligations. Heap and transitive heap identities advance to v54/v48. Conformance annotation
parsing also distinguishes backend-qualified `ExpectedOutput(carbon|silicon)(...)` entries from
backend-neutral requirements instead of treating a backend name as a diagnostic code.

The exact new targets are `issues/00049.py`, `issues/00252.py`, and `test_relative_import.py` plus
its two providers. The curated gate contains 79 fixtures; broad scalar/heap union coverage is 76 of
219 fixtures (34.7%) with zero accepted mismatches. The Rust gate contains 682 tests.
`FiniteDictKeys.lean` contributes eight constructive theorems about normalized keys, duplicate
insertion, ordered views, and unsupported indexing/slicing; frontend parsing and Rust-to-Lean
refinement remain explicit premises. `SourceImportClosure.lean` adds thirteen relative-resolution,
escape/missing/cycle, canonical-identity, and backend-expectation-filter theorems. The full formal
tree now contains 547 theorem/lemma declarations without proof holes.

Version 57 closes the exact pinned `test_operators.py` heap-expression slice. Direct integer field
`+=`, `-=`, and `*=` evaluate the receiver once, require read permission and full write permission,
and advance the heap only after those obligations discharge. Effectful conditional expressions
evaluate only the selected branch and preserve that branch's heap, mask, and obligations. Boolean
`and`/`or` short-circuit selected source calls; value-returning integer/mixed short-circuit forms
remain refusals. A local module heap-function summary is reusable only after its source declaration
has been proved, for one nominal receiver, normal-only execution, and effect-free remaining
arguments. Scalar `Old(receiver.field)` is rebound to the call-entry heap. Positive-literal modulo
uses Python floor-division semantics, including negative dividends; unsupported divisors refuse.

The heap/transitive identities advance to v55/v49; the scalar and VC identities do not change.
Exact `test_operators.py` matches all five pinned diagnostics. Broad scalar/heap union coverage is
77 of 219 fixtures (35.2%) with zero accepted mismatches, and the Rust gate contains 698 tests.
`ModuleHeapOperators.lean` adds fifteen constructive theorems for permissions, state transitions,
selected-branch effects, summary/refusal gates, scalar old-state rebinding, short-circuiting, and
positive-literal modulo. The formal tree contains 574 theorem/lemma declarations with no holes.
Python/frontend correspondence and Rust-to-Lean refinement remain explicit unproved obligations.

Version 58 adds the exact pinned single-generator collection-comprehension slice. The scalar
frontend accepts one synchronous direct-name generator over a homogeneous builtin list, with at
most one pure total filter and pure total mapper/key/value expressions. Lists retain source order
and duplicates. Sets expose deduplicated membership and bounded cardinality. Dictionaries retain
first key order and last-write-wins values; concrete Boolean/integer keys follow Python's shared
key identity. Missing dictionary lookup remains a proved application-precondition failure rather
than an invented value. Multiple or asynchronous generators, destructuring targets, nested
comprehensions, effectful/custom iteration, mutation, unsupported result sorts, and unsupported
key semantics refuse.

The scalar, checked-external scalar, transitive/combined scalar, and scalar VC identities advance
to v28, v18, v22, and v19 respectively. Heap remains v55 with transitive/combined heap v49. Exact
`test_list_comprehension.py`, `test_list_comprehension_filter.py`,
`test_dict_comprehension.py`, and `test_set_comprehension.py` match all 16 pinned diagnostics. The
curated gate is 83/83; broad scalar/heap union coverage is 81/219 (37.0%) with zero accepted
mismatches; and the Rust gate is 716/716. `CollectionComprehensions.lean` adds 35 constructive
theorem/lemma declarations for the finite comprehension algebra and refusal gates, bringing the
formal tree to 609 declarations with zero `sorry`, `admit`, or `axiom`. These results do not prove
Python/frontend correspondence or Rust-to-Lean implementation refinement; end-to-end refinement
coverage remains 0%.

Version 59 replaces frontend-local call matching on scalar source calls and heap direct-name
ordinary-method receivers (including the class-qualified adapter) with the shared
`python-call-argument-binding/v1` Rust kernel. It binds positional-only,
positional-or-keyword, keyword-only, defaulted, `*args`, and `**kwargs` formals into one canonical
environment. Fixed tuple stars expand in source order and a bound receiver is injected exactly
once before explicit arguments. Unknown-length `*` iterables and every `**mapping` expansion remain
fail-closed. Scalar `**kwargs` proof variables use independent stable symbolic key sequences and
value arrays; lookup still requires the frontend's explicit membership/`KeyError` guard.

The kernel capability does not claim that every user-call adapter has been ported. Imported scalar
calls, module predicates, the heap module-function adapter, base constructors, and ordinary
constructors remain restricted/manual seams (or refuse v59 argument syntax) and are explicit
completeness backlog. Arbitrary effectful receiver expressions and receiver chains still fail
closed and are not covered by v59 receiver injection.

The scalar, checked-external scalar, transitive/combined scalar, heap,
transitive/combined heap, and VC identities advance to v29, v19, v23, v56, v50, and
`maledictus-scalar-vc/v21`, respectively. The shared binder is part of the verifier kernel source
digest. `CallArgumentBinding.lean` proves the finite binding algebra from supplied signatures and
typed actuals; Python AST correspondence and Rust-to-Lean refinement remain unproved.

The v59 release gate passes 45/45 curated scalar fixtures and 42/42 curated heap fixtures. Broad
scalar/heap union coverage is 85/219 fixtures (38.8%) with zero accepted mismatches. All 759 Rust
tests pass. The complete Lean build checks 631 theorem/lemma declarations, including 22 in
`CallArgumentBinding.lean`, with zero `sorry`, `admit`, or `axiom`. These Lean results prove the
formal models from their premises; machine-checked Rust-to-Lean implementation refinement remains
0%.

After v59, the production binder identity advances to `python-call-argument-binding/v3`. It rejects
more than 4096 source-plus-expanded arguments with a typed error during a no-clone preflight. This
is a resource-safety semantic change, so v1 and v2 are not certificate-interchangeable. The small
86-case regression corpus remains separately identified and does not establish universal
implementation refinement.

That original v3 release record is historical. The current v3 implementation removes the policy
ceiling, uses checked machine-size arithmetic, and makes allocation failure a typed outcome with
the exact allocation site and requested size. Its cap-free public refinement theorem remains an
open proof obligation.

The accumulated post-v59 frontend work advances direct scalar to v32,
transitive/combined scalar to v26, direct heap to v60, and transitive/combined heap to v54. It adds path-sensitive conditional definedness, static
sequence slicing/index obligations, quoted constructor fields, exact strings, fixed Tuple
returns, and ordered structural matching over scalar value/singleton patterns, captures,
wildcards, OR/AS patterns, guards, canonical zero-argument `int()`/`bool()` class patterns, and
permission-checked qualified scalar value patterns. Sequence, mapping, starred, argument-bearing
class, shadowed-class, and other unmodeled pattern forms refuse before proof issuance. Reusing the
older identities for these semantics would make source-bound certificates ambiguous, so every
affected fragment advances together. Static string slices
are evaluated by Python code-point semantics for literal/static strings, including omitted,
negative, clipped, and positive/negative-step bounds; symbolic strings, dynamic bounds, zero
steps, and string indexing remain explicit refusal boundaries.
The finite-list mutation slice permits static in-range element stores and canonical unshadowed
`list.append` only for function-local, source-owned homogeneous lists with no direct or
transitively nested alias. It updates exact contents, length, indexing, and membership; dynamic
indices, slices, symbolic lists, aliases, incompatible elements, custom dispatch, and invalid
arity refuse. Canonical unshadowed `int.__add__` uses Python integer semantics. This raises the
broad classifier to 96/618 exact matches (15.5%), with 522 refusals and zero mismatches.
The scalar v33 line additionally verifies invariant-driven iteration over immutable symbolic
`List[T]` values, including nested loops, by checking invariant establishment and preservation for
an arbitrary in-domain element and retaining the invariant at natural exit. Iterable mutation or
alias escape, abrupt or exceptional body completion, `Previous`, and reads of a possibly unbound
post-loop target remain fail-closed. That slice raised broad coverage to 97/618 exact matches.
The protected module-metadata slice seeds immutable verifier-owned `__name__` and `__file__`
identities for entry and imported source modules, refuses uncertain module roles, and diagnoses
rebinding as an assignment-permission failure. Verified side-effect-only providers may be imported
without exporting their protected metadata. Canonical bounded dataclasses add typed generated
constructors, literal defaults, `field(default_factory=list)`, and frozen-write protection. The
source-local alias slice additionally resolves ordered immutable class and supported collection
annotation aliases, including one closed `List[int]` specialization of a one-`TypeVar` generic.
Reassignment, forward/cyclic/dynamic aliases, unions, nested or multiple specializations, and
runtime escape remain fail-closed. The pre-IntEnum gate reached 107/618 exact semantic matches
(17.3%). The bounded direct IntEnum tranche adds two exact semantic fixtures for 109/618. The
finite module-list mutation tranche adds one fully semantic fixture for 110/618; 26 separate exact
production-typecheck rejections are reported but are not counted as semantic proofs. The report
also retains 22 typecheck divergences, 460 refusals, and zero semantic mismatches. IntEnum retains
separate numeric projection and full-descriptor singleton identity, and its Lean algebra is not
claimed as Rust/frontend refinement. These exact categories reconcile to all 618 pinned fixtures.
The subsequent direct-heap v66 dataclass-defaults tranche adds exact
`test_dataclass_defaults.py`, including its five expected refutations. Its finite runtime heap
distinguishes factory-fresh list allocations from explicitly aliased list arguments and preserves
IntEnum-valued defaults. This raises semantic coverage to 111/618, reduces refusals to 459, and
retains zero semantic mismatches. The accompanying Lean allocation/default/alias algebra is
constructive only; it is not counted as Rust/frontend implementation-refinement coverage.
Direct-heap v67 adds a source-general, binding-aware contract-position gate after strict mypy and
before proof lowering. It exactly classifies 20 pinned malformed-contract fixtures whose sources
pass the production typechecker; four additional malformed fixtures remain typechecker-first
refusals and are not relabeled. The new source-wellformedness category is disjoint from semantic
proof and production-typecheck parity, so this tranche does not inflate semantic coverage. The
validator also locates all 24 malformed ASTs, preserves legal fractional permissions, global
Fold/Unfold ghost actions, SIF loop invariants, and ordinary shadowed callables, and returns zero
mismatches on the pinned functional, SIF, and obligations classifier roots. Its Lean context/order
algebra is constructive and model-only; Rust/frontend correspondence remains unproved.
Direct-heap v68 adds source-nominal `Optional[T]` module-function boundaries and bounded symbolic
typed-List return loops. Optional ingress remains nullable until a selected `is not None` path
narrows it, Optional fallthrough is the real implicit `None` result, and nonoptional nominal
fallthrough remains a refuted obligation. Symbolic List loops require explicit
`Acc(list_pred(items))`, retain independent exhaustion and arbitrary-element early-return exits,
and refuse effects or summaries that need induction. This adds exact `test_optional_types.py` and
`test_default_return.py` while the Lean null/loop-exit algebra remains explicitly model-only.
The source-wellformedness gate also closes the canonical inline/opaque declaration family:
incompatible `Inline`/`Pure`/`Predicate` combinations, `Opaque` without `Pure`, inline
constructors, modular contracts in inline functions, and overrides crossing an inline boundary.
Alias resolution and transitive source inheritance are structural; shadowed decorator spellings
remain ordinary Python values. Eight pinned translation fixtures match across scalar, heap, and
reference conformance without being relabeled as semantic proofs.
The source gate additionally rejects function/class-local imports, runtime local aliases made from
canonical `typing` constructors, and malformed canonical `@Pure` declarations. Pure functions may
not return `None`, declare or directly raise exceptions, omit every reachable return, or contain
statically dead statements after an unconditional exit. Alias and rebinding decisions remain
source ordered. Where strict mypy independently reports the same missing-return defect, that
diagnostic is retained as evidence while the more specific source-declaration result is reported;
no type-invalid source proceeds to proof lowering.

Any source class whose fields or effects enter that heap model or an exported heap summary must
first have a complete effective MRO ending at `object`. Source entries must prove no direct or
inherited `__getattribute__`, `__getattr__`, or `__setattr__` override and no
`__init_subclass__` class-creation mutation. Checked-external entries
instead retain an explicit hash-bound `checkedExternalHookFree` provider-conformance assumption
after the ContractOnly parser rejects declared hooks and `__init_subclass__`; they never become source proof. Dynamic or
unchecked interception refuses before
ordinary heap reads/writes can become evidence. Scalar-only classes outside heap modeling are not
rejected by this gate. Lean models only the finite frontend-supplied MRO/refusal premise, not
Python MRO extraction, provider conformance, or execution.
Version 17 requires source-ordered module constructor, typed virtual-dispatch, annotation
definedness, static-method receiver/override obligations, and class-qualified static dispatch
edges to prove before the module can export a summary. Version 18 additionally carries the v24
class-object and classmethod obligations through recursively proved source modules. Version 19
also carries the v26 predicate summaries, Fold/Unfold exchanges, inherited constants, and dynamic
class-receiver calls.
Version 21 carries the v27 fail-closed modular predicate boundary across source imports; imported
predicate identities remain provider-qualified, but predicate ownership is not transferred by a
method or constructor summary except for a folded predicate on a proved fresh construction result.
Version 22 carries the v28 exact-nominal constructor-field slice only after the complete
source-owned constructor dependency graph proves acyclic; no external, directly or transitively
exceptional, or custom-`__new__`-controlled edge is silently summarized as a fresh source result.
Version 23 carries v29 pure contextual conjunctions through proved source contracts; it adds no
permission, effect, truthiness, or short-circuit assumption at an import boundary.
Version 24 carries v30 nominal field-chain/direct-property return metadata through proved source summaries. It
preserves the non-optional value class and source subtype check without treating dynamic,
unresolved, optional, or unchecked external member access as verified; the combined external
variant retains checked-provider assumptions explicitly.
Version 25 carries v31 direct reference-field `Old` identities only from proved source summaries
whose complete transitive modification set excludes the field. Consumers rebind entry/exit heap
and mask versions per call; external `Old` contracts remain outside the checked-external fragment.
Version 26 carries v32 direct result/current-field identity or nonidentity only from a source provider that
proved the exact nominal/reference type, exit permission, unique terminal normal return, and
returned-reference equality. Each consumer rebinds result, receiver, exit heap, and exit mask. The
combined external variant does not turn an external contract-only postcondition into source-proved
provenance.
Version 27 carries v33 canonical late-bound class dependencies only from a proved, completely
initialized source provider. Local call sites still use their exact class prefix. Imported
dependencies retain provider-qualified identity; the combined external variant does not turn an
unchecked provider into a source-definedness proof. Provider-qualified transitive shapes travel
in a private layout catalog for downstream field/signature/base resolution and do not become
public imports of an intermediate module.
Version 28 carries v34 composed reference-chain metadata only from proved source members. It
preserves direct-field result provenance, exact non-optional nominal types, provider identity,
permission effects, and complete modification sets across the import edge. Checked-external or
external-inherited fields and methods remain ineligible for source-proved chain hops, including
when a source method wraps an inherited external field.
Version 29 carries v35's identity-sufficient positive reference-equality assertion rule only after
the provider establishes exact source-construction provenance for the named left local, complete
left source MRO with no `__eq__` override, and a current permission-checked raw-field or name
operand on the right whose every field receiver has normal-only source-allocation provenance,
exact source runtime class, and
ordinary attribute resolution. The current assumptions must already prove identity before the assertion is
lowered, and every prior call/permission/transition obligation must already be proved; false or
unknown identity refuses, and no source summary claims a refutation of general
Python equality or reverse dispatch. Calls or state changes in the ghost expression, custom/external/
dynamic equality, effective `__getattribute__`/`__getattr__`/`__setattr__` interception,
non-exact left values or field receivers,
properties, `!=`, negation, and contract-clause equality
remain refusals. The combined external variant retains provider assumptions but cannot use them as
v35 equality provenance. Lean formalizes only the typed IR/premise and refusal algebra, not Python
equality or frontend correspondence.
Version 30 carries v36's independently exact right-hand reference-equality evidence across a
proved source edge while deliberately preserving the asymmetric syntax: the left is still the
named exact source construction, and only the right may be a name or raw field chain. Both exact
runtime source classes and complete source/object MROs without any `__eq__` or `__init_subclass__`
binding must survive
canonical export; every right-hand raw-field receiver keeps its current permission, exact-class,
normal-allocation, and hook-free premises. This permits the identity VC to prove, refute, or remain
unknown without approximating Python reverse dispatch. The v35 identity-sufficient fallback is
unchanged for a right operand lacking independent exactness. General left chains and external,
custom, dynamic, property, call, optional, scalar, `!=`, negated, or contract-clause equality remain
refusals. The combined checked-external variant cannot turn a provider assumption into exact source
allocation/MRO evidence. Lean models only the typed IR and frontend-supplied premises, not Python or
import correspondence.
Version 31 carries v37's module-heap-function standalone nested one-argument call only from proved source receiver,
argument, and terminal members. The receiver chain runs first, the argument chain runs from its exit
heap/mask, and the Unit terminal summary is rebound once to the two saved caller terms at the
post-argument state. Complete permission effects, modification sets/frames, normal-only control
flow, exact source member origin, and the one required non-optional nominal-reference parameter are
preserved across source imports. Aliasing is passed to the ordinary alias-sensitive summary rule;
it is never replaced with distinctness. External/dynamic/property/optional/scalar chains,
exceptional terminals, keyword/default/multiple arguments, non-Unit results, class/method-body use,
and ghost uses refuse.
The combined checked-external variant cannot manufacture source provenance for this slice. Lean
models only the ordered IR transition and frontend premises, not Python/import correspondence,
alias analysis, exception freedom, or summary truth.
A following raw-field-left reference `==` remains outside v37 and refuses separately.
Version 32 carries v38's complete normal summary/transitive-modification metadata and canonical
source provenance. At a consumer, only direct typed fields from a finite verified-source caller-root
inventory may be framed, and only when the field name is absent from the complete transitive
modified set. This is conservative under aliasing and adds no distinctness assumption. A modified,
external, dynamic, unresolved, exceptional, or incomplete request refuses without extending prior
frame facts. Caller roots themselves are local and are never invented by an imported summary.

V38 separately accepts positive `raw_source_field_chain == exact_source_name` only after every left
receiver hop proves current permission, exact normal source class, and a complete hook-free MRO; the
right name proves exact source construction and a clean equality MRO; and current assumptions
already prove identity. It is deliberately not a symmetric/general equality rule and cannot refute
nonidentity. The combined checked-external variant cannot convert assumptions into source frame or
equality provenance. Lean models finite IR construction/refusal from supplied premises, not Python,
frontend, import, alias, semantic-frame, modification-completeness, or equality correspondence.
Version 33 carries v39's dedicated source reference-identity summary through proved source edges.
The summary preserves exact `@Pure`, the one required non-optional canonical source-nominal `T`
parameter and identical return, exact `return parameter`, total normal completion, neutrality, and
source binding. `Pure` must be the canonical imported Nagini binding, not a shadow with the same
name. Local consumers require the exact call-time callable/class prefix; imported
consumers require the canonical provider to have completed initialization. Applying the summary
after the wrapped argument chain preserves that chain's exact term, actual nominal provenance,
heap, mask, assumptions, and obligations before the outer Unit method. Malformed, shadowed,
unavailable, external, optional/default/keyword, nested, ghost, or arbitrary pure-call uses refuse.
The checked-external combination cannot promote an external contract into this source summary.
Lean models only sealed-summary, availability, neutral-transition, and refusal algebra from supplied
premises, not Python/frontend/import correspondence, totality, canonicalization, or provider truth.
V39 additionally uses canonical source exact-constructor field metadata for a finite conditional
frame: after a complete normal source instance summary proves all supported direct/transitive
writes receiver-local, a one-hop caller-local candidate proved exact, plain, hook-free, source-owned,
and distinct from that receiver retains all of its effective source fields across the heap change,
including same-named fields. The saved pre-heap candidate is framed; the rule does not grant
permission or establish that the caller root still reaches it. Alias, unknown aliasing, incomplete
effects/exactness, checked-external, and dynamic cases add no such fact, leaving the conservative
v38 name-based frame in force. Lean models only premise-driven IR construction, not frontend
enumeration, constructor freshness, alias/effect proofs, Python execution, or semantic framing.
Version 34 carries v40's raw-left/exact-name-right bilateral equality evidence only from proved
source metadata. The final raw reference—not merely its nominal annotation—must preserve exact
runtime source class, verified allocator, normal-only constructor, and complete clean source/object
MRO in addition to every current permission/exact/plain receiver-hop fact. The right remains a
normally completed exact source name with its own clean MRO. This lets the identity VC be proved,
refuted, or unresolved while preserving v38's identity-only fallback when final-left exactness is
missing. The combined checked-external variant cannot manufacture these source facts. Lean models
only typed lowering and solver disposition from supplied premises, not Python/import/frontend
correspondence or evidence truth.
Version 35 carries v41's canonical validated nominal/subtype and method-kind metadata through proved
source edges. Typed heap conditional expressions remain consumer-local `ite` values: equal scalar,
localized Boolean-to-integer, same/catalog-subtype nominal, and nominal/`None` joins are
branch-read-free and do not change heap, mask,
permissions, non-nullness, or exact runtime provenance. An optional receiver must separately
prove non-null before an imported source method's permission/effect summary applies; ordinary and
pure calls retain their distinct Nagini diagnostics. Effectful/incompatible/dynamic/unchecked joins
refuse. A hash-bound checked-external catalog type may participate in an effect-free join, but the
combined variant cannot manufacture source provenance or receiver-call evidence. Lean
models only this finite premise/transition algebra, not Python/import/frontend correspondence.
Statement-level heap `if`/`else` control flow is not part of v41/v35.
Version 36 carries v42's canonical type-catalog metadata for the first statement-level `if`/`else`
slice. Read-free Boolean conditions split path assumptions; `pass`, scalar assertions, typed local
assignments, simple initialized `int`/`bool` local annotations, and nested conditionals execute with
unchanged heap/mask and normal exits. Annotated initializers are checked exactly except for the
localized Boolean-to-integer coercion. Joins cover
definitely bound equal scalar, localized Boolean/integer, same/catalog-subtype nominal, and
validated-nominal/`None` values. Hash-bound checked-external types may participate in this
effect-free join, but unchecked/dynamic types, sibling LUB inference, calls, heap/permission
effects, contracts, returns, and exceptions refuse. Exact/source-construction provenance remains
source-only and survives only an identical term and class on both paths. Lean models the finite
split/join algebra from supplied premises, not Python/import/frontend correspondence or evidence
truth.
Version 37 carries v43's bounded guarded-state semantics through source consumers without exporting
consumer-local paths. From the first return-containing conditional through the remaining body, up
to 64 total normal/returned states retain independent heap and mask
versions under read-free Boolean guards. The v42-pure branch grammar gains typed early returns for
`None`, `bool`, and `int` (including the localized `bool`-to-`int` promotion); each returned path checks postconditions independently and skips
continuation. Unit fallthrough is implicit, reachable non-Unit fallthrough refuses, and overflow
fails closed. Nominal/optional returns, calls, constructors, heap/permission effects, exceptional
exits, and branch contracts remain outside v43. Lean models only finite guarded-path/return algebra
from supplied premises, not Python/import/frontend correspondence or evidence truth.
Version 38 carries v44's verified source-effect metadata into consumer-local guarded paths.
Conditionals containing a supported normal-only source constructor local assignment, source
instance-method result assignment, zero-argument Unit source-method statement, or direct
typed-local plain source-field write activate the 64-state path engine even without an early return.
Every normal path uses the ordinary statement transition and keeps its own heap/mask, obligations,
and continuation; returned paths skip it. Direct field writes require non-nullness, full permission,
and exact scalar or proved nominal/optional compatibility. Refuted receiver/call preconditions halt
only their guarded path, retain the failing obligation, roll back its effect state, and count toward
the cap. External/dynamic/descriptor behavior,
exceptional outcomes, predicate ownership transfer, and incompatible or unresolved field types
refuse. Lean models finite activation/transition/nonextension algebra from supplied premises, not
Python/import/frontend correspondence, executor parity, evidence truth, or solver validity.
The authoritative executable v42-v46 semantics is now `formal/Maledictus/HeapControl.lean`, which
constructs recursive branch paths and typed state transitions and binds postconditions at function
finalization. The older `HeapStatementBranchTrace`, `GuardedHeapBranchResult`, and
`GuardedPathLocalSourceEffectRequest` witness APIs were removed rather than retained as
theorem-shaped adapters. Constructive join/type utilities in `HeapCallable.lean` remain part of the
authoritative algebra. Python/frontend correspondence and
the truth of source-summary, permission, subtype, and solver premises remain separate obligations.
Version 45 behavior extends the authoritative `HeapControl` engine with opaque nullable `object`
parameters; canonical source-safe `isinstance(Name, SourceClass)` splitting; true-only nonoptional
nominal narrowing with false-path and same-term join restoration; catalog-resolved direct raw-field
returns under the exact current-mask read VC; and read-free `bool`/`int` conditional expressions.
Lean checks a finite direct-base/field catalog for duplicates, unresolved edges, and cycles and
computes subtype reachability/inherited fields itself. Opaque member access, arbitrary subtype or
field tables, external/dynamic/metaclass/`__instancecheck__` behavior, compound conditions, and
Reference/Class/effectful IfExp branches refuse. A refuted raw-read prerequisite halts only its
guarded path. That v45 release advertised direct heap version 45 and transitive/combined
source-heap version 39.
Version 46 adds executable left-to-right short-circuit `and`/`or`: only feasible left-true paths
evaluate the right side of `and`, and only feasible left-false paths evaluate the right side of
`or`, so skipped operands create no call or proof obligations. The narrow atom set is canonical
source-safe `isinstance`, scalar comparisons, and verified source-pure scalar method calls selected
from the checked catalog. Dispatch closes only for exact or source-constructed receivers; an open,
nonexact annotated ingress value remains unmodeled/refused instead of acquiring a sealed-world
assumption. Any concrete refuted modeled exit wins over unmodeled siblings, while an unmodeled
sibling blocks proof when no refutation exists. Reachable non-Unit fallthrough is retained as the
actual implicit-`None` exit and checked under its unique guard at the function line. Obligations
remain path-scoped and are emitted once per evaluated call or actual exit. Lean constructs these
short-circuit, dispatch, fallthrough, and final-disposition transitions; frontend correspondence,
catalog truth/completeness, and proof-kernel dispositions remain premises. That release advertised
direct heap version 46 and transitive/combined source-heap version 40.
Version 47 adds structural unary `not` over every supported statement-condition partition by swapping its
feasible true and false exits after evaluating the operand once. This preserves path-local calls,
permissions, halted/unmodeled states, and the logically corresponding `isinstance` narrowing.
Read-free `bool`/`int` chained statement comparisons lower each operand once and conjoin adjacent
comparisons in source order. Calls, heap reads, reference/class operands, and custom comparison
dispatch in a chain remain fail-closed rather than acquiring eager or sealed-world semantics. The
that release advertised direct heap version 47 and transitive/combined source-heap version 41.
Version 3 permits a proved source module to derive a single-inheritance class from an imported
verified source class, carrying its inherited layout, constructor, methods, and override
obligations across the module edge. Thus constructor-produced field permissions can discharge an
imported field-permission method precondition; a refuted
provider exports no heap summary. Version 4 retains source nominal method parameters and returns,
checks subtype arguments, and proves contravariant-parameter/covariant-return overrides across the
source edge when every participating canonical class is explicitly imported.
Version 5 adds source exception/default/permission override metadata. Version 6 makes those
permission-transferring summaries callable: each call advances a versioned mask, applies the exact
declared fractions, proves the resulting mask remains within `[0, 1]`, and exposes the new mask to
later caller obligations. Multiple same-field atoms on one contract side remain a fail-closed
alias-sensitive-sum boundary.
Version 7 preserves field optionality and nominal constructor parameters through source summaries,
including the implicit non-null invariant at normal exit.
Version 8 also preserves verified direct-field property bindings and direct-return pure-method
equations across source imports. Version 9 preserves verified computed getter and direct setter
summaries, including the setter's exact field write and permission-neutral call contract.
Version 10 also preserves each source summary's immutable scalar module environment across imports
and inheritance; an importer cannot substitute its own same-named global values.
Version 11 accepts the same verified passive class declarations and immutable class constants at a
source-module boundary; a module with a located definedness failure exports no class summary.
`checked-external-heap-contracts/v3` accepts the same layout and
effect summary from a hash-bound `@ContractOnly` class stub while recording provider conformance as
an assumption. External calls conservatively invalidate all declared field values because v2 does
not yet model explicit frame clauses. External methods must return exactly the permissions they
require; consuming or producing permission effects remain refused until the caller-mask transfer
rule is implemented.

Direct heap version 71 and transitive/combined heap version 59 add finite source-nominal
`typing.Union` receiver dispatch. The frontend resolves every source-ordered arm, binds the same
once-evaluated actual arguments against every method, preserves each arm's normal postconditions,
and requires neutral nonexceptional effects; Pure callers require all arms to be Pure. A mixed
primitive result is usable only as the matching direct Union return. Missing, incompatible,
dynamic, external, exceptional, effectful, or otherwise unknown arms remain refusals. Exact pinned
issues `00117.py` and `00124.py` exercise the real method-call path rather than a fixture-specific
diagnostic adapter.

The frozen v85 combined classifier reports 257/618 exact fixtures: 122 semantic proofs, 30
production strict-typecheck rejections, and 105 source-wellformedness rejections. Two upstream
unsupported fixtures remain separately superseded, 12 production-typecheck divergences remain
visible, 347 fixtures refuse, and no fixture mismatches. Its report SHA-256 is
`AB8BBA3A494C67552C12128D833B796F9AF2803A384869A51BB24290A2C51EEB`. The subsequent v86 tranche
adds two independently exact builtin-subclass fixtures; a complete current-source sweep remains
required before publishing a higher aggregate. The main Lean aggregate builds 31 jobs. The
cap-free full call-binding and extracted `Term::sort` projects have green supporting checkpoints,
but their public all-input refinement theorems remain open; those checkpoints do not count as
completed implementation refinements.

The current heap/scalar guarded-path implementation supersedes the historical fixed limits
recorded in the Version 49/43, Version 50/44, and transitive Version 37/38 release notes above.
Reusable pure scalar summaries, constructors, heap functions, and ordinary methods now retain the
complete finite path set generated by the source; they do not refuse merely because it contains
more than 64 states. `formal/Maledictus/HeapCallable.lean` and
`formal/Maledictus/HeapControl.lean` model the same cap-free list construction. The historical
entries remain unchanged because they describe the behavior and theorem inventory of those
specific releases.

The v41 scalar and v76 direct-heap frontends, with v64 transitive source-heap variants, also
supersede the former 4096-element materialization policies. Finite scalar loops execute every
lowered element. Constant ranges and byte repetition compute checked cardinalities and use
fallible allocation with typed size-overflow or allocation-failure outcomes; they do not impose a
smaller policy ceiling.

The cumulative post-v87 compatibility release uses scalar v42, direct-reference v4, direct-heap
v76, checked-external scalar/reference/heap v25/v4/v5, transitive scalar/reference/heap
v32/v4/v64, and the corresponding combined identities. It includes source-bound validation of
`MayCreate`, `MaySet`, and `Acc` targets; scalar `enumerate` and global-scope execution; reference
pure predicates; heap `Let`, `Refute`, ranges, dictionary keys, unary operators, truthiness,
`enumerate`, string conversion, ordered module calls, and typed empty-list/zero-iteration behavior;
it also validates canonical IOExists placement and rejects nested existential scopes without
misclassifying shadowed application callables. The heap frontend additionally models symbolic
list slicing with static nonzero bounds and steps; when Maledictus proves a fixture that Nagini
rejected as unsupported, conformance records a semantic supersession rather than an exact match.
Fragment identities live in one source-owned module, are part of the frontend-bundle digest, and
issuance refuses any fragment not advertised for the file's language. The native Windows
current-source sweep at pinned Nagini commit `c2fd68f27db324d110824f607aabfda827e3675a`
reported 314/618 exact fixtures: 131 semantic proofs, 30 production strict-typecheck rejections,
and 153 source-wellformedness rejections. It also reported three semantic supersessions, 12
production-typecheck divergences, one mismatch, and 288 refusals. The retained report SHA-256 is
`8BC4AB195BF10DE8AAB88C6C5CC82C6629EBBEADB38BFCC7612600BD3B48B096`.

The subsequent frozen v120 checkpoint includes the production-path ADT integration for
`test_adt_2.py`, `test_adt_3.py`, and `test_adt_4.py`; the IOExists context correction that removes
the sole false diagnostic for `tests/io/verification/test_builtins.py`; and the concrete persistent
collection algebra for `test_pseq.py`, `test_pset.py`, and `test_pmultiset.py`. A complete
three-lane sweep over all 618 pinned fixtures reports 321 exact matches: 138 semantic proofs, 30
production strict-typecheck rejections, and 153 source-wellformedness rejections. It retains three
semantic supersessions and 12 production-typecheck divergences, with zero mismatches and 282
refusals. The UTF-8 report is retained at `.cache/classification-current-v120.json` with SHA-256
`624CDE305D29BB76DD97873D00C1380D066657A233987FEE49D358DCF55C3D20`.

That report is a measured frozen-source checkpoint, not the current worktree total. It predates the
later type-algebra frontend and its exact `issues/00118.py`, `test_cast.py`, `test_conversion.py`,
`test_tuples.py`, and `test_union_types.py` gates, as well as subsequent proof-enabling internal
refactors. Those gains remain excluded from the aggregate until one complete sweep runs against the
fully integrated source snapshot.

The subsequent source-wellformedness tranche resolves final, unambiguous class and method bindings,
constructs the real class-qualified source-call graph, and rejects the earliest call edge entering
a strongly connected component as `invalid.program:recursive.static.call`. Module, class-body, and
lexical rebinding prevent an edge from being invented. The graph pass uses iterative linear-space
strong-component traversal rather than recursive inlining or repeated path searches. Its focused
gate exactly matches pinned `tests/functional/translation/test_static_call_1.py`; this additional
gain is likewise excluded from the aggregate until the next complete current-source sweep.

The next source-wellformedness tranche implements Python private-field access without treating a
double-underscore spelling as proof by itself. Final source class/method bindings establish fields
written through an ordinary method receiver; explicit source annotations, ordinary method
receivers, direct unreassigned source constructors, and the closed single-inheritance chain then
establish the field owner at each access. Access outside that owner is rejected as
`invalid.program:private.field.access`. Reassigned or unknown receivers, shadowed constructors,
dynamic hierarchies, and protocol names ending in `__` remain outside this preflight. The focused
gate exactly matches pinned `tests/functional/translation/test_fields.py`; this gain also awaits the
complete current-source sweep before inclusion in the aggregate.

## M3: JavaScript and TypeScript

- Add ECMAScript and TypeScript frontends over the same language-neutral effect kernel.
- Model throws, rejected promises, callbacks, and property access using JavaScript-specific rules.
- Verify cross-language boundaries rather than treating Python and JavaScript as unrelated files.

The current TypeScript slice is `strict-typescript-closed-total-functions/v11`. It delegates parsing
and strict static typing to pinned TypeScript 5.9.3, then proves closed primitive functions with
immutable primitive locals, blocks, `if` branches, and multiple returns. The sibling
`strict-javascript-jsdoc-closed-total-functions/v11` uses the same pinned compiler in
`allowJs`/`checkJs` mode and requires explicit JSDoc parameter and return types. Direct calls to
compiler-resolved source functions are accepted only when every callee body is in the closed module
and the complete call graph is acyclic. External/indirect calls, mutation, loops, and every other
unmodeled effect refuse. Version 4 includes readonly primitive arrays, fixed readonly
primitive tuples, and source-owned `const` primitive array literals. Only `.length` and numeric
indexing are modeled; potentially absent indexed values require compiler-visible `??` handling
under `noUncheckedIndexedAccess`. Mutation, collection methods, spread, destructuring, complex
element types, and noncanonical properties refuse. Version 5 derives finite outcomes for explicit
primitive throws, branches, sequences, catch-all `try/catch`, and acyclic source calls. Rust
recomputes the requested roots' boundary outcomes from the compiler bridge's typed graph; uncaught
throws refuse at their throw or propagating call site. Complex thrown values, catch-binding use,
callbacks, async code, and external effects remain outside the fragment.
Version 6 adds flat primitive source `const` records, exact readonly TS record declarations, and a
bounded private-helper seam. The source-bound compiler bridge establishes and serializes typed
parameters plus exact source-literal argument provenance; Rust validates the tag and recomputes
compatibility. Requested/exported structural
record parameters, getters, proxies, mutation, escape, forwarding, dynamic access, and complex
field types remain refused.
Version 7 adds exhaustive terminal primitive `switch` statements. The source-bound bridge requires
a once-evaluated primitive discriminant, unique same-typed literal labels, one final `default`, and
terminal modeled exits in every arm; Rust validates the schema-v4 node and recomputes the composed
exits. Fallthrough, `break`, dynamic labels, and post-switch continuation remain refused.
Version 8 adds catch-plus-finally and finally-only outcome composition. Rust validates the new
schema-v5 graph and recomputes ECMAScript completion precedence: a falling-through finalizer
preserves the protected completion, while a finalizer return or throw replaces it.
Version 9 adds nongeneric primitive-signature callbacks whose concrete arguments resolve to
top-level functions in the same compiler-bound source module. The compiler bridge emits explicit
callback descriptors, source-provenance arguments, and callback-invocation graph nodes; Rust
independently substitutes the concrete callback identity, composes every return/raise outcome, and
includes callback edges in cycle detection. Requested or exported callback boundaries, callback
forwarding or escape, closures, methods, overloads, generics, optional/rest parameters, async
callbacks, and external callback values remain fail-closed rather than being assumed total. The
focused and adjacent callback gate is 83/83.
Version 10 adds exact primitive `Promise<T>` async functions, direct await and direct promise
adoption, with Rust recomputing fulfillment/rejection propagation. Version 11 adds immutable
same-module source classes with required readonly primitive fields and compiler-resolved direct
constructors, field reads, and methods. Constructor and method graphs use the same call/outcome
composition as functions. Schema v8 binds a canonical ownership catalog which Rust independently
checks. Inheritance, accessors, proxies, mutation, escape, dynamic/external dispatch, overloads,
generics, and optional/rest/default parameters remain refused.
Compiler-package and Node-executable identities are serialized with either proof. General
JavaScript and TypeScript effects remain pending.

## M4: compatibility and formal correspondence

- Run the complete pinned Nagini unit suite through a compatibility harness.
- Classify every difference as supported, deliberately refused, or a defect.
- Prove the complete kernel rules in Lean.
- Add generated correspondence tests between Lean decisions and Rust decisions.

`formal/coverage-tool` now generates a source-hashed, function-level denominator rooted at the
production `verify_internal(..., issuance=true)` entry point. Ambiguous method, trait, macro, or
indirect-call resolution expands the denominator to every non-test production source function; it
can never silently shrink coverage. The artifact distinguishes unconditional source-bound proofs,
conditional source-bound proofs, unproved functions, model-only Lean declarations, external
boundaries, and the missing root-composition theorem. A top-level Rust test and explicit CI tool
gates reject source drift, stale proof manifests, open proof obligations, dirty axiom audits,
unclassified direct dependencies, and stale generated output.

## M5: Dagcert production backend

- Make Maledictus selectable explicitly in Dagcert without changing Maledictus repository ownership.
- Pin the executable and kernel identities in certificates.
- Prohibit silent backend fallback during issuance or verification.
- Add end-to-end positive, negative, tamper, timeout, and unsupported-language tests.

The application-facing source fragment is now `dagcert-closed-typed-operations/v3`: imported
`@operation` functions over frozen dataclass inputs and finite frozen-dataclass outcome unions, with
both `|` and explicitly imported `typing.Union[...]` syntax, total primitive field expressions,
primitive-only f-string interpolation, same-type primitive local reassignment, closed total `float`
arithmetic and comparisons, and path-complete `if` returns. Dagcert now has explicit
alternate-backend selection, independently checks the executable SHA-256, validates the returned
verifier/kernel/frontend identities plus exact source/file/symbol bindings, stores the complete
response in the certificate, and recomputes it during verification. Nagini remains the default and
there is no fallback. Version 3 binds every callable-valued input field to an exact requested source
function or checked external scalar contract, checks its real annotated signature, composes its
finite exception exits through actual handlers, and emits both endpoint hashes. Abstract,
mismatched, aliased, mutated, generic, variadic, async, or uncaught callback paths refuse. Wider
callback bodies, non-scalar callback types, and external callback preconditions remain
production-coverage work.
