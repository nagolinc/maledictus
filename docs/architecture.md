# Architecture

Maledictus is a separate verifier, not a module inside Dagcert. Dagcert is one possible caller.

The verifier is split into four trust layers:

1. A language frontend reads the exact source files, resolves types and imports, and lowers every
   reachable exit to a language-neutral effect graph. Unsupported syntax or unresolved behavior is
   an explicit `Unknown` effect.
2. The Rust kernel checks the effect graph against the requested proof obligation. It never accepts
   an empty or unknown graph as a vacuous proof.
3. Lean models state and prove kernel properties. A proof counts as implementation refinement only
   when Aeneas translates the real production Rust and Lean proves that generated definition
   equivalent to a separate exact model for every value in the stated scope; concrete regression
   cases and model-only theorems are reported separately.
4. The CLI binds the result to source hashes and returns a stable JSON response. It exits zero only
   for `proved`; refusal and tool failure are nonzero.

Python, JavaScript, and TypeScript frontends share the effect graph but retain language-specific
type rules. This avoids pretending that one language's exception and coercion semantics apply to
another.

Pinned Nagini conformance uses the same source-confined mypy 1.5.0 adapter as production Python
issuance. An exact expected static-type rejection is recorded as
`production-typecheck-rejection`, together with the complete typechecker identity and located raw
diagnostics; it is not counted as semantic verification. A missing, extra, differently located, or
differently coded diagnostic is retained as `production-typecheck-divergence`, with both expected
and actual diagnostic sets. Classification reports reconcile semantic matches, exact production
typecheck rejections, explicit typecheck divergences, semantic mismatches, and refusals without
combining those categories into a single proof count.

`maledictus capabilities` exposes universal implementation refinements separately from bounded
cross-model regressions. The first completed refinement is deliberately narrow: production
`call_binding::expand_actual_items` instantiated with String/Int values and total identity Clone
semantics, universally over finite actual-item slices and optional receivers. That proof is now
superseded because it covered the retired bounded implementation. The cap-free full-binder
extraction models checked machine-size arithmetic and typed allocation failures; its public
all-input refinement theorem remains open and therefore does not yet count as implementation-
refinement coverage.

## Current milestone

The protocol, source confinement/hashing, fail-closed kernel, initial Lean rule, and real Python AST
frontend exist. The first provable fragment,
`closed-total-functions+safe-builtin-slices/v1`, consists of fully annotated undecorated functions
that return a parameter, primitive literal, or builtin `list`/`str` slice with safe bounds and a
statically nonzero step. Dynamic or zero steps refuse because they may or certainly raise
`ValueError`. All other Python is refused. The frontend extracts callable-valued dataclass fields
without crashing, but complete call-effect analysis is still in progress.

The `strict-typescript-closed-total-functions/v11` and
`strict-javascript-jsdoc-closed-total-functions/v11` fragments invoke pinned TypeScript 5.9.3 in
strict, no-emit mode. JavaScript uses the compiler's `allowJs` plus `checkJs` path and requires
explicit JSDoc parameter and return types; TypeScript requires source annotations. Maledictus does
not reimplement either static type checker. Both effect proofs accept non-generic top-level
functions over primitive parameters, compiler-resolved immutable primitive locals, lexical blocks,
`if` branches, multiple primitive returns, and direct calls to other verified functions in the same
file. The compiler resolves every callee symbol and checks arguments/results; Maledictus constructs
the call graph and rejects every recursive cycle before composing call outcomes. Version
4 added readonly homogeneous arrays of one primitive element type, fixed readonly primitive
tuples, and source-owned `const` primitive array literals. Collections expose only canonical
`.length` and numeric indexing; a non-fixed index is admitted only when TypeScript's
`noUncheckedIndexedAccess` result includes `undefined` and the expression discharges it directly
with `??`. Mutation, methods, spread, destructuring, aliases, nested/object/union/`any` element
types, and noncanonical properties refuse. Version 5 adds explicit primitive `throw` outcomes and
catch-all `try/catch`. The compiler bridge emits a finite typed outcome graph for
returns, raises, branches, sequences, catches, and acyclic source calls; Rust independently derives
each requested root's boundary exits. Catch bindings are opaque and unused. Uncaught outcomes are
located refusals, while callbacks, async code, external calls, complex thrown values, and other
unmodeled constructs remain refused. Version 6 adds provenance-bound flat source `const`
records containing primitive fields. Exact readonly TypeScript interfaces/type literals and
private checkJs helpers may consume those records;
the bridge carries typed formal parameters and source-literal argument provenance, which Rust
revalidates. Structural record parameters at requested/exported boundaries, accessors, mutation,
escape, forwarding, computed reads, spreads, and nested or optional fields refuse. The executed
compiler bridge must byte-match the source-bound bridge compiled into Maledictus; the response also
binds the complete compiler package and Node executable identities for either language.
For every requested JavaScript/TypeScript symbol, the issuance response also returns a
`verified_interfaces` row derived from that same compiler descriptor: execution mode, ordered
parameter names/types, and return type. Callers such as Dagcert may compare a contract assertion
with this result, but cannot supply the result or override compiler authority. Python file results
never carry these rows, and a requested symbol without one refuses exact interface binding.
Version 7 adds exhaustive terminal `switch` over primitive values, sealed-record primitive fields,
or verified source-call results. The discriminant is evaluated once before the selected arm;
case labels are unique same-typed literals; exactly one final `default` is required; and every arm
must terminate with a modeled return or raise. Fallthrough, `break`, continuation after the switch,
dynamic labels, and other control flow remain refused. Rust validates the typed terminal-switch
node and independently recomputes its exits. These typed descriptors, call arguments, and switch
nodes are required fields in compiler-response schema v4. Version 8 composes `finally` over the
complete protected outcome union. A falling-through `finally` preserves each prior return, raise,
or fallthrough; an abrupt return or raise from `finally` overrides it, matching ECMAScript control
flow. Both catch-plus-finally and finally-only statements are represented explicitly, and Rust
recomputes their boundary exits from compiler-response schema v5.
Version 9 admits source-owned callbacks at a deliberately closed private-helper seam. Callback
formals have exact nongeneric primitive signatures, and every actual callback must resolve through
the compiler to a top-level function in the same verified module. Schema v6 represents callback
formals, source-function provenance, and callback invocation explicitly. Rust revalidates the
source function signature, substitutes callback provenance into the helper graph, composes every
return and primitive-raise outcome, and rejects cycles introduced through callback edges.
Requested or exported abstract callback boundaries, external callbacks, closures, methods,
callback escape or mutation, higher-order forwarding, and async callbacks remain refused.
Version 10 adds closed same-module async functions over exact primitive `Promise<T>` fulfillment
types. Schema v7 distinguishes synchronous calls, direct `await` calls, and direct promise adoption
by `return sourceAsync(...)`. Rust independently recomputes fulfillment and rejection: an awaited
rejection becomes a catchable throw at the await site, while an adopted rejection bypasses the
caller's synchronous `catch` and remains a rejected promise. Every async call edge participates in
cycle detection. Unknown or external thenables, floating promises, promise combinators and races,
dynamic dispatch, mutable captured state, and async callbacks remain refused. The mixed-language
v1 boundary remains synchronous and cannot relabel a promise as a total Python return.
Version 11 adds closed same-module source classes as immutable symbolic records with behavior.
Every class has required readonly primitive fields, one exact primitive constructor signature,
and final compiler-resolved direct methods. Constructor field writes occur exactly once at the
start of construction; later mutation and pre-initialization `this` reads refuse. Constructor and
method bodies are ordinary nodes in the same acyclic typed outcome graph, so synchronous
return/raise and asynchronous fulfill/reject outcomes compose at real call sites. Schema v8 binds
the canonical class, constructor, field, and method catalog for independent Rust validation.
Inheritance, accessors, proxies, aliases, mutation, instance escape, dynamic or external dispatch,
overloads, generics, and optional/rest/default parameters remain fail-closed.

The separate `python-to-js-primitive-total/v1` fragment composes one explicit source-bound Python
call edge with one requested TypeScript or checkJs export. The TypeScript compiler descriptor is
the signature authority; request-declared types are checked assertions only. Maledictus generates
the corresponding exact Python interface for strict mypy, proves the caller's real direct call
through the scalar import binder, and accepts the provider only as part of that composed edge.
Version 1 is limited to `bool`/`boolean`, `str`/`string`, and `None`/`void` with one pure total
provider body. Both source hashes, the generated-interface hash, and the complete Python and
TypeScript toolchain identities are returned. Missing or extra exports, type mismatches, cycles,
throws, mutation, external effects, escapes, and JavaScript `number` all fail closed.

The `caught-callable-dataclass-boundaries/v1` fragment verifies a narrow dependency-injection
boundary that Nagini currently crashes on: a typed callable dataclass field is invoked inside a
`try`, its successful result matches the method return type, and a bare or `BaseException` handler
converts every Python exceptional exit to the same return type. `except Exception` is refused
because it does not close arbitrary `BaseException` effects. Argument and fallback expressions are
restricted to typed parameters and primitive literals.

The `dagcert-closed-typed-operations/v3` fragment is the direct Dagcert application seam. It
resolves `operation` and frozen `dataclass` markers from their real imports, checks a one-record task
input and a finite record-outcome union written with either `|` or an explicitly imported
`typing.Union`, and proves straight-line or `if`-branched direct outcome construction from total
primitive field expressions. Version 2 also accepts primitive-only f-string interpolation without
format specifications or conversions; record formatting and other user-defined dispatch refuse.
The primitive surface includes `float` records, outcomes, locals, and total literals, unary signs,
addition, subtraction, multiplication, and comparisons. Partial arithmetic such as integer or
float division, arbitrary calls, helpers, and reachable missing returns refuse. Same-type primitive
local reassignment is accepted; type-changing reassignment refuses.
Homogeneous immutable primitive tuples written as `tuple[T, ...]` are valid record fields and
outcome values. The operation checker admits total, element-type-checked membership comparisons and
refuses heterogeneous or mutable collection shapes.

Version 3 adds callable-valued frozen input fields through an explicit hash-bound provenance edge.
The field's `typing.Callable[[...], ...]` annotation supplies its signature but is never evidence of
provider identity or totality. Every callable field receives exactly one request binding to either
a requested source function or a checked external `@ContractOnly` function. Source providers are
checked from their real body in a closed primitive return/branch/raise fragment. External providers
require a fixed positional primitive signature and currently refuse preconditions. Every declared
provider exception is composed through the operation's actual `try`/`except` handlers. Abstract or
mismatched fields, unknown providers, uncaught exits, callback alias or mutation,
generic/variadic/async providers, and unmodeled provider statements fail closed. The response binds
both endpoint hashes and the exact operation/input/field/provider edge. This is the actual
production source shape Dagcert binds, not a second handwritten effect summary. Multiple concrete
dependencies may run sequentially; each primitive result may be stored in a typed local and passed
to later callbacks or outcomes. Same-type primitive reassignment is allowed, while callable-valued
locals, callable rebinding, type-changing reassignment, and inconsistent branch/handler local
environments refuse.

The second fragment, `scalar-nagini-contracts/v44`, lowers path-sensitive
`int`/`bool`/`str`/`None` functions, recursively typed fixed `Tuple[...]` values, and homogeneous
immutable `List[...]`, `Set[...]`, and `Dict[...]` values,
distinct byte-string and range values, and statically known Python slices,
`Requires`, `Ensures`, assignments, assertions, path-sensitive `if` branches, and multiple returns
into a language-neutral verification-condition IR. Its contract semantics are partial correctness:
it proves obligations for reachable normal paths but does not claim loop termination. Each branch carries its own symbolic
environment and assumptions to the postcondition. A pinned Z3 backend proves each implication or
returns a concrete counterexample.
Version 43 gives fixed tuples a source-owned Z3 datatype whenever they cross a collection boundary.
Tuple constructors and accessors therefore retain exact heterogeneous field sorts inside list
sequences and dictionary arrays instead of being erased to an uninterpreted value. Immutable
lists accept recursively fixed-tuple elements; dictionaries accept fixed-tuple keys and values;
sets accept fixed-tuple keys and impose pairwise uniqueness on symbolic sequence models. Closed
set literals use exact duplicate elimination. Symbolic set construction, mutable tuple members,
collection mutation, `Old` snapshots, resource predicates, non-integer quantifiers, and
alias-sensitive identity remain outside this scalar tranche and fail closed.
Symbolic `for x in values` over a stable immutable `List[T]` uses a fresh arbitrary index constrained
to the list domain. The frontend proves each leading invariant initially and after one arbitrary
body step, retains it at natural exit, and applies the same rule recursively to nested loops.
Mutation or escape of an iterable alias, abrupt or exceptional body completion, `Previous`, and a
post-loop read of the target when the list may be empty all refuse or produce an explicit failed
definedness obligation.
Version 33 also models one source-order module-initialization mutation of a non-escaping finite
`List[int]`: a direct-name receiver, a static nonnegative in-bounds index, an integer-literal right
operand, and primitive `+=`, `-=`, or `*=`. The model records container evaluation, one index
evaluation, element read, right-operand evaluation, primitive operation, and store in that order.
Aliases, callable/class escape, repeated mutation, dynamic or negative indices, booleans, and
custom dispatch refuse. This slice deliberately rejects any module containing functions or
classes, so it cannot be selected by transitive or checked-external routes; their v26/v19 fragment
identities are therefore unchanged.
`formal/Maledictus/FiniteListModuleMutation.lean` is an executable model of this ordered update and
proves target-cell replacement plus preservation of every distinct cell. These are model theorems,
not an extracted Rust/frontend correspondence proof.
Verification conditions carry an explicit `prove` or `refute` expectation; `Refute(expr)` succeeds
only when Z3 finds a counterexample to `expr`. This polarity is serialized in proof results instead
of being inferred from diagnostic names.
The module frontend also builds typed summaries for source-owned, side-effect-free direct-return
functions and inlines their expressions at call sites. Recursive calls refuse until a termination
proof is available. Python's `bool` subtype relation to `int` is represented explicitly with a
typed conditional coercion in the VC IR.
At module scope, a unique undecorated no-base `class Name: pass` may coexist with unrelated scalar
functions but does not enter the scalar value or annotation environment. The one value-producing
class slice is a pass-only subclass of the canonical unshadowed builtin `int`: a direct call with
one `int`/`bool` positional argument has exactly the inherited integer value. This is sufficient to
verify the real numeric behavior in Nagini issue 00261 without modeling a nominal class object.
Custom bodies, decorators, metaclasses, other bases, keywords/default conversion forms, class
identity, nominal annotations, and rebinding either the class or `int` remain fail-closed.
Annotated `while` loops use the standard invariant rule: prove each leading `Invariant(...)` on
entry, havoc every loop-modified scalar, assume the invariant and condition for one symbolic
iteration, prove preservation, then analyze the exit under the invariant and negated condition.
Nested loops retain enclosing assumptions. Scalar augmented assignments and Python truthiness for
`bool`, `int`, `str`, `None`, fixed tuples, and immutable lists are explicit in the lowering.
Python `and` and `or` select and return their operand values rather than being collapsed to
booleans; conditional expressions use the same typed value selection. Partial operations in later
short-circuit operands or an unselected conditional branch do not create reachable exceptional
paths. Chained comparisons preserve Python's left-to-right short-circuit semantics and lower to a
conjunction of typed pairwise relations. Selection requires both possible values to have the same
verified sort. Dead constant branches are type-checked by the same join rule instead of
being used to hide an incompatible value. Tuple construction,
constant projection, length, equality, modular arguments, and modular results retain every element
sort. Dynamic indexing of a nonempty fixed tuple is guarded by its exact signed bounds and lowers
to a finite selection only when all components have one common result sort; incompatible
components, empty tuples, dynamic indexing in specifications, and variable-length tuple
annotations outside the v44 homogeneous boundary refuse. `Tuple[T, ...]` has its own immutable
sequence sort in v44: annotated literals, symbolic length, guarded integer indexing, exact static
slicing, equality, and direct-name iteration are modeled without conflating it with `List[T]` or a
fixed tuple. Concrete starred unpacking constructs the Python list capture; symbolic-width
unpacking refuses. This changes the solver IR to `maledictus-scalar-vc/v27`; the same lowering is
bound by checked-external scalar v26 and transitive/combined scalar v33. Loops without invariants,
`break`/`continue`,
unsupported calls, heap access, permissions, and other control flow
refuse instead of being abstracted away.
Constant `range(...)` values and trigger-free Nagini `Forall` over a statically known finite list
are expanded into explicit integer sequences and conjunctions. Constant ranges use an exact
checked cardinality and fallible allocation; size overflow and allocation failure are typed
outcomes rather than policy limits. Symbolic ranges and symbolic quantified collections refuse. Executable literal-zero range
construction produces a typed `ValueError` branch, while specifications reject that partial
operation because they have no executable exception boundary. `for` over one of
these statically known immutable sequences is exactly unrolled, including target rebinding and the
no-`break` `else` path. `in` and `not in` over the same finite values expand to typed equality
checks. Symbolic iterables, `break`, and `continue` refuse.
Static slice normalization covers omitted and signed literal bounds plus nonzero literal steps.
Lists, tuples, bytes, and ranges keep distinct sorts; `ToSeq` performs the explicit conversion used
for cross-container sequence equality. Symbolic sequence slicing remains a refusal boundary.
Runtime list indexing accepts symbolic integer indices and implements Python's negative-index
normalization. Execution forks into a bounded normal path and an `IndexError` path; ordinary
preconditions and branch assumptions can make the latter unreachable, while `Exsures(IndexError,
...)` and matching handlers preserve it as a typed outcome. An undeclared reachable error refutes
the proof. List indexing in contracts refuses rather than treating a partial Python operation as a
total specification function.
Byte strings use a distinct symbolic Z3 sequence sort with concatenation, length, truthiness, and
the same guarded integer-index semantics. Constant integer repetition uses checked conversion and
fallible exact allocation, and `bytes.join` is exact for a statically shaped `List[bytes]`. Symbolic
repeat counts and dynamically shaped joins refuse. Byte indexing in a specification also refuses,
because the executable `IndexError` branch would otherwise be erased.
Integer builtins lower without opaque function axioms: `abs`, positional `min`/`max`, and
nonnegative constant-exponent `**` up to 64 become typed conditionals and multiplication terms. One-argument
`min`/`max` accepts only a statically shaped nonempty `List[int]`; symbolic or empty iterables and
symbolic or negative exponents refuse. The pinned comparison harness reproduces Nagini's unboxed
integer `is`/`is not` diagnostics, but production verification refuses those operators rather than
misstating Python object identity as scalar equality.
The v36 scalar heap assigns source-known allocation identities to fresh tuple and `range`
constructions and preserves identity through ordinary aliases. Canonical constant `str(int)`
conversion is modeled as a source-known value, but implementation-dependent string interning and
identity between unconstrained parameters remain proof obligations or refusals. Shadowing a
constructor removes its canonical semantics. This is deliberately distinct from `==`: Maledictus
never proves object identity merely from equal element values.
Version 37 models Python string-literal statements at their real execution boundary. A module
string literal and a function's first string literal are inert, so ordinary module and function
docstrings cannot create an unsupported effect. Later string-literal statements are also inert,
but only the first function statement may precede `Requires` and `Ensures`; a later literal cannot
move a subsequently written contract back into the declaration prefix. Other expression
statements retain their existing effect and refusal rules. The checked-external and transitive
scalar identities advance with the same source-module parsing semantics.
Typed lambda postconditions use Nagini's two-argument
`Ensures(ReturnType, lambda result: condition)` form. The declared result type must equal the real
function return annotation, the lambda must have exactly one plain positional binder, and every
return path binds that name to its symbolic result before lowering the condition. Source-module
and checked-external summaries preserve the same typed binder rather than translating it to prose
or trusting an adapter assertion.
Module initialization has a closed immutable-value fragment. Direct-name assignments and
initialized annotations are evaluated in source order from primitive/sequence expressions and
already-defined total source functions; the same partial-operation checks used for specifications
reject an initializer that could raise. Function bodies see the final immutable environment after
removing names made local by Python's lexical assignment rule. Transitive source summaries carry
the provider's captured values, not the importing module's same-spelled bindings. Reassignment,
destructuring at module scope, executable module calls, explicit `global` writes, and other module
effects remain refusals until the module state transition is represented explicitly.
Within this immutable sequence-value fragment, Nagini's `list_pred(value)` is accepted only for a
typed homogeneous list and has no residual heap condition: the complete readable value is already
the VC sequence. This does not grant mutation or claim compatibility with Nagini's mutable-list
heap predicate outside the fragment.
Direct source-owned scalar calls prove every declared `Requires(...)` at the concrete call site.
A failed call precondition is retained as its own obligation and diagnostic; the precondition is
assumed only after that check, matching the contract-call rule. Results crossing an assignment or
return boundary are fresh symbolic values constrained only by the callee's separately verified
`Ensures(...)`; implementation expressions do not leak into the caller. Plain assignments,
annotated assignments, discarded results, and direct return calls share this modular rule.
Preconditioned calls embedded in other expressions still refuse until their evaluation order is
represented explicitly.

Scalar contract v21 includes Nagini `Exsures(ExceptionType, condition)`, source-derived custom
exception hierarchies, and explicit exceptional paths.
Direct built-in raises and modular calls fork normal and typed exceptional states. Undeclared
escapes refute, exceptional postconditions are proved under the exact path assumptions, and
`try/except` consumes only matching types in Python handler order. Bare handlers are exhaustive;
nonmatching branches continue outward. `except T as value` binds the exact raised nominal type,
supports hierarchy-aware `isinstance`, and deletes the binding on every normal, return, and
exceptional handler exit. Chained raises, `finally`, and exception tuples refuse until their semantics are
modeled.

Scalar contract v21 also recognizes source-owned `@Ghost` declarations. Their bodies are verified
and their ghost identity survives transitive source-summary export. A call from ordinary runtime
code refuses until the frontend has an explicit ghost execution context; recognizing the
declaration therefore cannot silently erase Nagini's ghost/runtime boundary.

`@Pure @Opaque` functions are verified like every other source body, but ordinary callers use only
their modular pre/postcondition summary. `Reveal(call)` is accepted only as a complete supported
source-call expression. In Nagini's filename-selected comparison harness, it also adds the named
opaque body to the selected proof set; this selection expansion is not an issuance shortcut.

`typing` imports are accepted only as annotation namespace declarations; unsupported imported
types still refuse when resolved. Maledictus never honors `# type: ignore` as a suppression of its
own checks. Because RustPython omits assignment type comments from its AST, Maledictus obtains them
from lexer comment tokens, binds them to the original assignment line, and enforces scalar
`# type: int`, `# type: bool`, and `# type: None` declarations. Unsupported or unattached type
comments refuse instead of disappearing.

Every response binds each source file to the exact fragment that handled it. Responses involving
SMT obligations additionally bind the runtime Z3 version, `z3-rs` binding version, and VC IR
version, so a Dagcert certificate does not hide which proof machinery established the result.
The Lean VC datatype now mirrors every current Rust scalar term constructor, including n-ary
boolean operators, conditionals, all four ordered comparisons, and addition, subtraction, and
multiplication. Lean proves operand-sort inversion lemmas for the arithmetic and n-ary boolean
forms; generated Rust/Lean correspondence remains a later milestone.
VC IR v19 contains symbolic strings and byte strings, concatenation, length and byte indexing,
recursively typed fixed tuples,
homogeneous list sequences with length/index operations, component projection, nominal reference
identities, and the heap primitives needed for the class/permission port: an uninterpreted reference
sort with a distinguished null value, versioned field reads, and exact fractional
`permission-at-least` atoms, universally bounded permission masks, and versioned permission-mask
transitions, plus exception-free Python floor division by a statically positive integer divisor.
Z3 lowers fields and
permission masks as typed functions over reference identities. Both Rust and Lean reject Unit
fields, non-reference receivers, zero denominators, and permission fractions outside `[0, 1]`.
It also distinguishes positive permission, sufficient for reads, from full permission required by
writes.
Class objects use a dedicated VC sort rather than being encoded as instances or strings. The
kernel exposes source class literals, an uninterpreted runtime-class projection from references,
and nominal class-subtyping atoms. `@classmethod` entry constrains the dynamic receiver beneath its
source-declared upper bound, while `cls()` construction records that the new object's runtime class
is exactly that receiver. This keeps inherited classmethod dispatch and `type(Result()) is cls`
machine-checkable without conflating class objects with heap references. The SMT encoding gives
each source class a distinct internal string identity while the VC IR retains its separate class
sort, so source strings still cannot be compared with class values and distinct class literals
cannot alias.
Source-owned predicates use a reserved permission-mask location for predicate ownership. Instance
predicates retain the full `self`-field fragment; top-level predicates additionally accept typed
arguments and positive literal fractional `Acc` footprints. Each token is keyed by the predicate
name and every lowered argument, so ownership of `p(obj, 12)` cannot authorize `p(obj, 13)`.
`Fold(...)` atomically consumes the declared footprint and produces the token; `Unfold(...)`
consumes that token, restores exactly the same footprint, and assumes the already-verified body.
While folded, each body field is constrained to at most the complement of the hidden fraction.
`Unfolding(predicate, expression)` performs those same transitions around the expression and
refolds afterward. The Lean model mirrors the fractional exchange and its inverse transition as
IR algebra only. Its current theorems do not establish Rust/frontend correspondence, preservation
of permission-mask validity, provider-qualified import identity, or the production fresh-result
call rule.
The focused `heap-method-contracts/v76` frontend now lowers real, source-declared class fields,
instance receivers, `Acc(self.field)`, scalar postconditions, and read-permission obligations into
those primitives. Full-permission field writes create a fresh heap version and constrain the
written field in that post-state. Fields may be declared with a class-level annotation or derived
from a direct constructor assignment whose value has a source-resolved scalar or nominal-reference
type.
Version 71 also admits a finite, source-ordered `typing.Union` of exact source-nominal receivers
when every arm exposes one compatible deterministic ordinary method. The shared call binder checks
every arm against the same once-lowered actual arguments; normal postconditions remain disjunctive
per arm, and Pure callers require all arms to be Pure. Missing methods, dynamic lookup, external or
unknown arms, exceptional/effectful summaries, incompatible binders, and results that cannot cross
a matching direct primitive-Union return boundary refuse. Transitive/combined heap version 59
carries the same verified-source catalogs without promoting external contracts to source proof.
The frozen post-v81 compatibility run reaches 231/618 exact pinned fixtures: 122 semantic proofs,
30 production strict-typecheck rejections, and 79 source-wellformedness rejections. There are 373
honest refusals, 12 explicit production-typecheck divergences, two separately superseded
upstream-unsupported cases, and zero mismatches. All 1099 Rust tests and the 31-job main Lean build
pass. The extracted call-binding proof covers all 28 generated loops and now includes an exact
canonical-environment theorem, but the complete public all-input `bind_call` and typechecker
refinement theorems remain unproved and are not inferred from those regression gates.
The same direct identity contains a separate closed IntEnum lowering. Values retain a full finite
descriptor plus an integer carrier: arithmetic comparison projects the carrier, while `is`
requires the complete descriptor and carrier to match. Source-order, binding uniqueness, canonical
imports, constructor-domain obligations, and strict-mypy issuance are enforced before proof
export. The Lean IntEnum file proves the descriptor/domain/projection/identity algebra only; Rust
and frontend correspondence is regression-tested, not formally extracted.
The v70 direct frontend also owns a closed, canonical dataclass-defaults slice when a module uses
both `IntEnum` and dataclasses. It executes required and immutable primitive defaults, enum-valued
defaults, fresh `field(default_factory=list)` allocations, explicit list aliases, field reads,
bounded list append/index operations, and reference identity through an explicit finite heap.
Factories other than canonical `list`, inheritance, generated hooks, mutable literal defaults,
unknown calls, unsupported field types, and frozen writes refuse. The constructive Lean heap and
freshness algebra is not an extracted Rust/frontend refinement proof.
Before any Python proof lowering, the v70 frontend performs source-ordered, binding-aware
well-formedness validation of Nagini contract primitives. Strict mypy remains the first issuance
gate. After it succeeds, module/function/loop/expression contexts reject misplaced declarations,
non-prefix preconditions and loop invariants, illegal nested permission expressions, and the
bounded IO/SIF/termination position errors represented by the pinned suite. The same source-general
pass rejects `Result()` and typed-result contracts that contradict the enclosing function's real
return annotation, plus malformed predicates whose return type, body shape, or source-owned call
effects violate the predicate boundary. Canonical imports,
aliases, rebinding, and local shadowing are resolved from the real AST; a definitely ordinary
shadowed callable is not relabeled as a contract. The same declaration gate resolves canonical
`Inline` and `Opaque` decorators. It rejects incompatible `Inline`/`Pure`/`Predicate` sets,
`Opaque` without `Pure`, inline constructors, modular contracts inside inline functions, and
source overrides crossing an inline boundary in either direction, including through transitive
source bases. Valid aliases retain decorator meaning; rebound spellings do not. These rejections
are reported separately from
semantic proofs and typechecker parity. `formal/Maledictus/ContractPositions.lean` proves only the
constructive context/order and declaration-validity algebra, not extracted correspondence with the
Rust validator. The same binding environment rejects imports inside functions or class bodies and
runtime local aliases built from canonical `typing` constructors. Module-level aliases and
ordinary subscripting remain legal. Canonical `@Pure` declarations must have a non-`None` result,
contain a reachable return, declare no exceptional postcondition or direct raise, and contain no
statically unreachable statement after an unconditional exit. A strict-mypy missing-return
diagnostic is retained in the conformance record, but the more precise Pure-declaration diagnostic
takes precedence; the invalid program still never reaches semantic verification. The same v70
boundary accepts direct source-nominal `Optional[T]` arguments and
returns without inventing a non-null premise. `is None` and `is not None` guards narrow only their
selected path; an Optional return may use Python's implicit `None`, while a reachable nonoptional
nominal fallthrough remains a refuted return obligation. Bounded symbolic loops over a direct typed
`List[T]` require explicit `Acc(list_pred(items))` permission and retain both an independent
exhaustion/fallthrough exit and an arbitrary-element early-return exit. Loop bodies with mutation,
`else`, effectful conditions, invariants, or induction-dependent summaries refuse.
`formal/Maledictus/OptionalListLoops.lean` proves only this constructive null/exit/permission
algebra; it is not extracted from the Rust frontend.
The same declaration gate classifies canonical `@Predicate @ContractOnly` declarations as
abstract specifications. Abstract predicates may appear in contracts, but they cannot be folded
or unfolded because they have no concrete permission footprint. Direct predicates and methods
resolve only through exact source bindings, nominal parameters or `self`, and once-only
before-use source-class construction; inheritance and concrete overrides retain their effective
kind. Unknown or dynamic receivers fail closed. The accompanying Lean algebra is model-only and
does not claim extracted frontend correspondence.
This heap model fails closed globally on dynamic attribute interception. Every source class whose
fields or effects are modeled or exported must have a complete effective MRO ending at `object`.
Each source entry must be proved free of effective `__getattribute__`, `__getattr__`, and
`__setattr__` overrides and of `__init_subclass__` class-creation mutation. A checked-external entry may instead carry a distinct hash-bound
`checkedExternalHookFree` provider-conformance assumption after its ContractOnly stub passes the
same hook and `__init_subclass__` refusal; that assumption is never relabeled as source proof. The gate applies before
field reads, writes, constructor facts, or method effects can become proof evidence, including
through inheritance and source-module export. It does not ban generic scalar-only code whose
classes never enter the heap model. The Lean definition checks this finite frontend-supplied MRO
gate and its refusal algebra; it does not prove MRO extraction or Python correspondence.
Version 28 accepts a constructor result stored directly in a nominal-reference field only when the
callee is a verified source-owned ordinary `__init__`, the field and result have the exact same
nominal class, and the finite source-constructor dependency graph is acyclic. The nested
constructor's postconditions establish the fresh result and its fields before the outer field write;
the post-heap equates that field with the result and the Rust frontend emits the frames needed for
the nested result's declared fields and the outer receiver's other declared fields. A custom
`__new__` on the class or anywhere in its effective allocation chain, a metaclass, an imported or
external constructor, a declared exceptional outcome on the constructor or a called base
constructor, a nominal mismatch, or a constructor cycle must refuse the fragment. The matching
Lean transition system checks the IR and frontend-supplied resolution/freshness premises,
constructs and typechecks requested frame equalities, and proves failure non-extension. It does not
prove semantic preservation of arbitrary receiver fields or correspondence from arbitrary Python
execution to those premises or to the IR. Its constructor summary keeps source-owned ordinary
allocation, normal-only completion, and acyclicity of the effective inherited/explicit-`super()`
dependency closure as three separate success premises rather than hiding them in a generic
"verified" flag.
Version 29 accepts a nonempty contextual `and` in the pure contract-expression subset by lowering
each permission/reference operand independently, requiring every resulting IR term to have Boolean
sort, preserving source operand order, concatenating every operand's heap-read inventory, and then
forming one IR conjunction. This is not a general translation of Python `and`: effectful operands,
truthiness coercion, and any expression whose correctness depends on short-circuit side effects
remain unsupported. The Lean model takes the frontend's pure-expression classification as an
explicit premise and proves only conjunction typing, operand retention, and read retention.
Version 30 resolves a nominal method return through a nonempty chain of effective typed fields. It
also accepts one verified source property when that property is read directly from a named
receiver. The class that selects a field layout is not reused as the field value's class. Every
intermediate and final reference must be non-optional, and the final value class must be the
declared return class or a proved source subtype. A property anywhere inside a multi-hop chain,
along with scalar, unresolved, call-valued, dynamic-attribute, and unverified descriptor results,
refuses. The Lean model separates layout-owner and value-class metadata, typechecks the resulting
reference term, and requires source-subtype compatibility as a frontend premise; it models the
direct-property gate separately and does not prove Python/frontend correspondence or descriptor
semantics.
Version 31 accepts the exact normal postcondition `self.field is Old(self.field)` for a direct,
non-optional effective typed reference field on a verified source-owned non-constructor instance
method. `Old` reads the method-entry heap and requires entry-mask read permission; the current
field reads the method-exit heap and independently requires exit-mask read permission. The field
must be absent from the complete direct-plus-transitive modification set, so the existing
same-receiver frame relates those two heap versions. Call summaries rebind both heaps and masks to
each invocation rather than retaining provider-local version numbers. A modified field, even if a
body might restore it, refuses this first slice. Constructors, nested fields, property/descriptor
targets, dynamic attributes, calls inside `Old`, external contract-only methods, and exception
postconditions also refuse. Lean constructs and typechecks the two reads, permission obligations,
frame equality, and call-site rebinding from explicit frontend premises; it does not prove
Python/frontend correspondence, permission truth, modification-set completeness, or semantic
framing.
Version 32 accepts only the direct normal postconditions `Result() is self.field` and
`Result() is not self.field` on a verified
source-owned, non-constructor instance method. The result and direct effective field must be
non-optional references of the exact declared nominal return class; the accepted method-type
constructor rejects `Optional[...]` returns before this rule. The provider must prove that
its unique terminal normal return has no executable successor and returns the field read from the
method-exit heap on every supported normal path; the negative form proves the negation of that
same equality. Equality of nominal labels alone is insufficient.
That current field read independently requires exit-mask permission. A proved call summary rebinds
the receiver, result, exit heap, and exit mask at each invocation. Constructors, identity inside
`Exsures`,
properties/descriptors, optional or scalar fields, nested or dynamic access, call-valued fields,
external contract-only methods, and bodies without the unique-terminal-return premise refuse.
Lean models and typechecks the provenance equality and rebinding from explicit frontend premises;
it does not establish Python/frontend correspondence, control-flow completeness, permission truth,
or provenance truth.
Version 33 separates late-bound source class names used by supported method contracts/bodies from
eager class-definition execution. A method is parsed at its definition; supported class references
inside its contracts/body are resolved against the sealed full source module, and its summary
carries every canonical class dependency.
At each runtime call in module initialization, every same-module dependency must exist in the exact
class prefix at that call; an imported summary instead requires its canonical provider module to
have completed initialization. A later class cannot repair an earlier failed call, and a class
that never exists prevents summary construction. Canonical identity cannot be replaced by a
same-spelled local, parameter, or importer class. Bases, decorators, class-body expressions, and
bare method annotations remain eager at the class statement; only the existing quoted/deferred
annotation path defers. Dynamic/reflection-based lookup and unchecked external
providers remain unsupported. Lean models the catalog/prefix/provider-state distinction and
failure rules from explicit frontend premises; it does not prove dependency completeness,
canonicalization, provider initialization, or Python/frontend correspondence.
Export may seal only a dependency or nominal identity already resolved as local to the exporting
module. A dependency, field type, parameter, return, base, or constructor edge resolved to a
foreign provider must retain that provider-qualified identity; absence of a dot in source spelling
is not evidence of local ownership. Required foreign shapes remain in a private canonical
dependency catalog so downstream consumers can resolve inherited layouts and reference-valued
fields/results; they do not become public symbols of the intermediate provider.
Version 34 composes genuinely multi-step, non-optional nominal-reference chains from raw source
fields and verified zero-argument source instance methods. Evaluation is left-to-right: every field
read checks permission in the current mask, and every call threads its proved result provenance,
nominal class, heap, mask, assumptions, and obligations into the next step. Empty complete write
sets and net-neutral permission effects preserve their respective versions independently; writes
advance the heap with complete modification/frame data, while non-neutral permission effects
advance the mask through the existing transfer rule. External ContractOnly methods and fields,
including an external-inherited field wrapped by a source method, cannot become source provenance.
Calls with arguments, optional/scalar/unresolved results, properties/descriptors, exceptional
outcomes, dynamic dispatch outside the resolved source table, and incomplete effects refuse. The
Lean model checks this typed transition algebra from explicit member-origin, summary, and frontend
premises; it does not prove Python correspondence, provenance truth, permission truth, or semantic
framing.
Version 35 adds one deliberately narrow proof rule for positive ghost assertions of the form
`Assert(left == right)`. The left operand must be a named local tied to a normally completed,
verified source allocation with an exact runtime class and a complete source-only MRO with no
`__eq__` override. The right operand must be a source name or a non-optional raw source-field chain
whose receiver at every hop has independently proved normal-only source-allocation provenance,
exact source runtime class, and
ordinary attribute resolution, read with permission in the current heap and mask; ordinary calls, properties, and state
transitions cannot execute inside this specification expression. Identity is only a sufficient
verification condition: the frontend first discharges identity from the current assumptions, which
also recovers the right operand's exact runtime class, and only then emits the proved assertion.
Every earlier call, permission, and transition obligation must already be proved before that
discharge.
A nominal right field/name class is never treated as runtime-class evidence. If identity is false
or cannot be proved, this v35 slice refuses instead of reporting general Python equality as
refuted; this is why the pinned line 59 proves while line 61 remains rejected. The rule does not
model reverse dispatch. `!=`, negation,
`Requires`/`Ensures`, arbitrary left expressions, non-exact or external allocation, custom
equality, a non-exact field receiver, effective `__getattribute__`/`__getattr__`/`__setattr__`
interception, and executable/spec call operands refuse. Lean checks the typed identity obligation,
current read-version/permission premises, MRO gate, and those refusal boundaries as IR/premise
algebra; it does not establish Python equality semantics or frontend correspondence.
Version 36 extends only the right-hand evidence of that same asymmetric assertion syntax. The
left operand must still be the v35 named local tied to one completed, verified source construction;
it is not generalized to a field chain. The right operand may be a source name or a permission-
checked raw source-field chain. Both resulting references must now have independently proved exact
runtime source classes, and both complete effective MROs must end at `object` without any
class-dictionary binding for `__eq__` or `__init_subclass__`. For a raw right-hand field chain, every receiver hop also
retains its current heap/mask read, permission, exact runtime source class, normal source allocator,
and global hook-free attribute-resolution premises. Under those bilateral exactness premises both
Python equality dispatch candidates are `object.__eq__`, so the equality is exactly the IR
reference-identity condition: the solver may prove equal identity, refute distinct identity, or
leave it unresolved. Reverse-dispatch and subclass-priority behavior cannot introduce a hidden
custom equality implementation because the right runtime class and its complete MRO are proved,
not inferred from a nominal annotation.

The class-scope scan covers every supported binding form, including functions, async functions,
assignments with nested tuple/list/starred targets, annotated/augmented assignments, and imports;
unsupported class-body forms refuse before a heap summary is issued. In particular, a source or
checked-external `__init_subclass__` refuses because it could inject equality or attribute hooks
while a derived class is created. The v35 identity-sufficient fallback remains for a right
operand without independent exact-class evidence: it can accept only identity already proved by
the current assumptions and still cannot refute nonidentity. General left field chains, properties,
ordinary calls, checked-external or dynamic equality, optional/scalar operands, `!=`, negation,
contract clauses, and executable side effects inside the ghost expression remain unsupported.
Lean formalizes the typed identity reduction and finite frontend premises/refusals only; it does not
prove Python AST/MRO extraction, allocation provenance, solver facts, or frontend correspondence.
Version 37 accepts one narrow standalone nested-call statement in a verified module heap function:
the callee receiver is a source
name/field/zero-argument-method reference chain, the call has exactly one positional
non-optional nominal-reference argument formed by the same chain grammar, and the terminal method
is a source-owned, nonexceptional instance method with exactly that one required parameter and a
normal Unit return. Evaluation follows Python order. The receiver chain is evaluated first; its
heap, mask, assumptions, obligations, and resulting reference are retained. The argument chain is
then evaluated left-to-right from those exit versions. Only after both succeed is the terminal
summary rebound once to the saved receiver and argument terms and applied to the argument's exit
heap and mask. Neither expression is re-evaluated.

Receiver and argument may alias: no distinctness fact is introduced. Preconditions, permission
effects, the complete modification set, frames, and postconditions must instead be instantiated for
the actual two terms under the existing alias-sensitive call rule. A receiver-stage refusal prevents
argument and terminal evaluation. Static terminal-summary validation occurs after receiver lowering
and may refuse before argument lowering; this verifier diagnostic order is not presented as Python
execution. Once that summary is accepted, an argument-stage refusal prevents the terminal call and
the terminal state transition starts only from the post-argument trace. External or dynamic members, optional/scalar results,
properties/descriptors, exceptional summaries, multiple/keyword/default arguments, non-Unit
returns, class/instance-method-body use, and calls in ghost/contracts remain unsupported. Lean composes the existing v34 reference-
chain transitions and models this ordering/refusal algebra from frontend premises; it does not prove
Python correspondence, alias analysis, exception freedom, permission truth, or summary correctness.
Version 37 does not widen reference equality: a following assertion whose left operand is a raw
field chain remains a separate unsupported/refusal case rather than part of the nested-call proof.
Version 38 adds two linked but separate narrow rules. First, after a complete normal source-method
summary advances the heap, the caller may instantiate frame equalities for a finite inventory of
its direct typed source-root fields. Each root and effective field must have verified source origin
and ordinary non-dynamic attribute resolution, and the summary must carry a proved complete
direct-plus-transitive modification set. A field is framed from the call-entry heap to the call-exit
heap only when its field name is absent from that set. This conservative name test remains safe when
the caller root aliases the call receiver: any possibly modified same-named field receives no frame.
Checked-external/dynamic roots, members, or summaries, exceptional/incomplete summaries, unresolved
types, and modified field names refuse without extending the accumulated frame facts.

Second, v38 accepts only the orientation `Assert(raw_source_field_chain == exact_source_name)`.
Every receiver hop on the left must have a current permission-checked read, proved exact runtime
source class, normal source allocation, and complete heap-hook-free MRO. The right must be a named,
normally completed exact source construction with a complete source/object MRO containing no
`__eq__` or `__init_subclass__` binding. The current assumptionsâ€”including any valid caller-root
framesâ€”must already prove reference identity before the assertion is emitted. Identity recovers the
left result's exact clean runtime class, so custom or reverse equality dispatch cannot intervene.
This is not a general symmetry rule: exact-name-left/raw-chain-right remains v35; arbitrary swapped
expressions, false/nonidentity refutation, calls/properties, external/dynamic values, `!=`, negation,
and contract clauses remain outside v38. Lean constructs and typechecks the finite frame/equality IR
and refusal transitions from frontend premises; it does not prove root enumeration, Python/frontend
correspondence, modification completeness, alias analysis, semantic framing, or Python equality.
Version 39 adds one dedicated source reference-identity function summary for the direct terminal
argument of the v37 standalone nested-call rule. The function must be exactly `@Pure`, have one
required non-optional positional parameter of canonical source nominal type `T`, return that same
canonical non-optional `T`, contain exactly `return parameter`, and prove one total normal,
heap-and-mask-neutral outcome. The call target must resolve lexically to that exact source summary.
A bare decorator spelling is insufficient: `Pure` must still resolve to the canonical imported
Nagini binding at the declaration, and rebinding or shadowing it refuses.
A local summary must be present in the exact call-time callable prefix; an imported source summary
requires its canonical provider to have completed initialization, while its nominal dependency
retains the v33 canonical class-availability check.

The wrapped source reference chain is evaluated once, after the outer receiver and before the
terminal method. Identity application returns the exact argument term and actual nominal
provenance; it creates no fresh result and preserves the argument-exit heap, mask, assumptions,
and obligations. Only then may the outer source Unit method consume that saved value. A malformed,
shadowed, unavailable, external, optional, defaulted, keyword, nested, ghost, or arbitrary pure
function use refuses and cannot apply the outer call. Lean models this finite neutral-application
and refusal algebra from frontend premises. It does not prove Python evaluation, decorator or
lexical resolution, source totality, canonicalization, provider completion, argument-chain
correctness, or summary truth.

Version 39 also adds a narrower object-sensitive frame after a verified non-external source
instance method advances the heap. The method's complete supported direct-`self` call closure must
prove that every executable write is a direct field write on that same instantiated receiver. The
frontend then inspects only the finite one-hop exact-constructor reference fields of typed local
caller roots. The root and reached candidate need exact source runtime classes and complete
plain/hook-free source MROs; the one-hop edge must be a non-optional source-owned reference with
exact-class metadata from a verified normal source constructor; and each framed candidate field
must be an effective source-owned heap field. Only when the current assumptions prove that reached candidate distinct from the
modified receiver may its effective source fields be framed between the call-entry and call-exit
heapsÃ¢â‚¬â€including a same-named field in the method's modification set. The frame uses the saved
pre-heap candidate reference; it neither frames the root edge nor creates permission.

An aliasing candidate, unknown alias relation, missing exactness, checked-external/dynamic member,
exceptional/incomplete summary, or unclosed effect set adds no object-sensitive frame. The older
v38 name-based root frame remains the fallback and still excludes every modified field name. Lean
models only this conditional frame IR from supplied premises; it does not prove local-root
enumeration, constructor freshness, exact-class/MRO facts, alias disjointness, effect closure,
frontend/Python correspondence, or semantic heap framing.

Version 40 extends only that same raw-left/exact-name-right assertion syntax when the raw chain's
final value now has independent bilateral evidence. In addition to current heap/mask permission
and exact plain source provenance at every receiver hop, the final left reference must prove its
exact runtime source class, verified source allocator, normal-only constructor, and complete source
MRO ending at `object` without `__eq__` or `__init_subclass__`. The exact constructed right name
retains the same clean-MRO and normal source-allocation gates. A nominal field annotation alone is
never final-value evidence.

With both exact runtime classes and both complete clean MROs, Python's forward, reflected, and
subclass-priority equality paths all resolve to `object.__eq__`; `==` is therefore exactly the
reference-identity VC. The ordinary assertion solver may prove identity, refute nonidentity, or
leave it unresolved. In the final expected-false assertion of upstream `test_method_calls.py`, the
second setter establishes `c1_1.c2.c1 is c1_2` while the two completed source constructions establish
`c1_1 is not c1_2`, so the emitted assertion is refuted rather than rejected by the frontend. The
v38 identity-sufficient branch remains available when final-left exactness is absent; v40 does not
add general symmetry, properties/calls, optional/scalar operands, external/dynamic/custom equality,
other operators, or contract contexts. Lean models only the typed identity reduction and solver
disposition from supplied premises, not Python/frontend correspondence, allocation/MRO facts,
permission truth, or those program-specific heap equations.

Version 41 adds typed conditional expressions as first-class heap-expression values. The condition
is evaluated first and must be Boolean. Both branches must be total, heap-read-free, and effect-free
in this slice: raw heap reads, calls, constructors, properties/descriptors, writes, permission
transfers, exceptional operations, and heap/mask transitions refuse. The VC result is
`ite(condition, then_value, else_value)`; condition-read obligations are unconditional, and the join
itself changes neither heap nor mask and grants no permission.
This slice does not accept or model statement-level Python `if`/`else` heap control flow.

Equal supported scalar sorts join directly. A localized mixed `bool`/`int` pair converts its Boolean
branch to `0`/`1` and joins as `int`; this coercion does not apply to other sorts. Canonically
identical validated nominal types join while preserving optionality; a proved catalog
subtype/supertype pair joins at the supported supertype; and one validated nominal branch plus
literal `None` joins as `Optional[T]`. The catalog evidence may come from verified source or a
hash-bound checked-external overlay because this expression invokes no provider behavior. A nominal annotation or join
never creates exact runtime provenance or non-nullness. Scalar/reference mixtures, unrelated
nominals without a proved supported join, unchecked/dynamic types, `None`/`None` without a
contextual nominal type, and effectful branches refuse.

A direct zero-argument source instance call through an optional local evaluates its receiver and
then emits a distinct `receiver != None` obligation before exposing the method's own permission
preconditions or effects. A refuted or unresolved receiver does not add method permissions,
assumptions, or a state transition. The logical check maps to `call.precondition` for an ordinary
method and `application.precondition` for `@Pure`, matching `null_test` and `null_test_pure` without
special-casing their class. A proved non-null receiver proceeds through the existing method-summary
rule, where existing mask factsâ€”not the conditional joinâ€”must establish its `Requires`. Lean models
only typed join, condition-obligation, state-preservation, and receiver-gate algebra from supplied
premises; it does not prove Python evaluation/frontend correspondence, subtype facts, permission
truth, or solver disposition.

Version 42 adds a conservative statement-level heap `if`/`else` path split. The condition must be a
read-free, call-free Boolean value. The then branch receives the condition as an assumption and the
else branch receives its negation. Branches may contain `pass`, scalar `Assert`, local assignments
from scalar values, validated nominal-reference names, literal `None`, or v41 conditional
expressions, and nested instances of the same statement form. Calls, heap reads or writes,
permission changes, contracts, returns, exceptional operations, and divergent heap/mask exits
refuse.
Simple initialized `int`/`bool` local annotations are also accepted when the initializer matches the
annotation after the localized `bool`-to-`int` coercion; annotation-only, non-scalar, mismatched, or
non-name targets refuse.

Both branches must complete normally. Every post-join local must be defined on both paths. Equal
scalar sorts join by `ite`, mixed `bool`/`int` uses the localized `0`/`1` promotion, and validated
nominals join only when they are identical or one is a proved catalog subtype of the other; the
selected type is the supported supertype. A validated nominal plus literal `None` becomes optional.
Sibling least-upper-bound inference and unchecked/dynamic nominal joins refuse. Hash-bound
checked-external catalog types may join because no provider behavior executes. Exact-runtime and
source-construction provenance remains source-only and survives only when both paths retain the
identical term and canonical class. An absent `else` is the unchanged incoming path, so a new local
created only in the then branch is not definitely bound and refuses.

Incoming obligations are retained once, while branch obligations retain their respective path
assumptions; branch-only assumptions do not become unconditional facts after the join. Lean models
the finite split, typed local join, provenance, state preservation, obligation guarding, and refusal
algebra from supplied frontend premises. It does not prove Python/frontend correspondence,
subtyping, environment canonicalization, branch execution, reachability, or solver validity. Heap,
permission, early-return, and exceptional state joins remain explicit future extensions.

Version 43 introduced a guarded-state set from the first return-containing conditional through
the remaining function body; earlier v42-pure conditionals may still use their exact typed local
join. The current executor tracks every finite normal and returned state generated in that
return-sensitive region; it has no fixed path-count cutoff. A read-free Boolean condition conjoins
itself to the then-path guard and its negation to the else-path guard; each path retains its own
environment, assumptions, obligations, heap version, and permission mask. Nested conditionals use
the same union, and an absent `else` contributes one unchanged normal path. Paths are never dropped
or collapsed to manufacture a proof.

The executable branch subset remains v42-pure, but it now permits early `return`. Return values are
limited to the existing heap-function `None`, `bool`, and `int` annotation domain and must match the
declared sort after the existing localized `bool`-to-`int` promotion. Each return preserves its path heap/mask, independently checks the function's normal
postconditions under that path guard, leaves the normal set, and skips all continuation. Unit
fallthrough becomes an implicit Unit return; any reachable non-Unit fallthrough refuses with a
missing-return diagnostic. Nominal/optional returns, calls, constructors, heap reads/writes,
permission changes, exceptional exits, and contracts inside branches remain later work.

Lean models guarded splitting, exact finite-list union, early-return transfer, per-exit obligations,
continuation exclusion, Unit fallthrough, and refusal algebra from frontend-supplied premises. It
does not prove AST correspondence, reachability, postcondition instantiation, solver results, or
heap/permission semantics, and it provides no conditional heap/mask join theorem.

Version 44 enters that guarded path engine at the first conditional containing either an early
return or a supported source heap effect, so an effect-only branch is never sent through v42's
heap-neutral local join. Each normal path invokes the same statement transition used outside a
conditional and retains its own post-statement environment, assumptions, obligations, heap, and
permission-mask versions. Returned paths remain counted but skip the effect and all continuation;
shared continuation and function postconditions execute independently for every reachable normal
or returned state. A path halted by a refuted receiver or call precondition is retained for its
failing obligation but skips continuation too. Normal, returned, and halted states all remain in
the exact finite path list, and no differing heap/mask pair is merged.

The accepted path-local effects are a normal-only verified source constructor assigned to a local
with effect-free positional arguments and no keywords; a normal-only verified source instance
method result assigned to a local under the same argument restriction; a direct zero-argument Unit
source-method statement; and a direct typed-local write to a plain verified source field with an
effect-free, heap-read-free right side. Constructor calls retain the existing fresh
source-allocation facts and current heap/mask versions. A method advances heap and mask exactly as
its complete transitive write and permission-transfer summary requires. A direct field write
requires a statically non-optional source receiver carrying its non-null premise and full current-mask permission, checks exact scalar typing or
proved nominal same/subtype compatibility (including `None` only for an optional field), advances
the heap once, preserves the mask, and records the write plus available frames. All prior
obligations remain path-local. A refuted receiver/precondition obligation halts only that guarded
path, retains the path-qualified failure, restores its entry heap/mask and pre-effect assumptions,
and executes neither the rejected transition nor later statements.

Exceptional summaries, properties/descriptors, dynamic or checked-external dispatch, predicate
ownership transfer, unresolved or optional field receivers, incompatible nominal assignments, calls in
guards/returns/contracts, and unsupported argument/call shapes refuse. Lean proves only the finite
activation, version-transition, guarded-batch, preservation, and refusal algebra from frontend
premises; it does not prove AST/executor correspondence, source ownership, freshness, subtype or
permission truth, summary completeness, exception freedom, or solver results.

The authoritative v42-v46 execution model is `formal/Maledictus/HeapControl.lean`. It recursively
constructs guarded paths, executes typed effects, preserves returned/halted paths without a fixed
path-count cutoff, and instantiates the function's bound postcondition list on actual exits. The former
witness-driven `HeapStatementBranchTrace`, `GuardedHeapBranchResult`, and
`GuardedPathLocalSourceEffectRequest` APIs were removed rather than retained as theorem-shaped
adapters. Constructive type joins and field-write compatibility utilities in `HeapCallable.lean`
remain authoritative. The
frontend still owes AST-to-IR correspondence and the truth/completeness of supplied source
summaries, solver dispositions, subtype facts, and permissions.

### Version 45 behavior: checked narrowing and path-local raw returns

Version 45 adds opaque nullable `object` parameters to the heap-function environment. An opaque
reference has no nominal member layout, exact-class provenance, or source-construction provenance;
it cannot access a field/method or enter a nominal slot before a checked narrowing. The only new
condition form is direct canonical `isinstance(Name, SourceClassName)`. The frontend excludes
shadowed builtins, indirect/compound calls, external or incomplete target MROs, nondefault
metaclasses, and `__instancecheck__`. Lean receives finite source-class records with direct-base and
field declarations, rejects duplicate/cyclic/unresolved graphs, and computes subtype reachability
and inherited field lookup rather than accepting a supplied subtype closure.

For a nonexact value the condition is exactly `value != null &&
ClassSubtype(RuntimeClass(value), target)`; an exact tracked source construction is constant-folded
through the checked class graph. The true path installs a nonoptional source nominal. It retains a
more precise known nominal subtype and retains exact/source-construction provenance only when that
metadata already belongs to the checked subtype. The false path changes no metadata. A no-effect
join whose two exits retain the incoming term restores the complete incoming binding, preventing
true-only narrowing from leaking; changed terms use the existing constructive typed join.

A path return may directly read a catalog-declared raw field. The request supplies only the local
receiver name and field name; Lean resolves the current binding, nominal class, inherited field,
field type, heap version, and exact current-mask read obligation itself. An opaque receiver refuses.
A proved prerequisite returns the constructed current-heap field term; a refuted prerequisite
retains its obligations and halts only that path, so it receives neither a return postcondition nor
later continuation. Read-free scalar conditional expressions support only `bool`/`int`, with the
localized Boolean-to-integer promotion; reference, class, and heap-read branches refuse.

`HeapControl.lean` proves these executable IR transitions without caller-supplied exit states or
subtype/field closure tables. Frontend recognition of canonical Python syntax, faithful extraction
of source-safe class records, solver disposition, and Python correspondence remain explicit
premises.

### Version 46 behavior: structural short-circuit conditions and real fallthrough

Version 46 extends the same executable path engine with structurally recursive `and` and `or`.
The left operand is evaluated first; only its feasible true exits enter the right operand for
`and`, and only its feasible false exits enter the right operand for `or`. Consequently a skipped
right operand creates no dispatch, permission, precondition, or proof obligation. Feasibility is a
proof-kernel disposition over the complete guarded assumptions, not a caller-supplied truth flag.
Supported atoms remain narrow: canonical source-safe `isinstance`, scalar comparisons, and
verified source-pure scalar method calls selected from the checked class/method catalog. Each
evaluated call emits its path-local precondition and result facts once, in Python operand order.

Method dispatch closes only for an exact or source-constructed receiver whose current class and
selected source summary are established by the checked catalog. A merely annotated, nonclosed
Python ingress value is not treated as ranging only over catalog subclasses: that path is
unmodeled/refused rather than justified by a silent sealed-world premise. Exact receivers dispatch
only to their exact class. Exceptional, impure, external, unresolved, dynamically dispatched, or
unsupported condition atoms remain fail-closed.

Final disposition is counterexample-first across actual modeled exits. Any concrete refuted
obligation refutes the function even if a sibling is unmodeled; absent a refutation, any unmodeled
reachable sibling blocks `Proved`. A reachable non-Unit fallthrough is represented as the real
implicit-`None` exit and receives the function's bound return/postcondition obligations under its
own guard at the function line. It is neither dropped nor converted to typed success. Obligation
identifiers remain path-scoped, and the finalizer instantiates the bound obligation set exactly
once for each actual exit.

`HeapControl.lean` constructs the short-circuit splits, dispatch lookup, selected body/contract
summary relation, path-local obligations, fallthrough exit, and final disposition. Frontend
AST-to-IR correspondence, completeness/truth of extracted source records, and proof-kernel
dispositions remain explicit premises.

### Version 47 behavior: structural negation and read-free primitive chains

Version 47 evaluates structural unary `not` by running the supported inner condition exactly once
and exchanging its feasible true and false path sets. Calls, permission checks, halted/unmodeled
paths, and flow-sensitive narrowing remain attached to their actual inner evaluation path. It also
accepts statement-condition chained comparisons whose operands are read-free `bool`/`int` values:
each operand is lowered once, adjacent comparisons are formed in source order, and their results
are conjoined. Chains containing calls, heap reads, references/classes, or custom comparison
dispatch remain fail-closed.

The completed release advertises
`heap-method-contracts/v47` and the corresponding transitive and combined source-heap summaries as
version 41.

### Version 48 behavior: closed monomorphic generics

Version 48 adds a deliberately closed, static-only Python generic slice. A type parameter must be
introduced by an unaliased, source-ordered `from typing import TypeVar` followed by the canonical
module declaration `T = TypeVar("T")`. A supported class has exactly one `Generic[T]` parameter and
exactly one concrete specialization in the checked module. The specialization may be an existing
scalar or source-nominal type, and `T` may occur only as a direct field, parameter, or return
annotation of its declaring class. The frontend substitutes that concrete type before ordinary
constructor, method, field, and permission checking, so constructor arguments and returned values
are checked against the specialized type rather than erased to an unconstrained reference.

`TypeVar` declarations never become module globals, captured values, heap locals, class members,
or proof-kernel terms. They are consumed by the static annotation resolver and removed before the
runtime heap model is built. The frontend refuses mismatched literal names, aliases or dynamic
callees, rebinding or runtime reads/exports, bounds, constraints, variance/default arguments,
multiple or missing concrete specializations, composite specializations outside the current type
IR, unsupported generic positions, and quoted direct `"T"` annotations. This is monomorphization,
not Python runtime `TypeVar` semantics and not parametric polymorphism. The pinned
`issues/00266_1.py` fixture is the exact conformance target.

Module-function expression lowering is also class-neutral. It first uses the ordinary contextual
lowerer; when a heap class is genuinely required, the root class is derived structurally from a
typed object receiver or class literal, including through supported scalar wrappers. It never
selects an arbitrary first class from the module. Ambiguous expressions therefore refuse, while
valid cross-root contextual comparisons retain their existing semantics.

The atomic release advertises `heap-method-contracts/v55` and transitive and combined source-heap
summaries at version 49. Version 49/version 43 remains the historical identity of the callable and
constructor-control-flow release.

### Version 49 callable and constructor control flow

Version 49 made canonical Nagini `@Pure` module functions reusable when their contract-free body
was scalar statement code rather than only one `return` expression.
Accepted bodies contain read-free `int`/`bool` local assignments, initialized simple-name
annotations, `Pass`, nested `if`/`else`, and early returns. The current implementation retains every
finite structural path and has no fixed path-count cutoff;
every structural path must return a compatible scalar value, with Python `bool`-to-`int`
promotion, and the call result is the corresponding nested `ite`. Internal `Assert` remains
definition-verifiable but is not reusable at a call until its proof is sealed. Heap reads/effects,
unsupported calls, missing returns, and incompatible values refuse.
Any local defined on only some structural paths remains guarded by its exact definition condition;
each later read emits a path-scoped definedness VC. A reachable non-Unit `@Pure` fallthrough emits
`function-totality:implicit-return[:path:i]` and is attributed as `function.not.wellformed`, while
ordinary heap-function fallthrough retains `postcondition:implicit-return[:path:i]` attribution.

Callable summaries carry provider-qualified identities, captured spelling-to-identity bindings,
and immutable provider globals. Their private transitive callable catalog is exported with a
proved source module, so a consumer-local helper or global with the same spelling cannot reinterpret
an imported body or contract. Current-module initialization still uses the exact source prefix;
completed providers use their sealed environment. Parameters and lexical locals are excluded from
captured callable bindings, and recursion is checked by stable identity.

The same tranche began statement-level constructor control flow without merging branch heaps or
permission masks. The original release retained up to 64 paths of nested or sequential
read-free Boolean `if` statements whose bodies contain `Pass` or direct writes to the current
receiver. Each path carries its own heap version, assumptions, obligations, and initialized-field
set, and every `Ensures` is checked per exit. A field promised by `Acc(self.field)` but initialized
on only some paths produces a refutable initialization-permission VC; an unpromised missing field
refuses. The exact zero-argument builtin `object()` is accepted only as a fresh non-null opaque
reference stored in an inferred opaque field. Other calls, field reads, complex receivers, and
ordinary-method conditional effects remain outside this initial constructor slice. Integer unary
minus is lowered to the typed VC negation term. Together these rules exactly cover the pinned
`test_definedness.py` diagnostics and are part of the v49/v43 atomic fragment.
The constructive formal slice contributes 13 named constructor-`if` theorems in
`formal/Maledictus/HeapControl.lean`; the release tree contains 84 `HeapControl` and 448 total
theorem/lemma declarations, with no `sorry` or `admit`. These are IR-semantics results, not a claim
that Lean independently translates Python ASTs.

The 64-path constructor limit in the preceding original Version 49 release description is
historical. The current Rust constructor executor and the current Lean `HeapControl` model retain
the complete finite path list without that cutoff.

### Version 50 ordinary instance-method control flow

Version 50 routes an ordinary source instance method through the same guarded path engine
used by heap functions. The accepted method must be source-owned and nonexceptional, with a
`None`, `bool`, or `int` return annotation. Nested and sequential `if`/`else`, early returns,
`Pass`, scalar local assignments and initialized scalar annotations, assertions, and direct writes
to fields of the current `self` receiver execute over every finite disjoint state generated by the
source, without a fixed path-count cutoff. Conditions,
scalar assignments, field-write right-hand sides, and returns may use modeled field reads from
typed source receivers, but every read emits and must discharge the current path's permission VC
before execution continues. Writes remain limited to scalar fields of the bound `self` receiver
and must match the declared field sort.

Each path retains its own environment, heap and mask versions, assumptions, obligations, return
status, and path tag. A failed read or write obligation halts that path without applying the
effect; returned paths skip the continuation. Normal postconditions are instantiated against each
actual normal exit, and a reachable fallthrough from a non-`None` method emits an implicit-return
VC instead of being silently given the declared result type. Method summary construction walks
both arms recursively and exports the conservative union of direct `self` fields modified on any
path, so callers and overrides never frame a conditionally written field.

This slice does not admit constructors, properties, static or class methods, exceptional methods,
method calls, allocations, predicate actions, foreign-receiver effects, reference-valued returns,
or reference field writes. Those forms refuse rather than being
executed by the ordinary-method path rule. The direct/transitive release identities are v50/v44.
The constructive method slice contributes 9 named ordinary-method theorems; `HeapControl.lean`
contains 93 theorem/lemma declarations and the complete formal tree contains 457, with no `sorry`
or `admit`.

### Version 51 source-ordered builtin type-object aliases

Version 51 treats `Alias = int`, `Alias = bool`, and `Alias = object` as real immutable module
execution. The resulting binding is a class-sorted canonical builtin type object, not an ignored
typing declaration or an unconstrained scalar. A source-ordered bound-name prefix includes imports,
functions, classes, and earlier assignments even when their values are outside the scalar IR, so a
shadowed builtin spelling cannot be silently recovered as the canonical builtin. Duplicate targets,
annotated scalar/type-object mismatches, and unsupported runtime uses continue to refuse.

The scalar/transitive identities advance to v24/v18, and the heap/transitive identities advance to
v51/v45. The constructive alias model adds 5 named theorems: builtin terms have class sort, a
successful alias binds the exact literal, unrelated prior bindings are preserved, successful
execution records the target name, and a shadowed source spelling refuses. `HeapControl.lean`
therefore contains 98 theorem/lemma declarations and the complete formal tree contains 462, with
no `sorry` or `admit`.

### Version 52 total literal indexing of finite lists

Version 52 executes `values[index]` in module initialization when `values` has already lowered to
a finite, well-sorted list term and `index` lowers to a static signed-64 Python integer. Negative
indices use Python's `length + index` normalization in widened arithmetic. The frontend substitutes
the selected term only after proving the normalized position is in bounds; list elements may remain
symbolic because the finite spine and selected position are known. Dynamic indices, out-of-range
indices, empty untyped list literals, oversized list spines, and integer literals outside the
signed-64 frontend continue to refuse rather than becoming unchecked `listGet` terms.

The scalar/transitive identities advance to v25/v19; the heap identities remain v51/v45. The
constructive `ConstantListIndex.lean` model adds 13 theorems for exact selection, Python negative
normalization, result bounds, and each refusal boundary. The complete formal tree therefore contains
475 theorem/lemma declarations, with no `sorry`, `admit`, or `axiom`.

### Version 53 undeclared-exception diagnostic and blame closure

Version 53 turns an already-proved undeclared exceptional exit into the same source-boundary
diagnostic Nagini exposes. An uncaught, non-application exception is reported as
`exhale.failed:assertion.false` at the callable declaration, because that callable failed to close
its declared exit union. An exception generated by a partial operation retains
`application.precondition:assertion.false` and the operation's source location. Declared `Exsures`
outcomes and caught exceptions do not produce undeclared-exit diagnostics. Multiple proof paths
that produce the same code and boundary location are deduplicated without discarding their
underlying obligations.

The scalar/transitive identities advance to v26/v20; heap remains v51/v45. The constructive
`ExceptionalExit.lean` classifier contributes 10 theorems covering suppression, diagnostic code,
blame location, unknown-exit refusal, and finite output bounds. The formal tree now contains 485
theorem/lemma declarations with no `sorry`, `admit`, or `axiom`.

### Version 54 ordinary-method result provenance and native assertion state

An ordinary-method assignment from a class-qualified source call now retains the selected
summary's nominal reference result. The binding is replaced, not merged, so a later scalar-returning
assignment clears stale object provenance. A native Python `assert` in an ordinary method lowers
against the current environment, heap, and mask; field initialization and read permissions are
checked before its truth obligation is emitted.

Direct source-constructor return summaries also carry a narrow allocation fact into the call rule.
Only a proved, nonexceptional source allocator without custom allocation behavior establishes that
the result is non-null, distinct from caller references, exact-classed, and has zero pre-call
permission at each returned `Result()` field. This zero premise makes the permission-mask validity
proof for `Acc(Result().field)` constructive; it is never inferred for external, indirect, or
unverified results. Heap identities advance to v52 and transitive/combined source-heap identities
to v46. The exact conformance target is `issues/00266_3.py`. The constructive v54 model adds 22
theorems and brings the formal tree to 507 declarations without proof holes.

### Version 55 recursive pinned source closure and re-exports

Pinned heap conformance now resolves each absolute explicit source import into a finite recursive
provider graph. Resolution starts at the importer, chooses the nearest unambiguous provider below
the pinned suite root, rejects symlink traversal, verifies parent package initializers, and then
verifies providers in depth-first postorder. No provider summary exists after a missing edge, a
cycle, an unsupported initializer, or a refuted provider obligation.

Verified explicit imports are ordinary Python module bindings and may be re-exported through an
intermediate source module. The exported entry carries the leaf summary's canonical class or
callable identity; it is not renamed to the intermediate module. Package metadata constants whose
values are immutable opaque literals can execute without an exceptional exit, but remain outside
the solver environment and cannot be consumed by verified callable logic. Heap identities advance
to v53 and transitive/combined source-heap identities to v47. Exact upstream `00266_2.py` and
`test_imports_2.py` now pass through their real provider graphs; broad union coverage is 73/219
(33.3%) with no accepted mismatch. Nineteen constructive source-closure theorems bring the formal
tree to 526 theorem/lemma declarations without `sorry`, `admit`, or `axiom`.

### Version 56 finite dictionary keys, relative imports, and backend-qualified expectations

The scalar IR now has distinct finite-dictionary and dictionary-key-view sorts. A supported literal
is completely evaluated in source order, normalizes Boolean keys according to Python's integer-key
equivalence, retains the first insertion position for duplicates, and retains the last associated
value. `keys()` returns an ordered view supporting only the operations proved by this slice:
length, iteration, and membership. Treating the view as an indexable or sliceable list is rejected.
The scalar fragment advances to v27, checked-external scalar to v17, transitive and combined scalar
to v21, and the solver IR to `maledictus-scalar-vc/v18`.

Pinned source conformance resolves explicit relative `from` imports from the importer's verified
package context. Normalized targets must remain below the pinned suite root and pass the same
provider-before-consumer, package-initializer, symlink, cycle, and canonical-leaf-identity gates as
absolute imports. Completed providers are invoked modularly during module initialization, and
module-level assertions are retained as obligations. These changes advance heap to v54 and
transitive/combined heap to v48. Backend-qualified upstream expectations are parsed structurally
and excluded from Maledictus's backend-neutral expected set; malformed qualifiers still refuse.

Exact upstream `issues/00049.py`, `issues/00252.py`, and `test_relative_import.py` now match. The
curated gate is 79/79 and broad scalar/heap union coverage is 76/219 (34.7%), with zero accepted
mismatches. The Rust gate is 682/682. `FiniteDictKeys.lean` adds eight constructive theorems;
`SourceImportClosure.lean` adds thirteen relative-resolution and expectation-filter theorems. The
formal tree contains 547 theorem/lemma declarations with no holes. Python/frontend correspondence
and Rust-to-Lean refinement remain outside that theorem count.

### Version 57 effectful operators and reusable module heap summaries

The heap frontend now lowers direct integer field augmented assignment with receiver-once Python
evaluation order, separate read/full-write permission obligations, and an exact heap transition.
Effectful conditional expressions split the path after evaluating the condition, execute only the
selected branch, and join compatible Boolean/integer values without eagerly evaluating either
effect. Boolean-only source-call `and`/`or` follows the same selected-operand rule. Integer or mixed
value-returning short-circuit expressions remain fail-closed.

A proved local module heap function can be applied modularly only when it has one source-owned
nominal receiver, a complete normal-only direct-effect summary, no exceptional/default/captured
call path, and effect-free remaining arguments. Calls before proof, recursion, nominal mismatch,
and refuted or exceptional callees refuse. Scalar old-field postconditions read the caller's entry
heap rather than the post-call heap. Positive-literal modulo is represented using floor division,
so negative dividends retain Python semantics. These changes advance direct heap to v55 and
transitive/combined heap to v49; the VC vocabulary is unchanged.

Exact `test_operators.py` matches all five expected diagnostics. Broad coverage is 77/219 (35.2%)
with no accepted mismatches, and 698/698 Rust tests pass. `ModuleHeapOperators.lean` brings the
formal tree to 574 theorem/lemma declarations with zero holes. Those theorems establish the stated
finite transition algebra from explicit premises, not Python AST correspondence or Rust-to-Lean
implementation refinement.

### Version 58 homogeneous collection comprehensions

The scalar frontend and VC IR now represent list, set, and dictionary comprehensions directly
instead of boundedly unrolling an arbitrary symbolic source. The accepted source shape is one
synchronous generator with a direct-name binder over a homogeneous builtin list, zero or one pure
total filter, and pure total primitive result expressions. Structural comprehension fingerprints
produce hygienic solver symbols; binder validation rejects sort confusion and nested same-name
capture. A per-query solver timeout returns `Unknown`, never a proof.

For symbolic sources, quantified obligations constrain every valid index: unfiltered list results
have exact length and mapped values in source order; filtered list and set results have bounded
length and include every selected mapped value; dictionaries have bounded key length, selected-key
membership, and the selected final source occurrence supplies the last-write value. For concrete
sources, evaluation preserves list order/duplicates, deduplicates sets, implements dictionary
first-key-order/last-value behavior, and uses Python floor modulo and Boolean/integer key identity.
Missing dictionary lookup is partial and must discharge its membership precondition. Unsupported
generator counts, filters, binders, custom/effectful iteration, mutation, nested comprehensions,
result sorts, and key behavior fail closed.

This tranche advances scalar to v28, checked-external scalar to v18, transitive/combined scalar to
v22, and VC IR to `maledictus-scalar-vc/v19`; heap remains v55/v49. The four exact upstream
comprehension fixtures match all 16 expected diagnostics. Evidence is 83/83 curated fixtures,
81/219 broad union matches (37.0%) with zero accepted mismatches, and 716/716 Rust tests.
`CollectionComprehensions.lean` adds 35 theorem/lemma declarations, bringing the formal inventory
to 609 with zero holes. The Lean file proves the finite algebra only from supplied premises; it
does not prove AST lowering, Rust solver encoding, or Rust-to-Lean refinement. End-to-end
implementation-refinement coverage remains 0%.

### Version 59 canonical call binding

The scalar source-call path and the heap direct-name ordinary-method receiver path (including its
class-qualified adapter) now pass evaluated actuals through the shared
`python-call-argument-binding/v1` kernel. One signature representation distinguishes
positional-only, positional-or-keyword, keyword-only, `*args`, and `**kwargs` slots, including
typed defaults. The result contains exactly one formal-order cell per slot plus source-order
evaluation metadata. Fixed tuple stars retain element order; bound receivers occupy exactly the
first positional slot. Duplicate bindings, missing or excess arguments, unexpected keywords, and
type mismatches are structured failures. Dynamic `*` and all `**mapping` expansions refuse.

This capability name identifies the shared binding kernel, not complete integration at every
Python call seam. Imported scalar calls, module predicate calls, the heap module-function adapter,
base-constructor calls, and ordinary constructor calls still use their existing restricted/manual
adapters or fail closed for v59 syntax. Porting those seams to the kernel remains completeness
backlog. Arbitrary effectful receiver expressions and receiver chains also remain fail-closed;
receiver injection here does not claim support for those expression forms.

Abstract dictionary formals lower to stable per-variable Z3 key sequences and value arrays. This
allows length, membership, and guarded lookup premises without inventing a value for an absent or
otherwise unconstrained key. Abstract sets and unsupported dictionary component sorts still fail
closed. Current identities are scalar v29, checked-external scalar v19,
transitive/combined scalar v23, heap v56, transitive/combined heap v50, and VC IR v20. The kernel
source is hash-bound. The Lean binding model does not establish frontend correspondence or
Rust-to-Lean implementation refinement.

The final v59 evidence is 45/45 curated scalar fixtures, 42/42 curated heap fixtures, and 85/219
broad scalar/heap union matches (38.8%) with zero accepted mismatches. The Rust gate is 759/759.
The original v59 Lean gate builds 631 theorem/lemma declarations, 22 of them in
`CallArgumentBinding.lean`, with zero `sorry`, `admit`, or `axiom`.

The former 86-case bounded cross-model regression and fixed-cap expansion model are retired. They
are not compiled, generated, or reported as capabilities. The current call-binding evidence is the
cap-free Aeneas extraction and the universal allocator-aware Lean refinement described below.

The production kernel subsequently advances to `python-call-argument-binding/v3`. The current v3
implementation supersedes its original bounded form: checked machine-size additions report typed
count overflow, and every fallible buffer allocation reports its exact site and requested size.
There is no smaller application-level argument-count ceiling. The obsolete bounded v1 identity is
not an active capability.

The current post-v59 Python identities are scalar v32, transitive/combined scalar v26, heap v60,
and transitive/combined heap v54. They cover path-sensitive conditional definedness, static
sequence slicing and indexing obligations, quoted constructor-field annotations, exact string
values, fixed-tuple returns, and ordered structural matching over the bounded scalar pattern
fragment. That pattern fragment includes value/singleton patterns, captures, wildcards, OR/AS
composition, guards, canonical zero-argument `int()`/`bool()` class patterns, and
permission-checked qualified scalar values. Destructuring sequences or mappings, starred forms,
argument-bearing or shadowed class patterns, and every other unmodeled shape fail closed. Static
literal string slicing follows Python Unicode code-point semantics for
omitted, negative, clipped, and positive/negative-step bounds; dynamic bounds, symbolic strings,
zero steps, and string indexing remain fail-closed. These identities are not interchangeable with
the v59 fragments.
The v60/v54 heap slice also models exact finite function-local list mutation: static in-range
subscript stores and canonical unshadowed bound/unbound `list.append` update exact contents,
length, indexing, and membership. Mutation requires exhaustive rejection of direct and nested
aliases; dynamic indices, slices, symbolic lists, incompatible elements, custom dispatch, and
invalid arity fail closed. Canonical unshadowed `int.__add__` lowers to Python integer addition.
The broad classifier therefore reaches 96/618 exact matches, 522 refusals, and zero mismatches.
The scalar symbolic-list loop slice then raised the classifier to 97/618 exact matches. It proves
invariant establishment and preservation for an arbitrary
valid list index, and natural exit (including nested loops), while retaining explicit refusal
boundaries for iterable mutation/escape, abrupt or exceptional bodies, `Previous`, and possibly
unbound target reads.
The canonical dataclass slice raises the classifier to 105/618 exact matches. It recognizes
canonical `dataclass`/`field` imports, generates an
ordered constructor through the shared binding kernel, initializes typed fields from supplied or
literal/default-factory values, and rejects frozen-field writes. Unsupported decorator options,
inheritance, generated hooks, dynamic factories, and collection identity remain fail-closed.
The source-local alias and closed collection-specialization slice reached 109/618 semantic exact
matches at the IntEnum checkpoint. The finite module-list mutation slice raises that result to 110
semantic exact matches. The closed dataclass-defaults heap adds exact
`test_dataclass_defaults.py` for 111 semantic exact matches, 26 separate exact
production-typecheck rejections, 22 retained typecheck divergences, 459 refusals, and zero
semantic mismatches. The 26 typecheck rejections are
not semantic proofs and are not included in the ported percentage. Ordered immutable aliases for source
classes and supported `List[T]` annotations are resolved before lowering. A one-`TypeVar`,
one-specialization generic can specialize `T` to canonical `List[int]`; reassigned, forward,
cyclic, quoted, union, nested, multiple, dynamic, or runtime-escaping aliases remain fail-closed.
Entry modules receive `__name__ == "__main__"`; imported providers
receive their qualified module identity; both receive a source-bound `__file__`. These bindings are
immutable, are excluded from provider star exports, and produce an assignment-permission
obligation when rebound. APIs without a qualified module role leave metadata unavailable rather
than guessing.

Constructors begin with write ownership of their layout, but must assign every field before normal
return; reads before assignment are refused rather than hidden behind permission.
Nagini contract declarations are collected throughout a method body rather than being mistaken for
runtime statements, and module functions can consume constructor postconditions in checked field
assertions. Optional source-class fields may be initialized with the distinguished null reference.
A constructor may temporarily store null in a non-optional reference field, matching Python's
runtime semantics, but normal exit emits an implicit obligation that every such field is non-null.
Non-optional nominal parameters contribute their real source type and implicit non-null premise to
constructor assignments. Field identity uses source-class nominality and optional-null constraints,
while user-defined reference equality outside the narrow version 35 positive-assert rule still
refuses. These rules exactly reproduce Nagini's pinned
`issues/00056.py` diagnostics.
Version 10 resolved non-optional source-class annotations on module-function and method parameters
and method returns. Method summaries retain those nominal identities instead of collapsing every
object to the VC reference sort. A call accepts the actual class only when it is the declared class
or a proved source subclass; method bodies and call contracts select the field layout from the
nominal receiver expression. This permits contracts such as `Acc(cell.value)` on a class-typed
method parameter without treating `cell` as `self`. Module functions import their `Requires`
permission/value facts, check method-call preconditions, and prove `Ensures` and `Assert`
expressions against the source-resolved receiver layout. Explicitly annotated `int` and `bool`
locals are immutable single-assignment bindings. A single expression that reads fields through
receivers from different class layouts still refuses; the frontend does not choose whichever one
layout happens to make the expression type-check.
Exact literal fractions such as `Acc(self.field, 1/2)` permit reads but cannot establish a write.
Writes frame every other declared field on the same receiver.
Version 9 added source-defined single inheritance. It derives inherited layouts and method and
constructor summaries, proves override preconditions are not strengthened and postconditions are
not weakened, and refuses widened override write frames. A zero-argument `super().__init__(...)`
call applies the verified direct-base constructor summary to the same receiver and advances the
heap. Exact `isinstance` checks are decided only for locals created by a known source constructor;
static annotations on parameters never masquerade as exact runtime classes. Multiple or dynamic
bases, general `super` dispatch, and framing across potentially aliased receivers still refuse.
Version 10 additionally checks behavioral override signatures using contravariant parameter types
and covariant return types over that exact single-inheritance graph; scalar types remain invariant.
Version 11 separates pre- and post-call permission masks while checking overrides, so fractional
permission contracts can consume permission without the pre-state falsely proving the post-state.
It distinguishes permission failures from value-condition failures at their original source
clauses. Pass-only source exception classes rooted at built-in `Exception` form a nominal hierarchy;
method `Exsures` summaries may narrow exception types covariantly. Primitive literal method defaults
are also checked for dynamic-dispatch compatibility. These rules reproduce all eight diagnostics in
Nagini's pinned `test_behavioural_subtyping.py` fixture.
Version 12 made direct method calls apply the verified callee's declared `Acc(...)` consumption and return effects
to a fresh caller permission-mask version. The call proves its preconditions in the old mask,
proves that the pointwise transfer leaves every known field mask within `[0, 1]`, and uses the new
mask for all later reads, writes, and postconditions. The SMT transition accounts for aliasing
between one consumed and one returned receiver per field. Contracts with multiple same-field atoms
on either side still refuse because their separating-conjunction sums are not yet modeled.
Version 13 adds constructor-exit non-null invariants and retains nominal constructor-parameter
types during field inference. Version 14 verifies source-owned direct-field `@property` getters and
uses the resolved backing field for value and permission reads, including inherited properties.
Direct-return `@Pure` methods retain their checked body equation as a callable result fact and are
permission-read-neutral. That equation participates in behavioral override checks; property
overrides that redirect storage and method/property shadowing refuse. Arbitrary descriptors,
setters, and computed property bodies remain outside this fragment. Source summaries also compute
a transitive field-write set from verified bodies. A call advances the
heap when that set is nonempty and frames only fields outside it. This fragment is not advertised as
general class support. Heap method bodies containing `raise` still refuse. Optional nominal method
types, nominal result propagation through arbitrary locals, and nominal heap signatures in
external stubs remain explicit refusals.
The separate `nominal-reference-contracts/v4` fragment verifies pass-only source classes used as
nominal types, non-null and `Optional` parameters, the distinguished null value, `is`/`is not`, and
implicit type preconditions at source-function calls. Unrelated non-null classes are disjoint;
unrelated optional classes can alias only at null. The fragment refuses inheritance, structural
subtyping, user-defined equality, and arbitrary reference-producing expressions rather than
collapsing them into an untyped pointer model.
The `checked-external-scalar-contracts/v26` fragment extends scalar modular calls across one
explicit environment boundary. An overlay binds a requested adapter and dotted provider module to
a source-root-confined contract file. Only fully annotated `@ContractOnly` declarations with
leading `Requires`/`Ensures` and a non-executable body are accepted. The adapter must use explicit
`from module import symbol` bindings, cannot shadow imported callables, and must prove every
precondition. Provider import and contract conformance are recorded assumptions; they are never
described as source proofs. External `Exsures` requires the explicit
`declared-by-exsures` policy; the adapter must handle or propagate every typed branch. Pass-only
custom exception declarations form a checked nominal hierarchy; an adapter can import a base and
catch a declared subclass outcome, and the result records declared classes separately from
exception outcomes. Serialized custom exception types use module-qualified nominal identities,
and composition refuses same-spelled types from distinct providers until Python alias semantics
are modeled explicitly. The protocol also hashes the contract, executable,
compiled frontend source bundle, and compiled kernel source bundle.
The `transitive-source-scalar-contracts/v33` fragment applies the same modular call rule to actual
source-owned modules. Paths below `source_root` map to conventional dotted module names. Before a
callee contract is available to an importer, Maledictus recursively proves every callee body and
its own dependencies. A refuted or unsupported dependency exports nothing, and import cycles
refuse. Each resolved edge and provider hash is serialized in `source_imports`; a collection of
independently proved files is not silently treated as a composed source DAG.
The separate `checked-external-nominal-reference-contracts/v4` fragment parses pass-only provider
classes into module-qualified identities and checks object-valued parameters and returns at the
adapter boundary. It proves non-nullness only for a non-optional return annotation, preserves
`Optional[T]` as nullable, and rejects aliases or name collisions that would erase nominal
identity. These summaries do not yet carry fields or heap permissions.
`transitive-source-nominal-reference-contracts/v4` uses the same recursive, no-summary-before-body-
proof rule as the scalar source resolver. Nominal identities originate at the declaring dotted
module and survive every exported source summary. The combined external variant is
`transitive-source+checked-external-nominal-reference-contracts/v4`.
The heap frontend also executes an immutable scalar subset of module initialization in source
order. Each method and constructor summary owns its captured `int`/`bool` environment rather than
consulting a caller or containing subclass. Function entry first erases every lexically local name
from that environment and then installs receiver and parameter bindings. This represents Python's
whole-body local-name rule and keeps inherited provider summaries independent of importer globals.
Mutable globals, reference globals used by callable logic, and general calls during initialization
are explicit refusal boundaries.

Version 17 layers a source-ordered passive namespace over that environment. Class docstrings,
pass-only declarations, and immutable scalar class constants are verified at definition time.
Unresolved bases and class-body globals become source-located false obligations and terminate the
remaining module prefix. Empty-class instances may be bound only as opaque passive references;
because those bindings are deliberately absent from callable environments, they cannot fabricate
nominal types, fields, or effects.

Version 18 adds source-ordered primitive callable summaries for effect-free `int`/`bool`
functions. Module-initializer calls resolve both globals and transitive callees from the namespace
visible at the call, so a later declaration cannot retroactively repair an earlier failed
initializer. Successful post-initialization and imported calls instead use the declaring module's
sealed scalar environment. Recursion, heap effects, unsupported partial expressions, wrong arity,
and argument/result sort mismatches refuse rather than being abstracted as pure calls.

Version 19 executes zero-argument, heap-neutral source constructors at module scope. Direct and
transitive primitive calls in the constructor resolve against the scalar and callable prefix at
the outer call statement. Each successful call emits a non-vacuous module obligation; a missing
call-time dependency emits one false obligation at the outer constructor call and halts later
module initialization. Constructors with field effects remain an explicit refusal until the
module executor carries a real heap state.

Version 20 adds typed module-dispatch summaries for a source function that accepts one nominal
base-class value and returns a zero-argument, scalar, effect-free instance-method call. At each
top-level invocation, the ordered executor enumerates every currently defined source subclass,
resolves its effective override body, and requires the directly returned immutable global to
exist with the declared result sort at that exact source prefix. Later subclasses cannot affect an
earlier call; a newly defined override with a not-yet-defined global refutes the outer call and
halts the module. Contracts, heap effects, nontrivial constructors, method arguments, and more
complex override bodies remain fail-closed rather than being silently summarized.

Version 21 distinguishes eager bare nominal annotations from deferred quoted annotations during
ordered module execution. A bare parameter or return annotation must name a class already present
in the source prefix at the function statement; a quoted class name is checked against the final
source-owned class set but does not require that class at definition time. The finite body fragment
proves exact scalar-literal returns and effect-free zero-argument constructor returns. A missing
eager annotation emits one false obligation at the function definition and halts the module.

Version 22 adds a distinct static-method receiver kind. Static methods verify all declared
parameters without inventing `self`, prove their executable return and postconditions, and
participate in the existing solver-checked override implication. Changing between static and
instance receiver kinds across an override is rejected. Calls through an instance preserve
Python's static-method arity.

Version 23 resolves class-qualified static calls against the verified source class table. Both
`A.f(...)` and inherited `B.f(...)` use the selected static summary without adding an instance
argument, and their preconditions, postconditions, permission transfers, and return types compose
through the existing call rule. A class-qualified call to an instance method fails closed because
no instance receiver exists. Dynamic `@classmethod` receiver semantics were a separate
unsupported feature in that version.

`transitive-source-heap-contracts/v48` carries verified class layouts, constructor contracts, and
typed method summaries through the recursive source resolver. A summary is available
only after every source method obligation has passed. Imported constructor postconditions extend
the caller mask, and imported method calls prove their `Acc` preconditions against that mask.
Source method bodies contribute exact direct and transitive receiver-field writes, so only
unmodified fields are framed across a call. Version 4 preserves source nominal parameter and
return identities on those method summaries and checks subtype calls and override variance across
a source import edge when the participating canonical classes are explicitly imported. Version 5
also carries source exception/default/permission override metadata. Version 6 applies non-neutral
permission effects across verified source edges with the same versioned-mask transfer and validity
obligations as an in-module call.
Version 7 also carries field optionality and nominal constructor-parameter types, so imported
constructor summaries preserve the same non-null exit semantics.
Version 8 carries verified property-to-field bindings and direct pure-result equations across
source edges with the same shadowing and override checks as an in-module class. Version 9 carries
verified direct-return computed getters and single-field setters, including their permission
contracts, heap effects, and property result equations. Chained self-returning property receivers
remain source-typed; unsupported descriptor bodies refuse.
Version 17 additionally carries class-qualified static dispatch only after the selected static
method body and inherited receiver-kind obligations have proved.
Version 19 additionally exports verified instance-predicate summaries and their framed permission
locations, dynamic class receivers, inherited immutable class constants, and supported
class-receiver static calls. Those facts cross a source edge only after the provider's predicate
bodies, fold/unfold uses, classmethod body, and override obligations prove.
Version 20 also exports verified top-level predicate summaries. Their typed argument list,
argument-keyed token identity, body formula, and positive fractional permission footprint remain
source-bound across an explicit canonical import; an unproved provider exports no predicate.
Version 21 makes modular predicate ownership fail closed until predicate tokens and folded-body
capacity are first-class method/constructor call effects. A modular method call refuses a
predicate-ownership precondition and any predicate postcondition for a non-fresh object.
Constructor and direct-base-constructor calls likewise refuse predicate ownership required from an
existing caller object or returned for a non-fresh object. A constructor or dynamically
constructing classmethod may return a folded predicate only for its newly allocated result; that
fresh-result exception is checked in the Rust frontend and is not yet a Lean correspondence
theorem.
Version 22 exports the version 28 constructor-result field slice only after every source constructor
in the finite dependency graph has proved and the graph is acyclic. Imported/external constructor
results, custom allocation anywhere in an effective `__new__` chain, metaclasses, direct or inherited
exceptional constructors, and cycles do not acquire a source summary.
Version 23 carries version 29 contextual conjunctions through verified source summaries without
adding an effect assumption: every operand must still belong to the pure contract-expression
subset and lower independently in the provider's source-bound environment.
Version 24 carries version 30 nominal field-chain and direct-property return metadata only from proved source summaries.
Import boundaries preserve the resolved non-optional value class and subtype facts; they do not
turn dynamic, unresolved, optional, or unchecked external accesses into source proofs. The
combined checked-external variant retains its explicit provider assumptions.
Version 25 carries version 31 direct-field `Old` identity summaries only after the provider proves
entry and exit permissions and exports a complete transitive modification set excluding the field.
Each consumer invocation supplies fresh caller entry/exit heap and mask versions. The combined
external variant does not convert an external `Old` clause into a verified source summary.
Version 26 carries version 32 direct result/current-field identity or nonidentity only after the source
provider proves the exact nominal/reference type, exit permission, unique terminal normal return,
and returned-reference equality. Consumers rebind the result, receiver, exit heap, and exit mask.
The combined external variant retains its checked-provider assumptions but does not invent this
provenance for an external contract-only method.
Version 27 carries version 33 canonical late-bound class dependencies across a source edge only
after the provider module has proved and completed initialization. A consumer cannot satisfy a
provider dependency with a same-spelled local class, and the combined checked-external variant
does not manufacture dependency completeness for an external contract.
Version 28 carries version 34 reference-chain metadata only from proved source members. Provider
identity, direct result-field provenance, exact non-optional nominal types, permission effects, and
complete modification sets remain bound to the source summary. Checked-external or inherited
external members cannot be relabeled as source-proved chain hops; the combined variant retains its
other explicit provider assumptions without using them for version 34 provenance.
Version 29 carries version 35 identity-sufficient positive reference-equality assertions only from
proved source metadata. Canonical source class/MRO identity, exact source-allocation provenance,
raw-field origin, nominal non-optionality, current permission reads, and the already-discharged
identity fact remain bound across the source edge. The combined checked-external variant cannot use
an external class, field, equality override, nominal type alone, or provider assumption to satisfy
the version 35 rule.
Version 30 carries version 36's independently exact right-hand equality evidence only from a proved
source provider. The left remains a named exact source construction, while the right remains a
source name or raw permission-checked field chain. Provider-qualified exact runtime classes,
complete source/object MROs with no class-scope `__eq__` or `__init_subclass__` binding, and every per-hop raw-field
receiver premise are preserved across the source edge. The combined checked-external variant may
retain its ordinary heap assumptions, but it cannot manufacture exact source allocation or
source-MRO evidence for this equality rule. Lean models that finite summary/premise boundary rather
than import resolution or Python equality correspondence.
Version 31 carries version 37 standalone nested-call metadata only from proved source members.
Canonical receiver/argument reference-chain provenance, non-optionality, normal-only Unit terminal
summary, exact one-parameter signature, complete effects/modification sets, and source order remain
bound across the import edge. The consumer still evaluates receiver then argument and applies the
terminal summary only to their saved caller terms and post-argument versions. No import summary may
add a nonaliasing premise. The combined checked-external variant cannot promote external chain or
terminal members into this source-only rule. Lean models the transition/premise composition rather
than Python/import correspondence or summary truth.
Version 32 carries version 38's complete normal summary and transitive modification metadata needed
for finite caller-root frame instantiation, plus the canonical source provenance needed by the
orientation-specific raw-left/exact-name-right identity rule. Caller roots remain consumer-local;
the provider summary does not invent or enumerate them. A consumer frames only typed source fields
whose names are absent from the complete set and may emit the equality only after current
permissions, exact per-hop source facts, clean MROs, and identity all prove. The combined
checked-external variant cannot turn provider assumptions into source root/member/equality facts.
Lean models this finite summary/premise algebra rather than import/Python correspondence, semantic
framing, modification completeness, or equality dispatch.
Version 33 carries v39 source reference-identity summaries only after their exact pure signature,
body, totality, neutrality, canonical nominal identity, and source binding prove. Local consumers
use the exact callable/class prefix at the call; imported consumers require the canonical source
provider to have completed initialization. Application preserves the already-evaluated argument
term, actual nominal provenance, heap, mask, assumptions, and obligations across the import edge.
The combined checked-external variant cannot promote an external identity-function contract into
this source proof. Lean models only the sealed-summary, call-time-availability, neutral-transition,
and refusal algebra from supplied premises, not Python/import correspondence or provider truth.
Version 34 carries v40's reverse-orientation bilateral equality premises across proved source edges.
The raw left chain's final exact runtime class, verified allocator, normal-only constructor, complete
source/object equality MRO, and every current per-hop permission/exact/plain-source fact remain
canonical source evidence. The exact constructed right name retains its own normal allocation and
clean MRO. The combined checked-external variant may retain unrelated provider assumptions but
cannot manufacture either operand's exact source provenance or clean source MRO. Lean models only
the premise/identity-disposition algebra, not import resolution, Python equality, or frontend
correspondence.
Version 35 carries v41's canonical verified-source or hash-bound checked-external nominal/subtype
metadata and ordinary-versus-pure method
summary kind through proved source edges. Conditional locals and their `ite` terms remain
consumer-local; an import summary neither invents a branch join nor grants permission. Optional
receiver calls still prove non-nullness before applying the imported method's own permission/effect
summary. A checked-external catalog identity may participate in the effect-free type join, but the
combined variant cannot turn that join into source provenance or receiver-call evidence. Lean
models only the finite join/gate algebra, not import/frontend/Python correspondence.
Version 36 carries the canonical verified-source or hash-bound checked-external type-catalog
metadata used by v42 statement joins across proved edges. Statement execution and joined local
terms remain consumer-local. Checked-external catalog identities may participate in this
effect-free type join, but they cannot manufacture source allocation/construction provenance or
authorize an external call or field effect. Lean models only the finite join algebra from supplied
provider/frontend premises, not import correspondence or evidence truth.
Version 37 carries the canonical type metadata needed by v43's pure guarded branch expressions
through proved source edges. Guarded paths, early-return exits, and postcondition checks remain
consumer-local and are never exported as provider behavior. The combined checked-external variant
may supply hash-bound type-catalog identities but cannot authorize external calls, effects, or
nominal returns. Lean models only the exact finite path/return algebra from supplied premises, not
import/frontend correspondence or provider truth.
Version 38 carries v44's already-proved source constructor, method, field, transitive-write, and
permission-transfer metadata to a consumer. Guarded states and their concrete heap/mask versions
remain consumer-local. The source transition may execute on each guarded consumer state only after
the provider has completed and the ordinary and guarded executors select the same canonical
summary. The combined checked-external variant may retain unrelated provider assumptions but
cannot authorize v44's source-only effect dispatch. Lean models only the supplied transition and
exact finite-path algebra, not import/frontend correspondence or provider truth.
`checked-external-heap-contracts/v5` uses the identical `ClassShape` representation for a
hash-bound provider stub. It requires explicit fields, a constructor contract, contract-only
method bodies, and permission-neutral callable methods. Because a stub has no executable body and
v2 has no frame-clause syntax, every external method conservatively invalidates all declared field
values before applying its postconditions. Protocol output separates these classes in `heap_types`;
no external body is described as verified source. Version 5 carries the cumulative current heap
semantics and source-wellformedness gate; it does not weaken the conservative external-call rule.
The current Python fragments prove source symbol bodies after function entry; they do not claim to
prove module import execution. The response therefore reports `all-source-symbol-bodies`, never
`complete-file`.
