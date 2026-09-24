# Dagcert backend protocol

Dagcert invokes Maledictus as a separate, explicitly selected executable:

```text
maledictus verify --request request.json
```

For Python operation tasks, the current directly compatible fragment is
`dagcert-closed-typed-operations/v3`. It verifies source-imported `@operation` boundaries and frozen
dataclass input/outcome types from the real application file. Version 2 accepts finite outcomes via
`|` or an explicitly imported `typing.Union[...]` and primitive-only f-string interpolation without
opening a user-defined formatting call. Version 3 adds explicit `python_callable_bindings` for
callable-valued frozen input fields. Each binding identifies the operation, input record, field,
and an exact requested source path/symbol or checked external module/symbol. Maledictus derives the
provider signature and exit effects, composes exceptional exits through real handlers, and reports
consumer/provider hashes. A bare `Callable` annotation is never accepted as proof of provider
identity or totality. Multiple bound callbacks may compose through single-assignment typed
primitive locals; callback values themselves cannot be aliased, stored, mutated, or returned.
Operation records, outcomes, locals, and callable signatures admit `float` alongside `int`, `bool`,
and `str`. The closed total float subset includes literals, unary signs, addition, subtraction,
multiplication, and comparisons. Division and other potentially exceptional or unmodeled numeric
operations remain refused. Same-type primitive local reassignment is accepted, including values
updated on one branch; type-changing reassignment and callable rebinding remain refused.
Dagcert must require that fragment in
the returned file result; a generic `proved` status or a different fragment is not interchangeable.
Dagcert selects it with `--proof-backend maledictus`, `--proof-backend-executable`, and
`--proof-backend-sha256` on lint, issue, and verify. Nagini remains the default. The integration
independently hashes the executable before launch, validates the complete response identity and
exact source/file/symbol bindings, and never falls back after a refusal. External callable
providers require an existing checked scalar overlay with a fixed primitive signature; external
preconditions and non-scalar provider types remain refused.

On Windows, the `gh-release` Z3 build is dynamically dependent on `libz3.dll`; invoking the raw
Cargo output without that DLL fails before Maledictus can emit a diagnostic. Build a callable
standalone directory with
`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/package-windows.ps1`. It places
`maledictus.exe`, the pinned Z3 runtime, the pinned TypeScript compiler/bridge, a captured
`capabilities.json`, and a SHA-256 manifest of every packaged file together under
`.cache/release/windows-x86_64` by default. Node remains an
explicit hashed runtime dependency for TypeScript and checkJs JavaScript proofs. Dagcert must select the packaged executable and bind its reported
executable/kernel identities; it must not search Cargo build directories or mutate `PATH` during
verification.

The request schema is `maledictus-verification-request/v4`. It carries the source root and
fingerprint, the proof obligation, source-relative files and symbols, their languages, and explicit
external-contract overlays plus concrete Python callable provenance edges. Maledictus reads and
hashes source and stub files itself and derives callable contracts from them; a caller cannot
provide a trusted signature or effect summary.

Each Python overlay names an exact requested adapter, an external dotted module name, and a
source-root-confined `@ContractOnly` stub. The stub may contain only fully annotated scalar
signatures, `Requires`/`Ensures`, and a final `pass` or ellipsis. Maledictus verifies that the
adapter explicitly imports declared names, type-checks calls, proves call-site preconditions, and
uses postconditions modularly. It hashes the stub and reports the remaining assumption explicitly:
the environment-owned provider imports successfully and conforms to that contract. The request
must state an exception policy. `"assume-no-exception"` is accepted only when the contract has no
`Exsures`; `"declared-by-exsures"` requires at least one typed exceptional outcome, propagates
those branches to the adapter, and assumes no outcome outside that finite union. Absence or a
policy/contract mismatch refuses. The provider implementation is not represented as verified
source.

The response schema is `maledictus-verification-result/v7`. It reports `proved`, `refuted`, or
`refused`, exact file hashes, verifier version, proof obligation, and diagnostics with stable codes
and optional source locations. `external_contracts` retains each module, adapter, stub hash,
exported functions, checked exception classes, actual `Exsures` outcome types, and assumption
scope. `nominal_types` separately records module-qualified user-defined value types exported by
object/reference contracts. Custom exception identities are module-qualified; built-in exception names remain
unqualified. `source_imports` retains each verified importer-module-
provider edge, the exact imported symbols, and the provider source hash. Exit status zero is
reserved for a completed proof. Exit
status 1 means the claimed property was refuted, 2 means the request was understood but proof was
refused, and 64 means malformed invocation or input.

Every well-formed verification attempt also reports `verifier_identity`: SHA-256 digests of the
running executable, the exact Python frontend source bundle compiled into it, and the exact
kernel/VC/solver source bundle compiled into it. A backend that cannot read and hash its running
executable refuses the proof. Dagcert must retain these identities and every external contract
hash; the version string alone is not a verifier identity.

The separate `capabilities` document distinguishes finite cross-model regression cases from
universal implementation refinements. Its current `implementation_refinements` entry is derived
from the embedded, hash-checked Aeneas/Lean artifact and applies only to production
`call_binding::expand_actual_items` under the stated String/Int total-identity specialization.
Dagcert must not reinterpret that scoped entry as proof of parameter binding, another verifier
kernel, another value specialization, or the whole backend. The entry also carries its axiom audit
and remaining allocator TCB.

Version 5 additionally requires `python_typechecker` on every Python issuance. It records the exact
strict-mypy version and profile, installed package closure, Python runtime executable and complete
runtime bundle, configuration, and contract-support hashes. Analysis-only APIs do not emit this
identity and cannot produce a v5 result. Dagcert must validate and retain the complete identity;
accepting a missing field or treating it as optional would discard the compile-time type gate.

Request v3 also supports the bounded `python-to-js-primitive-total/v1` composition. An explicit
`cross_language_bindings` entry binds one requested Python caller to one requested TypeScript or
checkJs export. The pinned TypeScript compiler is authoritative for the provider parameter and
return types and its complete modeled outcome graph; types repeated in the request are audit
assertions and must match that compiler-derived signature exactly. Maledictus derives an exact
Python interface from the compiler result, gives that interface to the same strict pinned-mypy
issuance gate as the caller source, and then verifies that the requested Python function actually
makes the declared direct call. The provider is part of this composed proof edge rather than an
independent successful file proof.

This first mixed-language boundary admits only `bool`/`boolean`, `str`/`string`, and
`None`/`void`, with a pure total provider body. It refuses JavaScript `number` as Python `int`,
missing or ambiguous exports, unrequested endpoints, mismatched signatures, call cycles,
exceptional outcomes, mutation or external effects, binding escape, and unmodeled values. The v6
response retains both source hashes, both checker identities, the generated-interface hash, the
compiler-derived signature, and the exact composition scope. A certificate must verify and bind
all of those fields.

Each verified file names the exact proof fragment used. Proofs and refutations discharged through
SMT also report the runtime solver name/version, Rust binding version, and language-neutral VC IR
version. Dagcert must retain and bind this metadata in its certificate; it must not infer a backend
or fragment merely from a successful exit status.

A TypeScript or checkJs JavaScript proof additionally reports `typescript_toolchain`: pinned
compiler version, a deterministic SHA-256 over the complete compiler package, Node version, and
Node executable hash. Dagcert must bind this identity exactly. The current
`strict-typescript-closed-total-functions/v11` and
`strict-javascript-jsdoc-closed-total-functions/v11` fragments are compiler-type-checked but
intentionally small. They include direct, compiler-resolved calls within an acyclic verified
source-function graph and read-only primitive collection values. Collection access is limited to
canonical `.length`, fixed tuple indices, and array indices whose compiler-visible `undefined`
case is handled directly with `??`. Version 5 also carries a typed outcome graph for explicit
primitive throws, catch-all `try/catch`, and acyclic source-call propagation. Rust recomputes the
requested roots' exits and refuses an uncaught outcome at its throw or call site. Neither fragment
implies support for mutation, methods, callbacks, async behavior, external/indirect calls, or
arbitrary JavaScript or TypeScript effects.
Version 6 additionally admits flat primitive source `const` records at a sealed private-helper
boundary. The source-bound compiler bridge establishes source-literal provenance from the AST;
Rust independently validates the provenance tag, exact formal field shape, and call compatibility.
Arbitrary structural values cannot enter that boundary.
Version 7 additionally admits exhaustive terminal primitive `switch`: one evaluation of a
primitive discriminant, one or more unique same-typed literal cases, exactly one final `default`,
and modeled terminal exits in every arm. The source-bound bridge establishes the AST ordering and
Rust validates the schema-v4 node and recomputes every arm exit. Fallthrough, `break`, dynamic
labels, and continuation after the switch refuse.
Version 8 adds explicit schema-v5 `try-finally` composition for both catch-plus-finally and
finally-only statements. Rust independently applies ECMAScript completion precedence, preserving
the protected outcome only when the finalizer falls through and otherwise using the finalizer's
return or throw.
Version 9 adds schema-v6 source-owned callback composition for private helpers. The compiler bridge
binds each callback actual to one top-level function in the same verified module; Rust independently
checks the exact primitive signature, substitutes that provenance at every callback-invocation
node, composes return and primitive-raise outcomes, and detects callback-induced call cycles.
Abstract callback boundaries, external functions, closures, methods, callback escape or mutation,
higher-order forwarding, and async callbacks remain refused. A TypeScript function annotation is
never treated as evidence that an unknown callback cannot throw.
Version 10 adds compiler-response schema v7 for source-owned async functions returning exact
primitive `Promise<T>` values. Direct awaits and direct returned-promise adoption are distinct graph
nodes. Rust recomputes fulfilled/rejected outcomes and preserves the ECMAScript difference between
catchable awaited rejection and non-catchable adoption propagation. All async call edges are
cycle-checked. External or unknown thenables, floating promises, `Promise` combinators/races,
dynamic dispatch, captured mutable state, and async callbacks fail closed; cross-language v1
providers must remain synchronous.
Version 11 adds compiler-response schema v8 for closed source-owned class instances. The bridge
emits a canonical class catalog and flattens each constructor and method into the existing typed
outcome graph under a compiler-resolved `Class.member` identity. Rust independently requires the
matching constructor/method definitions, primitive boundary signatures, exact call arguments, and
closed ownership before composing return/raise or fulfill/reject outcomes. Only required readonly
primitive fields, direct construction, direct field reads, and direct final method calls are
modeled. Inheritance, accessors, proxies, mutation, instance escape, dynamic/external dispatch,
overloads, generics, and optional/rest/default parameters refuse.
The executed compiler bridge is required to byte-match the copy bound into Maledictus's verifier
identity; an environment override cannot substitute a different proof producer.

Dagcert must check both the language status and advertised fragments. Python currently reports
`closed-total-functions+safe-builtin-slices/v1`, `caught-callable-dataclass-boundaries/v1`, and
`scalar-nagini-contracts/v44`, `nominal-reference-contracts/v4`, plus the separate
`heap-method-contracts/v76` class-and-heap-function fragment and `checked-external-scalar-contracts/v26`
adapter fragment. `checked-external-nominal-reference-contracts/v4` checks pass-only provider
classes and object-valued adapter calls without claiming heap effects.
`transitive-source-nominal-reference-contracts/v4` proves those signatures through recursive
source module edges; its combined external variant preserves provider assumptions.
`transitive-source-scalar-contracts/v33` proves absolute source-owned
`from module import symbol` DAGs; the combined external variant is
`transitive-source+checked-external-scalar-contracts/v33`.
`transitive-source-heap-contracts/v64` separately proves recursive source class layouts,
constructor contracts, and typed method effects; it is not an external-provider assumption
fragment. The variant that also consumes checked external heap contracts is
`transitive-source+checked-external-heap-contracts/v64` and retains those provider assumptions.
The shared production binder advertises `python-call-argument-binding/v3`. It has no application-
level argument-count ceiling: source, expanded, and formal counts use checked machine-size
arithmetic, while each allocation has a typed failure outcome containing the exact site and
requested size. Certificates requiring v3 must reject the retired bounded binder semantics.

The current Python identities also bind source-level IOExists placement validation. A canonical
IOExists declaration may be a direct function- or loop-body statement; nesting it in another
IOExists lambda, returning it, or placing it under another statement refuses before its fresh
existential variables can escape their defining scope. Imported aliases and wildcard imports are
resolved against the pinned `nagini_contracts` export catalog, while lexical shadowing prevents an
unrelated callable from being reclassified as the contract primitive.

Scalar version 38 introduced Python
string-literal statements as inert execution. Only a function's leading literal is a docstring
that may precede its contract declaration prefix; a later literal remains inert at its actual
position and does not reclassify a following `Requires` or `Ensures`. Non-string expression
statements retain their previous executable/refusal behavior.

The scalar v23 module boundary includes a deliberately narrow value-producing class form: an
undecorated pass-only subclass of canonical, unshadowed builtin `int`. A direct call with one
`int`/`bool` positional argument lowers to that exact inherited integer value. Plain pass-only
marker declarations remain unavailable as scalar values, while custom bodies, decorators,
metaclasses, other bases, class identity/annotations, keyword or partial conversions, and binding
collisions refuse. Thus the issue 00261 result is a real numeric VC, not acceptance of an ignored
class body.
For every source class whose fields or effects are modeled or exported, the heap frontend now
requires a complete effective MRO ending at `object`. Every source entry must prove no effective
`__getattribute__`, `__getattr__`, or `__setattr__` override and no `__init_subclass__`
class-creation mutation. A checked-external entry remains a
separate hash-bound `checkedExternalHookFree` provider-conformance assumption after the
ContractOnly parser refuses those hooks and `__init_subclass__`; it is not source proof. A direct or inherited hook or an
unchecked external entry refuses before field/effect facts can enter a proof or source summary.
This heap-specific gate does not reject scalar-only code
whose classes are not modeled as heap state. Lean checks the finite frontend-premise/refusal rule,
not Python MRO correspondence or provider conformance.
Version 4 preserves source nominal method parameter and return identities and checks
subtype calls plus contravariant-parameter/covariant-return overrides across source edges. Version 5
adds source exception/default/permission override metadata. Version 6 additionally applies
non-neutral source method permission effects through versioned, kernel-checked caller masks;
alias-sensitive multiple same-field atoms still refuse. Version 7 preserves field optionality and
nominal constructor parameters, including the implicit non-null invariant at normal constructor
exit. Version 8 carries verified direct-field property bindings and direct-return pure-method
equations through source summaries. Version 9 additionally carries verified direct-return computed
getters and single-field setters with their permission and heap effects; unsupported descriptor
behavior still refuses.
Version 10 additionally binds immutable scalar module initializers and carries their values in the
source summaries consumed by downstream modules. Provider methods, properties, and constructors
never borrow same-named globals from an adapter module.
Version 11 verifies passive class declarations, class constants, and source-located definition
failures before making any source class summary available to Dagcert.
Version 17 additionally requires ordered module constructor calls, supported typed
virtual-dispatch prefix obligations, and eager/deferred annotation definedness to prove before a
source heap summary is exported. Static-method summaries additionally bind receiver kind and
override compatibility, and class-qualified static calls must resolve to one of those proved
summaries without synthesizing an instance receiver. Version 18 classmethod summaries bind a distinct dynamic
class receiver, preserve it through inherited class-qualified dispatch, and prove supported
`cls()` construction plus runtime-class postconditions. Predicate state and general reflective
class-object behavior remained unsupported in that version and therefore refused. Version 19
carries the v26 full-permission source-predicate fragment: verified framed `Acc` bodies, reserved
predicate ownership, atomic `Fold`/`Unfold` permission exchange, dynamic predicate selection,
inherited immutable class constants, and supported `cls.static_method(cls.constant)` calls.
Top-level predicates additionally support typed arguments, positive literal fractional `Acc`
footprints, argument-keyed ownership tokens, and `Unfolding(...)` with automatic refolding.
Recursive predicates, semantic reasoning over abstract predicate families, and general class
reflection remain explicit refusals. The source-wellformedness gate does distinguish canonical
`@Predicate @ContractOnly` declarations from concrete predicates: abstract predicates may occur
in specifications, but exact `Fold`, `Unfold`, and `Unfolding` operations reject them rather than
inventing a permission footprint.
Version 21/v27 also makes modular predicate ownership an explicit refusal boundary. Methods cannot
consume or return predicate ownership for existing objects through summaries, and constructors
cannot consume predicate ownership from caller objects. Constructors and dynamically constructing
classmethods may return a folded predicate only for their proved fresh result. The Lean predicate
definitions establish IR typing and algebraic fold/unfold reversal only; they do not prove frontend
correspondence, permission-mask validity preservation, imported provider identity, or this
fresh-result exception.
Version 22/v28 accepts `self.field = SourceClass(...)` only for a verified source-owned ordinary
`__init__`, an exact nominal field/result match, and an acyclic finite source-constructor graph.
Constructor postconditions establish the fresh result before the outer field write. Custom
`__new__` on the class or anywhere in its effective allocation chain, metaclasses, imported or
external constructors, declared exceptional outcomes on the constructor or a called base
constructor, nominal mismatches, and cycles must refuse. The Lean model checks the typed IR
transition, records frontend-supplied freshness facts, constructs and typechecks requested frame
equalities, and proves absorbing failure from frontend-supplied resolution premises. It does not
prove semantic arbitrary-receiver preservation or that arbitrary Python execution corresponds to
those premises or to the IR. The formal constructor summary separately requires source-owned
ordinary allocator provenance, normal-only completion, and an acyclic effective inherited/
explicit-`super()` dependency closure before its success rule applies.
Version 23/v29 additionally accepts nonempty contextual Boolean conjunctions only in the pure
contract-expression subset. Each permission/reference operand is lowered independently, must have
Boolean IR sort, retains its source position and heap reads, and is then joined with IR `and`.
Neither the Rust frontend nor the Lean lemmas claim equivalence for effectful Python operands,
truthiness conversion, or behavior that depends on short-circuit side effects.
Version 24/v30 additionally resolves nonempty nominal return chains made entirely from effective
typed fields, plus a single verified source property read directly from a named receiver.
Layout-owner selection remains separate from the field value class; every intermediate and final
reference must be non-optional, and the final value must satisfy the source subtype relation for
the declared return. A property inside a multi-hop chain, calls, scalar/unresolved values, dynamic
attributes, unverified descriptors, and optional results refuse. Lean checks the field-chain IR
and compatibility gate from frontend-supplied resolution and subtype premises, and models the
direct-property gate separately; it does not establish Python/frontend correspondence or
descriptor semantics.
Version 25/v31 additionally accepts only the direct normal postcondition
`self.field is Old(self.field)` for a non-optional effective typed reference field on a verified
source-owned non-constructor instance method. The old/current reads bind to distinct entry/exit
heaps and require separate entry/exit mask permissions. The complete direct-plus-transitive
modification set must exclude the field, and call-summary use rebinds all four versions to the
consumer invocation. Modified fields, constructors, nested or dynamic access, property/descriptor
targets, calls inside `Old`, exceptional clauses, and external contract-only `Old`
remain refusals. Lean checks the IR algebra and rebinding from frontend premises; it does not prove
Python correspondence, permission truth, complete modification analysis, or semantic framing.
Version 26/v32 additionally accepts only the direct normal postconditions
`Result() is self.field` and `Result() is not self.field` on a verified source-owned,
non-constructor instance method. The field and
result are exact, non-optional nominal references of the declared return class; method-type
construction rejects `Optional[...]` returns before this rule. The read uses the
method-exit heap and requires exit-mask permission. The provider frontend must prove a unique
terminal normal return with no executable successor and returned-reference equality on every
supported normal path; the negative form proves the negation of that same equality. Nominal type
equality alone does not establish identity or nonidentity. Call summaries
rebind the receiver, result, exit heap, and exit mask. Constructors, identity inside `Exsures`, properties,
optional/scalar/nested/dynamic/call-valued targets, external contract-only methods, and unsupported
control flow refuse. Lean checks an explicit IR/premise model and does not prove Python
correspondence, control-flow completeness, permission truth, or provenance truth.
Version 27/v33 additionally permits supported method contracts and bodies to name source classes
defined later, while preserving runtime definedness. The frontend resolves each name to a stable
canonical source identity against the sealed complete module and stores the complete dependency set
in the method summary. A module-initializer call succeeds only when every local dependency is in
that exact call-time class prefix, or when an imported summary's canonical provider has completed
initialization. Later definitions do not repair earlier calls; never-defined, shadowed, dynamic,
or unchecked-external names refuse. Bases, decorators, class-body code, and bare method
annotations retain eager definition-prefix semantics; only the existing quoted/deferred annotation
path defers. Lean checks this summary/application algebra from frontend premises;
it does not establish Python correspondence, dependency collection, canonical identity, or
provider-initialization truth.
Export must preserve declaration-time binding origin: only a nominal identity proved local to the
exporting module may acquire that module's qualifier. Imported field, parameter, return, base,
constructor-edge, and late-dependency identities retain their original provider qualifier; source
spelling alone is not an ownership proof. Required foreign shapes travel in a private canonical
dependency catalog for downstream layout/type resolution and are not exposed as importable symbols
of the intermediate provider.
Version 28/v34 additionally carries genuinely composed non-optional reference field/method chains.
Each zero-argument source instance call must have proved direct-field result provenance, exact
nominal result type, a normal-only summary, complete permission effects, and a complete modification
set. Heap and mask versions advance independently according to writes and net permission effects;
the next hop uses those exit versions. Effective member origin is checked separately from receiver
class origin, so a ContractOnly-inherited field or methodâ€”and a source method wrapping such a
fieldâ€”cannot become source-proved provenance. Arguments, properties/descriptors, optional or
scalar results, exceptional or unresolved calls, and incomplete effects refuse. Lean checks the
typed IR transition from explicit frontend/member-origin premises and does not establish Python
correspondence, provenance truth, permission truth, or semantic framing.
Version 29/v35 additionally accepts only positive ghost `Assert(left == right)` expressions where
`left` is a named, exact, normally completed verified source construction and `right` is a source
name or permission-checked non-optional raw source-field chain whose every receiver has independently
proved normal-only source-allocation provenance, exact source runtime class, and ordinary attribute
resolution in the current heap/mask. The
resolved left source MRO must be complete and contain no custom `__eq__`, external, unresolved,
cyclic, or dynamic entry. The frontend must first prove identity from the current assumptions;
only then does it lower the assertion, with identity also recovering the right operand's exact
runtime class, and every prior call/permission/transition obligation must already be proved. False
or unknown identity refuses this v35 slice rather than becoming a general
Python-equality refutation, and nominal right-side type metadata is never a substitute. Calls and state changes in
the ghost expression, `!=`, negation, `Requires`/`Ensures`, properties, arbitrary/non-exact left
expressions, external allocation, custom/dynamic equality, non-exact field receivers, and effective
`__getattribute__`/`__getattr__`/`__setattr__` interception refuse. Lean checks the typed IR and
explicit frontend premises/refusals; it does not prove Python equality semantics, MRO extraction,
permission truth, or frontend correspondence.
Version 30/v36 preserves that asymmetric syntax but adds an independently exact right-hand branch.
The left remains the named exact source construction; only the right may be a source name or raw
field chain. Both runtime classes and both complete source/object MROs must be proved, with no
class-scope `__eq__` or `__init_subclass__` binding. Every raw-field receiver retains current permission, exact runtime
source class, normal source allocator, and hook-free attribute-resolution premises. These facts
make `object.__eq__` the only possible dispatch on either side, so the identity VC may prove,
refute, or remain unresolved. The v35 identity-sufficient fallback remains for a nonexact right
operand and still cannot refute. General left chains, reverse/custom/external/dynamic equality,
properties, calls, optional/scalar values, other operators, and contract-clause contexts refuse.
Source summaries preserve these canonical premises; the checked-external combination cannot invent
exact source provenance. Lean checks the IR reduction from explicit frontend premises and does not
prove Python dispatch, MRO extraction, or frontend/import correspondence.
Version 31/v37 adds one standalone expression-statement call in a verified module heap function
whose receiver and sole positional
nominal-reference argument are independently accepted source reference chains and whose terminal
source instance method is nonexceptional, Unit-returning, and has exactly one required non-optional
nominal-reference parameter. Receiver evaluation precedes argument evaluation, and each threads the
current heap, mask, assumptions, and obligations; the terminal summary then consumes the saved
terms at the post-argument versions without re-evaluation. Aliasing is handled by rebinding the
complete summary to the actual terms, never by assuming they are distinct. Failure halts at the
receiver, static-terminal-validation, argument, or terminal-transition phase before any later
runtime phase. External/dynamic/optional/property,
keyword/default/multiple-argument, exceptional, non-Unit, class/method-body, and ghost uses refuse. Lean checks this
finite ordering/state-transition algebra only, not Python correspondence, alias analysis, exception
freedom, or summary truth.
It does not include a following raw-field-left `==` assertion; that expression remains a separate
frontend refusal, not a v37 obligation.
Version 32/v38 adds finite caller-root frames and one orientation-specific equality rule. A complete
normal source summary with a proved complete transitive modification set may frame only direct typed
fields of the caller's finite verified-source root inventory whose field names are absent from that
set. Modified, unresolved, checked-external, dynamic, exceptional, or incomplete entries refuse and
do not extend the frame list. The conservative name exclusion requires no nonaliasing assumption.

Only after those and all earlier obligations prove may the frontend accept
`Assert(raw_source_field_chain == exact_source_name)`. Each left receiver hop retains current read
permission, exact normal source provenance, and complete hook-free MRO; the right name retains exact
source-construction provenance and a clean source/object equality MRO. Existing assumptions must
pre-prove identity. V38 adds neither a refutation rule nor general operand symmetry, calls,
properties, external/dynamic equality, other operators, or contract contexts. Source summaries
carry complete modification/provenance metadata, not caller-local roots. The checked-external
combination cannot manufacture source facts. Lean checks only finite IR/premise/refusal algebra, not
frontend/Python/import correspondence, alias analysis, semantic framing, or equality semantics.
Version 33/v39 adds a dedicated source reference-identity wrapper in the direct argument slot
of the v37 standalone terminal call. Its sealed summary requires exact `@Pure`, one required
non-optional positional source-nominal `T` parameter, the same canonical non-optional `T` return,
exact `return parameter`, total normal completion, and heap/mask neutrality. Local binding uses the
exact call-time callable prefix, and the `Pure` decorator must resolve to the canonical imported
Nagini binding rather than merely have that spelling. An imported source summary and its canonical nominal dependency
require completed-provider/v33 availability. The argument source chain is evaluated once and its
exact term, actual nominal provenance, heap, mask, assumptions, and obligations pass through
unchanged before the outer Unit method is applied. Shadowed, unavailable, malformed, external,
optional/default/keyword, nested, ghost, and arbitrary pure-call uses refuse and cannot reach that
outer application. The combined external fragment cannot manufacture a source identity summary.
Lean checks the finite summary/availability/neutral-transition algebra from frontend premises, not
Python evaluation, lexical/decorator resolution, totality, canonicalization, provider completion,
argument-chain correctness, or summary truth.

V39 also conditionally frames fields on a caller object proved distinct from the receiver modified
by a normal verified source instance call. The accepted method summary must close supported direct
`self` calls and prove every executable write remains a direct field write on that same receiver.
Candidates are finite one-hop exact-constructor reference fields of typed local caller roots; all
root/candidate exact-class and plain/hook-free source-MRO facts, one-hop non-optional source
reference/normal-constructor metadata, and effective candidate-field source ownership are frontend
supplied. A solver-proved distinct candidate receives
pre/post field equalities even for names in the method's modification set. The saved pre-heap
candidate is the receiver of both reads, and the rule grants no permission and does not separately
frame the root edge. Same receiver, unknown aliasing, external/dynamic origin, or incomplete facts
add no conditional frame; the v38 name-based frames remain conservative. Lean checks this finite
conditional-frame algebra only, not freshness, alias, effect-closure, frontend/Python, or semantic
frame correspondence.

Version 34/v40 adds only the reverse-orientation bilateral branch for
`Assert(raw_source_field_chain == exact_source_name)`. Every raw receiver hop must already have a
current permission-checked read, exact normal source runtime class, and complete plain/hook-free
source MRO. The final raw value independently needs a verified source allocator, normal-only
constructor, exact runtime source class, and complete source/object MRO with no `__eq__` or
`__init_subclass__`; its nominal field annotation is insufficient. The right name remains one
normally completed exact source construction with the same clean equality MRO. Only under those
premises does the frontend emit the identity VC and allow the ordinary solver result to be proved,
refuted, or unresolved. Missing final exactness falls back only to v38's already-proved-identity
branch. Calls, properties, optional/scalar values, external/dynamic/custom equality, other syntax,
and general operand symmetry still refuse. The combined checked-external fragment cannot create
source exactness or source-MRO evidence. Lean checks the finite premise/lowering/disposition algebra,
not Python/frontend/import correspondence or the truth of allocation, permission, MRO, and solver
facts.

Version 35/v41 adds typed heap conditional values and optional receiver preconditions. A Boolean
condition is evaluated before two total effect-free branches. Supported equal scalar sorts, a
localized mixed `bool`/`int` join that converts the Boolean branch to `0`/`1`,
canonical same/catalog-subtype nominal joins, and validated nominal plus literal `None` lower to a typed
`ite`; the last is explicitly `Optional[T]`. Condition reads are unconditional; branches containing
heap reads or permission obligations refuse. The join preserves heap/mask without
creating permission, non-nullness, or exact runtime provenance. Effectful/exceptional branches,
properties/calls/constructors, incompatible types, unsupported nominal joins, and dynamic/unchecked
types refuse. Nominal catalog evidence may be verified source or hash-bound checked external; the
join invokes no external behavior and grants no source provenance.
This is the expression form `then_value if condition else else_value`; statement-level heap
`if`/`else` remains outside v41.

Before a direct zero-argument source method can consume an optional receiver, the frontend checks
`receiver != None`. Only a proved receiver exposes the method's own permission obligations and
transition. Refuted or unresolved receivers stop without those effects; ordinary methods map the
failure to `call.precondition`, while `@Pure` methods map it to `application.precondition`. The
exact Nagini null fixtures are conformance instances of this general rule. Transitive source
version 35 preserves canonical join/subtype and method-kind metadata, but conditional locals
remain caller-local; the combined external variant cannot manufacture source provenance or callable
evidence merely from a type join. Lean checks
only finite typed join, ordering, condition-obligation, and nonextension algebra, not Python/frontend/
import correspondence or evidence truth.

Version 36/v42 adds statement-level heap `if`/`else` for a state-neutral subset. Conditions are
read-free, call-free Booleans. Branches split assumptions by the condition and its negation and may
contain `pass`, scalar assertions, local scalar/validated-reference/`None`/v41-IfExp assignments,
simple initialized `int`/`bool` local annotations, and nested statement conditionals. Annotated
initializers are checked exactly, with only the localized `bool`-to-`int` coercion. Both exits must
be normal with the entry heap and mask unchanged;
calls, heap reads/writes, permission changes, contracts, returns, exceptions, and state divergence
refuse.

The join requires every local on both normal paths. It supports equal scalar sorts, localized
`bool`-to-`int`, canonical same/catalog-subtype nominal joins, and validated nominal/`None`
optionality. Sibling nominal LUBs and unchecked/dynamic values refuse. Hash-bound checked-external
catalog types may join because no provider behavior executes. Exact-runtime/source-construction
provenance is source-only and retained only for the identical term and canonical class on both
paths. The no-else path is the incoming state. Base obligations are retained once and branch
obligations retain their path assumptions; no branch assumption is made unconditional. Lean proves
only the finite IR split/join/nonextension algebra from supplied premises, not Python/frontend/
import correspondence, branch execution, subtype truth, or solver validity.

Version 37/v43 introduced a guarded path set from the first return-containing conditional through
the remaining body; earlier v42-pure conditionals may retain their exact typed local join. The
current executor retains every finite normal and returned state generated by the source and has no
fixed path-count cutoff. Every read-free Boolean split preserves independent
environment, assumptions, obligations, heap, and mask state under the condition or its negation;
nested conditionals compose by union and a missing `else` contributes the unchanged path. No path
is silently dropped or merged to manufacture a proof.

Early returns are accepted within the v42-pure branch grammar for heap functions whose declared
return remains `None`, `bool`, or `int`. After the existing localized `bool`-to-`int` promotion, a
typed, read-free, call-free return value moves its path
from the normal set to the returned set and independently instantiates/checks normal postconditions
under that guard. Returned paths skip continuation. Unit fallthrough becomes an implicit Unit
return; reachable Boolean/integer fallthrough refuses as `function-return-value-missing`.
Nominal/optional returns, calls, constructors, field reads/writes, permission effects, exceptions,
and branch contracts refuse. Transitive v37 preserves only the canonical metadata needed by the
pure branch expressions; it does not export path execution. Lean checks the finite path-set and
return algebra from supplied premises, not frontend/import correspondence or solver truth.

Version 38/v44 also activates the guarded path set for a conditional subtree containing a
supported source effect, even when there is no early return. The shipped statements are a verified
normal-only source constructor local assignment or source instance-method result assignment with
effect-free positional arguments and no keywords; a direct zero-argument Unit source-method
statement; and a direct typed-local plain source-field write with an effect-free, heap-read-free
right side. Every normal
path uses the same transition as the ordinary statement executor and carries its own resulting
environment, assumptions, obligations, heap, and mask into later statements. Returned paths skip
the transition and continuation. Normal, returned, and halted states are retained without a fixed
state-count cutoff, and differing state versions are never merged. A refuted receiver or call precondition retains its path-qualified failing
obligation, rolls heap/mask and pre-effect assumptions back, halts that path before later effects,
and remains in the path set.

Constructor freshness, method pre/post/frame and permission-transfer facts, and field-write
permission/frame facts are instantiated under the current path assumptions. A direct field write
also requires a statically non-optional source receiver with its non-null premise and checks exact scalar compatibility or a proved
same/subtype nominal assignment; an optional assigned value cannot enter a non-optional field, and
literal `None` requires an optional nominal field. Exceptional, dynamic, checked-external,
descriptor/property, predicate-ownership, unsupported call-shape, and unresolved typing cases
refuse. Transitive v38 exports only proved canonical source summaries; guarded execution remains
consumer-local. Lean proves the finite IR transition/batch/refusal algebra from supplied premises,
not frontend/import/Python correspondence, executor parity, permission/subtype truth, or solver
validity.

For v42-v46 execution, certificates use `formal/Maledictus/HeapControl.lean`: its recursive
executor creates the condition split, runs both blocks, threads each path through typed effects,
skips continuation after return/halt, retains the complete finite path list, and applies the single
function-bound postcondition list to actual exits. The former witness-bearing
`HeapStatementBranchTrace`, `GuardedHeapBranchResult`, and
`GuardedPathLocalSourceEffectRequest` APIs were removed rather than retained as theorem-shaped
adapters. Their Boolean closure/parity fields and caller-supplied exit states are not certificate
evidence. `HeapCallable.lean` remains authoritative for its
constructive type joins and field-write compatibility functions. AST lowering, summary truth,
subtyping, permissions, and solver validity remain explicit frontend/prover obligations.

Version 45 behavior adds canonical direct `isinstance(Name, SourceClassName)` to guarded heap
statements, opaque nullable `object` parameters, permission-checked direct raw-field returns, and
read-free Boolean/integer conditional expressions. Opaque objects carry no nominal/member or exact
source provenance and cannot be used as a receiver or nominal value before narrowing. The backend
refuses shadowed `isinstance`, non-name arguments, unresolved/external/incomplete targets,
nondefault metaclasses, `__instancecheck__`, compound conditions, and unsupported calls.

The formal catalog contains source class records with direct-base edges and declared fields. Lean
checks unique names, acyclic/resolved chains, computes subtype reachability and inherited field
lookup, and never accepts caller-supplied safe-class/subtype closure lists. Dynamic `isinstance`
constructs the exact nonnull/runtime-subtype predicate once. The true path narrows to a nonoptional
source nominal (preserving a known more precise subtype); the false path preserves metadata. A
no-effect same-term join restores the complete incoming binding. Raw-return requests contain only
receiver/field names: current environment, catalog field/type, heap term, and current-mask
permission VC are resolved internally. Refuted prerequisites halt only that guarded path.
Reference/class/effectful IfExp branches refuse. Python AST/catalog extraction and solver truth
remain frontend/prover premises.

Version 46 adds structural left-to-right `and`/`or` evaluation to that executable engine. Only
feasible left-true paths evaluate an `and` right operand, and only feasible left-false paths
evaluate an `or` right operand; skipped operands emit no call, permission, precondition, or result
obligations. Supported atoms are limited to canonical source-safe `isinstance`, scalar
comparisons, and checked source-pure scalar method calls. Method selection is computed from the
finite source catalog, and dispatch closes only for exact or source-constructed receivers. A
nonexact annotated ingress value is not silently restricted to catalog subclasses, so an open
dynamic dispatch remains unmodeled/refused. Exceptional, impure, external, unresolved, and
unsupported atoms fail closed.

Version 47 adds structural unary `not` over that path partition: it evaluates the operand once and exchanges
the feasible true/false exits without duplicating calls, permissions, halted states, or narrowing
facts. Read-free `bool`/`int` chained statement comparisons lower each operand once, compare
adjacent terms in source order, and conjoin the results. Chains containing calls, heap reads,
reference/class operands, or custom comparison behavior remain explicit refusals.

Finalization scans every actual modeled-exit obligation: one concrete refutation wins even if a
sibling path is unmodeled; otherwise an unmodeled reachable sibling blocks `Proved`. Reachable
non-Unit fallthrough becomes the actual implicit-`None` exit and emits its return/postcondition
mismatch under that path guard at the function line. Calls and final obligations are path-scoped
and instantiated once per evaluated call or actual exit. Lean constructs these IR transitions and
the counterexample-first disposition; AST correspondence, source-record truth/completeness, and
proof-kernel feasibility/VC dispositions remain explicit premises. The historical version 47 release advertised
`heap-method-contracts/v47`, `transitive-source-heap-contracts/v41`, and
`transitive-source+checked-external-heap-contracts/v41` across source, tests, formal documentation,
and conformance artifacts.

The current atomic heap release is `heap-method-contracts/v76` with transitive and combined
source-heap summaries at version 64. Version 71 adds finite source-nominal `typing.Union` receiver
dispatch. Every arm must resolve to a deterministic source method with one compatible canonical
call binding and neutral, nonexceptional effects. Actual arguments are lowered once, each arm's
postconditions remain separate guarded obligations, and a Pure caller requires every arm to be
Pure. A heterogeneous primitive result may leave the call only through a matching direct Union
return boundary. Missing, dynamic, external, exceptional, effectful, or binder-incompatible arms
refuse. Transitive version 59 preserves the same rule using verified source class catalogs; the
checked-external combination cannot turn an external arm into source-proved dispatch.

The generic boundary remains closed monomorphization, not type erasure: an unaliased module-level
`T = TypeVar("T")` and a one-parameter `Generic[T]` class must
have exactly one representable concrete scalar, source-nominal, or canonical `List[int]`
specialization. Direct `T` field/parameter/return annotations are substituted before constructor
and method obligations are generated. Ordered immutable module aliases for source classes and
supported `List[T]` annotations are resolved before lowering and cannot become runtime values. The
`TypeVar` declaration itself is absent from runtime module globals, captures, heap locals, exports,
and proof-kernel input. Rich declarations (bounds, constraints, variance, or defaults), dynamic
callees, rebinding/runtime use, forward/cyclic/union/nested aliases, unsupported annotation
positions, quoted direct `"T"`, and missing/multiple/composite specializations refuse without
exporting a proof. Direct v70 retains the closed, source-ordered `IntEnum` family:
canonical imports, unique integer-literal members, finite-domain construction and parameters,
numeric projection/equality, descriptor-preserving singleton identity, and enum-valued dataclass
defaults. It rejects aliases, hooks, inheritance, duplicate values, protected-name rebinding,
non-prefix or unbound `Requires`, out-of-order annotations/defaults, unmodeled module statements,
and imported/exported enum semantics. The complete IntEnum frontend source is included in the
verifier frontend-bundle identity. `formal/Maledictus/IntEnum.lean` proves the finite algebra, but
is not an extracted Rust/frontend refinement proof. Direct v70 also executes a bounded canonical
dataclass-defaults heap: factory-created lists receive distinct allocation identities, explicitly
supplied lists retain their identity, append is visible through aliases, immutable primitive and
IntEnum defaults are preserved, and frozen writes refuse. Its Lean file proves the constructive
heap/default/freshness algebra only and makes no extraction claim. Dagcert must require the
v70/v58 fragment identities before treating this
capability as available; an older certificate does not claim it. Direct v70 additionally binds a
source-ordered contract-position preflight into the frontend identity. Issuance runs strict mypy
first, then rejects misplaced Nagini primitives with a located diagnostic before semantic
lowering. It also checks `Result`, typed-result, and predicate declarations against the enclosing
source function's return annotation, finite body shape, and known source-call effects. Conformance
reports these source-wellformedness rejections separately from semantic matches. Direct v70 also
models source-nominal `Optional[T]` without a fabricated non-null assumption and bounded symbolic
typed-List loops with an explicit `list_pred` permission. Every such loop retains exhaustion and
arbitrary-element early-return paths; effectful or induction-dependent loop bodies remain outside
the certified fragment. The accompanying Lean algebra is constructive and model-only, not an
extracted Rust/frontend refinement. Conformance counts source-wellformedness rejections in their
own category rather than presenting them as
semantic proofs or typecheck matches. The corresponding Lean file models the finite context/order
and declaration-validity algebra only and is not an extracted Rust/frontend correspondence proof.
The declaration gate also resolves canonical `Inline` and `Opaque` decorators from the real source
binding environment. It rejects incompatible decorator sets, inline constructors, modular
contracts in inline functions, and source overrides crossing an inline boundary in either
direction. `Opaque` is accepted only with `Pure`; aliases are honored and rebound spellings are
not trusted. These remain source-wellformedness results rather than semantic proofs.
The declaration gate also rejects imports in function/class scope and runtime local aliases built
from canonical `typing` constructors, while preserving legal module aliases and ordinary
subscripts. Canonical `@Pure` declarations require a non-`None` return contract, at least one
reachable return, no exceptional declaration or direct raise, and no statically unreachable
statement following an unconditional exit. The conformance harness retains strict-mypy evidence
for overlapping missing-return failures but reports the more specific declaration diagnostic; it
does not send the invalid source to a proof backend.

The source-wellformedness gate also checks the operand boundary of `Fold`, `Unfold`, and
`Unfolding`. Their first operand must be a call whose real source binding is an `@Predicate`
declaration; an ordinary `@Pure`/runtime function, a boolean value, a rebound name, a predicate
alias that lost declaration provenance, or a dynamic call target is rejected with
`invalid.program:invalid.contract.call`. Canonical contract/decorator import aliases are resolved,
while definitely shadowed contract spellings receive no Nagini meaning. This is a rejection gate,
not a semantic proof of predicate ownership. `formal/Maledictus/PredicateContractCalls.lean`
records the finite call-shape/binding algebra only and explicitly is not extracted frontend
correspondence.
Canonical `@Predicate @ContractOnly` declarations are classified as abstract specifications.
They may occur in contracts, but `Fold`, `Unfold`, and `Unfolding` reject them because no concrete
permission footprint exists. Direct names and methods resolve only through final source bindings,
exact source-nominal parameters or `self`, and once-only source-class construction before use;
effective inheritance and concrete overrides preserve the actual predicate kind. Reassigned,
chained, ambiguous, or dynamic receivers fail closed. The constructive
`formal/Maledictus/AbstractPredicates.lean` algebra is model-only and is not an extracted
Rust/frontend correspondence proof.

The same frontend uses class-neutral module-function expression contexts. Contextual lowering has
priority, and a class-dependent scalar wrapper must derive its root from a typed receiver or class
literal. Selecting an arbitrary module class is forbidden, so Dagcert must not interpret a refusal
of an ambiguous expression as generic support or as a proved heap relation.

Version 49 additionally proved canonical `@Pure` scalar statement bodies and constructor
conditionals.
Reusable scalar summaries retain provider-qualified callable dependencies and immutable provider
globals, execute every finite read-free local/`if`/return path generated by the source, require
every path to return, and
collapse the result to typed `ite`. Constructor paths retain separate heap/mask/assumption and
initialized-field state; postconditions are checked at each exit, conditional permission exposure
is a real initialization VC, and missing unpromised fields refuse. Dagcert must preserve the path
tags and captured callable identities and must not merge branch heaps, reinterpret provider names
through a consumer, or treat the narrow opaque `object()` field initializer as general object
semantics. The pinned `test_definedness.py` result is the exact current target.
Maybe-defined locals carry their exact path guard and every later read emits a definedness VC.
Reachable non-Unit reusable-`@Pure` fallthrough uses the stable
`function-totality:implicit-return[:path:i]` identity and `function.not.wellformed` attribution;
ordinary heap-function fallthrough remains `postcondition:implicit-return[:path:i]`.
The historical slice's constructive Lean inventory is 13 named constructor-`if` theorems, 84 theorem/lemma
declarations in `HeapControl`, and 448 across `formal/Maledictus`, with no `sorry` or `admit`.
Those results start from frontend-produced IR and do not independently prove Python-AST
correspondence or source-layout extraction.

Version 50/v44 routes ordinary source instance-method conditionals through the same
guarded path executor. It accepts nonexceptional methods returning `None`, `bool`, or `int`, with
nested/sequential `if`/`else`, early returns, scalar locals and assertions, permission-checked
modeled field reads, and scalar writes only to the bound `self`. A failed access obligation halts
that path before the read or write is used; returned paths absorb the continuation; non-Unit
fallthrough emits a guarded false VC; and each actual normal exit receives its own postcondition
instances. Recursive summary collection unions every conditionally modified `self` field before
call framing and override analysis. Calls, construction, predicates, exceptional/static/class/
property methods, foreign-receiver effects, and reference results/writes refuse. There is no fixed
path-count refusal.
The formal boundary contributes 9 ordinary-method theorems and leaves the release at 93
`HeapControl` and 457 total theorem/lemma declarations, with no proof holes.

Version 51/v45 additionally executes immutable module aliases of canonical builtin type objects.
`Alias = int`, `Alias = bool`, and `Alias = object` produce exact class-sorted builtin literals.
The source prefix separately records every prior bound name, including imports and declarations
whose values are not represented, so shadowing fails closed. Dagcert must require scalar v24 with
transitive v18 or heap v51 with transitive v45 before relying on this capability. Five constructive
theorems bring `HeapControl` to 98 declarations and the formal tree to 462, without proof holes.

Version 52 adds total literal indexing of already-lowered finite list terms. Dagcert must require
scalar v25 with transitive v19 before relying on a module initializer such as `PICKED = VALUES[-1]`.
The verifier widens the signed index before Python negative normalization and substitutes an element
only when the normalized position is statically in bounds. Dynamic and out-of-range indices retain
the partial-operation refusal. The constructive model contributes 13 theorems in
`ConstantListIndex.lean`, bringing the formal tree to 475 declarations without `sorry`, `admit`, or
`axiom`.

Version 53 requires scalar v26 with transitive v20 for source-boundary diagnostic parity. An
uncaught non-application exceptional exit maps to `exhale.failed:assertion.false` at the callable
declaration; application-precondition exceptions preserve their code and operation location.
Declared and caught exits remain non-diagnostic, while identical boundary diagnostics from
multiple paths are deduplicated after proof. Ten constructive theorems in `ExceptionalExit.lean`
bring the formal tree to 485 declarations without `sorry`, `admit`, or `axiom`.

Version 54 requires heap v52 with transitive heap v46 for ordinary-method native assertions over
class-qualified reference results. The call target's proved source summary supplies the nominal
result class; caller syntax cannot invent or preserve that class after an incompatible
reassignment. Assertion field reads use the current heap and mask and must prove permission before
their truth VC. A returned full permission for `Result().field` additionally requires a direct,
verified fresh source allocation whose call rule establishes zero permission for that result in the
pre-mask. Dagcert must not infer this allocation premise from a return annotation or external
contract alone. `OrdinaryMethodParity.lean` contributes 22 constructive theorems, bringing the
formal tree to 507 declarations without `sorry`, `admit`, or `axiom`.

Version 55 requires heap v53 with transitive heap v47 for recursive source-provider closure and
explicit re-exports. A consumer may use an imported class, primitive function,
reference-identity function, or predicate only after the pinned resolver has verified the complete
provider-before-consumer path. Missing, ambiguous, symlinked, cyclic, unsupported, and refuted
providers refuse; a later passing consumer cannot hide an earlier provider failure. Intermediate
re-exports retain the verified leaf canonical identity. For pinned conformance, every existing
parent `__init__.py` is also verified before the child provider is trusted; passive immutable
metadata remains opaque and cannot enter proof terms. `SourceImportClosure.lean` models the finite
closure and identity rules, while filesystem/module discovery and AST correspondence remain
frontend premises. Its 19 constructive theorems bring the formal tree to 526 theorem/lemma
declarations without proof holes.

Version 56 requires scalar v27 / checked-external scalar v17 / transitive scalar v21 and heap v54 /
transitive heap v48. Finite dictionary literals and `keys()` views are separate typed proof terms;
the view is never laundered into a sliceable list. Relative pinned source edges are normalized from
the importer package and must pass the same closed provider graph as absolute edges. Completed
providers remain modular during initialization, module assertions stay visible as obligations, and
backend-qualified upstream diagnostics do not become backend-neutral certificate claims.

The v56 regression set binds exact `issues/00049.py`, `issues/00252.py`, and
`test_relative_import.py`, including relative escape/cycle refusals and both real providers. Current
evidence is 79/79 curated fixtures, 76/219 broad union matches (34.7%), zero accepted mismatches,
and 682/682 Rust tests. Lean proves the constructive finite-dictionary/key-view algebra from
frontend-supplied premises plus relative-resolution/identity and backend-expectation filtering.
The formal tree has 547 theorem/lemma declarations and zero holes. Dagcert must not interpret those
theorems as a proof of Python parsing or Rust/Lean implementation refinement.

Version 57 requires heap v55 and transitive/combined heap v49. It adds permission-checked integer
field augmented assignment, selected-branch effectful conditional expressions, Boolean-only
effectful short-circuiting, normal-only proved module heap summaries, call-entry scalar `Old` field
rebinding, and positive-literal Python modulo. Each construct refuses when its source type,
evaluation order, permission, exceptional-exit, or summary-completeness premise is unavailable.

The v57 regression binds exact `test_operators.py` and all five expected diagnostics. Current v57
evidence is 77/219 broad union matches (35.2%), zero accepted mismatches, and 698/698 Rust tests.
The full Lean build checks 574 theorem/lemma declarations with zero holes. As in prior releases,
Dagcert must treat frontend correspondence and Rust-to-Lean refinement as unproved rather than
promoting the constructive Lean model into an implementation proof.

Version 58 requires scalar v28, checked-external scalar v18, transitive/combined scalar v22, and
VC IR v19. Heap identities remain v55/v49. It proves the supported finite comprehension algebra
for one synchronous direct-name generator over a homogeneous builtin list, at most one pure total
filter, and pure total primitive list/set/dictionary expressions. List order and duplicates, set
deduplication/membership, dictionary first-key order and last-write-wins values, Python floor
modulo, and concrete Boolean/integer dictionary-key identity are covered. Missing dictionary
lookup remains conditional on a membership precondition. Unsupported or effectful shapes refuse;
a refusal cannot be recast as a proof by Dagcert.

The v58 regression binds exact `test_list_comprehension.py`,
`test_list_comprehension_filter.py`, `test_dict_comprehension.py`, and
`test_set_comprehension.py`, including all 16 expected diagnostics. Current evidence is 83/83
curated fixtures, 81/219 broad scalar/heap union matches (37.0%), zero accepted mismatches, and
716/716 Rust tests. The complete Lean build checks 609 theorem/lemma declarations with zero
`sorry`, `admit`, or `axiom`. The constructive Lean comprehension model assumes the frontend shape,
purity, sorts, and source sequence; it does not verify Python parsing, Rust VC generation, Z3
lowering, or Rust-to-Lean refinement. Dagcert must report that end-to-end refinement gap as 0%, not
promote the Lean declaration count into an implementation-correctness claim.

Version 59 requires `python-call-argument-binding/v1`, scalar v29, checked-external scalar v19,
transitive/combined scalar v23, heap v56, transitive/combined heap v50, and VC IR v20. The shared
kernel is integrated at scalar source calls and the heap direct-name ordinary-method receiver path,
including its class-qualified adapter. There it produces a canonical typed environment for
positional-only, positional-or-keyword, keyword-only, defaulted, `*args`, and `**kwargs` formals.
Fixed tuple stars and receiver injection retain explicit source-order metadata. Dynamic `*` and
every `**mapping` expansion remain refusals. The binder source is included in the verifier kernel
digest.

The capability identifies the kernel and these integrated seams; it is not a claim that all call
adapters use it. Imported scalar calls, module predicate calls, the heap module-function adapter,
base constructors, and ordinary constructors remain restricted/manual or fail closed for v59
syntax. Dagcert must expose those seams as completeness backlog rather than infer whole-frontend
coverage from the capability string. Arbitrary effectful receiver expressions and receiver chains
also fail closed and are outside v59 receiver-injection coverage.

The solver represents an abstract dictionary with stable independent key-sequence and value-array
symbols. It can consume explicit length, membership, and lookup facts but cannot invent a lookup
value from membership or from an unconstrained dictionary. The frontend must still emit and prove
the membership guard that excludes `KeyError`. Abstract set variables and unsupported dictionary
sorts fail closed. `CallArgumentBinding.lean` covers only the finite algebra from trusted inputs;
Dagcert must not report it as Python/frontend correspondence or Rust implementation refinement.

The final v59 gate passes 45/45 curated scalar fixtures, 42/42 curated heap fixtures, and 85/219
broad scalar/heap union fixtures (38.8%) with zero accepted mismatches. All 759 Rust tests pass.
The original v59 Lean gate builds 631 theorem/lemma declarations, including 22 call-binding
declarations, with zero `sorry`, `admit`, or `axiom`.

The former 86-case bounded call-expansion witness and its fixed-cap model have been retired from
the active build and capabilities. They remain historical provenance only: the current capability
is the cap-free Aeneas extraction of the production binder and its universal allocator-aware Lean
refinement theorem. Dagcert must not report the retired bounded identity as an active gate.

`checked-external-heap-contracts/v5` records its module-qualified classes in
`heap_types` and keeps provider conformance explicit. Source summaries carry verified transitive
field-write sets; opaque external calls conservatively invalidate every declared field before
their postconditions are applied. Unsupported source receives a refusal. The current fragments report
scope `all-source-symbol-bodies`: source hashes cover the whole file and supported module-level
initialization is checked. The pinned conformance resolver discovers parent package initializers;
the production JSON protocol instead requires every source provider to be explicitly enumerated
and hash-bound by the request. Dagcert must not reinterpret a refusal as an observational check or
silently fall back to Nagini after issuance begins.

The bounded heap sequence-pattern frontend verifies fixed and single-star patterns over
source-typed `List[bool]`, `List[int]`, and `List[str]`. Fixed patterns require exact length;
single-star patterns require the prefix-plus-suffix minimum, and every head/suffix read is guarded
by that condition. The captured star tail has only its list sort: no length, content, slice, or
alias relationship is invented. Tuple subjects, reference elements, nested patterns, mappings,
multiple stars, and dynamic/untyped subjects fail closed.

Pinned upstream diagnostics that say only `unsupported:...` are never relabeled as exact matches.
The separate `SupersededUpstreamUnsupported` classification is available only when strict
production mypy succeeds and a real backend semantically verifies with no failed obligations.
Reports preserve the upstream expected diagnostics, the empty actual diagnostic set, and the
typechecker identity, while keeping this count separate from semantic, typecheck-rejection, and
source-wellformedness exact matches. `SequencePatterns.lean` is model-only length/index algebra;
it is not an extraction or a Rust/frontend refinement proof.

The source-wellformedness preflight also checks a bounded, source-general behavioral-override
boundary. It rejects runtime overrides involving a `@Pure` mathematical method, changes to the
ordered keyword-callable parameter names (including incompatible constructor surfaces), and
declared exceptional outcomes that are not nominal subtypes of an inherited declared outcome.
Ordinary overrides with the same keyword surface and exception-channel narrowing remain valid.
Default-value substitutability and property-contract implication are not guessed: cases requiring
those proofs remain refused by the semantic frontend rather than being mislabeled invalid.
`BehavioralOverrides.lean` states the corresponding boundary algebra as a model only; it is not a
Rust extraction or frontend-refinement theorem.
