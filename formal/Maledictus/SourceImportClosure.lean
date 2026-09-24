import Maledictus.Kernel

namespace Maledictus

/-!
# Recursive direct source-import closure

This module models the fail-closed core of recursive source-module resolution.  The frontend
supplies a finite resolution trace in depth-first postorder: every direct provider must already be
completed before its consumer can be added.  Checking every provider's own direct imports makes
that local rule recursive over the complete trace.  A missing provider, a provider cycle, an
unverified source module, or a symbol absent from the provider's verified exports refuses the
trace.

The model deliberately does not prove Python parsing, filesystem-to-module correspondence, import
discovery, hash binding, or completeness of the supplied catalog.  Those remain frontend premises.
Canonical symbol identities belong to verified exports and are copied by consumers.  This is
essential for explicit re-exports: importing `X` from intermediate provider `b` may retain the leaf
identity `a.X`.  Consumer-local aliases and passive opaque export metadata cannot rewrite it.

The final section models the finite premise used for one-level relative imports.  A relative target
is looked up only in the consumer's package, and the normalized target retains the provider's
canonical module identity.  Unsupported levels, an empty package/target, a missing provider, and an
active provider cycle are distinct refusals.  Python token parsing and filesystem correspondence
remain frontend premises.  Backend-qualified conformance expectations are likewise assumed to have
been parsed already; this module only models which parsed expectations apply to Maledictus.
-/

structure DirectSourceImportedSymbol where
  importedName : String
  localName : String
  deriving DecidableEq

structure DirectSourceImport where
  providerModule : String
  symbols : List DirectSourceImportedSymbol
  deriving DecidableEq

inductive PackageInitializerDisposition where
  | notRequired
  | verified
  | refuted
  | unknown
  deriving DecidableEq

structure VerifiedSourceExport where
  exportedName : String
  canonicalIdentity : String
  opaqueMetadata : List String
  deriving DecidableEq

structure SourceImportProvider where
  moduleName : String
  directImports : List DirectSourceImport
  exportedSymbols : List VerifiedSourceExport
  sourceVerified : Bool
  packageInitializer : PackageInitializerDisposition
  deriving DecidableEq

structure CanonicalSourceImportedSymbol where
  consumerModule : String
  localName : String
  providerModule : String
  importedName : String
  canonicalIdentity : String
  deriving DecidableEq

structure SourceImportClosureState where
  completedProviders : List String
  importedSymbols : List CanonicalSourceImportedSymbol
  deriving DecidableEq

def sourceImportProviderLookup :
    List SourceImportProvider → String → Option SourceImportProvider
  | [], _ => none
  | provider :: rest, moduleName =>
      if provider.moduleName == moduleName then some provider
      else sourceImportProviderLookup rest moduleName

def verifiedSourceExportLookup :
    List VerifiedSourceExport → String → Option VerifiedSourceExport
  | [], _ => none
  | verifiedExport :: rest, exportedName =>
      if verifiedExport.exportedName == exportedName then some verifiedExport
      else verifiedSourceExportLookup rest exportedName

def canonicalSourceSymbolIdentity (providerModule importedName : String) : String :=
  providerModule ++ "." ++ importedName

def canonicalSourceImportedSymbol
    (consumerModule providerModule : String)
    (symbol : DirectSourceImportedSymbol)
    (verifiedExport : VerifiedSourceExport) : CanonicalSourceImportedSymbol :=
  {
    consumerModule
    localName := symbol.localName
    providerModule
    importedName := symbol.importedName
    canonicalIdentity := verifiedExport.canonicalIdentity
  }

def verifiedSourceExportReady (verifiedExport : VerifiedSourceExport) : Bool :=
  !verifiedExport.exportedName.isEmpty && !verifiedExport.canonicalIdentity.isEmpty

def packageInitializerReady : PackageInitializerDisposition → Bool
  | .notRequired => true
  | .verified => true
  | .refuted => false
  | .unknown => false

def sourceImportProviderAcceptable (provider : SourceImportProvider) : Bool :=
  provider.sourceVerified && packageInitializerReady provider.packageInitializer

def sourceImportProviderExports
    (provider : SourceImportProvider) (symbols : List DirectSourceImportedSymbol) : Bool :=
  symbols.all (fun symbol =>
    match verifiedSourceExportLookup provider.exportedSymbols symbol.importedName with
    | none => false
    | some verifiedExport => verifiedSourceExportReady verifiedExport)

def directSourceImportReady
    (catalog : List SourceImportProvider)
    (completedProviders : List String)
    (directImport : DirectSourceImport) : Bool :=
  decide (directImport.providerModule ∈ completedProviders) &&
    match sourceImportProviderLookup catalog directImport.providerModule with
    | none => false
    | some provider =>
        sourceImportProviderAcceptable provider &&
          sourceImportProviderExports provider directImport.symbols

def sourceImportProviderReady
    (catalog : List SourceImportProvider)
    (completedProviders : List String)
    (provider : SourceImportProvider) : Bool :=
  sourceImportProviderAcceptable provider &&
    provider.directImports.all (directSourceImportReady catalog completedProviders)

def directSourceImportedSymbolBinding
    (consumerModule : String)
    (provider : SourceImportProvider)
    (symbol : DirectSourceImportedSymbol) : Option CanonicalSourceImportedSymbol :=
  match verifiedSourceExportLookup provider.exportedSymbols symbol.importedName with
  | none => none
  | some verifiedExport =>
      some (canonicalSourceImportedSymbol consumerModule provider.moduleName symbol verifiedExport)

def directSourceImportBindings
    (catalog : List SourceImportProvider)
    (consumerModule : String)
    (directImport : DirectSourceImport) : List CanonicalSourceImportedSymbol :=
  match sourceImportProviderLookup catalog directImport.providerModule with
  | none => []
  | some provider =>
      directImport.symbols.filterMap
        (directSourceImportedSymbolBinding consumerModule provider)

def sourceImportProviderBindings
    (catalog : List SourceImportProvider)
    (provider : SourceImportProvider) : List CanonicalSourceImportedSymbol :=
  provider.directImports.flatMap
    (directSourceImportBindings catalog provider.moduleName)

def advanceSourceImportProvider
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (provider : SourceImportProvider) : Option SourceImportClosureState :=
  if provider.moduleName.isEmpty || provider.moduleName ∈ state.completedProviders then none
  else if sourceImportProviderReady catalog state.completedProviders provider then
    some {
      completedProviders := state.completedProviders ++ [provider.moduleName]
      importedSymbols := state.importedSymbols ++ sourceImportProviderBindings catalog provider
    }
  else none

def advanceSourceImportModule
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (moduleName : String) : Option SourceImportClosureState :=
  match sourceImportProviderLookup catalog moduleName with
  | none => none
  | some provider => advanceSourceImportProvider catalog state provider

def executeSourceImportTrace
    (catalog : List SourceImportProvider) :
    Option SourceImportClosureState → List String → Option SourceImportClosureState
  | state, [] => state
  | none, _ :: _ => none
  | some state, moduleName :: rest =>
      executeSourceImportTrace catalog
        (advanceSourceImportModule catalog state moduleName) rest

def resolveDirectSourceImportClosure
    (catalog : List SourceImportProvider)
    (consumerModule : String)
    (providerBeforeConsumerTrace : List String) : Option SourceImportClosureState :=
  match executeSourceImportTrace catalog
      (some { completedProviders := [], importedSymbols := [] })
      providerBeforeConsumerTrace with
  | none => none
  | some state =>
      if state.completedProviders.getLast? = some consumerModule then some state else none

theorem canonical_imported_symbol_copies_verified_export_identity
    (consumerModule providerModule : String)
    (symbol : DirectSourceImportedSymbol)
    (verifiedExport : VerifiedSourceExport) :
    (canonicalSourceImportedSymbol consumerModule providerModule symbol
      verifiedExport).canonicalIdentity = verifiedExport.canonicalIdentity := by
  rfl

theorem local_alias_cannot_change_canonical_imported_symbol_identity
    (consumerModule providerModule importedName firstLocalName secondLocalName : String)
    (verifiedExport : VerifiedSourceExport) :
    (canonicalSourceImportedSymbol consumerModule providerModule {
        importedName
        localName := firstLocalName
      } verifiedExport).canonicalIdentity =
      (canonicalSourceImportedSymbol consumerModule providerModule {
        importedName
        localName := secondLocalName
      } verifiedExport).canonicalIdentity := by
  rfl

theorem passive_opaque_metadata_does_not_change_export_readiness
    (verifiedExport : VerifiedSourceExport)
    (firstMetadata secondMetadata : List String) :
    verifiedSourceExportReady { verifiedExport with opaqueMetadata := firstMetadata } =
      verifiedSourceExportReady { verifiedExport with opaqueMetadata := secondMetadata } := by
  rfl

theorem passive_opaque_metadata_does_not_change_imported_identity
    (consumerModule providerModule : String)
    (symbol : DirectSourceImportedSymbol)
    (verifiedExport : VerifiedSourceExport)
    (firstMetadata secondMetadata : List String) :
    (canonicalSourceImportedSymbol consumerModule providerModule symbol
        { verifiedExport with opaqueMetadata := firstMetadata }).canonicalIdentity =
      (canonicalSourceImportedSymbol consumerModule providerModule symbol
        { verifiedExport with opaqueMetadata := secondMetadata }).canonicalIdentity := by
  rfl

theorem two_hop_reexport_preserves_leaf_canonical_identity :
    let leafIdentity := canonicalSourceSymbolIdentity "a" "X"
    let middleProvider : SourceImportProvider := {
      moduleName := "b"
      directImports := []
      exportedSymbols := [{
        exportedName := "X"
        canonicalIdentity := leafIdentity
        opaqueMetadata := ["passive"]
      }]
      sourceVerified := true
      packageInitializer := .verified
    }
    let consumerImport : DirectSourceImport := {
      providerModule := "b"
      symbols := [{ importedName := "X", localName := "renamed" }]
    }
    (directSourceImportBindings [middleProvider] "c" consumerImport).map
        (fun binding => binding.canonicalIdentity) = [leafIdentity] := by
  simp [directSourceImportBindings, sourceImportProviderLookup,
    directSourceImportedSymbolBinding, verifiedSourceExportLookup,
    canonicalSourceImportedSymbol]

theorem verified_package_initializer_is_ready :
    packageInitializerReady .verified = true := by
  rfl

theorem refuted_package_initializer_is_not_ready :
    packageInitializerReady .refuted = false := by
  rfl

theorem unknown_package_initializer_is_not_ready :
    packageInitializerReady .unknown = false := by
  rfl

theorem missing_source_module_refuses_trace_step
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (moduleName : String)
    (missing : sourceImportProviderLookup catalog moduleName = none) :
    advanceSourceImportModule catalog state moduleName = none := by
  simp [advanceSourceImportModule, missing]

theorem unverified_source_provider_refuses
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (provider : SourceImportProvider)
    (unverified : provider.sourceVerified = false) :
    advanceSourceImportProvider catalog state provider = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady,
    sourceImportProviderAcceptable, unverified]

theorem refuted_package_initializer_refuses_source_provider
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (provider : SourceImportProvider)
    (refuted : provider.packageInitializer = .refuted) :
    advanceSourceImportProvider catalog state provider = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady,
    sourceImportProviderAcceptable, packageInitializerReady, refuted]

theorem unverified_direct_provider_refuses_consumer
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (consumer provider : SourceImportProvider)
    (directImport : DirectSourceImport)
    (lookup : sourceImportProviderLookup catalog directImport.providerModule = some provider)
    (unverified : provider.sourceVerified = false) :
    advanceSourceImportProvider catalog state
        { consumer with directImports := directImport :: consumer.directImports } = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady, directSourceImportReady,
    sourceImportProviderAcceptable, lookup, unverified]

theorem refuted_direct_provider_initializer_refuses_consumer
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (consumer provider : SourceImportProvider)
    (directImport : DirectSourceImport)
    (lookup : sourceImportProviderLookup catalog directImport.providerModule = some provider)
    (refuted : provider.packageInitializer = .refuted) :
    advanceSourceImportProvider catalog state
        { consumer with directImports := directImport :: consumer.directImports } = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady, directSourceImportReady,
    sourceImportProviderAcceptable, packageInitializerReady, lookup, refuted]

theorem missing_direct_provider_refuses_consumer
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (consumer : SourceImportProvider)
    (directImport : DirectSourceImport)
    (missing : sourceImportProviderLookup catalog directImport.providerModule = none) :
    advanceSourceImportProvider catalog state
        { consumer with directImports := directImport :: consumer.directImports } = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady, directSourceImportReady, missing]

theorem accepted_source_provider_was_verified
    (catalog : List SourceImportProvider)
    (state next : SourceImportClosureState)
    (provider : SourceImportProvider)
    (accepted : advanceSourceImportProvider catalog state provider = some next) :
    provider.sourceVerified = true := by
  by_cases rejected : provider.moduleName.isEmpty || provider.moduleName ∈ state.completedProviders
  · simp [advanceSourceImportProvider, rejected] at accepted
  · cases ready : sourceImportProviderReady catalog state.completedProviders provider with
    | false => simp [advanceSourceImportProvider, rejected, ready] at accepted
    | true =>
        have readyFacts := ready
        simp [sourceImportProviderReady, sourceImportProviderAcceptable] at readyFacts
        exact readyFacts.1.1

theorem accepted_source_provider_requires_provider_before_consumer
    (catalog : List SourceImportProvider)
    (state next : SourceImportClosureState)
    (consumer : SourceImportProvider)
    (directImport : DirectSourceImport)
    (member : directImport ∈ consumer.directImports)
    (accepted : advanceSourceImportProvider catalog state consumer = some next) :
    directImport.providerModule ∈ state.completedProviders := by
  by_cases rejected : consumer.moduleName.isEmpty ||
      consumer.moduleName ∈ state.completedProviders
  · simp [advanceSourceImportProvider, rejected] at accepted
  · cases ready : sourceImportProviderReady catalog state.completedProviders consumer with
    | false => simp [advanceSourceImportProvider, rejected, ready] at accepted
    | true =>
        have readyFacts := ready
        simp [sourceImportProviderReady, sourceImportProviderAcceptable] at readyFacts
        have directReady := readyFacts.2 directImport member
        simp [directSourceImportReady] at directReady
        exact directReady.1

theorem self_import_cycle_refuses_first_provider
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (provider : SourceImportProvider)
    (symbols : List DirectSourceImportedSymbol)
    (notCompleted : provider.moduleName ∉ state.completedProviders) :
    advanceSourceImportProvider catalog state {
        provider with
        directImports := {
          providerModule := provider.moduleName
          symbols
        } :: provider.directImports
      } = none := by
  simp [advanceSourceImportProvider, sourceImportProviderReady, directSourceImportReady,
    notCompleted]

theorem two_provider_cycle_has_no_first_provider
    (catalog : List SourceImportProvider)
    (state : SourceImportClosureState)
    (first second : SourceImportProvider)
    (firstSymbols secondSymbols : List DirectSourceImportedSymbol)
    (firstNotCompleted : first.moduleName ∉ state.completedProviders)
    (secondNotCompleted : second.moduleName ∉ state.completedProviders) :
    advanceSourceImportProvider catalog state {
        first with
        directImports := {
          providerModule := second.moduleName
          symbols := secondSymbols
        } :: first.directImports
      } = none ∧
    advanceSourceImportProvider catalog state {
        second with
        directImports := {
          providerModule := first.moduleName
          symbols := firstSymbols
        } :: second.directImports
      } = none := by
  constructor <;>
    simp [advanceSourceImportProvider, sourceImportProviderReady, directSourceImportReady,
      firstNotCompleted, secondNotCompleted]

theorem accepted_direct_source_import_closure_ends_with_consumer
    (catalog : List SourceImportProvider)
    (consumerModule : String)
    (trace : List String)
    (state : SourceImportClosureState)
    (accepted : resolveDirectSourceImportClosure catalog consumerModule trace = some state) :
    state.completedProviders.getLast? = some consumerModule := by
  unfold resolveDirectSourceImportClosure at accepted
  cases executed : executeSourceImportTrace catalog
      (some { completedProviders := [], importedSymbols := [] }) trace with
  | none =>
      rw [executed] at accepted
      simp at accepted
  | some finalState =>
      rw [executed] at accepted
      by_cases ending : finalState.completedProviders.getLast? = some consumerModule
      · simp [ending] at accepted
        subst state
        exact ending
      · simp [ending] at accepted

/-! ## One-level relative source imports -/

structure PackageSourceProvider where
  packageName : String
  relativeModuleName : String
  provider : SourceImportProvider
  deriving DecidableEq

structure FinitePackageContext where
  providers : List PackageSourceProvider
  deriving DecidableEq

structure RelativeSourceImportRequest where
  consumerPackage : String
  consumerModule : String
  relativeLevel : Nat
  relativeProviderName : String
  deriving DecidableEq

structure NormalizedRelativeSourceTarget where
  packageName : String
  canonicalModuleName : String
  provider : SourceImportProvider
  deriving DecidableEq

inductive RelativeSourceImportResolution where
  | resolved (target : NormalizedRelativeSourceTarget)
  | refusedMissingProvider
  | refusedEscape
  | refusedCycle
  deriving DecidableEq

def packageSourceProviderLookup :
    List PackageSourceProvider → String → String → Option PackageSourceProvider
  | [], _, _ => none
  | entry :: rest, packageName, relativeModuleName =>
      if entry.packageName == packageName &&
          entry.relativeModuleName == relativeModuleName then
        some entry
      else
        packageSourceProviderLookup rest packageName relativeModuleName

def normalizedRelativeSourceTarget
    (request : RelativeSourceImportRequest)
    (entry : PackageSourceProvider) : NormalizedRelativeSourceTarget :=
  {
    packageName := request.consumerPackage
    canonicalModuleName := entry.provider.moduleName
    provider := entry.provider
  }

def resolveLevelOneRelativeSourceImport
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest) : RelativeSourceImportResolution :=
  if request.relativeLevel != 1 || request.consumerPackage.isEmpty ||
      request.relativeProviderName.isEmpty then
    .refusedEscape
  else
    match packageSourceProviderLookup context.providers request.consumerPackage
        request.relativeProviderName with
    | none => .refusedMissingProvider
    | some entry =>
        if entry.provider.moduleName ∈ activeModules then .refusedCycle
        else .resolved (normalizedRelativeSourceTarget request entry)

def relativeSourceImportedSymbolBinding
    (request : RelativeSourceImportRequest)
    (target : NormalizedRelativeSourceTarget)
    (symbol : DirectSourceImportedSymbol) : Option CanonicalSourceImportedSymbol :=
  directSourceImportedSymbolBinding request.consumerModule target.provider symbol

theorem normalized_level_one_target_preserves_consumer_package
    (request : RelativeSourceImportRequest)
    (entry : PackageSourceProvider) :
    (normalizedRelativeSourceTarget request entry).packageName = request.consumerPackage := by
  rfl

theorem normalized_level_one_target_retains_provider_module_identity
    (request : RelativeSourceImportRequest)
    (entry : PackageSourceProvider) :
    (normalizedRelativeSourceTarget request entry).canonicalModuleName =
      entry.provider.moduleName := by
  rfl

theorem non_level_one_relative_import_refuses_escape
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (wrongLevel : request.relativeLevel ≠ 1) :
    resolveLevelOneRelativeSourceImport context activeModules request =
      .refusedEscape := by
  simp [resolveLevelOneRelativeSourceImport, wrongLevel]

theorem empty_relative_consumer_package_refuses_escape
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (level : request.relativeLevel = 1)
    (emptyPackage : request.consumerPackage.isEmpty = true) :
    resolveLevelOneRelativeSourceImport context activeModules request =
      .refusedEscape := by
  simp [resolveLevelOneRelativeSourceImport, level, emptyPackage]

theorem empty_relative_provider_name_refuses_escape
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (level : request.relativeLevel = 1)
    (nonemptyPackage : request.consumerPackage.isEmpty = false)
    (emptyTarget : request.relativeProviderName.isEmpty = true) :
    resolveLevelOneRelativeSourceImport context activeModules request =
      .refusedEscape := by
  simp [resolveLevelOneRelativeSourceImport, level, nonemptyPackage, emptyTarget]

theorem missing_level_one_relative_provider_refuses
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (level : request.relativeLevel = 1)
    (nonemptyPackage : request.consumerPackage.isEmpty = false)
    (nonemptyTarget : request.relativeProviderName.isEmpty = false)
    (missing : packageSourceProviderLookup context.providers request.consumerPackage
      request.relativeProviderName = none) :
    resolveLevelOneRelativeSourceImport context activeModules request =
      .refusedMissingProvider := by
  simp [resolveLevelOneRelativeSourceImport, level, nonemptyPackage, nonemptyTarget, missing]

theorem active_level_one_relative_provider_refuses_cycle
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (entry : PackageSourceProvider)
    (level : request.relativeLevel = 1)
    (nonemptyPackage : request.consumerPackage.isEmpty = false)
    (nonemptyTarget : request.relativeProviderName.isEmpty = false)
    (found : packageSourceProviderLookup context.providers request.consumerPackage
      request.relativeProviderName = some entry)
    (active : entry.provider.moduleName ∈ activeModules) :
    resolveLevelOneRelativeSourceImport context activeModules request = .refusedCycle := by
  simp [resolveLevelOneRelativeSourceImport, level, nonemptyPackage, nonemptyTarget, found,
    active]

theorem inactive_level_one_relative_provider_resolves
    (context : FinitePackageContext)
    (activeModules : List String)
    (request : RelativeSourceImportRequest)
    (entry : PackageSourceProvider)
    (level : request.relativeLevel = 1)
    (nonemptyPackage : request.consumerPackage.isEmpty = false)
    (nonemptyTarget : request.relativeProviderName.isEmpty = false)
    (found : packageSourceProviderLookup context.providers request.consumerPackage
      request.relativeProviderName = some entry)
    (inactive : entry.provider.moduleName ∉ activeModules) :
    resolveLevelOneRelativeSourceImport context activeModules request =
      .resolved (normalizedRelativeSourceTarget request entry) := by
  simp [resolveLevelOneRelativeSourceImport, level, nonemptyPackage, nonemptyTarget, found,
    inactive]

theorem relative_rebinding_retains_leaf_canonical_identity
    (request : RelativeSourceImportRequest)
    (target : NormalizedRelativeSourceTarget)
    (symbol : DirectSourceImportedSymbol)
    (verifiedExport : VerifiedSourceExport)
    (found : verifiedSourceExportLookup target.provider.exportedSymbols symbol.importedName =
      some verifiedExport) :
    (relativeSourceImportedSymbolBinding request target symbol).map
        (fun binding => binding.canonicalIdentity) = some verifiedExport.canonicalIdentity := by
  simp [relativeSourceImportedSymbolBinding, directSourceImportedSymbolBinding, found,
    canonicalSourceImportedSymbol]

/-! ## Backend-qualified conformance expectations -/

inductive ConformanceExpectationBackend where
  | any
  | maledictus
  | silicon
  | carbon
  deriving DecidableEq

structure ParsedConformanceExpectation where
  backend : ConformanceExpectationBackend
  diagnosticCode : String
  deriving DecidableEq

def conformanceExpectationAppliesToMaledictus
    (expectation : ParsedConformanceExpectation) : Bool :=
  expectation.backend == .any || expectation.backend == .maledictus

def filterMaledictusConformanceExpectations
    (expectations : List ParsedConformanceExpectation) : List ParsedConformanceExpectation :=
  expectations.filter conformanceExpectationAppliesToMaledictus

theorem backend_neutral_expectation_is_retained
    (diagnosticCode : String) :
    filterMaledictusConformanceExpectations [{
      backend := .any
      diagnosticCode
    }] = [{ backend := .any, diagnosticCode }] := by
  simp [filterMaledictusConformanceExpectations, conformanceExpectationAppliesToMaledictus]

theorem maledictus_qualified_expectation_is_retained
    (diagnosticCode : String) :
    filterMaledictusConformanceExpectations [{
      backend := .maledictus
      diagnosticCode
    }] = [{ backend := .maledictus, diagnosticCode }] := by
  simp [filterMaledictusConformanceExpectations, conformanceExpectationAppliesToMaledictus]

theorem silicon_qualified_expectation_is_filtered
    (diagnosticCode : String) :
    filterMaledictusConformanceExpectations [{
      backend := .silicon
      diagnosticCode
    }] = [] := by
  simp [filterMaledictusConformanceExpectations, conformanceExpectationAppliesToMaledictus]

theorem carbon_qualified_expectation_is_filtered
    (diagnosticCode : String) :
    filterMaledictusConformanceExpectations [{
      backend := .carbon
      diagnosticCode
    }] = [] := by
  simp [filterMaledictusConformanceExpectations, conformanceExpectationAppliesToMaledictus]

end Maledictus
