#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

use proc_macro2::Span;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Expr, ExprCall, ExprMethodCall, ImplItem, Item, ItemFn, ItemImpl, ItemMod, Macro, TraitItem,
};

const SCHEMA: &str = "maledictus-formal-coverage/v2";

#[derive(Debug, Deserialize)]
struct Config {
    schema: String,
    root: RootConfig,
    source_proofs: Vec<ProofConfig>,
    external_boundaries: Vec<ExternalBoundary>,
}

#[derive(Debug, Deserialize)]
struct RootConfig {
    symbol: String,
    invocation: String,
}

#[derive(Debug, Deserialize)]
struct ProofConfig {
    id: String,
    basis: Basis,
    source_file: String,
    #[serde(default)]
    function_names: Vec<String>,
    #[serde(default)]
    function_symbols: Vec<String>,
    #[serde(default)]
    manifest_function_names: Vec<String>,
    manifest: String,
    theorem: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
enum Basis {
    UnconditionalSourceBound,
    ConditionalSourceBound,
    ModelOnly,
    Unproved,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct ExternalBoundary {
    id: String,
    provider: String,
    #[serde(default)]
    cargo_packages: Vec<String>,
    used_by: Vec<String>,
    contract: Option<String>,
    basis: ExternalBasis,
}

#[derive(Clone, Debug, Deserialize, Serialize, Eq, PartialEq)]
#[serde(rename_all = "kebab-case")]
enum ExternalBasis {
    FormallyClosed,
    Assumed,
    RuntimeChecked,
    Unmodeled,
}

#[derive(Debug, Serialize)]
struct Coverage {
    schema: &'static str,
    generator: GeneratorIdentity,
    root: RootOutput,
    reachability: Reachability,
    metrics: Metrics,
    source_nodes: Vec<SourceNode>,
    external_boundaries: Vec<ExternalBoundary>,
    model_only_artifacts: Vec<ModelArtifact>,
}

#[derive(Debug, Serialize)]
struct GeneratorIdentity {
    path: String,
    sha256: String,
    config_path: String,
    config_sha256: String,
}

#[derive(Debug, Serialize)]
struct RootOutput {
    symbol: String,
    invocation: String,
    source_tree_sha256: String,
    callgraph_sha256: String,
    composition_proved: bool,
}

#[derive(Debug, Serialize)]
struct Reachability {
    algorithm: &'static str,
    conservative: bool,
    fallback: &'static str,
    fallback_used: bool,
    fallback_reason_nodes: Vec<FallbackReason>,
}

#[derive(Debug, Serialize)]
struct FallbackReason {
    source_node: String,
    categories: Vec<String>,
}

#[derive(Debug, Serialize)]
struct Metrics {
    source_unconditional_proved: usize,
    source_conditional_proved: usize,
    source_model_only: usize,
    source_unproved: usize,
    source_total: usize,
    source_unconditional_percent: String,
    external_closed: usize,
    external_total: usize,
    external_closed_percent: String,
    root_composition_proved: bool,
    whole_type_system_formally_proven: bool,
}

#[derive(Clone, Debug, Serialize)]
struct SourceNode {
    id: String,
    symbol: String,
    name: String,
    file: String,
    line_start: usize,
    line_end: usize,
    source_sha256: String,
    basis: Basis,
    proof: Option<ProofOutput>,
    calls: Vec<String>,
}

#[derive(Clone, Debug, Serialize)]
struct ProofOutput {
    id: String,
    manifest: String,
    manifest_sha256: String,
    theorem: String,
    current_source_hash_matches: bool,
    counts_as_implementation_refinement: bool,
    proof_obligations_closed: bool,
    axiom_audit_clean: bool,
}

#[derive(Debug, Serialize)]
struct ModelArtifact {
    path: String,
    sha256: String,
    theorem_or_lemma_declarations: usize,
    basis: Basis,
    counts_toward_source_numerator: bool,
}

#[derive(Debug)]
struct ParsedNode {
    output: SourceNode,
    direct_names: BTreeSet<String>,
    indirect_calls: BTreeSet<String>,
}

struct FunctionIdentity {
    name: String,
    span: Span,
    owner: Option<String>,
}

#[derive(Default)]
struct CallVisitor {
    direct_names: BTreeSet<String>,
    indirect_calls: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for CallVisitor {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        match node.func.as_ref() {
            Expr::Path(path) => {
                if let Some(segment) = path.path.segments.last() {
                    self.direct_names.insert(segment.ident.to_string());
                }
            }
            other => {
                self.indirect_calls.insert(format!(
                    "indirect-callable-expression:{}",
                    quote_expr_kind(other)
                ));
            }
        }
        visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.direct_names.insert(node.method.to_string());
        self.indirect_calls
            .insert("method-or-trait-dispatch".to_owned());
        visit::visit_expr_method_call(self, node);
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        self.indirect_calls.insert("macro-expansion".to_owned());
        visit::visit_macro(self, node);
    }
}

fn quote_expr_kind(expr: &Expr) -> &'static str {
    match expr {
        Expr::Closure(_) => "closure",
        Expr::Field(_) => "callable field",
        Expr::Index(_) => "indexed callable",
        Expr::Paren(_) => "parenthesized callable",
        _ => "non-path callable",
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("formal coverage: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let command = args.next().ok_or_else(usage)?;
    let mut project = None;
    let mut config = None;
    let mut output = None;
    while let Some(flag) = args.next() {
        let value = args.next().ok_or_else(usage)?;
        match flag.as_str() {
            "--project" => project = Some(PathBuf::from(value)),
            "--config" => config = Some(PathBuf::from(value)),
            "--output" => output = Some(PathBuf::from(value)),
            _ => return Err(usage()),
        }
    }
    let project = absolute(project.ok_or_else(usage)?)?;
    let config_path = project.join(config.ok_or_else(usage)?);
    let output_path = project.join(output.ok_or_else(usage)?);
    let rendered = generate(&project, &config_path)?;
    match command.as_str() {
        "generate" => {
            fs::write(&output_path, rendered)
                .map_err(|error| format!("cannot write {}: {error}", output_path.display()))?;
            println!("generated {}", output_path.display());
        }
        "check" => {
            let existing = fs::read_to_string(&output_path)
                .map_err(|error| format!("cannot read {}: {error}", output_path.display()))?;
            check_rendered(&existing, &rendered, &output_path)?;
            println!("formal coverage artifact is current");
        }
        _ => return Err(usage()),
    }
    Ok(())
}

fn check_rendered(existing: &str, generated: &str, output_path: &Path) -> Result<(), String> {
    if existing != generated {
        return Err(format!(
            "{} is stale; regenerate it with the documented generate command",
            output_path.display()
        ));
    }
    Ok(())
}

fn usage() -> String {
    "usage: maledictus-formal-coverage <generate|check> --project PATH --config RELATIVE_PATH --output RELATIVE_PATH".to_owned()
}

fn absolute(path: PathBuf) -> Result<PathBuf, String> {
    if path.is_absolute() {
        Ok(path)
    } else {
        env::current_dir()
            .map(|cwd| cwd.join(path))
            .map_err(|error| format!("cannot resolve current directory: {error}"))
    }
}

fn generate(project: &Path, config_path: &Path) -> Result<String, String> {
    let config_bytes = fs::read(config_path)
        .map_err(|error| format!("cannot read {}: {error}", config_path.display()))?;
    let config: Config = serde_json::from_slice(&config_bytes)
        .map_err(|error| format!("invalid {}: {error}", config_path.display()))?;
    if config.schema != SCHEMA {
        return Err(format!("unsupported config schema {:?}", config.schema));
    }

    let source_files = rust_source_files(&project.join("src"))?;
    let source_tree_sha256 = hash_tree(project, &source_files)?;
    let mut parsed = Vec::new();
    for file in &source_files {
        parse_source_file(project, file, &mut parsed)?;
    }
    parsed.sort_by(|left, right| left.output.id.cmp(&right.output.id));

    let root_index = parsed
        .iter()
        .position(|node| node.output.symbol == config.root.symbol)
        .ok_or_else(|| format!("root symbol {:?} not found", config.root.symbol))?;
    let mut by_name: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (index, node) in parsed.iter().enumerate() {
        by_name
            .entry(node.output.name.clone())
            .or_default()
            .push(index);
    }

    let mut reachable = BTreeSet::new();
    let mut queue = VecDeque::from([root_index]);
    let mut unresolved: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    while let Some(index) = queue.pop_front() {
        if !reachable.insert(index) {
            continue;
        }
        for indirect in &parsed[index].indirect_calls {
            unresolved
                .entry(parsed[index].output.symbol.clone())
                .or_default()
                .insert(indirect.clone());
        }
        for called in &parsed[index].direct_names {
            if let Some(candidates) = by_name.get(called) {
                for candidate in candidates {
                    queue.push_back(*candidate);
                }
            } else if called
                .chars()
                .next()
                .is_some_and(|first| first.is_ascii_lowercase())
            {
                unresolved
                    .entry(parsed[index].output.symbol.clone())
                    .or_default()
                    .insert("unresolved-callable-name".to_owned());
            }
        }
    }
    let fallback_used = !unresolved.is_empty();
    if fallback_used {
        reachable.extend(0..parsed.len());
    }

    let proof_outputs = load_proofs(project, &config.source_proofs)?;
    for (index, node) in parsed.iter_mut().enumerate() {
        if !reachable.contains(&index) {
            continue;
        }
        for proof in &config.source_proofs {
            let name_matches = proof
                .function_names
                .iter()
                .any(|name| name == &node.output.name);
            let symbol_matches = proof
                .function_symbols
                .iter()
                .any(|symbol| symbol == &node.output.symbol);
            if node.output.file == proof.source_file && (name_matches || symbol_matches) {
                if node.output.basis != Basis::Unproved {
                    return Err(format!(
                        "multiple proof classifications for {}",
                        node.output.symbol
                    ));
                }
                let output = proof_outputs
                    .get(&proof.id)
                    .expect("proof output was loaded")
                    .clone();
                if !output.current_source_hash_matches
                    || !output.counts_as_implementation_refinement
                    || !output.proof_obligations_closed
                    || !output.axiom_audit_clean
                {
                    return Err(format!(
                        "proof {:?} cannot classify {} because its source/artifact gate is not current and closed",
                        proof.id, node.output.symbol
                    ));
                }
                node.output.basis = proof.basis.clone();
                node.output.proof = Some(output);
            }
        }
    }

    for proof in &config.source_proofs {
        for expected in &proof.function_names {
            if !parsed.iter().enumerate().any(|(index, node)| {
                reachable.contains(&index)
                    && node.output.file == proof.source_file
                    && node.output.name == *expected
                    && node
                        .output
                        .proof
                        .as_ref()
                        .is_some_and(|item| item.id == proof.id)
            }) {
                return Err(format!(
                    "proof {:?} selector {:?} did not match a reachable source function",
                    proof.id, expected
                ));
            }
        }
        for expected in &proof.function_symbols {
            if !parsed.iter().enumerate().any(|(index, node)| {
                reachable.contains(&index)
                    && node.output.file == proof.source_file
                    && node.output.symbol == *expected
                    && node
                        .output
                        .proof
                        .as_ref()
                        .is_some_and(|item| item.id == proof.id)
            }) {
                return Err(format!(
                    "proof {:?} symbol selector {:?} did not match a reachable source function",
                    proof.id, expected
                ));
            }
        }
    }

    let source_nodes: Vec<_> = parsed
        .into_iter()
        .enumerate()
        .filter(|(index, _)| reachable.contains(index))
        .map(|(_, node)| node.output)
        .collect();
    let callgraph_sha256 = hash_json(&source_nodes)?;
    let unconditional = count_basis(&source_nodes, Basis::UnconditionalSourceBound);
    let conditional = count_basis(&source_nodes, Basis::ConditionalSourceBound);
    let source_model_only = count_basis(&source_nodes, Basis::ModelOnly);
    let unproved = count_basis(&source_nodes, Basis::Unproved);
    let external_closed = config
        .external_boundaries
        .iter()
        .filter(|boundary| boundary.basis == ExternalBasis::FormallyClosed)
        .count();
    let root_composition_proved = false;
    let model_only_artifacts = load_model_artifacts(project)?;
    validate_direct_dependencies(project, &config.external_boundaries)?;
    let generator_path = project.join("formal/coverage-tool/src/main.rs");
    let coverage = Coverage {
        schema: SCHEMA,
        generator: GeneratorIdentity {
            path: relative(project, &generator_path)?,
            sha256: sha256(&fs::read(&generator_path).map_err(|error| error.to_string())?),
            config_path: relative(project, config_path)?,
            config_sha256: sha256(&config_bytes),
        },
        root: RootOutput {
            symbol: config.root.symbol,
            invocation: config.root.invocation,
            source_tree_sha256,
            callgraph_sha256,
            composition_proved: root_composition_proved,
        },
        reachability: Reachability {
            algorithm: "syn-call-overapproximation/v1",
            conservative: true,
            fallback: "all-non-test-source-functions-on-indirect-call",
            fallback_used,
            fallback_reason_nodes: unresolved
                .into_iter()
                .map(|(source_node, categories)| FallbackReason {
                    source_node,
                    categories: categories.into_iter().collect(),
                })
                .collect(),
        },
        metrics: Metrics {
            source_unconditional_proved: unconditional,
            source_conditional_proved: conditional,
            source_model_only,
            source_unproved: unproved,
            source_total: source_nodes.len(),
            source_unconditional_percent: percent(unconditional, source_nodes.len()),
            external_closed,
            external_total: config.external_boundaries.len(),
            external_closed_percent: percent(external_closed, config.external_boundaries.len()),
            root_composition_proved,
            whole_type_system_formally_proven: root_composition_proved
                && unconditional == source_nodes.len()
                && external_closed == config.external_boundaries.len(),
        },
        source_nodes,
        external_boundaries: config.external_boundaries,
        model_only_artifacts,
    };
    serde_json::to_string_pretty(&coverage)
        .map(|rendered| format!("{rendered}\n"))
        .map_err(|error| error.to_string())
}

fn validate_direct_dependencies(
    project: &Path,
    boundaries: &[ExternalBoundary],
) -> Result<(), String> {
    let manifest = fs::read_to_string(project.join("Cargo.toml"))
        .map_err(|error| format!("cannot read Cargo.toml: {error}"))?;
    let mut in_dependencies = false;
    let mut packages = BTreeSet::new();
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('[') {
            in_dependencies = trimmed == "[dependencies]";
            continue;
        }
        if in_dependencies && !trimmed.is_empty() && !trimmed.starts_with('#') {
            let package = trimmed
                .split_once('=')
                .map(|(name, _)| name.trim().to_owned())
                .ok_or_else(|| format!("cannot parse dependency line {trimmed:?}"))?;
            packages.insert(package);
        }
    }
    let classified: BTreeSet<_> = boundaries
        .iter()
        .flat_map(|boundary| boundary.cargo_packages.iter().cloned())
        .collect();
    if packages != classified {
        return Err(format!(
            "external-boundary Cargo package classification drift: dependencies={packages:?}, classified={classified:?}"
        ));
    }
    Ok(())
}

fn rust_source_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect_files(root, "rs", &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_files(root: &Path, extension: &str, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in
        fs::read_dir(root).map_err(|error| format!("cannot read {}: {error}", root.display()))?
    {
        let path = entry.map_err(|error| error.to_string())?.path();
        if path.is_dir() {
            collect_files(&path, extension, files)?;
        } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
            files.push(path);
        }
    }
    Ok(())
}

fn parse_source_file(
    project: &Path,
    file: &Path,
    output: &mut Vec<ParsedNode>,
) -> Result<(), String> {
    let source = fs::read_to_string(file)
        .map_err(|error| format!("cannot read {}: {error}", file.display()))?;
    let syntax = syn::parse_file(&source)
        .map_err(|error| format!("cannot parse {}: {error}", file.display()))?;
    let relative_file = relative(project, file)?;
    let module = relative_file
        .strip_prefix("src/")
        .unwrap_or(&relative_file)
        .strip_suffix(".rs")
        .unwrap_or(&relative_file)
        .replace('/', "::");
    let module = if module == "lib" {
        "maledictus".to_owned()
    } else {
        format!("maledictus::{module}")
    };
    collect_items(&syntax.items, &module, &relative_file, &source, output)
}

fn collect_items(
    items: &[Item],
    module: &str,
    file: &str,
    source: &str,
    output: &mut Vec<ParsedNode>,
) -> Result<(), String> {
    for item in items {
        if cfg_test(item_attrs(item)) {
            continue;
        }
        match item {
            Item::Fn(function) => add_function(module, file, source, function, None, output),
            Item::Impl(item_impl) => collect_impl(module, file, source, item_impl, output),
            Item::Trait(item_trait) => {
                for trait_item in &item_trait.items {
                    if let TraitItem::Fn(function) = trait_item
                        && let Some(block) = &function.default
                    {
                        let owner = format!("trait {}", item_trait.ident);
                        add_block_function(
                            module,
                            file,
                            source,
                            FunctionIdentity {
                                name: function.sig.ident.to_string(),
                                span: function.span(),
                                owner: Some(owner),
                            },
                            block,
                            output,
                        );
                    }
                }
            }
            Item::Mod(ItemMod {
                ident,
                content: Some((_, nested)),
                ..
            }) => {
                collect_items(nested, &format!("{module}::{ident}"), file, source, output)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn item_attrs(item: &Item) -> &[syn::Attribute] {
    match item {
        Item::Const(item) => &item.attrs,
        Item::Enum(item) => &item.attrs,
        Item::ExternCrate(item) => &item.attrs,
        Item::Fn(item) => &item.attrs,
        Item::ForeignMod(item) => &item.attrs,
        Item::Impl(item) => &item.attrs,
        Item::Macro(item) => &item.attrs,
        Item::Mod(item) => &item.attrs,
        Item::Static(item) => &item.attrs,
        Item::Struct(item) => &item.attrs,
        Item::Trait(item) => &item.attrs,
        Item::TraitAlias(item) => &item.attrs,
        Item::Type(item) => &item.attrs,
        Item::Union(item) => &item.attrs,
        Item::Use(item) => &item.attrs,
        _ => &[],
    }
}

fn cfg_test(attributes: &[syn::Attribute]) -> bool {
    attributes.iter().any(|attribute| {
        let rendered = attribute
            .meta
            .to_token_stream()
            .to_string()
            .replace(' ', "");
        rendered == "cfg(test)" || rendered == "test"
    })
}

fn collect_impl(
    module: &str,
    file: &str,
    source: &str,
    item_impl: &ItemImpl,
    output: &mut Vec<ParsedNode>,
) {
    let owner = item_impl
        .self_ty
        .to_token_stream()
        .to_string()
        .replace(' ', "");
    for item in &item_impl.items {
        if let ImplItem::Fn(function) = item {
            if cfg_test(&function.attrs) {
                continue;
            }
            add_block_function(
                module,
                file,
                source,
                FunctionIdentity {
                    name: function.sig.ident.to_string(),
                    span: function.span(),
                    owner: Some(owner.clone()),
                },
                &function.block,
                output,
            );
        }
    }
}

fn add_function(
    module: &str,
    file: &str,
    source: &str,
    function: &ItemFn,
    owner: Option<String>,
    output: &mut Vec<ParsedNode>,
) {
    add_block_function(
        module,
        file,
        source,
        FunctionIdentity {
            name: function.sig.ident.to_string(),
            span: function.span(),
            owner,
        },
        &function.block,
        output,
    );
}

fn add_block_function(
    module: &str,
    file: &str,
    source: &str,
    identity: FunctionIdentity,
    block: &syn::Block,
    output: &mut Vec<ParsedNode>,
) {
    let symbol = identity
        .owner
        .as_ref()
        .map(|owner| format!("{module}::<{owner}>::{}", identity.name))
        .unwrap_or_else(|| format!("{module}::{}", identity.name));
    let line_start = identity.span.start().line;
    let line_end = identity.span.end().line;
    let source_sha256 = hash_lines(source, line_start, line_end);
    let id =
        sha256(format!("{symbol}\0{file}\0{line_start}\0{line_end}\0{source_sha256}").as_bytes());
    let mut calls = CallVisitor::default();
    calls.visit_block(block);
    output.push(ParsedNode {
        output: SourceNode {
            id,
            symbol,
            name: identity.name,
            file: file.to_owned(),
            line_start,
            line_end,
            source_sha256,
            basis: Basis::Unproved,
            proof: None,
            calls: calls.direct_names.iter().cloned().collect(),
        },
        direct_names: calls.direct_names,
        indirect_calls: calls.indirect_calls,
    });
}

fn hash_lines(source: &str, start: usize, end: usize) -> String {
    let selected = source
        .lines()
        .skip(start.saturating_sub(1))
        .take(end.saturating_sub(start) + 1)
        .collect::<Vec<_>>()
        .join("\n");
    sha256(selected.as_bytes())
}

fn load_proofs(
    project: &Path,
    proofs: &[ProofConfig],
) -> Result<BTreeMap<String, ProofOutput>, String> {
    let mut output = BTreeMap::new();
    for proof in proofs {
        if proof.basis == Basis::ModelOnly || proof.basis == Basis::Unproved {
            return Err(format!("source proof {:?} has invalid basis", proof.id));
        }
        let manifest_path = project.join(&proof.manifest);
        let bytes = fs::read(&manifest_path)
            .map_err(|error| format!("cannot read {}: {error}", manifest_path.display()))?;
        let manifest: serde_json::Value = serde_json::from_slice(&bytes)
            .map_err(|error| format!("invalid {}: {error}", manifest_path.display()))?;
        let source_path = manifest["source"]["path"]
            .as_str()
            .ok_or_else(|| format!("{} omits source.path", proof.manifest))?;
        if source_path != proof.source_file {
            return Err(format!(
                "proof {:?} source path does not match config",
                proof.id
            ));
        }
        let expected_hash = manifest["source"]["sha256"]
            .as_str()
            .ok_or_else(|| format!("{} omits source.sha256", proof.manifest))?;
        let current_hash =
            sha256(&fs::read(project.join(source_path)).map_err(|error| error.to_string())?);
        let current_source_hash_matches = expected_hash == current_hash;
        let counts_as_implementation_refinement =
            manifest["counts_as_implementation_refinement"] == true;
        let manifest_function_names = if proof.manifest_function_names.is_empty() {
            &proof.function_names
        } else {
            &proof.manifest_function_names
        };
        if manifest_function_names.is_empty() {
            return Err(format!(
                "proof {:?} must name at least one manifest function",
                proof.id
            ));
        }
        let proof_obligations_closed =
            proof_functions_are_universally_proved(&manifest, manifest_function_names);
        validate_manifest_artifact_hashes(project, &proof.manifest, &manifest)?;
        let checked_theorem = manifest
            .pointer("/lean_build/public_theorem")
            .and_then(|value| value.as_str())
            .or_else(|| {
                manifest
                    .pointer("/proof_progress/public_theorem")
                    .and_then(|value| value.as_str())
            })
            .or_else(|| {
                manifest
                    .pointer("/public_theorem")
                    .and_then(|value| value.as_str())
            });
        let theorem_listed = manifest
            .pointer("/proof_progress/checked_theorems")
            .and_then(|value| value.as_array())
            .is_some_and(|items| {
                items
                    .iter()
                    .any(|item| item.as_str() == Some(&proof.theorem))
            });
        if checked_theorem != Some(proof.theorem.as_str()) && !theorem_listed {
            return Err(format!(
                "proof {:?} theorem {:?} is not the manifest public theorem {:?}",
                proof.id, proof.theorem, checked_theorem
            ));
        }
        let detailed_axiom_audit_clean =
            manifest["axiom_audits"].as_array().is_some_and(|audits| {
                audits.iter().any(|audit| {
                    audit["contains_sorry_ax"] == false
                        && axiom_audit_names_theorem(audit, &proof.theorem)
                })
            });
        let declared_axiom_audit_clean = manifest
            .pointer("/proof_progress/axiom_dependency_audited")
            .and_then(|value| value.as_bool())
            == Some(true)
            && manifest["proof_project"]
                .as_array()
                .is_some_and(|artifacts| {
                    artifacts.iter().any(|artifact| {
                        artifact["path"]
                            .as_str()
                            .is_some_and(|path| path.ends_with("/AxiomAudit.lean"))
                    })
                });
        let axiom_audit_clean = detailed_axiom_audit_clean || declared_axiom_audit_clean;
        output.insert(
            proof.id.clone(),
            ProofOutput {
                id: proof.id.clone(),
                manifest: proof.manifest.clone(),
                manifest_sha256: sha256(&bytes),
                theorem: proof.theorem.clone(),
                current_source_hash_matches,
                counts_as_implementation_refinement,
                proof_obligations_closed,
                axiom_audit_clean,
            },
        );
    }
    Ok(output)
}

fn proof_functions_are_universally_proved(
    manifest: &serde_json::Value,
    function_names: &[String],
) -> bool {
    if let Some(functions) = manifest
        .pointer("/source/extracted_functions")
        .and_then(|value| value.as_array())
    {
        return function_names.iter().all(|expected| {
            functions.iter().any(|function| {
                function["name"].as_str() == Some(expected.as_str())
                    && function["universally_proved"] == true
            })
        });
    }

    manifest["open_obligations"]
        .as_array()
        .is_some_and(Vec::is_empty)
}

fn axiom_audit_names_theorem(audit: &serde_json::Value, theorem: &str) -> bool {
    audit["theorem"].as_str() == Some(theorem)
        || audit["theorems"].as_array().is_some_and(|theorems| {
            theorems
                .iter()
                .any(|candidate| candidate.as_str() == Some(theorem))
        })
}

fn validate_manifest_artifact_hashes(
    project: &Path,
    manifest_path: &str,
    manifest: &serde_json::Value,
) -> Result<(), String> {
    for key in ["manifest", "generated", "external_models", "proof_project"] {
        let Some(value) = manifest.get(key) else {
            continue;
        };
        let records: Vec<&serde_json::Value> = match value {
            serde_json::Value::Array(items) => items.iter().collect(),
            serde_json::Value::Object(_) => vec![value],
            _ => {
                return Err(format!(
                    "{manifest_path} has invalid {key} artifact records"
                ));
            }
        };
        for record in records {
            let Some(path) = record.get("path").and_then(|value| value.as_str()) else {
                continue;
            };
            let Some(expected) = record.get("sha256").and_then(|value| value.as_str()) else {
                return Err(format!("{manifest_path} artifact {path} omits sha256"));
            };
            let bytes = fs::read(project.join(path))
                .map_err(|error| format!("cannot read artifact {path}: {error}"))?;
            if sha256(&bytes) != expected {
                return Err(format!("{manifest_path} artifact {path} has a stale hash"));
            }
        }
    }
    Ok(())
}

fn load_model_artifacts(project: &Path) -> Result<Vec<ModelArtifact>, String> {
    let mut files = Vec::new();
    collect_files(&project.join("formal/Maledictus"), "lean", &mut files)?;
    files.sort();
    files
        .into_iter()
        .map(|path| {
            let bytes = fs::read(&path).map_err(|error| error.to_string())?;
            let text = String::from_utf8(bytes.clone()).map_err(|error| error.to_string())?;
            let declarations = text
                .lines()
                .filter(|line| {
                    let trimmed = line.trim_start();
                    trimmed.starts_with("theorem ") || trimmed.starts_with("lemma ")
                })
                .count();
            Ok(ModelArtifact {
                path: relative(project, &path)?,
                sha256: sha256(&bytes),
                theorem_or_lemma_declarations: declarations,
                basis: Basis::ModelOnly,
                counts_toward_source_numerator: false,
            })
        })
        .collect()
}

fn hash_tree(project: &Path, files: &[PathBuf]) -> Result<String, String> {
    let mut hasher = Sha256::new();
    for file in files {
        let relative = relative(project, file)?;
        hasher.update(relative.as_bytes());
        hasher.update([0]);
        hasher.update(fs::read(file).map_err(|error| error.to_string())?);
        hasher.update([0]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn hash_json<T: Serialize>(value: &T) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| sha256(&bytes))
        .map_err(|error| error.to_string())
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn relative(project: &Path, path: &Path) -> Result<String, String> {
    path.strip_prefix(project)
        .map(|relative| relative.to_string_lossy().replace('\\', "/"))
        .map_err(|_| format!("{} is outside {}", path.display(), project.display()))
}

fn count_basis(nodes: &[SourceNode], basis: Basis) -> usize {
    nodes.iter().filter(|node| node.basis == basis).count()
}

fn percent(part: usize, total: usize) -> String {
    if total == 0 {
        "0.00".to_owned()
    } else {
        format!("{:.2}", 100.0 * part as f64 / total as f64)
    }
}

use quote::ToTokens;

#[cfg(test)]
mod tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;

    struct Fixture {
        root: PathBuf,
    }

    impl Fixture {
        fn new(source: &str) -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system clock must be after the epoch")
                .as_nanos();
            let root = env::temp_dir().join(format!(
                "maledictus-formal-coverage-{}-{unique}",
                std::process::id()
            ));
            fs::create_dir_all(root.join("src")).unwrap();
            fs::create_dir_all(root.join("formal/Maledictus")).unwrap();
            fs::create_dir_all(root.join("formal/coverage-tool/src")).unwrap();
            fs::write(root.join("src/lib.rs"), source).unwrap();
            fs::write(
                root.join("formal/Maledictus/Model.lean"),
                "theorem model : True := by trivial\n",
            )
            .unwrap();
            fs::write(
                root.join("formal/coverage-tool/src/main.rs"),
                "fixture generator\n",
            )
            .unwrap();
            fs::write(
                root.join("Cargo.toml"),
                "[package]\nname = \"fixture\"\nversion = \"0.0.0\"\n\n[dependencies]\n",
            )
            .unwrap();
            fs::write(
                root.join("formal/coverage-config.json"),
                serde_json::to_vec_pretty(&serde_json::json!({
                    "schema": SCHEMA,
                    "root": {
                        "symbol": "maledictus::verify_internal",
                        "invocation": "verify_internal(request, issuance=true)"
                    },
                    "source_proofs": [],
                    "external_boundaries": []
                }))
                .unwrap(),
            )
            .unwrap();
            Self { root }
        }

        fn generate(&self) -> String {
            generate(&self.root, &self.root.join("formal/coverage-config.json")).unwrap()
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.root).unwrap();
        }
    }

    #[test]
    fn unresolved_indirect_call_expands_to_every_production_function() {
        let fixture = Fixture::new(
            "fn verify_internal(callback: fn()) { callback(); }\nfn otherwise_unreachable() {}\n#[cfg(test)] mod tests { fn excluded_test() {} }\n",
        );
        let coverage: serde_json::Value = serde_json::from_str(&fixture.generate()).unwrap();
        assert_eq!(coverage["reachability"]["fallback_used"], true);
        assert_eq!(coverage["metrics"]["source_total"], 2);
        assert!(
            coverage["source_nodes"]
                .as_array()
                .unwrap()
                .iter()
                .any(|node| {
                    node["symbol"] == "maledictus::otherwise_unreachable"
                        && node["basis"] == "unproved"
                })
        );
    }

    #[test]
    fn source_drift_makes_the_checked_artifact_fail() {
        let fixture = Fixture::new("fn verify_internal() {}\n");
        let recorded = fixture.generate();
        fs::write(
            fixture.root.join("src/lib.rs"),
            "fn verify_internal() {}\nfn newly_added() {}\n",
        )
        .unwrap();
        let regenerated = fixture.generate();
        let error = check_rendered(
            &recorded,
            &regenerated,
            &fixture.root.join("formal/coverage.json"),
        )
        .unwrap_err();
        assert!(error.contains("is stale"));
    }

    #[test]
    fn abstract_lean_model_never_enters_source_numerator() {
        let fixture = Fixture::new("fn verify_internal() {}\n");
        let coverage: serde_json::Value = serde_json::from_str(&fixture.generate()).unwrap();
        assert_eq!(coverage["metrics"]["source_unconditional_proved"], 0);
        assert_eq!(coverage["model_only_artifacts"][0]["basis"], "model-only");
        assert_eq!(
            coverage["model_only_artifacts"][0]["counts_toward_source_numerator"],
            false
        );
    }

    #[test]
    fn a_proved_kernel_remains_closed_when_a_sibling_kernel_is_open() {
        let manifest = serde_json::json!({
            "source": {
                "extracted_functions": [
                    {"name": "proved", "universally_proved": true},
                    {"name": "open", "universally_proved": false}
                ]
            },
            "open_obligations": ["open"]
        });
        assert!(proof_functions_are_universally_proved(
            &manifest,
            &["proved".to_owned()]
        ));
        assert!(!proof_functions_are_universally_proved(
            &manifest,
            &["open".to_owned()]
        ));
    }

    #[test]
    fn an_axiom_audit_must_name_the_claimed_theorem() {
        let audit = serde_json::json!({
            "theorems": ["Proofs.first", "Proofs.second"],
            "contains_sorry_ax": false
        });
        assert!(axiom_audit_names_theorem(&audit, "Proofs.second"));
        assert!(!axiom_audit_names_theorem(&audit, "Proofs.unrelated"));
    }
}
