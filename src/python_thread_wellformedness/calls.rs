//! Validates thread construction, lifecycle calls, and thread contract-expression operands.

use rustpython_ast::Ranged;
use rustpython_parser::ast;

use super::{
    Bindings, Candidate, Catalog, FunctionContext, FunctionInfo, INVALID_THREAD_CREATION,
    INVALID_THREAD_JOIN, INVALID_THREAD_START, ThreadSymbol,
};

pub(super) fn is_direct_get_method_call(
    expression: &ast::Expr,
    bindings: &Bindings,
    context: &FunctionContext,
) -> bool {
    let ast::Expr::Call(call) = expression else {
        return false;
    };
    thread_symbol(&call.func, bindings, context) == Some(ThreadSymbol::GetMethod)
        && call.args.len() == 1
        && call.keywords.is_empty()
        && matches!(call.args[0], ast::Expr::Name(ref receiver)
            if context.thread_locals.contains(receiver.id.as_str()))
}

pub(super) fn validate_thread_constructor(
    call: &ast::ExprCall,
    catalog: &Catalog,
    context: &FunctionContext,
    candidates: &mut Vec<Candidate>,
) {
    let target = call_argument(call, 1, "target");
    let args = call_argument(call, 3, "args");
    let Some(target) = target else {
        record(
            candidates,
            call,
            INVALID_THREAD_CREATION,
            "Thread construction requires an explicit target",
        );
        return;
    };
    let Some(info) = resolve_target(target, catalog, context) else {
        record(
            candidates,
            call,
            INVALID_THREAD_CREATION,
            "Thread target must resolve to a declared source method",
        );
        return;
    };
    if info.pure || info.predicate {
        record(
            candidates,
            call,
            INVALID_THREAD_CREATION,
            "Thread target must be an impure non-predicate method",
        );
        return;
    }
    let Some(ast::Expr::Tuple(arguments)) = args else {
        record(
            candidates,
            call,
            INVALID_THREAD_CREATION,
            "Thread args must be an explicit tuple matching the target parameters",
        );
        return;
    };
    if arguments.elts.len() < info.required_count || arguments.elts.len() > info.positional_count {
        record(
            candidates,
            call,
            INVALID_THREAD_CREATION,
            "Thread args arity does not match the target method",
        );
    }
}

pub(super) fn validate_thread_lifecycle_call(
    call: &ast::ExprCall,
    method: &str,
    catalog: &Catalog,
    context: &FunctionContext,
    candidates: &mut Vec<Candidate>,
) {
    let code = if method == "start" {
        INVALID_THREAD_START
    } else {
        INVALID_THREAD_JOIN
    };
    if !call.keywords.is_empty() {
        record(
            candidates,
            call,
            code,
            "Thread lifecycle target options must be positional source methods",
        );
        return;
    }
    for target in &call.args {
        let Some(info) = resolve_target(target, catalog, context) else {
            record(
                candidates,
                call,
                code,
                "Thread lifecycle target option is not a declared source method",
            );
            return;
        };
        if info.pure || info.predicate || (method == "start" && info.has_obligation_postcondition) {
            record(
                candidates,
                call,
                code,
                "Thread lifecycle target option is not fork/join compatible",
            );
            return;
        }
    }
}

fn call_argument<'a>(
    call: &'a ast::ExprCall,
    position: usize,
    keyword: &str,
) -> Option<&'a ast::Expr> {
    call.args.get(position).or_else(|| {
        call.keywords
            .iter()
            .find(|item| {
                item.arg
                    .as_ref()
                    .is_some_and(|name| name.as_str() == keyword)
            })
            .map(|item| &item.value)
    })
}

pub(super) fn resolve_target<'a>(
    expression: &ast::Expr,
    catalog: &'a Catalog,
    context: &FunctionContext,
) -> Option<&'a FunctionInfo> {
    match expression {
        ast::Expr::Name(name) if !context.local_names.contains(name.id.as_str()) => {
            catalog.functions.get(name.id.as_str())
        }
        ast::Expr::Attribute(attribute) => match attribute.value.as_ref() {
            ast::Expr::Name(owner) if catalog.classes.contains(owner.id.as_str()) => catalog
                .methods
                .get(owner.id.as_str())?
                .get(attribute.attr.as_str()),
            ast::Expr::Name(owner) => {
                let class = context.nominal_locals.get(owner.id.as_str())?;
                catalog.methods.get(class)?.get(attribute.attr.as_str())
            }
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn annotation_is_thread(annotation: Option<&ast::Expr>, bindings: &Bindings) -> bool {
    annotation.is_some_and(|annotation| match annotation {
        ast::Expr::Name(name) => {
            bindings.thread_names.get(name.id.as_str()) == Some(&ThreadSymbol::Thread)
        }
        ast::Expr::Attribute(attribute) => {
            attribute.attr.as_str() == "Thread"
                && matches!(attribute.value.as_ref(), ast::Expr::Name(module)
                    if bindings.thread_modules.contains(module.id.as_str()))
        }
        _ => false,
    })
}

pub(super) fn annotation_class<'a>(
    annotation: Option<&ast::Expr>,
    catalog: &'a Catalog,
) -> Option<&'a str> {
    let ast::Expr::Name(name) = annotation? else {
        return None;
    };
    catalog.classes.get(name.id.as_str()).map(String::as_str)
}

pub(super) fn callee_is_thread(
    callee: &ast::Expr,
    bindings: &Bindings,
    context: &FunctionContext,
) -> bool {
    thread_symbol(callee, bindings, context) == Some(ThreadSymbol::Thread)
}

pub(super) fn thread_symbol(
    expression: &ast::Expr,
    bindings: &Bindings,
    context: &FunctionContext,
) -> Option<ThreadSymbol> {
    match expression {
        ast::Expr::Name(name) if !context.local_names.contains(name.id.as_str()) => {
            bindings.thread_names.get(name.id.as_str()).copied()
        }
        ast::Expr::Attribute(attribute) => {
            let ast::Expr::Name(module) = attribute.value.as_ref() else {
                return None;
            };
            if !bindings.thread_modules.contains(module.id.as_str()) {
                return None;
            }
            match attribute.attr.as_str() {
                "Thread" => Some(ThreadSymbol::Thread),
                "getMethod" => Some(ThreadSymbol::GetMethod),
                "getOld" => Some(ThreadSymbol::GetOld),
                "arg" => Some(ThreadSymbol::Arg),
                _ => None,
            }
        }
        _ => None,
    }
}

pub(super) fn record(
    candidates: &mut Vec<Candidate>,
    ranged: &impl Ranged,
    code: &'static str,
    message: &'static str,
) {
    candidates.push(Candidate {
        code,
        message,
        byte_offset: u32::from(ranged.range().start()),
    });
}
