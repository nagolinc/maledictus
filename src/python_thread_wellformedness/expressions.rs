//! Traverses contract/runtime expressions and delegates thread-specific call checks.

use rustpython_parser::ast;

use super::calls::{
    callee_is_thread, is_direct_get_method_call, record, resolve_target, thread_symbol,
    validate_thread_constructor, validate_thread_lifecycle_call,
};
use super::{
    Bindings, Candidate, Catalog, FunctionContext, INVALID_ARG_USE, INVALID_GET_METHOD_USE,
    ThreadSymbol,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn validate_expression(
    expression: &ast::Expr,
    bindings: &Bindings,
    catalog: &Catalog,
    context: &FunctionContext,
    candidates: &mut Vec<Candidate>,
    allow_get_method: bool,
    allow_arg: bool,
) {
    match expression {
        ast::Expr::Call(call) => {
            let symbol = thread_symbol(&call.func, bindings, context);
            if symbol == Some(ThreadSymbol::GetMethod) && !allow_get_method {
                record(
                    candidates,
                    call,
                    INVALID_GET_METHOD_USE,
                    "getMethod is valid only as a direct method-identity comparison operand",
                );
            }
            if symbol == Some(ThreadSymbol::Arg) && !allow_arg {
                record(
                    candidates,
                    call,
                    INVALID_ARG_USE,
                    "arg is valid only inside the value expression of getOld",
                );
            }
            if callee_is_thread(&call.func, bindings, context) {
                validate_thread_constructor(call, catalog, context, candidates);
            }
            if let ast::Expr::Attribute(method) = call.func.as_ref()
                && matches!(method.value.as_ref(), ast::Expr::Name(receiver)
                    if context.thread_locals.contains(receiver.id.as_str()))
                && matches!(method.attr.as_str(), "start" | "join")
            {
                validate_thread_lifecycle_call(
                    call,
                    method.attr.as_str(),
                    catalog,
                    context,
                    candidates,
                );
            }
            validate_expression(
                &call.func, bindings, catalog, context, candidates, false, allow_arg,
            );
            for (index, argument) in call.args.iter().enumerate() {
                let nested_arg_allowed = symbol == Some(ThreadSymbol::GetOld) && index == 1;
                validate_expression(
                    argument,
                    bindings,
                    catalog,
                    context,
                    candidates,
                    false,
                    nested_arg_allowed,
                );
            }
            for keyword in &call.keywords {
                validate_expression(
                    &keyword.value,
                    bindings,
                    catalog,
                    context,
                    candidates,
                    false,
                    false,
                );
            }
        }
        ast::Expr::Compare(comparison) => {
            let direct_method_comparison = comparison.ops.len() == 1
                && matches!(comparison.ops[0], ast::CmpOp::Eq | ast::CmpOp::NotEq)
                && comparison.comparators.len() == 1;
            let allow_left = direct_method_comparison
                && is_direct_get_method_call(&comparison.left, bindings, context)
                && resolve_target(&comparison.comparators[0], catalog, context).is_some();
            let allow_right = direct_method_comparison
                && is_direct_get_method_call(&comparison.comparators[0], bindings, context)
                && resolve_target(&comparison.left, catalog, context).is_some();
            validate_expression(
                &comparison.left,
                bindings,
                catalog,
                context,
                candidates,
                allow_left,
                allow_arg,
            );
            for comparator in &comparison.comparators {
                validate_expression(
                    comparator,
                    bindings,
                    catalog,
                    context,
                    candidates,
                    allow_right,
                    allow_arg,
                );
            }
        }
        ast::Expr::BoolOp(operation) => {
            for value in &operation.values {
                validate_expression(
                    value, bindings, catalog, context, candidates, false, allow_arg,
                );
            }
        }
        ast::Expr::BinOp(operation) => {
            validate_expression(
                &operation.left,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
            validate_expression(
                &operation.right,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
        }
        ast::Expr::UnaryOp(operation) => validate_expression(
            &operation.operand,
            bindings,
            catalog,
            context,
            candidates,
            false,
            allow_arg,
        ),
        ast::Expr::IfExp(branch) => {
            validate_expression(
                &branch.test,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
            validate_expression(
                &branch.body,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
            validate_expression(
                &branch.orelse,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
        }
        ast::Expr::Attribute(attribute) => validate_expression(
            &attribute.value,
            bindings,
            catalog,
            context,
            candidates,
            false,
            allow_arg,
        ),
        ast::Expr::Subscript(subscript) => {
            validate_expression(
                &subscript.value,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
            validate_expression(
                &subscript.slice,
                bindings,
                catalog,
                context,
                candidates,
                false,
                allow_arg,
            );
        }
        ast::Expr::Tuple(tuple) => {
            for value in &tuple.elts {
                validate_expression(
                    value, bindings, catalog, context, candidates, false, allow_arg,
                );
            }
        }
        ast::Expr::List(list) => {
            for value in &list.elts {
                validate_expression(
                    value, bindings, catalog, context, candidates, false, allow_arg,
                );
            }
        }
        _ => {}
    }
}
