use crate::{AssistContext, AssistId, AssistKind, Assists};
use syntax::{
    ast::{self, HasAttrs},
    AstNode,
};

// TODO(verus): maybe when "lower"ing, register proof visibility on HIR semantics as well
//
//

// opacify selected function and reveal at every assertioin
//
//
// Verus says: "trigger must be a function call, a field access, or a bitwise operator",
// For now, ignore field access and bitwise ops
//
// 1.
// Similar to "intro_requires", opacify the function in the cursor range
// "#[verifier(opaque)]"
//
//
// 2.
// Reveal at every call site
// Spec function will be inside "assert", "requires", and "ensures"
// for now, deal with "assert" only

// let function = ctx.sema.to_def(&ast_func)?;
// let params = get_fn_params(ctx.sema.db, function, &param_list)?;
// let usages = Definition::Function(function).usages(&ctx.sema);

// see toggle_ignore's `fn has_ignore_attribute` for more info
fn has_opaque_attribute(fn_def: &ast::Fn) -> Option<ast::Attr> {
    fn_def.attrs().find(|attr| {
        attr.meta().map(|it| {
            dbg!(it.syntax());
            it.syntax().text() == "verifier(opaque)"
        }) == Some(true)
    })
}

pub(crate) fn opacify_function(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // get hir-def of function
    let (function, callinfo) = ctx.get_function_from_callsite()?;
    // get CST node of function
    let fn_source = ctx.sema.source(function)?;

    // if it is already opaque (it has #[verifier(opaque)]), return None
    if let Some(_) = has_opaque_attribute(&fn_source.value) {
        return None;
    }

    // TODO use ".usages" to reveal things

    let fn_start = fn_source.value.syntax().text_range().start();
    acc.add(
        AssistId("opacify_function", AssistKind::RefactorRewrite),
        "Make this function opaque and reveal at every callsite",
        callinfo.node.syntax().text_range(),
        |edit| {
            edit.insert(fn_start, "#[verifier(opaque)]\n");
        },
    )
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    #[test]
    fn opacify_function_easy() {
        check_assist(
            opacify_function,
            r#"
spec fn f1(i: int) -> int {
    i + 1
}

fn assert_by_test() {
    assert(f1$0(3) > 3)
}
"#,
            r#"
#[verifier(opaque)]
spec fn f1(i: int) -> int {
    i + 1
}

fn assert_by_test() {
    assert(f1(3) > 3) by {
        reveal(f1);
    }
}
"#,
        );
    }

    #[test]
    fn opacify_function_not_applicable() {
        check_assist_not_applicable(
            opacify_function,
            r#"
#[verifier(opaque)]
spec fn f1(i: int) -> int {
    i + 1
}

fn assert_by_test() {
    assert(f1$0(3) > 3);
}
"#,
        );
    }
}
