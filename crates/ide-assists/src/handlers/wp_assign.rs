use crate::{AssistContext, Assists};
use hir::{HasCrate, PathResolution};
use ide_db::{
    assists::{AssistId, AssistKind},
    syntax_helpers::node_ext::walk_expr,
};
use syntax::ted;

use syntax::{
    ast::{self, Expr},
    AstNode, SyntaxToken, T,
};

// TODO: is this the perfered way to get the previous statment?
fn get_prev_stmt(ctx: &AssistContext<'_>) -> Option<ast::Stmt> {
    let block: ast::BlockExpr = ctx.find_node_at_offset::<ast::BlockExpr>()?;
    let statements = block.stmt_list()?.statements();
    let cur_stmt: ast::Stmt = ctx.find_node_at_offset::<ast::Stmt>()?;
    let mut prev = None;
    for stmt in statements {
        if cur_stmt != stmt {
            prev = Some(stmt);
        } else {
            break;
        }
    }
    prev
}

fn is_assign_stmt(stmt: ast::Stmt) -> Option<ast::BinExpr> {
    let mut res = None;
    if let ast::Stmt::ExprStmt(stmt) = stmt {
        let bin_expr = ast::BinExpr::cast(stmt.syntax().first_child()?)?;
        if let Some(expr_op) = bin_expr.op_kind() {
            if expr_op == (ast::BinaryOp::Assignment { op: None }) {
                res = Some(bin_expr);
            }
        }
    }
    res
}

fn expr_contains_call(expr: &Expr) -> bool {
    let mut has_call = false;
    let cb = &mut |e: Expr| {
        if let ast::Expr::CallExpr { .. } = e {
            has_call = true;
        }
    };
    walk_expr(expr, cb);
    has_call
}

fn reoslve_local(e: &Expr, ctx: &AssistContext<'_>) -> Option<hir::Local> {
    let pexpr = ast::PathExpr::cast(e.syntax().clone())?;
    let pres = ctx.sema.resolve_path(&pexpr.path()?)?;
    if let PathResolution::Local(local) = pres {
        Some(local)
    } else {
        None
    }
}

fn local_usages(
    expr: &ast::Expr,
    target: &hir::Local,
    ctx: &AssistContext<'_>,
) -> Vec<syntax::SyntaxElement> {
    let mut vec = vec![];
    let cb = &mut |e: Expr| {
        if let Some(current) = reoslve_local(&e, ctx) {
            if current == *target {
                vec.push(ted::Element::syntax_element(e.syntax()));
            }
        }
    };
    walk_expr(&expr, cb);
    vec
}

pub(crate) fn wp_assign(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let assert_keyword = ctx.find_token_syntax_at_offset(T![assert])?;
    let assert_expr = ast::Expr::cast(assert_keyword.parent()?)?;
    let assert_range = assert_keyword.text_range();
    let cursor_in_range = assert_range.contains_range(ctx.selection_trimmed());

    if !cursor_in_range {
        return None;
    }

    let assign_stmt = get_prev_stmt(ctx)?;
    let assign_stmt = is_assign_stmt(assign_stmt)?;
    let rhs = assign_stmt.rhs()?;

    if expr_contains_call(&rhs) {
        // TODO: handle call? read ensures? unfold definition?
        dbg!("wp assgin rhs contains call");
        return None;
    }

    let assign_range = assign_stmt.syntax().text_range();
    // ctx.sema.to_def(&assign_stmt);

    if let Some(target) = reoslve_local(&assign_stmt.lhs()?, ctx) {
        let assert_expr = assert_expr.clone_for_update();
        let usages: Vec<syntax::SyntaxElement> = local_usages(&assert_expr, &target, ctx);
        for usage in usages {
            ted::replace(usage, ted::Element::syntax_element(rhs.clone_for_update().syntax()));
        }
        acc.add(
            AssistId("wp_assign", AssistKind::RefactorRewrite),
            "Weakest precondition for assign",
            assign_range,
            |edit| {
                edit.insert(assign_range.start(), format!("{};\n    ", assert_expr));
            },
        )
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn wp_assign_easy() {
        check_assist(
            wp_assign,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    a = 8;
    ass$0ert(a > 10 && a < 100);
}
"#,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    assert(8 > 10 && 8 < 100);
    a = 8;
    assert(a > 10 && a < 100);
}
"#,
        );
    }
    #[test]
    fn wp_assign_expr() {
        check_assist(
            wp_assign,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    a = 8 + 9;
    ass$0ert(a > 10 && a < 100);
}
"#,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    assert(8 + 9 > 10 && 8 + 9 < 100);
    a = 8 + 9;
    assert(a > 10 && a < 100);
}
"#,
        );
    }
}
