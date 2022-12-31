use std::{vec};

use crate::{AssistContext, AssistId, AssistKind, Assists};
use hir::{Adt, HasSource, Semantics, known::le};
use ide_db::{syntax_helpers::node_ext::walk_expr, RootDatabase, base_db::salsa::debug};

use syntax::{
    ast::{self, edit_in_place::Indent, Expr, HasName, HasAttrs, BinaryOp},
    AstNode, T,
};

// TODO: is this the perfered way to get the previous statment?
fn get_prev_stmt(ctx: &AssistContext<'_>) -> Option<ast::Stmt>
{
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

fn is_assign_stmt(stmt: &ast::Stmt) -> Option<()> 
{
    let mut res = None;
    if let ast::Stmt::ExprStmt(stmt) = stmt {
        let bin_expr = ast::BinExpr::cast(stmt.syntax().first_child()?)?;
        if let Some(expr_op) = bin_expr.op_kind() {
            if expr_op == (ast::BinaryOp::Assignment {op: None}) {
                dbg!("assign");
                res = Some(());
            }
        } 
    }
    res
}

pub(crate) fn wp_assign(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let assert_keyword = ctx.find_token_syntax_at_offset(T![assert])?;
    let assert_expr = ast::AssertExpr::cast(assert_keyword.parent()?)?;
    let assert_range = assert_keyword.text_range();
    let cursor_in_range = assert_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    let foo = get_prev_stmt(ctx)?;
    let _ = is_assign_stmt(&foo)?;

    None
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
fn assign_wp() 
{
    let mut a:u32 = 1;
    a = 0;
    ass$0ert(a > 10);
}
"#,
r#"
fn assign_wp() 
{
    assert(1 > 10);
    let a:u32 = 1;
    assert(a > 10);
}      
"#,
        );
    }
}
