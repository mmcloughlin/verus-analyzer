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

pub(crate) fn wp_single_branch(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let assert_keyword = ctx.find_token_syntax_at_offset(T![assert])?;
    let assert_expr = ast::AssertExpr::cast(assert_keyword.parent()?)?;
    let assert_range = assert_keyword.text_range();
    let cursor_in_range = assert_range.contains_range(ctx.selection_trimmed());

    if !cursor_in_range {
        return None;
    }
    let block: ast::BlockExpr = ctx.find_node_at_offset::<ast::BlockExpr>()?;
    let first_node = &block.stmt_list()?.syntax().first_child()?;
    let cur_stmt = ctx.find_node_at_offset::<ast::Stmt>()?;
    let cur_node = cur_stmt.syntax();

    // mut be the first statment of the block
    if cur_node != first_node {
        return None;
    }

    // the block must belong to an if expression
    let if_node = block.syntax().parent()?;
    let if_range = if_node.text_range();
    let if_expr = ast::IfExpr::cast(if_node)?;
    let cond = if_expr.condition()?;

    acc.add(
        AssistId("wp_single_branch", AssistKind::RefactorRewrite),
        "Weakest precondition for single branch",
        if_range,
        |edit| {
            let indent = ast::edit::AstNodeEdit::indent_level(&if_expr);
            let sep = format!("\n{indent}");
            let p = &cond.to_string();
            let q = &assert_expr.expr().unwrap().to_string();
            let res = format!("assert({} ==> ({}));{}", p, q, sep);
            edit.insert(if_range.start(), res);
        },
    )
}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn wp_assign_easy() {
        check_assist(
            wp_single_branch,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    a = 8;
    if (a < 10) {
        ass$0ert(a > 10 && a < 100);
    }
}
"#,
            r#"
fn foo()
{
    let mut a:u32 = 1;
    a = 8;
    assert((a < 10) ==> (a > 10 && a < 100));
    if (a < 10) {
        assert(a > 10 && a < 100);
    }
}
"#,
        );
    }
}
