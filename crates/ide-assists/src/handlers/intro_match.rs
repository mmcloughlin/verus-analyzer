use crate::{AssistContext, AssistId, AssistKind, Assists, PostFailure};
use ide_db::syntax_helpers::node_ext::{for_each_tail_expr, walk_expr};

use syntax::{
    ast::{self, edit::AstNodeEdit, make, Expr},
    match_ast, AstNode, TextRange,
};

pub(crate) fn intro_match(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // setup basic variables
    let func: ast::Fn = ctx.find_node_at_offset::<ast::Fn>()?;
    let body: ast::BlockExpr = func.body()?;
    // // let ensures: ast::EnsuresClause = func.ensures_clause()?;

    // // // trigger on "ensures"
    // // // check if cursor is on "ensures" keyword
    // // let ensures_keyword = ensures.ensures_token()?;
    // // let cursor_in_range = ensures_keyword.text_range().contains_range(ctx.selection_trimmed());
    // // if !cursor_in_range {
    // //     return None;
    // // }

    // // collect failing post-conditions
    // let mut failed_posts = vec![];
    // for post in ctx.verus_post_failures_fn()? {
    //     let post_cond = ctx.find_node_at_this_range::<ast::Expr>(post.failing_post)?;
    //     let post_assert = format!("assert({post_cond});");
    //     failed_posts.push(post_assert);
    // }
    // if failed_posts.len() == 0 {
    //     return None;
    // }

    // // Check if the function returns something (to confirm if we need to introduce let-binding)
    // let mut ret_name: String = String::new();
    // let mut has_ret: bool = false;
    // if let Some(ret) = func.ret_type() {
    //     let ret_pat = ret.pat()?;
    //     ret_name = format!("{ret_pat}");
    //     has_ret = true;
    // };

    // let exit_range = func.body()?.syntax().text_range().end();
    // acc.add(AssistId("intro_failing_ensures", AssistKind::RefactorRewrite), "Copy FAILED ensures clauses to the end", ensures_keyword.text_range(), |edit| {
    //     if !has_ret {
    //         let failed_post_concat = failed_posts.connect("\n    ");
    //         edit.insert(exit_range, failed_post_concat);
    //     } else {
    //         // when it returns a value, we need to introduce let-binding for each tailing expression
    //         // when the return expression is if-else or match-statement, we need to introduce let-binding for each cases
    //         // TODO: do this for "return" (see `wrap_return_type_in_result`)
            
    //         // collect tail expressions
    //         let body = ast::Expr::BlockExpr(body);
    //         let mut exprs_to_bind = Vec::new();
    //         let tail_cb = &mut |e: &ast::Expr| exprs_to_bind.push(e.clone());
    //         for_each_tail_expr(&body, tail_cb);

    //         // for all tail expressions, let-bind and then insert failing postcondition as assertion
    //         for ret_expr_arg in exprs_to_bind {
    //             let indent = ret_expr_arg.indent_level();
    //             let sep = format!("\n{indent}");
    //             let failed_post_concat = failed_posts.connect(&sep);
    //             let binded = format!("let {ret_name} = {ret_expr_arg};\n{indent}{failed_post_concat}\n{indent}{ret_expr_arg}");
    //             edit.replace(ret_expr_arg.syntax().text_range(), binded);
    //         }
    //     };
    // })
}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn intro_failing_ensures_easy() {
        check_assist(
            intro_failing_ensures,
r#"
    enum Movement {
        Up(u32),
        Down(u32),
    }
    
    spec fn is_good_move(m: Movement) -> bool {
        match  m {
            Movement::Up(v) => v > 100,
            Movement::Down(v) => v > 100,
        }
    }
    
    proof fn good_move(m: Movement)
    {
        assert (is_good_move(m));
    }
"#,
r#"
    enum Movement {
        Up(u32),
        Down(u32),
    }
    
    spec fn is_good_move(m: Movement) -> bool {
        match  m {
            Movement::Up(v) => v > 100,
            Movement::Down(v) => v > 100,
        }
    }
    
    proof fn good_move(m: Movement)
    {
        match  m {
            Movement::Up(_) => assert (is_good_move(m)),
            Movement::Down(_) =>  assert (is_good_move(m)),
        }
    }
"#,
    );
    }
}
