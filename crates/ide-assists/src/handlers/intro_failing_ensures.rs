use crate::{AssistContext, AssistId, AssistKind, Assists};
use ide_db::syntax_helpers::node_ext::{for_each_tail_expr, walk_expr};

use syntax::{
    ast::{self, Expr},
    match_ast, AstNode, TextRange,
};

// copied from `wrap_return_type_in_result`
fn tail_cb_impl(acc: &mut Vec<ast::Expr>, e: &ast::Expr) {
    match e {
        Expr::BreakExpr(break_expr) => {
            if let Some(break_expr_arg) = break_expr.expr() {
                for_each_tail_expr(&break_expr_arg, &mut |e| tail_cb_impl(acc, e))
            }
        }
        Expr::ReturnExpr(ret_expr) => {
            if let Some(ret_expr_arg) = &ret_expr.expr() {
                for_each_tail_expr(ret_expr_arg, &mut |e| tail_cb_impl(acc, e));
            }
        }
        e => acc.push(e.clone()),
    }
}

pub(crate) fn intro_failing_ensures(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // trigger on "ensures"
    let func = ctx.find_node_at_offset::<ast::Fn>()?;
    let func_range: TextRange = func.syntax().text_range();
    let body = func.body()?;
    let ensures = func.ensures_clause()?;
    let ensures_keyword = ensures.ensures_token()?;
    let ensures_range = ensures_keyword.text_range();
    let cursor_in_range = ensures_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    // collect failing post-conditions
    let mut failed_posts = vec![];
    for verr in &ctx.verus_errors {
        if let crate::VerusError::Post(post) = verr {
            let post_cond = ctx.find_node_at_this_range::<ast::Expr>(post.failing_post)?;
            let post_assert = format!("assert({post_cond});\n");
            failed_posts.push(post_assert);
        }
    }
    if failed_posts.len() == 0 {
        return None;
    }

    // calcaulte diff
    // first, check if the function returns something (to confirm if I need to introduce let-binding)
    // fn :[_] -> (:[ret]: :[_]) :[_] {:[_]}
    // fn :[_] -> (:[ret]::[_]) :[_]
    // TODO: let's just use CST API for getting return value. making comby search work as expected seems harder than looking up the CST API
    // TODO: might worth replacing it with SSR thing
    let ret_ranges: Vec<TextRange> =
        ctx.textranges_from_comby_pattern(String::from("fn :[_] -> (:[ret]::[_]) :[_]"))?;
    dbg!(&ret_ranges);
    dbg!(&func_range);
    let ret_range: Vec<TextRange> =
        ret_ranges.into_iter().filter(|x| func_range.contains_range(x.clone())).collect();
    dbg!(ret_range.len());
    if ret_range.len() > 1 {
        return None; // unexpected error
    }
    let mut ret_name: String = String::new();
    if ret_range.len() == 1 {
        let ret_name_expr = ctx.find_node_at_this_range::<ast::Pat>(ret_range[0])?;
        ret_name = format!("{}", ret_name_expr);
        dbg!(&ret_name);
    }
    let failed_post_concat = failed_posts.concat();

    // find the offset location of function exit
    let exit_ranges: Vec<TextRange> =
        ctx.textranges_from_comby_pattern(String::from("fn :[_]{:[body]}"))?;
    let exit_range: Vec<TextRange> =
        exit_ranges.into_iter().filter(|x| func_range.contains_range(x.clone())).collect();
    if exit_range.len() > 1 {
        return None; // unexpected error
    }

    // TODO: formatting -- rustfmt?
    acc.add(AssistId("intro_failing_ensures", AssistKind::RefactorRewrite), "Copy FAILED ensures clauses to the end", ensures_range, |edit| {
        if ret_range.len() == 0 {
            // no return value
            dbg!("no ret");
            edit.insert(exit_range[0].end(), failed_post_concat);
        } else {
            // when it returns a value, we need to introduce let-binding for each tailing expression
            // when the return expression is if-else or match-statement, we need to introduce let-binding for each cases
            // also, we need to insert assertions on "return"-statements, which could be anywhere
            // "return ret_expr;" -> {let r = ret_expr; assert(P); return r;}
            // should be fairly similar to `wrap_return_type_in_result`
            //
            dbg!("yes ret");
            let body = ast::Expr::BlockExpr(body);

            let mut exprs_to_bind = Vec::new();
            let tail_cb = &mut |e: &_| tail_cb_impl(&mut exprs_to_bind, e);
            walk_expr(&body, &mut |expr| {
                if let Expr::ReturnExpr(ret_expr) = expr {
                    if let Some(ret_expr_arg) = &ret_expr.expr() {
                        for_each_tail_expr(ret_expr_arg, tail_cb);
                    }
                }
            });
            for_each_tail_expr(&body, tail_cb);

            for ret_expr_arg in exprs_to_bind {
                let binded = format!("let {ret_name} = {ret_expr_arg};\n    {failed_post_concat}\n {ret_expr_arg}");
                edit.replace(ret_expr_arg.syntax().text_range(), binded);
            }
        };
    })
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
proof fn my_proof_fun(x: int, y: int)
    requires
        x < 100,
        y < 100,
    ens$0ures
        x + y < 200,
        x + y < 400,
{
    assert(x + y < 600);
}
"#,
            r#"
proof fn my_proof_fun(x: int, y: int)
    requires
        x < 100,
        y < 100,
    ensures
        x + y < 200,
        x + y < 400,
{
    assert(x + y < 600);

    assert(x + y < 400); 
}
"#,
        );
    }

    #[test]
    fn intro_ensure_ret_arg() {
        check_assist(
            intro_failing_ensures,
            r#"
proof fn my_proof_fun(x: int, y: int) -> (sum: int)
    requires
        x < 100,
        y < 100,
    ens$0ures
        sum < 200,
        sum < 300,
        sum < 400,
{
    x + y
}
"#,
            r#"
proof fn my_proof_fun(x: int, y: int) -> (sum: int)
    requires
        x < 100,
        y < 100,
    ensures
        sum < 200,
        sum < 300,
        sum < 400,
{
    let sum = x + y; 
    assert(sum < 200); 
    assert(sum < 300); 
    assert(sum < 400); 
    sum
}
"#,
        );
    }

    #[test]
    fn intro_ensure_fibo() {
        check_assist(
            intro_failing_ensures,
            r#"
proof fn lemma_fibo_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    e$0nsures
        fibo(i) <= fibo(j),
    decreases j - i
{
    if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        reveal_with_fuel(fibo, 2);
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
        lemma_fibo_is_monotonic(i, (j - 2) as nat);
    }
}
"#,
            r#"
proof fn lemma_fibo_is_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        fibo(i) <= fibo(j),
    decreases j - i
{
    let _ = if i < 2 && j < 2 {
    } else if i == j {
    } else if i == j - 1 {
        reveal_with_fuel(fibo, 2);
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
    } else {
        lemma_fibo_is_monotonic(i, (j - 1) as nat);
        lemma_fibo_is_monotonic(i, (j - 2) as nat);
    }; 
    assert(fibo(i) <= fibo(j)); 
    ()
}
"#,
        );
    }
}
