use syntax::{ast, AstNode, TextRange};
use crate::{AssistContext, AssistId, AssistKind, Assists};

pub(crate) fn intro_failing_ensures(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let func = ctx.find_node_at_offset::<ast::Fn>()?;
    let ensures = func.ensures_clause()?; 
    let ensures_keyword = ensures.ensures_token()?;
    let ensures_range = ensures_keyword.text_range();
    let cursor_in_range = ensures_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    let mut failed_posts = vec![];
    for verr in &ctx.verus_errors {
        if let crate::VerusError::Post(post) = verr {
            let post_cond = ctx.find_node_at_this_range::<ast::Expr>(post.failing_post)?;
            let post_assert = format!("assert({post_cond});\n");
            failed_posts.push(post_assert);
        }
    }

    let text_ranges: Vec<TextRange>= ctx.textrange_from_comby_pattern(String::from("fn :[_]{:[body]}"))?;
    // let n = ctx.find_node_at_this_range::<syntax::ast::Expr>(text_range)?;
    let func_range: TextRange = func.syntax().text_range();
    let filtered_ranges: Vec<TextRange> = text_ranges.into_iter().filter(|x| func_range.contains_range(x.clone())).collect();
    if filtered_ranges.len() > 1 {
        return None;
    }
    let post_asserts = failed_posts.concat();
    acc.add(AssistId("intro_failing_ensures", AssistKind::RefactorRewrite), "Copy FAILED ensures clauses to the end", ensures_range, |edit| {
        edit.insert(filtered_ranges[0].end(), post_asserts);
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

}