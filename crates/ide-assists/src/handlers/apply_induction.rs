use crate::{AssistContext, AssistId, AssistKind, Assists};

use syntax::{
    ast::{self, HasName},
    AstNode,
};

pub(crate) fn apply_induction(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // setup basic variables
    let func: ast::Fn = ctx.find_node_at_offset::<ast::Fn>()?;
    let body: ast::BlockExpr = func.body()?;
    let decreases: ast::DecreasesClause = func.decreases_clause()?;
    let decreasing_expr = decreases.expr()?;
    let func_name = func.name()?;

    // trigger on "decreases"
    let decreases_keyword = decreases.decreases_token()?;
    let cursor_in_range = decreases_keyword.text_range().contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    // TODO: improve
    // just assume integer and base case zero
    let recursive_call = format!("{func_name}({decreasing_expr} - 1);");
    let induction_proof_body = format!(
        "{{\n    if {decreasing_expr} == 0 {{}}\n    else {{\n        {recursive_call}\n    }}\n}}"
    );
    acc.add(
        AssistId("apply_induction", AssistKind::RefactorRewrite),
        "Apply induction",
        body.syntax().text_range(),
        |edit| edit.replace(body.syntax().text_range(), induction_proof_body),
    )
}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn apply_induction_easy() {
        check_assist(
            apply_induction,
            r#"
spec fn sum(n: nat) -> nat
{
    n * (n + 1) / 2
}

spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

#[verifier(nonlinear)]
proof fn sum_equal(n: nat) 
    ensures sum(n) == triangle(n),
    decre$0ases n,
{
}
"#,
            r#"
spec fn sum(n: nat) -> nat
{
    n * (n + 1) / 2
}

spec fn triangle(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        0
    } else {
        n + triangle((n - 1) as nat)
    }
}

#[verifier(nonlinear)]
proof fn sum_equal(n: nat) 
    ensures sum(n) == triangle(n),
    decreases n,
{
    if n == 0 {} 
    else {
        sum_equal((n-1) as nat);
    }
}            
"#,
        );
    }
}
