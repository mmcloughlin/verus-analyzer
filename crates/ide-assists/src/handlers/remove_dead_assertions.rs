// use ide_db::syntax_helpers::node_ext::is_pattern_cond;
use crate::{
    assist_context::{AssistContext, Assists},
    AssistId, AssistKind,
};
use syntax::{
    ast::{self, AstNode},
    SyntaxKind, T,
};

/*
Check all assertions in a function
From top to the bottom, check all assertions.
If it is redundant, the assertion is commented out
 */

pub(crate) fn remove_dead_assertions(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let func = ctx.find_node_at_offset::<ast::Fn>()?;
    let fn_token = func.fn_token()?;
    let fn_token_range = fn_token.text_range();
    let cursor_in_range = fn_token_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }

    let mut redundant_assertions = vec![];
    let body = func.body()?;
    for stmt in body.stmt_list()?.statements() {
        if let ast::Stmt::ExprStmt(ref stm) = stmt {
            if let ast::Expr::AssertExpr(..) = stm.expr()? {
                let assert_removed_fn = code_transformer_remove_expr_stmt(
                    func.clone(),
                    stmt.clone(),
                    &redundant_assertions,
                )?;
                if ctx.run_verus_on_fn(assert_removed_fn.fn_token()?)? {
                    redundant_assertions.push(stmt.clone());
                }
            }
        }
    }

    let fnrange = func.syntax().text_range();
    acc.add(
        AssistId("remove_dead_assertions", AssistKind::RefactorRewrite),
        "Comment out dead assertions",
        fnrange,
        |builder| {
            for stmt in redundant_assertions {
                builder.insert(stmt.syntax().text_range().start(), &format!("/* "));
                builder.insert(stmt.syntax().text_range().end(), &format!(" */"));
            }
        },
    )
}

// a code action that removes
// 1) `assert_stmt`, 2) any stmts inside `redundant_stmts`.
// `func` is a placeholder just to make `func` initialized..
pub(crate) fn code_transformer_remove_expr_stmt(
    func: ast::Fn,
    assert_stmt: ast::Stmt,
    redundant_stmts: &Vec<ast::Stmt>,
) -> Option<ast::Fn> {
    let mut func = func;
    let assert_stmt = assert_stmt.clone_for_update();
    for ancestor in assert_stmt.syntax().ancestors() {
        match ancestor.kind() {
            SyntaxKind::FN => {
                func = ast::Fn::cast(ancestor)?;
                break;
            }
            _ => (),
        }
    }

    assert_stmt.remove();

    // TODO:
    // statements get removed based on string.
    // this should consider something like offset.
    // in case we have multiple same assertions
    for mutable_stm in func.body()?.statements() {
        if redundant_stmts
            .iter()
            .map(|stm| stm.to_string())
            .any(|stm| stm == mutable_stm.to_string())
        {
            mutable_stm.remove();
        }
    }

    Some(func)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::check_assist;

    #[test]
    fn assert_comment_success() {
        check_assist(
            remove_dead_assertions,
            r#"
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{modes::*, seq::*, vec::*};

#[verifier(external)]
fn main() {
}

verus! {
    proof fn$0 proof_index(a: u16, offset: u16)
    requires    
        offset < 16
    ensures
        offset < 16
    {
        assert(offset < 16);
        assert(1 == 1);
        assert(15 < 16);
    }
} // verus!
"#,
            r#"
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{modes::*, seq::*, vec::*};

#[verifier(external)]
fn main() {
}

verus! {
    proof fn proof_index(a: u16, offset: u16)
    requires    
        offset < 16
    ensures
        offset < 16
    {
        /* assert(offset < 16); */
        /* assert(1 == 1); */
        /* assert(15 < 16); */
    }
} // verus!
"#,
        );
    }

    #[test]
    fn assert_comment_fail() {
        check_assist(
            remove_dead_assertions,
            r#"
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{modes::*, seq::*, vec::*};

#[verifier(external)]
fn main() {
}

verus! {
    proof f$0n proof_index(a: u16, offset: u16)
    requires    
        offset < 1000
    ensures
        offset & offset < 1000
    {
        assert(offset < 2000);
        assert(offset & offset == offset) by (bit_vector);
        assert(offset & offset == offset) by(bit_vector);
    }
} // verus!
"#,
            r#"
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::*;

mod pervasive;
#[allow(unused_imports)]
use crate::pervasive::{modes::*, seq::*, vec::*};

#[verifier(external)]
fn main() {
}

verus! {
    proof fn proof_index(a: u16, offset: u16)
    requires    
        offset < 1000
    ensures
        offset & offset < 1000
    {
        /* assert(offset < 2000); */
        /* assert(offset & offset == offset) by (bit_vector); */
        assert(offset & offset == offset) by(bit_vector);
    }
} // verus!
"#,
        );
    }

    // TODO: testcase for assertions inside a assert-by-proof-block
}
