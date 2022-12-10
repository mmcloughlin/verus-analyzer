// use ide_db::syntax_helpers::node_ext::is_pattern_cond;
use crate::{
    assist_context::{AssistContext, Assists},
    AssistId, AssistKind,
};
use std::collections::hash_map::DefaultHasher;
use std::env;
use std::{
    hash::{Hash, Hasher},
    process::Command,
};
use syntax::{
    ast::{self, AstNode, HasName},
    SyntaxKind, SyntaxToken, T,
};

pub(crate) fn assert_comment(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    let assert_keyword = ctx.find_token_syntax_at_offset(T![assert])?;
    let assert_range = assert_keyword.text_range();
    let cursor_in_range = assert_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }
    let func = ctx.find_node_at_offset::<ast::Fn>()?;
    let assert_expr = ast::AssertExpr::cast(assert_keyword.parent()?)?;
    let assert_stmt = ast::Stmt::ExprStmt(ast::ExprStmt::cast(assert_expr.syntax().parent()?)?);
    let assert_removed_fn = code_transformer_remove_expr_stmt(func, assert_stmt.clone())?;

    if ctx.run_verus_on_fn(assert_removed_fn.fn_token()?)? {
        // TODO: comment out using // rather than /* */
        acc.add(
            AssistId("assert_comment", AssistKind::RefactorRewrite),
            "Check if this assertion is essential",
            assert_range,
            |builder| {
                builder.insert(assert_stmt.syntax().text_range().start(), &format!("/* "));
                builder.insert(assert_stmt.syntax().text_range().end(), &format!(" */"));
            },
        )
    } else {
        acc.add(
            AssistId("assert_comment", AssistKind::RefactorRewrite),
            "Check if this assertion is essential",
            assert_range,
            |builder| {
                builder.insert(assert_stmt.syntax().text_range().end(), &format!(" // OBSERVE"));
            },
        )
    }
}

// a code action that removes a chosen assertion
pub(crate) fn code_transformer_remove_expr_stmt(
    func: ast::Fn,
    assert_stmt: ast::Stmt,
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
    Some(func)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tests::check_assist;

    #[test]
    fn assert_comment_success() {
        check_assist(
            assert_comment,
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
        ass$0ert(offset < 16);
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
    }
} // verus!
"#,
        );
    }

    #[test]
    fn assert_comment_fail() {
        check_assist(
            assert_comment,
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
        ass$0ert(offset & offset == offset) by(bit_vector);
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
        assert(offset & offset == offset) by(bit_vector); // OBSERVE
    }
} // verus!
"#,
        );
    }
}

// {"uri":"/Users/chanhee/Works/secure-foundations/verus_action_usage/src/main.rs","matches":[{"range":{"start":{"offset":1179,"line":49,"column":5},"end":{"offset":1213,"line":49,"column":39}},"environment":[{"variable":"exp","value":"false <== false <== false","range":{"start":{"offset":1186,"line":49,"column":12},"end":{"offset":1211,"line":49,"column":37}}}],"matched":"assert(false <== false <== false);"},{"range":{"start":{"offset":1218,"line":50,"column":5},"end":{"offset":1234,"line":50,"column":21}},"environment":[{"variable":"exp","value":"a === a","range":{"start":{"offset":1225,"line":50,"column":12},"end":{"offset":1232,"line":50,"column":19}}}],"matched":"assert(a === a);"},{"range":{"start":{"offset":1239,"line":51,"column":5},"end":{"offset":1272,"line":51,"column":38}},"environment":[{"variable":"exp","value":"false <==> true && false","range":{"start":{"offset":1246,"line":51,"column":12},"end":{"offset":1270,"line":51,"column":36}}}],"matched":"assert(false <==> true && false);"},{"range":{"start":{"offset":1407,"line":59,"column":9},"end":{"offset":1426,"line":59,"column":28}},"environment":[{"variable":"exp","value":"0 <= x * z","range":{"start":{"offset":1414,"line":59,"column":16},"end":{"offset":1424,"line":59,"column":26}}}],"matched":"assert(0 <= x * z);"},{"range":{"start":{"offset":1435,"line":60,"column":9},"end":{"offset":1468,"line":60,"column":42}},"environment":[{"variable":"exp","value":"x * z <= 0xffff * 0xffff","range":{"start":{"offset":1442,"line":60,"column":16},"end":{"offset":1466,"line":60,"column":40}}}],"matched":"assert(x * z <= 0xffff * 0xffff);"},{"range":{"start":{"offset":1760,"line":78,"column":5},"end":{"offset":1778,"line":78,"column":23}},"environment":[{"variable":"exp","value":"s2 === s3","range":{"start":{"offset":1767,"line":78,"column":12},"end":{"offset":1776,"line":78,"column":21}}}],"matched":"assert(s2 === s3);"},{"range":{"start":{"offset":2433,"line":104,"column":5},"end":{"offset":2478,"line":104,"column":50}},"environment":[{"variable":"exp","value":"u < 100 ==> (add(u, u) as int) < 250","range":{"start":{"offset":2440,"line":104,"column":12},"end":{"offset":2476,"line":104,"column":48}}}],"matched":"assert(u < 100 ==> (add(u, u) as int) < 250);"},{"range":{"start":{"offset":3486,"line":159,"column":5},"end":{"offset":3508,"line":159,"column":27}},"environment":[{"variable":"exp","value":"divides(x, z)","range":{"start":{"offset":3493,"line":159,"column":12},"end":{"offset":3506,"line":159,"column":25}}}],"matched":"assert(divides(x, z));"},{"range":{"start":{"offset":3513,"line":160,"column":5},"end":{"offset":3535,"line":160,"column":27}},"environment":[{"variable":"exp","value":"divides(y, z)","range":{"start":{"offset":3520,"line":160,"column":12},"end":{"offset":3533,"line":160,"column":25}}}],"matched":"assert(divides(y, z));"}]}~ /usr/local/bin/comby 'assert' . /Users/chanhee/Works/secure-foundations/verus_action_usage/src/main.rs -match-only -json-lines{"uri":"/Users/chanhee/Works/secure-foundations/verus_action_usage/src/main.rs","matches":[{"range":{"start":{"offset":1179,"line":49,"column":5},"end":{"offset":1185,"line":49,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1218,"line":50,"column":5},"end":{"offset":1224,"line":50,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1239,"line":51,"column":5},"end":{"offset":1245,"line":51,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1279,"line":54,"column":5},"end":{"offset":1285,"line":54,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1407,"line":59,"column":9},"end":{"offset":1413,"line":59,"column":15}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1435,"line":60,"column":9},"end":{"offset":1441,"line":60,"column":15}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":1760,"line":78,"column":5},"end":{"offset":1766,"line":78,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":2433,"line":104,"column":5},"end":{"offset":2439,"line":104,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":3486,"line":159,"column":5},"end":{"offset":3492,"line":159,"column":11}},"environment":[],"matched":"assert"},{"range":{"start":{"offset":3513,"line":160,"column":5},"end":{"offset":3519,"line":160,"column":11}},"environment":[],"matched":"assert"}]}
