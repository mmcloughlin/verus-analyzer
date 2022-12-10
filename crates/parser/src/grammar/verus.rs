use super::{items::ITEM_RECOVERY_SET, *};

// as of now...
// Publish =
//   ('closed' | 'open' )

// FnMode =
//   ('spec' | 'proof' | 'exec' | ModeSpecChecked )

pub(crate) fn publish(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    if p.at(T![open]) {
        p.bump(T![open]);
        m.complete(p, PUBLISH)
    } else if p.at(T![closed]) {
        p.bump(T![closed]);
        m.complete(p, PUBLISH)
    } else {
        p.error("TODO: expected open or closed or publish.");
        m.complete(p, ERROR)
    }
}

pub(crate) fn fn_mode(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    if p.at(T![proof]) {
        p.bump(T![proof]);
        m.complete(p, FN_MODE)
    } else if p.at(T![exec]) {
        p.bump(T![exec]);
        m.complete(p, FN_MODE)
    } else if p.at(T![spec]) {
        p.bump(T![spec]);
        if p.at(T!['(']) {
            p.expect(T!['(']);
            p.expect(T![checked]);
            p.expect(T![')']);
        }
        m.complete(p, FN_MODE)
    } else {
        p.error("Expected spec/spec(checked)/proof/exec.");
        m.complete(p, ERROR)
    }
}

pub(crate) fn assume(p: &mut Parser<'_>, m: Marker) {
    p.expect(T![assume]);
    p.expect(T!['(']);
    expressions::expr(p);
    p.expect(T![')']);
    m.complete(p, ASSUME_EXPR);
}

// AssertExpr =
//   'assert' '(' Expr ')' 'by'? ( '(' Name ')' )?  RequiresClause? BlockExpr?
pub(crate) fn assert(p: &mut Parser<'_>, m: Marker) -> CompletedMarker {
    p.expect(T![assert]);

    if p.at(T!['(']) {
        // parse expression here
        p.expect(T!['(']);
        expressions::expr(p);
        p.expect(T![')']);
    } else {
        // TODO: make this a separate kind AssertForall
        // assert forall|x: int, y: int| f1(x) + f1(y) == x + y + 2 by {
        //     reveal(f1);
        // }
        p.error("TODO: make this a separate kind AssertForall");
        expressions::expr(p);
        if p.at(T![implies]) {
            p.bump(T![implies]);
            expressions::expr(p);
        }
        // p.error("expected function arguments");
    }

    // parse optional `by`
    // bit_vector, nonlinear_artih ...
    if p.at(T![by]) {
        p.expect(T![by]);
        if p.at(T!['(']) {
            p.expect(T!['(']);
            // p.bump_any();
            name_r(p, ITEM_RECOVERY_SET);
            p.expect(T![')']);
        }
    }

    // parse optional 'requires`
    if p.at(T![requires]) {
        requires(p);
    }

    if p.at(T![;]) || p.at(T![,]) {
        // test fn_decl
        // trait T { fn foo(); }
        // dbg!("getting ;, but ignoring");
        // p.bump(T![;]);
    } else {
        // dbg!("proof block");
        // parse optional 'proof block'
        expressions::block_expr(p);
    }

    m.complete(p, ASSERT_EXPR)
}

pub(crate) fn requires(p: &mut Parser<'_>) -> CompletedMarker {
    // dbg!("requires");
    let m = p.start();
    p.expect(T![requires]);
    expressions::expr_no_struct(p);

    while !p.at(EOF)
        && !p.at(T![recommends])
        && !p.at(T![ensures])
        && !p.at(T![decreases])
        && !p.at(T!['{'])
        && !p.at(T![;])
    {
        if p.at(T![recommends]) || p.at(T![ensures]) || p.at(T![decreases]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at(1, T![recommends])
                || p.nth_at(1, T![ensures])
                || p.nth_at(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_cond(p);
            }
        } else {
            dbg!("requires parse error");
            p.error("TODO: please add COMMA after each requires clause.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, REQUIRES_CLAUSE)
}

pub(crate) fn recommends(p: &mut Parser<'_>) -> CompletedMarker {
    // dbg!("recommends");
    let m = p.start();
    p.expect(T![recommends]);
    expressions::expr_no_struct(p);
    while !p.at(EOF) && !p.at(T![ensures]) && !p.at(T![decreases]) && !p.at(T!['{']) && !p.at(T![;])
    {
        if p.at(T![recommends]) || p.at(T![ensures]) || p.at(T![decreases]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at(1, T![recommends])
                || p.nth_at(1, T![ensures])
                || p.nth_at(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_cond(p);
            }
        } else {
            dbg!("recommends parse error");
            p.error("TODO: please add COMMA after each recommends clause.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, RECOMMENDS_CLAUSE)
}

pub(crate) fn ensures(p: &mut Parser<'_>) -> CompletedMarker {
    // dbg!("ensures");
    let m = p.start();
    p.expect(T![ensures]);
    expressions::expr_no_struct(p);

    while !p.at(EOF) && !p.at(T![decreases]) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at(T![recommends]) || p.at(T![ensures]) || p.at(T![decreases]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at(1, T![recommends])
                || p.nth_at(1, T![ensures])
                || p.nth_at(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_cond(p);
            }
        } else {
            dbg!("ensures parse error");
            p.error("TODO: please add COMMA after each ensures clause.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, ENSURES_CLAUSE)
}

pub(crate) fn invariants(p: &mut Parser<'_>) -> CompletedMarker {
    // dbg!("invariants");
    let m = p.start();
    p.expect(T![invariant]);
    expressions::expr_no_struct(p);

    while !p.at(EOF) && !p.at(T![decreases]) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at(T![recommends]) || p.at(T![ensures]) || p.at(T![decreases]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at(1, T![recommends])
                || p.nth_at(1, T![ensures])
                || p.nth_at(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_cond(p);
            }
        } else {
            dbg!("invariants parse error");
            p.error("TODO: please add COMMA after each invariants clause.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, INVARIANT_CLAUSE)
}

pub(crate) fn decreases(p: &mut Parser<'_>) -> CompletedMarker {
    // dbg!("decreases");
    let m = p.start();
    p.expect(T![decreases]);
    expressions::expr_no_struct(p);
    while !p.at(EOF) && !p.at(T!['{']) && !p.at(T![;]) {
        if p.at(T![recommends]) || p.at(T![ensures]) || p.at(T![decreases]) || p.at(T!['{']) {
            break;
        }
        if p.at(T![,]) {
            if p.nth_at(1, T![recommends])
                || p.nth_at(1, T![ensures])
                || p.nth_at(1, T![decreases])
                || p.nth_at(1, T!['{'])
            {
                break;
            } else {
                comma_cond(p);
            }
        } else {
            dbg!("decreases parsing error");
            p.error("TODO: please add COMMA after each decreases clause.");
            return m.complete(p, ERROR);
        }
    }
    if p.at(T![,]) {
        p.expect(T![,]);
    }
    m.complete(p, DECREASES_CLAUSE)
}

fn comma_cond(p: &mut Parser<'_>) -> CompletedMarker {
    let m = p.start();
    p.expect(T![,]);
    expressions::expr_no_struct(p);
    m.complete(p, COMMA_AND_COND)
}

// fn comma_name(p: &mut Parser<'_>) -> CompletedMarker {
//     let m = p.start();
//     p.expect(T![,]);
//     name(p);
//     m.complete(p, COMMA_AND_NAME)
// }
// fn pat_comma(p: &mut Parser<'_>) -> CompletedMarker {
//     let m = p.start();
//     patterns::pattern(p);
//     if p.at(T![,]){
//         p.expect(T![,]);
//     }
//     m.complete(p, PAT_AND_COMMA)
// }

// fn cond_comma(p: &mut Parser<'_>) -> CompletedMarker {
//     dbg!("cond comma");
//     dbg!(p.current());
//     dbg!(p.nth(1));
//     let m = p.start();
//     expressions::expr(p);
//     if p.at(T![,]){
//         p.expect(T![,]);
//     }
//     m.complete(p, COND_AND_COMMA)
// }

// fn comma_expr(p: &mut Parser<'_>) -> CompletedMarker {
//     dbg!("comma_expr");
//     let m = p.start();
//     p.expect(T![,]);
//     expressions::expr_no_struct(p);
//     m.complete(p, COMMA_AND_EXPR)
// }
