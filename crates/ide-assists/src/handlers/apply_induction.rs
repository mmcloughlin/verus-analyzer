use crate::{AssistContext, AssistId, AssistKind, Assists};
use hir::{Adt, db::HirDatabase, Semantics, TypeInfo, ModuleDef, HasSource};
use syntax::{
    ast::{self, edit::IndentLevel, HasName, make},
    AstNode,
};
use ide_db::{RootDatabase, helpers::mod_path_to_ast};
use std::iter::{self, Peekable};
/*

For now we assume that the function has only a single argument.
We look for the type of the argument. If it is
1) `nat`
    do base-case zero, and do recursive call on `else`.
2) enum type, then generate a match statement
            for variants that contain `self`, do recursive lemma call
            for variants without `self`, do nothing
We also generate the decreases clause on the single argument.

*/


// referenced `add_missing_match_arms`
fn resolve_enum_type(sema: &Semantics<'_, RootDatabase>, type_of_enum: &ast::Type) -> Option<hir::Enum> {
    sema.resolve_type(type_of_enum)?.autoderef(sema.db).find_map(|ty| match ty.as_adt() {
        Some(Adt::Enum(e)) => Some(e),
        _ => None,
    })
}

// referenced `add_missing_match_arms`
fn build_pat(db: &RootDatabase, module: hir::Module, var: hir::Variant) -> Option<ast::Pat> {
    let path = mod_path_to_ast(&module.find_use_path(db, ModuleDef::from(var))?);

    // FIXME: use HIR for this; it doesn't currently expose struct vs. tuple vs. unit variants though
    let pat: ast::Pat = match var.source(db)?.value.kind() {
        ast::StructKind::Tuple(field_list) => {
            let pats =
                iter::repeat(make::wildcard_pat().into()).take(field_list.fields().count());
            make::tuple_struct_pat(path, pats).into()
        }
        ast::StructKind::Record(field_list) => {
            let pats = field_list
                .fields()
                .map(|f| make::ext::simple_ident_pat(f.name().unwrap()).into());
            make::record_pat(path, pats).into()
        }
        ast::StructKind::Unit => make::path_pat(path),
    };
    Some(pat)
}

// referenced `inline_call`
fn get_fn_params(
    db: &dyn HirDatabase,
    function: hir::Function,
    param_list: &ast::ParamList,
) -> Option<Vec<(ast::Pat, Option<ast::Type>, hir::Param)>> {
    let mut assoc_fn_params = function.assoc_fn_params(db).into_iter();

    let mut params = Vec::new();
    if let Some(self_param) = param_list.self_param() {
        // FIXME this should depend on the receiver as well as the self_param
        params.push((
            make::ident_pat(
                self_param.amp_token().is_some(),
                self_param.mut_token().is_some(),
                make::name("this"),
            )
            .into(),
            None,
            assoc_fn_params.next()?,
        ));
    }
    for param in param_list.params() {
        params.push((param.pat()?, param.ty(), assoc_fn_params.next()?));
    }

    Some(params)
}



pub(crate) fn apply_induction(acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()> {
    // setup basic variables
    // available on `fn` keyword
    let func: ast::Fn = ctx.find_node_at_offset::<ast::Fn>()?;
    let fn_token = func.fn_token()?;
    let fn_token_range = fn_token.text_range();
    let cursor_in_range = fn_token_range.contains_range(ctx.selection_trimmed());
    if !cursor_in_range {
        return None;
    }
    // if it is not proof function, return None
    func.fn_mode()?.proof_token()?;
    
    // setup indentation helpers
    let one_indent = IndentLevel::from(1);
    let two_indent = one_indent + 1;
    let three_indent = two_indent + 1;

    // get the single variable and its type
    let function = ctx.sema.to_def(&func)?;
    let param_list = func.param_list()?;
    let params = get_fn_params(ctx.sema.db, function, &param_list)?;
    if params.len() != 1 {
        return None;
    }
    let arg_pat = &params[0].0;
    let arg_type = params[0].1.as_ref()?;


    let body: ast::BlockExpr = func.body()?;
    let module = ctx.sema.scope(body.syntax())?.module();
    let func_name = func.name()?;

    // TODO: add decreases clause if there isn't
    // let decreases: ast::DecreasesClause = func.decreases_clause()?;
    // let decreasing_expr = decreases.expr()?;
    
    dbg!(arg_type.to_string());
    let mut found_recursive = false;
    let induction_proof_body = 
    if arg_type.to_string() == "nat".to_string() { // REVIEW: does this work?
        dbg!("apply induction nat");
        // If `nat`, do base-case zero, and do recursive call on `else`.
        // just assume integer and base case zero
        // Also, do type casting("as nat") on the recursive call.
        let recursive_call = format!("{func_name}(({arg_pat} - 1) as nat);");
        let induction_proof_body = format!(
            "{{\n{one_indent}if {arg_pat} == 0 {{}}\n{one_indent}else {{\n{two_indent}{recursive_call}\n{one_indent}}}\n}}"
        );
        induction_proof_body
    } else {
        // If enum type, then generate a match statement
        //     for variants that contain `self`, do recursive lemma call
        //     for variants without `self`, do nothing
        dbg!("apply induction enum");
        let enum_def = resolve_enum_type(&ctx.sema, &arg_type)?;
        let enum_variants: Vec<hir::Variant> = enum_def.variants(ctx.sema.db).into_iter().collect::<Vec<_>>();
        let enum_name = enum_def.name(ctx.sema.db);
        let enum_type = enum_def.ty(ctx.sema.db);
        let mut match_cases = vec![];

        // generate one match case for each variant
        // for each match case, do recursive call for any field with the same enum type
        for variant in enum_variants {
            let pat = build_pat(ctx.sema.db, module, variant)?;
            // let arm = make::match_arm(iter::once(pat), None, make::ext::expr_todo());
            let mut recursive_calls = vec![];
            let fields = variant.fields(ctx.sema.db);
            dbg!(fields.len());
            // let's invoke recursive call for each field with the original type
            for field in fields {
                let field_name = field.name(ctx.sema.db);
                let field_ty = field.ty(ctx.sema.db);
                // dbg!(enum_type == field_ty.remove_ref()?);
                let mut is_recursive = false;

                // TODO: check for actual type equality rather than `walk`
                // REVIEW: is it reasonable to add `*` dereference always?
                field_ty.walk(ctx.sema.db, |t| {
                    if t == enum_type {
                        is_recursive = true;
                        found_recursive = true;
                        dbg!("found recursive field");
                    }
                });
                if is_recursive {
                    let rec_call = format!("{func_name}(*{field_name});");
                    recursive_calls.push(rec_call);
                }
            }

            // now that we have all the recursive call,
            // generate a match case block
            dbg!(&recursive_calls);
            let seperator = format!("\n{three_indent}");
            let recursive_calls_string = recursive_calls.join(&seperator);

            let match_case_block = format!("{pat} => {{\n{three_indent}{recursive_calls_string}\n{two_indent}}},");
            match_cases.push(match_case_block);
        }
        if !found_recursive {
            dbg!("induction not applicable");
            return None;
        }
        dbg!(&match_cases);
        let seperator = format!("\n{two_indent}");
        let match_case_string = match_cases.join(&seperator);
        format!("{{\n{one_indent}match {arg_pat} {{\n{two_indent}{match_case_string}\n{one_indent}}}\n}}")
    };
    
    dbg!("register apply induction");
    acc.add(
        AssistId("apply_induction", AssistKind::RefactorRewrite),
        "Apply induction",
        body.syntax().text_range(),
        |edit| {
            edit.replace(body.syntax().text_range(), induction_proof_body)
        },
    )
    

}

#[cfg(test)]
mod tests {
    use crate::tests::check_assist;

    use super::*;

    #[test]
    fn apply_induction_on_nat1() {
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
proof $0fn sum_equal(n: nat) 
    ensures sum(n) == triangle(n),
    decreases n,
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
        sum_equal((n - 1) as nat);
    }
}            
"#,
        );
    }



    #[test]
// https://github.com/verus-lang/verus/blob/0088380265ed6e10c5d8034e89ce807a728f98e3/source/rust_verify/example/summer_school/chapter-1-22.rs
    fn apply_induction_on_enum1() {
        check_assist(
            apply_induction,
            r#"
use core::ops::Deref;

struct Box<T>(T);

impl<T> Deref for Box<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target;
}

struct Foo<T>(T);

impl<T> Foo<T> {
    fn get_inner<'a>(self: &'a Box<Self>) -> &'a T {}

    fn get_self<'a>(self: &'a Box<Self>) -> &'a Self {}

    fn into_inner(self: Box<Self>) -> Self {}
}
            
#[is_variant] #[derive(PartialEq, Eq)] 
enum Tree {
    Nil,
    Node { value: i64, left: Box<Tree>, right: Box<Tree> },
}

proof fn$0 sorted_tree_means_sorted_sequence(tree: Tree)
    requires
        tree.is_sorted(),
    ensures
        sequence_is_sorted(tree@),
{
}
"#,


            r#"
use core::ops::Deref;

struct Box<T>(T);

impl<T> Deref for Box<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target;
}

struct Foo<T>(T);

impl<T> Foo<T> {
    fn get_inner<'a>(self: &'a Box<Self>) -> &'a T {}

    fn get_self<'a>(self: &'a Box<Self>) -> &'a Self {}

    fn into_inner(self: Box<Self>) -> Self {}
}
            
#[is_variant] #[derive(PartialEq, Eq)] 
enum Tree {
    Nil,
    Node { value: i64, left: Box<Tree>, right: Box<Tree> },
}

proof fn sorted_tree_means_sorted_sequence(tree: Tree)
    requires
        tree.is_sorted(),
    ensures
        sequence_is_sorted(tree@),
    decreases tree // guessed by Dafny
{
    if let Tree::Node { left, right, value: _ } = tree {
        sorted_tree_means_sorted_sequence(*left); // guessed by Dafny
        sorted_tree_means_sorted_sequence(*right); // guessed by Dafny
    }
}    
"#,
        );
    }
}


// maybe do something without box first?
// box seems to work in runtime --- in test env, box seems not imported automatically
// num Nat { Succ(Self), Demo(Nat), Zero }


//
//
// enum List<A> {
//     Nil,
//     Cons(A, Box<List<A>>),
// }

// fn get_len<A>(list: &List<A>)
// {
//     let mut n: u64 = 0;
//     let mut done = false;
//     let mut iter = list;
//     while !done
//     {
//         match iter {
//             List::Nil => {
//                 done = true;
//             }
//             List::Cons(_, tl) => {
//                 iter = tl;
//                 reveal_with_fuel(len::<A>, 2);
//                 n = n + 1;
//             }
//         }
//     }
//     n
// }


        // let enum_syntax = enum_def.source(ctx.sema.db)?.value;
        // println!("{}", &enum_syntax);
        // for var in enum_syntax.variant_list()?.variants() {
        //     dbg!("{}", &var);
        //     if let Some(field_list) = var.field_list()  {
        //         match field_list{
        //             ast::FieldList::RecordFieldList(records) => {
        //                 for field in records.fields() {
        //                     dbg!(&field.name());
        //                     dbg!(&field.ty());
        //                 }
        //             }
        //             ast::FieldList::TupleFieldList(tuples) => {
        //                 for field in tuples.fields() {
        //                     dbg!(&field);
        //                 }
        //             }
        //         }
        //     }
        // }

        // walk_ty(enum_syntax, &mut |t| {
        //     dbg!(&t);
        //     if t == enum_type {
        //         // dbg!(&t);
        //         println!("found enum type");
        //     }
        // });
        // enum_type.walk(ctx.sema.db, |t| {
        //     dbg!(&t);
        //     if t == enum_type {
        //         // dbg!(&t);
        //         println!("found enum type");
        //     }
        // });


        // let recursive_call = format!("{func_name}(({arg_pat} - 1) as nat);");
        // let one_ident = IndentLevel::from(1);
        // let two_ident = one_ident + 1;
        // let induction_proof_body = format!(
        //     "{{\n{one_ident}if {arg_pat} == 0 {{}}\n{one_ident}else {{\n{two_ident}{recursive_call}\n{one_ident}}}\n}}"
        // );
        // acc.add(
        //     AssistId("apply_induction", AssistKind::RefactorRewrite),
        //     "Apply induction on nat",
        //     body.syntax().text_range(),
        //     |edit| edit.replace(body.syntax().text_range(), induction_proof_body),
        // )