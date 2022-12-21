//! See [`AssistContext`].

use hir::{Function, Semantics};
use ide_db::base_db::{FileId, FileRange};
use ide_db::{label::Label, RootDatabase};
use syntax::ast::HasName;
use syntax::{
    algo::{self, find_node_at_offset, find_node_at_range},
    ast, AstNode, AstToken, Direction, SourceFile, SyntaxElement, SyntaxKind, SyntaxToken,
    TextRange, TextSize, TokenAtOffset,
};

use crate::{
    assist_config::AssistConfig, Assist, AssistId, AssistKind, AssistResolveStrategy, GroupLabel,
    PostFailure, PreFailure, VerusError,
};
use crate::{CallInfo, VerusQuantifier};

pub(crate) use ide_db::source_change::{SourceChangeBuilder, TreeMutator};

use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::time::Instant;
use std::{
    hash::{Hash, Hasher},
    process::Command,
};

/// `AssistContext` allows to apply an assist or check if it could be applied.
///
/// Assists use a somewhat over-engineered approach, given the current needs.
/// The assists workflow consists of two phases. In the first phase, a user asks
/// for the list of available assists. In the second phase, the user picks a
/// particular assist and it gets applied.
///
/// There are two peculiarities here:
///
/// * first, we ideally avoid computing more things then necessary to answer "is
///   assist applicable" in the first phase.
/// * second, when we are applying assist, we don't have a guarantee that there
///   weren't any changes between the point when user asked for assists and when
///   they applied a particular assist. So, when applying assist, we need to do
///   all the checks from scratch.
///
/// To avoid repeating the same code twice for both "check" and "apply"
/// functions, we use an approach reminiscent of that of Django's function based
/// views dealing with forms. Each assist receives a runtime parameter,
/// `resolve`. It first check if an edit is applicable (potentially computing
/// info required to compute the actual edit). If it is applicable, and
/// `resolve` is `true`, it then computes the actual edit.
///
/// So, to implement the original assists workflow, we can first apply each edit
/// with `resolve = false`, and then applying the selected edit again, with
/// `resolve = true` this time.
///
/// Note, however, that we don't actually use such two-phase logic at the
/// moment, because the LSP API is pretty awkward in this place, and it's much
/// easier to just compute the edit eagerly :-)
pub(crate) struct AssistContext<'a> {
    pub(crate) config: &'a AssistConfig,
    pub(crate) sema: Semantics<'a, RootDatabase>,
    frange: FileRange,
    trimmed_range: TextRange,
    source_file: SourceFile,
    // verus
    // review: VerusContext ?
    pub(crate) verus_errors: Vec<VerusError>,
    pub(crate) verus_quantifiers: Vec<VerusQuantifier>, // WIP
}

impl<'a> AssistContext<'a> {
    pub(crate) fn new(
        sema: Semantics<'a, RootDatabase>,
        config: &'a AssistConfig,
        frange: FileRange,
        verus_errors: Vec<VerusError>,
        verus_quantifiers: Vec<VerusQuantifier>,
    ) -> AssistContext<'a> {
        let source_file = sema.parse(frange.file_id);

        let start = frange.range.start();
        let end = frange.range.end();
        let left = source_file.syntax().token_at_offset(start);
        let right = source_file.syntax().token_at_offset(end);
        let left =
            left.right_biased().and_then(|t| algo::skip_whitespace_token(t, Direction::Next));
        let right =
            right.left_biased().and_then(|t| algo::skip_whitespace_token(t, Direction::Prev));
        let left = left.map(|t| t.text_range().start().clamp(start, end));
        let right = right.map(|t| t.text_range().end().clamp(start, end));

        let trimmed_range = match (left, right) {
            (Some(left), Some(right)) if left <= right => TextRange::new(left, right),
            // Selection solely consists of whitespace so just fall back to the original
            _ => frange.range,
        };

        AssistContext {
            config,
            sema,
            frange,
            source_file,
            trimmed_range,
            verus_errors,
            verus_quantifiers,
        }
    }

    pub(crate) fn db(&self) -> &RootDatabase {
        self.sema.db
    }

    // NB, this ignores active selection.
    pub(crate) fn offset(&self) -> TextSize {
        self.frange.range.start()
    }

    pub(crate) fn file_id(&self) -> FileId {
        self.frange.file_id
    }

    pub(crate) fn has_empty_selection(&self) -> bool {
        self.trimmed_range.is_empty()
    }

    /// Returns the selected range trimmed for whitespace tokens, that is the range will be snapped
    /// to the nearest enclosed token.
    pub(crate) fn selection_trimmed(&self) -> TextRange {
        self.trimmed_range
    }

    pub(crate) fn token_at_offset(&self) -> TokenAtOffset<SyntaxToken> {
        self.source_file.syntax().token_at_offset(self.offset())
    }
    pub(crate) fn find_token_syntax_at_offset(&self, kind: SyntaxKind) -> Option<SyntaxToken> {
        self.token_at_offset().find(|it| it.kind() == kind)
    }
    pub(crate) fn find_token_at_offset<T: AstToken>(&self) -> Option<T> {
        self.token_at_offset().find_map(T::cast)
    }
    pub(crate) fn find_node_at_offset<N: AstNode>(&self) -> Option<N> {
        find_node_at_offset(self.source_file.syntax(), self.offset())
    }
    pub(crate) fn find_node_at_range<N: AstNode>(&self) -> Option<N> {
        find_node_at_range(self.source_file.syntax(), self.trimmed_range)
    }
    pub(crate) fn find_node_at_offset_with_descend<N: AstNode>(&self) -> Option<N> {
        self.sema.find_node_at_offset_with_descend(self.source_file.syntax(), self.offset())
    }
    /// Returns the element covered by the selection range, this excludes trailing whitespace in the selection.
    pub(crate) fn covering_element(&self) -> SyntaxElement {
        self.source_file.syntax().covering_element(self.selection_trimmed())
    }

    /*
        Verus

        HIR semantics related:

        document  1)API boundary and  2)Struct/enums
        Should write about the struct/enum definitions in hir crate

        how to goto hir def from cst node?   =>   ctx.sema.to_def(node)
        hot to goto cst node from hir def?    =>   ctx.sema.source(def)
        how to get type info?                 =>   ctx.sema.type_of_expr(&expr) , ctx.sema.type_of_pat(pat)
        resolve function at the callsite      =>  ctx.sema.resolve_method_call(&MethodcallExpr)?;
        resolve path                               ctx.sema.resolve_path(p);

        CST related

        document 1)API boundary and 2)struct/enums

        1)definition(struct/enums)
        defined at syntax::ast::generated::nodes, which are auto-generated from syntax/rust.ungram (which contains concise "ungrammar")

        To match a `SyntaxNode`(CST node) against an `ast` type =>  syntax::(lib)::match_ast!

        CST-visitor related:
        use ide_db::syntax_helpers::node_ext::{preorder_expr, walk_expr, walk_pat, walk_patterns_in_expr}
    */

    // REVIEW: trimmed_range?
    pub(crate) fn find_node_at_this_range<N: AstNode>(
        &self,
        trimmed_range: TextRange,
    ) -> Option<N> {
        find_node_at_range(self.source_file.syntax(), trimmed_range)
    }
    // just a "typed" duplicate of `find_node_at_this_range`
    #[allow(dead_code)]
    pub(crate) fn find_expr_at_this_range(
        &self,
        trimmed_range: TextRange,
    ) -> Option<syntax::ast::Expr> {
        self.find_node_at_this_range::<syntax::ast::Expr>(trimmed_range)
    }
    // just a "typed" duplicate of `find_node_at_offset`
    #[allow(dead_code)]
    pub(crate) fn find_surrounding_fn(&self) -> Option<syntax::ast::Fn> {
        self.find_node_at_offset::<syntax::ast::Fn>()
    }

    // REVIEW: use "flycheck id" to keep track of verus_error over several run of Verus
    // REVIEW: when Verus support crate, use "file id" to know which file a verus_error belongs to.
    // TODO: define API functions that returns a list of VerusError
    //       list of errors of specific conditions: error-type, surrounding function, offset, etc

    #[allow(dead_code)]
    fn filter_pre_failuires(&self, verus_errors: Vec<VerusError>) -> Vec<PreFailure> {
        let mut pre_errs = vec![];
        for verr in verus_errors {
            if let VerusError::Pre(p) = verr {
                pre_errs.push(p.clone());
            }
        }
        pre_errs
    }

    #[allow(dead_code)]
    fn filter_post_failuires(&self, verus_errors: Vec<VerusError>) -> Vec<PostFailure> {
        let mut post_errs = vec![];
        for verr in verus_errors {
            if let VerusError::Post(p) = verr {
                post_errs.push(p.clone());
            }
        }
        post_errs
    }
    #[allow(dead_code)]
    pub(crate) fn verus_errors_all(&self) -> Vec<VerusError> {
        self.verus_errors.to_vec()
    }
    #[allow(dead_code)]
    pub(crate) fn verus_pre_failures_all(&self) -> Vec<PreFailure> {
        self.filter_pre_failuires(self.verus_errors_all())
    }
    #[allow(dead_code)]
    pub(crate) fn verus_post_failures_all(&self) -> Vec<PostFailure> {
        self.filter_post_failuires(self.verus_errors_all())
    }
    #[allow(dead_code)]
    pub(crate) fn verus_errors_fn(&self) -> Option<Vec<VerusError>> {
        let surrounding_fn = self.find_node_at_offset::<syntax::ast::Fn>()?;
        let surrounding_range = surrounding_fn.syntax().text_range();
        let filtered_verus_errs = self
            .verus_errors_all()
            .into_iter()
            .filter(|verr| match verr {
                VerusError::Pre(pre) => surrounding_range.contains_range(pre.callsite),
                VerusError::Post(post) => surrounding_range.contains_range(post.failing_post),
                VerusError::Assert(assert) => surrounding_range.contains_range(assert.range),
            })
            .collect();
        Some(filtered_verus_errs)
    }
    #[allow(dead_code)]
    pub(crate) fn verus_pre_failures_fn(&self) -> Option<Vec<PreFailure>> {
        let verus_errors_fn = self.verus_errors_fn()?;
        Some(self.filter_pre_failuires(verus_errors_fn))
    }
    #[allow(dead_code)]
    pub(crate) fn verus_post_failures_fn(&self) -> Option<Vec<PostFailure>> {
        let verus_errors_fn = self.verus_errors_fn()?;
        Some(self.filter_post_failuires(verus_errors_fn))
    }

    // TODO: add verus error API function that filter verus_error of "this" function
    #[allow(dead_code)]
    pub(crate) fn node_from_pre_failure(&self, pre: PreFailure) -> Option<syntax::ast::Expr> {
        self.find_node_at_this_range::<syntax::ast::Expr>(pre.failing_pre)
    }
    #[allow(dead_code)]
    pub(crate) fn node_from_post_failure(&self, post: PostFailure) -> Option<syntax::ast::Expr> {
        self.find_node_at_this_range::<syntax::ast::Expr>(post.failing_post)
    }

    // among N found patterns, collect the range of named "hole".
    // for example, from this pattern "fn :[_]{:[body]}",
    // this collects the "body"'s range.
    // Assume only one "hole" is named and the other "hole"s are just "_".
    #[allow(dead_code)]
    pub(crate) fn textranges_from_comby_pattern(&self, pattern: String) -> Option<Vec<TextRange>> {
        let func: syntax::ast::Fn = self.find_node_at_offset::<syntax::ast::Fn>()?;
        let comby_result =
            run_comby_for(String::from("/usr/local/bin/comby"), pattern, func.fn_token()?)?;
        let mut text_ranges = vec![];
        for mat in comby_result.matches {
            for env in mat.environment {
                if env.variable == "_" {
                    continue;
                }
                let found_range = text_range_from(env.range.start.offset, env.range.end.offset);
                text_ranges.push(found_range);
            }
        }
        Some(text_ranges)
    }
    #[allow(dead_code)]
    pub(crate) fn textranges_in_current_fn(
        &self,
        ranges: Vec<TextRange>,
    ) -> Option<Vec<TextRange>> {
        let func = self.find_node_at_offset::<syntax::ast::Fn>()?;
        let func_range = func.syntax().text_range();
        let filtered_ranges =
            ranges.into_iter().filter(|x| func_range.contains_range(x.clone())).collect();
        Some(filtered_ranges)
    }

    // pub(crate) fn exprs_from_textranges(&self, ranges: Vec<TextRange>) -> Option<Vec<TextRange>> {
    //     let exprs = ranges.into_iter().map(|range| self.find_node_at_this_range::<ast::Expr>(range)?).collect();
    //     Some(exprs)
    // }
    #[allow(dead_code)]
    pub(crate) fn run_verus_on_fn(&self, token: SyntaxToken) -> Option<bool> {
        run_verus(self.config.verus_path.clone(), token, true)
    }
    #[allow(dead_code)]
    pub(crate) fn run_verus_on_file(&self, token: SyntaxToken) -> Option<bool> {
        run_verus(self.config.verus_path.clone(), token, false)
    }

    // if cursor is not on a function call, return None
    // if cursor is on a function call, get the HIR-def of the function
    #[allow(dead_code)]
    pub(crate) fn get_function_from_callsite(&self) -> Option<(Function, CallInfo)> {
        // code from inline_call
        let name_ref: ast::NameRef = self.find_node_at_offset()?;
        let call_info = crate::CallInfo::from_name_ref(name_ref.clone())?;
        let (function, _label) = match &call_info.node {
            ast::CallableExpr::Call(call) => {
                let path = match call.expr()? {
                    ast::Expr::PathExpr(path) => path.path(),
                    _ => None,
                }?;
                let function = match self.sema.resolve_path(&path)? {
                    hir::PathResolution::Def(hir::ModuleDef::Function(f)) => f,
                    _ => return None,
                };
                (function, format!("Inline `{}`", path))
            }
            ast::CallableExpr::MethodCall(call) => {
                (self.sema.resolve_method_call(call)?, format!("Inline `{}`", name_ref))
            }
        };
        Some((function, call_info))
    }
}

pub(crate) struct Assists {
    file: FileId,
    resolve: AssistResolveStrategy,
    buf: Vec<Assist>,
    allowed: Option<Vec<AssistKind>>,
}

impl Assists {
    pub(crate) fn new(ctx: &AssistContext<'_>, resolve: AssistResolveStrategy) -> Assists {
        Assists {
            resolve,
            file: ctx.frange.file_id,
            buf: Vec::new(),
            allowed: ctx.config.allowed.clone(),
        }
    }

    pub(crate) fn finish(mut self) -> Vec<Assist> {
        self.buf.sort_by_key(|assist| assist.target.len());
        self.buf
    }

    pub(crate) fn add(
        &mut self,
        id: AssistId,
        label: impl Into<String>,
        target: TextRange,
        f: impl FnOnce(&mut SourceChangeBuilder),
    ) -> Option<()> {
        let mut f = Some(f);
        self.add_impl(None, id, label.into(), target, &mut |it| f.take().unwrap()(it))
    }

    pub(crate) fn add_group(
        &mut self,
        group: &GroupLabel,
        id: AssistId,
        label: impl Into<String>,
        target: TextRange,
        f: impl FnOnce(&mut SourceChangeBuilder),
    ) -> Option<()> {
        let mut f = Some(f);
        self.add_impl(Some(group), id, label.into(), target, &mut |it| f.take().unwrap()(it))
    }

    fn add_impl(
        &mut self,
        group: Option<&GroupLabel>,
        id: AssistId,
        label: String,
        target: TextRange,
        f: &mut dyn FnMut(&mut SourceChangeBuilder),
    ) -> Option<()> {
        if !self.is_allowed(&id) {
            return None;
        }

        let mut trigger_signature_help = false;
        let source_change = if self.resolve.should_resolve(&id) {
            let mut builder = SourceChangeBuilder::new(self.file);
            f(&mut builder);
            trigger_signature_help = builder.trigger_signature_help;
            Some(builder.finish())
        } else {
            None
        };

        let label = Label::new(label);
        let group = group.cloned();
        self.buf.push(Assist { id, label, group, target, source_change, trigger_signature_help });
        Some(())
    }

    fn is_allowed(&self, id: &AssistId) -> bool {
        match &self.allowed {
            Some(allowed) => allowed.iter().any(|kind| kind.contains(id.1)),
            None => true,
        }
    }
}

// Arguments:
//      `token`: any SyntaxNode that is inside of the funtion/file that is needed to Verus to check
//      `verify_function`: Run Verus with `--verify-function` or not
//
// return value:
//     `Some`, it indicates either verification success or failure.
//     `None` indicates "failed to run Verus" including compile error and VIR/AIR error.
//
// REVIEW: we can make Verus error code. The, we can give Verus error code when failure, enabling further use-cases
pub fn run_verus(
    verus_exec_path: String,
    token: SyntaxToken,
    verify_function: bool,
) -> Option<bool> {
    let mut temp_text_string = String::new();
    let verify_func_flag = "--verify-function";
    let verify_root_flag = "--verify-root"; // TODO: figure out the surrounding module of `token`
    let rlimit_flag = "--rlimit";
    let rlimit_number = "3";
    let mut func_name = String::new();

    // get the text of the most grand parent
    // while doing so, find the surrounding function of this token. (to run "--verify-function")
    for ancestor in token.parent_ancestors() {
        temp_text_string = String::from(ancestor.text());
        match ancestor.kind() {
            SyntaxKind::FN => {
                if func_name.len() > 0 {
                    // if already found a function as a parent
                    dbg!("Not supported: when invoking verus, found func inside func. ");
                    return None;
                }
                let func = ast::Fn::cast(ancestor)?;
                func_name = func.name()?.to_string();
            }
            _ => (),
        }
    }

    // REIVEW: instead of writing to a file, consider
    // `dev/shm` OR `man memfd_create`
    let mut hasher = DefaultHasher::new();
    let now = Instant::now();
    now.hash(&mut hasher);

    let tmp_dir = env::temp_dir();
    let tmp_name = format!("{}_verus_assert_comment_{:?}_.rs", tmp_dir.display(), hasher.finish());
    dbg!(&tmp_name);
    let path = Path::new(&tmp_name);
    let display = path.display();

    // Open a file in write-only mode, returns `io::Result<File>`
    let mut file = match File::create(&path) {
        Err(why) => {
            dbg!("couldn't create {}: {}", display, why);
            return None;
        }
        Ok(file) => file,
    };

    // Write the modified verus program to `file`, returns `io::Result<()>`
    match file.write_all(temp_text_string.as_bytes()) {
        Err(why) => {
            dbg!("couldn't write to {}: {}", display, why);
            return None;
        }
        Ok(_) => dbg!("successfully wrote to {}", display),
    };

    dbg!(
        &verus_exec_path,
        &path,
        &verify_root_flag,
        &verify_func_flag,
        &func_name,
        &rlimit_flag,
        &rlimit_number
    );

    let output = if verify_function {
        Command::new(verus_exec_path)
            .arg(path)
            .arg(verify_root_flag)
            .arg(verify_func_flag)
            .arg(func_name)
            .arg(rlimit_flag)
            .arg(rlimit_number)
            .output()
    } else {
        Command::new(verus_exec_path).arg(path).arg(rlimit_flag).arg(rlimit_number).output()
    };

    match std::fs::remove_file(path) {
        Err(why) => {
            dbg!("couldn't remove file {}: {}", path.display(), why);
        }
        Ok(_) => {
            dbg!("successfully removed {}", path.display());
        }
    };

    let output = output.ok()?;
    dbg!(&output);
    if output.status.success() {
        return Some(true);
    } else {
        // disambiguate verification failure     VS    compile error etc
        match std::str::from_utf8(&output.stdout) {
            Ok(out) => {
                if out.contains("verification results:: verified: 0 errors: 0") {
                    // failure from other errors. (e.g. compile error)
                    return None;
                } else {
                    // verification failure
                    return Some(false);
                }
            }
            Err(_) => return None,
        }
    }
}

// `comby_exec_path`
// `comby_pattern`
// `token` argument can be any token in the file
//
// At the call site, it would be common to filter the textranges using the surrounding function's range
//
// REVIEW: for now, we assume a single line result, since we are running Verus/Comby for only one file.
// When Verus supports crate, consider returning vector of CombyResult
pub fn run_comby_for(
    comby_exec_path: String,
    comby_pattern: String,
    token: SyntaxToken,
) -> Option<CombyResult> {
    let mut temp_text_string = String::new();
    let _provide_rule = "-rule";
    let flag_match_only = "-match-only";
    let flag_json_lines = "-json-lines";
    let flag_match_new_line = "-match-newline-at-toplevel";

    // get the text of the most grand parent
    for ancestor in token.parent_ancestors() {
        temp_text_string = String::from(ancestor.text());
    }

    // REVIEW: instead of writing to a file, consider `dev/shm` OR `man memfd_create`
    let mut hasher = DefaultHasher::new();
    let now = Instant::now();
    now.hash(&mut hasher);
    let tmp_dir = env::temp_dir();
    let tmp_name = format!("{}_verus_search_comby{:?}_.rs", tmp_dir.display(), hasher.finish());
    let path = Path::new(&tmp_name);
    let display = path.display();

    let mut file = match File::create(&path) {
        Err(why) => {
            dbg!("couldn't create {}: {}", display, why);
            return None;
        }
        Ok(file) => file,
    };

    match file.write_all(temp_text_string.as_bytes()) {
        Err(why) => {
            dbg!("couldn't write to {}: {}", display, why);
            return None;
        }
        Ok(_) => (),
    };

    let output = Command::new(comby_exec_path)
        .arg(comby_pattern)
        .arg(".") // just a placeholder, since we are using `-match-only` flag.
        .arg(path)
        .arg(flag_match_only)
        .arg(flag_json_lines)
        .arg(flag_match_new_line)
        .output();

    match std::fs::remove_file(path) {
        Err(why) => {
            dbg!("couldn't remove file {}: {}", path.display(), why);
        }
        Ok(_) => (),
    };

    let output = output.ok()?;
    if !output.status.success() {
        dbg!("Comby output stauts failure");
        return None;
    }

    // For now, assume a single line result, since we are running Comby for only one file
    for line in output.stdout.lines() {
        let line = line.expect("Failed to parse comby result as json");
        let deserialized: CombyResult = serde_json::from_str(&line).unwrap();
        return Some(deserialized);
    }
    return None;
}

pub fn text_range_from(start: u32, end: u32) -> TextRange {
    TextRange::new(TextSize::from(start), TextSize::from(end))
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CombyResult {
    pub uri: Option<String>, // REVIEW: PATH
    pub matches: Vec<MatchInfo>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MatchInfo {
    pub range: CombyRange,
    pub environment: Vec<EnvironmentInfo>,
    pub matched: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentInfo {
    pub variable: String, // REVIEW: Option<String>
    pub value: String,
    pub range: CombyRange,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CombyRange {
    pub start: RangeInfo,
    pub end: RangeInfo,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RangeInfo {
    pub offset: u32,
    pub line: u32,
    pub column: u32,
}

#[test]
fn verus_comby1() {
    let json_line = r#"{"uri":"/Users/chanhee/hey.rs","matches":[{"range":{"start":{"offset":6,"line":1,"column":7},"end":{"offset":167,"line":10,"column":2}},"environment":[{"variable":"_","value":"my_proof_fun(x: u32, y: u32)\n    requires\n        x < 100,\n        y < 100,\n    ensures\n        x + y < 200,\n        x + y < 400,\n","range":{"start":{"offset":9,"line":1,"column":10},"end":{"offset":139,"line":8,"column":1}}},{"variable":"body","value":"\n    assert(x + y < 600);\n","range":{"start":{"offset":140,"line":8,"column":2},"end":{"offset":166,"line":10,"column":1}}}],"matched":"fn my_proof_fun(x: u32, y: u32)\n    requires\n        x < 100,\n        y < 100,\n    ensures\n        x + y < 200,\n        x + y < 400,\n{\n    assert(x + y < 600);\n}"}]}"#;
    let deserialized: CombyResult = serde_json::from_str(&json_line).unwrap();
    dbg!(&deserialized);
}
