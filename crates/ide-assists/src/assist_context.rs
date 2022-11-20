//! See [`AssistContext`].

use hir::Semantics;
use ide_db::base_db::{FileId, FileRange};
use ide_db::{label::Label, RootDatabase};
use syntax::ast::HasName;
use syntax::{
    algo::{self, find_node_at_offset, find_node_at_range},
    AstNode, AstToken, Direction, SourceFile, SyntaxElement, SyntaxKind, SyntaxToken, TextRange,
    TextSize, TokenAtOffset,
};

use crate::{
    assist_config::AssistConfig, Assist, AssistId, AssistKind, AssistResolveStrategy, GroupLabel,
    VerusError,PostFailure, PreFailure, AssertFailure,
};

pub(crate) use ide_db::source_change::{SourceChangeBuilder, TreeMutator};
use lsp_types::{DiagnosticSeverity, Range};




use std::{process::Command, hash::{Hash, Hasher}};
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use std::time::{Instant};
use std::collections::hash_map::DefaultHasher;
use std::env;
use serde::{Serialize, Deserialize, Deserializer};

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
    pub(crate) verus_errors: Vec<VerusError>, 
}

impl<'a> AssistContext<'a> {
    pub(crate) fn new(
        sema: Semantics<'a, RootDatabase>,
        config: &'a AssistConfig,
        frange: FileRange,
        verus_errors: Vec<VerusError>, 
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

        AssistContext { config, sema, frange, source_file, trimmed_range, verus_errors}
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

    // verus

    // REVIEW: trimmed_range?
    pub(crate) fn find_node_at_this_range<N: AstNode>(&self, trimmed_range:TextRange) -> Option<N> {
        find_node_at_range(self.source_file.syntax(), trimmed_range)
    }
    // TODO: use "flycheck id" and "file id"
    // TODO: define API functions that returns a list of VerusError 
    //       list of errors of specific conditions: error-type, surrounding function, offset, etc
    pub(crate) fn verus_errors(&self) -> Vec<VerusError> {
        self.verus_errors.to_vec()
    }
    pub(crate) fn verus_pre_failures(&self) -> Vec<VerusError> {
        let pre_errors:Vec<VerusError> = self.verus_errors.to_vec().into_iter().filter(
            |verr| 
                match *verr {
                    VerusError::Pre(_) => true,
                    _ => false}).collect();
        pre_errors
    }
    pub(crate) fn verus_post_failures(&self) -> Vec<VerusError> {
        let post_errors:Vec<VerusError> = self.verus_errors.to_vec().into_iter().filter(
            |verr| 
                match *verr {
                    VerusError::Post(_) => true,
                    _ => false}).collect();
        post_errors
    }

    // TODO: add verus error API function that filter verus_error of "this" function

    pub(crate) fn node_from_pre_failure(&self, pre: PreFailure) -> Option<syntax::ast::Expr> {
        self.find_node_at_this_range::<syntax::ast::Expr>(pre.failing_pre)
    }
    pub(crate) fn node_from_post_failure(&self, post: PostFailure) -> Option<syntax::ast::Expr> {
        self.find_node_at_this_range::<syntax::ast::Expr>(post.failing_post)
    }

    // among N found patterns, collect the range of named "hole".
    // for example, from this pattern "fn :[_]{:[body]}",
    // this collects the "body"'s range.
    // Assume only one "hole" is named and the other "hole"s are just "_".
    pub(crate) fn textrange_from_comby_pattern(&self, pattern: String) -> Option<Vec<TextRange>> {
        let func : syntax::ast::Fn = self.find_node_at_offset::<syntax::ast::Fn>()?;
        let comby_result = run_comby_for(String::from("/usr/local/bin/comby"), pattern, func.fn_token()?)?;
        dbg!(&comby_result);        
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
        dbg!(&text_ranges);
        Some(text_ranges)
    }

    // pub(crate) fn node_from_comby_pattern(&self, pattern: String) -> Option<syntax::ast::Expr> { // REVIEW: return type?
    // }


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



// TODO: return vector of textrange instead of one
// at the call site, filter results with the surrounding function range
pub fn run_comby_for(comby_exec_path: String, comby_pattern: String, token: SyntaxToken) -> Option<CombyResult> {
    let mut temp_text_string = String::new();
    let mut func_name = String::new();
    let flag_match_only = "-match-only";
    let flag_json_lines = "-json-lines";
    let flag_match_new_line = "-match-newline-at-toplevel";

    // get the text of the most grand parent
    // while doing so, find the surrounding function of this token. (to run "--verify-function")
    for ancestor in token.parent_ancestors() {
        temp_text_string = String::from(ancestor.text());
        match ancestor.kind() {
            SyntaxKind::FN => {
                if func_name.len() > 0 { // if already found a function as a parent
                    dbg!("Not supported: when invoking verus, found func inside func. ");
                    return None;
                }
                let func = syntax::ast::Fn::cast(ancestor)?;
                func_name = func.name()?.to_string();
            }
            _ => (),
        }
    }

    // TODO: instead of writing to a file, consider
    // `dev/shm` OR `man memfd_create`
    let mut hasher = DefaultHasher::new();
    let now = Instant::now();
    now.hash(&mut hasher);
    let tmp_dir = env::temp_dir();
    let tmp_name = format!("{}_verus_search_comby{:?}_.rs", tmp_dir.display(), hasher.finish());
    let path = Path::new(&tmp_name);
    let display = path.display();

    let mut file = match File::create(&path) {
        Err(why) =>{dbg!("couldn't create {}: {}", display, why); return None},
        Ok(file) => file,
    };

    match file.write_all(temp_text_string.as_bytes()) {
        Err(why) => {dbg!("couldn't write to {}: {}", display, why); return None},
        Ok(_) => dbg!("successfully wrote to {}", display),
    };

    // dbg!(&comby_exec_path, &comby_pattern, &path, &flag_match_only, &flag_json_lines);
    let output = Command::new(comby_exec_path)
    .arg(comby_pattern)
    .arg(".")
    .arg(path)
    .arg(flag_match_only)
    .arg(flag_json_lines)
    .arg(flag_match_new_line)
    .output();

    match std::fs::remove_file(path) {
        Err(why) => {dbg!("couldn't remove file {}: {}", path.display(), why);},
        Ok(_) => {dbg!("successfully removed {}", path.display());},
    };

    let output = output.ok()?;
    // dbg!(&output);
    if output.status.success() {
        dbg!("output stauts success");
    } else {
        dbg!("output stauts failure");
        return None;
    }

    // REVIEW: assume only one line result
    for line in output.stdout.lines() {
        let line = line.unwrap(); // TODO: change this to ? instead of unwrap. For now, I am keeping it to see if this json parsing works well
        let deserialized: CombyResult = serde_json::from_str(&line).unwrap();
        return(Some(deserialized));
    }
    return None;
}


pub fn text_range_from(start: u32, end: u32) -> TextRange {
    TextRange::new(TextSize::from(start), TextSize::from(end))
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CombyResult {
    pub uri: Option<String>, // REVIEW: PATH?
    pub matches: Vec<MatchInfo>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct MatchInfo {
    pub range: CombyRange,
    pub environment: Vec<EnvironmentInfo> ,
    pub matched: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct EnvironmentInfo {
    pub variable: String,  // REVIEW: Option<String> ?
    pub value: String,
    pub range: CombyRange,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CombyRange {
    pub start: RangeInfo,
    pub end: RangeInfo,
}

#[derive(Debug, Serialize, Deserialize)]
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


