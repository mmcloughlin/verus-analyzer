# Developing Verus Code Action

<!-- Just for now, assume reader's some knowledge/experience on Verus, rust-analyzer, Comby, and LSP. -->


## Overview: How to Develop Verus Code Action
`ide-assists` crate implements all code action inside rust-analyzer. We can start implementing a new Verus code action by making a new file inside `handlers` module, and registering the code action at `ide-assist/lib.rs`. 

All code action shares the same signature, which is `fn (acc: &mut Assists, ctx: &AssistContext<'_>) -> Option<()>`. A code action utilizes `ctx: &AssistContext` to get its relevant context, and append the generated source change to `acc: &mut Assists`. 

If a code action returns `None`, it indicates that the code action is not applicable in the given context. For example, assume we want a code action to be applicable only when the user's cursor hovers on `ensures` keyword. In this case, the code action should return `None` when the cursor isn't on `ensures`. Many APIs follow this style, which is returning `None` when a certain 

#### `AssistContext`
`AssistContext` contains all relevant context information, and it also contains basic APIs for developing code actions. 
It contains API for various tasks, including the following:

- [Retrieve Verus error from the previous run](#retrieve-verus-error-info-from-the-previous-run)
- [Invoke Verus and use its results](#invoking-verus-and-using-its-result)
- [Invoke Comby for syntactic search and use its results](#comby-syntactic-search)
- [Retrieve CST node at a given TextRange](#find-the-cst-node-at-a-given-textrange)
- [Use the user's current cursor location](#using-the-users-current-cursor-location)
<!-- - Filter out byte offsets with the current function scope(TODO) -->

Note that many APIs use `TextRange`, which is just a pair of byte offsets. For example, we can easily get `TextRange` of Verus errors, Comby search results, the surrounding function, the user's current cursor, and more. `TextRange` can be subsequently used to retrieve the CST node at that range, delete code at a range, insert code at a range, and more.

For more details, see `AssistContext`'s definition at `ide-assists::assist_context::AssistContext`.

#### Returning source changes
At the end of a code action implementation, we need to return the resulting source change using `SourceChangeBuilder`. These changes are propagated to LSP client, and these changes can be applied to users' code inside the IDE. `SourceChangeBuilder` implements various useful APIs, including `replace_ast`,  `insert`(insert a text string at a certain offset), and `delete`(remove the text string at a `TextRange`).

For more details, see `SourceChangeBuilder`'s definition at `ide_db::source_change::SourceChangeBuilder`.

#### Rust analyzer's internal API   
For advanced usages, APIs of `AssistContext` and `SourceChangeBuilder` might not be sufficient. However, since our custom rust-analyzer is already extended for Verus-specific parts, we can readily use rust analyzer's internal APIs to support advanced usages.

For example, the following tasks can be achieved by using rust analyzer's internal APIs:

- [Generate a CST node from a text string](#cst-from-text)
- [Use CST visitor patterns over ast::Expr, ast::Pat, and ast::Type](#cst-visitor-patterns)
- [Find the function definition from a callsite](#finding-function-definition-at-a-callsite)
- [Find the type of expression or variable](#how-to-get-type-info)
- TODO(find-all-usages, inline-function)








## How to interact with Verus 

#### Invoking Verus and using its result    
`AssistContext` has helper functions to invoke Verus. They return `Option<bool>`. `None` indicates "failed to run Verus" error, which includes compile error and VIR/AIR error. When it returns `Some`, it indicates either verification success or failure. These APIs can be used to check verification results, assuming certain CST replacements.

For more details, see helper functions at `assist_context::AssistContext::{run_verus_on_fn, run_verus_on_file}`.

#### Retrieve Verus Error Info from the previous run
After the user runs Verus by hitting the save button, the verification result is saved inside `AssistContext`. `AssistContext` contains APIs for retrieving Verus Errors.

Verus errors are defined as the following:
```
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum VerusError {
    Pre(PreFailure),
    Post(PostFailure),
    Assert(AssertFailure),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct PreFailure {
    pub failing_pre: TextRange,
    pub callsite: TextRange,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct PostFailure {
    pub failing_post: TextRange,
    pub func_body: TextRange,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct AssertFailure {
    pub range: TextRange,
}
```

For more details, see helper functions at `assist_context::AssistContext::{verus_errors, verus_pre_failures, verus_post_failures, node_from_pre_failure, node_from_post_failure}`.









## Comby syntactic search

To use this feature, users first need to install Comby, which is a syntactic search and rewrite tool. 
`AssistContext` contains an API to utilize Comby. It uses the user's pattern to get `TextRange`.

For example, one can use this pattern `fn :[_]{:[body]}` to get the function body's `Textrange`. 

Any "hole" that is not named (`:[_]`) is ignored. Unnamed holes' `TextRange` will not be returned.

For more details, see `assist_context::AssistContext::textranges_from_comby_pattern`.


(TODO: explain shortly how to use Comby)

#### For more deatils on Comby, see also:
https://comby.dev/
https://comby.live










## Concrete Syntax Tree(CST)

Concrete syntax tree tries to capture the exact text on the user's IDE, including whitespace, newline, and comments. It enables IDEs to manipulate formats as well. Verus code action manipulates text at CST level.

#### CST and `SyntaxNode`
Concrete syntax tree is based on `SyntaxNode`, which is a tree structure that is not aware of Rust syntax structure.

`AST` wraps `SyntaxNode` to make it easier to work with by defining CST as a wrapper. Note that these definitions are auto-generated from `syntax/rust.ungram`. This "ungrammar" file contains basic definitions concisely. It is very useful to see `syntax/rust.ungram` when working at CST level.

To get the underlying `SyntaxNode` of an AST node, use the `syntax` function, which is implemented by all AST nodes.




For example, in `rust.ungram`, `Fn` is defined as the following:

```
Fn =
 Attr* Visibility? Publish?
 'default'? 'const'? 'async'? 'unsafe'? Abi? FnMode?
 'fn' Name GenericParamList? ParamList RetType? WhereClause? RequiresClause? EnsuresClause?
 (body:BlockExpr | ';')
```

From the above, CST's `Fn` is auto-generated as the following:

```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fn {
    pub(crate) syntax: SyntaxNode,
}
impl ast::HasAttrs for Fn {}
impl ast::HasName for Fn {}
impl ast::HasVisibility for Fn {}
impl ast::HasGenericParams for Fn {}
impl ast::HasDocComments for Fn {}
impl Fn {
    pub fn publish(&self) -> Option<Publish> { support::child(&self.syntax) }
    pub fn default_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![default]) }
    pub fn const_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![const]) }
    pub fn async_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![async]) }
    pub fn unsafe_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![unsafe]) }
    pub fn abi(&self) -> Option<Abi> { support::child(&self.syntax) }
    pub fn fn_mode(&self) -> Option<FnMode> { support::child(&self.syntax) }
    pub fn fn_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![fn]) }
    pub fn param_list(&self) -> Option<ParamList> { support::child(&self.syntax) }
    pub fn ret_type(&self) -> Option<RetType> { support::child(&self.syntax) }
    pub fn requires_clause(&self) -> Option<RequiresClause> { support::child(&self.syntax) }
    pub fn ensures_clause(&self) -> Option<EnsuresClause> { support::child(&self.syntax) }
    pub fn body(&self) -> Option<BlockExpr> { support::child(&self.syntax) }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> { support::token(&self.syntax, T![;]) }
}
```

For more details, see `syntax::ast::generated::nodes` for `AST` definition, and `syntax::ast` for trait `AstNode` definition.,


#### Find the CST node at a given TextRange
We can use `AssistContext::find_node_at_range::<>` to get the CST node at a given `TextRange`. Note that we need to type the output, which are often `ast::Fn` or `ast::Expr`.

#### Using the user's current cursor location
For details, see `AssistContext::{find_token_at_offset, find_node_at_offset}`.

#### CST from text
To produce new code, it is often convenient to generate from a text string. We can simply do so using the parser of rust-analyzer. 
`ast_from_text` directly invokes the parser to get the CST from a given text. 

Note that we sometimes need to pad the text string with some additional string, especially when the text alone will produce a syntax error. To help with the situation, there are many helper functions, including `expr_from_text`.

For more details, see `syntax::ast::make`.

#### CST visitor patterns
AST visitor patterns are partially implemented. We can directly use these APIs to visit each node of `ast::Expr`, `ast::Pat`, and `ast::Type`. 
The following functions might be particularly useful:

- `walk_expr`
- `walk_pat`
- `walk_ty`
- `walk_patterns_in_expr`

Since `SyntaxNode` is untyped, it could be cumbersome to match against `AST` types. To help with this situation, we can use `match_ast!` macro to match a `SyntaxNode`(CST node) against `AST` types.

For more details, see `ide_db::syntax_helpers::node_ext`, and `syntax::match_ast!`.














## Using rust-analyzer's HIR

`AssisContext` contains `sema` field, which has type `Semantics`. It contains the semantics database, which can be used to query vairous facts about specific CST nodes.

Note that rust-analyzer's HIR is **not** rustc's HIR. Crate `hir` defines rust-analyzer's higher level description of source code.


#### HIR Definition

Each HIR struct is assigned its `Id`. For example, `hir::Function` has a single field `FunctionId`. 

Each struct implements various methods. For example, `struct Function` implements a method to get the list of typed arguments, and `struct Enum` implements a method to get the list of variants.

For more details, see `hir::lib`.


#### How to find hir definition from a CST node?   
`ctx.sema.to_def(node)`


#### How to find the CST node from a hir definition?    
`ctx.sema.source(def)`


#### Finding Function Definition at a Callsite
Noe that `ctx`'s type is `AssisContext`, `ctx.sema`'s type is `Semantics`, and `call`'s type is `ast::CallExpr`.

We could use below code snippet to get the hir definition of the function.

```
let path =  match call.expr()? {
                ast::Expr::PathExpr(path) => path.path(),
                _ => None,
            }?;
let function = match ctx.sema.resolve_path(&path)? {
    PathResolution::Def(hir::ModuleDef::Function(f)) => f,
    _ => return None,
};
```            
(TODO: make this a helper function?)

We can also use `ctx.sema.to_def(&function)` to get the CST node of the function.

#### How to get type info?                 
`ctx.sema.type_of_expr(&expr)`
`ctx.sema.type_of_pat(pat)`    

<!-- #### resolve function at the callsite      
ctx.sema.resolve_method_call(&MethodcallExpr)?;

#### resolve path                               ctx.sema.resolve_path(p);   -->

<!-- #### find all usages
See module `ide_db::search` -->


<!-- #### `Inline Function`
---- HIR
document  1)API boundary and  2)Struct/enums 
Should write about the struct/enum definitions in hir crate -->


<!-- Q: _to_def  VS resolve? -->


    

   


## Example: "Check if this assertion is essential"
TODO: walk through this example to provide an overall view of how this works













## misc

#### Code Style
For composability, users are encouraged to separate the code action's rewriting part as a new function. The rewrite functions will have the signature of `CSTNode -> Option<CSTNode>`, where `None` indicates the rewrite failure. 

TODO: elaborate

#### Testing code action
TODO
`$0` for the user's cursor

#### key binding
In VS Code, the default key binding for code action might be `ctrl .` or `fn .`

#### Details of LSP specifications
https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#codeAction 

#### Details of rust-analyzer internals
https://github.com/rust-lang/rust-analyzer/blob/master/docs/dev/syntax.md
https://github.com/rust-lang/rust-analyzer/blob/master/docs/dev/lsp-extensions.md
https://github.com/rust-lang/rust-analyzer/blob/master/docs/dev/architecture.md#crateshir







<!-- 
TODO: rustdoc on `assist_context`

Q. how can I do "find all references"? "comby?"
Q. is this document enough to get started?

 -->
