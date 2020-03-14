//! Simply typed lambda-calculus with booleans.
//!
//! Unlike the one in the book, it uses '\' as the token for λ to simplify the
//! notation. `Expr` corresponds to "term" in the book.

use std::collections::HashMap;
use std::env;
use std::fmt;
use std::fs::File;
use std::io::{prelude::*, BufReader};
use std::iter::Peekable;
use std::str::CharIndices;

use tapl::{hash_map, Error, Result, Span};

fn syntax_error(at: Span, summary: &str) -> Error {
    Error::new("SyntaxError").at(at).summary(summary)
}

fn type_error(at: Option<Span>, summary: &str) -> Error {
    let e = Error::new("TypeError").summary(summary);
    match at {
        Some(at) => e.at(at),
        None => e,
    }
}

fn type_mismatch(node: &Node, expect: &Ty, actual: &Ty) -> Error {
    type_error(node.span, "type mismatch").expect_actual(&expect.to_string(), &actual.to_string())
}

fn eval_error(summary: &str) -> Error {
    Error::new("EvalError").summary(summary)
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum TokenKind {
    Arrow,
    Bool,
    Colon,
    Dot,
    Else,
    False,
    If,
    Lambda,
    ParenL,
    ParenR,
    Then,
    True,
    Ident,
}

/// Lexical token. Distinguished by the kind.
/// `span` holds the place at which the token appears in the text.
#[derive(Clone, Copy)]
struct Token {
    kind: TokenKind,
    span: Span,
}

/// Lexical scanner. It is an iterator over `Result<Token>`.
struct TokenStream<'tx> {
    text: &'tx str,
    src: Peekable<CharIndices<'tx>>,
    keywords: HashMap<&'static str, TokenKind>,
}

impl<'tx> TokenStream<'tx> {
    fn new(text: &'tx str) -> Self {
        TokenStream {
            text,
            src: text.char_indices().peekable(),
            keywords: hash_map! {
                "Bool" => TokenKind::Bool,
                "else" => TokenKind::Else,
                "false" => TokenKind::False,
                "if" => TokenKind::If,
                "then" => TokenKind::Then,
                "true" => TokenKind::True,
            },
        }
    }

    fn next_token(&mut self) -> Result<Option<Token>> {
        while let Some((start, ch)) = self.src.next() {
            let kind = match ch {
                ' ' | '\n' => continue,
                '-' => {
                    self.eat('>')?;
                    TokenKind::Arrow
                }
                ':' => TokenKind::Colon,
                '.' => TokenKind::Dot,
                '\\' => TokenKind::Lambda,
                '(' => TokenKind::ParenL,
                ')' => TokenKind::ParenR,
                'A'..='Z' | 'a'..='z' | '_' => {
                    let cond = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '\'';
                    while matches!(self.src.peek(), Some((_, ch)) if cond(*ch)) {
                        self.src.next();
                    }
                    let name = &self.text[self.span(start).range()];
                    *self.keywords.get(name).unwrap_or(&TokenKind::Ident)
                }
                _ => return Err(syntax_error(self.span(start), "invalid character")),
            };
            let span = self.span(start);
            return Ok(Some(Token { kind, span }));
        }
        Ok(None)
    }

    fn eat(&mut self, ch: char) -> Result<()> {
        match self.src.next() {
            Some((_, c)) if c == ch => Ok(()),
            Some((i, _)) => Err(syntax_error(self.span(i), "invalid character")),
            None => Err(syntax_error(self.span(self.text.len()), "unexpected EOF")),
        }
    }

    fn span(&mut self, start: usize) -> Span {
        let end = match self.src.peek() {
            Some((i, _)) => *i,
            None => self.text.len(),
        };
        Span { start, end }
    }
}

impl<'tx> Iterator for TokenStream<'tx> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().transpose()
    }
}

/// Type expression.
#[derive(Clone, PartialEq)]
enum Ty {
    Arrow(Box<Ty>, Box<Ty>),
    Bool,
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Arrow(l, r) => match l.as_ref() {
                Ty::Arrow(_, _) => write!(f, "({}) -> {}", l, r),
                _ => write!(f, "{} -> {}", l, r),
            },
            Ty::Bool => f.write_str("Bool"),
        }
    }
}

/// Symbol environment.
struct Context<'tx> {
    text: &'tx str,
    stack: Vec<(String, Ty)>,
    map: HashMap<String, Vec<usize>>,
}

impl<'tx> Context<'tx> {
    /// Creates a new context referring the text.
    fn new(text: &'tx str) -> Self {
        let stack = Vec::new();
        let map = HashMap::new();
        Context { text, stack, map }
    }

    fn text_at(&self, span: Span) -> &str {
        &self.text[span.range()]
    }

    /// Pair of variable name and type for the given de Brujin index.
    fn get(&self, index: i64) -> (&str, &Ty) {
        let pair = &self.stack[self.stack.len() - (index as usize) - 1];
        (&pair.0, &pair.1)
    }

    /// Variable name for the given de Brujin index.
    fn name(&self, index: i64) -> &str {
        self.get(index).0
    }

    /// Variatle type for the given de Brujin index.
    fn ty(&self, index: i64) -> &Ty {
        self.get(index).1
    }

    /// de Brujin index of the given name.
    fn rfind(&self, name: Span) -> Option<i64> {
        match self.map.get(self.text_at(name)) {
            Some(v) => v.last().map(|i| (self.stack.len() - *i - 1) as i64),
            _ => None,
        }
    }

    /// Pushes a variable to the context. Returns the name for display.
    fn push(&mut self, name: Span, ty: Ty) -> &str {
        let n_ticks = {
            let name_s = self.text_at(name).to_string();
            let v = self.map.entry(name_s).or_insert(Vec::new());
            v.push(self.stack.len());
            v.len() - 1
        };
        self.stack.push((
            format!("{}{:'<w$}", self.text_at(name), "", w = n_ticks),
            ty,
        ));
        &self.stack.last().unwrap().0
    }

    /// Pops the variable name for the inner most abstraction term.
    ///
    /// It returns the type of the variable.
    fn pop(&mut self) -> Ty {
        let (display_name, ty) = self.stack.pop().expect("popped from empty context");
        let name = match display_name.find('\'') {
            Some(i) => &display_name[..i],
            None => &display_name[..],
        };
        self.map.get_mut(name).unwrap().pop();
        ty
    }
}

/// Structure of abstract syntax tree.
#[derive(Clone)]
enum Expr {
    Var(i64),
    Abs(Span, Ty, Node),
    App(Node, Node),
    If(Node, Node, Node),
    False,
    True,
}

impl Into<Node> for Expr {
    fn into(self) -> Node {
        Node::new(None, self)
    }
}

/// Node of the abstract syntax tree.
#[derive(Clone)]
struct Node {
    span: Option<Span>,
    expr: Box<Expr>,
}

impl Node {
    fn new(span: Option<Span>, expr: Expr) -> Node {
        let expr = Box::new(expr);
        Node { span, expr }
    }

    /// Creates a node with span information.
    fn at(span: Span, expr: Expr) -> Node {
        Node {
            span: Some(span),
            expr: Box::new(expr),
        }
    }

    /// True if the node is a value term.
    fn is_val(&self) -> bool {
        matches!(self.expr.as_ref(), Expr::Abs(_, _, _) | Expr::True | Expr::False)
    }

    /// Shifts de Brujin indices.
    fn shift(&self, d: i64) -> Node {
        fn walk(c: i64, d: i64, t: &Node) -> Node {
            let expr = match t.expr.as_ref() {
                Expr::Var(x) => Expr::Var(if *x >= c { x + d } else { *x }),
                Expr::Abs(name, ty, body) => Expr::Abs(*name, ty.clone(), walk(c + 1, d, body)),
                Expr::App(t1, t2) => Expr::App(walk(c, d, t1), walk(c, d, t2)),
                Expr::If(cond, then, els) => {
                    Expr::If(walk(c, d, cond), walk(c, d, then), walk(c, d, els))
                }
                Expr::True => Expr::True,
                Expr::False => Expr::False,
            };
            Node::new(t.span, expr)
        }
        walk(0, d, self)
    }

    /// Substitutes a term to the given variable.
    fn subst(&self, j: i64, s: &Node) -> Node {
        fn walk(j: i64, c: i64, s: &Node, t: &Node) -> Node {
            let expr = match t.expr.as_ref() {
                Expr::Var(x) => {
                    if *x == j + c {
                        return s.shift(c);
                    } else {
                        Expr::Var(*x)
                    }
                }
                Expr::Abs(name, ty, body) => Expr::Abs(*name, ty.clone(), walk(j, c + 1, s, body)),
                Expr::App(t1, t2) => Expr::App(walk(j, c, s, t1), walk(j, c, s, t2)),
                Expr::If(cond, then, els) => {
                    Expr::If(walk(j, c, s, cond), walk(j, c, s, then), walk(j, c, s, els))
                }
                Expr::True => Expr::True,
                Expr::False => Expr::False,
            };
            Node::new(t.span, expr)
        }
        walk(j, 0, s, self)
    }

    /// Single step evaluation of the node.
    fn eval1(&self) -> Result<Node> {
        match self.expr.as_ref() {
            Expr::App(t1, t2) => match t1.expr.as_ref() {
                // E-AbsApp
                Expr::Abs(_, _, t12) if t2.is_val() => Ok(t12.subst(0, &t2.shift(1)).shift(-1)),
                // E-App2
                Expr::Abs(_, _, _) => Ok(Node::new(self.span, Expr::App(t1.clone(), t2.eval1()?))),
                // E-App1
                _ => Ok(Node::new(self.span, Expr::App(t1.eval1()?, t2.clone()))),
            },
            Expr::If(cond, then, els) => match cond.expr.as_ref() {
                // E-IfTrue
                Expr::True => Ok(then.clone()),
                // E-IfFalse
                Expr::False => Ok(els.clone()),
                // E-If
                _ => Ok(Expr::If(cond.eval1()?, then.clone(), els.clone()).into()),
            },
            _ => Err(eval_error("no rule applied")),
        }
    }

    /// Runs type check.
    fn ty(&self, ctx: &mut Context) -> Result<Ty> {
        match self.expr.as_ref() {
            Expr::Var(i) => Ok(ctx.ty(*i).clone()),
            Expr::Abs(name, ty, body) => {
                ctx.push(*name, ty.clone());
                let body_ty = body.ty(ctx)?;
                Ok(Ty::Arrow(Box::new(ctx.pop()), Box::new(body_ty)))
            }
            Expr::App(t1, t2) => {
                let ty1 = t1.ty(ctx)?;
                let ty2 = t2.ty(ctx)?;
                match ty1 {
                    Ty::Arrow(arg, ret) if *arg == ty2 => Ok(*ret),
                    Ty::Arrow(arg, _) => Err(type_mismatch(t2, &arg, &ty2)),
                    Ty::Bool => Err(type_error(t1.span, "cannot apply non-abstract value")),
                }
            }
            Expr::If(cond, then, els) => {
                let cond_ty = cond.ty(ctx)?;
                if cond_ty != Ty::Bool {
                    return Err(type_mismatch(cond, &Ty::Bool, &cond_ty));
                }
                let then_ty = then.ty(ctx)?;
                let els_ty = els.ty(ctx)?;
                if then_ty != els_ty {
                    return Err(type_mismatch(els, &then_ty, &els_ty));
                }
                Ok(then_ty)
            }
            Expr::True | Expr::False => Ok(Ty::Bool),
        }
    }

    /// Pretty prints the AST.
    fn show(&self, ctx: &mut Context) -> String {
        match self.expr.as_ref() {
            Expr::Var(x) => ctx.name(*x).to_string(),
            Expr::Abs(name, ty, e) => {
                let name_show = ctx.push(*name, ty.clone()).to_owned();
                let e_show = e.show(ctx);
                ctx.pop();
                format!("\\{}:{}. {}", name_show, ty, e_show)
            }
            Expr::App(t1, t2) => {
                let t1_show = match t1.expr.as_ref() {
                    Expr::Abs(_, _, _) | Expr::If(_, _, _) => format!("({})", t1.show(ctx)),
                    _ => t1.show(ctx),
                };
                match t2.expr.as_ref() {
                    Expr::Abs(_, _, _) | Expr::App(_, _) => {
                        format!("{} ({})", t1_show, t2.show(ctx))
                    }
                    _ => format!("{} {}", t1_show, t2.show(ctx)),
                }
            }
            Expr::If(cond, then, els) => format!(
                "if {} then {} else {}",
                cond.show(ctx),
                then.show(ctx),
                els.show(ctx)
            ),
            Expr::False => "false".to_string(),
            Expr::True => "true".to_string(),
        }
    }
}

impl fmt::Display for Node {
    /// Shows the AST as a nameless term.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr.as_ref() {
            Expr::Var(x) => write!(f, "{}", x),
            Expr::Abs(_, ty, e) => write!(f, "\\:{}. {}", ty, e),
            Expr::App(t1, t2) => {
                match t1.expr.as_ref() {
                    Expr::Abs(_, _, _) | Expr::If(_, _, _) => write!(f, "({}) ", t1)?,
                    _ => write!(f, "{} ", t1)?,
                }
                match t2.expr.as_ref() {
                    Expr::Abs(_, _, _) | Expr::App(_, _) => write!(f, "({})", t2),
                    _ => write!(f, "{}", t2),
                }
            }
            Expr::If(cond, then, els) => write!(f, "if {} then {} else {}", cond, then, els),
            Expr::False => f.write_str("false"),
            Expr::True => f.write_str("true"),
        }
    }
}

/// Syntaxtic parser.
struct Parser<'tx> {
    ctx: Context<'tx>,
    src: Peekable<TokenStream<'tx>>,
}

macro_rules! matches_kind {
    ($expr:expr, $($pat:pat)|* $(if $guard:expr)?) => {
        matches!($expr, Some(Ok(token)) if matches!(token.kind, $($pat)|* $(if $guard)*))
    };
}

impl<'tx> Parser<'tx> {
    /// Parses the text.
    fn parse(text: &'tx str) -> Result<Node> {
        let mut parser = Parser {
            ctx: Context::new(text),
            src: TokenStream::new(text).peekable(),
        };
        let expr = parser.expr()?;
        match parser.src.next() {
            Some(Ok(token)) => Err(parser.invalid_token(token)),
            Some(Err(e)) => Err(e),
            None => Ok(expr),
        }
    }

    fn expr(&mut self) -> Result<Node> {
        let mut lhs = self.arg()?;
        while matches_kind!(
            self.src.peek(),
            TokenKind::If
                | TokenKind::Lambda
                | TokenKind::ParenL
                | TokenKind::True
                | TokenKind::False
                | TokenKind::Ident
        ) {
            let rhs = self.arg()?;
            lhs = Node::new(None, Expr::App(lhs, rhs));
        }
        Ok(lhs)
    }

    fn arg(&mut self) -> Result<Node> {
        match self.src.next() {
            Some(Ok(token)) => match token.kind {
                TokenKind::ParenL => {
                    let expr = self.expr()?;
                    self.eat(TokenKind::ParenR)?;
                    Ok(expr)
                }
                TokenKind::Lambda => {
                    let name = self.eat(TokenKind::Ident)?;
                    self.eat(TokenKind::Colon)?;

                    let ty = self.ty()?;
                    self.ctx.push(name.span, ty.clone());

                    let dot = self.eat(TokenKind::Dot)?;
                    let expr = self.expr()?;
                    self.ctx.pop();
                    Ok(Node::at(
                        Span::cover(token.span, dot.span),
                        Expr::Abs(name.span, ty, expr),
                    ))
                }
                TokenKind::Ident => match self.ctx.rfind(token.span) {
                    Some(index) => Ok(Node::at(token.span, Expr::Var(index))),
                    None => Err(syntax_error(token.span, "undefined variable")),
                },
                TokenKind::If => {
                    let cond = self.expr()?;
                    self.eat(TokenKind::Then)?;
                    let then = self.expr()?;
                    self.eat(TokenKind::Else)?;
                    let els = self.expr()?;
                    Ok(Node::at(token.span, Expr::If(cond, then, els)))
                }
                TokenKind::True => Ok(Node::at(token.span, Expr::True)),
                TokenKind::False => Ok(Node::at(token.span, Expr::False)),
                _ => Err(self.invalid_token(token)),
            },
            Some(Err(e)) => Err(e),
            None => Err(self.unexpected_eof()),
        }
    }

    fn ty(&mut self) -> Result<Ty> {
        let lhs = match self.src.next() {
            Some(Ok(token)) => match token.kind {
                TokenKind::ParenL => {
                    let ty = self.ty()?;
                    self.eat(TokenKind::ParenR)?;
                    ty
                }
                TokenKind::Bool => Ty::Bool,
                _ => return Err(self.invalid_token(token)),
            },
            Some(Err(e)) => return Err(e),
            None => return Err(self.unexpected_eof()),
        };
        Ok(if matches_kind!(self.src.peek(), TokenKind::Arrow) {
            self.src.next();
            let rhs = self.ty()?;
            Ty::Arrow(Box::new(lhs), Box::new(rhs))
        } else {
            lhs
        })
    }

    fn eat(&mut self, expect: TokenKind) -> Result<Token> {
        match self.src.next() {
            Some(Ok(token)) if token.kind == expect => Ok(token),
            Some(Ok(token)) => Err(self.invalid_token(token)),
            Some(Err(e)) => Err(e),
            None => Err(self.unexpected_eof()),
        }
    }

    fn invalid_token(&mut self, token: Token) -> Error {
        syntax_error(token.span, "invalid token")
    }

    fn unexpected_eof(&mut self) -> Error {
        let len = self.ctx.text.len();
        syntax_error(Span::new(len..len), "unexpected EOF")
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let path = args.get(1).expect("invalid arguments");
    let file = File::open(path).expect("cannot open file");
    let mut reader = BufReader::new(file);
    let mut text = String::new();
    reader.read_to_string(&mut text).expect("cannot read file");

    let mut node = tapl::unwrap_or_die(Parser::parse(&text));
    let ty = tapl::unwrap_or_die(node.ty(&mut Context::new(&text)));
    println!("{} :: {}", node.show(&mut Context::new(&text)), ty);
    while !node.is_val() {
        node = tapl::unwrap_or_die(node.eval1());
        println!("=> {}", node.show(&mut Context::new(&text)));
    }
}
