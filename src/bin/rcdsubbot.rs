//! Simply typed lambda-calculus with subtyping, records, and bottom.
//!
//! Unlike the one in the book, it uses '\' as the token for λ to simplify the
//! notation. `Expr` corresponds to "term" in the book. This implementation
//! also adds an `error` expression to create a term of a type `Bot`.

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

fn record_type_mismatch(expect: &Ty, actual: &Ty, key: &str) -> Error {
    type_error(None, &format!("subtype failed at key {}", key))
        .expect_actual(&expect.to_string(), &actual.to_string())
}

fn type_mismatch(expect: &Ty, actual: &Ty) -> Error {
    type_error(None, "subtype failed").expect_actual(&expect.to_string(), &actual.to_string())
}

fn eval_error(summary: &str) -> Error {
    Error::new("EvalError").summary(summary)
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum TokenKind {
    Arrow,
    Bot,
    BraceL,
    BraceR,
    Colon,
    Comma,
    Dot,
    Equal,
    Error,
    Lambda,
    ParenL,
    ParenR,
    Top,
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
                "Bot" => TokenKind::Bot,
                "error" => TokenKind::Error,
                "Top" => TokenKind::Top,
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
                '{' => TokenKind::BraceL,
                '}' => TokenKind::BraceR,
                ':' => TokenKind::Colon,
                ',' => TokenKind::Comma,
                '.' => TokenKind::Dot,
                '=' => TokenKind::Equal,
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
    Record(Vec<(String, Ty)>),
    Bot,
    Top,
}

impl Ty {
    fn subtype(&self, other: &Ty) -> Result<()> {
        match (self, other) {
            _ if self == other => Ok(()),
            (Ty::Arrow(s1, s2), Ty::Arrow(t1, t2)) => {
                t1.subtype(s1)?;
                s2.subtype(t2)
            }
            (Ty::Record(s), Ty::Record(t)) => {
                for (key, t1) in t {
                    match rcd_find(s, key) {
                        Some(s1) => s1.subtype(t1)?,
                        None => return Err(record_type_mismatch(other, self, key)),
                    }
                }
                Ok(())
            }
            (Ty::Bot, _) => Ok(()),
            (_, Ty::Top) => Ok(()),
            _ => Err(type_mismatch(other, self)),
        }
    }
}

fn rcd_find<'a, K: PartialEq, V>(rcd: &'a [(K, V)], key: &K) -> Option<&'a V> {
    rcd.iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ty::Arrow(l, r) => match l.as_ref() {
                Ty::Arrow(_, _) => write!(f, "({}) -> {}", l, r),
                _ => write!(f, "{} -> {}", l, r),
            },
            Ty::Record(entries) => {
                let reprs = entries
                    .iter()
                    .map(|(name, ty)| format!("{}:{}", name, ty))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{{{}}}", reprs)
            }
            Ty::Bot => write!(f, "Bot"),
            Ty::Top => write!(f, "Top"),
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
    Record(Vec<(String, Node)>),
    Proj(Node, String),
    Error,
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
        match self.expr.as_ref() {
            Expr::Abs(_, _, _) => true,
            Expr::Record(entries) => entries.iter().all(|(_, t)| t.is_val()),
            _ => false,
        }
    }

    /// Shifts de Brujin indices.
    fn shift(&self, d: i64) -> Node {
        fn walk(c: i64, d: i64, t: &Node) -> Node {
            let expr = match t.expr.as_ref() {
                Expr::Var(x) => Expr::Var(if *x >= c { x + d } else { *x }),
                Expr::Abs(name, ty, body) => Expr::Abs(*name, ty.clone(), walk(c + 1, d, body)),
                Expr::App(t1, t2) => Expr::App(walk(c, d, t1), walk(c, d, t2)),
                Expr::Record(entries) => Expr::Record(
                    entries
                        .iter()
                        .map(|(k, t)| (k.clone(), walk(c, d, t)))
                        .collect(),
                ),
                Expr::Proj(t, k) => Expr::Proj(walk(c, d, t), k.clone()),
                Expr::Error => Expr::Error,
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
                Expr::Record(entries) => Expr::Record(
                    entries
                        .iter()
                        .map(|(k, t)| (k.clone(), walk(j, c, s, t)))
                        .collect(),
                ),
                Expr::Proj(t, k) => Expr::Proj(walk(j, c, s, t), k.clone()),
                Expr::Error => Expr::Error,
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
            Expr::Record(entries) => {
                let mut rcd = Vec::new();
                let mut done = false;
                for (k, t) in entries {
                    if done || t.is_val() {
                        rcd.push((k.clone(), t.clone()));
                    } else {
                        rcd.push((k.clone(), t.eval1()?));
                        done = true;
                    }
                }
                Ok(Node::new(self.span, Expr::Record(rcd)))
            }
            Expr::Proj(t, k) => match t.expr.as_ref() {
                Expr::Record(entries) => {
                    Ok(rcd_find(entries, k).expect("record key not found").clone())
                }
                _ => panic!("not a record"),
            },
            Expr::Error => Err(eval_error("`error` is evaluated")),
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
                    Ty::Arrow(arg, ret) => ty2.subtype(&arg).map(|_| *ret),
                    Ty::Bot => Ok(Ty::Bot),
                    _ => Err(type_error(
                        t1.span,
                        &format!("cannot apply non-abstract value of type {}", ty1),
                    )),
                }
            }
            Expr::Record(entries) => {
                let mut rcd = Vec::new();
                for (key, node) in entries {
                    let node_ty = node.ty(ctx)?;
                    rcd.push((key.clone(), node_ty));
                }
                Ok(Ty::Record(rcd))
            }
            Expr::Proj(node, key) => {
                let ty = node.ty(ctx)?;
                match &ty {
                    Ty::Record(entries) => rcd_find(entries, key).cloned().ok_or_else(|| {
                        type_error(
                            self.span,
                            &format!("key \"{}\" not found in the record of type {}", key, ty),
                        )
                    }),
                    Ty::Bot => Ok(Ty::Bot),
                    _ => Err(type_error(
                        node.span,
                        &format!("cannot project non-record term of type {}", ty),
                    )),
                }
            }
            Expr::Error => Ok(Ty::Bot),
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
                    Expr::Abs(_, _, _) => format!("({})", t1.show(ctx)),
                    _ => t1.show(ctx),
                };
                match t2.expr.as_ref() {
                    Expr::Abs(_, _, _) | Expr::App(_, _) => {
                        format!("{} ({})", t1_show, t2.show(ctx))
                    }
                    _ => format!("{} {}", t1_show, t2.show(ctx)),
                }
            }
            Expr::Record(entries) => {
                let reprs = entries
                    .iter()
                    .map(|(key, node)| format!("{}={}", key, node.show(ctx)))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{{}}}", reprs)
            }
            Expr::Proj(node, key) => format!("{}.{}", node.show(ctx), key),
            Expr::Error => "error".to_string(),
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
            TokenKind::BraceL
                | TokenKind::Error
                | TokenKind::Lambda
                | TokenKind::ParenL
                | TokenKind::Ident
        ) {
            let rhs = self.arg()?;
            lhs = Node::new(None, Expr::App(lhs, rhs));
        }
        Ok(lhs)
    }

    fn arg(&mut self) -> Result<Node> {
        let mut node = match self.src.next() {
            Some(Ok(token)) => match token.kind {
                TokenKind::ParenL => {
                    let expr = self.expr()?;
                    self.eat(TokenKind::ParenR)?;
                    expr
                }
                TokenKind::BraceL => {
                    let mut rcd = Vec::new();
                    let span = loop {
                        if let Some(r_tok) = self.try_eat(TokenKind::BraceR) {
                            break Span::cover(token.span, r_tok.span);
                        }
                        if !rcd.is_empty() {
                            self.eat(TokenKind::Comma)?;
                        }
                        let name_tok = self.eat(TokenKind::Ident)?;
                        self.eat(TokenKind::Equal)?;
                        let expr = self.expr()?;
                        rcd.push((self.text_of(&name_tok), expr));
                    };
                    Node::at(span, Expr::Record(rcd))
                }
                TokenKind::Lambda => {
                    let name = self.eat(TokenKind::Ident)?;
                    self.eat(TokenKind::Colon)?;

                    let ty = self.ty()?;
                    self.ctx.push(name.span, ty.clone());

                    let dot = self.eat(TokenKind::Dot)?;
                    let span = Span::cover(token.span, dot.span);
                    let expr = self.expr()?;
                    self.ctx.pop();
                    Node::at(span, Expr::Abs(name.span, ty, expr))
                }
                TokenKind::Ident => match self.ctx.rfind(token.span) {
                    Some(index) => Node::at(token.span, Expr::Var(index)),
                    None => return Err(syntax_error(token.span, "undefined variable")),
                },
                TokenKind::Error => Node::at(token.span, Expr::Error),
                _ => return Err(self.invalid_token(token)),
            },
            Some(Err(e)) => return Err(e),
            None => return Err(self.unexpected_eof()),
        };
        while self.try_eat(TokenKind::Dot).is_some() {
            let ident = self.eat(TokenKind::Ident)?;
            let key = self.ctx.text_at(ident.span).to_string();
            node = Node::at(ident.span, Expr::Proj(node, key));
        }
        Ok(node)
    }

    fn ty(&mut self) -> Result<Ty> {
        let lhs = match self.src.next() {
            Some(Ok(token)) => match token.kind {
                TokenKind::ParenL => {
                    let ty = self.ty()?;
                    self.eat(TokenKind::ParenR)?;
                    ty
                }
                TokenKind::BraceL => {
                    let mut rcd = Vec::new();
                    while self.try_eat(TokenKind::BraceR).is_none() {
                        if !rcd.is_empty() {
                            self.eat(TokenKind::Comma)?;
                        }
                        let name_tok = self.eat(TokenKind::Ident)?;
                        self.eat(TokenKind::Colon)?;
                        let ty = self.ty()?;
                        rcd.push((self.text_of(&name_tok), ty));
                    }
                    Ty::Record(rcd)
                }
                TokenKind::Bot => Ty::Bot,
                TokenKind::Top => Ty::Top,
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

    fn try_eat(&mut self, expect: TokenKind) -> Option<Token> {
        match self.src.peek() {
            Some(Ok(token)) if token.kind == expect => Some(self.src.next().unwrap().unwrap()),
            _ => None,
        }
    }

    fn text_of(&self, token: &Token) -> String {
        self.ctx.text_at(token.span).to_string()
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
