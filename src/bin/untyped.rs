//! Untyped lambda calculus.
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

use tapl::{matches, Error, Result, Span};

fn syntax_error(at: Span, summary: &str) -> Error {
    Error::new("SyntaxError").at(at).summary(summary)
}

fn eval_error(summary: &str) -> Error {
    Error::new("EvalError").summary(summary)
}

#[derive(Clone, Copy, PartialEq)]
enum TokenKind {
    Dot,
    Lambda,
    ParenL,
    ParenR,
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
}

impl<'tx> TokenStream<'tx> {
    fn new(text: &'tx str) -> Self {
        TokenStream {
            text,
            src: text.char_indices().peekable(),
        }
    }

    fn next_token(&mut self) -> Result<Option<Token>> {
        while let Some((start, ch)) = self.src.next() {
            let kind = match ch {
                ' ' | '\n' => continue,
                '.' => TokenKind::Dot,
                '\\' => TokenKind::Lambda,
                '(' => TokenKind::ParenL,
                ')' => TokenKind::ParenR,
                'a'..='z' | '_' => {
                    let cond = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '\'';
                    while matches!(self.src.peek(), Some((_, ch)) if cond(*ch)) {
                        self.src.next();
                    }
                    TokenKind::Ident
                }
                _ => return Err(syntax_error(self.span(start), "invalid character")),
            };
            let span = self.span(start);
            return Ok(Some(Token { kind, span }));
        }
        Ok(None)
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

/// Symbol environment.
struct Context<'tx> {
    text: &'tx str,
    stack: Vec<String>,
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

    /// Variable name for the given de Brujin index.
    fn name(&self, index: i64) -> &str {
        &self.stack[self.stack.len() - (index as usize) - 1]
    }

    /// de Brujin index of the given name.
    fn rfind(&self, name: Span) -> Option<i64> {
        match self.map.get(self.text_at(name)) {
            Some(v) => v.last().map(|i| (self.stack.len() - *i - 1) as i64),
            _ => None,
        }
    }

    /// Pushes a variable name to the context. Returns the name for display.
    fn push(&mut self, name: Span) -> &str {
        let n_ticks = {
            let name_s = self.text_at(name).to_string();
            let v = self.map.entry(name_s).or_insert(Vec::new());
            v.push(self.stack.len());
            v.len() - 1
        };
        self.stack
            .push(format!("{}{:'<w$}", self.text_at(name), "", w = n_ticks));
        &self.stack.last().unwrap()
    }

    /// Pops the variable name for the inner most abstraction term.
    fn pop(&mut self) {
        let display_name = self.stack.pop().expect("popped from empty context");
        let name = match display_name.find('\'') {
            Some(i) => &display_name[..i],
            None => &display_name[..],
        };
        self.map.get_mut(name).unwrap().pop();
    }
}

/// Structure of abstract syntax tree.
#[derive(Clone)]
enum Expr {
    Var(i64),
    Abs(Span, Node),
    App(Node, Node),
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
        matches!(self.expr.as_ref(), Expr::Abs(_, _))
    }

    /// Shifts de Brujin indices.
    fn shift(&self, d: i64) -> Node {
        fn walk(c: i64, d: i64, t: &Node) -> Node {
            let expr = match t.expr.as_ref() {
                Expr::Var(x) => Expr::Var(if *x >= c { x + d } else { *x }),
                Expr::Abs(name, body) => Expr::Abs(*name, walk(c + 1, d, body)),
                Expr::App(t1, t2) => Expr::App(walk(c, d, t1), walk(c, d, t2)),
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
                Expr::Abs(name, body) => Expr::Abs(*name, walk(j, c + 1, s, body)),
                Expr::App(t1, t2) => Expr::App(walk(j, c, s, t1), walk(j, c, s, t2)),
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
                Expr::Abs(_, t12) if t2.is_val() => Ok(t12.subst(0, &t2.shift(1)).shift(-1)),
                // E-App2
                Expr::Abs(_, _) => Ok(Node::new(self.span, Expr::App(t1.clone(), t2.eval1()?))),
                // E-App1
                _ => Ok(Node::new(self.span, Expr::App(t1.eval1()?, t2.clone()))),
            },
            _ => Err(eval_error("no rule applied")),
        }
    }

    /// Pretty prints the AST.
    fn show(&self, ctx: &mut Context) -> String {
        match self.expr.as_ref() {
            Expr::Var(x) => ctx.name(*x).to_string(),
            Expr::Abs(name, e) => {
                let name_show = ctx.push(*name).to_owned();
                let e_show = e.show(ctx);
                ctx.pop();
                format!("\\{}. {}", name_show, e_show)
            }
            Expr::App(t1, t2) => {
                let t1_show = match t1.expr.as_ref() {
                    Expr::Abs(_, _) => format!("({})", t1.show(ctx)),
                    _ => t1.show(ctx),
                };
                match t2.expr.as_ref() {
                    Expr::Var(_) => format!("{} {}", t1_show, t2.show(ctx)),
                    _ => format!("{} ({})", t1_show, t2.show(ctx)),
                }
            }
        }
    }
}

impl fmt::Display for Node {
    /// Shows the AST as a nameless term.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr.as_ref() {
            Expr::Var(x) => write!(f, "{}", x),
            Expr::Abs(_, e) => write!(f, "\\. {}", e),
            Expr::App(t1, t2) => {
                match t1.expr.as_ref() {
                    Expr::Abs(_, _) => write!(f, "({}) ", t1)?,
                    _ => write!(f, "{} ", t1)?,
                }
                match t2.expr.as_ref() {
                    Expr::Var(_) => write!(f, "{}", t2),
                    _ => write!(f, "({})", t2),
                }
            }
        }
    }
}

/// Syntaxtic parser.
struct Parser<'tx> {
    ctx: Context<'tx>,
    src: Peekable<TokenStream<'tx>>,
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
        let mut lhs = self.atom()?;
        while let Some(Ok(token)) = self.src.peek() {
            match token.kind {
                TokenKind::ParenL | TokenKind::Lambda | TokenKind::Ident => {
                    let rhs = self.atom()?;
                    lhs = Node::new(None, Expr::App(lhs, rhs));
                }
                _ => break,
            }
        }
        Ok(lhs)
    }

    fn atom(&mut self) -> Result<Node> {
        match self.src.next() {
            Some(Ok(token)) => match token.kind {
                TokenKind::ParenL => {
                    let expr = self.expr()?;
                    self.eat(TokenKind::ParenR)?;
                    Ok(expr)
                }
                TokenKind::Lambda => {
                    let name = self.eat(TokenKind::Ident)?;
                    self.ctx.push(name.span);
                    let dot = self.eat(TokenKind::Dot)?;
                    let expr = self.expr()?;
                    self.ctx.pop();
                    Ok(Node::at(
                        Span::cover(token.span, dot.span),
                        Expr::Abs(name.span, expr),
                    ))
                }
                TokenKind::Ident => match self.ctx.rfind(token.span) {
                    Some(index) => Ok(Node::at(token.span, Expr::Var(index))),
                    None => Err(syntax_error(token.span, "undefined variable")),
                },
                _ => Err(self.invalid_token(token)),
            },
            Some(Err(e)) => Err(e),
            None => Err(self.unexpected_eof()),
        }
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
    println!("{}", node.show(&mut Context::new(&text)));
    while !node.is_val() {
        node = tapl::unwrap_or_die(node.eval1());
        println!("=> {}", node.show(&mut Context::new(&text)));
    }
}
