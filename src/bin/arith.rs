use std::collections::HashMap;
use std::env;
use std::fmt;
use std::fs::File;
use std::io::{prelude::*, BufReader};
use std::iter::Peekable;
use std::str::CharIndices;

use tapl::{hash_map, matches, Error, Result, Span};

fn syntax_error(at: Span, summary: &str) -> Error {
    Error::new("SyntaxError").at(at).summary(summary)
}

fn eval_error(summary: &str) -> Error {
    Error::new("EvalError").summary(summary)
}

#[derive(Clone, Copy, PartialEq)]
enum TokenKind {
    Else,
    False,
    If,
    Iszero,
    Pred,
    Then,
    True,
    Succ,
    Zero,
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
    kwmap: HashMap<&'static str, TokenKind>,
}

impl<'tx> TokenStream<'tx> {
    fn new(text: &'tx str) -> Self {
        let kwmap = hash_map! {
            "else" => TokenKind::Else,
            "false" => TokenKind::False,
            "if" => TokenKind::If,
            "iszero" => TokenKind::Iszero,
            "pred" => TokenKind::Pred,
            "then" => TokenKind::Then,
            "true" => TokenKind::True,
            "succ" => TokenKind::Succ,
        };
        TokenStream {
            text,
            src: text.char_indices().peekable(),
            kwmap,
        }
    }

    fn next_token(&mut self) -> Result<Option<Token>> {
        while let Some((start, ch)) = self.src.next() {
            let kind = match ch {
                ' ' | '\n' => continue,
                '0' => TokenKind::Zero,
                'a'..='z' => self.parse_keyword(start)?,
                _ => return Err(syntax_error(self.span(start), "invalid character")),
            };
            let span = self.span(start);
            return Ok(Some(Token { kind, span }));
        }
        Ok(None)
    }

    fn parse_keyword(&mut self, start: usize) -> Result<TokenKind> {
        while matches!(self.src.peek(), Some((_, ch)) if ch.is_ascii_alphanumeric()) {
            self.src.next();
        }
        let span = self.span(start);
        match self.kwmap.get(&self.text[span.range()]) {
            Some(kind) => Ok(*kind),
            None => Err(syntax_error(span, "invalid keyword")),
        }
    }

    fn span(&mut self, start: usize) -> Span {
        let end = match self.src.peek() {
            Some((i, _)) => *i,
            None => self.text.len(),
        };
        Span::new(start..end)
    }
}

/// Structure of abstract syntax tree.
#[derive(Clone)]
enum Expr {
    False,
    If(Node, Node, Node),
    Iszero(Node),
    Pred(Node),
    Succ(Node),
    True,
    Zero,
}

impl Into<Node> for Expr {
    fn into(self) -> Node {
        Node::from_expr(self)
    }
}

/// Node of the abstract syntax tree.
#[derive(Clone)]
struct Node {
    span: Option<Span>,
    expr: Box<Expr>,
}

impl Node {
    /// Creates a new AST node.
    fn new(span: Option<Span>, expr: Expr) -> Node {
        Node {
            span,
            expr: Box::new(expr),
        }
    }

    /// Creates a node without span information.
    fn from_expr(expr: Expr) -> Node {
        Node::new(None, expr)
    }

    /// Creates a node with span information.
    fn at(span: Span, expr: Expr) -> Node {
        Node::new(Some(span), expr)
    }

    /// Examines if the node represents a numeric value.
    fn is_nv(&self) -> bool {
        match self.expr.as_ref() {
            Expr::Succ(node) => node.is_nv(),
            Expr::Zero => true,
            _ => false,
        }
    }

    /// Examines if the node represents a value.
    fn is_val(&self) -> bool {
        self.is_nv() || tapl::matches!(self.expr.as_ref(), Expr::False | Expr::True)
    }

    /// Single step evaluation of the node.
    fn eval1(&self) -> Result<Node> {
        Ok(match self.expr.as_ref() {
            Expr::If(cond, then, els) => match cond.expr.as_ref() {
                // E-IfTrue
                Expr::True => then.clone(),
                // E-IfFalse
                Expr::False => els.clone(),
                // E-If
                _ => Expr::If(cond.eval1()?, then.clone(), els.clone()).into(),
            },
            // E-Succ
            Expr::Succ(arg) => Expr::Succ(arg.eval1()?).into(),
            Expr::Pred(arg) => match arg.expr.as_ref() {
                // E-PredZero
                Expr::Zero => Expr::Zero.into(),
                // E-PredSucc
                Expr::Succ(nv) if nv.is_nv() => nv.clone(),
                // E-Pred
                _ => Expr::Pred(arg.eval1()?).into(),
            },
            Expr::Iszero(arg) => match arg.expr.as_ref() {
                // E-IszeroZero
                Expr::Zero => Expr::True.into(),
                // E-IszeroSucc
                Expr::Succ(nv) if nv.is_nv() => Expr::False.into(),
                // E-Iszero
                _ => Expr::Iszero(arg.eval1()?).into(),
            },
            _ => return Err(eval_error(&format!("normal form: {}", self))),
        })
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.expr.as_ref() {
            Expr::False => write!(f, "false"),
            Expr::If(cond, then, els) => write!(f, "if {} then {} else {}", cond, then, els),
            Expr::Iszero(arg) => write!(f, "iszero {}", arg),
            Expr::Pred(arg) => write!(f, "pred {}", arg),
            Expr::Succ(arg) => write!(f, "succ {}", arg),
            Expr::True => write!(f, "true"),
            Expr::Zero => write!(f, "0"),
        }
    }
}

/// Syntaxtic parser.
struct Parser<'tx> {
    text: &'tx str,
    src: TokenStream<'tx>,
}

impl<'tx> Parser<'tx> {
    /// Parses the text.
    fn parse(text: &'tx str) -> Result<Node> {
        let mut parser = Parser {
            text,
            src: TokenStream::new(text),
        };
        let expr = parser.expr()?;
        match parser.src.next_token()? {
            Some(token) => Err(parser.invalid_token(token)),
            None => Ok(expr),
        }
    }

    fn expr(&mut self) -> Result<Node> {
        if let Some(token) = self.src.next_token()? {
            match token.kind {
                TokenKind::False => Ok(Node::at(token.span, Expr::False)),
                TokenKind::If => self.if_expr(token),
                TokenKind::Iszero => Ok(Node::at(token.span, Expr::Iszero(self.expr()?))),
                TokenKind::Pred => Ok(Node::at(token.span, Expr::Pred(self.expr()?))),
                TokenKind::Succ => Ok(Node::at(token.span, Expr::Succ(self.expr()?))),
                TokenKind::True => Ok(Node::at(token.span, Expr::True)),
                TokenKind::Zero => Ok(Node::at(token.span, Expr::Zero)),
                _ => Err(self.invalid_token(token)),
            }
        } else {
            Err(syntax_error(self.eof(), "unexpected EOF"))
        }
    }

    fn if_expr(&mut self, if_tok: Token) -> Result<Node> {
        let cond = self.expr()?;
        self.eat(TokenKind::Then)?;
        let then = self.expr()?;
        self.eat(TokenKind::Else)?;
        let els = self.expr()?;
        Ok(Node::at(if_tok.span, Expr::If(cond, then, els)))
    }

    fn eat(&mut self, expect: TokenKind) -> Result<Token> {
        match self.src.next_token()? {
            Some(token) if token.kind == expect => Ok(token),
            Some(token) => Err(self.invalid_token(token)),
            None => Err(self.unexpected_eof()),
        }
    }

    fn eof(&mut self) -> Span {
        let len = self.text.len();
        Span::new(len..len)
    }

    fn invalid_token(&mut self, token: Token) -> Error {
        syntax_error(token.span, "invalid token")
    }

    fn unexpected_eof(&mut self) -> Error {
        syntax_error(self.eof(), "unexpected EOF")
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
    println!("{}", node);
    while !node.is_val() {
        node = tapl::unwrap_or_die(node.eval1());
        println!("=> {}", node);
    }
}
