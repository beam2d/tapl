use std::cmp;
use std::env;
use std::fmt;
use std::ops::Range;
use std::result;

#[macro_export]
macro_rules! hash_map {
    ($($key:expr => $val:expr),* $(,)?) => {
        [ $(($key, $val),)* ].iter().cloned().collect::<HashMap<_, _>>();
    };
}

/// Unwraps the result or exist process.
pub fn unwrap_or_die<T, E: fmt::Display>(r: result::Result<T, E>) -> T {
    match r {
        Ok(v) => v,
        Err(e) => {
            println!("{}", e);
            panic!()
        }
    }
}

/// Span in the source file used in build error information.
#[derive(Clone, Copy, Debug)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    /// Creates a span from a range.
    pub fn new(range: Range<usize>) -> Span {
        Span {
            start: range.start,
            end: range.end,
        }
    }

    /// Creates a span covering two spans.
    pub fn cover(left: Span, right: Span) -> Span {
        let start = cmp::min(left.start, right.start);
        let end = cmp::max(left.end, right.end);
        Span { start, end }
    }

    /// Converts to `Range`.
    pub fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Error value.
#[derive(Debug)]
pub struct Error {
    name: &'static str,
    summary: String,
    note: String,
    span: Option<Span>,
}

impl Error {
    /// Creates a new error.
    pub fn new(name: &'static str) -> Error {
        if let Ok(_) = env::var("RUST_BACKTRACE") {
            panic!(name);
        }
        Error {
            name,
            summary: String::new(),
            note: String::new(),
            span: None,
        }
    }

    /// Attaches a span.
    pub fn at(mut self, span: Span) -> Error {
        self.span = Some(span);
        self
    }

    /// Attaches a summary text.
    pub fn summary(mut self, summary: impl Into<String>) -> Error {
        self.summary = summary.into();
        self
    }

    /// Attaches a text that compares expected and actual types/values.
    pub fn expect_actual(mut self, expect: &str, actual: &str) -> Error {
        self.note
            .push_str(&format!("\texpect: {}\n\tactual: {}\n", expect, actual));
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name)?;
        if let Some(span) = self.span {
            write!(f, " at ({:?})", span.range())?;
        }
        write!(f, ": {}\n", self.summary)?;
        if !self.note.is_empty() {
            f.write_str(&self.note)?;
        }
        Ok(())
    }
}

pub type Result<T> = result::Result<T, Error>;
