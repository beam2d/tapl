use std::fmt;
use std::ops::Range;
use std::process;
use std::result;

#[macro_export]
macro_rules! hash_map {
    ($($key:expr => $val:expr),* $(,)?) => {
        [ $(($key, $val),)* ].iter().cloned().collect::<HashMap<_, _>>();
    };
}

#[macro_export]
macro_rules! matches {
    ($expr:expr, $($pat:pat)|+ $(if $guard:expr)?) => {
        match $expr {
            $($pat)|+ $(if $guard)? => true,
            _ => false,
        }
    };
}

/// Unwraps the result or exist process.
pub fn unwrap_or_die<T, E: fmt::Display>(r: result::Result<T, E>) -> T {
    match r {
        Ok(v) => v,
        Err(e) => {
            println!("{}", e);
            process::exit(1);
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
    pub fn new(range: Range<usize>) -> Span {
        Span {
            start: range.start,
            end: range.end,
        }
    }

    pub fn range(self) -> Range<usize> {
        self.start..self.end
    }
}

/// Error value.
#[derive(Debug)]
pub struct Error {
    name: &'static str,
    summary: String,
    span: Option<Span>,
}

impl Error {
    /// Creates a new error.
    pub fn new(name: &'static str) -> Error {
        Error {
            name,
            summary: String::new(),
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
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.name)?;
        if let Some(span) = self.span {
            write!(f, " at ({:?})", span.range())?;
        }
        write!(f, ": {}\n", self.summary)
    }
}

pub type Result<T> = result::Result<T, Error>;
