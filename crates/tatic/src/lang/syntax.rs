//! A real, parseable surface syntax for the term language `term.rs`
//! defines structurally -- until now, every term in this project (demos,
//! tests, benchmarks) was hand-built through `TermStore`'s De Bruijn-index
//! builders (`s.var(0)`, `s.abs(..)`, ...), which is exact but unreadable
//! and error-prone to write by hand. This module is a small recursive-
//! descent parser from ordinary named-variable source text straight into
//! `TermStore` terms -- no separate AST: each grammar production interns
//! directly via `TermStore`'s own builders, and named-variable resolution
//! happens through an ordinary lexical scope stack, translating names to
//! De Bruijn indices as it goes (the same translation a human does by hand
//! today, just automated and checked).
//!
//! ## Grammar (low to high precedence)
//!
//! ```text
//! expr    := "let" IDENT "=" expr "in" expr
//!          | "\" IDENT+ "." expr
//!          | "rec" IDENT IDENT* "=" expr
//!          | "if" expr "then" expr "else" expr
//!          | or
//! or      := and ("||" and)*
//! and     := cmp ("&&" cmp)*
//! cmp     := add (("<" | "<=" | "==" | ">" | ">=" | "!=") add)?
//! add     := mul (("+" | "-") mul)*
//! mul     := unary (("*" | "/" | "%") unary)*
//! unary   := ("-" | "!") unary | app
//! app     := atom+                      -- left-associative juxtaposition
//! atom    := INT | IDENT | "(" expr ")"
//! ```
//!
//! `>`/`>=`/`!=`/`&&`/`||`/`!` are all pure sugar, desugaring at parse time
//! into the existing `Lt`/`Le`/`Eq` primitives and `If` -- no new `PrimOp`
//! is needed for any of them (see each production's own implementation for
//! the exact desugaring and why it stays correct for *any* truthy operand,
//! not just a clean `0`/`1` one). `&&`/`||` genuinely short-circuit (the
//! right operand sits inside an `If` branch, so it's never evaluated when
//! the left operand alone already determines the result), matching every
//! other language's own convention for these operators.
//!
//! Unary minus on an integer literal is itself a (negative) literal --
//! `-5` parses to `Lit(-5)`, not `0 - 5` -- the way OCaml's parser folds
//! it, so every `Lit` has an exact spelling (`-9223372036854775808`
//! included). On anything else, `-e` desugars to `0 - e`. Juxtaposition
//! still binds tighter than unary minus, so a negative argument needs
//! parentheses: `f (-2)`, since `f -2` is the subtraction `f - 2`.
//!
//! `let`/`\`/`rec`/`if` all extend as far right as possible, so (as in most
//! ML-family languages) they need explicit parentheses when used as a
//! function argument or an operand of an arithmetic/comparison operator --
//! `f (\x. x) (if c then 1 else 2)`, not `f \x. x if c then 1 else 2`.
//!
//! `let x = e1 in e2` is pure sugar, desugaring to `(\x. e2) e1` (an
//! ordinary, non-recursive application) -- the term language has no
//! separate `let` primitive, and doesn't need one. A named *recursive*
//! top-level function reads naturally as one `let` binding a `rec` value:
//! `let fact = rec f n = if n <= 1 then 1 else n * f (n - 1) in fact 10`.
//!
//! Multi-parameter `\x y. body` and `rec f x y. body` are sugar for nested
//! single-parameter `Abs`/`Rec(Abs(Abs(..)))` chains, exactly matching this
//! project's existing De Bruijn convention throughout (`Var(0)` = the
//! *last*-declared parameter, i.e. the innermost binder -- see `proof.rs`'s
//! module docs for where else this convention matters): parameters are
//! pushed onto the scope stack in declaration order, so the last one
//! declared is the last one pushed, and therefore resolves to `Var(0)`.

use crate::lang::term::{Hash, PrimOp, Term, TermStore};

#[derive(Debug, Clone, PartialEq)]
enum Token {
    /// Unsigned: `9223372036854775808` is only in range as the operand of
    /// a unary minus (`i64::MIN`), which `parse_unary` checks.
    Int(u64),
    Ident(String),
    Lambda,
    Dot,
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Lt,
    Le,
    Gt,
    Ge,
    EqEq,
    Ne,
    Bang,
    AmpAmp,
    PipePipe,
    Eq,
    If,
    Then,
    Else,
    Rec,
    Let,
    In,
    Eof,
}

/// A parse (or lex) failure, with the byte offset into the source it was
/// found at.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub pos: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (at byte {})", self.message, self.pos)
    }
}

impl std::error::Error for ParseError {}

fn lex(src: &str) -> Result<Vec<(Token, usize)>, ParseError> {
    let bytes = src.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let c = bytes[i] as char;
        match c {
            ' ' | '\t' | '\n' | '\r' => i += 1,
            '\\' => {
                tokens.push((Token::Lambda, i));
                i += 1;
            }
            '.' => {
                tokens.push((Token::Dot, i));
                i += 1;
            }
            '(' => {
                tokens.push((Token::LParen, i));
                i += 1;
            }
            ')' => {
                tokens.push((Token::RParen, i));
                i += 1;
            }
            '+' => {
                tokens.push((Token::Plus, i));
                i += 1;
            }
            '-' => {
                tokens.push((Token::Minus, i));
                i += 1;
            }
            '*' => {
                tokens.push((Token::Star, i));
                i += 1;
            }
            '/' => {
                tokens.push((Token::Slash, i));
                i += 1;
            }
            '%' => {
                tokens.push((Token::Percent, i));
                i += 1;
            }
            '<' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    tokens.push((Token::Le, i));
                    i += 2;
                } else {
                    tokens.push((Token::Lt, i));
                    i += 1;
                }
            }
            '=' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    tokens.push((Token::EqEq, i));
                    i += 2;
                } else {
                    tokens.push((Token::Eq, i));
                    i += 1;
                }
            }
            '>' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    tokens.push((Token::Ge, i));
                    i += 2;
                } else {
                    tokens.push((Token::Gt, i));
                    i += 1;
                }
            }
            '!' => {
                if bytes.get(i + 1) == Some(&b'=') {
                    tokens.push((Token::Ne, i));
                    i += 2;
                } else {
                    tokens.push((Token::Bang, i));
                    i += 1;
                }
            }
            '&' => {
                if bytes.get(i + 1) == Some(&b'&') {
                    tokens.push((Token::AmpAmp, i));
                    i += 2;
                } else {
                    return Err(ParseError { message: "expected `&&`, found a single `&` (no bitwise operators)".to_string(), pos: i });
                }
            }
            '|' => {
                if bytes.get(i + 1) == Some(&b'|') {
                    tokens.push((Token::PipePipe, i));
                    i += 2;
                } else {
                    return Err(ParseError { message: "expected `||`, found a single `|` (no bitwise operators)".to_string(), pos: i });
                }
            }
            '0'..='9' => {
                let start = i;
                while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                    i += 1;
                }
                let text = &src[start..i];
                let n: u64 = text
                    .parse()
                    .map_err(|_| ParseError { message: format!("invalid integer literal `{text}`"), pos: start })?;
                tokens.push((Token::Int(n), start));
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < bytes.len() && ((bytes[i] as char).is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let text = &src[start..i];
                let tok = match text {
                    "if" => Token::If,
                    "then" => Token::Then,
                    "else" => Token::Else,
                    "rec" => Token::Rec,
                    "let" => Token::Let,
                    "in" => Token::In,
                    _ => Token::Ident(text.to_string()),
                };
                tokens.push((tok, start));
            }
            other => return Err(ParseError { message: format!("unexpected character `{other}`"), pos: i }),
        }
    }
    tokens.push((Token::Eof, bytes.len()));
    Ok(tokens)
}

struct Parser<'a> {
    store: &'a mut TermStore,
    tokens: Vec<(Token, usize)>,
    pos: usize,
    /// Names currently in scope, in binding order -- the *last* entry is
    /// the innermost binder, `Var(0)` (see the module docs).
    scope: Vec<String>,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> &Token {
        &self.tokens[self.pos].0
    }

    fn peek_pos(&self) -> usize {
        self.tokens[self.pos].1
    }

    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.pos].0.clone();
        if self.pos + 1 < self.tokens.len() {
            self.pos += 1;
        }
        tok
    }

    fn error(&self, message: impl Into<String>) -> ParseError {
        ParseError { message: message.into(), pos: self.peek_pos() }
    }

    fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
        if *self.peek() == expected {
            self.advance();
            Ok(())
        } else {
            Err(self.error(format!("expected {expected:?}, found {:?}", self.peek())))
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        let pos = self.peek_pos();
        match self.advance() {
            Token::Ident(name) => Ok(name),
            other => Err(ParseError { message: format!("expected an identifier, found {other:?}"), pos }),
        }
    }

    /// One or more parameter names, stopping at the first non-identifier
    /// (`.` for `\`, `=` for `rec`).
    fn parse_params(&mut self) -> Result<Vec<String>, ParseError> {
        let params = self.parse_ident_list();
        if params.is_empty() {
            return Err(self.error("expected at least one parameter"));
        }
        Ok(params)
    }

    /// Like `parse_params`, but allows zero identifiers -- only `rec` uses
    /// this (`rec f = body`, a zero-arity self-recursive value, is
    /// unusual and out of `compile.rs`'s fragment, but still a legitimate
    /// term this grammar can express; `print`, the reverse direction, can
    /// produce this shape for a `Rec` with no `Abs` layers).
    fn parse_ident_list(&mut self) -> Vec<String> {
        let mut names = Vec::new();
        while let Token::Ident(name) = self.peek() {
            names.push(name.clone());
            self.advance();
        }
        names
    }

    fn resolve_var(&self, name: &str) -> Option<u32> {
        let pos = self.scope.iter().rposition(|s| s == name)?;
        Some((self.scope.len() - 1 - pos) as u32)
    }

    fn starts_atom(&self) -> bool {
        matches!(self.peek(), Token::Int(_) | Token::Ident(_) | Token::LParen)
    }

    fn parse_expr(&mut self) -> Result<Hash, ParseError> {
        match self.peek() {
            Token::Let => self.parse_let(),
            Token::Lambda => self.parse_lambda(),
            Token::Rec => self.parse_rec(),
            Token::If => self.parse_if(),
            _ => self.parse_or(),
        }
    }

    /// `a || b`: sugar, no new `PrimOp` -- `if a == 0 then (if b == 0 then
    /// 0 else 1) else 1`. Genuinely short-circuits (`b` sits inside an
    /// `If` branch, never evaluated when `a` alone already determines the
    /// result), and correct for *any* truthy operand under this language's
    /// own "nonzero is true" convention, not just a clean `0`/`1` one,
    /// since both operands are only ever compared against `0` via `Eq`.
    fn parse_or(&mut self) -> Result<Hash, ParseError> {
        let mut lhs = self.parse_and()?;
        while matches!(self.peek(), Token::PipePipe) {
            self.advance();
            let rhs = self.parse_and()?;
            let zero = self.store.lit(0);
            let one = self.store.lit(1);
            let lhs_is_zero = self.store.prim(PrimOp::Eq, lhs, zero);
            let rhs_is_zero = self.store.prim(PrimOp::Eq, rhs, zero);
            let inner = self.store.if_(rhs_is_zero, zero, one);
            lhs = self.store.if_(lhs_is_zero, inner, one);
        }
        Ok(lhs)
    }

    /// `a && b`: sugar, no new `PrimOp` -- `if a == 0 then 0 else (if b ==
    /// 0 then 0 else 1)`. Same short-circuiting and any-truthy-operand
    /// correctness as `parse_or`'s own `||`.
    fn parse_and(&mut self) -> Result<Hash, ParseError> {
        let mut lhs = self.parse_cmp()?;
        while matches!(self.peek(), Token::AmpAmp) {
            self.advance();
            let rhs = self.parse_cmp()?;
            let zero = self.store.lit(0);
            let one = self.store.lit(1);
            let lhs_is_zero = self.store.prim(PrimOp::Eq, lhs, zero);
            let rhs_is_zero = self.store.prim(PrimOp::Eq, rhs, zero);
            let inner = self.store.if_(rhs_is_zero, zero, one);
            lhs = self.store.if_(lhs_is_zero, zero, inner);
        }
        Ok(lhs)
    }

    fn parse_let(&mut self) -> Result<Hash, ParseError> {
        self.expect(Token::Let)?;
        let name = self.expect_ident()?;
        self.expect(Token::Eq)?;
        let value = self.parse_expr()?; // `name` is not yet in scope for its own definition
        self.expect(Token::In)?;
        self.scope.push(name);
        let body = self.parse_expr()?;
        self.scope.pop();
        let lam = self.store.abs(body);
        Ok(self.store.app(lam, value))
    }

    fn parse_lambda(&mut self) -> Result<Hash, ParseError> {
        self.expect(Token::Lambda)?;
        let params = self.parse_params()?;
        self.expect(Token::Dot)?;
        for p in &params {
            self.scope.push(p.clone());
        }
        let body = self.parse_expr()?;
        self.scope.truncate(self.scope.len() - params.len());
        let mut h = body;
        for _ in &params {
            h = self.store.abs(h);
        }
        Ok(h)
    }

    fn parse_rec(&mut self) -> Result<Hash, ParseError> {
        self.expect(Token::Rec)?;
        let self_name = self.expect_ident()?;
        let params = self.parse_ident_list();
        self.expect(Token::Eq)?;
        self.scope.push(self_name);
        for p in &params {
            self.scope.push(p.clone());
        }
        let body = self.parse_expr()?;
        self.scope.truncate(self.scope.len() - params.len() - 1);
        let mut h = body;
        for _ in &params {
            h = self.store.abs(h);
        }
        Ok(self.store.rec(h))
    }

    fn parse_if(&mut self) -> Result<Hash, ParseError> {
        self.expect(Token::If)?;
        let c = self.parse_expr()?;
        self.expect(Token::Then)?;
        let t = self.parse_expr()?;
        self.expect(Token::Else)?;
        let e = self.parse_expr()?;
        Ok(self.store.if_(c, t, e))
    }

    fn parse_cmp(&mut self) -> Result<Hash, ParseError> {
        let lhs = self.parse_add()?;
        match self.peek() {
            Token::Lt => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(PrimOp::Lt, lhs, rhs))
            }
            Token::Le => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(PrimOp::Le, lhs, rhs))
            }
            Token::EqEq => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(PrimOp::Eq, lhs, rhs))
            }
            // `a > b`: sugar, no new `PrimOp` -- desugars to `b < a`.
            Token::Gt => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(PrimOp::Lt, rhs, lhs))
            }
            // `a >= b`: sugar, no new `PrimOp` -- desugars to `b <= a`.
            Token::Ge => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(PrimOp::Le, rhs, lhs))
            }
            // `a != b`: sugar, no new `PrimOp` -- `1 - (a == b)`. `Eq`
            // already yields a clean `0`/`1`, so this is exact, not just
            // truthy.
            Token::Ne => {
                self.advance();
                let rhs = self.parse_add()?;
                let eq = self.store.prim(PrimOp::Eq, lhs, rhs);
                let one = self.store.lit(1);
                Ok(self.store.prim(PrimOp::Sub, one, eq))
            }
            _ => Ok(lhs),
        }
    }

    fn parse_add(&mut self) -> Result<Hash, ParseError> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Token::Plus => PrimOp::Add,
                Token::Minus => PrimOp::Sub,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_mul()?;
            lhs = self.store.prim(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> Result<Hash, ParseError> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Token::Star => PrimOp::Mul,
                Token::Slash => PrimOp::Div,
                Token::Percent => PrimOp::Mod,
                _ => break,
            };
            self.advance();
            let rhs = self.parse_unary()?;
            lhs = self.store.prim(op, lhs, rhs);
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> Result<Hash, ParseError> {
        match self.peek() {
            // `-e`: `0 - e`, except that a literal operand folds into a
            // negative `Lit` (as OCaml's parser does), so `print`'s `-5`
            // reads back as exactly `Lit(-5)`. `wrapping_neg` matches
            // `0 - n`'s own wrapping `Sub`, so folding never changes a value.
            Token::Minus => {
                let pos = self.peek_pos();
                self.advance();
                // `i64::MIN`'s magnitude alone is out of range, so it's
                // only a literal here, never an atom (see `parse_atom`).
                if matches!(self.peek(), Token::Int(n) if *n == i64::MIN.unsigned_abs()) {
                    self.advance();
                    if self.starts_atom() {
                        return Err(ParseError { message: format!("integer literal `{}` out of range", i64::MIN.unsigned_abs()), pos: pos + 1 });
                    }
                    return Ok(self.store.lit(i64::MIN));
                }
                let operand = self.parse_unary()?;
                if let Term::Lit(n) = *self.store.resolve(operand) {
                    return Ok(self.store.lit(n.wrapping_neg()));
                }
                let zero = self.store.lit(0);
                Ok(self.store.prim(PrimOp::Sub, zero, operand))
            }
            // `!a`: sugar, no new `PrimOp` -- `a == 0`. Correct for any
            // truthy operand, not just a clean `0`/`1` one.
            Token::Bang => {
                self.advance();
                let operand = self.parse_unary()?;
                let zero = self.store.lit(0);
                Ok(self.store.prim(PrimOp::Eq, operand, zero))
            }
            _ => self.parse_app(),
        }
    }

    fn parse_app(&mut self) -> Result<Hash, ParseError> {
        let mut h = self.parse_atom()?;
        while self.starts_atom() {
            let arg = self.parse_atom()?;
            h = self.store.app(h, arg);
        }
        Ok(h)
    }

    fn parse_atom(&mut self) -> Result<Hash, ParseError> {
        let pos = self.peek_pos();
        match self.advance() {
            Token::Int(n) => match i64::try_from(n) {
                Ok(n) => Ok(self.store.lit(n)),
                Err(_) => Err(ParseError { message: format!("integer literal `{n}` out of range"), pos }),
            },
            Token::Ident(name) => match self.resolve_var(&name) {
                Some(idx) => Ok(self.store.var(idx)),
                None => Err(ParseError { message: format!("unbound variable `{name}`"), pos }),
            },
            Token::LParen => {
                let e = self.parse_expr()?;
                self.expect(Token::RParen)?;
                Ok(e)
            }
            other => Err(ParseError { message: format!("expected an expression, found {other:?}"), pos }),
        }
    }
}

/// Parses `src` as a closed term, interning it into `store`. Returns a
/// [`ParseError`] for a lex/syntax error, an unbound variable, or trailing
/// input after a complete expression (e.g. a stray `)`).
pub fn parse(store: &mut TermStore, src: &str) -> Result<Hash, ParseError> {
    let tokens = lex(src)?;
    let mut p = Parser { store, tokens, pos: 0, scope: Vec::new() };
    let h = p.parse_expr()?;
    p.expect(Token::Eof)?;
    Ok(h)
}

// --- pretty-printer (the reverse direction) -------------------------------
//
// `print` walks a term and reconstructs source text this module's own
// `parse` accepts, assigning each binder a fresh name (`v0`, `v1`, ... by
// nesting *depth* at the point it's introduced, not a running counter --
// two independent binders at the same depth, e.g. two sibling lambdas,
// safely reuse a name exactly the way ordinary shadowing already allows,
// since neither's body can see the other's parameter). Precedence-aware:
// each node knows its own precedence level and the minimum its parent
// requires, adding parentheses only where the grammar in this module's own
// docs would otherwise parse the text differently (or not at all) --
// e.g. an `Abs`/`If`/`Rec` used as a function argument always needs them
// (juxtaposition has no delimiting keyword to fall back on), but the same
// node as an `If`'s condition/branch never does (`then`/`else` delimit it
// unambiguously, matching `parse_if` calling `parse_expr` for each part).
//
// Round-trips exactly (hash-identical) for every well-scoped term. A
// negative `Lit(n)` prints as `-n`, which `parse_unary` folds straight back
// into `Lit(n)` (including `i64::MIN`, whose magnitude alone is out of
// range). Since `-n` is unary minus rather than an atom, it's printed at
// unary precedence, so it's parenthesised wherever a bare `-n` would parse
// differently (`f (-2)`, not `f -2`, which reads back as the subtraction
// `f - 2`).

fn fresh_name(depth: usize) -> String {
    format!("v{depth}")
}

fn op_symbol(op: PrimOp) -> &'static str {
    use PrimOp::*;
    match op {
        Add => "+",
        Sub => "-",
        Mul => "*",
        Div => "/",
        Mod => "%",
        Lt => "<",
        Le => "<=",
        Eq => "==",
    }
}

/// Precedence level, matching this module's own grammar (higher binds
/// tighter): 0 = `let`/`\`/`rec`/`if` (`let` never appears here -- it's
/// pure sugar with no `Term` of its own), 1 = comparison, 2 = `+`/`-`,
/// 3 = `*`/`/`/`%`, 4 = unary minus (a negative `Lit`), 5 = application,
/// 6 = an atom (`Var`/non-negative `Lit`/parenthesized).
fn op_prec(op: PrimOp) -> u8 {
    use PrimOp::*;
    match op {
        Lt | Le | Eq => 1,
        Add | Sub => 2,
        Mul | Div | Mod => 3,
    }
}

/// `names[i]` is the name bound to `Var(names.len() - 1 - i)` in the
/// current scope -- the exact mirror of `Parser::scope`.
fn print_at(store: &TermStore, h: Hash, names: &mut Vec<String>, min_prec: u8) -> String {
    let (own_prec, text) = match store.resolve(h) {
        // a free variable (index past the binders in scope) has no name: `#i`, which does not reparse
        Term::Var(i) => (6, names.len().checked_sub(1 + *i as usize).map_or_else(|| format!("#{i}"), |k| names[k].clone())),
        // `-n` is unary minus, not an atom: bare as an application's
        // argument (`f -2`) it would reparse as the subtraction `f - 2`,
        // and as its function (`-2 x`) as `-(2 x)`.
        Term::Lit(n) => (if *n < 0 { 4 } else { 6 }, n.to_string()),
        Term::Prim(op, a, b) => {
            let p = op_prec(*op);
            // Comparisons don't chain (parse_cmp allows only one), so
            // *both* sides need strictly-higher precedence to force
            // parentheses around any nested comparison; the arithmetic
            // ops are left-associative, so the left side accepts its own
            // precedence back (matching how the term was actually built)
            // while the right side needs strictly higher, to disambiguate
            // right-nesting from the left-nesting parse_add/parse_mul
            // themselves always produce.
            let (lp, rp) = if p == 1 { (2, 2) } else { (p, p + 1) };
            let lhs = print_at(store, *a, names, lp);
            let rhs = print_at(store, *b, names, rp);
            (p, format!("{lhs} {} {rhs}", op_symbol(*op)))
        }
        Term::If(c, t, e) => {
            let cs = print_at(store, *c, names, 0);
            let ts = print_at(store, *t, names, 0);
            let es = print_at(store, *e, names, 0);
            (0, format!("if {cs} then {ts} else {es}"))
        }
        Term::Abs(body) => {
            let name = fresh_name(names.len());
            names.push(name.clone());
            let bs = print_at(store, *body, names, 0);
            names.pop();
            (0, format!("\\{name}. {bs}"))
        }
        Term::App(f, a) => {
            let fs = print_at(store, *f, names, 5);
            let as_ = print_at(store, *a, names, 6);
            (5, format!("{fs} {as_}"))
        }
        Term::Rec(inner) => {
            let mut k = 0usize;
            let mut cur = *inner;
            while let Term::Abs(next) = store.resolve(cur) {
                k += 1;
                cur = *next;
            }
            let body_hash = cur;
            let self_name = fresh_name(names.len());
            names.push(self_name.clone());
            let mut param_names = Vec::with_capacity(k);
            for _ in 0..k {
                let pname = fresh_name(names.len());
                names.push(pname.clone());
                param_names.push(pname);
            }
            let bs = print_at(store, body_hash, names, 0);
            names.truncate(names.len() - k - 1);
            let params = if param_names.is_empty() { String::new() } else { format!(" {}", param_names.join(" ")) };
            (0, format!("rec {self_name}{params} = {bs}"))
        }
    };
    if own_prec < min_prec { format!("({text})") } else { text }
}

/// Prints `h` as source text this module's own `parse` accepts back --
/// see the section docs above for exactly what round-trips.
pub fn print(store: &TermStore, h: Hash) -> String {
    print_at(store, h, &mut Vec::new(), 0)
}

#[cfg(test)]
mod tests;
