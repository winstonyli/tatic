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
//!          | "rec" IDENT IDENT+ "=" expr
//!          | "if" expr "then" expr "else" expr
//!          | cmp
//! cmp     := add (("<" | "<=" | "==") add)?
//! add     := mul (("+" | "-") mul)*
//! mul     := unary (("*" | "/" | "%") unary)*
//! unary   := "-" unary | app
//! app     := atom+                      -- left-associative juxtaposition
//! atom    := INT | IDENT | "(" expr ")"
//! ```
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

use crate::term::{Hash, PrimOp, TermStore};

#[derive(Debug, Clone, PartialEq)]
enum Token {
    Int(i64),
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
    EqEq,
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
            '0'..='9' => {
                let start = i;
                while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                    i += 1;
                }
                let text = &src[start..i];
                let n: i64 = text
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
        let mut params = Vec::new();
        while let Token::Ident(_) = self.peek() {
            params.push(self.expect_ident()?);
        }
        if params.is_empty() {
            return Err(self.error("expected at least one parameter"));
        }
        Ok(params)
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
            _ => self.parse_cmp(),
        }
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
        let params = self.parse_params()?;
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
        let op = match self.peek() {
            Token::Lt => Some(PrimOp::Lt),
            Token::Le => Some(PrimOp::Le),
            Token::EqEq => Some(PrimOp::Eq),
            _ => None,
        };
        match op {
            Some(op) => {
                self.advance();
                let rhs = self.parse_add()?;
                Ok(self.store.prim(op, lhs, rhs))
            }
            None => Ok(lhs),
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
        if matches!(self.peek(), Token::Minus) {
            self.advance();
            let operand = self.parse_unary()?;
            let zero = self.store.lit(0);
            Ok(self.store.prim(PrimOp::Sub, zero, operand))
        } else {
            self.parse_app()
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
            Token::Int(n) => Ok(self.store.lit(n)),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::eval;
    use crate::term::Term;

    #[test]
    fn literal() {
        let mut s = TermStore::new();
        let h = parse(&mut s, "42").unwrap();
        assert_eq!(*s.resolve(h), Term::Lit(42));
    }

    #[test]
    fn arithmetic_precedence() {
        // 1 + 2 * 3 should parse as 1 + (2 * 3), not (1 + 2) * 3.
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "1 + 2 * 3").unwrap();

        let one = s.lit(1);
        let two = s.lit(2);
        let three = s.lit(3);
        let mul = s.prim(PrimOp::Mul, two, three);
        let expected = s.prim(PrimOp::Add, one, mul);

        assert_eq!(parsed, expected);
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);
    }

    #[test]
    fn unary_minus_desugars_to_zero_minus_operand() {
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "-5 + 3").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), -2);
    }

    #[test]
    fn comparison_and_if() {
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "if 1 < 2 then 10 else 20").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 10);
    }

    #[test]
    fn lambda_application_and_last_param_is_innermost() {
        // \x y. x - y applied to (10, 3): x = 10 (first-applied, outer),
        // y = 3 (last-applied, inner) -- if the convention were backwards
        // this would come out -7 instead of 7.
        let mut s = TermStore::new();
        let f = parse(&mut s, "\\x y. x - y").unwrap();
        let ten = s.lit(10);
        let three = s.lit(3);
        let applied = s.app2(f, ten, three);
        assert_eq!(eval::apply_term(&s, applied, &[]).unwrap(), 7);
    }

    #[test]
    fn let_binding() {
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "let x = 5 in x + 1").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 6);
    }

    #[test]
    fn shadowing_resolves_to_the_innermost_binder() {
        let mut s = TermStore::new();
        let f = parse(&mut s, "\\x. \\x. x").unwrap();
        let a = s.lit(1);
        let b = s.lit(2);
        let applied = s.app2(f, a, b);
        assert_eq!(eval::apply_term(&s, applied, &[]).unwrap(), 2);
    }

    #[test]
    fn factorial_matches_the_hand_built_term_exactly() {
        // rec f n = if n <= 1 then 1 else n * f (n - 1) -- content-addressed
        // hashing means an *identical* structure, however it was built,
        // hashes identically; this is a strictly stronger check than "it
        // evaluates to the same answer".
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "rec f n = if n <= 1 then 1 else n * f (n - 1)").unwrap();

        let n = s.var(0);
        let fv = s.var(1);
        let one = s.lit(1);
        let cond = s.prim(PrimOp::Le, n, one);
        let n_minus_1 = s.prim(PrimOp::Sub, n, one);
        let rec_call = s.app(fv, n_minus_1);
        let else_branch = s.prim(PrimOp::Mul, n, rec_call);
        let body = s.if_(cond, one, else_branch);
        let abs = s.abs(body);
        let hand_built = s.rec(abs);

        assert_eq!(parsed, hand_built);
        assert_eq!(eval::apply_term(&s, parsed, &[10]).unwrap(), 3628800);
    }

    #[test]
    fn gcd_two_params_matches_the_hand_built_term_exactly() {
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "rec f a b = if b == 0 then a else f b (a % b)").unwrap();

        let b = s.var(0);
        let a = s.var(1);
        let f = s.var(2);
        let zero = s.lit(0);
        let cond = s.prim(PrimOp::Eq, b, zero);
        let a_mod_b = s.prim(PrimOp::Mod, a, b);
        let rec_call = s.app2(f, b, a_mod_b);
        let body = s.if_(cond, a, rec_call);
        let inner = s.abs(body);
        let abs = s.abs(inner);
        let hand_built = s.rec(abs);

        assert_eq!(parsed, hand_built);
        assert_eq!(eval::apply_term(&s, parsed, &[48, 18]).unwrap(), 6);
    }

    #[test]
    fn higher_order_let_chain_evaluates_like_the_hand_built_demo_term() {
        // Mirrors main.rs's higher_order_demo: (twice inc) 5, but with
        // twice/inc each bound through their own let -- a behavioral
        // check, not a hash-equality one, since let-desugaring genuinely
        // builds a different term structure from the inlined hand-built
        // version (an extra App(Abs(..), ..) wrapper per let), not just a
        // different way of writing the same one.
        //
        // Interesting, honest finding: this term does NOT compile via
        // compile.rs, and falls back to the interpreter -- correctly.
        // `let x = e1 in e2` desugars to `App(Abs(e2), e1)`, so nesting a
        // *second* let inside the first's body makes the inner let's own
        // `\y. ..` value reference the outer let's binding by `Var`, not
        // by name -- and when compile.rs peels that inner lambda
        // *standalone* (as it does for any candidate combinator, per its
        // non-capturing check), that outer reference is exactly a
        // captured free variable. Nothing about the *source* looks like a
        // capturing closure; the capture is an artifact of two lets
        // nesting this way once desugared. A single, non-nested let (see
        // `a_single_let_around_a_closure_still_compiles` below) doesn't
        // have this problem.
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "let inc = \\y. y + 1 in let twice = \\f. \\x. f (f x) in twice inc 5").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);

        use crate::jit::JitEngine;
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, parsed, &[]).unwrap(), 7);
        assert!(!jit.is_kernel_verified(parsed), "nested lets across a closure boundary should (still, correctly) capture");
        assert_eq!(jit.stats.interpreted, 1);
    }

    #[test]
    fn a_single_let_around_a_closure_still_compiles() {
        // let twice = \f. \x. f (f x) in twice (\y. y + 1) 5 -- inc is
        // inlined directly rather than separately let-bound, so twice's
        // own let-lambda doesn't reference anything outside its own
        // parameter range when peeled standalone: no accidental capture
        // (see the test above), and this does compile and get proven.
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "let twice = \\f. \\x. f (f x) in twice (\\y. y + 1) 5").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);

        use crate::jit::JitEngine;
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, parsed, &[]).unwrap(), 7);
        assert!(jit.is_kernel_verified(parsed));
    }

    #[test]
    fn unbound_variable_is_a_parse_error() {
        let mut s = TermStore::new();
        let err = parse(&mut s, "x + 1").unwrap_err();
        assert!(err.message.contains("unbound variable"), "message was: {}", err.message);
    }

    #[test]
    fn trailing_input_is_a_parse_error() {
        let mut s = TermStore::new();
        let err = parse(&mut s, "1 + 2)").unwrap_err();
        assert!(err.message.contains("Eof") || err.message.contains("expected"), "message was: {}", err.message);
    }

    #[test]
    fn unclosed_paren_is_a_parse_error() {
        let mut s = TermStore::new();
        assert!(parse(&mut s, "(1 + 2").is_err());
    }

    #[test]
    fn compiles_and_runs_through_the_jit_like_any_hand_built_term() {
        use crate::jit::JitEngine;

        let mut s = TermStore::new();
        let parsed = parse(&mut s, "rec f a b = if b == 0 then a else f b (a % b)").unwrap();
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, parsed, &[270, 192]).unwrap(), 6);
        assert!(jit.is_kernel_verified(parsed));
    }
}
