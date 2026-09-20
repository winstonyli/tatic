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

use crate::term::{Hash, PrimOp, Term, TermStore};

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
// Round-trips for everything this grammar can express, with one honest
// exception: a literal built directly as `Term::Lit(n)` for `n < 0` (never
// produced by `parse` itself, which only reaches a negative value via
// unary-minus desugaring to `Prim(Sub, Lit(0), ..)`) prints using Rust's
// ordinary negative-number formatting, but this grammar has no negative-
// literal syntax at all -- only subtraction -- so reparsing that text
// yields the desugared `Prim(Sub, Lit(0), Lit(-n))` form, not the original
// bare `Lit(n)`. Semantically identical, not hash-identical; see this
// module's own test for it.

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
/// 3 = `*`/`/`/`%`, 5 = application, 6 = an atom (`Var`/`Lit`/parenthesized).
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
        Term::Var(i) => (6, names[names.len() - 1 - *i as usize].clone()),
        Term::Lit(n) => (6, n.to_string()),
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
mod tests {
    use super::*;
    use crate::eval;

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
        // Interesting, honest finding: `let x = e1 in e2` desugars to
        // `App(Abs(e2), e1)`, so nesting a *second* let inside the
        // first's body makes the inner let's own `\y. ..` value reference
        // the outer let's binding by `Var`, not by name -- and when
        // compile.rs peels that inner lambda *standalone* (as it does for
        // any candidate combinator), that outer reference is exactly a
        // captured free variable. Nothing about the *source* looks like a
        // capturing closure; the capture is an artifact of two lets
        // nesting this way once desugared. compile.rs's closure
        // conversion (see its module docs) handles this correctly -- it
        // compiles and runs, not just falls back to the interpreter.
        //
        // A second, later finding, once `proof::prove_closure_expr_instance`
        // existed: this term's outer `inc` parameter is never actually
        // *called* anywhere in its own body (`inc` is only ever passed
        // along, as a plain value, to `twice`) -- so `param_types_for`
        // classifies it `None` (Int) for exactly the same reason it
        // classifies a genuinely inconsistent parameter that way (see
        // `compile::ArityUse`'s own docs): "never assigned a single
        // static arity", whether that's because it's never called at all
        // or because it's called at two disagreeing ones. `denote_closure`'s
        // own *universal* proof still declines this (the same `Int`
        // classification makes its own per-argument type check fail once
        // it sees `inc` is actually a `Clo`), but the per-instance
        // strategy's inlining doesn't care *why* a parameter was
        // classified `None` -- only that the concretely-supplied argument
        // disagrees with it -- so it picks this shape up too, entirely as
        // a side effect of the same mechanism built for the inconsistent-
        // arity case, not a separate one.
        let mut s = TermStore::new();
        let parsed = parse(&mut s, "let inc = \\y. y + 1 in let twice = \\f. \\x. f (f x) in twice inc 5").unwrap();
        assert_eq!(eval::apply_term(&s, parsed, &[]).unwrap(), 7);

        use crate::jit::JitEngine;
        let mut jit = JitEngine::new();
        assert_eq!(jit.apply(&s, parsed, &[]).unwrap(), 7);
        assert!(
            jit.is_kernel_verified(parsed),
            "prove_closure_expr_instance's own inlining covers this now, as a side effect of the inconsistent-arity mechanism -- see this test's own updated comment"
        );
        assert_eq!(jit.stats.compiled, 1);
        assert_eq!(jit.stats.interpreted, 0);
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

    /// `print(store, h)` reparses (into a fresh store) to the exact same
    /// content hash -- a strictly stronger check than "prints something
    /// plausible": content-addressing means this only holds if the printed
    /// text really does denote the identical term structure.
    fn assert_round_trips(store: &TermStore, h: Hash) {
        let text = print(store, h);
        let mut fresh = TermStore::new();
        let reparsed =
            parse(&mut fresh, &text).unwrap_or_else(|e| panic!("printed text failed to reparse: {text:?}\nerror: {e}"));
        assert_eq!(reparsed, h, "round-trip mismatch; printed: {text:?}");
    }

    #[test]
    fn round_trips_arithmetic_with_mixed_precedence_and_right_nesting() {
        let mut s = TermStore::new();
        // 1 + 2 * 3 -- Mul binds tighter, no parens needed either way.
        let h1 = parse(&mut s, "1 + 2 * 3").unwrap();
        assert_round_trips(&s, h1);

        // A hand-built *right*-nested subtraction, which a left-associative
        // parser would never itself produce -- print must add parens
        // around the right operand to preserve the grouping, or this
        // would silently change from (a - (b - c)) to ((a - b) - c).
        let a = s.lit(10);
        let b = s.lit(3);
        let c = s.lit(2);
        let bc = s.prim(PrimOp::Sub, b, c);
        let right_nested = s.prim(PrimOp::Sub, a, bc);
        assert_round_trips(&s, right_nested);
        assert_eq!(eval::apply_term(&s, right_nested, &[]).unwrap(), 9); // 10 - (3 - 2)

        // A hand-built nested comparison -- parse_cmp doesn't chain, so
        // this needs parens around the inner comparison on either side.
        let one = s.lit(1);
        let two = s.lit(2);
        let three = s.lit(3);
        let inner_cmp = s.prim(PrimOp::Lt, one, two);
        let nested_cmp = s.prim(PrimOp::Eq, inner_cmp, three);
        assert_round_trips(&s, nested_cmp);
    }

    #[test]
    fn round_trips_if_lambda_application_and_rec() {
        let mut s = TermStore::new();
        for src in [
            "if 1 < 2 then 10 else 20",
            "(\\x y. x - y) 10 3",
            "rec f n = if n <= 1 then 1 else n * f (n - 1)",
            "rec f a b = if b == 0 then a else f b (a % b)",
            "let inc = \\y. y + 1 in let twice = \\f. \\x. f (f x) in twice inc 5",
            "\\x. \\x. x", // shadowing
        ] {
            let h = parse(&mut s, src).unwrap_or_else(|e| panic!("fixture `{src}` failed to parse: {e}"));
            assert_round_trips(&s, h);
        }
    }

    #[test]
    fn round_trips_an_application_argument_that_is_itself_an_application() {
        // f (g x) -- without parens around the argument, "f g x" would
        // parse as a 3-ary call to f instead.
        let mut s = TermStore::new();
        let h = parse(&mut s, "\\f. \\g. \\x. f (g x)").unwrap();
        assert_round_trips(&s, h);
    }

    #[test]
    fn round_trips_a_zero_arity_rec() {
        // rec f = 5 -- unusual (no base case reachable via any argument,
        // out of compile.rs's fragment too -- see its own docs), but a
        // legitimate term this grammar can express and print needs to
        // handle it (zero Abs layers inside the Rec).
        let mut s = TermStore::new();
        let h = parse(&mut s, "rec f = 5").unwrap();
        assert_round_trips(&s, h);
    }

    #[test]
    fn a_directly_built_negative_literal_does_not_round_trip_exactly() {
        // Term::Lit(n) for n < 0 is never produced by parse itself (which
        // only reaches a negative value via unary-minus desugaring to
        // Prim(Sub, Lit(0), ..)) -- this grammar simply has no negative-
        // literal syntax. print still emits something reasonable (Rust's
        // ordinary negative-number formatting), but reparsing it yields
        // the desugared Prim form, not the original bare Lit -- a real,
        // documented gap, not silently worked around.
        let mut s = TermStore::new();
        let neg_five = s.lit(-5);
        let text = print(&s, neg_five);
        assert_eq!(text, "-5");

        let mut fresh = TermStore::new();
        let reparsed = parse(&mut fresh, &text).unwrap();
        assert_ne!(reparsed, neg_five, "a bare negative Lit has no exact round trip in this grammar");
        assert_eq!(eval::apply_term(&fresh, reparsed, &[]).unwrap(), -5); // still semantically equal
    }
}
