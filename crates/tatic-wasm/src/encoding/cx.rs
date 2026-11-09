//! The binder depth while a term is built, so terms are written with names (`At`), not de Bruijn indices.
use super::*;

/// A term together with the binder depth it was built at, so it can be used under more binders (`Cx::at` shifts it).
#[derive(Clone, Copy)]
pub struct At(Expr, u32);

/// The binder depth while a term is built. Binders give their variable as an `At`, so terms are written with names,
/// not indices.
#[derive(Default)]
pub struct Cx(u32);

impl Cx {
    pub fn at(&self, a: At) -> Expr {
        let d = self.0.checked_sub(a.1).expect("an At used below its birth depth");
        shift(&a.0, 0, d as i32)
    }
    /// `e`, built at the current depth.
    pub fn mark(&self, e: Expr) -> At {
        At(e, self.0)
    }
    /// `body` one binder deeper, with that binder's variable, and no binder emitted (the caller wraps the result).
    pub fn under<R>(&mut self, body: impl FnOnce(&mut Cx, At) -> R) -> R {
        self.0 += 1;
        let x = At(var(0), self.0);
        let b = body(self, x);
        self.0 -= 1;
        b
    }
    pub fn lam(&mut self, ty: Expr, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr {
        lam(ty, self.under(body))
    }
    pub fn pi(&mut self, ty: Expr, body: impl FnOnce(&mut Cx, At) -> Expr) -> Expr {
        pi(ty, self.under(body))
    }
}

/// A telescope entry: a binder's type from the variables bound before it.
pub type Ty<'a> = Box<dyn Fn(&mut Cx, &[At]) -> Expr + 'a>;

/// `body` under the telescope `tys`, each binder's type built once and wrapped around the inside by `wrap`: `lam` or `pi`
/// for one side, both at once for a law (`law`).
pub fn tele<R>(c: &mut Cx, tys: &[Ty], xs: &mut Vec<At>, wrap: &dyn Fn(Expr, R) -> R, body: &mut dyn FnMut(&mut Cx, &[At]) -> R) -> R {
    if xs.len() == tys.len() {
        return body(c, xs);
    }
    let ty = tys[xs.len()](c, xs);
    let inner = c.under(|c, x| {
        xs.push(x);
        let b = tele(c, tys, xs, wrap, body);
        xs.pop();
        b
    });
    wrap(ty, inner)
}

/// `(proof, statement)` from one walk of the telescope: `body` gives both at the same depth, so a subterm they share (the
/// `refl` side of an equation) is built once. The proof gets the lambdas, the statement the Pis.
pub fn law(tys: &[Ty], mut body: impl FnMut(&mut Cx, &[At]) -> (Expr, Expr)) -> (Expr, Expr) {
    tele(&mut Cx::default(), tys, &mut vec![], &|ty, (p, s)| (lam(ty, p), pi(ty, s)), &mut body)
}

#[macro_export]
macro_rules! ty {
    (|$c:ident, $x:ident| $e:expr) => {
        Box::new(move |$c: &mut $crate::encoding::Cx, $x: &[$crate::encoding::At]| $e) as $crate::encoding::Ty
    };
}
pub use crate::ty;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn under_binds_a_variable_with_no_lambda() {
        let mut cx = Cx::default();
        assert!(cx.under(|cx, x| cx.at(x)) == var(0));
        let s = sigma(bool0(), Cx::default().under(|cx, x| id(bool0(), cx.at(x), t())));
        assert!(tatic_kernel::typecheck(&s).is_ok());
    }
    #[test]
    #[should_panic(expected = "below its birth depth")]
    fn an_at_used_below_its_birth_depth_panics() {
        let mut cx = Cx::default();
        let mut leaked = None;
        cx.lam(bool0(), |_, x| { leaked = Some(x); t() });
        cx.at(leaked.unwrap());
    }
    #[test]
    fn a_law_is_its_two_one_sided_telescopes() {
        let tys = [ty!(|_c, _x| bool0()), ty!(|c, x| id(bool0(), c.at(x[0]), c.at(x[0])))];
        let stmt = |c: &mut Cx, x: &[At]| id(bool0(), c.at(x[0]), c.at(x[0]));
        let proof = |c: &mut Cx, x: &[At]| refl(c.at(x[0]));
        let (p, s) = law(&tys, |c, x| (proof(c, x), stmt(c, x)));
        assert!(s == tele(&mut Cx::default(), &tys, &mut vec![], &pi, &mut |c, x| stmt(c, x)));
        assert!(p == tele(&mut Cx::default(), &tys, &mut vec![], &lam, &mut |c, x| proof(c, x)));
        assert!(holds(&p, &s).is_ok());
    }
}
