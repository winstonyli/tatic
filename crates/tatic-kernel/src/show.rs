use super::*;

/// `x` printed with `{:?}`, cut off after about 400 characters. A term is a DAG but prints as a tree,
/// so the full text of an error's terms can be exponentially large in the DAG's size (the rejection
/// of a false statement at n=12 spent 99% of its 11 s, and 2.4 GB, in formatting the message;
/// doc section 82). The writer fails once it is full, which stops the printer's recursion.
pub(crate) fn brief<T: fmt::Debug + ?Sized>(x: &T) -> String {
    const LIMIT: usize = 400;
    struct Limited(String);
    impl fmt::Write for Limited {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            let room = LIMIT.saturating_sub(self.0.len());
            if s.len() > room {
                let mut cut = room;
                while !s.is_char_boundary(cut) {
                    cut -= 1;
                }
                self.0.push_str(&s[..cut]);
                return Err(fmt::Error);
            }
            self.0.push_str(s);
            Ok(())
        }
    }
    let mut out = Limited(String::new());
    if fmt::Write::write_fmt(&mut out, format_args!("{x:?}")).is_err() {
        out.0.push_str(" ...");
    }
    out.0
}

/// `brief(&nf(e))`, normalizing only what gets printed: each node is reduced to whnf as the printer
/// reaches it, and `brief`'s limit stops the printer, so a type mismatch between two large normal
/// forms costs the first `LIMIT` characters of each, not both whole normal forms (doc section
/// "The NEG control's wall was the error message").
pub(crate) fn brief_nf(e: &Expr) -> String {
    struct Nf(Expr);
    impl fmt::Debug for Nf {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let w = with_spaces(|s| whnf_in(s, &self.0));
            write_expr(&w.node(), f, &|c, f| fmt::Debug::fmt(&Nf(*c), f))
        }
    }
    brief(&Nf(*e))
}

/// A child printed by the function it carries (`write_expr`).
struct Child<'a, F>(&'a Expr, &'a F);
impl<F: Fn(&Expr, &mut fmt::Formatter<'_>) -> fmt::Result> fmt::Debug for Child<'_, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (self.1)(self.0, f)
    }
}

/// The node `n`, with each child printed by `child`.
fn write_expr<F: Fn(&Expr, &mut fmt::Formatter<'_>) -> fmt::Result>(n: &Node<Expr>, f: &mut fmt::Formatter<'_>, child: &F) -> fmt::Result {
    let c = |x| Child(x, child);
    grow(|| match n {
        Node::Var(k) => write!(f, "#{k}"),
        Node::Sort(i) => write!(f, "Type{i}"),
        Node::Const(l) => write!(f, "@{l}"),
        Node::Free(l) => write!(f, "${l}"),
        Node::Pi(a, b) => write!(f, "(Pi {:?}. {:?})", c(a), c(b)),
        Node::Lam(a, b) => write!(f, "(\\{:?}. {:?})", c(a), c(b)),
        Node::App(g, a) => write!(f, "({:?} {:?})", c(g), c(a)),
        Node::Id(a, x, y) => write!(f, "(Id {:?} {:?} {:?})", c(a), c(x), c(y)),
        Node::Refl(a) => write!(f, "(refl {:?})", c(a)),
        Node::J { a, b, p, .. } => write!(f, "(J .. {:?} {:?} {:?})", c(a), c(b), c(p)),
        Node::W(a, b) => write!(f, "(W {:?}. {:?})", c(a), c(b)),
        Node::Sup(a, g) => write!(f, "(sup {:?} {:?})", c(a), c(g)),
        Node::WRec { target, .. } => write!(f, "(wrec .. {:?})", c(target)),
        Node::Sigma(a, b) => write!(f, "(Sigma {:?}. {:?})", c(a), c(b)),
        Node::Pair(fam, a, b) => write!(f, "(pair {:?} {:?} {:?})", c(fam), c(a), c(b)),
        Node::SigRec { target, .. } => write!(f, "(sigrec .. {:?})", c(target)),
    })
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match with_spaces(|s| s.live(self.r, self.epoch).then(|| s.node(self))) {
            None => write!(f, "<dead handle>"),
            Some(n) => write_expr(&n, f, &|c, f| fmt::Debug::fmt(c, f)),
        }
    }
}

