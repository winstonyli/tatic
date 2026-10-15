//! A binary format for closed terms. A term is a DAG (equal subterms built in a [`scoped`](crate::kernel::scoped) call are one node), so the format
//! is a node table: the node count, then each distinct node once, children before parents, as a tag byte and LEB128 varints
//! (the index of a `Var` or level of a `Sort`, or each child as its distance back in the table). The root is the last node.
//! Reading goes through the public constructors, so a term read inside `scoped` is interned.

use super::*;
use std::collections::HashMap;

/// The children of `n` in field order.
fn children(n: &Node<Expr>) -> Vec<Expr> {
    let mut cs = Vec::new();
    n.for_kids(|c, _| cs.push(c.clone()));
    cs
}

fn tag(n: &Node<Expr>) -> u8 {
    match n {
        Node::Var(_) => 0,
        Node::Sort(_) => 1,
        Node::Pi(..) => 2,
        Node::Lam(..) => 3,
        Node::App(..) => 4,
        Node::Id(..) => 5,
        Node::Refl(_) => 6,
        Node::J { .. } => 7,
        Node::W(..) => 8,
        Node::Sup(..) => 9,
        Node::WRec { .. } => 10,
        Node::Sigma(..) => 11,
        Node::Pair(..) => 12,
        Node::SigRec { .. } => 13,
        Node::Const(_) | Node::Free(_) => u8::MAX,
    }
}

fn put(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push(v as u8 | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

fn get(b: &[u8], pos: &mut usize) -> Result<u64, String> {
    let mut v = 0u64;
    for shift in (0..64).step_by(7) {
        let byte = *b.get(*pos).ok_or("truncated varint")?;
        *pos += 1;
        v |= ((byte & 0x7f) as u64) << shift;
        if byte < 0x80 {
            return Ok(v);
        }
    }
    Err("varint too long".into())
}

/// The bytes of `e`; `Err` on a `Const` or `Free` (the format is for closed terms).
pub fn write(e: &Expr) -> Result<Vec<u8>, String> {
    let mut index: HashMap<u64, u64> = HashMap::new();
    let mut body = Vec::new();
    // post-order without recursion: (node, children already pushed)
    let mut stack: Vec<(Expr, bool)> = vec![(e.clone(), false)];
    while let Some((x, expanded)) = stack.pop() {
        let key = node_key(&x);
        if index.contains_key(&key) {
            continue;
        }
        let n = x.node();
        if !expanded {
            stack.push((x, true));
            stack.extend(children(&n).into_iter().rev().map(|c| (c, false)));
            continue;
        }
        let at = index.len() as u64;
        match n {
            Node::Const(_) | Node::Free(_) => return Err(format!("not a closed term: {x:?}")),
            Node::Var(k) | Node::Sort(k) => {
                body.push(tag(&n));
                put(&mut body, k as u64);
            }
            _ => {
                body.push(tag(&n));
                for c in children(&n) {
                    put(&mut body, at - index[&node_key(&c)]);
                }
            }
        }
        index.insert(key, at);
    }
    let mut out = Vec::with_capacity(body.len() + 5);
    put(&mut out, index.len() as u64);
    out.extend(body);
    Ok(out)
}

/// The term `write` wrote; `Err` on a bad tag, a child out of range, or missing or trailing bytes.
pub fn read(b: &[u8]) -> Result<Expr, String> {
    let mut pos = 0;
    let n = get(b, &mut pos)?;
    let mut nodes: Vec<Expr> = Vec::new();
    for at in 0..n {
        let t = *b.get(pos).ok_or("truncated node")?;
        pos += 1;
        let mut kid = || -> Result<Expr, String> {
            let d = get(b, &mut pos)?;
            if d == 0 || d > at {
                return Err(format!("child distance {d} out of range at node {at}"));
            }
            Ok(nodes[(at - d) as usize].clone())
        };
        let e = match t {
            0 | 1 => {
                let k = u32::try_from(get(b, &mut pos)?).map_err(|_| "index too large")?;
                if t == 0 { var(k) } else { sort(k) }
            }
            6 => refl(kid()?),
            2 | 3 | 4 | 8 | 9 | 11 => {
                let (x, y) = (kid()?, kid()?);
                match t {
                    2 => pi(x, y),
                    3 => lam(x, y),
                    4 => app(x, y),
                    8 => wty(x, y),
                    9 => sup(x, y),
                    _ => sigma(x, y),
                }
            }
            5 | 12 | 13 => {
                let (x, y, z) = (kid()?, kid()?, kid()?);
                match t {
                    5 => id(x, y, z),
                    12 => pair(x, y, z),
                    _ => sigrec(x, y, z),
                }
            }
            10 => {
                let (m, c, s, g) = (kid()?, kid()?, kid()?, kid()?);
                wrec(m, c, s, g)
            }
            7 => {
                let (m, base, x, y, p) = (kid()?, kid()?, kid()?, kid()?, kid()?);
                jelim(m, base, x, y, p)
            }
            _ => return Err(format!("bad tag {t} at node {at}")),
        };
        nodes.push(e);
    }
    if pos != b.len() {
        return Err(format!("{} trailing bytes", b.len() - pos));
    }
    nodes.pop().ok_or_else(|| "no nodes".into())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A closed term using every variant, with a shared subterm.
    fn sample() -> Expr {
        let ty = pi(sort(0), pi(var(0), var(1)));
        let x = lam(sort(0), lam(var(0), var(0)));
        let eq = id(ty.clone(), x.clone(), x.clone());
        let j = jelim(var(0), var(1), x.clone(), x.clone(), refl(x.clone()));
        let w = wrec(var(0), var(1), var(2), sup(var(3), var(4)));
        let s = sigrec(var(0), pair(var(1), var(2), var(3)), sigma(sort(1), wty(var(0), var(1))));
        lam(eq, app(app(j, w), s))
    }

    #[test]
    fn bin_round_trips_and_shares_nodes() {
        let e = sample();
        let b = write(&e).unwrap();
        assert!(read(&b).unwrap() == e);
        // inside an interning scope equal subterms are one node, so the table is smaller than the tree
        scoped(|| {
            let shared = sample();
            let bs = write(&shared).unwrap();
            assert!(read(&bs).unwrap() == shared);
            assert!(bs.len() < b.len(), "interned {} bytes, plain {}", bs.len(), b.len());
        })
    }

    #[test]
    fn bin_rejects_bad_input() {
        let b = write(&sample()).unwrap();
        assert!(read(&b[..b.len() - 1]).is_err(), "truncated");
        let mut extra = b.clone();
        extra.push(0);
        assert!(read(&extra).is_err(), "trailing byte");
        assert!(read(&[1, 99]).is_err(), "bad tag");
        assert!(read(&[1, 6, 1]).is_err(), "child before the first node");
        assert!(read(&[]).is_err(), "empty");
        assert!(write(&app(mk(Node::Free(0)), sort(0))).is_err(), "a Free is not closed");
    }
}
