//! The learned class table (docs/superpowers/specs/2026-10-22-class-table-normal-form-design.md): terms over x, y, z, 0
//! and -1 to size `SIZE`, enumerated from representatives only and keyed by their values on a learned key
//! (`class_key.txt`, baked in) and their sort. A class's representative is its smallest member `Machine::parse` takes,
//! else its smallest (decision 7). `rep` looks a term's class up; `step` and `normalize` use a replacement only with a
//! proof (§3).

use super::*;

/// The operators in enumeration order; `shl1` and `shr1` are unary, enumerated with the second operand `0`.
pub const OPS: [usize; 8] = [ADD, AND, OR, XOR, SUB, SHL1, SHR1, LT];
/// The largest term size the table enumerates (decision 4).
pub const SIZE: usize = 9;
/// The key, learned by `regenerate_key` and baked in, so the table depends only on the source.
pub const KEY_FILE: &str = include_str!("class_key.txt");
const REGENERATE: &str = "<exe> classes::regenerate_key --exact --ignored --nocapture, then rebuild";

/// The table's key: per width, its inputs (x, y, z).
#[derive(Clone, Debug, PartialEq)]
pub struct Key {
    pub sets: Vec<(usize, Vec<[u128; 3]>)>,
}

impl Key {
    /// The header the build expects: its operators in order and its size.
    fn header() -> String {
        format!("ops {} size {SIZE}", OPS.map(|o| OP_INFO[o].name).join(" "))
    }

    /// A key file's inputs; an error when its header is not this build's (it was learned for another table) or a line is
    /// not `<width> <x> <y> <z>` with a width of 1 to 8.
    pub fn parse(text: &str) -> Result<Key, String> {
        let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty());
        let head = lines.next().unwrap_or("");
        if head != Key::header() {
            return Err(format!("class key header {head:?} is not {:?}: regenerate the key ({REGENERATE})", Key::header()));
        }
        let mut key = Key { sets: vec![] };
        for l in lines {
            let f: Vec<u128> = l.split_whitespace().map(str::parse).collect::<Result<_, _>>().map_err(|e| format!("class key line {l:?}: {e}"))?;
            let &[w, x, y, z] = f.as_slice() else {
                return Err(format!("class key line {l:?}: not `<width> <x> <y> <z>`"));
            };
            if !(1..=8).contains(&w) || [x, y, z].iter().any(|v| *v > low_bits(w as usize)) {
                return Err(format!("class key line {l:?}: width 1 to 8 and values within it"));
            }
            key.push(w as usize, [x, y, z]);
        }
        Ok(key)
    }

    /// The key file's text.
    pub fn text(&self) -> String {
        let mut s = Key::header() + "\n";
        for (w, ins) in &self.sets {
            for x in ins {
                s += &format!("{w} {} {} {}\n", x[0], x[1], x[2]);
            }
        }
        s
    }

    /// Adds an input at width `w`.
    pub fn push(&mut self, w: usize, x: [u128; 3]) {
        match self.sets.iter_mut().find(|s| s.0 == w) {
            Some(s) => s.1.push(x),
            None => self.sets.push((w, vec![x])),
        }
    }

    /// The refinement's start: the 8 tuples of 0s and 1s, at width 8.
    pub fn start() -> Key {
        let mut k = Key { sets: vec![] };
        for i in 0..8u128 {
            k.push(8, [0, 1, 2].map(|v| i >> v & 1));
        }
        k
    }

    /// Inputs over all widths.
    pub fn len(&self) -> usize {
        self.sets.iter().map(|s| s.1.len()).sum()
    }
}

/// A key file's text reads back as the same key, and the baked-in file parses.
#[test]
fn a_key_round_trips_through_its_text() {
    let mut k = Key::start();
    k.push(4, [15, 0, 7]);
    k.push(3, [1, 2, 3]);
    assert_eq!(Key::parse(&k.text()), Ok(k.clone()));
    assert_eq!(k.len(), 10);
    assert!(Key::parse(KEY_FILE).is_ok(), "{:?}", Key::parse(KEY_FILE).err());
}

/// A key learned for another operator set or size, or a malformed line, is refused with the regeneration command.
#[test]
fn a_key_with_another_header_names_the_regeneration() {
    let other_ops = Key::start().text().replacen(" lt size", " size", 1);
    let other_size = Key::start().text().replacen("size 9", "size 11", 1);
    for text in [other_ops, other_size] {
        let e = Key::parse(&text).unwrap_err();
        assert!(e.contains("classes::regenerate_key"), "{e}");
    }
    let head = Key::start().text().lines().next().unwrap().to_string();
    assert!(Key::parse(&format!("{head}\n8 1 2\n")).is_err(), "three fields");
    assert!(Key::parse(&format!("{head}\n4 16 0 0\n")).is_err(), "a value wider than its width");
    assert!(Key::parse(&format!("{head}\n9 0 0 0\n")).is_err(), "width 9");
}
