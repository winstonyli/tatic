use crate::state::*;
use std::time::{Duration, Instant};

#[test]
fn line_has_the_three_fields() {
    let l = line();
    let re = regex::Regex::new(r"^RTP=(True|False|\?) CPU=\d+% lockpriv=(True|False)$").unwrap();
    assert!(re.is_match(&l), "{l}");
}

#[test]
fn rtp_is_known_on_this_machine() {
    assert!(rtp().is_some());
}

#[test]
fn only_service_unavailable_decides_rtp() {
    assert_eq!(rtp_from_status(1), Some(false));
    assert_eq!(rtp_from_status(0x8001), Some(false));
    assert_eq!(rtp_from_status(0), None);
    assert_eq!(rtp_from_status(2), None);
}

#[test]
fn privilege_list_is_a_count_then_luid_attribute_triples() {
    let luid = Luid { low: 4, high: 0 };
    assert!(privileges_contain(&[2, 23, 0, 3, 4, 0, 0], luid));
    assert!(!privileges_contain(&[1, 23, 0, 3], luid));
    // a count past the buffer reads no further than the buffer
    assert!(!privileges_contain(&[5, 23, 0], luid));
}

#[test]
fn load_is_a_percentage_and_sees_a_busy_thread() {
    let a = times();
    let t = Instant::now();
    let mut x = 0u64;
    while t.elapsed() < Duration::from_millis(300) {
        x = std::hint::black_box(x.wrapping_add(1));
    }
    let b = times();
    let (busy, total) = b.since(&a);
    assert!(busy >= 0.25, "busy {busy} s while this thread spun 0.3 s");
    assert!(total >= busy);
    let l = b.load_since(&a);
    assert!((0.0..=100.0).contains(&l), "{l}");
}
