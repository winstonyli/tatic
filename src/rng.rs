//! SplitMix64, the one pseudo-random stream of the crate's fuzzers and randomised tests (lib and `tests/*.rs`). Not for
//! anything that needs unpredictability. Seeds name streams in docs and regressions (`compile_fuzz` seed 2117, say), so the
//! output for a seed must never change.

/// SplitMix64's output function: a stateless 64-bit mixer, for hashing an index into a well-spread value.
pub fn mix64(mut z: u64) -> u64 {
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A SplitMix64 stream from its seed.
#[derive(Clone, Debug)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        SplitMix64(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        mix64(self.0)
    }

    /// Uniform-ish in `0..n` (modulo bias, which the fuzzers accept).
    pub fn below(&mut self, n: u32) -> u32 {
        (self.next_u64() % n as u64) as u32
    }

    /// Uniform-ish in `lo..=hi`.
    pub fn i64_range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next_u64() % ((hi - lo + 1) as u64)) as i64
    }
}

#[cfg(test)]
mod tests {
    use super::SplitMix64;

    #[test]
    fn seed_0_gives_the_reference_stream() {
        let mut r = SplitMix64::new(0);
        assert_eq!([r.next_u64(), r.next_u64(), r.next_u64()], [0xe220a8397b1dcdaf, 0x6e789e6aa1b965f4, 0x06c45d188009454f]);
    }
}
