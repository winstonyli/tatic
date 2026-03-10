type Hash = blake3::Hash;

enum Term {
    Var(usize),
    Abs(Hash),
    App([Hash; 2]),
}

fn main() {
    println!("Hello, world!");
}
