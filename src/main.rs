use crate::ff::FiniteField;

mod ff;
mod utils;

const P: u64 = 2147483647; // 2^31 - 1 (Mersenne prime)

fn main() {
    let f = FiniteField::new(P);
    println!("{}", 12u64);
}
