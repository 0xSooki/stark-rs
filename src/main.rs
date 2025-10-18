use crate::ff::FiniteField;
mod ff;
mod utils;
pub mod univariate;
use crate::univariate::Polynomial;
const P: u64 = 998244353; // 2^31 - 1 (Mersenne prime)

fn main() {
    let f = FiniteField::new(P);
    let root = f.prim_nth_root(8);
    let pp = Polynomial::new(vec![], f);

    println!("{:?}", pp);
}
