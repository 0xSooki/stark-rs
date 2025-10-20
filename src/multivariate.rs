use std::{collections::{HashMap, hash_map}, ops::{Add, BitXor, Mul, Neg, Sub}};

use crate::{ff::FieldElement, univariate::Polynomial};


#[derive(Debug, Clone)]
pub struct MPolynomial {
  pub terms: HashMap<usize, Vec<FieldElement>>
}

impl MPolynomial {
  pub fn new(terms: &HashMap<usize, Vec<FieldElement>>) -> MPolynomial {
    MPolynomial { terms: terms.clone() }
  }

  pub fn zero() -> MPolynomial {
        MPolynomial { terms: HashMap::new() }
  }
}

impl Add<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn add(self, rhs: &MPolynomial) -> Self::Output {
        todo!()
    }
}

impl Mul<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn mul(self, rhs: &MPolynomial) -> Self::Output {
        todo!()
    }
}

impl Sub<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn sub(self, rhs: &MPolynomial) -> Self::Output {
        todo!()
    }
}

impl Neg for &MPolynomial {
    type Output = MPolynomial;

    fn neg(self) -> Self::Output {
        todo!()
    }
}

impl BitXor for &MPolynomial {
    type Output = MPolynomial;

    fn bitxor(self, rhs: Self) -> Self::Output {
        todo!()
    }
}