use std::ops::{Add, Mul, Neg, Sub};

use crate::ff::FieldElement;

#[derive(Debug, Clone)]
pub struct Polynomial {
  coeffs: Vec<FieldElement>
}

impl Neg for Polynomial {
  type Output = Polynomial;

  fn neg(self) -> Self::Output {
    Polynomial { 
      coeffs: self.coeffs.into_iter().map(|c| -c).collect()
    }
  }
}

impl Add for Polynomial {
    type Output = Polynomial;

    fn add(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl Sub for Polynomial {
    type Output = Polynomial;

    fn sub(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl Mul for Polynomial {
    type Output = Polynomial;

    fn mul(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        self.coeffs == other.coeffs
    }

    fn ne(&self, other: &Self) -> bool {
        self.coeffs != other.coeffs
    }
}

impl Polynomial {
  pub fn new(coeffs: Vec<FieldElement>) -> Polynomial {
    Polynomial { coeffs: coeffs }
  }

  pub fn deg(&self) -> i128 {
    if self.coeffs.len() == 0 {
      return -1
    }
    if self.coeffs.iter().all(|&c| c == c.field.zero()) {
      return -1;
    }
    let mut maxidx = 0;
    for (i , k) in self.coeffs.iter().enumerate() {
      if *k != k.field.zero() {
        maxidx = i;
      }
    }
    maxidx as i128
  }

  pub fn is_zero(&self) -> bool {
    self.deg() == -1
  }

  pub fn leading_coeff(&self) -> FieldElement {
    self.coeffs[self.deg() as usize]
  }
}