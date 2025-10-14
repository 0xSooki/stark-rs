
#![allow(dead_code)]
use core::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::utils::xgcd;

#[derive(Debug, Clone, Copy)]
pub struct FiniteField {
  p: u64
}

impl PartialEq for FiniteField {
    fn eq(&self, other: &Self) -> bool {
        self.p == other.p
    }
    
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FieldElement {
  pub value: u64,
  pub field: FiniteField
}

impl Add for FieldElement {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        self.field.add(&self, &rhs)
    }
}

impl Sub for FieldElement {
  type Output = Self;

  fn sub(self, rhs: Self) -> Self::Output {
      self.field.sub(&self, &rhs)
  }
}

impl Mul for FieldElement {
  type Output = Self;

  fn mul(self, rhs: Self) -> Self::Output {
    self.field.mul(&self, &rhs)
  }
}

impl Div for FieldElement {
  type Output = Self;

  fn div(self, rhs: Self) -> Self::Output {
      self.field.div(&self, &rhs)
  }
}

impl Neg for FieldElement {
    type Output = FieldElement;

    fn neg(self) -> Self::Output {
      self.field.neg(&self)
    }
}

impl PartialEq for FieldElement {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value && self.field == other.field
    }
    
    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl FiniteField {
  pub fn new(p: u64) -> Self {
    FiniteField { p: p }
  }

  pub fn new_element(&self, value: u64) -> FieldElement {
    FieldElement { value: value, field: *self }
  }

  pub fn modulus(&self) -> u64 {
    self.p
  }

  pub fn one(&self) -> FieldElement {
    FieldElement { value: 1, field: *self }
  }

  pub fn zero(&self) -> FieldElement {
    FieldElement { value: 0, field: *self }
  }

  pub fn mul(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
    let res = ((l.value as u128) * (r.value as u128)) % (self.p as u128);
    FieldElement { value: res as u64, field: *self }
  }

  pub fn add(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
    let res = ((l.value as u128) + (r.value as u128)) % (self.p as u128);
    FieldElement { value: res as u64, field: *self }
  }

  pub fn sub(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
    let res = ((self.p as u128) + (l.value as u128) - (r.value as u128)) % (self.p as u128);
    FieldElement { value: res as u64, field: *self }
  }

  pub fn neg(&self, op: &FieldElement) -> FieldElement {
    FieldElement { value: (self.p - op.value) % self.p, field: *self }
  }

  pub fn inv(&self, op: &FieldElement) -> FieldElement {
    let (g, x, _) = xgcd(op.value, self.p);
    assert!(g == 1, "no inverse");
    let p = self.p as i128;
    let inv = ((x % p) + p) % p; // normalize to [0, p-1]
    FieldElement { value: inv as u64, field: *self }
  }

  // rx + py = gcd(r,p) = 1, so x mod p = r^-1, therefore l/r ≡ lr^-1 ≡ lx mod p
  pub fn div(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
    assert!(r.value != 0, "no division by zero");
    let rinv = self.inv(&r);
    let val = (l.value as u128 * rinv.value as u128) % self.p as u128;
    FieldElement { value: val as u64, field: *self }
  }

  pub fn g(&self) -> FieldElement {
    assert!(self.p == 998244353);
    FieldElement { value: 3, field: *self }
  }

  // fast modular exponentiation based on Applied Cryptography book by Bruce Schneier
  pub fn exp(&self, base: &FieldElement, exp: u64) -> FieldElement {
    let mut res = self.one();
    let mut base = *base;
    let mut exp = exp;

    while exp > 0 {
      if exp % 2 == 1 {
        res = res * base;
      }
      base = base * base;
      exp >>= 1;
    }
    res
  }

  pub fn prim_nth_root(&self, n: u64) -> FieldElement {
    assert!(self.p == 998244353);
    assert!((n & (n-1)) == 0, "n must be a power of two");
    assert!(n <= (1 << 23), "n > 2^23 not supported by this modulus");
    // w_n = g^((p-1)/n)
    let g = self.g();
    let exp = (self.p - 1) / n; 
    self.exp(&g, exp)
  }

  pub fn sample(&self, salt: &[u8]) -> FieldElement {
    let mut acc = self.zero();
    for b in salt.iter() {
      acc.value = (((acc.value as u128) << 8) % self.p as u128) as u64;
      acc.value = (((acc.value as u128) ^ *b as u128) % self.p as u128) as u64;
    }
    acc
  }
}

#[cfg(test)]
mod tests {
    use super::*;

  const P: u64 = 998244353;

  #[test]
  pub fn test_exp() {
    let ff = FiniteField::new(P);
    let e = ff.new_element(3);
    assert_eq!(ff.exp(&e, 2), ff.new_element(9));
  }

  #[test]
  pub fn test_prim_nth_root() {
    let ff = FiniteField::new(P);
    let root = ff.prim_nth_root(8);
    assert!(ff.exp(&root, 8) == ff.one());
  }

}