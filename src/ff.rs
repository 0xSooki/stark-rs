#![allow(dead_code)]
use core::fmt;
use std::ops::{Add, BitXor, Div, Mul, Neg, Sub};

use crate::utils::xgcd;

#[derive(Debug, Clone, Copy)]
pub struct FiniteField {
    p: u64,
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
    pub field: FiniteField,
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
        FieldElement {
            value: value,
            field: *self,
        }
    }

    pub fn modulus(&self) -> u64 {
        self.p
    }

    pub fn one(&self) -> FieldElement {
        FieldElement {
            value: 1,
            field: *self,
        }
    }

    pub fn zero(&self) -> FieldElement {
        FieldElement {
            value: 0,
            field: *self,
        }
    }

    pub fn mul(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
        let res = ((l.value as u128) * (r.value as u128)) % (self.p as u128);
        FieldElement {
            value: res as u64,
            field: *self,
        }
    }

    pub fn add(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
        let res = ((l.value as u128) + (r.value as u128)) % (self.p as u128);
        FieldElement {
            value: res as u64,
            field: *self,
        }
    }

    pub fn sub(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
        let res = ((self.p as u128) + (l.value as u128) - (r.value as u128)) % (self.p as u128);
        FieldElement {
            value: res as u64,
            field: *self,
        }
    }

    pub fn neg(&self, op: &FieldElement) -> FieldElement {
        FieldElement {
            value: (self.p - op.value) % self.p,
            field: *self,
        }
    }

    pub fn inv(&self, op: &FieldElement) -> FieldElement {
        let (g, x, _) = xgcd(op.value, self.p);
        assert!(g == 1, "no inverse");
        let p = self.p as i128;
        let inv = ((x % p) + p) % p; // normalize to [0, p-1]
        FieldElement {
            value: inv as u64,
            field: *self,
        }
    }

    // rx + py = gcd(r,p) = 1, so x mod p = r^-1, therefore l/r ≡ lr^-1 ≡ lx mod p
    pub fn div(&self, l: &FieldElement, r: &FieldElement) -> FieldElement {
        assert!(r.value != 0, "no division by zero");
        let rinv = self.inv(&r);
        let val = (l.value as u128 * rinv.value as u128) % self.p as u128;
        FieldElement {
            value: val as u64,
            field: *self,
        }
    }

    pub fn g(&self) -> FieldElement {
        assert!(self.p == 998244353);
        FieldElement {
            value: 3,
            field: *self,
        }
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
        assert!((n & (n - 1)) == 0, "n must be a power of two");
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

impl Add<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn add(self, rhs: &FieldElement) -> Self::Output {
        self.field.add(&self, &rhs)
    }
}

impl Sub<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn sub(self, rhs: &FieldElement) -> Self::Output {
        self.field.sub(&self, &rhs)
    }
}

impl Mul<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn mul(self, rhs: &FieldElement) -> Self::Output {
        self.field.mul(&self, &rhs)
    }
}

impl Div<&FieldElement> for &FieldElement {
    type Output = FieldElement;

    fn div(self, rhs: &FieldElement) -> Self::Output {
        self.field.div(self, rhs)
    }
}

impl BitXor<u64> for &FieldElement {
    type Output = FieldElement;

    fn bitxor(self, rhs: u64) -> Self::Output {
        self.field.exp(self, rhs)
    }
}

impl Neg for &FieldElement {
    type Output = FieldElement;

    fn neg(self) -> Self::Output {
        self.field.neg(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = 998244353;

    #[test]
    fn test_field_creation() {
        let field = FiniteField::new(P);
        assert_eq!(field.modulus(), P);
    }

    #[test]
    fn test_element_creation() {
        let field = FiniteField::new(P);
        let elem = field.new_element(42);
        assert_eq!(elem.value, 42);
        assert_eq!(elem.field, field);
    }

    #[test]
    fn test_zero_and_one() {
        let field = FiniteField::new(P);
        let zero = field.zero();
        let one = field.one();

        assert_eq!(zero.value, 0);
        assert_eq!(one.value, 1);
        assert_ne!(zero, one);
    }

    #[test]
    fn test_field_equality() {
        let field1 = FiniteField::new(P);
        let field2 = FiniteField::new(P);
        let field3 = FiniteField::new(P - 1);

        assert_eq!(field1, field2);
        assert_ne!(field1, field3);
    }

    #[test]
    fn test_element_equality() {
        let field = FiniteField::new(P);
        let a = field.new_element(100);
        let b = field.new_element(100);
        let c = field.new_element(200);

        assert_eq!(a, b);
        assert_ne!(a, c);
    }

    #[test]
    fn test_element_equality_different_fields() {
        let field1 = FiniteField::new(P);
        let field2 = FiniteField::new(P - 1);
        let a = field1.new_element(100);
        let b = field2.new_element(100);

        assert_ne!(a, b);
    }

    #[test]
    fn test_addition_basic() {
        let field = FiniteField::new(P);
        let a = field.new_element(100);
        let b = field.new_element(200);
        let c = field.add(&a, &b);

        assert_eq!(c.value, 300);

        let d = a + b;
        assert_eq!(c, d);
    }

    #[test]
    fn test_addition_modular() {
        let field = FiniteField::new(P);
        let a = field.new_element(P - 1);
        let b = field.new_element(5);
        let result = field.add(&a, &b);
        assert_eq!(result.value, 4);
    }

    #[test]
    fn test_addition_zero() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let zero = field.zero();

        let result1 = field.add(&a, &zero);
        let result2 = field.add(&zero, &a);

        assert_eq!(result1, a);
        assert_eq!(result2, a);
    }

    #[test]
    fn test_addition_commutativity() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let b = field.new_element(456);

        let result1 = field.add(&a, &b);
        let result2 = field.add(&b, &a);

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_subtraction_basic() {
        let field = FiniteField::new(P);
        let a = field.new_element(200);
        let b = field.new_element(100);
        let c = field.sub(&a, &b);

        assert_eq!(c.value, 100);

        let d = a - b;
        assert_eq!(c, d);
    }

    #[test]
    fn test_subtraction_underflow() {
        let field = FiniteField::new(P);
        let a = field.new_element(5);
        let b = field.new_element(10);
        let result = field.sub(&a, &b);
        assert_eq!(result.value, P - 5);
    }

    #[test]
    fn test_subtraction_zero() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let zero = field.zero();

        let result1 = field.sub(&a, &zero);
        let result2 = field.sub(&zero, &a);

        assert_eq!(result1, a);
        assert_eq!(result2.value, P - 123);
    }

    #[test]
    fn test_multiplication_basic() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let b = field.new_element(456);
        let c = field.mul(&a, &b);

        assert_eq!(c.value, (123 * 456) % P);

        let d = a * b;
        assert_eq!(c, d);
    }

    #[test]
    fn test_multiplication_zero() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let zero = field.zero();

        let result1 = field.mul(&a, &zero);
        let result2 = field.mul(&zero, &a);

        assert_eq!(result1, zero);
        assert_eq!(result2, zero);
    }

    #[test]
    fn test_multiplication_one() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let one = field.one();

        let result1 = field.mul(&a, &one);
        let result2 = field.mul(&one, &a);

        assert_eq!(result1, a);
        assert_eq!(result2, a);
    }

    #[test]
    fn test_multiplication_large() {
        let field = FiniteField::new(P);
        let a = field.new_element(1000000);
        let b = field.new_element(2000000);
        let result = field.mul(&a, &b);
        assert_eq!(result.value, (2000000000000u128 % P as u128) as u64);
    }

    #[test]
    fn test_multiplication_commutativity() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let b = field.new_element(456);

        let result1 = field.mul(&a, &b);
        let result2 = field.mul(&b, &a);

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_negation() {
        let field = FiniteField::new(P);
        let a = field.new_element(100);
        let neg_a = field.neg(&a);

        assert_eq!(neg_a.value, P - 100);

        let neg_a2 = -a;
        assert_eq!(neg_a, neg_a2);
    }

    #[test]
    fn test_negation_zero() {
        let field = FiniteField::new(P);
        let zero = field.zero();
        let neg_zero = field.neg(&zero);
        assert_eq!(neg_zero, zero);
    }

    #[test]
    fn test_negation_additive_inverse() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let neg_a = field.neg(&a);
        let sum = field.add(&a, &neg_a);
        assert_eq!(sum, field.zero());
    }

    #[test]
    fn test_double_negation() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let neg_neg_a = field.neg(&field.neg(&a));
        assert_eq!(neg_neg_a, a);
    }

    #[test]
    fn test_inverse() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let inv_a = field.inv(&a);

        let product = field.mul(&a, &inv_a);
        assert_eq!(product, field.one());
    }

    #[test]
    fn test_inverse_one() {
        let field = FiniteField::new(P);
        let one = field.one();
        let inv_one = field.inv(&one);
        assert_eq!(inv_one, one);
    }

    #[test]
    fn test_inverse_large() {
        let field = FiniteField::new(P);
        let a = field.new_element(P - 1);
        let inv_a = field.inv(&a);
        let product = field.mul(&a, &inv_a);
        assert_eq!(product, field.one());
    }

    #[test]
    #[should_panic(expected = "no inverse")]
    fn test_inverse_zero_panics() {
        let field = FiniteField::new(P);
        let zero = field.zero();
        field.inv(&zero);
    }

    #[test]
    fn test_division() {
        let field = FiniteField::new(P);
        let a = field.new_element(1000);
        let b = field.new_element(25);
        let c = field.div(&a, &b);

        let product = field.mul(&c, &b);
        assert_eq!(product, a);

        let d = a / b;
        assert_eq!(c, d);
    }

    #[test]
    fn test_division_one() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let one = field.one();
        let result = field.div(&a, &one);
        assert_eq!(result, a);
    }

    #[test]
    #[should_panic(expected = "no division by zero")]
    fn test_division_by_zero_panics() {
        let field = FiniteField::new(P);
        let a = field.new_element(100);
        let zero = field.zero();
        field.div(&a, &zero);
    }

    #[test]
    pub fn test_exp() {
        let ff = FiniteField::new(P);
        let e = ff.new_element(3);
        assert_eq!(ff.exp(&e, 2), ff.new_element(9));
    }

    #[test]
    fn test_exp_zero_exponent() {
        let field = FiniteField::new(P);
        let base = field.new_element(123);
        let result = field.exp(&base, 0);
        assert_eq!(result, field.one());
    }

    #[test]
    fn test_exp_one_exponent() {
        let field = FiniteField::new(P);
        let base = field.new_element(123);
        let result = field.exp(&base, 1);
        assert_eq!(result, base);
    }

    #[test]
    fn test_exp_large() {
        let field = FiniteField::new(P);
        let base = field.new_element(3);
        let result = field.exp(&base, 100);
        assert!(result.value < P);
    }

    #[test]
    fn test_exp_power_of_two() {
        let field = FiniteField::new(P);
        let base = field.new_element(2);
        let result = field.exp(&base, 10);
        assert_eq!(result.value, 1024);
    }

    #[test]
    fn test_generator() {
        let field = FiniteField::new(P);
        let g = field.g();
        assert_eq!(g.value, 3);
    }

    #[test]
    #[should_panic]
    fn test_generator_wrong_field() {
        let field = FiniteField::new(2147483647);
        field.g();
    }

    #[test]
    pub fn test_prim_nth_root() {
        let ff = FiniteField::new(P);
        let root = ff.prim_nth_root(8);
        assert!(ff.exp(&root, 8) == ff.one());
    }

    #[test]
    fn test_prim_nth_root_powers_of_two() {
        let field = FiniteField::new(P);

        for i in 1..=10 {
            let n = 1u64 << i;
            let root = field.prim_nth_root(n);
            let result = field.exp(&root, n);
            assert_eq!(result, field.one());
        }
    }

    #[test]
    fn test_prim_nth_root_primitive() {
        let field = FiniteField::new(P);
        let root = field.prim_nth_root(8);

        for i in 1..8 {
            let power = field.exp(&root, i);
            assert_ne!(power, field.one());
        }
    }

    #[test]
    fn test_prim_nth_root_different_orders() {
        let field = FiniteField::new(P);

        let root2 = field.prim_nth_root(2);
        let root4 = field.prim_nth_root(4);
        let root8 = field.prim_nth_root(8);

        assert_eq!(field.exp(&root2, 2), field.one());
        assert_eq!(field.exp(&root4, 4), field.one());
        assert_eq!(field.exp(&root8, 8), field.one());

        assert_ne!(root2, root4);
        assert_ne!(root4, root8);
        assert_ne!(root2, root8);
    }

    #[test]
    #[should_panic]
    fn test_prim_nth_root_wrong_field() {
        let field = FiniteField::new(2147483647);
        field.prim_nth_root(8);
    }

    #[test]
    #[should_panic(expected = "n must be a power of two")]
    fn test_prim_nth_root_not_power_of_two() {
        let field = FiniteField::new(P);
        field.prim_nth_root(6);
    }

    #[test]
    #[should_panic(expected = "n > 2^23 not supported")]
    fn test_prim_nth_root_too_large() {
        let field = FiniteField::new(P);
        field.prim_nth_root(1 << 24);
    }

    #[test]
    fn test_sample_empty() {
        let field = FiniteField::new(P);
        let result = field.sample(&[]);
        assert_eq!(result, field.zero());
    }

    #[test]
    fn test_sample_single_byte() {
        let field = FiniteField::new(P);
        let result = field.sample(&[42]);
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_sample_multiple_bytes() {
        let field = FiniteField::new(P);
        let result = field.sample(&[1, 2, 3]);
        assert!(result.value < P);
    }

    #[test]
    fn test_sample_deterministic() {
        let field = FiniteField::new(P);
        let result1 = field.sample(&[1, 2, 3, 4]);
        let result2 = field.sample(&[1, 2, 3, 4]);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_sample_different_inputs() {
        let field = FiniteField::new(P);
        let result1 = field.sample(&[1, 2, 3, 4]);
        let result2 = field.sample(&[1, 2, 3, 5]);
        assert_ne!(result1, result2);
    }

    #[test]
    fn test_sample_large_input() {
        let field = FiniteField::new(P);
        let large_input: Vec<u8> = (0..100).collect();
        let result = field.sample(&large_input);
        assert!(result.value < P);
    }

    #[test]
    fn test_sample_max_bytes() {
        let field = FiniteField::new(P);
        let max_bytes = vec![255u8; 10];
        let result = field.sample(&max_bytes);
        assert!(result.value < P);
    }

    #[test]
    fn test_field_arithmetic_properties() {
        let field = FiniteField::new(P);
        let a = field.new_element(123);
        let b = field.new_element(456);
        let c = field.new_element(789);
        let zero = field.zero();
        let one = field.one();

        assert_eq!(field.add(&a, &zero), a);
        assert_eq!(field.add(&zero, &a), a);
        assert_eq!(field.mul(&a, &one), a);
        assert_eq!(field.mul(&one, &a), a);

        let add1 = field.add(&field.add(&a, &b), &c);
        let add2 = field.add(&a, &field.add(&b, &c));
        assert_eq!(add1, add2);

        let mul1 = field.mul(&field.mul(&a, &b), &c);
        let mul2 = field.mul(&a, &field.mul(&b, &c));
        assert_eq!(mul1, mul2);

        let left = field.mul(&a, &field.add(&b, &c));
        let right = field.add(&field.mul(&a, &b), &field.mul(&a, &c));
        assert_eq!(left, right);
    }
}
