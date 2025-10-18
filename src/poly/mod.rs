#![allow(unused)]

use std::{cmp::max, ops::Add};

use crate::ff::{FieldElement, FiniteField};

#[derive(Debug, Clone)]
pub struct Polynomial {
    pub coeffs: Vec<FieldElement>,
    pub field: FiniteField,
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        if self.deg() != other.deg() {
            return false;
        }
        if self.deg() == -1 {
            return true;
        }
        
        let max_degree = self.deg() as usize;
        for i in 0..=max_degree {
            let self_coeff = if i < self.coeffs.len() {
                self.coeffs[i]
            } else {
                self.field.zero()
            };
            let other_coeff = if i < other.coeffs.len() {
                other.coeffs[i]
            } else {
                other.field.zero()
            };
            if self_coeff != other_coeff {
                return false;
            }
        }
        true
    }

    fn ne(&self, other: &Self) -> bool {
        !self.eq(other)
    }
}

impl Polynomial {
    pub fn new(coeffs: Vec<FieldElement>, field: FiniteField) -> Polynomial {
        Polynomial {
            coeffs: coeffs,
            field: field,
        }
    }

    pub fn deg(&self) -> i128 {
        if self.coeffs.len() == 0 {
            return -1;
        }
        if self.coeffs.iter().all(|&c| c == c.field.zero()) {
            return -1;
        }
        let mut maxidx = 0;
        for (i, k) in self.coeffs.iter().enumerate() {
            if *k != k.field.zero() {
                maxidx = i;
            }
        }
        maxidx as i128
    }

    pub fn neg(poly: &Polynomial) -> Polynomial {
        Polynomial {
            coeffs: poly.coeffs.iter().map(|&c| -c).collect(),
            field: poly.field,
        }
    }

    fn assert_same_field(p1: &Polynomial, p2: &Polynomial) {
        assert_eq!(
            p1.field, p2.field,
            "Polynomials must be from the same field"
        );
    }

    pub fn is_zero(&self) -> bool {
        self.deg() == -1
    }

    pub fn leading_coeff(&self) -> FieldElement {
        if self.is_zero() {
            panic!("Zero polynomial has no leading coefficient");
        }
        self.coeffs[self.deg() as usize]
    }
}

mod add;
mod sub;
mod mul;
mod div;
mod exp;
mod eval;
mod interpolate;



#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::FiniteField;

    const P: u64 = 998244353;

    fn setup_field() -> FiniteField {
        FiniteField::new(P)
    }

    fn zero_poly(field: &FiniteField) -> Polynomial {
        Polynomial::new(vec![], *field)
    }

    fn constant_poly(field: &FiniteField, value: u64) -> Polynomial {
        Polynomial::new(vec![field.new_element(value)], *field)
    }

    fn linear_poly(field: &FiniteField, a: u64, b: u64) -> Polynomial {
        Polynomial::new(vec![field.new_element(a), field.new_element(b)], *field)
    }

    #[test]
    fn test_polynomial_creation() {
        let field = setup_field();

        let empty = Polynomial::new(vec![], field);
        assert_eq!(empty.coeffs.len(), 0);

        let constant = Polynomial::new(vec![field.new_element(5)], field);
        assert_eq!(constant.coeffs.len(), 1);
        assert_eq!(constant.coeffs[0].value, 5);

        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        assert_eq!(poly.coeffs.len(), 3);
    }

    #[test]
    fn test_degree() {
        let field = setup_field();

        let zero = zero_poly(&field);
        assert_eq!(zero.deg(), -1);

        let constant = constant_poly(&field, 5);
        assert_eq!(constant.deg(), 0);

        let linear = linear_poly(&field, 1, 2);
        assert_eq!(linear.deg(), 1);

        let quadratic = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        assert_eq!(quadratic.deg(), 2);

        let with_trailing_zeros = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(0),
                field.new_element(0),
            ],
            field,
        );
        assert_eq!(with_trailing_zeros.deg(), 1);
    }

    #[test]
    fn test_is_zero() {
        let field = setup_field();

        let zero = zero_poly(&field);
        assert!(zero.is_zero());

        let constant = constant_poly(&field, 5);
        assert!(!constant.is_zero());

        let all_zeros = Polynomial::new(vec![field.new_element(0), field.new_element(0)], field);
        assert!(all_zeros.is_zero());
    }

    #[test]
    fn test_leading_coefficient() {
        let field = setup_field();

        let linear = linear_poly(&field, 1, 2);
        assert_eq!(linear.leading_coeff().value, 2);

        let quadratic = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        assert_eq!(quadratic.leading_coeff().value, 3);

        let with_trailing_zeros = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(0),
                field.new_element(0),
            ],
            field,
        );
        assert_eq!(with_trailing_zeros.leading_coeff().value, 2);
    }

    #[test]
    #[should_panic(expected = "Zero polynomial has no leading coefficient")]
    fn test_leading_coefficient_zero_poly() {
        let field = setup_field();
        let zero = zero_poly(&field);
        zero.leading_coeff();
    }

    #[test]
    fn test_equality() {
        let field = setup_field();

        let poly1 = linear_poly(&field, 1, 2);
        let poly2 = linear_poly(&field, 1, 2);
        assert_eq!(poly1, poly2);

        let poly3 = linear_poly(&field, 1, 3);
        assert_ne!(poly1, poly3);

        let poly4 = Polynomial::new(
            vec![field.new_element(1), field.new_element(2), field.new_element(0)],
            field,
        );
        assert_eq!(poly1, poly4);
    }

    #[test]
    fn test_negation() {
        let field = setup_field();

        let poly = linear_poly(&field, 3, 4);
        let neg = Polynomial::neg(&poly);

        assert_eq!(neg.deg(), 1);
        assert_eq!(neg.coeffs[0].value, P - 3);
        assert_eq!(neg.coeffs[1].value, P - 4);

        let sum = Polynomial::add(&poly, &neg);
        assert!(sum.is_zero());
    }
}