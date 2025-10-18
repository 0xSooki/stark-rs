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

    pub fn zerofier(domain: &Vec<FieldElement>) -> Polynomial {
        let field = domain[0].field;
        let x = Polynomial {
            coeffs: vec![field.zero(), field.one()],
            field: field,
        };
        let mut acc = Polynomial {
            coeffs: vec![field.one()],
            field: field,
        };
        for d in domain {
            acc = &acc
                * &(&x
                    - &Polynomial {
                        coeffs: vec![*d],
                        field: field,
                    });
        }
        acc
    }

    // computer f(c*X)
    pub fn scale(&self, factor: &FieldElement) -> Polynomial {
        let coeffs: Vec<FieldElement> = self
            .coeffs
            .iter()
            .enumerate()
            .map(|(i, &coeff)| {
                let power = self.field.exp(factor, i as u64);
                &power * &coeff
            })
            .collect();
        Polynomial {
            coeffs: coeffs,
            field: self.field,
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
mod div;
mod eval;
mod exp;
mod interpolate;
mod mul;
mod sub;

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
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(0),
            ],
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

    #[test]
    fn test_zerofier_single_point() {
        let field = setup_field();
        let domain = vec![field.new_element(5)];

        let zerofier = Polynomial::zerofier(&domain);

        assert_eq!(zerofier.deg(), 1);
        assert_eq!(zerofier.coeffs[0].value, P - 5);
        assert_eq!(zerofier.coeffs[1].value, 1);

        let eval = Polynomial::eval(&zerofier, &domain[0]);
        assert_eq!(eval.value, 0);
    }

    #[test]
    fn test_zerofier_two_points() {
        let field = setup_field();
        let domain = vec![field.new_element(2), field.new_element(3)];

        let zerofier = Polynomial::zerofier(&domain);

        assert_eq!(zerofier.deg(), 2);
        assert_eq!(zerofier.coeffs[0].value, 6);
        assert_eq!(zerofier.coeffs[1].value, P - 5);
        assert_eq!(zerofier.coeffs[2].value, 1);

        for point in &domain {
            let eval = Polynomial::eval(&zerofier, point);
            assert_eq!(eval.value, 0);
        }
    }

    #[test]
    fn test_zerofier_three_points() {
        let field = setup_field();
        let domain = vec![
            field.new_element(1),
            field.new_element(2),
            field.new_element(3),
        ];

        let zerofier = Polynomial::zerofier(&domain);

        assert_eq!(zerofier.deg(), 3);
        assert_eq!(zerofier.coeffs[0].value, P - 6);
        assert_eq!(zerofier.coeffs[1].value, 11);
        assert_eq!(zerofier.coeffs[2].value, P - 6);
        assert_eq!(zerofier.coeffs[3].value, 1);

        for point in &domain {
            let eval = Polynomial::eval(&zerofier, point);
            assert_eq!(eval.value, 0);
        }
    }

    #[test]
    fn test_zerofier_zero_point() {
        let field = setup_field();
        let domain = vec![field.new_element(0)];

        let zerofier = Polynomial::zerofier(&domain);

        assert_eq!(zerofier.deg(), 1);
        assert_eq!(zerofier.coeffs[0].value, 0);
        assert_eq!(zerofier.coeffs[1].value, 1);

        let eval = Polynomial::eval(&zerofier, &domain[0]);
        assert_eq!(eval.value, 0);
    }

    #[test]
    fn test_zerofier_nonzero_evaluation() {
        let field = setup_field();
        let domain = vec![field.new_element(1), field.new_element(2)];

        let zerofier = Polynomial::zerofier(&domain);

        let test_point = field.new_element(5);
        let eval = Polynomial::eval(&zerofier, &test_point);

        assert_eq!(eval.value, 12);
        assert_ne!(eval.value, 0);
    }

    #[test]
    fn test_zerofier_degree() {
        let field = setup_field();

        for n in 1..=5 {
            let domain: Vec<FieldElement> = (1..=n).map(|i| field.new_element(i as u64)).collect();
            let zerofier = Polynomial::zerofier(&domain);
            assert_eq!(zerofier.deg(), n as i128);
        }
    }

    #[test]
    fn test_scale_constant_polynomial() {
        let field = setup_field();
        let poly = constant_poly(&field, 5);
        let c = field.new_element(3);

        let scaled = poly.scale(&c);
        assert_eq!(scaled.deg(), 0);
        assert_eq!(scaled.coeffs[0].value, 5);
    }

    #[test]
    fn test_scale_linear_polynomial() {
        let field = setup_field();
        let poly = linear_poly(&field, 2, 3);
        let c = field.new_element(5);

        let scaled = poly.scale(&c);
        assert_eq!(scaled.deg(), 1);
        assert_eq!(scaled.coeffs[0].value, 2);
        assert_eq!(scaled.coeffs[1].value, 15);
    }

    #[test]
    fn test_scale_quadratic_polynomial() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        let c = field.new_element(2);

        let scaled = poly.scale(&c);
        assert_eq!(scaled.deg(), 2);
        assert_eq!(scaled.coeffs[0].value, 1);
        assert_eq!(scaled.coeffs[1].value, 4);
        assert_eq!(scaled.coeffs[2].value, 12);
    }

    #[test]
    fn test_scale_evaluation_shift() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(1),
                field.new_element(1),
            ],
            field,
        );

        let c = field.new_element(2);

        for test_val in 1..=5 {
            let x = field.new_element(test_val);
            let cx = &c * &x;

            let scaled = poly.scale(&c);
            let eval_scaled_at_x = Polynomial::eval(&scaled, &x);
            let eval_original_at_cx = Polynomial::eval(&poly, &cx);

            assert_eq!(
                eval_scaled_at_x, eval_original_at_cx,
                "f(c·X) at X={} should equal f(X) at X={}",
                test_val,
                test_val * c.value
            );
        }
    }

    #[test]
    fn test_scale_sequence_shift() {
        let field = setup_field();
        let c = field.new_element(2);

        let values: Vec<FieldElement> = (0..4).map(|i| field.new_element(i)).collect();

        let domain: Vec<FieldElement> = (0..4).map(|i| field.exp(&c, i)).collect();

        let poly = Polynomial::interpolate_domain(&domain, &values);

        let scaled = poly.scale(&c);

        for i in 0..3 {
            let point = field.exp(&c, i);
            let eval_scaled = Polynomial::eval(&scaled, &point);

            let expected = field.new_element(i + 1);
            assert_eq!(
                eval_scaled, expected,
                "Scaled polynomial should shift sequence by one position"
            );
        }
    }

    #[test]
    fn test_scale_by_one() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );

        let one = field.one();

        let scaled = poly.scale(&one);
        assert_eq!(scaled, poly);
    }

    #[test]
    fn test_scale_zero_polynomial() {
        let field = setup_field();
        let zero = zero_poly(&field);
        let c = field.new_element(5);

        let scaled = zero.scale(&c);
        assert!(scaled.is_zero());
    }

    #[test]
    fn test_scale_preserves_degree() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
                field.new_element(4),
            ],
            field,
        );

        let c = field.new_element(7);
        let scaled = poly.scale(&c);

        assert_eq!(scaled.deg(), poly.deg());
    }
}
