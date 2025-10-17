#![allow(unused)]

use std::{cmp::max, ops::Add};

use crate::ff::{FieldElement, FiniteField};

#[derive(Debug, Clone)]
pub struct Polynomial {
    coeffs: Vec<FieldElement>,
    field: FiniteField,
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

    pub fn add(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.deg() == -1 {
            return rhs.clone();
        }
        if rhs.deg() == -1 {
            return lhs.clone();
        }
        let mut coeffs: Vec<FieldElement> =
            vec![lhs.coeffs[0].field.zero(); max(lhs.coeffs.len(), rhs.coeffs.len())];
        for i in 0..coeffs.len() {
            let left = lhs
                .coeffs
                .get(i)
                .copied()
                .unwrap_or_else(|| lhs.coeffs[0].field.zero());
            let right = rhs
                .coeffs
                .get(i)
                .copied()
                .unwrap_or_else(|| rhs.coeffs[0].field.zero());
            coeffs[i] = left + right;
        }
        Polynomial {
            coeffs: coeffs,
            field: lhs.field,
        }
    }

    pub fn neg(poly: &Polynomial) -> Polynomial {
        Polynomial {
            coeffs: poly.coeffs.iter().map(|&c| -c).collect(),
            field: poly.field,
        }
    }

    pub fn sub(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.deg() == -1 {
            return Self::neg(rhs);
        }
        if rhs.deg() == -1 {
            return lhs.clone();
        }
        let mut coeffs: Vec<FieldElement> =
            vec![lhs.coeffs[0].field.zero(); max(lhs.coeffs.len(), rhs.coeffs.len())];
        for i in 0..coeffs.len() {
            let left = lhs
                .coeffs
                .get(i)
                .copied()
                .unwrap_or_else(|| lhs.coeffs[0].field.zero());
            let right = rhs
                .coeffs
                .get(i)
                .copied()
                .unwrap_or_else(|| rhs.coeffs[0].field.zero());
            coeffs[i] = left - right;
        }
        Polynomial {
            coeffs: coeffs,
            field: lhs.field,
        }
    }

    pub fn mul(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.is_zero() || rhs.is_zero() {
            return Polynomial {
                coeffs: vec![],
                field: lhs.field,
            };
        }

        let mut coeffs = vec![lhs.coeffs[0].field.zero(); lhs.coeffs.len() + rhs.coeffs.len() - 1];

        for (i, &a) in lhs.coeffs.iter().enumerate() {
            if a.value == 0 {
                continue;
            } else {
                for (j, &b) in rhs.coeffs.iter().enumerate() {
                    coeffs[i + j] = coeffs[i + j] + a * b
                }
            }
        }
        return Polynomial {
            coeffs: coeffs,
            field: lhs.field,
        };
    }

    pub fn div(numer: &Polynomial, denom: &Polynomial) -> (Polynomial, Polynomial) {
        if denom.deg() == -1 {
            panic!("No division by zero")
        }
        if numer.deg() < denom.deg() {
            return (
                Polynomial {
                    coeffs: vec![],
                    field: numer.field,
                },
                numer.clone(),
            );
        }

        let field = denom.coeffs[0].field;
        let mut q = vec![field.zero(); (numer.deg() - denom.deg() + 1) as usize];
        let mut r = numer.clone();

        while r.deg() >= denom.deg() {
            let coeff = r.leading_coeff() / denom.leading_coeff();
            let shift = (r.deg() - denom.deg()) as usize;
            let mut subtractee_coeffs = vec![field.zero(); shift];
            subtractee_coeffs.push(coeff);
            let subtractee_poly = Polynomial::new(subtractee_coeffs, numer.field);
            let subtractee = Polynomial::mul(&subtractee_poly, denom);
            q[shift] = coeff;
            r = Polynomial::sub(&r, &subtractee);
        }
        (
            Polynomial {
                coeffs: q,
                field: numer.field,
            },
            r,
        )
    }

    pub fn intdiv(numer: &Polynomial, denom: &Polynomial) -> Polynomial {
        let (q, r) = Self::div(numer, denom);
        assert!(r.is_zero());
        q
    }

    pub fn modulo(numer: &Polynomial, denom: &Polynomial) -> Polynomial {
        let (q, r) = Self::div(numer, denom);
        r
    }

    pub fn exp(base: &Polynomial, exp: u64) -> Polynomial {
        let mut exp = exp;
        if exp == 0 {
            return Polynomial {
                coeffs: vec![base.field.one()],
                field: base.field,
            };
        }
        if base.is_zero() {
            return Polynomial {
                coeffs: vec![],
                field: base.field,
            };
        }
        let mut result = Polynomial {
            coeffs: vec![base.field.one()],
            field: base.field,
        };
        let mut bpower = base.clone();
        while exp != 0 {
            if (exp & 1) == 1 {
                result = Self::mul(&result, base);
            }
            bpower = Self::mul(&bpower, &bpower);
            exp >>= 1;
        }
        result
    }

    pub fn eval(&self, x: &FieldElement) -> FieldElement {
        let mut xi = x.field.one();
        let mut val = x.field.zero();
        for c in &self.coeffs {
            val = val + (*c) * xi;
            xi = xi * (*x);
        }
        val
    }

    pub fn eval_domain(&self, domain: &Vec<FieldElement>) -> Vec<FieldElement> {
        domain
            .iter()
            .map(|x| Self::eval(self, x))
            .collect::<Vec<FieldElement>>()
    }

    pub fn interpolate_domain(
        domain: &Vec<FieldElement>,
        values: &Vec<FieldElement>,
    ) -> Polynomial {
        assert!(domain.len() == values.len());
        assert!(domain.len() > 0);
        let field = domain[0].field;
        let mut x = Polynomial {
            coeffs: vec![field.zero(), field.one()],
            field: field,
        };
        let mut acc = Polynomial {
            coeffs: vec![],
            field: field,
        };
        for i in 0..domain.len() {
            let mut prod = Polynomial {
                coeffs: vec![values[i]],
                field: field,
            };
            for j in 0..domain.len() {
                if j == i {
                    continue;
                }
                prod = prod
            }
        }
        acc
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
        self.coeffs[self.deg() as usize]
    }
}
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

        let all_zeros = Polynomial::new(vec![field.zero(), field.zero(), field.zero()], field);
        assert_eq!(all_zeros.deg(), -1);

        let constant = constant_poly(&field, 5);
        assert_eq!(constant.deg(), 0);

        let linear = linear_poly(&field, 1, 2);
        assert_eq!(linear.deg(), 1);

        let with_zeros = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.zero(),
                field.zero(),
            ],
            field,
        );
        assert_eq!(with_zeros.deg(), 1);

        let cubic = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(0),
                field.new_element(0),
                field.new_element(7),
            ],
            field,
        );
        assert_eq!(cubic.deg(), 3);
    }

    #[test]
    fn test_is_zero() {
        let field = setup_field();

        assert!(zero_poly(&field).is_zero());

        let all_zeros = Polynomial::new(vec![field.zero(), field.zero()], field);
        assert!(all_zeros.is_zero());

        let non_zero = constant_poly(&field, 1);
        assert!(!non_zero.is_zero());

        let mixed = Polynomial::new(vec![field.zero(), field.new_element(1)], field);
        assert!(!mixed.is_zero());
    }

    #[test]
    fn test_leading_coefficient() {
        let field = setup_field();

        let constant = constant_poly(&field, 7);
        assert_eq!(constant.leading_coeff().value, 7);

        let linear = linear_poly(&field, 3, 5);
        assert_eq!(linear.leading_coeff().value, 5);

        let with_zeros = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.zero(),
                field.zero(),
            ],
            field,
        );
        assert_eq!(with_zeros.leading_coeff().value, 2);
    }

    #[test]
    #[should_panic]
    fn test_leading_coefficient_zero_poly() {
        let field = setup_field();
        let zero = zero_poly(&field);
        zero.leading_coeff();
    }

    #[test]
    fn test_equality() {
        let field = setup_field();

        let p1 = linear_poly(&field, 1, 2);
        let p2 = linear_poly(&field, 1, 2);
        assert_eq!(p1, p2);

        let p3 = linear_poly(&field, 1, 3);
        assert_ne!(p1, p3);

        let p4 = constant_poly(&field, 1);
        assert_ne!(p1, p4);

        let z1 = zero_poly(&field);
        let z2 = Polynomial::new(vec![field.zero()], field);
        assert_ne!(z1, z2);
    }

    #[test]
    fn test_addition_basic() {
        let field = setup_field();

        let p1 = linear_poly(&field, 1, 2);
        let p2 = linear_poly(&field, 3, 4);
        let result = Polynomial::add(&p1, &p2);

        assert_eq!(result.coeffs.len(), 2);
        assert_eq!(result.coeffs[0].value, 4);
        assert_eq!(result.coeffs[1].value, 6);

        let constant = constant_poly(&field, 5);
        let linear = linear_poly(&field, 2, 3);
        let result2 = Polynomial::add(&constant, &linear);

        assert_eq!(result2.coeffs.len(), 2);
        assert_eq!(result2.coeffs[0].value, 7);
        assert_eq!(result2.coeffs[1].value, 3);
    }

    #[test]
    fn test_addition_zero_cases() {
        let field = setup_field();

        let p = linear_poly(&field, 1, 2);
        let zero = zero_poly(&field);
        let result1 = Polynomial::add(&p, &zero);
        let result2 = Polynomial::add(&zero, &p);

        assert_eq!(result1, p);
        assert_eq!(result2, p);

        let zero_result = Polynomial::add(&zero, &zero);
        assert!(zero_result.is_zero());
    }

    #[test]
    fn test_addition_different_lengths() {
        let field = setup_field();

        let short = constant_poly(&field, 5);
        let long = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );

        let result = Polynomial::add(&short, &long);
        assert_eq!(result.coeffs.len(), 3);
        assert_eq!(result.coeffs[0].value, 6);
        assert_eq!(result.coeffs[1].value, 2);
        assert_eq!(result.coeffs[2].value, 3);
    }

    #[test]
    fn test_negation() {
        let field = setup_field();

        let p = linear_poly(&field, 3, 5);
        let neg_p = Polynomial::neg(&p);

        assert_eq!(neg_p.coeffs.len(), 2);
        assert_eq!(neg_p.coeffs[0].value, P - 3);
        assert_eq!(neg_p.coeffs[1].value, P - 5);

        let zero = zero_poly(&field);
        let neg_zero = Polynomial::neg(&zero);
        assert!(neg_zero.is_zero());

        let double_neg = Polynomial::neg(&neg_p);
        assert_eq!(double_neg, p);
    }

    #[test]
    fn test_subtraction_basic() {
        let field = setup_field();

        let p1 = linear_poly(&field, 5, 7);
        let p2 = linear_poly(&field, 2, 3);
        let result = Polynomial::sub(&p1, &p2);

        assert_eq!(result.coeffs.len(), 2);
        assert_eq!(result.coeffs[0].value, 3);
        assert_eq!(result.coeffs[1].value, 4);
    }

    #[test]
    fn test_subtraction_zero_cases() {
        let field = setup_field();

        let p = linear_poly(&field, 1, 2);
        let zero = zero_poly(&field);
        let result = Polynomial::sub(&zero, &p);

        let expected = Polynomial::neg(&p);
        assert_eq!(result.coeffs.len(), expected.coeffs.len());
        assert_eq!(result.coeffs[0].value, expected.coeffs[0].value);
        assert_eq!(result.coeffs[1].value, expected.coeffs[1].value);

        let result2 = Polynomial::sub(&p, &zero);
        assert_eq!(result2, p);
    }

    #[test]
    fn test_subtraction_underflow() {
        let field = setup_field();

        let p1 = constant_poly(&field, 2);
        let p2 = constant_poly(&field, 5);
        let result = Polynomial::sub(&p1, &p2);

        assert_eq!(result.coeffs[0].value, P - 3);
    }

    #[test]
    fn test_multiplication_basic() {
        let field = setup_field();

        let p1 = constant_poly(&field, 3);
        let p2 = constant_poly(&field, 4);
        let result = Polynomial::mul(&p1, &p2);

        assert_eq!(result.coeffs.len(), 1);
        assert_eq!(result.coeffs[0].value, 12);

        let linear = linear_poly(&field, 2, 3);
        let constant = constant_poly(&field, 4);
        let result2 = Polynomial::mul(&linear, &constant);

        assert_eq!(result2.coeffs.len(), 2);
        assert_eq!(result2.coeffs[0].value, 8);
        assert_eq!(result2.coeffs[1].value, 12);
    }

    #[test]
    fn test_multiplication_linear() {
        let field = setup_field();

        let p1 = linear_poly(&field, 1, 2);
        let p2 = linear_poly(&field, 3, 4);
        let result = Polynomial::mul(&p1, &p2);

        assert_eq!(result.coeffs.len(), 3);
        assert_eq!(result.coeffs[0].value, 3);
        assert_eq!(result.coeffs[1].value, 10);
        assert_eq!(result.coeffs[2].value, 8);
    }

    #[test]
    fn test_multiplication_zero_cases() {
        let field = setup_field();

        let p = linear_poly(&field, 1, 2);
        let zero = zero_poly(&field);
        let result1 = Polynomial::mul(&p, &zero);
        let result2 = Polynomial::mul(&zero, &p);

        assert!(result1.is_zero());
        assert!(result2.is_zero());

        let zero_result = Polynomial::mul(&zero, &zero);
        assert!(zero_result.is_zero());
    }

    #[test]
    fn test_multiplication_with_zero_coefficients() {
        let field = setup_field();

        let p1 = Polynomial::new(
            vec![field.new_element(1), field.zero(), field.new_element(3)],
            field,
        );
        let p2 = constant_poly(&field, 2);

        let result = Polynomial::mul(&p1, &p2);
        assert_eq!(result.coeffs.len(), 3);
        assert_eq!(result.coeffs[0].value, 2);
        assert_eq!(result.coeffs[1].value, 0);
        assert_eq!(result.coeffs[2].value, 6);
    }

    #[test]
    fn test_large_coefficients() {
        let field = setup_field();

        let large1 = field.new_element(P - 1);
        let large2 = field.new_element(P - 2);

        let p1 = Polynomial::new(vec![large1], field);
        let p2 = Polynomial::new(vec![large2], field);

        let result = Polynomial::mul(&p1, &p2);
        assert_eq!(result.coeffs[0].value, 2);
    }

    #[test]
    fn test_arithmetic_properties() {
        let field = setup_field();

        let p1 = linear_poly(&field, 1, 2);
        let p2 = linear_poly(&field, 3, 4);
        let p3 = constant_poly(&field, 5);
        let zero = zero_poly(&field);

        let add1 = Polynomial::add(&p1, &p2);
        let add2 = Polynomial::add(&p2, &p1);
        assert_eq!(add1, add2);

        let assoc1 = Polynomial::add(&Polynomial::add(&p1, &p2), &p3);
        let assoc2 = Polynomial::add(&p1, &Polynomial::add(&p2, &p3));
        assert_eq!(assoc1, assoc2);

        let id1 = Polynomial::add(&p1, &zero);
        let id2 = Polynomial::add(&zero, &p1);
        assert_eq!(id1, p1);
        assert_eq!(id2, p1);

        let mul1 = Polynomial::mul(&p1, &p2);
        let mul2 = Polynomial::mul(&p2, &p1);
        assert_eq!(mul1, mul2);

        let sub1 = Polynomial::sub(&p1, &p2);
        let sub2 = Polynomial::add(&p1, &Polynomial::neg(&p2));
        assert_eq!(sub1, sub2);
    }

    #[test]
    fn test_edge_case_single_zero_coefficient() {
        let field = setup_field();

        let single_zero = Polynomial::new(vec![field.zero()], field);
        let p = constant_poly(&field, 5);
        let result = Polynomial::add(&single_zero, &p);

        assert!(result.coeffs.len() > 0);
    }

    #[test]
    fn test_polynomial_coefficient_resultess() {
        let field = setup_field();

        let short = constant_poly(&field, 3);
        let long = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
                field.new_element(4),
            ],
            field,
        );

        let result = Polynomial::add(&short, &long);

        assert_eq!(result.coeffs.len(), 4);
        assert_eq!(result.coeffs[0].value, 4);
        assert_eq!(result.coeffs[1].value, 2);
        assert_eq!(result.coeffs[2].value, 3);
        assert_eq!(result.coeffs[3].value, 4);
    }

    #[test]
    fn test_zero_polynomial_representations() {
        let field = setup_field();

        let empty = zero_poly(&field);
        let single_zero = Polynomial::new(vec![field.zero()], field);
        let multiple_zeros = Polynomial::new(vec![field.zero(), field.zero(), field.zero()], field);

        assert!(empty.is_zero());
        assert!(single_zero.is_zero());
        assert!(multiple_zeros.is_zero());

        assert_eq!(empty.deg(), -1);
        assert_eq!(single_zero.deg(), -1);
        assert_eq!(multiple_zeros.deg(), -1);
    }

    #[test]
    fn test_polynomial_normalization() {
        let field = setup_field();

        let p_with_trailing_zeros = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.zero(),
                field.zero(),
                field.zero(),
            ],
            field,
        );

        assert_eq!(p_with_trailing_zeros.deg(), 1);
        assert_eq!(p_with_trailing_zeros.leading_coeff().value, 2);
    }

    #[test]
    fn test_multiplication_distributive() {
        let field = setup_field();

        let a = linear_poly(&field, 1, 2);
        let b = linear_poly(&field, 3, 4);
        let c = constant_poly(&field, 5);

        let left = Polynomial::mul(&a, &Polynomial::add(&b, &c));
        let right = Polynomial::add(&Polynomial::mul(&a, &b), &Polynomial::mul(&a, &c));

        assert_eq!(left, right);
    }

    #[test]
    fn test_additive_inverse() {
        let field = setup_field();

        let p = linear_poly(&field, 3, 7);
        let neg_p = Polynomial::neg(&p);
        let sum = Polynomial::add(&p, &neg_p);

        for coeff in sum.coeffs {
            assert_eq!(coeff.value, 0);
        }
    }

    #[test]
    fn test_multiplication_by_one() {
        let field = setup_field();

        let p = linear_poly(&field, 3, 7);
        let one = constant_poly(&field, 1);
        let result = Polynomial::mul(&p, &one);

        assert_eq!(result, p);
    }

    #[test]
    fn test_polynomial_degree_after_operations() {
        let field = setup_field();

        let p1 = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        let p2 = Polynomial::new(vec![field.new_element(4), field.new_element(5)], field);

        let sum = Polynomial::add(&p1, &p2);
        assert_eq!(sum.deg(), 2);

        let product = Polynomial::mul(&p1, &p2);
        assert_eq!(product.deg(), 3);
    }

    #[test]
    fn test_division_basic() {
        let field = setup_field();

        let dividend = Polynomial::new(
            vec![
                field.new_element(2),
                field.new_element(3),
                field.new_element(1),
            ],
            field,
        );
        let divisor = Polynomial::new(vec![field.new_element(1), field.new_element(1)], field);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert_eq!(quotient.deg(), 1);
        assert_eq!(quotient.coeffs[0].value, 2);
        assert_eq!(quotient.coeffs[1].value, 1);
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_with_remainder() {
        let field = setup_field();

        let dividend = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(0),
                field.new_element(1),
            ],
            field,
        );
        let divisor = Polynomial::new(vec![field.new_element(1), field.new_element(1)], field);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert_eq!(quotient.deg(), 1);
        assert_eq!(remainder.deg(), 0);
        assert_eq!(remainder.coeffs[0].value, 2);
    }

    #[test]
    fn test_division_by_constant() {
        let field = setup_field();

        let dividend = Polynomial::new(
            vec![
                field.new_element(2),
                field.new_element(4),
                field.new_element(6),
            ],
            field,
        );
        let divisor = constant_poly(&field, 2);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert_eq!(quotient.deg(), 2);
        assert_eq!(quotient.coeffs[0].value, 1);
        assert_eq!(quotient.coeffs[1].value, 2);
        assert_eq!(quotient.coeffs[2].value, 3);
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_lower_degree_dividend() {
        let field = setup_field();

        let dividend = linear_poly(&field, 1, 1);
        let divisor = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(0),
                field.new_element(1),
            ],
            field,
        );

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert!(quotient.is_zero());
        assert_eq!(remainder, dividend);
    }

    #[test]
    #[should_panic(expected = "No division by zero")]
    fn test_division_by_zero() {
        let field = setup_field();

        let dividend = linear_poly(&field, 1, 1);
        let zero = zero_poly(&field);

        Polynomial::div(&dividend, &zero);
    }

    #[test]
    fn test_division_zero_dividend() {
        let field = setup_field();

        let zero = zero_poly(&field);
        let divisor = linear_poly(&field, 1, 1);

        let (quotient, remainder) = Polynomial::div(&zero, &divisor);

        assert!(quotient.is_zero());
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_same_polynomials() {
        let field = setup_field();

        let poly = linear_poly(&field, 2, 3);

        let (quotient, remainder) = Polynomial::div(&poly, &poly);

        assert_eq!(quotient.deg(), 0);
        assert_eq!(quotient.coeffs[0].value, 1);
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_verification() {
        let field = setup_field();

        let dividend = Polynomial::new(
            vec![
                field.new_element(5),
                field.new_element(7),
                field.new_element(3),
                field.new_element(1),
            ],
            field,
        );
        let divisor = Polynomial::new(vec![field.new_element(2), field.new_element(1)], field);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        let product = Polynomial::mul(&quotient, &divisor);
        let reconstructed = Polynomial::add(&product, &remainder);

        assert_eq!(reconstructed, dividend);
    }

    #[test]
    fn test_division_high_degree() {
        let field = setup_field();

        let dividend = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(1),
                field.new_element(1),
                field.new_element(1),
            ],
            field,
        );
        let divisor = linear_poly(&field, 1, 1);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert_eq!(quotient.deg(), 2);
        assert!(remainder.is_zero());
    }

    #[test]
    fn test_division_with_field_arithmetic() {
        let field = setup_field();

        let dividend = Polynomial::new(vec![field.new_element(7), field.new_element(14)], field);
        let divisor = constant_poly(&field, 7);

        let (quotient, remainder) = Polynomial::div(&dividend, &divisor);

        assert_eq!(quotient.deg(), 1);
        assert_eq!(quotient.coeffs[0].value, 1);
        assert_eq!(quotient.coeffs[1].value, 2);
        assert!(remainder.is_zero());
    }
}
