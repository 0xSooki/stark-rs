use std::ops::Mul;

use super::Polynomial;

impl Polynomial {
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
}

impl Mul<&Polynomial> for &Polynomial {
    type Output = Polynomial;

    fn mul(self, rhs: &Polynomial) -> Self::Output {
        Polynomial::mul(self, rhs)
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

    #[test]
    fn test_mul_zero() {
        let field = setup_field();
        let poly = Polynomial::linear_poly(&field, 2, 3);
        let zero = Polynomial::zero_poly(&field);

        let result = Polynomial::mul(&poly, &zero);
        assert!(result.is_zero());

        let result2 = Polynomial::mul(&zero, &poly);
        assert!(result2.is_zero());
    }

    #[test]
    fn test_mul_by_one() {
        let field = setup_field();
        let poly = Polynomial::linear_poly(&field, 2, 3);
        let one = Polynomial::constant_poly(&field, 1);

        let result = Polynomial::mul(&poly, &one);
        assert_eq!(result, poly);

        let result2 = Polynomial::mul(&one, &poly);
        assert_eq!(result2, poly);
    }

    #[test]
    fn test_mul_constants() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, 3);
        let poly2 = Polynomial::constant_poly(&field, 4);

        let result = Polynomial::mul(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 12);
    }

    #[test]
    fn test_mul_linear() {
        let field = setup_field();
        let poly1 = Polynomial::linear_poly(&field, 1, 1);
        let poly2 = Polynomial::linear_poly(&field, 1, 1);

        let result = Polynomial::mul(&poly1, &poly2);
        assert_eq!(result.deg(), 2);
        assert_eq!(result.coeffs[0].value, 1);
        assert_eq!(result.coeffs[1].value, 2);
        assert_eq!(result.coeffs[2].value, 1);
    }

    #[test]
    fn test_mul_different_degrees() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, 2);
        let poly2 = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(0),
                field.new_element(1),
            ],
            field,
        );

        let result = Polynomial::mul(&poly1, &poly2);
        assert_eq!(result.deg(), 2);
        assert_eq!(result.coeffs[0].value, 2);
        assert_eq!(result.coeffs[1].value, 0);
        assert_eq!(result.coeffs[2].value, 2);
    }

    #[test]
    fn test_mul_commutativity() {
        let field = setup_field();
        let poly1 = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(2),
                field.new_element(3),
            ],
            field,
        );
        let poly2 = Polynomial::linear_poly(&field, 4, 5);

        let result1 = Polynomial::mul(&poly1, &poly2);
        let result2 = Polynomial::mul(&poly2, &poly1);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_mul_distributivity() {
        let field = setup_field();
        let poly1 = Polynomial::linear_poly(&field, 1, 1);
        let poly2 = Polynomial::linear_poly(&field, 2, 3);
        let poly3 = Polynomial::linear_poly(&field, 4, 5);

        let sum = Polynomial::add(&poly2, &poly3);
        let result1 = Polynomial::mul(&poly1, &sum);

        let prod1 = Polynomial::mul(&poly1, &poly2);
        let prod2 = Polynomial::mul(&poly1, &poly3);
        let result2 = Polynomial::add(&prod1, &prod2);

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_mul_overflow() {
        let field = setup_field();
        let large_val = P - 1;
        let poly1 = Polynomial::constant_poly(&field, large_val);
        let poly2 = Polynomial::constant_poly(&field, 2);

        let result = Polynomial::mul(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, (2 * large_val) % P);
    }

    #[test]
    fn test_mul_sparse() {
        let field = setup_field();
        let poly1 = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(0),
                field.new_element(2),
            ],
            field,
        );
        let poly2 = Polynomial::new(
            vec![
                field.new_element(3),
                field.new_element(0),
                field.new_element(4),
            ],
            field,
        );

        let result = Polynomial::mul(&poly1, &poly2);
        assert_eq!(result.deg(), 4);
        assert_eq!(result.coeffs[0].value, 3);
        assert_eq!(result.coeffs[1].value, 0);
        assert_eq!(result.coeffs[2].value, 10);
        assert_eq!(result.coeffs[3].value, 0);
        assert_eq!(result.coeffs[4].value, 8);
    }
}
