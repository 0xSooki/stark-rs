use std::cmp::max;

use crate::ff::FieldElement;

use super::poly::Polynomial;

impl Polynomial {
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
    fn test_sub_zero() {
        let field = setup_field();
        let poly = linear_poly(&field, 3, 4);
        let zero = zero_poly(&field);

        let result = Polynomial::sub(&poly, &zero);
        assert_eq!(result, poly);

        let result2 = Polynomial::sub(&zero, &poly);
        assert_eq!(result2, Polynomial::neg(&poly));
    }

    #[test]
    fn test_sub_constants() {
        let field = setup_field();
        let poly1 = constant_poly(&field, 8);
        let poly2 = constant_poly(&field, 3);

        let result = Polynomial::sub(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 5);
    }

    #[test]
    fn test_sub_same_degree() {
        let field = setup_field();
        let poly1 = linear_poly(&field, 6, 8);
        let poly2 = linear_poly(&field, 2, 3);

        let result = Polynomial::sub(&poly1, &poly2);
        assert_eq!(result.deg(), 1);
        assert_eq!(result.coeffs[0].value, 4);
        assert_eq!(result.coeffs[1].value, 5);
    }

    #[test]
    fn test_sub_different_degrees() {
        let field = setup_field();
        let poly1 = linear_poly(&field, 1, 2);
        let poly2 = constant_poly(&field, 1);

        let result = Polynomial::sub(&poly1, &poly2);
        assert_eq!(result.deg(), 1);
        assert_eq!(result.coeffs[0].value, 0);
        assert_eq!(result.coeffs[1].value, 2);
    }

    #[test]
    fn test_sub_self() {
        let field = setup_field();
        let poly = linear_poly(&field, 5, 7);

        let result = Polynomial::sub(&poly, &poly);
        assert!(result.is_zero());
    }

    #[test]
    fn test_sub_underflow() {
        let field = setup_field();
        let poly1 = constant_poly(&field, 1);
        let poly2 = constant_poly(&field, 3);

        let result = Polynomial::sub(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, P - 2);
    }

    #[test]
    fn test_sub_anticommutativity() {
        let field = setup_field();
        let poly1 = Polynomial::new(
            vec![field.new_element(1), field.new_element(2), field.new_element(3)],
            field,
        );
        let poly2 = linear_poly(&field, 4, 5);

        let result1 = Polynomial::sub(&poly1, &poly2);
        let result2 = Polynomial::sub(&poly2, &poly1);
        assert_eq!(result1, Polynomial::neg(&result2));
    }

    #[test]
    fn test_sub_with_add() {
        let field = setup_field();
        let poly1 = linear_poly(&field, 3, 7);
        let poly2 = linear_poly(&field, 1, 2);

        let diff = Polynomial::sub(&poly1, &poly2);
        let sum = Polynomial::add(&diff, &poly2);
        assert_eq!(sum, poly1);
    }
}
