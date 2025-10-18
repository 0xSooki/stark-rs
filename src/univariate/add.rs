use super::Polynomial;
use crate::ff::FieldElement;
use std::{cmp::max, ops::Add};

impl Polynomial {
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
}

impl Add<&Polynomial> for &Polynomial {
    type Output = Polynomial;

    fn add(self, rhs: &Polynomial) -> Self::Output {
        Polynomial::add(self, rhs)
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
    fn test_add_zero() {
        let field = setup_field();
        let poly = Polynomial::linear_poly(&field, 1, 2);
        let zero = Polynomial::zero_poly(&field);

        let result = &poly + &zero;
        assert_eq!(result, poly);

        let result2 = Polynomial::add(&zero, &poly);
        assert_eq!(result2, poly);
    }

    #[test]
    fn test_add_constants() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, 3);
        let poly2 = Polynomial::constant_poly(&field, 5);

        let result = Polynomial::add(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 8);
    }

    #[test]
    fn test_add_same_degree() {
        let field = setup_field();
        let poly1 = Polynomial::linear_poly(&field, 1, 2);
        let poly2 = Polynomial::linear_poly(&field, 3, 4);

        let result = Polynomial::add(&poly1, &poly2);
        assert_eq!(result.deg(), 1);
        assert_eq!(result.coeffs[0].value, 4);
        assert_eq!(result.coeffs[1].value, 6);
    }

    #[test]
    fn test_add_different_degrees() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, 5);
        let poly2 = Polynomial::linear_poly(&field, 1, 2);

        let result = Polynomial::add(&poly1, &poly2);
        assert_eq!(result.deg(), 1);
        assert_eq!(result.coeffs[0].value, 6);
        assert_eq!(result.coeffs[1].value, 2);

        let result2 = Polynomial::add(&poly2, &poly1);
        assert_eq!(result2, result);
    }

    #[test]
    fn test_add_result_zero() {
        let field = setup_field();
        let poly1 = Polynomial::linear_poly(&field, 1, 2);
        let poly2 = Polynomial::new(
            vec![field.new_element(P - 1), field.new_element(P - 2)],
            field,
        );

        let result = Polynomial::add(&poly1, &poly2);
        assert!(result.is_zero());
    }

    #[test]
    fn test_add_overflow() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, P - 1);
        let poly2 = Polynomial::constant_poly(&field, 2);

        let result = Polynomial::add(&poly1, &poly2);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 1);
    }

    #[test]
    fn test_add_commutativity() {
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

        let result1 = Polynomial::add(&poly1, &poly2);
        let result2 = Polynomial::add(&poly2, &poly1);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_add_associativity() {
        let field = setup_field();
        let poly1 = Polynomial::constant_poly(&field, 1);
        let poly2 = Polynomial::constant_poly(&field, 2);
        let poly3 = Polynomial::constant_poly(&field, 3);

        let result1 = Polynomial::add(&Polynomial::add(&poly1, &poly2), &poly3);
        let result2 = Polynomial::add(&poly1, &Polynomial::add(&poly2, &poly3));
        assert_eq!(result1, result2);
    }
}
