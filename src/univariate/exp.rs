use std::ops::BitXor;

use super::Polynomial;

impl Polynomial {
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
                result = Self::mul(&result, &bpower);
            }
            bpower = Self::mul(&bpower, &bpower);
            exp >>= 1;
        }
        result
    }
}

impl BitXor<u64> for &Polynomial {
    type Output = Polynomial;

    fn bitxor(self, rhs: u64) -> Self::Output {
        Polynomial::exp(self, rhs)
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
    fn test_exp_zero() {
        let field = setup_field();
        let poly = linear_poly(&field, 1, 2);

        let result = &poly ^ 0;
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 1);
    }

    #[test]
    fn test_exp_one() {
        let field = setup_field();
        let poly = linear_poly(&field, 3, 4);

        let result = Polynomial::exp(&poly, 1);
        assert_eq!(result, poly);
    }

    #[test]
    fn test_exp_zero_poly() {
        let field = setup_field();
        let zero = zero_poly(&field);

        let result = Polynomial::exp(&zero, 5);
        assert!(result.is_zero());
    }

    #[test]
    fn test_exp_constant() {
        let field = setup_field();
        let poly = constant_poly(&field, 3);

        let result = Polynomial::exp(&poly, 4);
        assert_eq!(result.deg(), 0);
        assert_eq!(result.coeffs[0].value, 81);
    }

    #[test]
    fn test_exp_linear_square() {
        let field = setup_field();
        let poly = linear_poly(&field, 1, 1);

        let result = Polynomial::exp(&poly, 2);
        assert_eq!(result.deg(), 2);
        assert_eq!(result.coeffs[0].value, 1);
        assert_eq!(result.coeffs[1].value, 2);
        assert_eq!(result.coeffs[2].value, 1);
    }

    #[test]
    fn test_exp_linear_cube() {
        let field = setup_field();
        let poly = linear_poly(&field, 1, 1);

        let result = Polynomial::exp(&poly, 3);
        assert_eq!(result.deg(), 3);
        assert_eq!(result.coeffs[0].value, 1);
        assert_eq!(result.coeffs[1].value, 3);
        assert_eq!(result.coeffs[2].value, 3);
        assert_eq!(result.coeffs[3].value, 1);
    }

    #[test]
    fn test_exp_powers_of_two() {
        let field = setup_field();
        let poly = linear_poly(&field, 0, 1);

        let result2 = Polynomial::exp(&poly, 2);
        let result4 = Polynomial::exp(&poly, 4);
        let result8 = Polynomial::exp(&poly, 8);

        assert_eq!(result2.deg(), 2);
        assert_eq!(result4.deg(), 4);
        assert_eq!(result8.deg(), 8);
    }

    #[test]
    fn test_exp_large() {
        let field = setup_field();
        let poly = linear_poly(&field, 2, 1);

        let result = Polynomial::exp(&poly, 10);
        assert_eq!(result.deg(), 10);
    }

    #[test]
    fn test_exp_consistency() {
        let field = setup_field();
        let poly = linear_poly(&field, 1, 2);

        let result1 = Polynomial::exp(&poly, 3);
        let manual = Polynomial::mul(&Polynomial::mul(&poly, &poly), &poly);
        assert_eq!(result1, manual);
    }
}
