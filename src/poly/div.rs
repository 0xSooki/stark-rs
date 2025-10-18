use super::Polynomial;

impl Polynomial {
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
        let (_, r) = Self::div(numer, denom);
        r
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
