use crate::ff::FieldElement;

use super::Polynomial;

impl Polynomial {
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
            coeffs: vec![field.zero()],
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
                let xj = &Polynomial {
                    coeffs: vec![domain[j]],
                    field: field,
                };
                let denom = field.inv(&(domain[i] - domain[j]));
                prod = &prod * &(&x - &xj);

                for c in &mut prod.coeffs {
                    *c = *c * denom;
                }
            }
            acc = &acc + &prod;
        }
        acc
    }
}

#[cfg(test)]
mod test {
    use std::ops::Neg;

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
    fn test_x2() {
        let field = setup_field();
        let domain = vec![
            field.new_element(1),
            field.new_element(2),
            field.new_element(3),
        ];
        let values = vec![
            field.new_element(1),
            field.new_element(4),
            field.new_element(9),
        ];

        let res = Polynomial::interpolate_domain(&domain, &values);

        assert_eq!(res.coeffs.len(), 3);
        assert_eq!(res.coeffs[0].value, 0);
        assert_eq!(res.coeffs[1].value, 0);
        assert_eq!(res.coeffs[2].value, 1);

        for (x, expected) in domain.iter().zip(values.iter()) {
            assert_eq!(Polynomial::eval(&res, x), *expected);
        }
    }

    #[test]
    fn test_linear_polynomial() {
        let field = setup_field();
        let domain = vec![field.new_element(1), field.new_element(3)];
        let values = vec![field.new_element(5), field.new_element(9)];
        let res = Polynomial::interpolate_domain(&domain, &values);
        assert_eq!(res.coeffs.len(), 2);
        assert_eq!(res.coeffs[0].value, 3);
        assert_eq!(res.coeffs[1].value, 2);
    }

    #[test]
    fn test_quadratic_polynomial() {
        let field = setup_field();
        let domain = vec![
            field.new_element(1),
            field.new_element(2),
            field.new_element(3),
        ];
        let values = vec![
            field.new_element(2),
            field.new_element(5),
            field.new_element(10),
        ];
        let res = Polynomial::interpolate_domain(&domain, &values);
        assert_eq!(res.coeffs.len(), 3);
        assert_eq!(res.coeffs[0].value, 1);
        assert_eq!(res.coeffs[1].value, 0);
        assert_eq!(res.coeffs[2].value, 1);
    }

    #[test]
    fn test_interpolation_matches_values() {
        let field = setup_field();
        let domain = vec![
            field.new_element(0),
            field.new_element(1),
            field.new_element(2),
            field.new_element(4),
        ];
        let values = vec![
            field.new_element(3),
            field.new_element(7),
            field.new_element(13),
            field.new_element(35),
        ];
        let res = Polynomial::interpolate_domain(&domain, &values);
        for (x, expected) in domain.iter().zip(values.iter()) {
            assert_eq!(Polynomial::eval(&res, x), *expected);
        }
    }

    #[test]
    fn test_lagrange_three_points() {
        let field = setup_field();

        let domain = vec![
            field.new_element(0),
            field.new_element(1),
            field.new_element((P as i128 - 5) as u64),
        ];
        let values = vec![
            field.new_element((P as i128 - 2) as u64),
            field.new_element(6),
            field.new_element(48),
        ];

        let res = Polynomial::interpolate_domain(&domain, &values);

        assert_eq!(res.coeffs.len(), 3);
        assert_eq!(res.coeffs[0].value, (P as i128 - 2) as u64);
        assert_eq!(res.coeffs[1].value, 5);
        assert_eq!(res.coeffs[2].value, 3);

        for (x, expected) in domain.iter().zip(values.iter()) {
            assert_eq!(Polynomial::eval(&res, x), *expected);
        }
    }
}
