use crate::ff::FieldElement;

use super::Polynomial;

impl Polynomial {
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
    fn test_eval_zero_poly() {
        let field = setup_field();
        let zero = zero_poly(&field);
        let x = field.new_element(5);

        let result = zero.eval(&x);
        assert_eq!(result.value, 0);
    }

    #[test]
    fn test_eval_constant() {
        let field = setup_field();
        let poly = constant_poly(&field, 7);
        let x = field.new_element(10);

        let result = poly.eval(&x);
        assert_eq!(result.value, 7);
    }

    #[test]
    fn test_eval_linear() {
        let field = setup_field();
        let poly = linear_poly(&field, 2, 3);
        let x = field.new_element(4);

        let result = poly.eval(&x);
        assert_eq!(result.value, 14);
    }

    #[test]
    fn test_eval_zero_point() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![field.new_element(5), field.new_element(7), field.new_element(9)],
            field,
        );
        let x = field.new_element(0);

        let result = poly.eval(&x);
        assert_eq!(result.value, 5);
    }

    #[test]
    fn test_eval_higher_degree() {
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
        let x = field.new_element(2);

        let result = poly.eval(&x);
        assert_eq!(result.value, 49);
    }

    #[test]
    fn test_eval_domain() {
        let field = setup_field();
        let poly = linear_poly(&field, 1, 1);
        let domain = vec![
            field.new_element(0),
            field.new_element(1),
            field.new_element(2),
            field.new_element(3),
        ];

        let results = poly.eval_domain(&domain);
        assert_eq!(results.len(), 4);
        assert_eq!(results[0].value, 1);
        assert_eq!(results[1].value, 2);
        assert_eq!(results[2].value, 3);
        assert_eq!(results[3].value, 4);
    }

    #[test]
    fn test_eval_consistency() {
        let field = setup_field();
        let poly = Polynomial::new(
            vec![field.new_element(2), field.new_element(3), field.new_element(1)],
            field,
        );
        let x = field.new_element(5);

        let manual = field.new_element(2) + field.new_element(3) * field.new_element(5)
            + field.new_element(1) * field.new_element(25);
        let eval_result = poly.eval(&x);

        assert_eq!(eval_result, manual);
    }

    #[test]
    fn test_eval_large_values() {
        let field = setup_field();
        let poly = constant_poly(&field, P - 1);
        let x = field.new_element(P - 1);

        let result = poly.eval(&x);
        assert_eq!(result.value, P - 1);
    }

    #[test]
    fn test_eval_polynomial_arithmetic() {
        let field = setup_field();
        let poly1 = linear_poly(&field, 1, 2);
        let poly2 = linear_poly(&field, 3, 4);
        let sum = Polynomial::add(&poly1, &poly2);
        let x = field.new_element(7);

        let eval_sum = sum.eval(&x);
        let eval1 = poly1.eval(&x);
        let eval2 = poly2.eval(&x);
        let manual_sum = eval1 + eval2;

        assert_eq!(eval_sum, manual_sum);
    }
}
