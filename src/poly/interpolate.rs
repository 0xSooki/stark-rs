use crate::ff::FieldElement;

use super::poly::Polynomial;

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
}
