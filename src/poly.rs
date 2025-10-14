use std::cmp::max;

use crate::ff::FieldElement;

#[derive(Debug, Clone)]
pub struct Polynomial {
    coeffs: Vec<FieldElement>,
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
    pub fn new(coeffs: Vec<FieldElement>) -> Polynomial {
        Polynomial { coeffs: coeffs }
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
            Vec::with_capacity(max(lhs.coeffs.len(), rhs.coeffs.len()));
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
            coeffs.push(left + right);
        }
        Polynomial { coeffs: coeffs }
    }

    pub fn neg(poly: &Polynomial) -> Polynomial {
        Polynomial {
            coeffs: poly.coeffs.iter().map(|c| -c.clone()).collect(),
        }
    }

    pub fn sub(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.deg() == -1 {
            return rhs.clone();
        }
        if rhs.deg() == -1 {
            return lhs.clone();
        }
        let mut coeffs: Vec<FieldElement> =
            Vec::with_capacity(max(lhs.coeffs.len(), rhs.coeffs.len()));
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
            coeffs.push(left - right);
        }
        Polynomial { coeffs: coeffs }
    }

    pub fn mul(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.coeffs == vec![] && rhs.coeffs == vec![] {
            return Polynomial { coeffs: vec![] };
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
        return Polynomial { coeffs: coeffs };
    }

    pub fn div(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        todo!()
    }

    pub fn is_zero(&self) -> bool {
        self.deg() == -1
    }

    pub fn leading_coeff(&self) -> FieldElement {
        self.coeffs[self.deg() as usize]
    }
}
