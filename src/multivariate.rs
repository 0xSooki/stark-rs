use std::{cmp::max, collections::{HashMap, hash_map}, hash::Hash, ops::{Add, BitXor, Mul, Neg, Sub}};

use crate::{ff::FieldElement, univariate::Polynomial};

#[derive(Debug, Clone)]
pub struct MPolynomial {
    pub terms: HashMap<Vec<usize>, FieldElement>,
}

impl MPolynomial {
    pub fn new(terms: &HashMap<Vec<usize>, FieldElement>) -> MPolynomial {
        MPolynomial { terms: terms.clone() }
    }

    pub fn zero() -> MPolynomial {
        MPolynomial { terms: HashMap::new() }
    }
}

fn pad_key(k: &[usize], num_variables: usize) -> Vec<usize> {
    let mut out = k.to_vec();
    out.resize(num_variables, 0);
    out
}

impl Add<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn add(self, rhs: &MPolynomial) -> Self::Output {
        let num_variables = self
            .terms
            .keys()
            .chain(rhs.terms.keys())
            .map(|k| k.len())
            .max()
            .unwrap_or(0);

        let mut terms: HashMap<Vec<usize>, FieldElement> = HashMap::new();

        for (k, v) in self.terms.iter() {
            let pad = pad_key(k, num_variables);
            terms.insert(pad, *v);
        }

        for (k, v) in rhs.terms.iter() {
            let pad = pad_key(k, num_variables);
            if let Some(acc) = terms.get_mut(&pad) {
                *acc = &*acc + v;
            } else {
                terms.insert(pad, *v);
            }
        }

        MPolynomial { terms: terms }
    }
}

impl Mul<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn mul(self, rhs: &MPolynomial) -> Self::Output {
        todo!()
    }
}

impl Sub<&MPolynomial> for &MPolynomial {
    type Output = MPolynomial;

    fn sub(self, rhs: &MPolynomial) -> Self::Output {
        todo!()
    }
}

impl Neg for &MPolynomial {
    type Output = MPolynomial;

    fn neg(self) -> Self::Output {
        todo!()
    }
}

impl BitXor for &MPolynomial {
    type Output = MPolynomial;

    fn bitxor(self, rhs: Self) -> Self::Output {
        todo!()
    }
}