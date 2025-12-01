use crate::ff::{FieldElement, FiniteField};

#[derive(Clone)]
pub struct Trace {
    pub trace: Vec<Vec<i128>>,
    pub num_columns: usize,
}

impl Trace {
    pub fn new(trace: &Vec<Vec<i128>>) -> Trace {
        Trace {
            trace: trace.to_vec(),
            num_columns: trace[0].len(),
        }
    }

    pub fn get_row(&self, i: usize) -> Option<&Vec<i128>> {
        self.trace.get(i)
    }

    pub fn get_col(&self, j: usize) -> Vec<i128> {
        self.trace.iter().map(|r| r[j]).collect()
    }

    pub fn get(&self, i: usize, j: usize) -> Option<i128> {
        self.trace.get(i)?.get(j).copied()
    }

    pub fn to_field_elements(&self, field: FiniteField) -> Vec<Vec<FieldElement>> {
        self.trace
            .iter()
            .map(|r| r.iter().map(|&e| field.new_element(e as u64)).collect())
            .collect()
    }

    pub fn fibonacci(length: usize) -> Trace {
        let mut trace = Vec::new();
        let mut a = 1i128;
        let mut b = 1i128;

        for _ in 0..length {
            trace.push(vec![a]);
            let next = a + b;
            a = b;
            b = next;
        }

        Trace::new(&trace)
    }
}
