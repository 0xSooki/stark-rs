use crate::ff::{FieldElement, FiniteField};
use crate::hash::Hash;

pub struct FiatShamir {
    pub transcript: Vec<u8>,
}

impl FiatShamir {
    pub fn new() -> Self {
        FiatShamir {
            transcript: Vec::new(),
        }
    }

    pub fn absorb(&mut self, data: &[u8]) {
        self.transcript.extend_from_slice(data);
    }

    pub fn challenge(&self, field: &FiniteField) -> FieldElement {
        let hash = Hash::from_bytes(&self.transcript);
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&hash.0[..8]);
        let val = u64::from_le_bytes(bytes);
        field.new_element(val)
    }
}
