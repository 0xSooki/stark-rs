use crate::ff::FieldElement;
use crate::hash::Hash;

pub struct ProofStream {
    pub objects: Vec<ProofObject>,
}

#[derive(Clone, Debug)]
pub enum ProofObject {
    MerkleRoot(Hash),
    FieldElement(FieldElement),
    FieldElements(Vec<FieldElement>),
    MerklePath(Vec<Hash>),
}

impl ProofStream {
    pub fn new() -> Self {
        ProofStream {
            objects: Vec::new(),
        }
    }

    pub fn push(&mut self, obj: ProofObject) {
        self.objects.push(obj);
    }

    pub fn pop(&mut self) -> Option<ProofObject> {
        if self.objects.is_empty() {
            None
        } else {
            Some(self.objects.remove(0))
        }
    }

    pub fn serialize(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for obj in &self.objects {
            match obj {
                ProofObject::MerkleRoot(hash) => {
                    bytes.push(0);
                    bytes.extend_from_slice(&hash.0);
                }
                ProofObject::FieldElement(fe) => {
                    bytes.push(1);
                    bytes.extend_from_slice(&fe.value.to_le_bytes());
                }
                ProofObject::FieldElements(fes) => {
                    bytes.push(2);
                    bytes.extend_from_slice(&(fes.len() as u64).to_le_bytes());
                    for fe in fes {
                        bytes.extend_from_slice(&fe.value.to_le_bytes());
                    }
                }
                ProofObject::MerklePath(path) => {
                    bytes.push(3);
                    bytes.extend_from_slice(&(path.len() as u64).to_le_bytes());
                    for hash in path {
                        bytes.extend_from_slice(&hash.0);
                    }
                }
            }
        }
        bytes
    }
}
