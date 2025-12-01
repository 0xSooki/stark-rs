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

    pub fn deserialize(bytes: &[u8], field: crate::ff::FiniteField) -> Self {
        let mut objects = Vec::new();
        let mut i = 0;

        while i < bytes.len() {
            let tag = bytes[i];
            i += 1;

            match tag {
                0 => {
                    // MerkleRoot
                    if i + 32 <= bytes.len() {
                        let mut hash_bytes = [0u8; 32];
                        hash_bytes.copy_from_slice(&bytes[i..i + 32]);
                        objects.push(ProofObject::MerkleRoot(Hash(hash_bytes)));
                        i += 32;
                    }
                }
                1 => {
                    // FieldElement
                    if i + 8 <= bytes.len() {
                        let val = u64::from_le_bytes([
                            bytes[i],
                            bytes[i + 1],
                            bytes[i + 2],
                            bytes[i + 3],
                            bytes[i + 4],
                            bytes[i + 5],
                            bytes[i + 6],
                            bytes[i + 7],
                        ]);
                        objects.push(ProofObject::FieldElement(field.new_element(val)));
                        i += 8;
                    }
                }
                2 => {
                    // FieldElements
                    if i + 8 <= bytes.len() {
                        let len = u64::from_le_bytes([
                            bytes[i],
                            bytes[i + 1],
                            bytes[i + 2],
                            bytes[i + 3],
                            bytes[i + 4],
                            bytes[i + 5],
                            bytes[i + 6],
                            bytes[i + 7],
                        ]) as usize;
                        i += 8;

                        let mut fes = Vec::new();
                        for _ in 0..len {
                            if i + 8 <= bytes.len() {
                                let val = u64::from_le_bytes([
                                    bytes[i],
                                    bytes[i + 1],
                                    bytes[i + 2],
                                    bytes[i + 3],
                                    bytes[i + 4],
                                    bytes[i + 5],
                                    bytes[i + 6],
                                    bytes[i + 7],
                                ]);
                                fes.push(field.new_element(val));
                                i += 8;
                            }
                        }
                        objects.push(ProofObject::FieldElements(fes));
                    }
                }
                3 => {
                    // MerklePath
                    if i + 8 <= bytes.len() {
                        let len = u64::from_le_bytes([
                            bytes[i],
                            bytes[i + 1],
                            bytes[i + 2],
                            bytes[i + 3],
                            bytes[i + 4],
                            bytes[i + 5],
                            bytes[i + 6],
                            bytes[i + 7],
                        ]) as usize;
                        i += 8;

                        let mut path = Vec::new();
                        for _ in 0..len {
                            if i + 32 <= bytes.len() {
                                let mut hash_bytes = [0u8; 32];
                                hash_bytes.copy_from_slice(&bytes[i..i + 32]);
                                path.push(Hash(hash_bytes));
                                i += 32;
                            }
                        }
                        objects.push(ProofObject::MerklePath(path));
                    }
                }
                _ => break,
            }
        }

        ProofStream { objects }
    }
}
