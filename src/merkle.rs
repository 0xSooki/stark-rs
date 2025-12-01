use crate::hash::Hash;

#[derive(Debug, Clone)]
pub struct MerkleTree {
    pub leaves: Vec<Hash>,
    pub nodes: Vec<Vec<Hash>>,
    pub root: Hash,
}

impl MerkleTree {
    pub fn new(leaves: &Vec<Hash>) -> Self {
        assert!(!leaves.is_empty(), "Cannot create tree from empty leaves");
        assert!(
            leaves.len().is_power_of_two(),
            "Number of leaves must be power of 2"
        );

        let mut nodes = vec![leaves.clone()];
        let mut current_level = leaves.clone();

        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for i in (0..current_level.len()).step_by(2) {
                let combined = Hash::combine(&current_level[i], &current_level[i + 1]);
                next_level.push(combined);
            }
            nodes.push(next_level.clone());
            current_level = next_level;
        }

        let root = current_level[0].clone();

        MerkleTree {
            leaves: leaves.to_vec(),
            nodes,
            root,
        }
    }

    pub fn get_root(&self) -> &Hash {
        &self.root
    }

    pub fn commit(leaves: &Vec<Hash>) -> Hash {
        assert!(!leaves.is_empty(), "Cannot create tree from empty leaves");
        assert!(
            leaves.len().is_power_of_two(),
            "Number of leaves must be power of 2"
        );

        let mut nodes = vec![leaves.clone()];
        let mut current_level = leaves.clone();

        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for i in (0..current_level.len()).step_by(2) {
                let combined = Hash::combine(&current_level[i], &current_level[i + 1]);
                next_level.push(combined);
            }
            nodes.push(next_level.clone());
            current_level = next_level;
        }

        current_level[0].clone()
    }

    pub fn open(&self, index: usize) -> Vec<Hash> {
        assert!(index < self.leaves.len(), "Index out of bounds");

        let mut proof = Vec::new();
        let mut idx = index;

        for level in 0..self.nodes.len() - 1 {
            let sibling_idx = if idx % 2 == 0 { idx + 1 } else { idx - 1 };
            proof.push(self.nodes[level][sibling_idx].clone());
            idx /= 2;
        }

        proof
    }

    pub fn verify(leaf: &Hash, index: usize, proof: &[Hash], root: &Hash) -> bool {
        let mut current = leaf.clone();
        let mut idx = index;

        for sibling in proof {
            current = if idx % 2 == 0 {
                Hash::combine(&current, sibling)
            } else {
                Hash::combine(sibling, &current)
            };
            idx /= 2;
        }

        &current == root
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merkle_tree_creation() {
        let leaves: Vec<Hash> = (0..4).map(|i| Hash::from_bytes(&[i])).collect();

        let tree = MerkleTree::new(&leaves);
        assert_eq!(tree.leaves.len(), 4);
        assert_eq!(tree.nodes.len(), 3);
    }

    #[test]
    fn test_merkle_proof_verification() {
        let leaves: Vec<Hash> = (0..8).map(|i| Hash::from_bytes(&[i])).collect();

        let tree = MerkleTree::new(&leaves);

        for i in 0..leaves.len() {
            let proof = tree.open(i);
            assert!(MerkleTree::verify(&leaves[i], i, &proof, tree.get_root()));
        }
    }

    #[test]
    fn test_merkle_proof_invalid() {
        let leaves: Vec<Hash> = (0..4).map(|i| Hash::from_bytes(&[i])).collect();

        let tree = MerkleTree::new(&leaves);
        let proof = tree.open(0);

        let wrong_leaf = Hash::from_bytes(&[99]);
        assert!(!MerkleTree::verify(&wrong_leaf, 0, &proof, tree.get_root()));
    }
}
