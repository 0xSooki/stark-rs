use crate::ff::{FieldElement, FiniteField};
use crate::fiat_shamir::FiatShamir;
use crate::hash::Hash;
use crate::merkle::MerkleTree;
use crate::stream::{ProofObject, ProofStream};
use crate::univariate::Polynomial;

pub struct Fri {
    pub offset: FieldElement,
    pub omega: FieldElement,
    pub domain_length: usize,
    pub field: FiniteField,
    pub expansion_factor: usize,
    pub num_colinearity_tests: usize,
}

pub struct FriProof {
    pub merkle_roots: Vec<Hash>,
    pub final_codeword: Vec<FieldElement>,
    pub query_data: Vec<QueryData>,
}

pub struct QueryData {
    pub index: usize,
    pub values_per_round: Vec<FieldElement>,
    pub merkle_paths: Vec<Vec<Hash>>,
}

impl Fri {
    pub fn new(
        omega: FieldElement,
        offset: FieldElement,
        domain_length: usize,
        expansion_factor: usize,
        num_colinearity_tests: usize,
    ) -> Self {
        assert!(
            domain_length.is_power_of_two(),
            "Domain length must be power of 2"
        );
        assert!(
            expansion_factor.is_power_of_two(),
            "Expansion factor must be power of 2"
        );
        assert!(expansion_factor >= 4, "Expansion factor must be at least 4");

        Fri {
            omega,
            offset,
            domain_length,
            field: omega.field,
            expansion_factor,
            num_colinearity_tests,
        }
    }

    fn fold_codeword(
        &self,
        codeword: &[FieldElement],
        alpha: &FieldElement,
        offset: &FieldElement,
        omega: &FieldElement,
    ) -> Vec<FieldElement> {
        let one = self.field.one();
        let two = self.field.new_element(2);
        let two_inv = self.field.inv(&two);
        let half = codeword.len() / 2;
        let mut folded = Vec::with_capacity(half);

        for i in 0..half {
            // Compute offset * omega^i
            let x = self.field.mul(offset, &self.field.exp(omega, i as u64));

            // (one + alpha / x)
            let a = self.field.add(&one, &self.field.div(alpha, &x));

            // (one - alpha / x)
            let b = self.field.sub(&one, &self.field.div(alpha, &x));

            // a * codeword[i] + b * codeword[half + i]
            let term = self.field.add(
                &self.field.mul(&a, &codeword[i]),
                &self.field.mul(&b, &codeword[half + i]),
            );

            // two_inv * term
            folded.push(self.field.mul(&two_inv, &term));
        }

        folded
    }

    pub fn num_rounds(&self) -> u64 {
        let mut codeword_length = self.domain_length;
        let mut num_rounds = 0;
        while codeword_length > self.expansion_factor
            && 4 * self.num_colinearity_tests < codeword_length
        {
            codeword_length /= 2;
            num_rounds += 1;
        }
        num_rounds
    }

    pub fn commit(
        &self,
        initial_codeword: Vec<FieldElement>,
        proof_stream: &mut ProofStream,
        fiat_shamir: &mut FiatShamir,
    ) -> Vec<Vec<FieldElement>> {
        let mut codeword = initial_codeword;
        let mut omega = self.omega;
        let mut offset = self.offset;
        let mut codewords = Vec::new();

        for r in 0..self.num_rounds() {
            // compute and send Merkle root
            let hashes: Vec<Hash> = codeword
                .iter()
                .map(|e| Hash::from_field_elements(&[e.value]))
                .collect();

            let padded_len = hashes.len().next_power_of_two();
            let mut padded_hashes = hashes;
            padded_hashes.resize(padded_len, Hash([0u8; 32]));

            let tree = MerkleTree::new(&padded_hashes);
            let root = tree.get_root().clone();
            proof_stream.push(ProofObject::MerkleRoot(root));

            fiat_shamir.absorb(&root.0);

            if r == self.num_rounds() - 1 {
                break;
            }

            // get challenge
            let alpha = fiat_shamir.challenge(&self.field);

            codewords.push(codeword.clone());

            // split and fold
            codeword = self.fold_codeword(&codeword, &alpha, &offset, &omega);

            // square omega and offset
            omega = self.field.mul(&omega, &omega);
            offset = self.field.mul(&offset, &offset);
        }

        // send last codeword (which is the last folded one, or the initial if num_rounds=1)
        proof_stream.push(ProofObject::FieldElements(codeword.clone()));

        codewords.push(codeword.clone());

        codewords
    }

    fn eval_domain(&self, round: usize) -> Vec<FieldElement> {
        let size = self.domain_length >> round;
        (0..size)
            .map(|i| {
                let omega_power = self.field.exp(&self.omega, ((1 << round) * i) as u64);
                self.field.mul(&self.offset, &omega_power)
            })
            .collect()
    }

    fn sample_index(byte_array: &[u8], size: usize) -> usize {
        let mut acc: u128 = 0;
        for &b in byte_array {
            acc = (acc << 8) ^ (b as u128);
        }
        (acc as usize) % size
    }

    pub fn sample_indices(
        &self,
        seed: &[u8],
        size: usize,
        reduced_size: usize,
        number: usize,
    ) -> Vec<usize> {
        assert!(
            number <= 2 * reduced_size,
            "not enough entropy in indices wrt last codeword"
        );
        assert!(
            number <= reduced_size,
            "cannot sample more indices than available in last codeword; requested: {}, available: {}",
            number,
            reduced_size
        );

        let mut indices = Vec::new();
        let mut reduced_indices = Vec::new();
        let mut counter = 0u32;

        while indices.len() < number {
            let mut seed_with_counter = seed.to_vec();
            seed_with_counter.extend_from_slice(&counter.to_le_bytes());
            let hash = Hash::from_bytes(&seed_with_counter);
            let index = Self::sample_index(&hash.0, size);
            let reduced_index = index % reduced_size;
            counter += 1;

            if !reduced_indices.contains(&reduced_index) {
                indices.push(index);
                reduced_indices.push(reduced_index);
            }
        }

        indices
    }

    pub fn query(
        &self,
        current_codeword: &[FieldElement],
        next_codeword: &[FieldElement],
        c_indices: &[usize],
        proof_stream: &mut ProofStream,
        current_tree: &MerkleTree,
        next_tree: &MerkleTree,
    ) -> Vec<usize> {
        let half = current_codeword.len() / 2;
        let a_indices: Vec<usize> = c_indices.iter().map(|&index| index).collect();
        let b_indices: Vec<usize> = a_indices.iter().map(|&index| index + half).collect();

        // reveal leafs
        for s in 0..self.num_colinearity_tests {
            let triple = vec![
                current_codeword[a_indices[s]],
                current_codeword[b_indices[s]],
                next_codeword[c_indices[s]],
            ];
            proof_stream.push(ProofObject::FieldElements(triple));
        }

        // reveal authentication paths
        for s in 0..self.num_colinearity_tests {
            proof_stream.push(ProofObject::MerklePath(current_tree.open(a_indices[s])));
            proof_stream.push(ProofObject::MerklePath(current_tree.open(b_indices[s])));
            proof_stream.push(ProofObject::MerklePath(next_tree.open(c_indices[s])));
        }

        let mut all_indices = a_indices;
        all_indices.extend(b_indices);
        all_indices
    }

    pub fn prove(
        &self,
        initial_codeword: Vec<FieldElement>,
        fiat_shamir: &mut FiatShamir,
        proof_stream: &mut ProofStream,
    ) -> Vec<usize> {
        assert_eq!(
            self.domain_length,
            initial_codeword.len(),
            "initial codeword length does not match domain length"
        );

        // commit phase
        let codewords = self.commit(initial_codeword, proof_stream, fiat_shamir);

        // get indices
        let sample_size = if codewords.len() > 1 {
            codewords[1].len()
        } else {
            codewords[0].len()
        };
        let top_level_indices = self.sample_indices(
            &Hash::from_u64(fiat_shamir.challenge(&codewords[0][0].field).value).0,
            sample_size,
            codewords[codewords.len() - 1].len(),
            self.num_colinearity_tests,
        );
        let mut indices: Vec<usize> = top_level_indices.clone();

        // query phase
        for i in 0..(codewords.len() - 1) {
            // fold indices
            indices = indices
                .iter()
                .map(|&index| index % (codewords[i].len() / 2))
                .collect();

            // build temporary merkle trees for query
            let current_hashes: Vec<Hash> = codewords[i]
                .iter()
                .map(|e| Hash::from_field_elements(&[e.value]))
                .collect();
            let next_hashes: Vec<Hash> = codewords[i + 1]
                .iter()
                .map(|e| Hash::from_field_elements(&[e.value]))
                .collect();

            let current_tree = MerkleTree::new(&current_hashes);
            let next_tree = MerkleTree::new(&next_hashes);

            self.query(
                &codewords[i],
                &codewords[i + 1],
                &indices,
                proof_stream,
                &current_tree,
                &next_tree,
            );
        }

        top_level_indices
    }

    pub fn verify(
        &self,
        proof_stream: &mut ProofStream,
        fiat_shamir: &mut FiatShamir,
        polynomial_values: &mut Vec<(usize, FieldElement)>,
    ) -> bool {
        let mut omega = self.omega;
        let mut offset = self.offset;

        // extract all roots and alphas
        let mut roots = Vec::new();
        let mut alphas = Vec::new();
        for _ in 0..self.num_rounds() {
            if let Some(ProofObject::MerkleRoot(root)) = proof_stream.pop() {
                roots.push(root);
                fiat_shamir.absorb(&root.0);
                alphas.push(fiat_shamir.challenge(&self.field));
            } else {
                println!("Failed to extract Merkle root");
                return false;
            }
        }

        // extract last codeword
        let last_codeword = if let Some(ProofObject::FieldElements(vals)) = proof_stream.pop() {
            vals
        } else {
            println!("Failed to extract last codeword");
            return false;
        };

        // check if it matches the given root
        if roots.is_empty() {
            println!("No FRI roots extracted");
            return false;
        }
        let last_hashes: Vec<Hash> = last_codeword
            .iter()
            .map(|e| Hash::from_field_elements(&[e.value]))
            .collect();
        let last_tree = MerkleTree::new(&last_hashes);
        if roots[roots.len() - 1] != *last_tree.get_root() {
            println!("last codeword is not well formed");
            return false;
        }

        // check if it is low degree
        let degree_bound = (last_codeword.len() / self.expansion_factor);
        if degree_bound == 0 {
            println!("last codeword too small");
            return false;
        }
        let degree = degree_bound - 1;
        let mut last_omega = omega;
        let mut last_offset = offset;
        for _ in 0..(self.num_rounds() - 1) {
            last_omega = self.field.mul(&last_omega, &last_omega);
            last_offset = self.field.mul(&last_offset, &last_offset);
        }

        // compute interpolant
        let last_domain: Vec<FieldElement> = (0..last_codeword.len())
            .map(|i| {
                self.field
                    .mul(&last_offset, &self.field.exp(&last_omega, i as u64))
            })
            .collect();

        let poly = Polynomial::interpolate_domain(&last_domain, &last_codeword);

        // verify interpolation
        let re_evaluated = poly.eval_domain(&last_domain);
        for (i, &val) in last_codeword.iter().enumerate() {
            if re_evaluated[i] != val {
                println!("re-evaluated codeword does not match original!");
                return false;
            }
        }

        if poly.deg() > degree as i128 {
            println!("last codeword does not correspond to polynomial of low enough degree");
            println!("observed degree: {}", poly.deg());
            println!("but should be: {}", degree);
            return false;
        }

        // get indices
        let top_level_indices = self.sample_indices(
            &Hash::from_u64(fiat_shamir.challenge(&self.field).value).0,
            self.domain_length >> 1,
            self.domain_length >> (self.num_rounds() - 1),
            self.num_colinearity_tests,
        );

        // for every round, check consistency of subsequent layers
        for r in 0..(self.num_rounds() - 1) as usize {
            // fold c indices
            let c_indices: Vec<usize> = top_level_indices
                .iter()
                .map(|&index| index % (self.domain_length >> (r + 1)))
                .collect();

            // infer a and b indices
            let a_indices: Vec<usize> = c_indices.clone();
            let b_indices: Vec<usize> = a_indices
                .iter()
                .map(|&index| index + (self.domain_length >> (r + 1)))
                .collect();

            // read values and check colinearity
            let mut aa = Vec::new();
            let mut bb = Vec::new();
            let mut cc = Vec::new();
            for s in 0..self.num_colinearity_tests {
                if let Some(ProofObject::FieldElements(triple)) = proof_stream.pop() {
                    if triple.len() != 3 {
                        println!("Expected triple of values");
                        return false;
                    }
                    let ay = triple[0];
                    let by = triple[1];
                    let cy = triple[2];
                    aa.push(ay);
                    bb.push(by);
                    cc.push(cy);

                    // record top-layer values for later verification
                    if r == 0 {
                        polynomial_values.push((a_indices[s], ay));
                        polynomial_values.push((b_indices[s], by));
                    }

                    // colinearity check
                    let ax = self
                        .field
                        .mul(&offset, &self.field.exp(&omega, a_indices[s] as u64));
                    let bx = self
                        .field
                        .mul(&offset, &self.field.exp(&omega, b_indices[s] as u64));
                    let cx = alphas[r];
                    if !test_colinearity(&[(ax, ay), (bx, by), (cx, cy)], &self.field) {
                        println!("colinearity check failure");
                        return false;
                    }
                } else {
                    println!("Failed to extract triple values");
                    return false;
                }
            }

            // verify authentication paths
            for i in 0..self.num_colinearity_tests {
                if let Some(ProofObject::MerklePath(path)) = proof_stream.pop() {
                    let leaf = Hash::from_field_elements(&[aa[i].value]);
                    if !MerkleTree::verify(&leaf, a_indices[i], &path, &roots[r]) {
                        println!("merkle authentication path verification fails for aa");
                        return false;
                    }
                } else {
                    println!("Failed to extract path for aa");
                    return false;
                }

                if let Some(ProofObject::MerklePath(path)) = proof_stream.pop() {
                    let leaf = Hash::from_field_elements(&[bb[i].value]);
                    if !MerkleTree::verify(&leaf, b_indices[i], &path, &roots[r]) {
                        println!("merkle authentication path verification fails for bb");
                        return false;
                    }
                } else {
                    println!("Failed to extract path for bb");
                    return false;
                }

                if let Some(ProofObject::MerklePath(path)) = proof_stream.pop() {
                    let leaf = Hash::from_field_elements(&[cc[i].value]);
                    if !MerkleTree::verify(&leaf, c_indices[i], &path, &roots[r + 1]) {
                        println!("merkle authentication path verification fails for cc");
                        return false;
                    }
                } else {
                    println!("Failed to extract path for cc");
                    return false;
                }
            }

            // square omega and offset to prepare for next round
            omega = self.field.mul(&omega, &omega);
            offset = self.field.mul(&offset, &offset);
        }
        true
    }
}

fn test_colinearity(points: &[(FieldElement, FieldElement)], field: &FiniteField) -> bool {
    if points.len() != 3 {
        return false;
    }

    let (x0, y0) = points[0];
    let (x1, y1) = points[1];
    let (x2, y2) = points[2];

    let dy1 = field.sub(&y1, &y0);
    let dx1 = field.sub(&x1, &x0);
    let dy2 = field.sub(&y2, &y0);
    let dx2 = field.sub(&x2, &x0);

    let lhs = field.mul(&dy1, &dx2);
    let rhs = field.mul(&dy2, &dx1);

    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ff::FiniteField;

    #[test]
    fn test_fri_prove_verify_constant() {
        let field = FiniteField::new(998244353);
        let omega = field.prim_nth_root(32);
        let offset = field.new_element(3);
        let fri = Fri::new(omega, offset, 32, 4, 2);

        let constant = field.new_element(5);
        let codeword: Vec<FieldElement> = (0..32).map(|_| constant).collect();

        let mut proof_stream = ProofStream::new();
        let mut prover_fiat_shamir = FiatShamir::new();

        let _top_level_indices =
            fri.prove(codeword.clone(), &mut prover_fiat_shamir, &mut proof_stream);

        let proof_bytes = proof_stream.serialize();
        let mut verifier_stream = ProofStream::deserialize(&proof_bytes, field);

        let mut verifier_fiat_shamir = FiatShamir::new();
        let mut polynomial_values = Vec::new();
        let result = fri.verify(
            &mut verifier_stream,
            &mut verifier_fiat_shamir,
            &mut polynomial_values,
        );

        assert!(
            result,
            "FRI verification should succeed for constant polynomial"
        );
    }

    #[test]
    fn test_fri_prove_verify_linear_polynomial() {
        let field = FiniteField::new(998244353);
        let omega = field.prim_nth_root(64);
        let offset = field.new_element(7);
        let fri = Fri::new(omega, offset, 64, 4, 3);

        // f(x) = 3x + 5
        let poly = Polynomial::new(vec![field.new_element(5), field.new_element(3)], field);

        let domain: Vec<FieldElement> = (0..64)
            .map(|i| field.mul(&offset, &field.exp(&omega, i as u64)))
            .collect();
        let codeword = poly.eval_domain(&domain);

        let mut proof_stream = ProofStream::new();
        let mut prover_fiat_shamir = FiatShamir::new();

        let _top_level_indices =
            fri.prove(codeword.clone(), &mut prover_fiat_shamir, &mut proof_stream);

        let proof_bytes = proof_stream.serialize();
        let mut verifier_stream = ProofStream::deserialize(&proof_bytes, field);

        let mut verifier_fiat_shamir = FiatShamir::new();
        let mut polynomial_values = Vec::new();
        let result = fri.verify(
            &mut verifier_stream,
            &mut verifier_fiat_shamir,
            &mut polynomial_values,
        );

        assert!(
            result,
            "FRI verification should succeed for linear polynomial"
        );
    }

    #[test]
    fn test_fri_prove_verify_quadratic_polynomial() {
        let field = FiniteField::new(998244353);
        let omega = field.prim_nth_root(128);
        let offset = field.new_element(13);
        let fri = Fri::new(omega, offset, 128, 4, 4);

        // f(x) = 2x^2 + 3x + 1
        let poly = Polynomial::new(
            vec![
                field.new_element(1),
                field.new_element(3),
                field.new_element(2),
            ],
            field,
        );

        let domain: Vec<FieldElement> = (0..128)
            .map(|i| field.mul(&offset, &field.exp(&omega, i as u64)))
            .collect();
        let codeword = poly.eval_domain(&domain);

        let mut proof_stream = ProofStream::new();
        let mut prover_fiat_shamir = FiatShamir::new();

        let _top_level_indices =
            fri.prove(codeword.clone(), &mut prover_fiat_shamir, &mut proof_stream);

        let proof_bytes = proof_stream.serialize();
        let mut verifier_stream = ProofStream::deserialize(&proof_bytes, field);

        let mut verifier_fiat_shamir = FiatShamir::new();
        let mut polynomial_values = Vec::new();
        let result = fri.verify(
            &mut verifier_stream,
            &mut verifier_fiat_shamir,
            &mut polynomial_values,
        );

        assert!(
            result,
            "FRI verification should succeed for quadratic polynomial"
        );
    }

    #[test]
    fn test_fri_prove_verify_high_degree_polynomial() {
        let field = FiniteField::new(998244353);
        let omega = field.prim_nth_root(256);
        let offset = field.new_element(17);
        let fri = Fri::new(omega, offset, 256, 8, 5);

        let coeffs: Vec<FieldElement> = vec![
            field.new_element(1),
            field.new_element(2),
            field.new_element(5),
            field.new_element(3),
            field.new_element(7),
            field.new_element(4),
            field.new_element(1),
            field.new_element(2),
        ];
        let poly = Polynomial::new(coeffs, field);

        let domain: Vec<FieldElement> = (0..256)
            .map(|i| field.mul(&offset, &field.exp(&omega, i as u64)))
            .collect();
        let codeword = poly.eval_domain(&domain);

        let mut proof_stream = ProofStream::new();
        let mut prover_fiat_shamir = FiatShamir::new();

        let _top_level_indices =
            fri.prove(codeword.clone(), &mut prover_fiat_shamir, &mut proof_stream);

        let proof_bytes = proof_stream.serialize();
        let mut verifier_stream = ProofStream::deserialize(&proof_bytes, field);

        let mut verifier_fiat_shamir = FiatShamir::new();
        let mut polynomial_values = Vec::new();
        let result = fri.verify(
            &mut verifier_stream,
            &mut verifier_fiat_shamir,
            &mut polynomial_values,
        );

        assert!(
            result,
            "FRI verification should succeed for degree 7 polynomial"
        );
    }
}
