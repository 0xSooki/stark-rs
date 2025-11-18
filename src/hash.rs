#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Hash(pub [u8; 32]);

impl Hash {
    // Simple hash function using a Feistel-like construction
    // Not cryptographically secure!
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut state = [0u8; 32];

        for i in 0..32 {
            state[i] = PRIMES[i % PRIMES.len()];
        }

        for (chunk_idx, chunk) in bytes.chunks(32).enumerate() {
            for (i, &byte) in chunk.iter().enumerate() {
                let pos = (i + chunk_idx * 32) % 32;
                state[pos] = state[pos].wrapping_add(byte);
                state[pos] = rotate_left(state[pos], 3);
                state[(pos + 7) % 32] ^= state[pos];
            }

            mix_state(&mut state);
        }

        for _ in 0..8 {
            mix_state(&mut state);
        }

        Hash(state)
    }

    pub fn from_field_elements(elements: &[u64]) -> Self {
        let bytes: Vec<u8> = elements.iter().flat_map(|e| e.to_le_bytes()).collect();
        Hash::from_bytes(&bytes)
    }

    pub fn from_u64(value: u64) -> Self {
        Hash::from_bytes(&value.to_le_bytes())
    }

    pub fn combine(left: &Hash, right: &Hash) -> Self {
        let mut combined = [0u8; 64];
        combined[..32].copy_from_slice(&left.0);
        combined[32..].copy_from_slice(&right.0);
        Hash::from_bytes(&combined)
    }

    pub fn to_hex(&self) -> String {
        self.0.iter().map(|b| format!("{:02x}", b)).collect()
    }
}

const PRIMES: [u8; 16] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53];

fn rotate_left(byte: u8, n: u8) -> u8 {
    (byte << n) | (byte >> (8 - n))
}

fn mix_state(state: &mut [u8; 32]) {
    for i in 0..32 {
        state[i] = sbox(state[i]);
    }

    for i in 0..8 {
        let base = i * 4;
        let t0 = state[base];
        let t1 = state[base + 1];
        let t2 = state[base + 2];
        let t3 = state[base + 3];

        state[base] = t0 ^ t1 ^ t3;
        state[base + 1] = t0 ^ t2 ^ t3;
        state[base + 2] = t0 ^ t1 ^ t2;
        state[base + 3] = t1 ^ t2 ^ t3;
    }

    for i in 0..32 {
        let next = (i + 1) % 32;
        let prev = if i == 0 { 31 } else { i - 1 };
        state[i] = state[i].wrapping_add(state[next]).wrapping_add(state[prev]);
    }

    for i in 0..32 {
        state[i] = state[i].wrapping_add(ROUND_CONSTANTS[i]);
    }
}

fn sbox(byte: u8) -> u8 {
    let mut result = byte;
    result = result.wrapping_mul(251);
    result = rotate_left(result, 1);
    result ^= 0x63;
    result
}

const ROUND_CONSTANTS: [u8; 32] = [
    0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36, 0x6c, 0xd8, 0xab, 0x4d, 0x9a, 0x2f,
    0x5e, 0xbc, 0x63, 0xc6, 0x97, 0x35, 0x6a, 0xd4, 0xb3, 0x7d, 0xfa, 0xef, 0xc5, 0x91, 0x39, 0x72,
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_deterministic() {
        let hash1 = Hash::from_bytes(b"hello");
        let hash2 = Hash::from_bytes(b"hello");
        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_hash_different_inputs() {
        let hash1 = Hash::from_bytes(b"hello");
        let hash2 = Hash::from_bytes(b"world");
        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_hash_avalanche_effect() {
        let hash1 = Hash::from_bytes(b"hello");
        let hash2 = Hash::from_bytes(b"hallo");

        let mut diff_count = 0;
        for i in 0..32 {
            if hash1.0[i] != hash2.0[i] {
                diff_count += 1;
            }
        }

        assert!(diff_count > 10, "Hash should have good avalanche effect");
    }

    #[test]
    fn test_hash_from_field_elements() {
        let elements = vec![1u64, 2, 3, 4, 5];
        let hash = Hash::from_field_elements(&elements);
        assert_eq!(hash.0.len(), 32);
    }

    #[test]
    fn test_hash_combine() {
        let hash1 = Hash::from_bytes(b"left");
        let hash2 = Hash::from_bytes(b"right");
        let combined = Hash::combine(&hash1, &hash2);

        assert_ne!(combined, hash1);
        assert_ne!(combined, hash2);
    }
}
