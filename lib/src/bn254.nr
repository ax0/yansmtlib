mod test;

use crate::{aux, SMT, SMTProof};
use dep::std::hash::{pedersen_hash, poseidon, poseidon2::Poseidon2};

// Pedersen SMT struct
pub fn pedersen_smt<DEPTH>() -> SMT<Field, Field, Field, DEPTH>
{
    let default_value = 0;
    let hash_leaf = |empty_leaf: bool, key, value| (1 - empty_leaf as Field) * pedersen_hash([key, value, 1]);
    let hash_branch = |l, r| pedersen_hash([l,r]);
    let to_bits: fn(Field) -> [u1; DEPTH] = |key| aux::key_to_bits(key);
    let hash_eq = |x, y| x == y;
    let key_eq = |x, y| x == y;

    SMT::new(default_value, hash_leaf, hash_branch, to_bits, hash_eq, key_eq)    
}

// Poseidon SMT struct
pub fn poseidon_smt<DEPTH>() -> SMT<Field, Field, Field, DEPTH>
{
    let default_value = 0;
    let hash_leaf = |empty_leaf: bool, key, value| (1 - empty_leaf as Field) * poseidon::bn254::hash_3([key, value, 1]);
    let hash_branch = |l, r| poseidon::bn254::hash_2([l,r]);
    let to_bits: fn(Field) -> [u1; DEPTH] = |key| aux::key_to_bits(key);
    let hash_eq = |x, y| x == y;
    let key_eq = |x, y| x == y;

    SMT::new(default_value, hash_leaf, hash_branch, to_bits, hash_eq, key_eq)    

}


// Poseidon2 SMT struct
pub fn poseidon2_smt<DEPTH>() -> SMT<Field, Field, Field, DEPTH>
{
    let default_value = 0;
    let hash_leaf = |empty_leaf: bool, key, value| (1 - empty_leaf as Field) * Poseidon2::hash([key, value, 1], 3);
    let hash_branch = |l, r| Poseidon2::hash([l,r], 2);
    let to_bits: fn(Field) -> [u1; DEPTH] = |key| aux::key_to_bits(key);
    let hash_eq = |x, y| x == y;
    let key_eq = |x, y| x == y;

    SMT::new(default_value, hash_leaf, hash_branch, to_bits, hash_eq, key_eq)    
}

