mod aux;
mod bn254;
mod op;

use crate::aux::{foldr, zip, zip3};
use crate::op::{Operation, INSERT, UPDATE, DELETE, is_op, is_insertion, is_update, is_deletion};
use dep::std::unsafe::zeroed;

/// SMT type defining the value representing empty subtrees,
/// the leaf and branch hashers, as well as a function for
/// decomposing keys into bits
struct SMT<Key, Value, HashValue, DEPTH>
{
    /// Default value for empty nodes
    default_value: HashValue,
    /// Leaf hasher
    hash_leaf: fn(bool, Key, Value) -> HashValue,
    /// Branch hasher
    hash_branch: fn(HashValue, HashValue) -> HashValue,
    /// Bit decomposer for `Key`
    to_bits: fn(Key) -> [u1; DEPTH],
    /// Equality test for `HashValue` (TODO: Key: Eq)
    hash_eq: fn(HashValue, HashValue) -> bool,
    /// Equality test for `Key` (TODO: Key: Eq)
    key_eq: fn(Key, Key) -> bool
}

/// Type for representing SMT proofs
struct SMTProof<Key, Value, HashValue, DEPTH>
{
    /// Predicate to indicate whether `key` resolves to an empty leaf
    empty_leaf: bool,
    /// Key to resolve
    key: Key,
    /// Value contained in leaf, which is ignored in case empty_p == true
    value: Value,
    /// The siblings arranged by tree depth
    siblings: [HashValue; DEPTH]    
}

impl<Key, Value, HashValue, DEPTH> SMTProof<Key, Value, HashValue, DEPTH>
{
    /// SMT proof constructor
    pub fn new(empty_leaf: bool, key: Key, value: Value, siblings: [HashValue; DEPTH]) -> Self
    {
        Self
        {
            empty_leaf, key, value, siblings
        }
    }
}

impl<Key, Value, HashValue, DEPTH> SMT<Key, Value, HashValue, DEPTH>
{
    /// Canonical constructor
    pub fn new(default_value: HashValue, hash_leaf: fn(bool, Key, Value) -> HashValue,
           hash_branch: fn(HashValue, HashValue) -> HashValue, to_bits: fn(Key) -> [u1; DEPTH],
           hash_eq: fn(HashValue, HashValue) -> bool, key_eq: fn(Key, Key) -> bool) -> Self
    {
        Self
        {
            default_value, hash_leaf, hash_branch, to_bits, hash_eq, key_eq
        }
    }

    /// A proof for the empty tree
    pub fn empty_proof(self) -> SMTProof<Key, Value, HashValue, DEPTH>
    {
        SMTProof::new(true, zeroed(), zeroed(), [self.default_value; DEPTH])
    }

    /// Levelwise hash computation
    fn hash_comp(self, cur_params: (HashValue, u1, u1), cur_hash: HashValue) -> HashValue
    {
        let (sibling, key_bit, node_bit) = cur_params;

        // Swap left and right if bit is 1
        let (l,r) = if key_bit == 1 { (sibling, cur_hash) } else { (cur_hash, sibling) };

        let hash_branch = self.hash_branch;
        
        if node_bit as bool { hash_branch(l,r) } else { cur_hash }
    }

    /// Proof bitmap. Returns an array of the form [1,1,...,1,0,...,0], where 1 indicates
    /// those nodes that are actually part of the given proof (cf. default value optimisation).
    fn bitmap(self, proof: SMTProof<Key, Value, HashValue, DEPTH>) -> [u1; DEPTH]
    {
        let mut node_bit = 0; // Indicator of whether we are dealing with a non-empty node
        let mut out = [0; DEPTH];
        let val_eq = self.hash_eq;

        for i in 0..DEPTH
        {
            // Starting from the maximum depth, check whether we have reached a non-empty node
            // and set the bit to 1 if we have.
            node_bit += (1 - node_bit) * (!val_eq(proof.siblings[DEPTH - 1 - i], self.default_value)) as u1;
            out[DEPTH - 1 - i] = node_bit;
        }

        out
    }

    /// Method for computing the root of the SMT
    pub fn compute_root(self, proof: SMTProof<Key, Value, HashValue, DEPTH>) -> HashValue
    {
        let key_to_bits = self.to_bits;
        let hash_leaf = self.hash_leaf;
        let hash_comp = |cur_params: (HashValue, u1, u1), cur_hash: HashValue| { self.hash_comp(cur_params, cur_hash) };
        
        // Decompose keys to bits (little-endian convention)
        let key_bits: [u1; DEPTH] = key_to_bits(proof.key);

        // Non-empty node bitmap
        let node_bitmap = self.bitmap(proof);

        let leaf_hash = hash_leaf(proof.empty_leaf, proof.key, proof.value);

        let params = zip3(proof.siblings, key_bits, node_bitmap);
        
        foldr(hash_comp, leaf_hash, params)
    }

    /// SMT membership verification. Returns the result as a boolean.
    ///
    /// # Arguments
    /// * `proof` - The proof to be verified
    /// * `inclusion` - Indicator of whether an inclusion is verified
    /// * `empty_node` - Indicator of whether the (key, value) pair being checked is empty. Relevant for exclusion proofs.
    /// * `excluded_key` - Key whose exclusion from the tree is verified
    /// * `key` - The key whose inclusion is
    pub fn verify_membership(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, inclusion: bool, excluded_key: Key, root: HashValue) -> bool
    {
        let key_to_bits = self.to_bits;
        let val_eq = self.hash_eq;
        
        // Decompose keys to bits
        let key_bits: [u1; DEPTH] = key_to_bits(proof.key);
        let excluded_key_bits: [u1; DEPTH] = key_to_bits(excluded_key);

        assert(!inclusion | !proof.empty_leaf, "A proof resolving to an empty leaf is an exclusion proof.");

        if !inclusion
        {
            // Follow the siblings to the first unequal bit in the case of an indirect exclusion proof
            let comp = zip(key_bits, excluded_key_bits)
                .fold(
                    (0, !proof.empty_leaf),
                    |acc: (Field, bool), bit_pair: (u1, u1)| {
                        let (i, key_bits_eq) = acc;
                        (i + 1,
                         if key_bits_eq & (bit_pair.0 != bit_pair.1) {
                             assert(val_eq(proof.siblings[i], self.default_value), "For a key to be excluded, its leaf must be empty.");
                             false
                         } else { key_bits_eq })
                    });
            
            let key_bits_eq = comp.1;
            
            assert(!key_bits_eq, "The keys must either differ or the proof should resolve the excluded key to the empty leaf.");
        }

        val_eq(self.compute_root(proof), root)
    }

    /// Proof verifier (i.e. proof of inclusion)
    pub fn verify(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, root: HashValue) -> bool
    {
        self.verify_membership(proof, true, zeroed(), root)
    }

    /// Proof of exclusion (i.e. establish exclusion of a key using the given proof)
    pub fn verify_exclusion(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, excluded_key: Key, root: HashValue) -> bool
    {
        self.verify_membership(proof, false, excluded_key, root)
    }

    /// Processor of OP(OP_KEY, OP_VALUE).
    /// The other inputs are assumed to be the following depending on the operation:
    /// INSERT: An exclusion proof for `op_key`.
    /// UPDATE: An inclusion proof for the `(op_key, value)` pair to be replaced by `(op_key, op_value)`.
    /// DELETE: An inclusion proof for a `(key, value)` pair for which `(op_key, op_value)` lies in the set {root, sibling[0], ..., sibling[N-1]}.
    pub fn process(mut self, mut proof: SMTProof<Key, Value, HashValue, DEPTH>, op: Operation, op_key: Key, op_value: Value, root: HashValue)
                  -> SMTProof<Key, Value, HashValue, DEPTH>
    {
        let hash_leaf = self.hash_leaf;
        let key_to_bits = self.to_bits;
        let val_eq = self.hash_eq;
        let key_eq = self.key_eq;
        
        assert(is_op(op));
        let op_ins = is_insertion(op);
        let op_upd = is_update(op);
        let op_del = is_deletion(op);

        // Key update consistency
        assert(!op_upd | key_eq(proof.key, op_key), "The proof key must be the key to be updated.");
        
        // Depending on `op`, check for inclusion/exclusion of (op_key, op_value)
        // For insertions, check for exclusion of `op_key`, else check for inclusion
        // of `(key, value)`.
        assert(self.verify_membership(proof, !op_ins, if op_ins { op_key } else { zeroed() }, root), "The given proof is invalid.");

        let leaf_hash = hash_leaf(proof.empty_leaf, proof.key, proof.value);

        let key_bits: [u1; DEPTH] = key_to_bits(proof.key);
        let op_key_bits: [u1; DEPTH] = key_to_bits(op_key);

        let mut loop = true;

        // Add/delete (op_key, op_value) in case of insertion/deletion
        if !op_upd
        {
            for i in 0..DEPTH
            {
                if loop
                {
                    if key_bits[i] != op_key_bits[i]
                    {
                        assert(!op_del | val_eq(proof.siblings[i], hash_leaf(false, op_key, op_value)), "The given proof does not contain the key-value pair to be deleted as a sibling.");
                        proof.siblings[i] = if op_del { self.default_value } else { leaf_hash };
                        loop = false;
                    }
                }
                else if !op_del
                {
                    assert(val_eq(proof.siblings[i], self.default_value), "The exclusion proof given should lead to a leaf at a level less than or equal to that of the key to be inserted.");
                }
            }
        }

        // If we are deleting, then the above loop should find an unequal bit, else the given proof must be for a singleton tree
        // containing the key to be deleted.
        assert(!op_del | self.bitmap(proof).eq([0; DEPTH]) | !loop);
        
        // In case of deletion, `loop` will remain true if the tree consists of a singleton `(key,value)`, in which case
        // the new tree will be empty.
        let proc_proof = SMTProof::new(op_del & loop, if op_del { proof.key } else { op_key }, if op_del { proof.value } else { op_value }, proof.siblings);
        proc_proof

    }

    pub fn delete_and_compute_root(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, key_to_delete: Key, value_to_delete: Value, root: HashValue) -> HashValue
    {
        self.compute_root(self.process(proof, DELETE, key_to_delete, value_to_delete, root))
    }

    pub fn insert_and_compute_root(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, new_key: Key, new_value: Value, root: HashValue) -> HashValue
    {
        self.compute_root(self.process(proof, INSERT, new_key, new_value, root))
    }

    pub fn update_and_compute_root(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, key: Key, new_value: Value, root: HashValue) -> HashValue
    {
        self.compute_root(self.process(proof, UPDATE, key, new_value, root))
    }

    /// Verify a deletion by means of an exclusion proof of the deleted key
    pub fn verify_deletion(self, proof: SMTProof<Key, Value, HashValue, DEPTH>, deleted_key: Key, deleted_value: Value, new_root: HashValue, old_root: HashValue)
    {
        let val_eq = self.hash_eq;
        let computed_old_root = self.insert_and_compute_root(proof, deleted_key, deleted_value, new_root);

        assert(val_eq(computed_old_root, old_root));
    }


}
