mod aux;

use aux::{foldr, key_to_bits};
use dep::std::cmp::Eq;

/// Enum for tree processing operations together with useful predicates
type Operation = Field;

global INSERT: Field = 0;
global UPDATE: Field = 1;
global DELETE: Field = 2;

fn is_op(op: Operation) -> bool
{
    (op == DELETE) | (op == INSERT) | (op == UPDATE)
}

fn is_insertion(op: Operation) -> bool
{
    op == INSERT
}

fn is_update(op: Operation) -> bool
{
    op == UPDATE
}

fn is_deletion(op: Operation) -> bool
{
    op == DELETE
}

/// Sparse Merkle tree (SMT) proof structure.
struct SMTProof<DEPTH>
{
    /// Indicator of whether the key resolves to an empty leaf, i.e. whether this is a
    /// direct proof of exclusion (true) or an inclusion proof (false)
    empty_leaf: bool,
    /// Key to resolve
    key: Field,
    /// Value contained in leaf, which is ignored in case empty_leaf == true
    value: Field,
    /// The siblings along the path down the tree
    siblings: [Field; DEPTH]
}

impl<DEPTH> SMTProof<DEPTH>
{
    /// SMT proof constructor
    pub fn new(empty_leaf: bool, key: Field, value: Field, siblings: [Field; DEPTH]) -> Self
    {
        Self
        {
            empty_leaf, key, value, siblings
        }
    }

    /// Empty SMT proof constructor
    pub fn empty() -> Self
    {
        SMTProof::new(true, 0, 0, [0; DEPTH])
    }

    
    /// Proof bitmap. Returns an array of the form [1,1,...,1,0,...,0], where 1 indicates
    /// those nodes that are actually part of the given proof (cf. default value optimisation).
    fn bitmap(self) -> [Field; DEPTH]
    {
        let mut node_bit = 0; // Indicator of whether we are dealing with a non-empty node
        let mut out = [0; DEPTH];

        for i in 0..DEPTH
        {
            // Starting from the maximum depth, check whether we have reached a non-empty node
            // and set the bit to 1 if we have.
            node_bit += (1 - node_bit) * (!self.siblings[DEPTH - 1 - i].eq(0)) as Field;
            out[DEPTH - 1 - i] = node_bit;
        }

        out
    }

    /// Method for computing the root of the SMT
    pub fn compute_root(self) -> Field
    {
        // Decompose keys to bits (little-endian convention)
        let key_bits: [u1; DEPTH] = key_to_bits(self.key);

        // Non-empty node bitmap
        let node_bitmap = self.bitmap();

        let leaf_hash = if self.empty_leaf { 0 } else { hash_leaf(self.key, self.value) };

        let mut params: [(Field, u1, Field); DEPTH] = [(0,0,0); DEPTH];

        for i in 0..DEPTH
        {
            params[i] = (self.siblings[i], key_bits[i], node_bitmap[i]);
        }

        foldr(hash_comp, leaf_hash, params)
    }

    /// SMT membership verification. Returns the result as a boolean.
    ///
    /// # Arguments
    /// * `inclusion` - Indicator of whether an inclusion is verified
    /// * `empty_node` - Indicator of whether the (key, value) pair being checked is empty. Relevant for exclusion proofs.
    /// * `excluded_key` - Key whose exclusion from the tree is verified
    /// * `key` - The key whose inclusion is
    pub fn verify_membership(self, inclusion: bool, excluded_key: Field, root: Field) -> bool
    {
        // Decompose keys to bits
        let key_bits: [u1; DEPTH] = key_to_bits(self.key);
        let excluded_key_bits: [u1; DEPTH] = key_to_bits(excluded_key);

        assert(!inclusion | !self.empty_leaf, "A proof resolving to an empty leaf is an exclusion proof.");

        if !inclusion
        {
            // Follow the siblings to the first unequal bit in the case of an indirect exclusion proof
            let mut key_bits_eq = !self.empty_leaf;
            
            // Check that excluded_key and key agree up to the (potentially) empty leaf corresponding to `key` in the tree
            for i in 0..DEPTH
            {
                if key_bits_eq
                {
                    if key_bits[i] != excluded_key_bits[i]
                    {
                        // Empty node where `excluded_key` should be.
                        assert(self.siblings[i] == 0, "For a key to be excluded, its leaf must be empty.");
                        key_bits_eq = false;
                    }
                }
            }

            assert(!key_bits_eq, "The keys must either differ or the proof should resolve the excluded key to the empty leaf.");
        }

        self.compute_root() == root
    }

    /// Proof verifier (i.e. proof of inclusion)
    pub fn verify(self, root: Field) -> bool
    {
        self.verify_membership(true, 0, root)
    }

    /// Proof of exclusion (i.e. establish exclusion of a key using the given proof)
    pub fn verify_exclusion(self, excluded_key: Field, root: Field) -> bool
    {
        self.verify_membership(false, excluded_key, root)
    }

    /// Processor of OP(OP_KEY, OP_VALUE).
    /// The other inputs are assumed to be the following depending on the operation:
    /// INSERT: An exclusion proof for `op_key`.
    /// UPDATE: An inclusion proof for the `(op_key, value)` pair to be replaced by `(op_key, op_value)`.
    /// DELETE: An inclusion proof for a `(key, value)` pair for which `(op_key, op_value)` lies in the set {root, sibling[0], ..., sibling[N-1]}.
    pub fn process(mut self, op: Operation, op_key: Field, op_value: Field, root: Field)
                  -> Self
    {
        assert(is_op(op));
        let op_ins = is_insertion(op);
        let op_upd = is_update(op);
        let op_del = is_deletion(op);

        // Key update consistency
        assert(!op_upd | (self.key == op_key), "The proof key must be the key to be updated.");
        
        // Depending on `op`, check for inclusion/exclusion of (op_key, op_value)
        // For insertions, check for exclusion of `op_key`, else check for inclusion
        // of `(key, value)`.
        assert(self.verify_membership(!op_ins, if op_ins { op_key } else { 0 }, root), "The given proof is invalid.");

        let leaf_hash = if op_del { 0 } else { hash_leaf(self.key, self.value) };

        let key_bits: [u1; DEPTH] = key_to_bits(self.key);
        let op_key_bits: [u1; DEPTH] = key_to_bits(op_key);

        // TODO
        let mut loop = !self.empty_leaf;

        // Add/delete (op_key, op_value) in case of insertion/deletion
        if !op_upd
        {
            for i in 0..DEPTH
            {
                if loop
                {
                    if key_bits[i] != op_key_bits[i]
                    {
                        assert(!op_del | (self.siblings[i] == hash_leaf(op_key, op_value)), "The given proof does not contain the key-value pair to be deleted as a sibling.");
                        self.siblings[i] = leaf_hash;
                        loop = false;
                    }
                }
            }
        }

        // If we are deleting, then the above loop should find an unequal bit, else the given proof must be for a singleton tree
        // containing the key to be deleted.
        assert(!op_del | self.bitmap().eq([0; DEPTH]) | !loop);
        
        // In case of deletion, loop will remain true if the tree consists of a singleton `(key,value)`, in which case
        // the new tree will be empty.
        let proc_proof = SMTProof::new(op_del & loop, if op_del { self.key } else { op_key }, if op_del { self.value } else { op_value }, self.siblings);
        proc_proof

    }

    pub fn delete_and_compute_root(self, key_to_delete: Field, value_to_delete: Field, root: Field) -> Field
    {
        self.process(DELETE, key_to_delete, value_to_delete, root).compute_root()
    }

    pub fn insert_and_compute_root(self, new_key: Field, new_value: Field, root: Field) -> Field
    {
        self.process(INSERT, new_key, new_value, root).compute_root()
    }

    pub fn update_and_compute_root(self, key: Field, new_value: Field, root: Field) -> Field
    {
        self.process(UPDATE, key, new_value, root).compute_root()
    }

    /// Verify a deletion by means of an exclusion proof of the deleted key
    pub fn verify_deletion(self, deleted_key: Field, deleted_value: Field, new_root: Field, old_root: Field)
    {
        let computed_old_root = self.insert_and_compute_root(deleted_key, deleted_value, new_root);

        assert(computed_old_root == old_root);
    }

    
}

/// Leaf hasher
#[field(bn254)]
fn hash_leaf(key: Field, value: Field) -> Field
{
    dep::std::hash::poseidon::bn254::hash_3([key, value, 1])
}

#[field(bn254)]
fn hash_branch(l: Field, r: Field) -> Field
{
    dep::std::hash::poseidon::bn254::hash_2([l,r])
}

fn hash_comp(cur_params: (Field, u1, Field), cur_hash: Field) -> Field
{
    let (sibling, key_bit, node_bit) = cur_params;

    // Swap left and right if bit is 1
    let l = (1 - key_bit as Field)*cur_hash + (key_bit as Field)*sibling;
    let r = (1 - key_bit as Field)*sibling + (key_bit as Field)*cur_hash;
    
    node_bit*hash_branch(l,r) + (1 - node_bit)*cur_hash
}

#[test]
fn compute_root_test()
{
    let proof = SMTProof::new(true, 1, 10, [0,0,0]);

    assert(proof.compute_root() == 0);
}

#[test]
fn singleton_inclusion_test()
{
    let root = 18069132284520201727832024694996019315677027866342868341249356941629964797693;
    
    let proof = SMTProof::new(false, 0, 10, [0,0]);

    assert(proof.verify(root));
}

#[test]
fn exclusion_tests()
{
    let root = 18069132284520201727832024694996019315677027866342868341249356941629964797693;
    let excluded_key = 1;
    let proof = SMTProof::new(false, 0, 10, [0,0]);

    assert(proof.verify_exclusion(excluded_key, root));

    let root = 20779312880898074970670314993181086284764142729786515947732018439009703374807;
    let proof = SMTProof::new(false, 3, 10, [10191582656864925769156865225870025203058537754039061649524289359932542504350, 0]);

    assert(proof.verify_exclusion(excluded_key, root));

    let root = 0;
    let proof: SMTProof<2> = SMTProof::empty();

    assert(proof.verify_exclusion(excluded_key, root));
    
    // 3-bit keys where an empty leaf stands in the way
    let root = 11200423218306708598617125785191052227073238119871447957507555181072865815573;
    let proof = SMTProof::new(true, 3, 0, [5425677653063334718369405482428677484996329809930801119387142625676133786812, 12647614716995876798787341026950410656216295113507334411840593152532739648659, 0]);

    assert(proof.verify_exclusion(3, root));

}

#[test]
fn insertion_test()
{
    // Start with an empty tree of max depth 3 to which we add (1, 10)
    let proof: SMTProof<3> = SMTProof::empty();
    let new_key = 1;
    let new_value = 10;
    let root = 0;
    let new_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;

    assert(proof.insert_and_compute_root(new_key, new_value, root) == new_root);

    // Now add (5, 20)
    let proof = SMTProof::new(false, 1, 10, [0,0,0]);
    let new_key = 5;
    let new_value = 20;
    let root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let new_root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;

    assert(proof.insert_and_compute_root(new_key, new_value, root) == new_root);
    
    // And add (2, 10)
    let proof = SMTProof::new(true, 2, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]); 
    let new_key = 2;
    let new_value = 10;
    let root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;
    let new_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;

    assert(proof.insert_and_compute_root(new_key, new_value, root) == new_root);
}

#[test]
fn deletion_test()
{
    // Reverse of insertion tests
    // Start with a prepopulated tree of max depth 3 containing [(2,10), (5,20), (1,10)]
    let old_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;

    // Verify the deletion of (2,10)
    let proof = SMTProof::new(true, 2, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]);
    let deleted_key = 2;
    let deleted_value = 10;
    let new_root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;

    proof.verify_deletion(deleted_key, deleted_value, new_root, old_root);

    // Alternatively, delete (2,10) and check that we get the same result. Use the proof for (5,20):
    let proof = SMTProof::new(false, 5, 20, [hash_leaf(2,10), 0x00, 0x273b79dd2dbb4163ccbee92a259242d3d728b787e5cb5b69e45509c6b8b6a19c]);
    assert(proof.delete_and_compute_root(deleted_key, deleted_value, old_root) == new_root);
    dep::std::println(hash_leaf(2,10));
    
    // Now delete (5,20)
    let old_root = new_root;
    let new_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let proof = SMTProof::new(false, 1, 10, [0,0,0]);
    let deleted_key = 5;
    let deleted_value = 20;

    proof.verify_deletion(deleted_key, deleted_value, new_root, old_root);

    // Again, using the alternative approach, this time using the proof for (1,10):
    let proof = SMTProof::new(false, 1, 10, [0, 0, hash_leaf(5,20)]);
    assert(proof.delete_and_compute_root(deleted_key, deleted_value, old_root) == new_root);

    // And finally delete (1,10):
    let proof: SMTProof<3> = SMTProof::empty();
    let old_root = new_root;
    let new_root = 0;
    let deleted_key = 1;
    let deleted_value = 10;

    proof.verify_deletion(deleted_key, deleted_value, new_root, old_root);

    // And using the alternative approach via a proof for (1,10):
    let proof = SMTProof::new(false, 1, 10, [0;3]);
    assert(proof.delete_and_compute_root(deleted_key, deleted_value, old_root) == new_root);   
}

#[test]
fn update_test()
{
    // Start with a singleton tree containing (1,10) and update the value to 20
    let old_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let proof = SMTProof::new(false, 1, 10, [0; 3]);
    let new_root = 10455899125583343723660476237945369238709688510771807024557867026308788199134;
    assert(proof.update_and_compute_root(1, 20, old_root) == new_root);

    // Now update the same key in a tree containing [(2,10), (5,20), (1,10)]
    let old_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;
    let proof = SMTProof::new(false, 1, 10, [5425677653063334718369405482428677484996329809930801119387142625676133786812, 0, 19735322091264336512950257930646484565260209912040081148652494901448121943620]);
    let new_root = 15867537976956771516439137845581469689324005659662177136611526013827776190974;
    assert(proof.update_and_compute_root(1, 20, old_root) == new_root);
}

#[test]
fn inclusion_test()
{
    let root = 13641896154762338744380940191307230798491407654292674264435730700274728762350;
    let proof = SMTProof::new(false, 0, 10, [13289200780321203042507732593690917219706942416586022721573559355563330806949, 5425677653063334718369405482428677484996329809930801119387142625676133786812]);

    assert(proof.verify(root));
}


#[test]
fn no_sibling_indicator_test()
{
    let empty_proof: SMTProof<10> = SMTProof::empty();
    assert(empty_proof.bitmap() == [0; 10]);
}

#[test]
fn all_sibling_indicator_test()
{
    let proof = SMTProof::new(false, 0, 10, [13289200780321203042507732593690917219706942416586022721573559355563330806949, 5425677653063334718369405482428677484996329809930801119387142625676133786812]);
    assert(proof.bitmap() == [1,1]);
}


