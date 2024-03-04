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

// Tests
#[test]
fn poseidon_compute_root_test()
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    let proof = SMTProof::new(true, 1, 10, [0,0,0]);

    assert(smt.compute_root(proof) == 0);
}

#[test]
fn poseidon_singleton_inclusion_test()
{
    let smt: SMT<Field, Field, Field, 2> = poseidon_smt();
    
    let root = 18069132284520201727832024694996019315677027866342868341249356941629964797693;
    
    let proof = SMTProof::new(false, 0, 10, [0,0]);

    assert(smt.verify(proof, root));
}

#[test]
fn poseidon_exclusion_tests()
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    
    // 3-bit keys where an empty leaf stands in the way
    let root = 11200423218306708598617125785191052227073238119871447957507555181072865815573;
    let proof = SMTProof::new(true, 3, 0, [5425677653063334718369405482428677484996329809930801119387142625676133786812, 12647614716995876798787341026950410656216295113507334411840593152532739648659, 0]);

    assert(smt.verify_exclusion(proof, 3, root));

    // Start with a prepopulated tree of max depth 3 containing [(2,10), (5,20), (1,10)] and prove that 0 is not in the tree
    let root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;
    let proof = SMTProof::new(false, 2, 10, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]);
    assert(smt.verify_exclusion(proof, 0, root));

    // Remove (2,10) and prove that 0 is not in the tree
    let root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;
    let proof = SMTProof::new(true, 0, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]);
    assert(smt.verify_exclusion(proof, 0, root));

    // Technically the key in the proof doesn't matter as long as it resolves properly. For example:
    let proof = SMTProof::new(true, 2, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]);
    assert(smt.verify_exclusion(proof, 0, root));
}

#[test]
fn poseidon_insertion_test()
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    
    // Start with an empty tree of max depth 3 to which we add (1, 10)
    let proof = smt.empty_proof();
    let new_key = 1;
    let new_value = 10;
    let root = 0;
    let new_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;

    assert(smt.insert_and_compute_root(proof, new_key, new_value, root) == new_root);

    // Now add (5, 20)
    let proof = SMTProof::new(false, 1, 10, [0,0,0]);
    let new_key = 5;
    let new_value = 20;
    let root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let new_root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;

    assert(smt.insert_and_compute_root(proof, new_key, new_value, root) == new_root);
    
    // And add (2, 10)
    let proof = SMTProof::new(true, 2, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]); 
    let new_key = 2;
    let new_value = 10;
    let root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;
    let new_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;

    assert(smt.insert_and_compute_root(proof, new_key, new_value, root) == new_root);
}

#[test]
fn poseidon_deletion_test()
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    let hash_leaf = smt.hash_leaf;
    
    // Reverse of insertion tests
    // Start with a prepopulated tree of max depth 3 containing [(2,10), (5,20), (1,10)]
    let old_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;

    // Verify the deletion of (2,10)
    let proof = SMTProof::new(true, 2, 0, [2996922252417443465966018502620271371886265112327727499202960396308391015872, 0, 0]);
    let deleted_key = 2;
    let deleted_value = 10;
    let new_root = 18508676215879297097623875026733409214533276976775300711445773127911914420383;

    smt.verify_deletion(proof, deleted_key, deleted_value, new_root, old_root);

    // Alternatively, delete (2,10) and check that we get the same result. Use the proof for (5,20):
    let proof = SMTProof::new(false, 5, 20, [hash_leaf(false, 2, 10), 0x00, 0x273b79dd2dbb4163ccbee92a259242d3d728b787e5cb5b69e45509c6b8b6a19c]);
    assert(smt.delete_and_compute_root(proof, deleted_key, deleted_value, old_root) == new_root);
    
    // Now delete (5,20)
    let old_root = new_root;
    let new_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let proof = SMTProof::new(false, 1, 10, [0,0,0]);
    let deleted_key = 5;
    let deleted_value = 20;

    smt.verify_deletion(proof, deleted_key, deleted_value, new_root, old_root);

    // Again, using the alternative approach, this time using the proof for (1,10):
    let proof = SMTProof::new(false, 1, 10, [0, 0, hash_leaf(false, 5, 20)]);
    assert(smt.delete_and_compute_root(proof, deleted_key, deleted_value, old_root) == new_root);

    // And finally delete (1,10):
    let proof = smt.empty_proof();
    let old_root = new_root;
    let new_root = 0;
    let deleted_key = 1;
    let deleted_value = 10;

    smt.verify_deletion(proof,deleted_key, deleted_value, new_root, old_root);

    // And using the alternative approach via a proof for (1,10):
    let proof = SMTProof::new(false, 1, 10, [0;3]);
    assert(smt.delete_and_compute_root(proof, deleted_key, deleted_value, old_root) == new_root);   
}

#[test]
fn poseidon_update_test()
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    
    // Start with a singleton tree containing (1,10) and update the value to 20
    let old_root = 17745286145841574461080870515538432642488178426701997089182084200349283295644;
    let proof = SMTProof::new(false, 1, 10, [0; 3]);
    let new_root = 10455899125583343723660476237945369238709688510771807024557867026308788199134;
    assert(smt.update_and_compute_root(proof, 1, 20, old_root) == new_root);

    // Now update the same key in a tree containing [(2,10), (5,20), (1,10)]
    let old_root = 12969130658784983238190929361355671504677343582636515678221303782186445329124;
    let proof = SMTProof::new(false, 1, 10, [5425677653063334718369405482428677484996329809930801119387142625676133786812, 0, 19735322091264336512950257930646484565260209912040081148652494901448121943620]);
    let new_root = 15867537976956771516439137845581469689324005659662177136611526013827776190974;
    assert(smt.update_and_compute_root(proof, 1, 20, old_root) == new_root);
}

#[test]
fn inclusion_test()
{
    let smt: SMT<Field, Field, Field, 2> = poseidon_smt();

    let root = 13641896154762338744380940191307230798491407654292674264435730700274728762350;
    let proof = SMTProof::new(false, 0, 10, [13289200780321203042507732593690917219706942416586022721573559355563330806949, 5425677653063334718369405482428677484996329809930801119387142625676133786812]);

    assert(smt.verify(proof, root));
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


#[test]
fn no_sibling_indicator_test()
{
    let smt: SMT<Field, Field, Field, 10> = poseidon_smt();
    let empty_proof = smt.empty_proof();
    assert(smt.bitmap(empty_proof) == [0; 10]);
}

#[test]
fn all_sibling_indicator_test()
{
    let smt: SMT<Field, Field, Field, 2> = poseidon_smt();
    let proof = SMTProof::new(false, 0, 10, [13289200780321203042507732593690917219706942416586022721573559355563330806949, 5425677653063334718369405482428677484996329809930801119387142625676133786812]);
    assert(smt.bitmap(proof) == [1,1]);
}
