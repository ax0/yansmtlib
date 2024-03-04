use dep::smt::{bn254::poseidon_smt, SMT, SMTProof};

fn main(proof: SMTProof<Field, Field, Field, 3>, new_key: Field, new_value: Field, new_root: Field,  root: Field)
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    assert(smt.insert_and_compute_root(proof,new_key, new_value, root) == new_root);
}
