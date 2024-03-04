use dep::smt::{bn254::poseidon_smt, SMT, SMTProof};

fn main(proof: SMTProof<Field, Field, Field, 3>, key: Field, value: Field, root: Field, new_root: Field)
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    assert(smt.update_and_compute_root(proof, key, value, root) == new_root);
}
