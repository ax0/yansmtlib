use dep::smt::{bn254::poseidon_smt, SMT, SMTProof, Operation};

fn main(proof: SMTProof<Field, Field, Field, 3>, key_to_delete: Field, value_to_delete: Field, new_root: Field, root: Field)
{
    let smt: SMT<Field, Field, Field, 3> = poseidon_smt();
    assert(smt.delete_and_compute_root(proof, key_to_delete, value_to_delete, root) == new_root);
}
