use dep::smt_noir::SMTProof;

fn main(proof: SMTProof<3>, key_to_delete: Field, value_to_delete: Field, new_root: Field, root: Field)
{
    assert(proof.delete_and_compute_root(key_to_delete, value_to_delete, root) == new_root);
}
