use dep::smt_noir::SMTProof;

fn main(proof: SMTProof<3>, key: Field, value: Field, root: Field, new_root: Field)
{
    assert(proof.update_and_compute_root(key, value, root) == new_root);
}
