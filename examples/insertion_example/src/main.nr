use dep::smt_noir::SMTProof;

fn main(proof: SMTProof<3>, new_key: Field, new_value: Field, new_root: Field,  root: Field)
{
    assert(proof.insert_and_compute_root(new_key, new_value, root) == new_root);
}
