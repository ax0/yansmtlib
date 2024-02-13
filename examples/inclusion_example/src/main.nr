use dep::smt_noir::SMTProof;

fn main(key: Field, value: Field, siblings: [Field; 2], root: Field)
{
    let proof = SMTProof::new(false, key, value, siblings);
    assert(proof.verify(root));
}
