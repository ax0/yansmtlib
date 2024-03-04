use dep::smt::{bn254::poseidon_smt, SMT, SMTProof};

fn main(key: Field, value: Field, siblings: [Field; 2], root: Field)
{
    let smt: SMT<Field, Field, Field, 2> = poseidon_smt();
    let proof = SMTProof::new(false, key, value, siblings);
    assert(smt.verify(proof, root));
}
