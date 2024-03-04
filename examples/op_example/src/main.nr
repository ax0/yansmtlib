use dep::smt::{bn254::poseidon_smt, SMT, SMTProof, Operation};

fn main(proof: SMTProof<Field, Field, Field, 160>, op: pub Field, op_key: pub Field, op_value: Field, root: pub Field, new_root: pub Field)
{
    let smt: SMT<Field, Field, Field, 160> = poseidon_smt();
    assert(smt.compute_root(smt.process(proof,op, op_key, op_value, root)) == new_root);
}
