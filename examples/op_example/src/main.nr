use dep::smt::{SMTProof, Operation};

fn main(proof: SMTProof<160>, op: pub Operation, op_key: pub Field, op_value: Field, root: pub Field, new_root: pub Field) {
    assert(proof.process(op, op_key, op_value, root).compute_root() == new_root);
}
