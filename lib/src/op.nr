/// Enum for tree processing operations together with useful predicates
type Operation = Field;

global INSERT: Field = 0;
global UPDATE: Field = 1;
global DELETE: Field = 2;

pub(crate) fn is_op(op: Operation) -> bool
{
    (op == DELETE) | (op == INSERT) | (op == UPDATE)
}

pub(crate) fn is_insertion(op: Operation) -> bool
{
    op == INSERT
}

pub(crate) fn is_update(op: Operation) -> bool
{
    op == UPDATE
}

pub(crate) fn is_deletion(op: Operation) -> bool
{
    op == DELETE
}
