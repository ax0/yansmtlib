pub(crate) fn foldr<B,C,N>(f: fn(B,C) -> C, c: C, bs: [B; N]) -> C
{
    let mut acc = c;

    for i in 0..N
    {
        acc = f(bs[N - 1 - i], acc);
    }

    acc
}

/// Helper function for copying slices to arrays
fn slice_to_array<T,N>(x: [T]) -> [T; N]
{
    let mut out = [x[0]; N];

    for i in 1..N
    {
        out[i] = x[i];
    }

    out
}

/// Key bits in little-endian format
#[field(bn254)]
pub(crate) fn key_to_bits<N>(key: Field) -> [u1; N]
{
    slice_to_array(key.to_le_bits(N))
}

