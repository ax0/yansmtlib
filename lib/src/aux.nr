pub(crate) fn foldr<B,C,N>(f: fn(B,C) -> C, c: C, bs: [B; N]) -> C
{
    let mut acc = c;

    for i in 0..N
    {
        acc = f(bs[N - 1 - i], acc);
    }

    acc
}

pub(crate) fn zip<X, Y, N>(xs: [X; N], ys: [Y; N]) -> [(X, Y); N]
{
    let mut out = [(xs[0], ys[0]); N];

    for i in 1..N
    {
        out[i] = (xs[i], ys[i]);
    }

    out
}

pub(crate) fn zip3<X, Y, Z, N>(xs: [X; N], ys: [Y; N], zs: [Z; N]) -> [(X, Y, Z); N]
{
    let mut out = [(xs[0], ys[0], zs[0]); N];

    for i in 1..N
    {
        out[i] = (xs[i], ys[i], zs[i]);
    }

    out
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

