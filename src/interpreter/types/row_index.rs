/// A position in an in-memory row sequence: an index into a `Vec`, a slice, or a column's backing
/// storage.
///
/// `RowIndex` is the host's `usize`, so it is as wide as the platform's address space and no wider.
/// It types a tile's `row_starts` and never appears as a value, so it is distinct from the CCL
/// unsigned integer [`Value::UInt`](super::Value::UInt), a `u64` whose width does not vary by
/// platform.
pub type RowIndex = usize;

/// The row a CCL `UInt` names. Panics where `uint` exceeds the host's address space, since such a
/// value cannot index in-memory rows.
pub fn row_index(uint: u64) -> RowIndex {
    RowIndex::try_from(uint)
        .unwrap_or_else(|_| panic!("UInt {uint} exceeds the host's row index range"))
}

/// The CCL `UInt` carrying the number of `row`. Lossless: `usize` is at most 64 bits on every
/// supported host.
pub fn uint_of_row(row: RowIndex) -> u64 {
    row as u64
}
