pub type OpTable = [[u8; 10]; 10];

pub const STANDARD_OP_TABLE: OpTable = [[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
                                        [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
                                        [4, 2, 0, 6, 8, 7, 1, 3, 5, 9],
                                        [1, 7, 5, 0, 9, 8, 3, 4, 2, 6],
                                        [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
                                        [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
                                        [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
                                        [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
                                        [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
                                        [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]];

/// # Examples
///
/// ```
/// use damm::{STANDARD_OP_TABLE, generate_with};
///
/// assert_eq!(Some(4), generate_with(&STANDARD_OP_TABLE, &[5, 7, 2]));
/// assert_eq!(Some(0), generate_with(&STANDARD_OP_TABLE, &[]));
/// assert_eq!(None, generate_with(&STANDARD_OP_TABLE, &[3, 10, 6]));
/// ```
pub fn generate_with(op_table: &OpTable, nums: &[u8]) -> Option<u8> {
    nums.iter().fold(Some(0), |res, n| {
        res.and_then(|interim_digit| {
            op_table.get(interim_digit as usize)
                .and_then(|row| row.get(*n as usize))
                .map(|x| *x)
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const DIGITS: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    #[test]
    fn sot_properties() {
        assert_eq!(10, STANDARD_OP_TABLE.len(), "wrong number of rows");

        for (row_i, row) in STANDARD_OP_TABLE.iter().enumerate() {
            assert_eq!(10, row.len(), "wrong number of columns in row {}", row_i);
            assert_eq!(0, row[row_i], "non-zero diagonal in row {}", row_i);
            assert_digit_permutation(&row_i, &row);
        }
    }

    fn assert_digit_permutation(row_i: &usize, row: &[u8; 10]) {
        let mut row_sorted = row.clone();
        row_sorted.sort();

        assert_eq!(DIGITS, row_sorted, "invalid row {}", row_i);
    }
}
