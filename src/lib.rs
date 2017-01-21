//! Generates and validates check digits with the [Damm] algorithm.
//!
//! [Damm]: https://en.wikipedia.org/wiki/Damm_algorithm

/// A Damm operation table. Must meet the requirements of the Damm algorithm
/// (containing only the numbers 0-9, zero diagonal, etc).
pub type OpTable = [[u8; 10]; 10];

/// An operation table, taken from [Wikipedia].
///
/// [Wikipedia]: https://en.wikipedia.org/w/index.php?title=Damm_algorithm&oldid=740274149#Example
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

/// Shortcut for calling [generate_with](fn.generate_with.html) using
/// [STANDARD_OP_TABLE](constant.STANDARD_OP_TABLE.html).
///
/// # Examples
///
/// ```
/// use damm::{generate};
///
/// assert_eq!(Ok(4), generate(&[5, 7, 2]));
/// assert_eq!(Ok(0), generate(&[]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::{generate};
///
/// assert_eq!(Err("non-digit 10 in nums".to_string()), generate(&[3, 10, 6]));
/// ```
pub fn generate<'a, T: IntoIterator<Item = &'a u8>>(nums: T) -> Result<u8, String> {
    generate_with(&STANDARD_OP_TABLE, nums)
}

/// Attempt to generate a check digit with a given [OpTable](type.OpTable.html).
/// Returns `Err` if the `OpTable` is invalid or the input contains numbers
/// other than 0-9.
///
/// # Examples
///
/// ```
/// use damm::{STANDARD_OP_TABLE, generate_with};
///
/// assert_eq!(Ok(4), generate_with(&STANDARD_OP_TABLE, &[5, 7, 2]));
/// assert_eq!(Ok(0), generate_with(&STANDARD_OP_TABLE, &[]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::{STANDARD_OP_TABLE, generate_with};
///
/// let bad_op_table = [[10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10]];
///
/// assert_eq!(Err("non-digit 10 in nums".to_string()),
///            generate_with(&STANDARD_OP_TABLE, &[3, 10, 6]));
///
/// assert_eq!(Err("non-digit 10 in op_table".to_string()),
///            generate_with(&bad_op_table, &[3, 4, 6]));
/// ```
pub fn generate_with<'a, T: IntoIterator<Item = &'a u8>>(op_table: &OpTable,
                                                         nums: T)
                                                         -> Result<u8, String> {
    nums.into_iter().fold(Ok(0), |res, n| {
        res.and_then(|interim_digit| {
            op_table.get(interim_digit as usize)
                .ok_or(format!("non-digit {} in op_table", interim_digit))
                .and_then(|row| row.get(*n as usize).ok_or(format!("non-digit {} in nums", n)))
                .map(|x| *x)
        })
    })
}

/// Shortcut for calling [validate_with](fn.validate_with.html) using
/// [STANDARD_OP_TABLE](constant.STANDARD_OP_TABLE.html).
///
/// # Examples
///
/// ```
/// use damm::{validate};
///
/// assert_eq!(Ok(true), validate(&[5, 7, 2, 4]));
/// assert_eq!(Ok(false), validate(&[5, 7, 2, 1]));
/// assert_eq!(Err("non-digit 10 in nums".to_string()), validate(&[3, 10, 6, 2]));
/// ```
pub fn validate<'a, T: IntoIterator<Item = &'a u8>>(nums: T) -> Result<bool, String> {
    validate_with(&STANDARD_OP_TABLE, nums)
}

/// Attempt to validate that a sequence of digits ends with a valid check
/// digit, using an arbitrary [OpTable](type.OpTable.html). Returns `Err`
/// if the `OpTable` is invalid or the digit sequence contains a number other
/// than 0-9.
///
/// # Examples
///
/// ```
/// use damm::{STANDARD_OP_TABLE, validate_with};
///
/// assert_eq!(Ok(true), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 4]));
/// assert_eq!(Ok(false), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 1]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::{STANDARD_OP_TABLE, validate_with};
///
/// let bad_op_table = [[10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10],
///                     [10, 10, 10, 10, 10, 10, 10, 10, 10, 10]];
///
/// assert_eq!(Err("non-digit 10 in nums".to_string()),
///            validate_with(&STANDARD_OP_TABLE, &[3, 10, 6, 2]));
///
/// assert_eq!(Err("non-digit 10 in op_table".to_string()),
///            validate_with(&bad_op_table, &[3, 4, 6]));
/// ```
pub fn validate_with<'a, T: IntoIterator<Item = &'a u8>>(op_table: &OpTable,
                                                         nums: T)
                                                         -> Result<bool, String> {
    generate_with(op_table, nums).map(|d| d == 0)
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
