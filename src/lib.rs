//! Generates and validates check digits with the [Damm] algorithm.
//!
//! [Damm]: https://en.wikipedia.org/wiki/Damm_algorithm

extern crate try_from;

use std::error;
use std::fmt;

use try_from::TryFrom;

/// A Damm operation table. Must meet the requirements of the Damm algorithm
/// (containing only the numbers 0-9, zero diagonal, etc).
#[derive(Debug, Eq, PartialEq)]
pub struct OpTable([[u8; 10]; 10]);

impl TryFrom<[[u8; 10]; 10]> for OpTable {
    type Err = InvalidOpTable;

    /// # Examples
    ///
    /// ```
    /// extern crate try_from;
    /// extern crate damm;
    /// use damm::*;
    /// use try_from::TryFrom;
    ///
    /// fn main() {
    ///     let op_table = [[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
    ///                     [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
    ///                     [4, 2, 0, 6, 8, 7, 1, 3, 5, 9],
    ///                     [1, 7, 5, 0, 9, 8, 3, 4, 2, 6],
    ///                     [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
    ///                     [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
    ///                     [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
    ///                     [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
    ///                     [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
    ///                     [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]];
    ///
    ///      assert!(OpTable::try_from(op_table).is_ok());
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// ```
    /// extern crate try_from;
    /// extern crate damm;
    /// use damm::*;
    /// use try_from::TryFrom;
    ///
    /// fn main() {
    ///     let nonzero_diag = [[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
    ///                         [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
    ///                         [4, 2, 0, 6, 8, 7, 1, 3, 5, 9],
    ///                         [1, 7, 5, 9, 0, 8, 3, 4, 2, 6],
    ///                         [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
    ///                         [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
    ///                         [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
    ///                         [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
    ///                         [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
    ///                         [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]];
    ///
    ///     let incomplete_row = [[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
    ///                           [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
    ///                           [4, 4, 0, 6, 8, 7, 1, 3, 5, 9],
    ///                           [1, 7, 5, 0, 9, 8, 3, 4, 2, 6],
    ///                           [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
    ///                           [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
    ///                           [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
    ///                           [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
    ///                           [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
    ///                           [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]];
    ///
    ///      assert_eq!(Err(InvalidOpTable::NonZeroDiagonal(9, 3)),
    ///                 OpTable::try_from(nonzero_diag));
    ///
    ///      assert_eq!(Err(InvalidOpTable::IncompleteRow([4, 4, 0, 6, 8, 7, 1, 3, 5, 9], 2)),
    ///                 OpTable::try_from(incomplete_row));
    /// }
    /// ```
    fn try_from(rows: [[u8; 10]; 10]) -> Result<OpTable, InvalidOpTable> {
        for (row_i, row) in rows.iter().enumerate() {
            let n = row[row_i];

            if n != 0 {
                return Err(InvalidOpTable::NonZeroDiagonal(n, row_i));
            } else if !is_digit_permutation(*row) {
                return Err(InvalidOpTable::IncompleteRow(*row, row_i));
            }
        }

        Ok(OpTable(rows))
    }
}

const DIGITS: [u8; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

fn is_digit_permutation(mut row: [u8; 10]) -> bool {
    row.sort();

    return DIGITS == row;
}

/// Error for an invalid operation table.
#[derive(Debug, Eq, PartialEq)]
pub enum InvalidOpTable {
    IncompleteRow([u8; 10], usize),
    NonZeroDiagonal(u8, usize),
}

impl fmt::Display for InvalidOpTable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let msg = match *self {
            InvalidOpTable::IncompleteRow(row, row_i) => {
                format!("incomplete row {}: {:?}", row_i, row)
            }
            InvalidOpTable::NonZeroDiagonal(n, row_i) => {
                format!("non-zero diagonal in row {}: {}", row_i, n)
            }
        };

        write!(f, "{}", msg)
    }
}

impl error::Error for InvalidOpTable {
    fn description(&self) -> &str {
        match *self {
            InvalidOpTable::IncompleteRow(_, _) => "incomplete row; does not contain every digit",
            InvalidOpTable::NonZeroDiagonal(_, _) => "non-zero diagonal value",
        }
    }
}

/// An error related to a Damm operation.
#[derive(Debug, Eq, PartialEq)]
pub enum DammError {
    /// A bad input number; contains the bad entry.
    BadInputNum(u8),
}

impl fmt::Display for DammError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let msg = match *self {
            DammError::BadInputNum(n) => format!("non-digit {} in input number sequence", n),
        };

        write!(f, "{}", msg)
    }
}

impl error::Error for DammError {
    fn description(&self) -> &str {
        match *self {
            DammError::BadInputNum(_) => "bad input number",
        }
    }
}

/// An operation table, taken from [Wikipedia].
///
/// [Wikipedia]: https://en.wikipedia.org/w/index.php?title=Damm_algorithm&oldid=740274149#Example
pub const STANDARD_OP_TABLE: OpTable = OpTable([[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
                                                [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
                                                [4, 2, 0, 6, 8, 7, 1, 3, 5, 9],
                                                [1, 7, 5, 0, 9, 8, 3, 4, 2, 6],
                                                [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
                                                [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
                                                [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
                                                [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
                                                [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
                                                [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]]);

/// Shortcut for calling [generate_with](fn.generate_with.html) using
/// [STANDARD_OP_TABLE](constant.STANDARD_OP_TABLE.html).
///
/// # Examples
///
/// ```
/// use damm::*;
///
/// assert_eq!(Ok(4), generate(&[5, 7, 2]));
/// assert_eq!(Ok(0), generate(&[]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
///
/// assert_eq!(Err(DammError::BadInputNum(10)), generate(&[3, 10, 6]));
/// ```
pub fn generate<'a, T: IntoIterator<Item = &'a u8>>(nums: T) -> Result<u8, DammError> {
    generate_with(&STANDARD_OP_TABLE, nums)
}

/// Attempt to generate a check digit with a given [OpTable](type.OpTable.html).
/// Returns `Err` if the `OpTable` is invalid or the input contains numbers
/// other than 0-9.
///
/// # Examples
///
/// ```
/// use damm::*;
///
/// assert_eq!(Ok(4), generate_with(&STANDARD_OP_TABLE, &[5, 7, 2]));
/// assert_eq!(Ok(0), generate_with(&STANDARD_OP_TABLE, &[]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
///
/// assert_eq!(Err(DammError::BadInputNum(10)), generate_with(&STANDARD_OP_TABLE, &[3, 10, 6]));
/// ```
pub fn generate_with<'a, T: IntoIterator<Item = &'a u8>>(op_table: &OpTable,
                                                         nums: T)
                                                         -> Result<u8, DammError> {
    nums.into_iter().fold(Ok(0), |res, &n| {
        res.and_then(|interim_digit| {
            op_table.0
                .get(interim_digit as usize)
                .unwrap() // OpTables are guaranteed to only contain digits, so this is safe
                .get(n as usize).ok_or(DammError::BadInputNum(n))
                .map(|&x| x)
        })
    })
}

/// Shortcut for calling [validate_with](fn.validate_with.html) using
/// [STANDARD_OP_TABLE](constant.STANDARD_OP_TABLE.html).
///
/// # Examples
///
/// ```
/// use damm::*;
///
/// assert_eq!(Ok(true), validate(&[5, 7, 2, 4]));
/// assert_eq!(Ok(false), validate(&[5, 7, 2, 1]));
/// assert_eq!(Err(DammError::BadInputNum(10)), validate(&[3, 10, 6, 2]));
/// ```
pub fn validate<'a, T: IntoIterator<Item = &'a u8>>(nums: T) -> Result<bool, DammError> {
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
/// use damm::*;
///
/// assert_eq!(Ok(true), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 4]));
/// assert_eq!(Ok(false), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 1]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
///
/// assert_eq!(Err(DammError::BadInputNum(10)), validate_with(&STANDARD_OP_TABLE, &[3, 10, 6, 2]));
/// ```
pub fn validate_with<'a, T: IntoIterator<Item = &'a u8>>(op_table: &OpTable,
                                                         nums: T)
                                                         -> Result<bool, DammError> {
    generate_with(op_table, nums).map(|d| d == 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;
    use try_from::TryFrom;

    // originally I had the error_fmt and error_description tests as doctests,
    // but I moved them here because I don't want to suppress the default
    // documentation

    #[test]
    fn error_fmt() {
        assert_eq!("non-zero diagonal in row 3: 8",
                   format!("{}", InvalidOpTable::NonZeroDiagonal(8, 3)));

        assert_eq!("incomplete row 3: [0, 1, 2, 3, 4, 5, 6, 7, 8, 8]",
                   format!("{}",
                           InvalidOpTable::IncompleteRow([0, 1, 2, 3, 4, 5, 6, 7, 8, 8], 3)));

        assert_eq!("non-digit 10 in input number sequence",
                   format!("{}", DammError::BadInputNum(10)));
    }

    #[test]
    fn error_description() {
        assert_eq!("non-zero diagonal value",
                   InvalidOpTable::NonZeroDiagonal(8, 3).description());

        assert_eq!("incomplete row; does not contain every digit",
                   InvalidOpTable::IncompleteRow([0, 1, 2, 3, 4, 5, 6, 7, 8, 8], 3).description());

        assert_eq!("bad input number", DammError::BadInputNum(10).description());
    }

    #[test]
    fn sot_is_valid() {
        assert!(OpTable::try_from(STANDARD_OP_TABLE.0).is_ok());
    }
}
