//! Damm operation table.

use std::error;
use std::fmt;
use try_from::TryFrom;

/// A Damm operation table.
#[derive(Debug, Eq, PartialEq)]
pub struct OpTable([[u8; 10]; 10]);

impl OpTable {
    /// Get the rows of an `OpTable`.
    pub fn rows(&self) -> &[[u8; 10]; 10] {
        &self.0
    }
}

impl TryFrom<[[u8; 10]; 10]> for OpTable {
    type Err = InvalidOpTable;

    /// Try to create an `OpTable` from a `[[u8; 10]; 10]` operation table. The table must meet the
    /// requirements of the Damm algorithm (it must only contain the digits 0-9 and have a zero
    /// diagonal).
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate damm;
    /// extern crate try_from;
    /// use damm::optable::*;
    /// use try_from::TryFrom;
    ///
    /// fn main() {
    ///     let rows = [[0, 3, 1, 7, 5, 9, 8, 6, 4, 2],
    ///                 [7, 0, 9, 2, 1, 5, 4, 8, 6, 3],
    ///                 [4, 2, 0, 6, 8, 7, 1, 3, 5, 9],
    ///                 [1, 7, 5, 0, 9, 8, 3, 4, 2, 6],
    ///                 [6, 1, 2, 3, 0, 4, 5, 9, 7, 8],
    ///                 [3, 6, 7, 4, 2, 0, 9, 5, 8, 1],
    ///                 [5, 8, 6, 9, 7, 2, 0, 1, 3, 4],
    ///                 [8, 9, 4, 5, 3, 6, 2, 0, 1, 7],
    ///                 [9, 4, 3, 8, 6, 1, 7, 2, 0, 5],
    ///                 [2, 5, 8, 1, 4, 3, 6, 7, 9, 0]];
    ///
    ///     assert!(OpTable::try_from(rows).is_ok());
    /// }
    /// ```
    ///
    /// # Errors
    ///
    /// ```
    /// extern crate damm;
    /// extern crate try_from;
    /// use damm::optable::*;
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
    ///     assert_eq!(Err(InvalidOpTable::NonZeroDiagonal(9, 3)),
    ///                OpTable::try_from(nonzero_diag));
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
    /// A row is incomplete - it does not contain exactly one of the digits 0-9.
    /// Contains the invalid row, and the index of the row within the table.
    IncompleteRow([u8; 10], usize),

    /// A row does not have a zero in the diagonal position.
    /// Contains the invalid diagonal value, and the index of the row within the table.
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
    }

    #[test]
    fn error_description() {
        assert_eq!("non-zero diagonal value",
                   InvalidOpTable::NonZeroDiagonal(8, 3).description());

        assert_eq!("incomplete row; does not contain every digit",
                   InvalidOpTable::IncompleteRow([0, 1, 2, 3, 4, 5, 6, 7, 8, 8], 3).description());
    }

    #[test]
    fn sot_is_valid() {
        assert!(OpTable::try_from(STANDARD_OP_TABLE.0).is_ok());
    }
}
