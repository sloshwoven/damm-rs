//! Generates and validates check digits with the [Damm] algorithm.
//!
//! [Damm]: https://en.wikipedia.org/wiki/Damm_algorithm

extern crate try_from;

use std::error;
use std::fmt;

pub mod optable;

use optable::{OpTable, STANDARD_OP_TABLE};

/// An error related to Damm generation or validation.
#[derive(Debug, Eq, PartialEq)]
pub enum DammError {
    /// A bad (non-digit) input number; contains the bad entry.
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
/// use damm::optable::*;
///
/// assert_eq!(Ok(4), generate_with(&STANDARD_OP_TABLE, &[5, 7, 2]));
/// assert_eq!(Ok(0), generate_with(&STANDARD_OP_TABLE, &[]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
/// use damm::optable::*;
///
/// assert_eq!(Err(DammError::BadInputNum(10)), generate_with(&STANDARD_OP_TABLE, &[3, 10, 6]));
/// ```
pub fn generate_with<'a, T: IntoIterator<Item = &'a u8>>(op_table: &OpTable,
                                                         nums: T)
                                                         -> Result<u8, DammError> {
    nums.into_iter().fold(Ok(0), |res, &n| {
        res.and_then(|interim_digit| {
            op_table
                .rows()
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
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
///
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
/// use damm::optable::*;
///
/// assert_eq!(Ok(true), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 4]));
/// assert_eq!(Ok(false), validate_with(&STANDARD_OP_TABLE, &[5, 7, 2, 1]));
/// ```
///
/// # Errors
///
/// ```
/// use damm::*;
/// use damm::optable::*;
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

    // originally I had the error_fmt and error_description tests as doctests,
    // but I moved them here because I don't want to suppress the default
    // documentation

    #[test]
    fn error_fmt() {
        assert_eq!("non-digit 10 in input number sequence",
                   format!("{}", DammError::BadInputNum(10)));
    }

    #[test]
    fn error_description() {
        assert_eq!("bad input number", DammError::BadInputNum(10).description());
    }
}
