// leantex: formats = html
//! # Tide tables
//!
//! Invented tides, read as a page: inner docs describe the file.

use std::fmt;

/// A reading in metres.
///
/// Its height is invented too.
pub struct Reading {
    pub height: f64,
}

//// Four slashes are a plain comment.
impl fmt::Display for Reading {
    /// Writes the height.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = "/// not a doc";
        write!(f, "{}m {}", self.height, s)
    }
}

/** A block doc /* with a nested comment */ still the doc. */
pub fn calm() -> bool { true }
