//! Invented tide tables, read by a lexer.
#![allow(dead_code)]

use std::collections::HashMap;
use std::fmt::{self, Display};

/// A tide reading in metres.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Reading {
    pub height: f64,
    hour: u8,
}

/** A named harbour. */
pub enum Harbour<'a> {
    Named(&'a str),
    Unnamed,
}

impl Display for Reading {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:.2}m at {}h", self.height, self.hour)
    }
}

pub trait Tidal {
    /// The highest reading, if any.
    fn peak(&self) -> Option<Reading>;
}

impl Tidal for Vec<Reading> {
    fn peak(&self) -> Option<Reading> {
        self.iter().copied().fold(None, |best, r| match best {
            Some(b) if b.height >= r.height => Some(b),
            _ => Some(r),
        })
    }
}

fn main() {
    let mut table: HashMap<&str, Vec<Reading>> = HashMap::new();
    let raw = r#"a "raw" string"#;
    let bytes = b"\x7f\n";
    let ch = '\u{1F30A}';
    let n = 1_000u32 + 0xFFi64 as u32 + 0o17 + 0b1010;
    let x = 2.5e-3_f64;
    'outer: for hour in 0..=23u8 {
        if hour % 6 == 0 { continue 'outer; }
        table.entry("north").or_default().push(Reading { height: x * f64::from(hour), hour });
    }
    println!("{} {:?} {} {}", raw, bytes, ch, n);
    assert!(table.len() <= 1, "one harbour");
}
