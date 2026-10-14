-- leantex: formats = pdf, html
/-
An invented module for the code-file reader's golden fixture.
-/

/-! # Tide tables

Every name here is invented. A *tide* is a list of water heights, and the
module keeps the heights that rise above a mark.

## What the page shows

Documentation comments read as markdown; the code between them sets as
listings, its line comments and block comments included. -/

namespace Tides

/-- The heights, in centimetres, above `mark`. -/
def above (mark : Nat) (heights : List Nat) : List Nat :=
  heights.filter (· > mark) -- a line comment stays in the code

/-- A string can hold comment markers and still be code. -/
def markers : String := "a /-- not a doc -/ b"

/- A plain block comment, /- nested -/, stays in the code. -/
def spring : Nat := 3

/-- Keeping the heights above a mark keeps no more than it was given. -/
theorem above_length (mark : Nat) (hs : List Nat) :
    (above mark hs).length ≤ hs.length :=
  List.length_filter_le _ _

structure Gauge where
  /-- A field's docstring is indented and stays in the code. -/
  depth : Nat
  deriving Repr

end Tides
