module

import LeanTex.Core.Ink

/-! Ordinary outline consumers can read font tables, measure glyphs and
inspect the prepared source kind. Transform state and CFF parser state
remain internal. -/

open LeanTex.Core.Ink

namespace Tests.InkInterface

example : ByteArray → Nat → Nat := u8
example : ByteArray → Nat → Nat := u16
example : ByteArray → Nat → Nat := u32
example : ByteArray → Nat → Int := i16
example : ByteArray → Nat → Int := i32
example (offset length : Nat) : Table := ⟨offset, length⟩
example : ByteArray → String → Option Table := findTable
example : ByteArray → Table → Bool := fits
example : ByteArray → Nat → Option (Array (Nat × Nat) × Nat) := parseIndex

example : Inhabited Cmd := inferInstance
example : BEq Cmd := inferInstance
example (x y : Int) : Array Cmd :=
  #[.move x y, .line x y, .quad x y x y, .cube x y x y x y]
example (cmds : Array Cmd) (minY : Int) : Outline := ⟨cmds, minY⟩
example : Outline → Int → Int → Array (Int × Int) := bandIntervals
example : Outline → Bounds := Outline.bounds
example : Outline → Int × Int := Outline.yExtent

example : Repr Bounds := inferInstance
example : BEq Bounds := inferInstance
example : Inhabited Bounds := inferInstance
example (left bottom right top : Int) : Bounds := ⟨left, bottom, right, top⟩
example : Bounds → Bounds → Bounds := Bounds.union

example : Inhabited Src := inferInstance
example : ByteArray → Bool → Nat → Src := Src.make
example : Src → Nat → Option Bounds := Src.boundsAt
example : Src → Nat → Option (Int × Int) := Src.yExtentAt
example : Src → Nat → Option (Array Cmd) := Src.cmdsAt
example : Src → Nat → Int → Int → Option (Array (Int × Int)) := Src.inkAt

-- The subset writer inspects this tag without reading the CFF parser state.
example (src : Src) : Bool :=
  match src with
  | .cffSrc .. => true
  | .glyfSrc .. | .opaque => false

example : True := by
  fail_if_success have := LeanTex.Core.Ink.i8
  fail_if_success have := LeanTex.Core.Ink.edgesOf
  fail_if_success have := LeanTex.Core.Ink.fillAt
  fail_if_success have := LeanTex.Core.Ink.Xf
  fail_if_success have := LeanTex.Core.Ink.simpleOutline
  fail_if_success have := LeanTex.Core.Ink.glyfOutline
  fail_if_success have := LeanTex.Core.Ink.CffDict
  fail_if_success have := LeanTex.Core.Ink.Cff.mk
  fail_if_success have := LeanTex.Core.Ink.Cff.charStrings
  fail_if_success have := LeanTex.Core.Ink.Cff.gsubrs
  fail_if_success have := LeanTex.Core.Ink.parseDict
  fail_if_success have := LeanTex.Core.Ink.parseCff
  fail_if_success have := LeanTex.Core.Ink.runCharstring
  trivial

end Tests.InkInterface
