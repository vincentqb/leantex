module

import LeanTex.Core.Font

/-! Fonts are shared values for the driver, layout and both backends.
An ordinary import provides those values and their contracts, while sfnt
parsers, search machinery and GPOS subtable representation stay private. -/

open LeanTex.Core
open LeanTex.Core.Font

namespace Tests.FontInterface

example : Repr MathConsts := inferInstance
example : BEq MathConsts := inferInstance
example : Inhabited MathConsts := inferInstance
example : Repr Class := inferInstance
example : Inhabited Class := inferInstance
example : Inhabited Font := inferInstance
example : Inhabited FontSet := inferInstance
example : Inhabited SpaceKernCache := inferInstance

example (f : Font) (bounds : Ink.Bounds) (source : Ink.Src) : Font :=
  { f with
    inkExtent := Thunk.mk fun _ => #[Thunk.mk fun _ => some bounds]
    inkSrc := Thunk.mk fun _ => source
    kernData := Thunk.mk fun _ => (#[], #[]) }

example (f : Font) (coverage : Math.MathAlphabetCoverage) : FontSet :=
  { fonts := #[f], math := some 0, mathAlphabets := coverage }

example : ByteArray → Except String Class := classify
example : ByteArray → Except String Font := parse
example : Nat := classifierVersion
example : ByteArray → Array (UInt32 × UInt32 × UInt32) := cmapRanges
example : Array (UInt32 × UInt32 × UInt32) → Char → Option Nat := gidIn
example : Font → Char → Option Nat := Font.gid
example : Font → Math.MathAlphabetSources → Math.MathAlphabetCoverage :=
  Font.mathAlphabetCoverage
example : Font → Nat → Nat := Font.smallCapGid
example : Font → Nat → Nat → Int := Font.kernAdv
example : Font → Bool → Nat → Int := Font.spaceKernAdv
example : Font → Char → Nat := Font.advance
example : Font → Nat := Font.spaceAdvance
example : Font → Int := Font.inkAscent
example : Font → Nat → Array (Int × Int) := Font.inkAt
example : Font → Nat → Option Ink.Bounds := Font.bounds
example : Font → Nat → Option (Int × Int) := Font.yExtent
example : Font → Nat := Font.xHeightOptical
example : Font → Nat → Array (Nat × Int) := Font.vertVariants
example : Font → Nat → Array (Nat × Int) := Font.horizVariants
example : Font → Nat → Int := Font.markAttachX
example : Font → Int × Int := Font.band

example : Nat → Nat := spaceKernDepth
example : SpaceKernCache → Nat → Option ((Int × Int) × Nat) := SpaceKernCache.lookup?
example (cache : SpaceKernCache) : Nat × Nat := (cache.size, cache.depth)
example (f : Font) : Bool :=
  f.kernData.get.1.isEmpty && f.kernData.get.2.isEmpty

example : FontSet → Font := FontSet.body
example : FontSet → Nat → Font := FontSet.get
example : FontSet → Option (Nat × Font × MathConsts) := FontSet.mathFont?
example : FontSet → Nat → Nat → Bool → Nat := FontSet.lookup
example : FontSet → Char → Option Nat := FontSet.fallbackFor

example (upem descent pos thick : Int) (h : upem / 10 ≤ -descent) :
    descent ≤ (underlineBand upem descent pos thick).1 :=
  underline_in_descent upem descent pos thick h

example (f : Font) (g : Nat) :
    0 ≤ f.topAccentX g ∧ f.topAccentX g ≤ (f.widths[g]?.getD 0 : Int) :=
  f.topAccentX_covers g

example (fs : FontSet) (nonempty : 0 < fs.fonts.size)
    (valid : ∀ e ∈ fs.index, e.2 < fs.fonts.size) (slot weight : Nat) (italic : Bool) :
    fs.lookup slot weight italic < fs.fonts.size :=
  fs.index_total nonempty valid slot weight italic

example (fs : FontSet) : fs.slotCollapsed 0 = false :=
  fs.slotCollapsed_body

example (fs : FontSet) (slot : Nat) (h : slot != 0) :
    fs.slotCollapsed slot = (fs.lookup slot 400 false == fs.lookup 0 400 false) :=
  fs.slotCollapsed_exact slot h

example (fs : FontSet) (slot : Nat) (h : fs.lookup slot 400 false < fs.fonts.size) :
    fs.slotIsFixedPitch slot = (fs.fonts[fs.lookup slot 400 false]).isFixedPitch :=
  fs.slotIsFixedPitch_exact slot h

example : True := by
  fail_if_success have := LeanTex.Core.Font.bsearch (α := Nat) #[] id 0
  fail_if_success have := LeanTex.Core.Font.substGid
  fail_if_success have := LeanTex.Core.Font.parseMath
  fail_if_success have := LeanTex.Core.Font.parseCmap
  fail_if_success have := LeanTex.Core.Font.parseGsubSmallCaps
  fail_if_success have := LeanTex.Core.Font.parseKernSubs
  fail_if_success have := LeanTex.Core.Font.pairAdv
  fail_if_success have := LeanTex.Core.Font.makeSpaceKernTree
  fail_if_success have := LeanTex.Core.Font.spaceKernLookup
  fail_if_success have := LeanTex.Core.Font.SpaceKernTree
  fail_if_success have := LeanTex.Core.Font.SpaceKernCache.mk
  fail_if_success have := LeanTex.Core.Font.SpaceKernCache.space
  fail_if_success have := LeanTex.Core.Font.SpaceKernCache.root
  fail_if_success have := LeanTex.Core.Font.KernSub.mk
  fail_if_success have := LeanTex.Core.Font.KernSub.fmt
  fail_if_success have := LeanTex.Core.Font.KernSub.cov
  trivial

end Tests.FontInterface
