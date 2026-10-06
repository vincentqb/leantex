import LeanTex.Core.Layout.SpacingContract
import Tests.Support

namespace LeanTex.Tests.ElementSpacing

open Core Core.Dim Core.Ir Core.Layout Core.Font

private def geometry : Geom := {
  pageW := pt 220, pageH := pt 200
  hmargin := pt 12, vmargin := pt 12, fontSize := pt 10
  parskip := { width := Length.ofSp (pt 6) }
  hyphenate := false, justify := false }

private def gap (n : Int) : SymGlue := { width := Length.ofSp (pt n) }

/-- Ordinary role spacing reaches `Acc.addvspace`; a nonempty `.spaced`
block instead uses the distinct explicit-skip path. -/
private def spacingPage (fs : FontSet) (before after : Option SymGlue)
    (between : Array Block := #[]) (geom : Geom := geometry)
    (content : Array Inline := #[.text "Second"]) : Out :=
  let first := Block.role "previous" #[.para #[.text "First"]]
  let second := Block.role "next" #[.para content]
  run geom fs none {
    styles := { entries := #[("previous", { after }), ("next", { before })] }
    body := #[first] ++ between ++ #[second] }

private def pair (out : Out) : Option (LineOut × LineOut) :=
  match ((bodyLines out).filter fun l => !l.note && hasGlyphRun l).toList with
  | [first, second] =>
    if lineText first == "First" && lineText second == "Second"
    then some (first, second) else none
  | _ => none

private def displacement (before after : Out) (delta : Sp) : Bool :=
  before.pages.size == 1 && after.pages.size == 1 &&
  noDroppedGlyph before && noDroppedGlyph after &&
  match pair before, pair after with
  | some (a, b), some (a', b') => a.y == a'.y && b'.y - b.y == delta
  | _, _ => false

private def paragraphDisplacement (before after : Out) (delta : Sp) : Bool :=
  let a := (bodyLines before).filter Spacing.inkLine
  let b := (bodyLines after).filter Spacing.inkLine
  before.pages.size == 1 && after.pages.size == 1 &&
  noDroppedGlyph before && noDroppedGlyph after &&
  a.size > 2 && a.size == b.size &&
  (a.map (lineText ·)) == (b.map (lineText ·)) &&
  a.zipIdx.all (fun (line, i) =>
    (b[i]?).any fun other => other.y - line.y == if i == 0 then 0 else delta) &&
  (Spacing.inkBaselines after).getLast?.getD 0 -
    (Spacing.inkBaselines before).getLast?.getD 0 == delta

/-- Synthetic shipped-page witnesses for the corrected spacing contract.
Natural fixed glue leaves page-close redistribution out of these checks.
The two false-premise probes distinguish default replacement and pagination
from a missing glyph or a changed line break. -/
def elementSpacingChecks (fs : FontSet) : Array (String × Bool) := Id.run do
  let ordinary := spacingPage fs none none
  let mut out := #[
    ("resolved element gap covers the peer default exactly",
      displacement ordinary (spacingPage fs (some (gap 6)) none) 0),
    ("resolved element gap covers a smaller peer default",
      displacement ordinary (spacingPage fs (some (gap 12)) none) (pt 6)),
    ("positive element gap can replace a larger peer default",
      displacement ordinary (spacingPage fs (some (gap 1)) none) (pt (-5)))]
  for old in #[-4, 3, 12] do
    for next in #[0, 4, 8, 12] do
      let before := spacingPage fs none (some (gap old))
      let after := spacingPage fs (some (gap next)) (some (gap old))
      out := out.push (s!"element gap selects the larger nonzero tail {old}/{next}",
        displacement before after (pt (max old next - old)))
  for old in #[-4, 0, 7] do
    let between := #[Block.spaced (Sourced.bare (gap old)) #[]]
    for next in #[6, 12] do
      let before := spacingPage fs none none between
      let after := spacingPage fs (some (gap next)) none between
      out := out.push (s!"element gap appends after a zero tail {old}/{next}",
        displacement before after (pt (next - 6)))
  let relative : SymGlue := { width := { em := 1200 } }
  out := out.push ("element em lengths use the resolved font size",
    displacement ordinary (spacingPage fs (some relative) none) (pt 6) &&
    displacement (spacingPage fs (some (gap 12)) none) (spacingPage fs (some relative) none) 0)
  let xHeight := fs.body.xHeight * geometry.fontSize / fs.body.unitsPerEm
  let relativeEx : SymGlue := { width := { ex := 2000 } }
  let resolved := relativeEx.resolve geometry.fontSize xHeight
  let absolute : SymGlue := { width := Length.ofSp resolved.width }
  out := out.push ("element ex lengths agree with their resolved absolute length",
    displacement ordinary (spacingPage fs (some relativeEx) none) (resolved.width - pt 6) &&
    displacement (spacingPage fs (some absolute) none) (spacingPage fs (some relativeEx) none) 0)
  let signed : SymGlue := { width := { sp := pt 6, em := -1000 } }
  out := out.push ("a positive absolute component can resolve to negative space",
    signed.width.sp > 0 && (signed.resolve geometry.fontSize xHeight).width < 0 &&
    displacement ordinary (spacingPage fs (some signed) none) (pt (-10)))
  let short := { geometry with pageH := pt 80 }
  let before := spacingPage fs none none #[] short
  let after := spacingPage fs (some (gap 80)) none #[] short
  out := out.push ("an element gap can lower the local baseline on a fresh page",
    noDroppedGlyph before && noDroppedGlyph after &&
    before.pages.size == 1 && after.pages.size == 2 &&
    match pair before, pair after with
    | some (a, b), some (a', b') => a.y == a'.y && b'.y < b.y
    | _, _ => false)
  let narrow := { geometry with pageW := pt 110 }
  let words := "A measured paragraph has several ordinary lines of text. " ++
    "Each line keeps its breaks while the declared gap moves the whole paragraph."
  let plain := #[Inline.text words]
  let decorated := #[Inline.decorated .underline
    #[.decorated .lineThrough plain]]
  for (label, content) in #[("plain", plain), ("decorated", decorated)] do
    out := out.push (s!"resolved element gap moves every {label} paragraph line",
      paragraphDisplacement (spacingPage fs none none #[] narrow content)
        (spacingPage fs (some (gap 12)) none #[] narrow content) (pt 6))
  return out

end LeanTex.Tests.ElementSpacing
