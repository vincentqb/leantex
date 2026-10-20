module

public import Tests.Support

public section

open LeanTex.Core

/-! A markdown page is set for the characters it holds. -/

namespace Tests.MarkdownPage

/-- Ordinary English words, enough to set many full lines. -/
def prose : String :=
  String.intercalate " " (List.replicate 12
    "The river bends past the old mill where quiet water gathers fallen \
leaves, and the morning light settles slowly on the stones along the bank.")

/-- The characters, spaces included, of every shipped body line set to the full measure. -/
def fullLineChars (out : Layout.Out) (measure : Dim.Length) : Array Nat :=
  (bodyLines out).filterMap fun l =>
    if l.setWidth + Dim.pt 1 ≥ measure then some (lineText l).length else none

def avg (xs : Array Nat) : Nat := if xs.isEmpty then 0 else xs.foldl (· + ·) 0 / xs.size

/-- The markdown measure on both artifacts, and in every shipped text face a line length inside the
readable band. -/
def markdownPageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mdDoc := (elabMd (prose ++ "\n")).1
  let texDoc := (elabStr (dvDoc "" prose)).1
  let width (d : Ir.Doc) : Dim.Length := d.page.width - 2 * d.page.hmargin
  t "markdown takes the markdown text block, an article its own"
    (width mdDoc == Ir.markdownTextBlock && width texDoc == Ir.articleTextBlock)
  t "a declared page geometry still keeps every value it names"
    (width (elabStr (dvDoc "\\page{ hmargin = 100pt }\n" prose)).1 == Dim.bp 612 - 2 * Dim.pt 100)
  let measureOf (d : Ir.Doc) : String :=
    let (head, _, _) := HtmlDoc.emitTree {} d
    String.join (head.toList.filterMap fun
      | .style rules => some rules
      | _ => none)
  t "the markdown page's HTML measure is its web layout's, the tex page's its text block, in rem"
    (hasStr (measureOf mdDoc) "--measure: calc(60ch + 7.25rem);" && hasStr (measureOf texDoc) "--measure: 31.2rem;")
  let mut faces := 0
  for file in ["OpenSans-Regular.ttf", "FiraSans-Regular.otf", "SourceSerifPro-Regular.otf"] do
    let some font ← loadTestFont file | t s!"markdown page: {file} loads" false; continue
    faces := faces + 1
    let fonts := oneFaceOf font
    let mdOut := layoutOf fonts mdDoc
    let texOut := layoutOf fonts texDoc
    let mdLines := fullLineChars mdOut Ir.markdownTextBlock
    let texLines := fullLineChars texOut Ir.articleTextBlock
    t s!"markdown page in {font.family}: full lines set to the markdown measure ({mdLines.size})"
      (mdLines.size ≥ 8
        -- protrusion hangs a boundary glyph's edge past the measure, no more
        && (bodyLines mdOut).all (·.setWidth ≤ Ir.markdownTextBlock + Dim.pt 3))
    t s!"markdown page in {font.family}: {avg mdLines} characters per line, inside 70–90 \
and wider than the article's {avg texLines}"
      (70 ≤ avg mdLines && avg mdLines ≤ 90 && avg texLines < avg mdLines)
    t s!"markdown page in {font.family}: the readable-band judge stays quiet"
      (!mdOut.diags.any (·.kind == .W0201))
    let digit := font.advance '0' * 1000 / font.unitsPerEm
    t s!"markdown page in {font.family}: the web measure is sixty of its digits and the insets"
      (HtmlDoc.chMilli (some fonts) == digit &&
        HtmlDoc.measureMilli mdDoc (HtmlDoc.chMilli (some fonts)) == 60 * digit + 7250)
  t "markdown page: every shipped text face was measured" (faces == 3)

end Tests.MarkdownPage
