import Tests.Support

open LeanTex.Core

/-! **A markdown page is set for the characters it holds.**

A markdown source declares no page, so the engine's default is the whole of
its geometry, and the article's 26-pica measure left a long generated report
with two-inch margins around 61 characters of its face. The invariant is
over what ships: the shipped lines' measure and characters per line on
`Layout.Out` in every shipped text face, and the typed HTML's measure. Every
word here is invented. -/

namespace Tests.MarkdownPage

/-- Invented prose: ordinary English words of ordinary lengths, enough of
them to set many full lines. -/
def prose : String :=
  String.intercalate " " (List.replicate 12
    "The river bends past the old mill where quiet water gathers fallen \
leaves, and the morning light settles slowly on the stones along the bank.")

/-- The characters (spaces included) of every shipped body line set to the
full measure: the lines a measure claim is about. -/
def fullLineChars (out : Layout.Out) (measure : Dim.Sp) : Array Nat :=
  (bodyLines out).filterMap fun l =>
    if l.setWidth + Dim.pt 1 ≥ measure then some (lineText l).length else none

def avg (xs : Array Nat) : Nat := if xs.isEmpty then 0 else xs.foldl (· + ·) 0 / xs.size

/-- The page: the markdown measure on both artifacts, and in every shipped
text face a line length inside the readable band. -/
def markdownPageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mdDoc := (elabMd (prose ++ "\n")).1
  let texDoc := (elabStr (dvDoc "" prose)).1
  let width (d : Ir.Doc) : Dim.Sp := d.page.width - 2 * d.page.hmargin
  t "a markdown page takes the markdown text block, the article page its own"
    (width mdDoc == Ir.markdownTextBlock && width texDoc == Ir.articleTextBlock)
  t "a declared page geometry still keeps every value it names"
    (width (elabStr (dvDoc "\\page{ hmargin = 100pt }\n" prose)).1 == Dim.pt 412)
  let measureOf (d : Ir.Doc) : String :=
    let (head, _, _) := HtmlDoc.emitTree {} d
    String.join (head.toList.filterMap fun
      | .style rules => some rules
      | _ => none)
  t "the markdown page's HTML measure is the same text block, in em"
    (hasStr (measureOf mdDoc) "--measure: 38.4em;" && hasStr (measureOf texDoc) "--measure: 31.2em;")
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
  t "markdown page: every shipped text face was measured" (faces == 3)

end Tests.MarkdownPage
