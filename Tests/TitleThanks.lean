module

public import Tests.Support

public section

open LeanTex.Core

/-! A title's `\thanks` as `\maketitle` sets it: a note at its page's foot marked in `\fnsymbol`, apart
from the body's count, a style's anonymous block dropping the author's with the author. -/

namespace Tests.TitleThanks

private def doc (cls pre body : String) : String :=
  s!"\\documentclass\{{cls}}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

private def titled : String :=
  "\\title{An Invented Title\\thanks{Funded by an invented grant.}}\n" ++
  "\\author{Ada Example\\thanks{Written at an example place.} \\and " ++
  "Bo Sample\\thanks{Written at a sample place.}}\n\\date{}"

private def body : String := "\\maketitle\nWidgets turn.\\footnote{A body note.}"

/-- The text of each line of text set at a page's foot, in page order. -/
private def noteTexts (out : Layout.Out) : Array String :=
  (allLines out).filter (·.note) |>.map (lineText ·) |>.filter (!·.isEmpty)

/-- The text of each body line, in page order. -/
private def textLines (out : Layout.Out) : Array String :=
  (bodyLines out).filter (!·.note) |>.map (lineText ·)

/-- Each endnote's list item attributes on the web page, in order. -/
private def endnoteWalk : Html.Walk Unit (Array (Array (String × String))) where
  enter _ acc tag attrs _ := if tag == "li" && attrs.any (·.1 == "id") then acc.push attrs else acc

/-- The face set with the shipped math face answering for the series' marks a text face lacks. -/
private def withMathAsterisk (fonts : Font.FontSet) : IO Font.FontSet := do
  let .ok fira := Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf"))
    | return fonts
  return { fonts with fonts := fonts.fonts.push fira
                      fallback := fonts.fallback ++ #[('\u2217', fonts.fonts.size),
                        ('\u2016', fonts.fonts.size)] }

def thanksChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← withMathAsterisk fonts
  let (art, artDs) := elabStr (doc "article" titled body)
  let out := layoutOf fonts art
  let notes := noteTexts out
  t s!"an article's title notes stand at its page's foot in the fnsymbol series, before the body's \
first ({notes})"
    (notes == #["\u2217Funded by an invented grant.", "\u2020Written at an example place.",
      "\u2021Written at a sample place.", "1A body note."])
  let lines := textLines out
  t s!"each mark follows the words it marks ({lines})"
    (lines.any (· == "An Invented Title\u2217") &&
      lines.any fun l => hasStr l "Ada Example\u2020" && hasStr l "Bo Sample\u2021")
  t "no note text stands in the title's lines"
    (lines.all fun l => !hasStr l "invented grant" && !hasStr l "example place")
  t "a title's thanks is no loss" (artDs.all (·.subject != some "ctrl:thanks"))
  t s!"the title's metadata holds its words alone ({art.info.title}, {art.info.author})"
    (art.info.title == some "An Invented Title" && art.info.author == some "Ada Example, Bo Sample")
  let items := endnoteWalk.list () #[] (docNodesOf art).toList
  t s!"the web page's endnotes show the same marks ({items})"
    (items.size == 4 &&
      (items[0]?.any fun a => a.contains ("style", "list-style-type: \"\u2217 \"")) &&
      (items[3]?.any fun a => a.contains ("value", "1")))
  for cls in ["report", "book", "article[titlepage]"] do
    let src := (doc cls titled body).replace "{article[titlepage]}" "[titlepage]{article}"
    let (d, _) := elabStr src
    let ns := noteTexts (layoutOf fonts d)
    t s!"{cls}: a title set above the text marks its notes apart from the body's ({ns})"
      (ns == notes)
  let several := "\\newcommand{\\grant}{\\thanks{Granted by a macro.}}\n" ++
    "\\title{A \\textbf{Bold\\thanks{Inside bold.}} Title\\grant\\footnote{A title footnote.}}\n" ++
    "\\author{Ada Example\\thanks{First of two.}\\thanks{Second of two.}}\n" ++
    "\\date{Today\\thanks{On the date.}}"
  let (sev, _) := elabStr (doc "article" several
    "Before.\\footnote{An early note.}\n\\maketitle\nAfter.\\footnote{A later note.}")
  let sns := noteTexts (layoutOf fonts sev)
  t s!"a title's notes, through a macro, a box and a footnote, its author's two and its date's, take \
the series in order past the body's count, which then restarts ({sns})"
    (sns == #["1An early note.", "\u2020Inside bold.", "\u2021Granted by a macro.",
      "\u00a7A title footnote.", "\u00b6First of two.", "\u2016Second of two.",
      "\u2217\u2217On the date.", "1A later note."])
  let (deck, deckDs) := elabStr (dvDeck titled "\\begin{frame}\\titlepage\\end{frame}")
  t "a deck's title keeps its thanks inline, a named loss"
    (deckDs.any (·.subject == some "ctrl:thanks") && (Ir.footnotesOf deck.body).isEmpty)
  let (noted, _) := elabStr (dvDeck "\\title{Deck Title\\footnote{A title footnote.}}"
    "\\begin{frame}\\titlepage\\end{frame}\n\\begin{frame}Body.\\footnote{A body note.}\\end{frame}")
  t "a deck's title footnote keeps its number, the body's counting on past it"
    ((Ir.footnotesOf noted.body).map (·.1) == #[some (.arabic 1), some (.arabic 2)])
  let (late, lateDs) := elabStr (doc "article" "\\title{T}" "\\maketitle\nA \\thanks{kept} b.")
  t "after the title a thanks is its text, as LaTeX relaxes it"
    ((Ir.footnotesOf late.body).isEmpty && hasStr (Ir.blocksText late.body) "kept" &&
      lateDs.all (·.subject != some "ctrl:thanks"))

/-- A style's anonymous block drops the author's thanks with the author; the title's stands. -/
def anonymousThanksChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let fonts ← withMathAsterisk fonts
  let (anon, _, _) ← runStyParity "venue-thanks"
  let out := layoutOf fonts anon
  let page := String.intercalate "\n" ((allLines out).toList.map (lineText ·))
  let html := (HtmlDoc.emit {} anon).1
  let md := MarkdownDoc.emit anon
  t s!"a submission's title keeps its own thanks ({noteTexts out})"
    (noteTexts out == #["\u2217Funded by an invented grant.", "1A body note."])
  t "a submission shows its author's thanks in no artifact"
    (!hasStr page "Example University" && !hasStr html "Example University" &&
      !hasStr md "Example University")
  let (final, _, _) ← runStyParity "venue-thanks-final"
  let fout := layoutOf fonts final
  t s!"a final copy sets its authors' thanks after the title's ({noteTexts fout})"
    (noteTexts fout == #["\u2217Funded by an invented grant.",
      "\u2020Written at Example University, in a room with a long view.",
      "\u2021Written at a sample institute on the far side of the river.", "1A body note."])
  let ys := (bodyLines fout).filterMap fun l =>
    if hasStr (lineText l) "Ada Example" || hasStr (lineText l) "Bo Sample" then some l.y else none
  t s!"its authors stand side by side, each name's box as wide as its name and mark ({ys.map reprStr})"
    (ys.size == 2 && ys[0]? == ys[1]?)

end Tests.TitleThanks
