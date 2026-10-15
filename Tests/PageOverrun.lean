module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.PageOverrun

private def deck (body : String) : String :=
  "\\documentclass{beamer}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

private def article (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

/-- The codes of a source's run through the overflow ladder, as the driver sets it. -/
private def codes (fonts : Font.FontSet) (src : String) : Array DiagCode :=
  ((fittedOf fonts (elabStr src).1).out.diags.map (·.kind)).filter fun c =>
    c == .W0358 || c == .W0384 || c == .W0400

/-- The index of the first page with a line reading `text`. -/
private def pageOf (out : Layout.Out) (text : String) : Option Nat :=
  out.pages.findIdx? fun p => p.lines.any fun l => (lineText l).trimAscii.toString == text

/-- The codes a source's run names, any code. -/
private def allCodes (fonts : Font.FontSet) (src : String) : Array DiagCode :=
  (fittedOf fonts (elabStr src).1).out.diags.map (·.kind)

/-- `n` rows of a tabular whose cells name their row, each cell's word distinct. -/
private def rows (n : Nat) (cols : List String) : String :=
  String.join ((List.range n).map fun i =>
    " & ".intercalate (cols.map fun c => s!"{c} {i}") ++ " \\\\\n")

/-- Per page, the lines reading `title` and the marked-content sequences the tagged PDF's title
elements own there. -/
private def titleCounts (fonts : Font.FontSet) (src title : String) : Array (Nat × Nat) :=
  let doc := (elabStr src).1
  let out := (fittedOf fonts doc).out
  let tree := Struct.ofDoc (Layout.pdfView doc)
  let ops := Pdf.pageOps (Layout.Geom.ofPage doc.page) fonts out.pages {} tree
  let es := Pdf.fill (Pdf.skeleton tree) (Pdf.leafPagesOf tree.leaves.size (ops.map Pdf.pageMarks))
  out.pages.zipIdx.map fun (p, i) =>
    ((p.lines.filter fun l => (lineText l).trimAscii.toString == title).size,
     es.foldl (fun n e => if e.s == "Title" then
       n + (e.kids.filter fun k => match k with
         | .mcid q _ => q == i
         | .elem _ | .leaf _ => false).size
       else n) 0)

/-- A footnote of `n` sentences. -/
private def longNote (n : Nat) : String :=
  "\\footnote{" ++ String.join (List.replicate n "Mike note words. ") ++ "}"

/-- A box no break can help stands past its page's floor named, a frame's or a flow page's alike;
the ladder names what it moves, and what fits is named by nothing. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- A row of one-line cells that does not fit breaks with every one of its cells.
  let longTab := article ("\\begin{tabular}{lll}\n" ++ rows 120 ["Kilo", "Lima", "Mike"] ++
    "\\end{tabular}")
  let longOut := (fittedOf oneFace (elabStr longTab).1).out
  let split := (List.range 120).filter fun i =>
    let ps := ["Kilo", "Lima", "Mike"].map fun c => pageOf longOut s!"{c} {i}"
    ps.any (· != ps.head!) || ps.any (·.isNone)
  t "page overrun: a long tabular breaks between rows, every row's cells on one page, named by nothing"
    (split.isEmpty && 1 < longOut.pages.size && !(allCodes oneFace longTab).contains .W0358)
  let frameTab := deck ("\\begin{frame}[allowframebreaks]{Kilo}\n\\begin{tabular}{ll}\n" ++
    rows 40 ["Lima", "Mike"] ++ "\\end{tabular}\n\\end{frame}")
  let frameOut := (fittedOf oneFace (elabStr frameTab).1).out
  t "page overrun: a tabular in a frame with declared breaks breaks between rows, named by nothing"
    ((List.range 40).all (fun i => pageOf frameOut s!"Lima {i}" == pageOf frameOut s!"Mike {i}") &&
      !(allCodes oneFace frameTab).contains .W0358)
  let fillers := String.join ((List.range 53).map fun i => s!"Kilo filler {i}.\\\\\n")
  let lines (w : String) := String.join ((List.range 12).map fun i => s!"{w} line {i}.\n\n")
  let minis := article ("\\noindent " ++ fillers ++ "\n\\begin{minipage}[t]{0.45\\textwidth}\n" ++
    lines "Lima" ++ "\\end{minipage}\\hfill\\begin{minipage}[t]{0.45\\textwidth}\n" ++
    lines "Mike" ++ "\\end{minipage}")
  let miniOut := (fittedOf oneFace (elabStr minis).1).out
  t "page overrun: two minipages at a page's foot move together, named by nothing"
    (pageOf miniOut "Lima line 0." == pageOf miniOut "Mike line 0." &&
      !(allCodes oneFace minis).contains .W0358)
  t "page overrun: a float taller than the text block is named once"
    ((allCodes oneFace (article ("Kilo words.\n\\begin{figure}[h]\n\\rule{1cm}{30cm}\n" ++
      "\\caption{Lima caption.}\n\\end{figure}\nMike words."))).filter (· == .W0358) == #[.W0358])
  t "page overrun: an untitled frame whose rule overruns names the rule, not its note"
    ((allCodes oneFace (deck "\\begin{frame}\n\\rule{1cm}{12cm}\\footnote{Kilo note.}\n\\end{frame}")).filter
      (fun c => c == .W0358 || c == .W0372) == #[.W0358])
  t "page overrun: an untitled frame's overrunning rule on its second step names it once"
    (codes oneFace (deck ("\\begin{frame}\n\\only<1>{Mike words.}\n\\only<2>{\\rule{1cm}{12cm}}\n" ++
      "\\end{frame}")) == #[.W0358])
  t "page overrun: an untitled frame's rule taller than its page is named once (W0358)"
    (codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{12cm}\n\\end{frame}") == #[.W0358])
  t "page overrun: a titled frame's rule taller than its page stands below the title, named once"
    (codes oneFace (deck "\\begin{frame}{Kilo}\n\\rule{1cm}{12cm}\n\\end{frame}") == #[.W0358])
  t "page overrun: a flow page's rule taller than the text block is named once (W0358)"
    (codes oneFace (article "Lima words.\n\n\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a rule opening the document taller than the text block is named once"
    (codes oneFace (article "\\rule{1cm}{30cm}\n\nMike words.") == #[.W0358])
  t "page overrun: a frame whose rule fits names nothing"
    ((codes oneFace (deck "\\begin{frame}\n\\rule{1cm}{3cm}\n\\end{frame}")).isEmpty)
  t "page overrun: a flow rule that fits names nothing"
    ((codes oneFace (article "Lima words.\n\n\\rule{1cm}{15cm}\n\nMike words.")).isEmpty)
  let tab (n : Nat) (cols : List String) := "\\begin{tabular}{" ++
    String.join (cols.map fun _ => "l") ++ "}\n" ++ rows n cols ++ "\\end{tabular}"
  let titled (pre body : String) := "\\documentclass{beamer}\n" ++ pre ++
    "\\begin{document}\n\\begin{frame}[allowframebreaks]{Kilo}\n" ++ body ++
    "\n\\end{frame}\n\\end{document}\n"
  let column (body : String) := "\\begin{column}{0.45\\textwidth}\n" ++ body ++ "\n\\end{column}\n"
  for (what, src) in [("a tabular", titled "" (tab 40 ["Lima", "Mike"])),
      ("a moloch frame's tabular", titled "\\usetheme{moloch}\n" (tab 40 ["Lima", "Mike"])),
      ("a three-column tabular", titled "" (tab 40 ["Lima", "Mike", "Oscar"])),
      ("tabulars in beamer columns", titled "" ("\\begin{columns}[T]\n" ++
        column (tab 30 ["Lima", "Mike"]) ++ column (tab 30 ["Oscar", "Papa"]) ++ "\\end{columns}")),
      ("beamer columns", titled "" ("\\begin{columns}\n" ++ column (lines "Lima" ++ lines "Oscar") ++
        column (lines "Mike" ++ lines "Papa") ++ "\\end{columns}"))] do
    let counts := titleCounts oneFace src "Kilo"
    t s!"page overrun: {what} breaking in a titled frame draws its title once a page, tags too"
      (1 < counts.size && counts.all (· == (1, 1)))
  for (what, title, first) in
      [("a titled frame", "{Kilo}", "220pt"), ("an untitled frame", "", "263pt")] do
    let ds := (sitedFitDiags oneFace (deck ("\\begin{frame}" ++ title ++ "\n\\only<1>{\\rule{1cm}{" ++
      first ++ "}}\n\\only<2>{\\rule{1cm}{300pt}}\n\\end{frame}"))).filter fun d =>
        d.kind == .W0358 || d.kind == .W0384 || d.kind == .W0400
    t s!"page overrun: {what}'s box past its page on one step and overhang on another are one line"
      (ds.map (·.kind) == #[.W0358] &&
        ds.all fun d => (d.detail.getD "").endsWith "past on another step")
  for (what, box, caption) in
      [("on its box", longNote 130, ""), ("in its caption", "", longNote 130)] do
    t s!"page overrun: a float whose footnote {what} alone overruns its page names the note"
      ((allCodes oneFace (article ("Kilo words.\n\\begin{figure}[h]\n\\rule{1cm}{15cm}" ++ box ++
        "\n\\caption{Lima caption." ++ caption ++ "}\n\\end{figure}\nMike words."))).filter
        (fun c => c == .W0358 || c == .W0372) == #[.W0372])
  let boxDetails (src : String) : Array (Option String) :=
    ((fittedOf oneFace (elabStr src).1).out.diags.filter (·.kind == .W0358)).map (·.detail)
  for (what, noted) in [
      ("a flow page's", fun n => article ("Kilo words.\n\n\\rule{1cm}{30cm}" ++ longNote n ++
        "\n\nMike words.")),
      ("a titled frame's", fun n => deck ("\\begin{frame}{Kilo}\n\\rule{1cm}{12cm}" ++ longNote n ++
        "\n\\end{frame}"))] do
    t s!"page overrun: {what} box past its page under a note is named by its own overrun"
      ((boxDetails (noted 1)).size == 1 && boxDetails (noted 12) == boxDetails (noted 1))
  let floatFrame := deck ("\\begin{frame}{Kilo}\n\\begin{figure}\n\\rule{1cm}{12cm}\n" ++
    "\\caption{Lima caption.}\n\\end{figure}\n\\end{frame}")
  t "page overrun: a titled frame's float taller than its page stands below the title on one page"
    ((fittedOf oneFace (elabStr floatFrame).1).out.pages.size == 1 &&
      (allCodes oneFace floatFrame).filter (· == .W0358) == #[.W0358])

end Tests.PageOverrun
