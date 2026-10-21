module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.TitleNames

/-- An article whose preamble is `pre`, its title block `\maketitle` and its body `body`. -/
private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n\\maketitle\n" ++ body ++
    "\n\\end{document}\n"

/-- datetime's named dates, the kernel's text scripts and `\and` set what LaTeX sets on the page,
and none prints a configuration name as ink. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let dated := "\\usepackage{datetime}\n\\newdate{zzday}{15}{1}{2026}\n\\title{Lima}\\author{Kilo}" ++
    "\\date{\\displaydate{zzday}}\n"
  let (c, ds) := page (article dated "Body.")
  -- lualatex prints "Thursday 15th January, 2026" for this date, the suffix raised
  t "datetime: a displayed date is its day, ordinal and month, never the date's name"
    (pageHas c 0 "Thursday" && pageHas c 0 "January, 2026" && !pageHas c 0 "zzday" &&
      ds.all (·.code != "W0301") && ds.all (·.code != "W0103"))
  let raisedTh := c[0]?.any fun p => p.lines.any fun l =>
    hasStr l.text "15th" && l.runRaises.any (· > 0)
  t s!"datetime: the ordinal suffix stands raised above the date's baseline \
({c[0]?.map fun p => p.lines.map fun l => (l.text, l.runRaises.map (·.toSp))})" raisedTh
  for (opts, switch, want) in [("[us]", "", "January 15, 2026"), ("[yyyymmdd]", "", "2026/01/15"),
      ("[nodayofweek]", "", "15th January, 2026"), ("", "\\shortdate", "Thu 15th Jan, 2026"),
      ("", "\\ddmmyyyydate", "15/01/2026")] do
    let pre := s!"\\usepackage{opts}\{datetime}\n\\newdate\{zzday}\{15}\{1}\{2026}\n"
    let (c, ds) := page (article pre (switch ++ "\\displaydate{zzday}"))
    t s!"datetime {opts}{switch}: the date reads '{want}' ({c[0]?.map fun p => p.lines.map (·.text)})"
      (pageHas c 0 want && ds.all (·.code != "W0104") && ds.all (·.code != "W0301"))
  let (c, ds) := page (article "\\usepackage{datetime}\n" "Lead \\displaydate{zzmissing} tail.")
  t "datetime: an undeclared date sets nothing and is named once"
    (pageHas c 0 "Lead" && !pageHas c 0 "zzmissing" && (ds.filter (·.code == "W0104")).size == 1)
  let (c, _) := page (article "" "Kilo\\textsuperscript{zz} and Lima\\textsubscript{yy}.")
  let raisedOn (w : String) (above : Bool) : Bool := c[0]?.any fun p => p.lines.any fun l =>
    hasStr l.text w && l.runRaises.any fun r => if above then r > 0 else r < 0
  t "text scripts: a superscript stands above the baseline and a subscript below"
    (raisedOn "zz" true && raisedOn "yy" false)
  let named := "\\title{Lima}\\author{Ada Example \\and Bo Sample}\\date{}\n"
  let (doc, ds) := elabStr (article named "Body.")
  let out := layoutOf oneFace doc
  let runs := (out.pages[0]?.map (·.lines)).getD #[] |>.flatMap fun l =>
    (lineRuns l).map fun (_, text, x, w) => (text, x, w, l.y)
  let ends := (runs.find? (hasStr ·.1 "Example")).map fun (_, x, w, y) => (x + w, y)
  let starts := (runs.find? (hasStr ·.1 "Bo")).map fun (_, x, _, y) => (x, y)
  t "and: \\and is read" (ds.all (·.code != "W0301"))
  -- latex.ltx's `\and` sets each name in a tabular, a tabcolsep, 1em and a share of the line apart
  t s!"and: the metadata reads the names apart by a comma ({doc.info.author})"
    (doc.info.author == some "Ada Example, Bo Sample")
  t s!"and: the names share a line, an em and two tabcolseps apart ({ends.map (·.1.toSp)}, {starts.map (·.1.toSp)})"
    (match ends, starts with
      | some (e, y), some (b, y') => y == y' && b - e ≥ Dim.pt 22 - Dim.Length.ofSp 64
      | _, _ => false)
  let stacked := "\\title{Lima}\\author{Ada Example\\\\ Kilo Institute \\and Bo Sample\\\\ Mike College}" ++
    "\\date{}\n"
  let (c, _) := page (article stacked "Body.")
  t "and: a name of several lines keeps its lines, the next name after them, a named loss"
    (["Ada Example", "Kilo Institute", "Bo Sample", "Mike College"].all (pageHas c 0 ·) &&
      (lineYOf c 0 "Kilo Institute").any fun y => (lineYOf c 0 "Bo Sample").any (y < ·))

  let deck := "\\documentclass{beamer}\n\\title{Lima}\\author{Ada Example \\and Bo Sample}\n" ++
    "\\begin{document}\n\\begin{frame}\\titlepage\\end{frame}\n\\end{document}\n"
  let (ddoc, dds) := elabStr deck
  t s!"and: a deck reads \\and, its metadata a comma apart ({ddoc.info.author})"
    (dds.all (·.code != "W0301") && ddoc.info.author == some "Ada Example, Bo Sample")
  let (c, _) := page (article "\\usepackage{datetime}\n"
    ("{\\shortdate} \\formatdate{9}{9}{2026}. \\shortdate\\formatdate{9}{9}{2026}. " ++
      "\\renewcommand{\\dateseparator}{-}\\yyyymmdddate\\formatdate{15}{1}{2026}"))
  t s!"datetime: a format switch ends with its group, September's short name is Sept, and a declared separator stands ({censusText c})"
    (pageHas c 0 "Wednesday 9th September, 2026." && pageHas c 0 "Wed 9th Sept, 2026." &&
      pageHas c 0 "2026-01-15")
  let (sdoc, _) := elabStr (article "" "{\\Large Kilo\\textsuperscript{zz}}\n\nLima\\textsuperscript{zz}")
  let sruns := ((layoutOf oneFace sdoc).pages[0]?.map (·.lines)).getD #[] |>.flatMap fun l =>
    (lineRuns l).map fun (_, text, _, w) => (text, w)
  let widths : Array Dim.Length := (sruns.filter (·.1 == "zz")).map (·.2)
  -- lualatex sets `\textsuperscript` at `\sf@size`: 10pt under `\Large`, 7pt in the body
  t s!"text scripts: a superscript takes the script size of the size in force ({widths.map (·.toSp)})"
    (match widths.toList with
      | [big, small] => small * 9 < big * 7 && big * 7 < small * 11
      | _ => false)

end Tests.TitleNames
