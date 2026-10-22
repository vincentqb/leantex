module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.MystPackages

/-- An article loading `pkgs` with body `body`. -/
private def article (pkgs body : String) : String :=
  "\\documentclass{article}\n" ++ pkgs ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}\n"

/-- framed.sty's frames, longtable's tables and glossaries' entries set as LaTeX sets them on the
rendered page, as myst-to-tex writes them. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let note := "Lead paragraph.\n\n\\begin{framed}\n\\textbf{Note}\\\\\nKilo words.\n\\end{framed}\n\nTail."
  let (c, ds) := page (article "\\usepackage{framed}\n" note)
  let lead := lineXOf c 0 "Lead"
  let inside := lineXOf c 0 "Kilo"
  -- lualatex sets the frame's text 0.4pt and 9pt in from the measure, the frame its four rules
  t s!"framed: the text stands the rule and FrameSep in, the frame drawn ({ds.map (·.message)})"
    (ds.all (·.severity != .error) && ds.all (·.code != "W0302") &&
      (match lead, inside with
        | some l, some k => (k - l - Dim.pt 94 / 10).abs ≤ Dim.Length.ofSp 64
        | _, _ => false) && (c[0]?.any fun p => p.rules + p.fills > 0))
  let (plain, _) := page (article "" "Lead paragraph.\n\n\\textbf{Note}\\\\\nKilo words.\n\nTail.")
  let gap (c : Array CensusPage) := (lineYOf c 0 "Tail").bind fun y => (lineYOf c 0 "Lead").map (y - ·)
  t "framed: the frame stands its outer seps and its own above and below the text"
    ((gap c).any fun g => (gap plain).any fun p => g > p + Dim.pt 20)
  let rows := "\\begin{longtable}{ll}\nFirstHead & H \\\\\n\\endfirsthead\nNextHead & H \\\\\n\\endhead\n" ++
    "NextFoot & F \\\\\n\\endfoot\nLastFoot & F \\\\\n\\endlastfoot\nAlpha & 1 \\\\\nBravo & 2 \\\\\n\\end{longtable}"
  let (c, ds) := page (article "\\usepackage{longtable}\n" rows)
  t s!"longtable: one page sets the first head, the rows and the last foot, the repeats dropped ({censusText c})"
    (ds.all (·.severity != .error) && ["FirstHead", "Alpha", "Bravo", "LastFoot"].all (pageHas c 0 ·) &&
      !pageHas c 0 "NextHead" && !pageHas c 0 "NextFoot" &&
      (lineYOf c 0 "FirstHead").any fun y => (lineYOf c 0 "Alpha").any fun a => y < a &&
        (lineYOf c 0 "LastFoot").any (a < ·))
  let gls := "\\newacronym{zzap}{ZAP}{Zulu Alpha Papa}\n\\newglossaryentry{zzk}{name={kilo},description={a unit}}\n"
  let (c, ds) := page (article ("\\usepackage{glossaries}\n" ++ gls)
    "First \\gls{zzap}, then \\gls{zzap}, \\acrlong{zzap}, \\Gls{zzk} and \\glspl{zzk}.\\index{zzkey}")
  -- lualatex prints "First Zulu Alpha Papa (ZAP), then ZAP, Zulu Alpha Papa, Kilo and kilos."
  t s!"glossaries: a first use sets the long form and the short in parentheses, later ones the short ({censusText c})"
    (ds.all (·.code != "W0301") && pageHas c 0 "First Zulu Alpha Papa (ZAP), then ZAP," &&
      pageHas c 0 "Kilo and kilos." && !pageHas c 0 "zzap" && !pageHas c 0 "zzkey")
  let (c, _) := page (article ("\\usepackage{glossaries}\n" ++ gls)
    "\\acrlong{zzap}; \\acrshort{zzap}; \\gls{zzap}. \\gls{zzk}['s]; \\gls*{zzk}.")
  -- lualatex prints "Zulu Alpha Papa; ZAP; Zulu Alpha Papa (ZAP). kilo’s; kilo."
  t s!"glossaries: only a gls use spends the first use, and a final insert follows the text ({censusText c})"
    (pageHas c 0 "ZAP; Zulu Alpha Papa (ZAP)." && pageHas c 0 "kilo’s; kilo.")
  let long := String.join ((List.range 80).map fun i => s!"Paragraph {i} of invented words.\n\n")
  let (c, _) := page (article "\\usepackage{framed}\n" ("\\begin{framed}\n" ++ long ++ "\\end{framed}\nAfter."))
  t "framed: a frame no page holds breaks across pages, every paragraph shipped"
    (c.size ≥ 2 && (List.range 80).all fun i => c.any fun p => hasStr p.text s!"Paragraph {i} of")
  let (_, ds) := page (article "\\usepackage{glossaries}\n" "Lead \\gls{zzmissing}.")
  t "glossaries: an undeclared key sets nothing and is named"
    ((ds.filter (·.code == "W0104")).size == 1)

/-- authblk's authors and affiliations, doi's links, orcidlink's mark and lastpage's page count set
as LaTeX sets them, as myst-to-tex's templates use them. -/
def titleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (src : String) : Array CensusPage × Array Diag :=
    let (doc, ds) := elabStr src
    (censusOf #[] (layoutOf oneFace doc), ds)
  let blk := "\\author[1]{Ada Example}\n\\author[2]{Bo Sample}\n\\author[1,2]{Cy Third}\n" ++
    "\\affil[1]{Example Institute}\n\\affil[2]{Sample University}\n\\title{An Invented Paper}\n"
  let (c, ds) := page (article "\\usepackage{authblk}\n" (blk ++ "\\maketitle\nBody."))
  -- lualatex sets "Ada Example1, Bo Sample2, and Cy Third1,2", then each affiliation on its line
  t s!"authblk: every author with its mark and ', and' before the last, the affiliations below ({censusText c})"
    (ds.all (·.code != "W0103") && pageHas c 0 "Ada Example" && pageHas c 0 "Cy Third" && pageHas c 0 ", and" &&
      (lineYOf c 0 "Ada Example").any fun y => (lineYOf c 0 "Example Institute").any fun a =>
        (lineYOf c 0 "Sample University").any fun b => y < a && a < b)
  let (c, ds) := page (article ("\\usepackage{doi}\\usepackage{orcidlink}\\usepackage{lastpage}" ++
      "\\usepackage{fancyhdr}\\pagestyle{fancy}\\fancyhf{}\\cfoot{\\thepage\\ of \\pageref{LastPage}}\n")
    "Read \\doi{10.1000/zz} by \\orcidlink{0000-0000-0000-0000}.\\newpage Second.")
  -- lualatex prints "doi:10.1000/zz", the iD mark, and "1 of 2" and "2 of 2" in the feet
  t s!"doi, orcidlink and lastpage: the link's text, the iD mark named, the page count in the foot ({censusText c})"
    (ds.all (·.code != "W0103") && pageHas c 0 "doi:10.1000/zz" && pageHas c 0 "iD" &&
      ds.any (·.code == "N0100") && c.size == 2 && (c[1]?.any fun p => hasStr p.text "2 of 2"))

end Tests.MystPackages
