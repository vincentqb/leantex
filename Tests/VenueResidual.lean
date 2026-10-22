module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Dim

/-! The constructs a usual venue paper shows beside its style: pictures reading the measure,
float barriers, declared characters, indented verbatim, headings through macro chains, the
normal font on the web and natbib's tied labels. -/

/-- Every body line's text, place and size. -/
private def residualLines (out : Layout.Out) : Array (String × Length × Length × Length) :=
  (bodyLines out).map fun l => (lineText l, l.x, l.y, l.size)

/-- A boundary picture reading the measure reads the document's text width, and one reading none
carries no measure. -/
def pictureMeasureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc := (elabStr (dvDoc "\\usepackage{geometry}\n\\geometry{textwidth=5.5in}\n" "x")).1
  let req (body : String) : String := Ir.pictureRequest doc { kind := .picture, body }
  let flow := req ("[box/.style={draw, rounded corners, text width=.155\\linewidth}]\n" ++
    "\\node[box] (a) {Alpha};\n\\node[box, right=of a] (b) {Beta};\n")
  t "a boundary picture reading \\linewidth is drawn at the document's text width"
    (hasStr flow "\\setlength{\\linewidth}{397.485pt}" &&
      hasStr flow "\\setlength{\\textwidth}{397.485pt}")
  t "a boundary picture reading no measure sets none"
    (!hasStr (req "[box/.style={draw, rounded corners, text width=2cm}]\n\\node[box] {Alpha};\n")
      "\\setlength{\\linewidth}")

/-- placeins' `\FloatBarrier` sets nothing, as a float here never moves past the text after it. -/
def floatBarrierChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let set (pre body : String) := residualLines (layoutOf fonts (elabStr (dvDoc pre body)).1)
  let fig := "Before words.\n\n\\begin{figure}[t]\\centering Boxed words.\\caption{A caption.}" ++
    "\\end{figure}\n"
  t "a float before a barrier stands where it stands without the barrier"
    (set "\\usepackage{placeins}\n" (fig ++ "\\FloatBarrier\nAfter words.") ==
      set "" (fig ++ "After words."))
  let (_, ds) := elabStr (dvDoc "\\usepackage{placeins}\n" "Words.\\FloatBarrier")
  t "the barrier and its package are read, not unknown"
    (ds.all fun d => d.code != "W0301" && d.code != "W0103")
  let (_, opts) := elabStr (dvDoc "\\usepackage[section]{placeins}\n" "Words.")
  t "the package's section option is inert, not a loss" (opts.all (·.code != "W0104"))
  let tall := String.join (List.replicate 200 "Filler words fill the page. ") ++ "\n\n" ++
    "\\begin{figure}[t]\\centering\\rule{1pt}{0.6\\textheight}\\caption{A tall caption.}" ++
    "\\end{figure}\n\\FloatBarrier\nAfter words."
  let out := layoutOf fonts (elabStr (dvDoc "\\usepackage{placeins}\n" tall)).1
  let at? (w : String) : Option (Nat × Length) := out.pages.zipIdx.toList.findSome? fun (p, i) =>
    (p.lines.find? fun l => hasStr (lineText l) w).map fun l => (i, l.y)
  t "a float the page cannot hold still stands before the text after a barrier"
    (match at? "A tall caption.", at? "After words." with
     | some (pf, yf), some (pa, ya) => pf < pa || (pf == pa && yf < ya)
     | _, _ => false)

/-- newunicodechar's declared character sets its code wherever it stands after the declaration. -/
def unicodeCharChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let text (pre body : String) : String :=
    String.join ((bodyLines (layoutOf fonts (elabStr (dvDoc pre body)).1)).toList.map (lineText ·))
  let pre := "\\usepackage{newunicodechar}\n\\newunicodechar{¶}{Q}\n"
  t "a declared character sets its code in a word, a group and math"
    (text pre "a¶b {¶} $x¶$ end." == text "" "aQb {Q} $xQ$ end.")
  t "verbatim text keeps the character"
    (hasStr (text pre "\\verb|a¶b|") "a¶b")
  t "the character before its declaration stands as written"
    (hasStr (text "" "a¶b \\newunicodechar{¶}{Q}a¶b") "a¶b")
  let (_, ds) := elabStr (dvDoc pre "a¶b")
  t "the declaration is read, not unknown" (ds.all fun d => d.code != "W0301" && d.code != "W0103")

/-- fancyvrb's `xleftmargin` sets the code in from the measure's left, its em the ambient font's. -/
def verbatimMarginChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let xs (opts : String) : Array Length :=
    (bodyLines (layoutOf fonts (elabStr (dvDoc "\\usepackage{fancyvrb}\n"
      ("\\begin{Verbatim}" ++ opts ++ "\ndef f(x):\n    return x\n\\end{Verbatim}"))).1)).map (·.x)
  let plain := xs ""
  let wide := xs "[xleftmargin=2em]"
  let small := xs "[xleftmargin=2em, fontsize=\\small]"
  t "each line stands two ems of the body in"
    (plain.size == 2 && wide.size == 2 &&
      (wide.zip plain).all fun (w, p) => w - p == Dim.pt 20)
  t "the em is the ambient font's at any code size"
    ((small.zip plain).all fun (w, p) => w - p == Dim.pt 20)
  let inScope := (bodyLines (layoutOf fonts (elabStr (dvDoc "\\usepackage{fancyvrb}\n"
    ("{\\small\\begin{Verbatim}[xleftmargin=2em]\ndef f(x):\n    return x\n\\end{Verbatim}}"))).1)).map (·.x)
  t "the em is the ambient size's inside a size scope"
    ((inScope.zip plain).all fun (w, p) => w - p == Dim.pt 18)
  let lst := (bodyLines (layoutOf fonts (elabStr (dvDoc "\\usepackage{listings}\n"
    ("\\begin{lstlisting}[xleftmargin=2em, basicstyle=\\small]\ndef f(x):\n    return x\n" ++
      "\\end{lstlisting}"))).1)).map (·.x)
  let lstPlain := (bodyLines (layoutOf fonts (elabStr (dvDoc "\\usepackage{listings}\n"
    ("\\begin{lstlisting}[basicstyle=\\small]\ndef f(x):\n    return x\n\\end{lstlisting}"))).1)).map
      (·.x)
  let captionX (opts : String) : Option Length :=
    ((bodyLines (layoutOf fonts (elabStr (dvDoc "\\usepackage{listings}\n"
      ("\\begin{lstlisting}[caption={An invented caption.}" ++ opts ++ "]\nx = 1\n" ++
        "\\end{lstlisting}"))).1)).find? fun l => hasStr (lineText l) "invented caption").map (·.x)
  t "a listing's caption keeps its place beside a margin"
    (captionX ", xleftmargin=2em" == captionX "" && (captionX "").isSome)
  t "listings reads the em in its code font"
    (lst.size == 2 && (lst.zip lstPlain).all fun (w, p) => w - p == Dim.pt 18)
  let html := docHtmlOf (elabStr (dvDoc "\\usepackage{fancyvrb}\n"
    "\\begin{Verbatim}[xleftmargin=1cm]\nx = 1\n\\end{Verbatim}")).1
  t "the web page sets the same margin" (hasStr html "margin-inline-start: 28.346pt")
  let (_, ds) := elabStr (dvDoc "\\usepackage{fancyvrb}\n"
    "\\begin{Verbatim}[xleftmargin=2em]\nx\n\\end{Verbatim}")
  t "the key and the package are read" (ds.all fun d => d.code != "W0110" && d.code != "W0103")

/-- A heading a document macro reaches through another macro is a heading, in the flow and at an
environment's opening. -/
def macroChainHeadingChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let set (pre body : String) := residualLines (layoutOf fonts (elabStr (dvDoc pre body)).1)
  let chain := "\\newcommand{\\inner}{\\section*{Thanks}}\n\\newcommand{\\outer}{\\inner}\n"
  t "a macro calling a heading macro sets the heading"
    (set chain "Start.\n\\outer\nBody." == set "" "Start.\n\n\\section*{Thanks}\nBody.")
  t "an environment opening with that macro sets the heading"
    (set (chain ++ "\\newenvironment{wrap}{\\outer}{}\n") "Start.\n\\begin{wrap}Body.\\end{wrap}" ==
      set "" "Start.\n\n\\section*{Thanks}\nBody.")
  let (_, ds) := elabStr (dvDoc chain "Start.\n\\outer\nBody.")
  t "the chained heading is no misplaced command" (ds.all (·.code != "E0312"))

/-- `\normalfont` inside a weight or a shape resets it on the web page, as on paper. -/
def normalFontHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let html (body : String) : String := docHtmlOf (elabStr (dvDoc "" body)).1
  let reset := "<span class=\"rm md up\">"
  t "the text after \\normalfont in a bold run is set upright and regular"
    (hasStr (html "{\\bfseries Bold \\normalfont plain} words.") (reset ++ "plain</span>"))
  t "\\textnormal inside an italic run is reset too"
    (hasStr (html "\\textit{slanted \\textnormal{upright}} words.") (reset ++ "upright</span>"))

/-- natbib's author-year label reads a tie as the space it prints, so the citation names the
authors before it. -/
def natbibTieChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let cited (label : String) : Option String :=
    let (d, _) := elabStr (dvDoc "\\usepackage[round]{natbib}\n"
      ("See \\citep{ex}.\n\n\\begin{thebibliography}{9}\n\\bibitem[" ++ label ++
        "]{ex} A.~Example. A title. 2017.\n\\end{thebibliography}"))
    (Bib.apply #[] d Bib.plainReading).1.body[0]? |>.map fun
      | Ir.Block.para xs => Ir.plainText xs
      | _ => ""
  t "a tied et al. label cites its first author"
    (cited "Example et~al.(2017)Example, Sample, and Other" == some "See (Example et al., 2017).")
  t "the tied label cites as the spaced one"
    (cited "Example et~al.(2017)Example, Sample, and Other" ==
      cited "Example et al.(2017)Example, Sample, and Other")

/-- The venue residual checks, over one face. -/
def venueResidualChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  pictureMeasureChecks ref
  floatBarrierChecks ref fonts
  unicodeCharChecks ref fonts
  verbatimMarginChecks ref fonts
  macroChainHeadingChecks ref fonts
  normalFontHtmlChecks ref
  natbibTieChecks ref
