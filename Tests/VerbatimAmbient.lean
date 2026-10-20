module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! A bare `verbatim` sets in the mono family at the size in force where it stands, as LaTeX's
`\verbatim@font` does; a package's own size option stays separate. -/

/-- The first verbatim or listing block of an elaborated source. -/
private def firstListingSpec (src : String) : Option Ir.ListingSpec :=
  (elabStr src).1.body.findSome? fun b => match b with
    | .verbatim _ _ spec | .role _ #[.verbatim _ _ spec] => some spec
    | _ => none

/-- The first glyph-setting run of a shipped body line holding `needle`: its face index, size and
leading. -/
private def runOf (out : Layout.Out) (needle : String) :
    Option (Nat × Dim.Length × Option Dim.Length) :=
  (bodyLines out).findSome? fun l =>
    if hasStr (lineText l) needle then
      l.segs.findSome? fun s => match s with
        | .run idx _ _ _ glyphs size metrics _ _ _ _ =>
          if glyphs.isEmpty then none else some (idx, size, metrics.leading)
        | _ => none
    else none

/-- The `style` attribute of the emitted `<pre>` block. -/
private def preStyleOf (doc : Ir.Doc) : Option String :=
  let page := (HtmlDoc.emit {} doc).1
  match page.splitOn "<pre" with
  | _ :: rest :: _ =>
    match (rest.splitOn "style=\"") with
    | _ :: v :: _ => (v.splitOn "\"").head?
    | _ => none
  | _ => none

def verbatimAmbientChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (n : String) : IO (Option Font) := do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    match Font.parse (← IO.FS.readBinFile p) with
    | .ok f => pure (some f)
    | .error _ => pure none
  -- The mono slot (2) in its own face, so a run's face index says whether it set monospaced.
  let some serif ← load "SourceSerifPro-Regular.otf"
    | failures ref "verbatim ambient: the shipped serif face did not load"
  let some mono ← load "SourceCodePro-Regular.otf"
    | failures ref "verbatim ambient: the shipped mono face did not load"
  let fs : Font.FontSet := {
    fonts := #[serif, mono]
    index := ((List.range 3).flatMap fun slot =>
      let f := if slot == 2 then 1 else 0
      [((slot, 400, false), f), ((slot, 700, false), f),
       ((slot, 400, true), f), ((slot, 700, true), f)]).toArray }
  let geom : Layout.Geom := {}
  let base := geom.fontSize
  let footStep := Ir.scaleStepIn Ir.sizeScale base "footnotesize"
  let smallStep := Ir.scaleStepIn Ir.sizeScale base "small"

  t "verbatim ambient: a top-level bare verbatim inherits normalsize"
    ((firstListingSpec (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).map (·.fontSize)
      == some (Ir.Style.size "normalsize"))
  t "verbatim ambient: a bare verbatim in a \\small group inherits small"
    ((firstListingSpec (dvDoc "" "{\\small\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).map
      (·.fontSize) == some (.size "small"))
  t "verbatim ambient: a bare verbatim in a \\Large group inherits Large"
    ((firstListingSpec (dvDoc "" "{\\Large\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).map
      (·.fontSize) == some (.size "Large"))
  t "verbatim ambient: after a \\small group closes, verbatim is back at normalsize"
    ((firstListingSpec (dvDoc "" "{\\small x}\n\\begin{verbatim}\nx\n\\end{verbatim}")).map
      (·.fontSize) == some (.size "normalsize"))
  t "verbatim ambient: a nested \\footnotesize group reaches verbatim as footnotesize"
    ((firstListingSpec
        (dvDoc "" "{\\Large {\\footnotesize\n\\begin{verbatim}\nx\n\\end{verbatim}\n}}")).map
      (·.fontSize) == some (.size "footnotesize"))

  let outBase := layoutOf fs (elabStr
    (dvDoc "" "prose reading.\n\n\\begin{verbatim}\ncodeline\n\\end{verbatim}")).1 geom
  match runOf outBase "codeline", runOf outBase "prose" with
  | some (vIdx, vSize, vLead), some (pIdx, _, _) =>
    t "verbatim ambient: the shipped code sets at the ambient (normalsize) size"
      (vSize == base && vSize != footStep)
    t "verbatim ambient: the shipped code sets on the ambient leading"
      (vLead == some (Ir.leadingFor base geom.leading) &&
        vLead != some (Ir.leadingFor footStep geom.leading))
    t "verbatim ambient: the shipped code sets in the mono slot"
      (vIdx == 1 && pIdx == 0)
  | _, _ => failures ref "verbatim ambient: the code or prose line did not ship"

  let outSmall := layoutOf fs (elabStr
    (dvDoc "" "{\\small\n\\begin{verbatim}\ncodeline\n\\end{verbatim}\n}")).1 geom
  match runOf outSmall "codeline" with
  | some (_, vSize, _) =>
    t "verbatim ambient: a \\small group sets the code at the small step"
      (vSize == smallStep && vSize != footStep)
  | none => failures ref "verbatim ambient: the small-scoped code line did not ship"

  let preBase := preStyleOf (elabStr (dvDoc "" "\\begin{verbatim}\nx\n\\end{verbatim}")).1
  t "verbatim ambient: the HTML pre carries the ambient font-size, not footnotesize"
    ((preBase.map fun s => hasStr s "font-size: 1em;" && !hasStr s "font-size: 0.8em;")
      == some true)
  let preSmall := preStyleOf
    (elabStr (dvDoc "" "{\\small\n\\begin{verbatim}\nx\n\\end{verbatim}\n}")).1
  t "verbatim ambient: a \\small group sets the HTML pre at 0.9em"
    ((preSmall.map fun s => hasStr s "font-size: 0.9em;") == some true)

  t "verbatim ambient: lstlisting basicstyle sets its own size, separate from ambient"
    ((firstListingSpec
        (dvDoc "" "\\begin{lstlisting}[basicstyle=\\ttfamily\\footnotesize]\nx\n\\end{lstlisting}")).map
      (·.fontSize) == some (.size "footnotesize"))
  t "verbatim ambient: minted fontsize sets its own size, separate from ambient"
    ((firstListingSpec
        (dvDoc "" "\\begin{minted}[fontsize=\\small]{text}\nx\n\\end{minted}")).map
      (·.fontSize) == some (.size "small"))
  t "verbatim ambient: a bare lstlisting inherits the ambient size"
    ((firstListingSpec (dvDoc "" "{\\small\n\\begin{lstlisting}\nx\n\\end{lstlisting}\n}")).map
      (·.fontSize) == some (.size "small"))

/-- A heading inside a text-font command's argument sets as LaTeX sets it, ending the paragraph
around it, and a listing read through a command's argument is named, both on shipped lines. -/
def argumentBlockChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some serif ← (do
      match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
      | .ok f => pure (some f)
      | .error _ => pure none)
    | failures ref "argument blocks: the shipped serif face did not load"
  let fs : Font.FontSet := {
    fonts := #[serif]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray }
  let lines (src : String) : Array String × Array Diag :=
    let (doc, ds) := elabStr src
    ((bodyLines (layoutOf fs doc)).map (lineText ·), ds)
  for (what, inner) in [("bold", "\\textbf{Alpha \\section{Kqzv} Omega}"),
      ("nested emphasis", "\\textbf{\\emph{Alpha \\section*{Kqzv} Omega}}"),
      ("coloured", "\\textcolor{red}{Alpha \\subsection{Kqzv} Omega}")] do
    let (ls, ds) := lines (dvDoc "" ("Before.\n" ++ inner ++ "\nAfter."))
    let lineAt (s : String) : Option Nat := ls.findIdx? (hasStr · s)
    t s!"argument blocks: a heading in {what} text ends its paragraph, the text either side joining \
the paragraphs around it ({ls}, {ds.map (·.code)})"
      (!ds.any (·.kind == .E0312) && lineAt "Before." == lineAt "Alpha" && lineAt "Omega" == lineAt "After." &&
        (match lineAt "Alpha", lineAt "Kqzv", lineAt "Omega" with
         | some a, some k, some o => a < k && k < o
         | _, _, _ => false))
  let listing := "\\begin{verbatim}\nverb words\n\\end{verbatim}"
  -- Every W0411 a source raises counts, so one site's two accountings would read as two.
  let sites (ds : Array Diag) : Nat := (ds.filter (·.kind == .W0411)).size
  let lr := "\\fbox{" ++ listing ++ "}"
  for (what, src, want) in [
      ("a box's argument", dvDoc "" ("A \\parbox{6cm}{" ++ listing ++ "} b."), 1),
      ("a box's argument among words",
        dvDoc "" ("\\parbox{6cm}{Some words " ++ listing ++ " more words}"), 1),
      ("a centre in a box's argument",
        dvDoc "" ("\\parbox{6cm}{\\begin{center}" ++ listing ++ "\\end{center}}"), 1),
      ("an LR box's argument, named by the inline reading alone", dvDoc "" ("A " ++ lr ++ " b."), 1),
      ("a macro's argument",
        dvDoc "\\newcommand{\\wrapper}[1]{#1}\n" ("A\n\\wrapper{" ++ listing ++ "}\nb."), 1),
      ("a box in a macro's argument", dvDoc "\\newcommand{\\wrapper}[1]{#1}\n"
        ("\\wrapper{\\parbox{3cm}{" ++ listing ++ "}}"), 1),
      ("a used definition's text", dvDoc ("\\newcommand{\\cbody}{" ++ listing ++ "}\n") "\\cbody", 1),
      ("a group after a spacing command", dvDoc "" ("A.\n\\medskip\n{\\small " ++ listing ++ "}"), 0),
      ("a group after a length", dvDoc "" ("A.\n\\vspace{1em}\n{\\footnotesize " ++ listing ++ "}"),
        0),
      ("a group after noindent", dvDoc "" ("\\noindent{" ++ listing ++ "}"), 0),
      ("an item's group", dvDoc ""
        ("\\begin{itemize}\n\\item[\\textbf{x}] {\\small " ++ listing ++ "}\n\\end{itemize}"), 0),
      ("an mbox's argument", dvDoc "" ("A \\mbox{" ++ listing ++ "} b."), 1),
      ("a makebox's argument", dvDoc "" ("A \\makebox[4cm]{" ++ listing ++ "} b."), 1),
      ("a box in a box", dvDoc "" ("A \\mbox{\\mbox{" ++ listing ++ "}} b."), 1),
      ("a minipage", dvDoc "" ("\\begin{minipage}{6cm}\n" ++ listing ++ "\n\\end{minipage}"), 0),
      ("the body", dvDoc "" listing, 0)] do
    let (ls, ds) := lines src
    t s!"argument blocks: a listing in {what} draws {want} W0411, its words set ({sites ds})"
      (sites ds == want && ls.any (hasStr · "verbwords"))
  -- An environment defined over verbatim's halves sets its body verbatim, as the verbatim package
  -- reads it; spelled as the environment, which LaTeX cannot read, it is named.
  for (halves, want) in [("{\\verbatim}{\\endverbatim}", 0),
      ("{\\begin{verbatim}}{\\end{verbatim}}", 1)] do
    let (ls, ds) := lines (dvDoc ("\\usepackage{verbatim}\n\\newenvironment{codev}" ++ halves ++ "\n")
      "Before.\n\\begin{codev}\nverb \\words{\n\\end{codev}\nAfter.")
    t s!"argument blocks: an environment over verbatim's halves {halves} sets its body verbatim, \
{want} W0411 ({ls}, {ds.map (·.code)})"
      (sites ds == want && !ds.any (fun d => d.severity == .error || d.kind == .W0301) &&
        ls.any (hasStr · "\\words{"))
  let (_, boxDefDs) := lines (dvDoc ("\\newcommand{\\unusedbox}{\\mbox{" ++ listing ++ "}}\n") "Words.")
  t "argument blocks: a box in a definition no call runs names nothing" (sites boxDefDs == 0)
  let (cls, cds) := lines (dvDoc ("\\usepackage{verbatim}\n\\newenvironment{codev}% note\n  " ++
    "{\\verbatim}%\n  {\\endverbatim}\n") "\\begin{codev}\nverb \\words{\n\\end{codev}")
  t s!"argument blocks: a verbatim definition across commented lines is read ({cls})"
    (!cds.any (fun d => d.severity == .error || d.kind == .W0301) && cls.any (hasStr · "\\words{"))
  let (rls, rds) := lines (dvDoc ("\\newenvironment{codev}{\\verbatim}{\\endverbatim}\n" ++
    "\\renewenvironment{codev}{\\itshape}{}\n") "\\begin{codev}\\emph{Kqzv} y\\end{codev}")
  t s!"argument blocks: a redefinition with other text ends a verbatim environment ({rls})"
    (!rds.any (·.severity == .error) && rls.any (hasStr · "Kqzv") && !rls.any (hasStr · "\\emph"))
  let (ils, ids) := lines (dvDoc "" ("\\begin{itemize}\n\\item Alpha \\textbf{\\item Kqzv} Omega\n" ++
    "\\end{itemize}"))
  let itemAt (s : String) : Option Nat := ils.findIdx? (hasStr · s)
  t s!"argument blocks: an item in bold text starts the next item, the text after it bold in it \
({ils}, {ids.map (·.code)})"
    (!ids.any (·.kind == .E0312) && itemAt "Kqzv" == itemAt "Omega" &&
      (match itemAt "Alpha", itemAt "Kqzv" with
       | some a, some k => a < k
       | _, _ => false))
  let (odoc, ods) := elabStr ("\\documentclass{beamer}\n\\begin{document}\n\\begin{frame}\n" ++
    "\\begin{itemize}\n\\item Alpha \\textbf{\\item<2-> Kqzv} Omega\n\\end{itemize}\n" ++
    "\\end{frame}\n\\end{document}")
  let ols := (allLines (layoutOf fs odoc)).map (lineText ·)
  t s!"argument blocks: an item's overlay stays the item's when bold text holds it ({ols})"
    (!ods.any (·.severity == .error) && !ols.any (hasStr · "<2") && ols.any (hasStr · "Kqzv"))
  let (tdoc, _) := elabStr (dvDoc "" "Text\\footnote{Intro. \\section{Ka}\\subsection{Kb} rest.} more.")
  let tls := (allLines (layoutOf fs tdoc)).map (lineText ·)
  t s!"argument blocks: two headings in a footnote are two lines, no empty one between ({tls})"
    (match tls.findIdx? (hasStr · "Ka"), tls.findIdx? (hasStr · "Kb") with
     | some a, some b => b == a + 1
     | _, _ => false)
  let (ldoc, _) := elabStr (dvDoc "" ("Text\\footnote{Intro. \\section{Ka}\\begin{itemize}\\item Kone " ++
    "\\item Ktwo\\end{itemize}\\section{Kb} rest.} more \\footnote{Intro. \\section{Kc}\\label{s:kc}} end."))
  let lls := (allLines (layoutOf fs ldoc)).map (lineText ·)
  let lat (s : String) : Option Nat := lls.findIdx? (hasStr · s)
  t s!"argument blocks: a footnote's headings and list items are lines, none empty, a label after the last ending none ({lls})"
    ((match lat "Ka", lat "Kone", lat "Ktwo", lat "Kb", lat "rest." with
      | some a, some o, some w, some b, some r => o == a + 1 && w == o + 1 && b == w + 1 && r == b + 1
      | _, _, _, _, _ => false) && lat "Kc" == some (lls.size - 2))
  let (fdoc, fds) := elabStr (dvDoc "" "Text\\footnote{Before. \\section{Kqzv} note.} more.")
  let fls := (allLines (layoutOf fs fdoc)).map (lineText ·)
  let fat (s : String) : Option Nat := fls.findIdx? (hasStr · s)
  t s!"argument blocks: a heading in a footnote is a bold line of the note, named once \
({fls}, {fds.map (·.code)})"
    (!fds.any (·.kind == .E0312) && (fds.filter (·.kind == .W0371)).size == 1 &&
      (match fat "Before.", fat "Kqzv", fat "note." with
       | some a, some k, some o => a < k && k < o
       | _, _, _ => false))
  let (_, unusedDs) := lines (dvDoc ("\\newcommand{\\unused}{" ++ listing ++ "}\n") "Words.")
  t "argument blocks: a definition no call runs names nothing" (sites unusedDs == 0)
  let (_, fileDs) := lines (dvDoc "\\usepackage{listings}\n\\newcommand{\\inc}[1]{\\lstinputlisting{#1}}\n"
    "\\inc{probe-snippet.txt}")
  t "argument blocks: a listing a macro reads from a file is no listing scanned as an argument"
    (sites fileDs == 0)
  let (cdoc, _) := elabStr (dvDoc "\\usepackage{xcolor}\n" "\\textcolor{red}{\\section{Kqzv}}")
  let red : Ir.Color := ((default : Ir.Palette).resolve "red").getD Ir.Color.black
  t "argument blocks: a colour over a heading colours the heading"
    (let inks := inksOn (layoutOf fs cdoc) (hasStr · "Kqzv"); !inks.isEmpty && inks.all (· == red))
  let (mdoc, mds) := elabStr (dvDoc "\\usepackage{xcolor}\n"
    "Before.\n\\textcolor[rgb]{1,0,0}{C \\section{Model} D}\nAfter.")
  t "argument blocks: a colour with a model argument over a heading sets it"
    (!mds.any (·.kind == .E0312) && (bodyLines (layoutOf fs mdoc)).any (fun l => hasStr (lineText l) "Model"))
