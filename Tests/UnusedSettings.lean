module

public import Tests.ParamCensus
public import LeanTex.Cli.FaceUse
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.FontDiscovery

public section

open LeanTex.Core LeanTex.Cli

/-! A setting the document declares that nothing it sets uses is named once where it stands
(W0449), judged from what the build reads; a package's, a class's or a theme's never is. -/

namespace Tests.UnusedSettings

/-- The unused-setting losses of a source, elaborated. -/
def unused (src : String) : Array Diag := (elabStr src).2.filter (·.kind == .W0449)

def article (pre body : String) : String :=
  s!"\\documentclass\{article}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

def deck (pre body : String) : String :=
  s!"\\documentclass\{beamer}\n{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"

/-- A probe colour no default spells. -/
def probeColor : String := "\\definecolor{probeink}{HTML}{8A2BE2}"

/-- Each declaration a document can leave unread, in a document that reads none of it, with the
subject its loss is keyed by. -/
def unreadCases : List (String × String × String) :=
  [("an xcolor colour", article probeColor "Words.", "unused:color:probeink"),
   ("a colour mixed from another", article "\\colorlet{probeink}{red!40}" "Words.",
     "unused:color:probeink"),
   ("a palette colour", article "\\palette{ probeink = #8A2BE2 }" "Words.",
     "unused:color:probeink"),
   ("a list style", article "\\style{itemize}{ gap = 4pt }" "Words.", "unused:style:itemize"),
   ("a heading style", article "\\style{section}{ before = 30pt }" "Words.",
     "unused:style:section"),
   ("a list level", article "\\usepackage{enumitem}\\setlist[enumerate,2]{leftmargin=4em}"
     "\\begin{enumerate}\\item Alpha\\end{enumerate}", "unused:style:enumerate2"),
   ("link colours", article "\\usepackage{hyperref}\\hypersetup{colorlinks, linkcolor=red}"
     "Words.", "unused:style:link,url,cite"),
   ("a beamer block font", deck "\\setbeamerfont{block title}{size=\\tiny}"
     "\\begin{frame}{Title}Words.\\end{frame}", "unused:style:block"),
   ("a beamer item template", deck "\\setbeamertemplate{itemize item}{\\textbullet}"
     "\\begin{frame}{Title}Words.\\end{frame}", "unused:style:itemize"),
   ("listing defaults", article "\\usepackage{listings}\\lstset{numbers=left}" "Words.",
     "unused:listing:lstset"),
   ("minted defaults", article "\\usepackage{minted}\\setminted{linenos}" "Words.",
     "unused:listing:setminted"),
   ("a lexer's minted defaults", article "\\usepackage{minted}\\setminted[python]{linenos}"
     "\\begin{minted}{bash}\necho probe\n\\end{minted}", "unused:listing:setminted:python"),
   ("inline-code defaults", article "\\usepackage{minted}\\setmintedinline{fontsize=\\small}"
     "\\begin{minted}{python}\nx = 1\n\\end{minted}", "unused:listing:setmintedinline")]

/-- Each declaration with content that reads it. -/
def readCases : List (String × String) :=
  [("a colour painting text", article probeColor "\\textcolor{probeink}{Words.}"),
   ("a colour in a mix", article probeColor "\\textcolor{probeink!50!white}{Words.}"),
   ("a colour as a declaration", article probeColor "{\\color{probeink} Words.}"),
   ("a colour its own command sets", article probeColor "\\probeink{Words.}"),
   ("a colour another declares from", article (probeColor ++ "\\colorlet{probedeep}{probeink!60!black}")
     "\\textcolor{probedeep}{Words.}"),
   ("a colour a picture paints", article ("\\usepackage{tikz}" ++ probeColor)
     "\\begin{tikzpicture}\\fill[probeink] (0,0) rectangle (1,1);\\end{tikzpicture}"),
   ("a colour a beamer element takes", deck (probeColor ++ "\\setbeamercolor{frametitle}{fg=probeink}")
     "\\begin{frame}{Title}Words.\\end{frame}"),
   ("a list style", article "\\style{itemize}{ gap = 4pt }"
     "\\begin{itemize}\\item Alpha\\end{itemize}"),
   ("a second-level list style", article "\\style{itemize2}{ gap = 4pt }"
     "\\begin{itemize}\\item Alpha\\begin{itemize}\\item Beta\\end{itemize}\\end{itemize}"),
   ("a numbered list style an algorithm's lines read", article
     "\\usepackage{algpseudocode}\\style{enumerate}{ gap = 4pt }"
     "\\begin{algorithmic}[1]\\State alpha\\end{algorithmic}"),
   ("a heading style", article "\\style{section}{ before = 30pt }" "\\section{Opening}Words."),
   ("a heading style a frame title reads on the web page", deck "\\style{section}{ before = 30pt }"
     "\\begin{frame}{Title}Words.\\end{frame}"),
   ("an abstract's heading style", article "\\style{section}{ before = 30pt }"
     "\\begin{abstract}Words.\\end{abstract}"),
   ("link colours", article "\\usepackage{hyperref}\\hypersetup{colorlinks}"
     "\\href{https://example.org}{A place}."),
   ("a beamer block font", deck "\\setbeamerfont{block title}{size=\\tiny}"
     "\\begin{frame}{Title}\\begin{alertblock}{Alert}Words.\\end{alertblock}\\end{frame}"),
   ("listing defaults", article "\\usepackage{listings}\\lstset{numbers=left}"
     "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}"),
   ("a lexer's minted defaults", article "\\usepackage{minted}\\setminted[python]{linenos}"
     "\\begin{minted}{python}\nx = 1\n\\end{minted}"),
   ("inline-code defaults", article "\\usepackage{minted}\\setmintedinline{fontsize=\\small}"
     "Inline \\mintinline{python}{x = 1} code.")]

/-- Each kind of declaration nothing reads is named once at its site, keyed by what it declares;
one something reads is not. -/
def firesChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (what, src, subject) in unreadCases do
    let ds := unused src
    t s!"unused settings: {what} nothing reads is named once, keyed by it ({ds.map (·.subject)})"
      (ds.size == 1 && ds.all fun d => d.kind == .W0449 && d.subject == some subject)
    t s!"unused settings: {what} is named where it stands, as a warning with help"
      (ds.all fun d => d.span.any (·.pos.line == 2) && d.severity == .warning && d.help.isSome)
  for (what, src) in readCases do
    t s!"unused settings: {what} read by the document is not named ({(unused src).map (·.subject)})"
      (unused src).isEmpty
  let twice := unused (article (probeColor ++ "\n" ++ probeColor) "Words.")
  t "unused settings: a colour declared twice and never read is one loss at both sites"
    (((Diag.foldRepeats twice).filter (·.severity == .warning)).size == 1)
  let later := unused (article "\\usepackage{listings}"
    "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}\n\\lstset{numbers=left}\nWords.")
  t "unused settings: listing defaults after the last listing are named"
    (later.map (·.subject) == #[some "unused:listing:lstset"])
  let both := unused (article "\\definecolor{probeone}{HTML}{8A2BE2}\\definecolor{probetwo}{HTML}{2BE28A}"
    "\\textcolor{probetwo}{Words.}")
  t "unused settings: of two colours, the one nothing paints is the one named"
    (both.map (·.subject) == #[some "unused:color:probeone"])

/-- A declaration in a package, class or theme file is the file's, and one in a file the document
inputs is the document's; one a loading command lowers, or a definition's replacement text makes,
is not the document's either. -/
def scopeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let declared := "\n" ++ probeColor ++ "\n\\style{itemize}{ gap = 4pt }\n\\usepackage{listings}" ++
    "\\lstset{numbers=left}\n\\fonts{ mono = \"Probe Mono\" }\n"
  let spliced (cls child : String) : Ir.Doc × Array Diag × Elab.ReqSpans :=
    let raws := parse "root.tex" s!"\\documentclass\{{cls}}\n" ++
      #[Parse.Raw.env (Parse.inputEnv child) (parse child declared) {}] ++
      parse "root.tex" "\\begin{document}\nWords.\n\\end{document}"
    Elab.runRawsSpanned "root.tex" raws
  for (what, cls, child) in [("a package", "article", "probe.sty"),
      ("a class", "article", "probe.cls"), ("a local theme", "beamer", "beamerthemeprobe.sty")] do
    let (_, ds, spans) := spliced cls child
    t s!"unused settings: {what}'s unread declarations are its own, never named"
      (!ds.any (·.kind == .W0449) && spans.faces.isEmpty)
  let (_, ds, spans) := spliced "article" "part.tex"
  t s!"unused settings: an input file's unread declarations are the document's, named in it ({ds.filter (·.kind == .W0449) |>.map (·.subject)})"
    ((ds.filter (·.kind == .W0449)).size == 3 &&
      ds.all fun d => d.kind != .W0449 || d.span.any (·.file == "part.tex"))
  t "unused settings: an input file's face is judged with the face set"
    (spans.faces.map (·.1) == #["mono"] && spans.faces.all (·.2.file == "part.tex"))
  let loaders := [("a link-colour package option", article "\\usepackage[colorlinks]{hyperref}" "Words."),
    ("a font package", article "\\usepackage{courier}" "Words."),
    ("a shipped theme", deck "\\usetheme{moloch}" "\\begin{frame}Words.\\end{frame}")]
  for (what, src) in loaders do
    let (doc, ds, spans) := Elab.runRawsSpanned "t" (parse "t" src)
    t s!"unused settings: {what} declares nothing of the document's own"
      (!ds.any (·.kind == .W0449) && spans.faces.isEmpty && doc.body.size ≥ 1)
  t "unused settings: a colour a document's macro declares where it is called is the macro's"
    (unused (article ("\\newcommand{\\probesetup}{" ++ probeColor ++ "}") "\\probesetup Words.")).isEmpty

/-- `\allow{W0449}` accepts the loss as a note; a site another warning names keeps that one
accounting; a translated declaration's note stands beside the loss as its own fact. -/
def accountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (allowing, allowed) := elabStr (article (probeColor ++ "\\allow{W0449}") "Words.")
  let accepted := (allowed.filter (·.kind == .W0449)).map (Diag.accept allowing.allow false · |>.1)
  t "unused settings: \\allow{W0449} accepts the loss as a note"
    (accepted.size == 1 && accepted.all (·.severity == .note))
  let (_, ds) := elabStr (article "\\usepackage{enumitem}\\setlist{nosep}" "Words.")
  t "unused settings: a declaration already named unread keeps that one accounting"
    (ds.any (·.kind == .W0104) && !ds.any (·.kind == .W0449))
  let (_, ds) := elabStr (article probeColor "Words.")
  t "unused settings: the translation's note and the loss stand at one site"
    (ds.any (·.kind == .N0100) && ds.any (·.kind == .W0449) &&
      (ds.filter fun d => d.kind == .N0100 || d.kind == .W0449).all fun d =>
        d.span.any (·.pos.line == 2))

/-- A markdown document's metadata keys only a citation reads are named where the document cites
nothing, each at its field; a citation, a `nocite` or an included file's role reads them. -/
def metadataChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let front := "---\nbibliography: refs.bib\nbiblio-style: plainnat\nreference-section-title: Works\n---\n\n"
  let named (src : String) : Array (Option String) :=
    ((elabMd src).2.filter (·.kind == .W0449)).map (·.subject)
  let uncited := (elabMd (front ++ "# A note\n\nPlain words, citing nothing.\n")).2.filter
    (·.kind == .W0449)
  t s!"unused metadata: a document citing nothing names each citation key it declares ({uncited.map (·.subject)})"
    (uncited.map (·.subject) == #[some "unused:meta:bibliography", some "unused:meta:biblio-style",
      some "unused:meta:reference-section-title"])
  t "unused metadata: each is named at its own field"
    (uncited.map (·.span.map (·.pos.line)) == #[some 2, some 3, some 4])
  t "unused metadata: a citation reads them"
    (named (front ++ "A claim [@roe2020].\n")).isEmpty
  t "unused metadata: a nocite reads them"
    (named ("---\nbibliography: refs.bib\nnocite: '@roe2020'\n---\n\nPlain words.\n")).isEmpty
  t "unused metadata: a document with no metadata names nothing"
    (named "# A note\n\nPlain words.\n").isEmpty
  let (_, included) := Md.readIncluded "part.md" (front ++ "Plain words.\n") false
  t "unused metadata: an included file's keys are the including document's to judge"
    (!included.any (·.kind == .W0449))
  t "unused metadata: a key already named keeps that one accounting"
    ((named ("---\nbibliography: refs.bib\nlink-citations: false\n---\n\nPlain words.\n")) ==
      #[some "unused:meta:bibliography"])

/-- Each tag and class a typed HTML tree holds, a class written `.name`, with the most of it one
path from the root nests. -/
def presentOne (path : List String) (acc : Array (String × Nat)) : Html.Node → Array (String × Nat)
  | .elem tag attrs kids =>
    let classes := ((((attrs.find? (·.1 == "class")).map (·.2)).getD "").splitOn " ").filter
      (!·.isEmpty) |>.map ("." ++ ·)
    let path := tag :: path
    let acc := (tag :: classes).foldl (fun a n =>
      let depth := path.count n + (if classes.contains n then 1 else 0)
      match a.findIdx? (·.1 == n) with
      | some i => a.modify i fun (k, d) => (k, max d depth)
      | none => a.push (n, depth)) acc
    kids.attach.foldl (fun a ⟨k, _⟩ => presentOne path a k) acc
  | .text _ | .style _ | .script _ _ => acc
termination_by n => sizeOf n
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹_ ∈ kids›
  simp_wf
  omega

/-- The tags and classes a selector's compounds name, pseudo-classes and their arguments aside. -/
def selectorNames (sel : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  let mut pseudo := false
  for c in sel.toList ++ [' '] do
    if c == '(' then
      depth := depth + 1
    else if c == ')' then
      depth := depth - 1
    else if depth > 0 then
      pure ()
    else if c.isAlphanum || c == '-' || c == '_' then
      cur := cur.push c
    else
      if !cur.isEmpty && !pseudo then out := out.push cur
      cur := if c == '.' then "." else ""
      pseudo := c == ':' || (pseudo && c == ':')
      if c == '.' then pseudo := false
  return out.filter (· != ".")

/-- Whether some selector of a rule's prelude names only what the page holds, a tag a descendant
chain repeats nested as often on the page. -/
def liveSelector (present : Array (String × Nat)) (prelude : String) : Bool :=
  (prelude.splitOn ",").any fun sel =>
    let names := selectorNames sel.trimAscii.toString
    names.all fun n => ["html", "body", "root"].contains n ||
      present.any fun (k, d) => k == n && d ≥ names.count n

/-- Style text without the font faces and the rules no element of the page answers. -/
def liveRules (present : Array (String × Nat)) (css : String) : String := Id.run do
  let mut out := ""
  let mut prelude := ""
  let mut leaf := ""
  let mut keep := false
  let mut depth := 0
  for c in css.toList do
    if depth > 0 then
      leaf := leaf.push c
      if c == '{' then depth := depth + 1
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then
          if keep then out := out ++ leaf
          leaf := ""
    else if c == '{' then
      let sel := prelude.trimAscii.toString
      if sel.startsWith "@media" || sel.startsWith "@supports" || sel.startsWith "@layer" then
        out := out ++ prelude ++ "{"
      else
        keep := !sel.startsWith "@font-face" &&
          (sel.startsWith "@" || liveSelector present sel)
        leaf := prelude ++ "{"
        depth := 1
      prelude := ""
    else if c == '}' || c == ';' then
      out := (out ++ prelude).push c
      prelude := ""
    else prelude := prelude.push c
  return out ++ prelude

/-- A source's artifacts as a reader meets them: the PDF's bytes, the web page's body and head
without what nothing on it reads, the markdown twin, and the diagnostics. -/
structure Seen where
  pdf : ByteArray
  page : String
  css : String
  md : String
  diags : Array Diag

def seen (fonts : Font.FontSet) (src : String) : Seen :=
  let (doc, ds) := bibBuild src #[("refs", ParamCensus.refsBib), ("refs.bib", ParamCensus.refsBib)]
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  let present := tree.foldl (presentOne []) #[]
  let styles := String.join (head.toList.filterMap fun | .style c => some c | _ => none)
  let live := liveRules present styles
  let page := Html.render (Html.elem "div" (ParamCensus.plainNodes #[] tree.toList)) 0 ++
    Html.render (Html.elem "head" (head.filter fun | .style _ => false | _ => true)) 0
  let markup := Html.render (Html.elem "div" tree) 0
  -- A property only an unread property reads is unread too.
  let css := (List.range 4).foldl (fun css _ =>
    ParamCensus.dropUnreadIn (ParamCensus.readProps (css ++ markup)) css) live
  { pdf := driverPdf fonts (Layout.Geom.ofPage doc.page) doc out, page, css
    md := MarkdownDoc.emit doc, diags := ds ++ out.diags ++ hds }

/-- The documents the two-build judge varies a declaration in. -/
def judgedBodies : List (String × String) :=
  [("plain", "Plain words in a paragraph."),
   ("sections", "\\section{Opening}Words.\\subsection{Second}More words."),
   ("lists", "\\begin{itemize}\\item Alpha\\begin{itemize}\\item Beta\\end{itemize}\\end{itemize}" ++
     "\\begin{enumerate}\\item One\\begin{enumerate}\\item Two\\end{enumerate}\\end{enumerate}"),
   ("an algorithm", "\\begin{algorithmic}[1]\\State alpha\\If{beta}\\State gamma\\EndIf\\end{algorithmic}"),
   ("a note", "Words\\footnote{Note words.} here."),
   ("an abstract and a title", "\\maketitle\\begin{abstract}Abstract words.\\end{abstract}Body."),
   ("links and a citation", "\\section{A}\\label{s:a}See Section~\\ref{s:a}, " ++
     "\\href{https://example.org}{a place} and \\cite{key1}.\\bibliographystyle{plainnat}\\bibliography{refs}"),
   ("listings", "\\begin{lstlisting}\nx = 1\n\\end{lstlisting}\\begin{minted}{python}\ny = 2\n" ++
     "\\end{minted}Inline \\mintinline{bash}{echo z} code."),
   ("colour", "\\textcolor{probeink}{Coloured words.}")]

/-- The declarations the two-build judge varies, one at a time. -/
def judgedDecls : List String :=
  [probeColor, "\\colorlet{probeink}{red!40}", "\\palette{ probeink = #8A2BE2 }",
   "\\style{section}{ before = 30pt }", "\\style{subsection}{ before = 30pt }",
   "\\style{itemize}{ indent = 4em }", "\\style{enumerate}{ indent = 4em }",
   "\\style{itemize2}{ indent = 4em }", "\\style{abstract}{ font = {\\Large} }",
   "\\style{titlepage}{ font = {\\Huge} }", "\\style{cite}{ color = red }",
   "\\setlist[enumerate,2]{leftmargin=4em}", "\\hypersetup{colorlinks, linkcolor=red}",
   "\\lstset{numbers=left}", "\\setminted{linenos}", "\\setminted[python]{linenos}",
   "\\setmintedinline{fontsize=\\small}"]

/-- The two-build judge: wherever W0449 names a declaration, the document without it ships the same
PDF bytes, web page and markdown twin. -/
def oracleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let pre := "\\title{Probe title}\\author{Probe author}\\usepackage{listings}\\usepackage{minted}" ++
    "\\usepackage{algpseudocode}\\usepackage{hyperref}\\usepackage{natbib}\\usepackage{enumitem}"
  let tasks := judgedBodies.map fun (what, body) =>
    let base := Task.spawn fun _ => seen fonts (article pre body)
    (what, judgedDecls.map fun decl => (decl, base.bind fun b => Task.spawn fun _ =>
      let w := seen fonts (article (pre ++ "\n" ++ decl) body)
      let named := w.diags.any fun (d : Diag) => d.kind == DiagCode.W0449 &&
        d.span.any fun (sp : Span) => sp.pos.line == 3
      let same := w.pdf == b.pdf && w.page == b.page && w.css == b.css && w.md == b.md
      (named, same)))
  let mut faults : Array String := #[]
  let mut named := 0
  for (what, row) in tasks do
    for (decl, task) in row do
      let (n, same) := task.get
      if n then named := named + 1
      if n && !same then faults := faults.push s!"{decl} in {what}"
  check ref s!"unused settings, two builds: a declaration named unused changes no artifact ({faults})"
    faults.isEmpty
  check ref s!"unused settings, two builds: the judge names declarations ({named})" (named ≥ 40)

/-- A declared face is judged over the settled face set: one no text is set in is named, one a run
or a fallback glyph reads is not. -/
def faceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FontAssembly.FaceScan := { faces := scanned, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let judge (cls fonts body : String) : IO (Option (Array Diag × ByteArray)) := do
    let src := s!"\\documentclass\{{cls}}\n\\fonts\{ {fonts} }\n\\begin\{document}\n{body}\n" ++
      "\\end{document}\n"
    let (doc, _, spans) := Elab.runRawsSpanned "t" (Parse.parse "t" (Lex.lex "t" src).1).1
    match ← FontAssembly.buildFontSet doc scan cache .settled with
    | .ok (fs, doc, _, _) =>
      let out := Layout.run (Layout.Geom.ofPage doc.page) fs none doc
      return some (FaceUse.diags spans.faces fs doc,
        driverPdf fs (Layout.Geom.ofPage doc.page) doc out)
    | .error _ => return none
  let keys (r : Option (Array Diag × ByteArray)) : Array String :=
    ((r.map (·.1)).getD #[]).filterMap (·.subject)
  let serif := "body = \"Source Serif Pro\""
  let monoOnly ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "Plain words."
  let without ← judge "article" serif "Plain words."
  t s!"unused faces: a typewriter face no code sets in is named ({keys monoOnly})"
    (keys monoOnly == #["unused:face:mono"])
  t "unused faces: the document without it ships the same PDF bytes"
    ((monoOnly.map (·.2)) == (without.map (·.2)) && monoOnly.isSome)
  let code ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "A \\texttt{code} run."
  t s!"unused faces: a typewriter face code sets in is not named ({keys code})" (keys code).isEmpty
  let fallback ← judge "article" (serif ++ ", mono = \"Source Code Pro\"") "A rule \u2500 drawn."
  t s!"unused faces: a face a glyph the text face lacks falls back to is not named ({keys fallback})"
    (keys fallback).isEmpty
  let math ← judge "article" (serif ++ ", math = \"Fira Math\"") "Plain words."
  t s!"unused faces: a math face no formula sets in is named ({keys math})"
    (keys math == #["unused:face:math"])
  let formula ← judge "article" (serif ++ ", math = \"Fira Math\"") "A formula $x^2$."
  t s!"unused faces: a math face a formula sets in is not named ({keys formula})"
    (keys formula).isEmpty
  let sans ← judge "article" (serif ++ ", sans = \"Open Sans\"") "Plain words."
  t s!"unused faces: a sans face no text sets in is named ({keys sans})"
    (keys sans == #["unused:face:sans"])
  let headed ← judge "article" (serif ++ ", sans = \"Open Sans\"") "\\section{Opening}Words."
  t s!"unused faces: a sans face the web page's headings set in is not named ({keys headed})"
    (keys headed).isEmpty
  let deckFaces := serif ++ ", sans = \"Open Sans\", mono = \"Source Code Pro\""
  let deckBody := "\\begin{frame}{Title}Words.\\end{frame}"
  let slides ← judge "slides" deckFaces deckBody
  t s!"unused faces: a deck's body face its sans text never reads is named ({keys slides})"
    (keys slides == #["unused:face:body", "unused:face:mono"])
  let companion ← judge "slides" deckFaces "\\begin{frame}{Title}A formula $x^2$.\\end{frame}"
  t s!"unused faces: a deck's body face whose companion sets its math is not named ({keys companion})"
    (!(keys companion).contains "unused:face:body")

end Tests.UnusedSettings
