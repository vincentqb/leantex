module

public import LeanTex.Core.Font
public import LeanTex.Core.Elab
public import LeanTex.Core.Layout
public import LeanTex.Core.HtmlDoc
public import Tests.Support

public section

open LeanTex.Core

namespace Tests.GroupScope

/-- The fill colour of every body glyph run carrying `marker`, when they
all agree: what the page shows the word in. -/
private def pdfInk (out : Layout.Out) (marker : String) : Option Ir.Color :=
  let colors := out.pages.flatMap (·.lines) |>.filter (! ·.furniture) |>.flatMap fun line =>
    line.segs.filterMap fun seg => match seg with
      | .run _ color .. =>
        if hasStr (String.ofList seg.glyphChars) marker then some color else none
      | _ => none
  match colors[0]? with
  | some c => if colors.all (· == c) then some c else none
  | none => none

/-- The ground the layout painted on page `i`: its first fill, when that
fill covers the medium (`Layout.Geom.ground`). -/
private def pdfGround (doc : Ir.Doc) (out : Layout.Out) (i : Nat) : Option Ir.Color :=
  let geom := Layout.Geom.ofPage doc.page
  out.pages[i]?.bind fun page => page.fills[0]?.bind fun fill =>
    if fill.x == -geom.bleed && fill.y == -geom.bleed &&
        fill.w == geom.pageW + 2 * geom.bleed &&
        fill.h == geom.pageH + 2 * geom.bleed then some fill.color else none

/-- Every body line's text and position: what a colour-only edit must leave
alone. -/
private def linePlaces (out : Layout.Out) : Array (String × Dim.Sp × Dim.Sp) :=
  out.pages.flatMap (·.lines) |>.filter (! ·.furniture) |>.map fun l => (lineText l, l.x, l.y)

private def declarations (style : String) : List (String × String) :=
  (style.splitOn ";").filterMap fun decl =>
    match decl.splitOn ":" with
    | key :: value :: more =>
      some (key.trimAscii.toString, (String.intercalate ":" (value :: more)).trimAscii.toString)
    | _ => none

/-- The shipped stylesheet's top-level rules, selector and declarations, in
order: a rule inside an at-rule (the dark scheme, print) is not one. -/
private def topRules (head : Array Html.Node) : List (String × List (String × String)) :=
  head.toList.flatMap fun node => match node with
    | .style css => (css.splitOn "}").filterMap fun chunk =>
        match chunk.splitOn "{" with
        | [sel, body] => some (sel.trimAscii.toString, declarations body)
        | _ => none
    | _ => []

private def rootVariables (head : Array Html.Node) : List (String × String) :=
  (topRules head).foldl (fun vars (sel, decls) =>
    if sel == ":root" then decls.foldl (fun vars (k, v) =>
      if k.startsWith "--" then (k, v) :: vars else vars) vars
    else vars) []

/-- The colour the shipped stylesheet gives `<body>`: the last top-level
`body` rule's that declares one. -/
private def bodyColor (head : Array Html.Node) : String :=
  (topRules head).foldl (fun acc (sel, decls) =>
    if sel != "body" then acc
    else match (decls.filter (·.1 == "color")).getLast? with
      | some (_, v) => v
      | none => acc) ""

/-- One `var(--name, fallback)` read against the custom properties in force. -/
private def varStep (vars : List (String × String)) (value : String) : String :=
  if value.startsWith "var(" && value.endsWith ")" then
    let inner := ((value.drop 4).dropEnd 1).toString
    match inner.splitOn "," with
    | k :: rest =>
      (vars.lookup k.trimAscii.toString).getD (String.intercalate "," rest).trimAscii.toString
    | [] => value
  else value

/-- The stylesheet nests one fallback (`var(--fg, var(--ink))`) and its
root properties are colours, so two reads reach the paint. -/
private def resolveVar (vars : List (String × String)) (value : String) : String :=
  varStep vars (varStep vars value)

private structure Leaf where
  text : String
  color : String
  lang : Option String
  classes : String
  tags : String

/-- The stylesheet's colour rule for an element under `<body>`: a deck's
stage reads `stageInk`; an inline `color` wins where an element declares
one. -/
private def ruleColor (tag : String) (classes : String) : Option String :=
  if tag == "section" && ((classes.splitOn " ").any fun c =>
      c == "slide" || c == "section-page") then some HtmlDoc.stageInk
  else none

mutual
  private def leavesList (vars : List (String × String)) (color : String)
      (lang : Option String) (classes tags : String) (out : Array Leaf) :
      List Html.Node → Array Leaf
    | [] => out
    | node :: rest =>
      leavesList vars color lang classes tags (leavesOne vars color lang classes tags out node) rest
  private def leavesOne (vars : List (String × String)) (color : String)
      (lang : Option String) (classes tags : String) (out : Array Leaf) :
      Html.Node → Array Leaf
    | .text text => out.push { text := text.trimAscii.toString, color, lang, classes, tags }
    | .elem tag attrs kids =>
      let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
      let decls := declarations style
      let vars := decls.foldl (fun vars (k, v) =>
        if k.startsWith "--" then (k, v) :: vars else vars) vars
      let own := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
      let color := match (decls.filter (·.1 == "color")).getLast? with
        | some (_, v) => resolveVar vars v
        | none => match ruleColor tag own with
          | some v => resolveVar vars v
          | none => color
      let lang := ((attrs.find? (·.1 == "lang")).map (·.2)).or lang
      leavesList vars color lang (classes ++ " " ++ own) (tags ++ " " ++ tag) out kids.toList
    | .style _ | .script .. => out
end

/-- Every text leaf of the typed tree with the paint the shipped stylesheet
gives it, the walk starting from `<body>`'s own colour — and that colour,
what a word with no colour of its own reads in. -/
private def leavesOf (doc : Ir.Doc) (fonts : Font.FontSet) : Array Leaf × String :=
  let (head, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
  let vars := rootVariables head
  let body := resolveVar vars (bodyColor head)
  (leavesList vars body none "" "" #[] nodes.toList, body)

/-- The paint the typed HTML tree gives the text leaf carrying `marker`;
`none` when the leaf is absent or repeated. -/
private def htmlInk (leaves : Array Leaf) (marker : String) : Option String :=
  match leaves.filter (hasStr ·.text marker) with
  | #[leaf] => some leaf.color
  | _ => none

private def htmlLeaf (leaves : Array Leaf) (marker : String) : Option Leaf :=
  match leaves.filter (hasStr ·.text marker) with
  | #[leaf] => some leaf
  | _ => none

mutual
  /-- Every element but an inline span, with its class, in document order:
  the block structure and roles a colour declaration must leave alone. -/
  private def blockShape (out : Array (String × String)) : Html.Node → Array (String × String)
    | .elem tag attrs kids =>
      let out := if tag == "span" then out
        else out.push (tag, ((attrs.find? (·.1 == "class")).map (·.2)).getD "")
      blockShapeList out kids.toList
    | _ => out
  private def blockShapeList (out : Array (String × String)) :
      List Html.Node → Array (String × String)
    | [] => out
    | n :: rest => blockShapeList (blockShape out n) rest
end

private def shapeOf (doc : Ir.Doc) (fonts : Font.FontSet) : Array (String × String) :=
  let (_, nodes, _) := HtmlDoc.emitTree { fonts := some fonts } doc
  blockShapeList #[] nodes.toList

mutual
  /-- The longest `style` attribute and the deepest element nesting in a
  typed tree: what an epoch-heavy flow must keep bounded. -/
  private def treeMeasure (depth : Nat) (acc : Nat × Nat) : Html.Node → Nat × Nat
    | .elem _ attrs kids =>
      let style := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
      treeMeasureList (depth + 1) (max acc.1 style.length, max acc.2 (depth + 1)) kids.toList
    | _ => acc
  private def treeMeasureList (depth : Nat) (acc : Nat × Nat) : List Html.Node → Nat × Nat
    | [] => acc
    | n :: rest => treeMeasureList depth (treeMeasure depth acc n) rest
end

/-- One probe: an invented document, and the ink each marker word ships in.
`none` asks for the document's own ink — what the same word reads in with
no colour declared at all. `htmlOwed` names the markers whose HTML paint is
pending, each with the colour its group set, which it must have left: an
inline `\normalcolor` ships the IR's concrete normal ink, where the page's
own text reads the stylesheet's. -/
private structure Probe where
  name : String
  source : String
  inks : List (String × Option Ir.Color)
  htmlOwed : List (String × Ir.Color) := []

private def blue : Ir.Color := { r := 0, g := 0, b := 255 }
private def wine : Ir.Color := { r := 128, g := 0, b := 0 }
private def white : Ir.Color := { r := 255, g := 255, b := 255 }
private def navy : Ir.Color := { r := 0, g := 64, b := 128 }
private def probeInk : Ir.Color := { r := 0x7A, g := 0x1F, b := 0x1F }

private def bracePageSource : String :=
  dvDoc "\\usepackage{xcolor}\n"
    "{\\pagecolor{black}\\color{white}\nCover.\n\nMore.\\par}\n\\clearpage\n\\nopagecolor\nBody."

private def titleSource : String :=
  dvDoc "\\usepackage{xcolor}\n"
    ("\\begin{titlepage}\n\\pagecolor{black}\n\\color{white}\nCover words\n" ++
      "\\end{titlepage}\n\\nopagecolor\n\\clearpage\nBody words after.\n\n" ++
      "\\begin{itemize}\\item Listed item\\end{itemize}")

/-- The probes, each measured under lualatex: `\current@color` logged at
every marker, and the fill colour at every text operator of the uncompressed
PDF, read the colour the group's start held after `\end{...}`, `}`,
`\endgroup`, `\egroup` and a column's end — a `\color` reaches the end of
its group and no further, through paragraph ends and list items alike
(neither a `\par` nor an `\item` closes a group) — and `\normalcolor` reads
the colour in force at `\begin{document}`, a preamble `\color` included.
Beamer paints `normal text` where `\usebeamercolor` uses it, so its probe
says so. -/
private def probes : List Probe := [
  { name := "title page"
    source := titleSource
    inks := [("Cover", some white), ("Body", none), ("Listed", none)] },
  { name := "brace group across a paragraph end"
    source := dvDoc "\\usepackage{xcolor}\n" "{\\color{blue} Alpha\\par Beta} Gamma"
    inks := [("Alpha", some blue), ("Beta", some blue), ("Gamma", none)] },
  { name := "environment"
    source := dvDoc "\\usepackage{xcolor}\n"
      "\\begin{center}\\color{blue} Delta\\end{center}\nEpsilon"
    inks := [("Delta", some blue), ("Epsilon", none)] },
  { name := "list items share the list's group"
    source := dvDoc "\\usepackage{xcolor}\n"
      "\\begin{itemize}\\item \\color{blue} Zeta \\item Eta\\end{itemize}\nTheta"
    inks := [("Zeta", some blue), ("Eta", some blue), ("Theta", none)] },
  { name := "begingroup and endgroup"
    source := dvDoc "\\usepackage{xcolor}\n" "\\begingroup\\color{blue} Iota\\par Kappa\\endgroup\nLambda"
    inks := [("Iota", some blue), ("Kappa", some blue), ("Lambda", none)] },
  { name := "bgroup and egroup"
    source := dvDoc "\\usepackage{xcolor}\n" "\\bgroup\\color{blue} Mu\\par Nu\\egroup\nXi"
    inks := [("Mu", some blue), ("Nu", some blue), ("Xi", none)] },
  { name := "a group restores the enclosing colour"
    source := dvDoc "\\usepackage{xcolor}\n"
      "\\color{blue}Omicron\n\n\\begin{quote}\\color[HTML]{800000}Pi\\end{quote}\nRho"
    inks := [("Omicron", some blue), ("Pi", some wine), ("Rho", some blue)] },
  { name := "normalcolor"
    source := dvDoc "\\usepackage{xcolor}\n"
      "{\\color{blue} Sigma \\normalcolor Tau}\n\n\\color{blue}Upsilon\n\n\\normalcolor Phi"
    inks := [("Sigma", some blue), ("Tau", none), ("Upsilon", some blue), ("Phi", none)]
    htmlOwed := [("Tau", blue)] },
  { name := "normalcolor reads a preamble colour"
    source := dvDoc "\\usepackage{xcolor}\n\\color{blue}\n"
      "{\\color[HTML]{800000} Leto \\normalcolor Maia}\n\n\\color[HTML]{800000}Nyx\n\n\\normalcolor Orion"
    inks := [("Leto", some wine), ("Maia", some blue), ("Nyx", some wine), ("Orion", some blue)] },
  { name := "a paragraph end closes no group"
    source := dvDoc "\\usepackage{xcolor}\n"
      "\\begin{minipage}{5cm} Omega \\color{blue} Ares\\par Bia\\end{minipage}\n\nCrius"
    inks := [("Omega", none), ("Ares", some blue), ("Bia", some blue), ("Crius", none)] },
  { name := "a colour declared in an item's text reaches the next item"
    source := dvDoc "\\usepackage{xcolor}\n"
      "\\begin{itemize}\\item Kea \\color{blue} Lato\\item Melos\\end{itemize}\nNaxos"
    inks := [("Kea", none), ("Lato", some blue), ("Melos", some blue), ("Naxos", none)] },
  { name := "columns are groups"
    source := dvDoc "\\usepackage{xcolor}\n"
      ("\\begin{minipage}{.4\\textwidth}\\color[HTML]{800000} Hecate\\end{minipage}\\hfill" ++
        "\\begin{minipage}{.4\\textwidth} Iris \\begin{center}\\color{blue} Janus\\end{center} " ++
        "Kronos\\end{minipage}")
    inks := [("Hecate", some wine), ("Iris", none), ("Janus", some blue), ("Kronos", none)] },
  { name := "a later colour wins over a palette name before it"
    source := dvDoc "\\palette{probeink=#7A1F1F}\n"
      "Alpha \\probeink Pallas.\n\nRhea.\n\n\\color{blue} Selene.\n\nTethys."
    inks := [("Alpha", none), ("Pallas", some probeInk), ("Rhea", some probeInk),
      ("Selene", some blue), ("Tethys", some blue)] },
  { name := "a colour outlives a declaration that ends its paragraph"
    source := dvDoc "\\usepackage{xcolor}\n"
      "Ceos \\color{blue} Dione \\palette{probeink=#800080} Eos\n\nGaia"
    inks := [("Ceos", none), ("Dione", some blue), ("Eos", some blue), ("Gaia", some blue)] },
  { name := "a body palette keeps its flow scope"
    source := dvDoc "" "\\begin{center}\\palette{fg=#004080}\\end{center}\nChi"
    inks := [("Chi", some navy)] },
  { name := "a colour before a group that restores its lengths"
    source := dvDoc "\\usepackage{xcolor}\n"
      "Aaa \\color{blue} Bbb {\\setlength{\\tabcolsep}{2pt}Ccc\\par Ddd} Eee.\n\nFff."
    inks := [("Aaa", none), ("Bbb", some blue), ("Ccc", some blue), ("Ddd", some blue),
      ("Eee", some blue), ("Fff", some blue)] },
  { name := "a group after a colour is its content, not its argument"
    source := dvDoc "\\usepackage{xcolor}\n" "Aaa \\color{blue}{\\bfseries Bbb} Ccc.\n\nDdd."
    inks := [("Aaa", none), ("Bbb", some blue), ("Ccc", some blue), ("Ddd", some blue)] },
  { name := "a page colour inside braces"
    source := bracePageSource
    inks := [("Cover", some white), ("More", some white), ("Body", none)] },
  { name := "frames"
    source := "\\documentclass{beamer}\n\\usepackage{xcolor}\n\\begin{document}\n" ++
      "\\begin{frame}\\color{blue} One\\end{frame}\n\\begin{frame}Two\\end{frame}\n" ++
      "\\end{document}"
    inks := [("One", some blue), ("Two", none)] },
  { name := "beamer colours inside a frame"
    source := "\\documentclass{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}\\setbeamercolor{normal text}{fg=blue}\\usebeamercolor[fg]{normal text}" ++
      " Three\\end{frame}\n\\begin{frame}Four\\end{frame}\n\\end{document}"
    inks := [("Three", some blue), ("Four", none)] }
]

/-- Pairs of invented documents differing by colour declarations alone: the
lualatex pages place every line alike, so both artifacts must too. -/
private def colourOnly : List (String × String × String) :=
  let pre := "\\usepackage{xcolor}\n\\usepackage{amsthm}\n"
  [("a display after a paragraph's colour",
     dvDoc pre "Alpha \\color[HTML]{800000} Beta\n\\[x=y\\]\nGamma",
     dvDoc pre "Alpha Beta\n\\[x=y\\]\nGamma"),
   ("a list opened in a paragraph after its colour",
     dvDoc pre "Alpha \\color[HTML]{800000} Beta\n\\begin{itemize}\\item Gamma\\item Delta\\end{itemize}",
     dvDoc pre "Alpha Beta\n\\begin{itemize}\\item Gamma\\item Delta\\end{itemize}"),
   ("a display after a list that coloured an item",
     dvDoc pre "\\begin{itemize}\\item \\color[HTML]{800000} Beta\\end{itemize}\n\\[x=y\\]\nGamma",
     dvDoc pre "\\begin{itemize}\\item Beta\\end{itemize}\n\\[x=y\\]\nGamma"),
   ("a display after a quote that coloured its text",
     dvDoc pre "\\begin{quote}\\color[HTML]{800000} Beta\\end{quote}\n\\[x=y\\]\nGamma",
     dvDoc pre "\\begin{quote}Beta\\end{quote}\n\\[x=y\\]\nGamma"),
   ("a proof's mark after its text's colour",
     dvDoc pre "\\begin{proof} Alpha \\color[HTML]{800000} Beta\\end{proof}\nGamma",
     dvDoc pre "\\begin{proof} Alpha Beta\\end{proof}\nGamma")]

/-- **A colour declared inside a group does not reach text after it**, in
either artifact: every marker's glyph runs in `Layout.Out` and its leaf in
the typed HTML tree carry the colour the lualatex measurement names, and a
colour declaration moves no line. -/
def groupScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  for p in probes do
    let (doc, ds) := Elab.run "group-scope.tex" p.source
    t s!"group scope/{p.name}: no errors" (ds.all (·.severity != .error))
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    let (leaves, bodyInk) := leavesOf doc fonts
    let normal := (Ir.Design.ofDoc doc).fg
    for (marker, ink) in p.inks do
      let want := ink.getD normal
      t s!"group scope/{p.name}: PDF {marker} in {want.css}" (pdfInk out marker == some want)
      match p.htmlOwed.lookup marker with
      | some left =>
        t s!"group scope/{p.name}: HTML {marker} left {left.css}"
          ((htmlInk leaves marker).any (· != left.css))
      | none =>
        let html := (ink.map (·.css)).getD bodyInk
        t s!"group scope/{p.name}: HTML {marker} in {html}" (htmlInk leaves marker == some html)
  for (name, coloured, plain) in colourOnly do
    let (cdoc, _) := Elab.run "group-scope.tex" coloured
    let (pdoc, _) := Elab.run "group-scope.tex" plain
    t s!"group scope/{name}: every line stands where it stands uncoloured"
      (linePlaces (Layout.run (Layout.Geom.ofPage cdoc.page) fonts none cdoc) ==
        linePlaces (Layout.run (Layout.Geom.ofPage pdoc.page) fonts none pdoc))
    t s!"group scope/{name}: every HTML block keeps its tag and classes"
      (shapeOf cdoc fonts == shapeOf pdoc fonts)
  -- `\pagecolor` is global (xcolor manual §2.6.4): the title page's ground
  -- reaches its page and `\nopagecolor` takes it back; a ground set inside
  -- an environment outlives the environment, as it does under lualatex.
  let (tdoc, _) := Elab.run "group-scope.tex" titleSource
  let tout := Layout.run (Layout.Geom.ofPage tdoc.page) fonts none tdoc
  let black : Ir.Color := { r := 0, g := 0, b := 0 }
  t "group scope/title page: its ground is black and the next page's is the document's"
    (tout.pages.size == 2 && pdfGround tdoc tout 0 == some black && pdfGround tdoc tout 1 == none)
  let (gdoc, _) := Elab.run "group-scope.tex"
    (dvDoc "\\usepackage{xcolor}\n" "\\begin{center}\\pagecolor{yellow}\\end{center}\nAegis\n\\clearpage\nBoreas")
  let gout := Layout.run (Layout.Geom.ofPage gdoc.page) fonts none gdoc
  let yellow : Ir.Color := { r := 255, g := 255, b := 0 }
  t "group scope/a page ground set inside an environment outlives it"
    (gout.pages.size == 2 && pdfGround gdoc gout 0 == some yellow &&
      pdfGround gdoc gout 1 == some yellow)
  -- The page ground is global wherever its declaration stands, a brace
  -- group or `\begingroup` included (lualatex: the braced title's page is
  -- black and the next white; `\begingroup\pagecolor{yellow}\endgroup`
  -- grounds both pages; a braced `\nopagecolor` clears the next page's).
  let grounds (src : String) : Array (Option Ir.Color) × Bool :=
    let (doc, ds) := Elab.run "group-scope.tex" src
    let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
    ((List.range out.pages.size).toArray.map (pdfGround doc out ·),
      ds.all (·.kind != .W0301))
  t "group scope/a page colour inside braces grounds its page alone, and names nothing unknown"
    (grounds bracePageSource == (#[some black, none], true))
  t "group scope/a page colour inside begingroup outlives the group"
    (grounds (dvDoc "\\usepackage{xcolor}\n"
      "\\begingroup\\pagecolor{yellow}\\endgroup\nAaa\n\\clearpage\nBbb") ==
      (#[some yellow, some yellow], true))
  t "group scope/a page colour reset inside braces outlives the braces"
    (grounds (dvDoc "\\usepackage{xcolor}\n"
      "\\pagecolor{yellow}\nAaa\n\\clearpage\n{\\nopagecolor}\nBbb") ==
      (#[some yellow, none], true))
  -- Small caps is its own axis since LaTeX 2020: `\scshape` after
  -- `\itshape` keeps the slant (lualatex: `scsl`, LMRomanCaps10-Oblique),
  -- through the paragraph end and not past the minipage.
  let (shdoc, _) := Elab.run "group-scope.tex"
    (dvDoc "" "\\begin{minipage}{5cm} Aaa \\itshape Bbb \\scshape Ccc\\par Ddd\\end{minipage}\n\nEee")
  let shleaves := (leavesOf shdoc fonts).1
  let shape (marker : String) : Option (Bool × Bool) := (htmlLeaf shleaves marker).map fun l =>
    ((l.tags.splitOn " ").contains "em", (l.classes.splitOn " ").contains "sc")
  t "group scope/small caps keeps the italic before it, to its group's end"
    (shape "Ddd" == some (true, true) && shape "Eee" == some (false, false))
  -- A `\selectlanguage` between blocks is local to its group too (babel:
  -- `\languagename` reads the outer language after `\end{center}`).
  let (ldoc, _) := Elab.run "group-scope.tex"
    (dvDoc "\\usepackage[french,english]{babel}\n"
      "\\begin{center}\\selectlanguage{french} Cyrene.\\end{center}\n\nDelphi")
  let lleaves := (leavesOf ldoc fonts).1
  t "group scope/a language switch inside an environment stays there"
    ((htmlLeaf lleaves "Cyrene").any (·.lang == some "fr") &&
      (htmlLeaf lleaves "Delphi").any (·.lang != some "fr"))
  -- url.sty's `\urlstyle` is a local face selector (lualatex sets a in
  -- roman, b mono, c and g sans, d mono, e roman, f mono: `\UrlFont` reads
  -- `\ttfamily` again after the group, and a paragraph end inside the group
  -- keeps the face).
  let (udoc, _) := Elab.run "group-scope.tex"
    (dvDoc "\\usepackage{url}\n"
      ("Lyre {\\urlstyle{rm}\\url{http://example.org/a}} and \\url{http://example.org/b}\n\n" ++
        "{\\urlstyle{sf}\\url{http://example.org/c}\\par \\url{http://example.org/g}} " ++
        "\\url{http://example.org/d}\n\n" ++
        "{\\urlstyle{rm}\\par\\url{http://example.org/e}}\\par \\url{http://example.org/f}"))
  let uleaves := (leavesOf udoc fonts).1
  let mono (url : String) : Bool :=
    (htmlLeaf uleaves url).any fun l => (l.tags.splitOn " ").contains "code"
  let shipped (url : String) : Bool := (htmlLeaf uleaves url).isSome
  t "group scope/a URL face chosen inside a group stays there"
    (["a", "b", "c", "g", "d", "e", "f"].all (shipped s!"example.org/{·}") &&
      !mono "example.org/a" && mono "example.org/b" && !mono "example.org/c" &&
      !mono "example.org/g" && mono "example.org/d" && !mono "example.org/e" &&
      mono "example.org/f")
  -- A size declared in a paragraph's own text holds to the end of its group
  -- (lualatex: `\f@size` is 14.4 after the paragraph end, 10 after the
  -- minipage).
  let (sdoc, _) := Elab.run "group-scope.tex"
    (dvDoc "" "\\begin{minipage}{5cm} Delos \\Large Ephyra\\par Gortyn\\end{minipage}\n\nHalos")
  let sc := censusOf (coveredColorsOf sdoc) (layoutOf fonts sdoc)
  t "group scope/a size declared in a paragraph's text reaches the rest of its group"
    (match lineSizeOf sc 0 "Ephyra", lineSizeOf sc 0 "Gortyn", lineSizeOf sc 0 "Halos" with
     | some big, some next, some after => next == big && after < big
     | _, _, _ => false)
  -- A palette name read with its argument colours the argument alone, so a
  -- paragraph end inside its group carries no declaration past it.
  let (adoc, _) := Elab.run "group-scope.tex"
    (dvDoc "\\palette{probeink=#7A1F1F}\n" "{\\probeink{Elis} Fano\\par Gela} Hydra")
  let aout := Layout.run (Layout.Geom.ofPage adoc.page) fonts none adoc
  let anormal := (Ir.Design.ofDoc adoc).fg
  t "group scope/a palette name with its argument colours the argument alone"
    (pdfInk aout "Elis" == some probeInk &&
      pdfInk aout "Gela" == some anormal && pdfInk aout "Hydra" == some anormal)
  -- A body `\palette` is global, so a frame's end replays it, and the named
  -- Beamer colour derived from its entry resolves again over the replay.
  let (bdoc, _) := Elab.run "group-scope.tex"
    ("\\documentclass{beamer}\n\\palette{ProbeMuted=#596674}\n" ++
      "\\setbeamercolor{alerted text}{fg=ProbeMuted}\n\\begin{document}\n" ++
      "\\begin{frame}\\color[HTML]{800000}\\palette{ProbeMuted=#123456} Ilion\\end{frame}\n" ++
      "\\begin{frame}Jolly \\textcolor{alert}{Knossos}\\end{frame}\n\\end{document}")
  let bout := Layout.run (Layout.Geom.ofPage bdoc.page) fonts none bdoc
  let replayed : Ir.Color := { r := 0x12, g := 0x34, b := 0x56 }
  t "group scope/a replayed palette entry resolves its Beamer colours again"
    (pdfInk bout "Knossos" == some replayed &&
      htmlInk (leavesOf bdoc fonts).1 "Knossos" == some replayed.css)
  -- An epoch-heavy flow keeps its typed tree bounded: an epoch restates what
  -- it changes, and a scope holds one declaration per axis, however many
  -- groups closed or paragraphs declared before.
  let many := String.join ((List.range 40).map fun i =>
    s!"\\begin\{center}\\color\{blue} Ring{i}\\end\{center}\nPara{i} \\small small\\normalsize " ++
      s!"\\fontsize\{11}\{13}\\selectfont sized \\em turned \\itshape slanted \\em back\n\n")
  let (mdoc, _) := Elab.run "group-scope.tex" (dvDoc "\\usepackage{xcolor}\n" many)
  let (_, mnodes, _) := HtmlDoc.emitTree { fonts := some fonts } mdoc
  let (longest, deepest) := treeMeasureList 0 (0, 0) mnodes.toList
  -- A colour epoch restates the ink and every role that follows it (the
  -- muted step, the list marker, the printed ink, the standout ground): a
  -- custom property resolves where it is declared, so a dependent declared
  -- at the root would keep the root's ink.
  t s!"group scope/forty closed groups keep every style short ({longest} characters)"
    (longest ≤ 200)
  t s!"group scope/forty carried sizes keep the tree shallow ({deepest} levels)"
    (deepest ≤ 12)

end Tests.GroupScope
