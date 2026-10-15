module

public import Tests.Support

public section

open LeanTex.Core

/-! leanblueprint's commands on an invented blueprint: its PDF sets none of them, as the package's
print macros set nothing, and its web page and twin set each statement's Lean names, linked through
its documentation's template, its status as marked, and its uses, proof and discussion. -/

namespace Tests.Blueprint

/-- The invented blueprint, its blueprint commands and declarations kept where `marked`. -/
def source (marked : Bool) (sites : String := "") (macros : String := "") : String :=
  let m (s : String) : String := if marked then s else ""
  "\\documentclass{article}\n\\usepackage{amsthm}\n" ++ m "\\usepackage{blueprint}\n" ++
  m sites ++ macros ++
  "\\newtheorem{theorem}{Theorem}\n\\newtheorem{lemma}[theorem]{Lemma}\n" ++
  "\\theoremstyle{definition}\n\\newtheorem{definition}[theorem]{Definition}\n" ++
  "\\begin{document}\n" ++
  "\\begin{definition}[Widget]\n  \\label{def:widget}\n" ++
  m "  \\lean{Example.Widget}\n  \\leanok\n" ++
  "  A widget is a pair of numbers, the first at most the second.\n\\end{definition}\n\n" ++
  "\\begin{lemma}\n  \\label{lem:double}\n" ++
  m "  \\lean{Example.Widget.double, Example.Widget.double_le}\n  \\leanok\n  \\uses{def:widget}\n" ++
  "  Doubling a widget gives a widget.\n\\end{lemma}\n\n" ++
  "\\begin{proof}\n" ++ m "  \\leanok\n  \\uses{def:widget}\n" ++
  "  Multiply both sides by two.\n\\end{proof}\n\n" ++
  "\\begin{theorem}\n  \\label{thm:main}\n" ++
  m "  \\lean{Example.main}\n  \\notready\n  \\uses{lem:double, def:widget}\n  \\discussion{12}\n" ++
  "  Every widget doubles twice.\n\\end{theorem}\n\n" ++
  "\\begin{proof}\n" ++ m "  \\proves{thm:main}\n  \\uses{lem:double}\n" ++
  "  Apply Lemma~\\ref{lem:double} twice.\n\\end{proof}\n\n" ++
  "\\begin{lemma}\n  \\label{lem:known}\n" ++ m "  \\lean{Nat.le_refl}\n  \\mathlibok\n" ++
  "  Every number is at most itself.\n\\end{lemma}\n" ++
  "\\end{document}\n"

/-- The sites the web version declares, and a colour for its graph. -/
def sites : String :=
  "\\github{https://github.com/example/widgets/}\n\\dochome{https://example.org/docs}\n" ++
  "\\graphcolor{proved}{green}{Green}\n"

/-- Print macros of the package's shape: the marks defined to set nothing, and `\uses` in expl3. -/
def printMacros : String :=
  "\\newcommand{\\lean}[1]{}\n\\newcommand{\\leanok}{}\n\\newcommand{\\notready}{}\n" ++
  "\\newcommand{\\mathlibok}{}\n\\newcommand{\\discussion}[1]{}\n\\newcommand{\\proves}[1]{}\n" ++
  "\\ExplSyntaxOn\n\\NewDocumentCommand\\uses{m}\n" ++
  "  {\\clist_map_inline:nn{#1}{\\phantom{\\ref{##1}}}\\ignorespaces}\n\\ExplSyntaxOff\n"

/-- The source of a page built with its locations, as a build lays it out. -/
def docOf (src : String) : Ir.Doc × Array Diag := elabLocated "t" src

/-- Every shipped line's text and place. -/
def placed (out : Layout.Out) : Array (String × Dim.Sp × Dim.Sp) :=
  (allLines out).map fun l => (lineText l, l.x, l.y)

mutual

/-- A node's text, its descendants' in order. -/
def nodeText (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .elem _ _ kids => nodesText acc kids.toList
  | _ => acc

def nodesText (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => nodesText (nodeText acc n) rest

end

mutual

/-- Every element with `tag`, in document order. -/
def elemsOne (tag : String) (acc : Array Html.Node) : Html.Node → Array Html.Node
  | n@(.elem t _ kids) => elemsList tag (if t == tag then acc.push n else acc) kids.toList
  | _ => acc

def elemsList (tag : String) (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => elemsList tag (elemsOne tag acc n) rest

end

def attrOf (n : Html.Node) (key : String) : Option String :=
  match n with
  | .elem _ attrs _ => attrs.findSome? fun (k, v) => if k == key then some v else none
  | _ => none

/-- Each link on a page: its target and its text. -/
def links (nodes : Array Html.Node) : Array (String × String) :=
  (elemsList "a" #[] nodes.toList).filterMap fun n =>
    (attrOf n "href").map fun h => (h, nodeText "" n)

/-- Each paragraph's text on a page. -/
def paragraphs (nodes : Array Html.Node) : Array String :=
  (elemsList "p" #[] nodes.toList).map (nodeText "")

def blueprintChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some face ← loadTestFont "SourceSerifPro-Regular.otf"
    | t "blueprint: the face loads" false
  let fs := oneFaceOf face
  let (marked, ds) := docOf (source true sites)
  let (linkless, _) := docOf (source true)
  let (bare, _) := docOf (source false)
  -- The PDF: the print macros set nothing, so every line ships as the blueprint without its marks.
  let shipped := placed (layoutOf fs marked)
  t "blueprint: the PDF ships every line of the unmarked blueprint, in place"
    (shipped == placed (layoutOf fs bare))
  t "blueprint: the PDF ships no Lean name, label, status or discussion"
    (shipped.all fun (s, _, _) =>
      !["Example.", "Nat.", "def:", "lem:", "thm:", "marked", "Lean:", "issue"].any (hasStr s ·))
  -- The web page: each statement's marks after its text, its names linked to the documentation.
  let html := docNodesOf marked
  let ps := paragraphs html
  let nb := "\u00a0"
  t "blueprint: a definition's name links to its documentation, and its status is the author's mark"
    (ps.contains "Lean: Example.Widget; marked formalized" &&
      (links html).contains ("https://example.org/docs/find/#doc/Example.Widget", "Example.Widget"))
  t "blueprint: a lemma's names each link, and its uses are cross-references set as headed"
    (ps.contains s!"Lean: Example.Widget.double, Example.Widget.double_le; marked formalized; uses Definition{nb}1" &&
      (links html).contains
        ("https://example.org/docs/find/#doc/Example.Widget.double_le", "Example.Widget.double_le") &&
      (links html).contains ("#def:widget", s!"Definition{nb}1"))
  t "blueprint: a proof's line marks the proof"
    (ps.contains s!"Marked formalized; uses Definition{nb}1")
  t "blueprint: a theorem not ready, its uses in order and its discussion linked to the repository's issue"
    (ps.contains s!"Lean: Example.main; marked not ready to formalize; uses Lemma{nb}2, Definition{nb}1; discussed in issue 12" &&
      (links html).contains ("https://github.com/example/widgets/issues/12", "issue 12"))
  t "blueprint: a proof elsewhere names the statement it proves"
    (ps.contains s!"Proves Theorem{nb}3; uses Lemma{nb}2")
  t "blueprint: a Mathlib mark subsumes the formalized one"
    (ps.contains "Lean: Nat.le_refl; marked in Mathlib")
  let names := ["Example.Widget", "Example.Widget.double", "Example.Widget.double_le",
    "Example.main", "Nat.le_refl"]
  let plain := docNodesOf linkless
  t "blueprint: without a documentation site the names are set unlinked"
    ((paragraphs plain).contains "Lean: Example.Widget; marked formalized" &&
      names.all fun n => !(links plain).any (·.2 == n))
  t "blueprint: a name is set as code, the whole of its link"
    ((elemsList "a" #[] html.toList).any fun a =>
      (elemsOne "code" #[] a).map (nodeText "") == #["Example.Widget"] &&
        nodeText "" a == "Example.Widget")
  -- The twin carries the web page's lines.
  let twin := MarkdownDoc.emit marked
  t "blueprint: the markdown twin carries each statement's line"
    (hasStr twin "marked formalized" && hasStr twin "(https://example.org/docs/find/#doc/Example.Widget)")
  -- The graph, named once over its sites.
  let graph := (Diag.foldRepeats ds).filter fun d => d.kind == .W0434 && d.severity.isWarning
  t "blueprint: the dependency graph is one named loss, over the load and each colour of it"
    (graph.size == 1 && (ds.filter (·.kind == .W0434)).size == 2)
  t "blueprint: no command is unknown"
    (ds.all fun d => d.kind != .W0301 && d.kind != .W0302 && d.severity != .error)
  -- A mark outside any statement or proof marks nothing, and is named.
  let (outside, ods) := docOf ("\\documentclass{article}\n\\usepackage{blueprint}\n" ++
    "\\begin{document}\nA claim \\lean{Example.Widget}\\leanok here.\n\\end{document}\n")
  t "blueprint: a mark outside a statement marks nothing and is named"
    (ods.any (·.kind == .W0387) && !(paragraphs (docNodesOf outside)).any (hasStr · "Lean"))
  -- Print macros of the package's shape: the document's definitions stand, and `\uses`, whose
  -- expl3 is skipped, sets its labels nowhere in the PDF.
  let (printed, _) := docOf (source false "" printMacros |>.replace "\\label{lem:double}\n"
    "\\label{lem:double}\n  \\lean{Example.Widget.double}\n  \\leanok\n  \\uses{def:widget}\n")
  t "blueprint: under print macros the PDF ships the unmarked lines"
    (placed (layoutOf fs printed) == placed (layoutOf fs bare))
  t "blueprint: under print macros a document's own empty definition of a mark stands"
    (!(paragraphs (docNodesOf printed)).any (hasStr · "Example.Widget.double") &&
      (paragraphs (docNodesOf printed)).contains s!"Uses Definition{nb}1")
  -- A statement's label carries its heading, which a headed reference sets.
  t "blueprint: a headed reference sets a statement's heading and number, else cleveref's name"
    (Ir.refText Locale.en .headed { kind := none, num := "2", heading := some "Lemma" } ==
        s!"Lemma{nb}2" &&
      Ir.refText Locale.en .headed { kind := some .heading, num := "1" } == s!"Section{nb}1" &&
      Ir.refText Locale.en .headed { kind := none, num := "4" } == "4")
  t "blueprint: a name's link fills the template's name as a Lean file's link fills it"
    (Blueprint.nameLink { dochome := some "https://example.org/docs/" } "Höhe.x'" ==
      some "https://example.org/docs/find/#doc/H%C3%B6he.x%27")

end Tests.Blueprint
