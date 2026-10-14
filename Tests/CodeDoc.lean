module

public import Tests.Support

public section

open LeanTex.Core

/-! The code-file reader, on invented words: documentation comments read as markdown and code as
listings, every source character in one segment and every code character shipped as written. -/

namespace Tests.CodeDoc

/-- The listings a document's body holds, in order: their language and their content. -/
def listings (doc : Ir.Doc) : Array (Option String × String) :=
  doc.body.filterMap fun b => match b with
    | .verbatim _ content spec => some (spec.langToken, content)
    | _ => none

/-- The listings a source assembles into, in page order. -/
def codePieces (lang : Ir.CodeLang) (src : String) : Array String :=
  (Code.assemble (Code.segmentsOf lang src)).filterMap fun p => (Code.Piece.code? p).map String.ofList

/-- The documentation comments a source assembles into, in page order. -/
def prosePieces (lang : Ir.CodeLang) (src : String) : Array String :=
  (Code.assemble (Code.segmentsOf lang src)).filterMap fun p =>
    (Code.Piece.prose? p).map (String.ofList ·.text)

/-- Whether a shipped line is set in the typewriter face alone, as a listing's lines are. -/
def monoLine (l : Layout.LineOut) : Bool :=
  let runs := lineRuns l
  !runs.isEmpty && runs.all (·.1 == 1)

/-- The lines a listing ships: its content's lines, an empty one as the one no-break space that
holds its height. -/
def shownLines (code : String) : Array String :=
  (Ir.verbatimLines ("\n" ++ code)).map fun l => if l.isEmpty then " " else l

/-- The text of every `pre` element an emitted body holds, in order. -/
def preTexts (doc : Ir.Doc) : Array String :=
  (elemNodesList (· == "pre") #[] (docNodesOf doc).toList).map fun n => match n with
    | .elem _ _ kids => nodeTextList "" kids.toList
    | .text _ | .style _ | .script .. => ""

/-- The prose a documentation comment reads as, from a comment at the start of line 1. -/
def proseOf (lang : Ir.CodeLang) (comment : String) : String :=
  (Code.proseIn lang comment.toList 1 0).text

/-- The text of every element of the emitted body whose tag is `tag`, in order. -/
def elemTexts (tag : String) (doc : Ir.Doc) : Array String :=
  (elemNodesList (· == tag) #[] (docNodesOf doc).toList).map fun n => match n with
    | .elem _ _ kids => nodeTextList "" kids.toList
    | .text _ | .style _ | .script .. => ""

/-- The targets of every link the emitted body holds, in order. -/
def hrefs (doc : Ir.Doc) : Array String :=
  (elemAttrsList (· == "a") #[] (docNodesOf doc).toList).filterMap fun (_, attrs) =>
    HtmlDoc.attrOf? attrs "href"

/-- Every source character in one segment, and every listing its code exactly, for one file. -/
def exactnessChecks (t : String → Bool → IO Unit) (name : String) (lang : Ir.CodeLang)
    (src : String) : IO Unit := do
  t s!"code {name}: the segments hold every source character once, in order"
    (String.ofList ((Code.segmentsOf lang src).flatMap (·.text)) == src)
  t s!"code {name}: each listing's content is its code exactly, in the language the extension names"
    (listings (elabCode s!"{name}" src).1 == (codePieces lang src).map fun c => (some lang.listing, "\n" ++ c))

def codeDocChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some text ← loadTestFont "OpenSans-Regular.ttf" | t "code files: the text face loads" false
  let some mono ← loadTestFont "SourceCodePro-Regular.otf" | t "code files: the mono face loads" false
  let fonts := slotPairOf 2 text mono
  for (n, lang) in codeGoldenNames do
    let src ← fixtureText (goldenFile n)
    exactnessChecks t s!"{n}.{lang.extension}" lang src
    let (doc, ds) := elabCode s!"{n}.{lang.extension}" src
    t s!"code {n}: the file reads with no diagnostic" ds.isEmpty
    let out := layoutOf fonts doc
    t s!"code {n}: every code line ships as written, in order"
      (((bodyLines out).filter monoLine).map lineInk == (codePieces lang src).flatMap shownLines)
    t s!"code {n}: every listing's HTML is its code's lines"
      (preTexts doc == (codePieces lang src).map fun c =>
        String.intercalate "\n" (Ir.verbatimLines ("\n" ++ c)).toList)
  for e in ← System.FilePath.readDir "testdata/codedoc/cases" do
    match Ir.Surface.ofPath e.fileName with
    | .code lang => exactnessChecks t e.fileName lang (← fixtureText e.path.toString)
    | .tex | .markdown => pure ()
  -- The title.
  let lean ← fixtureText (goldenFile "code-lean")
  let (leanDoc, _) := elabCode "code-lean.lean" lean
  t "code files: the first module doc's first heading is the document's title"
    (leanDoc.info.title == some "Tide tables" &&
      (match leanDoc.body[0]? with
       | some (Ir.Block.section .title _ _ _) => true
       | _ => false))
  let python ← fixtureText (goldenFile "code-python")
  let pyDoc := (elabCode "code-python.py" python).1
  t "code files: a module doc with no heading leaves the file's name as the title, its first heading"
    (pyDoc.info.title == some "code-python.py" &&
      (match pyDoc.body[0]? with
       | some (Ir.Block.section .title _ _ title) => Ir.plainText title == "code-python.py"
       | _ => false))
  t "code files: a file with no module doc takes its name as its title"
    ((elabCode "dir/plain.lean" "def x := 1\n").1.info.title == some "plain.lean")
  let late := "def a := 1\n/-! # Late -/\ndef b := 2\n"
  t "code files: a module doc after code stays where it stands and names no title"
    ((elabCode "t.lean" late).1.info.title == some "t.lean" &&
      prosePieces .lean late == #["/-! # Late -/"] &&
      codePieces .lean late == #["def a := 1\n", "def b := 2\n"])
  let scopedSrc := "module\npublic section\nnamespace Tide\n/-! # Tides -/\ndef x := 1\n"
  t "code files: a module doc after commands that declare nothing describes the file"
    ((elabCode "t.lean" scopedSrc).1.info.title == some "Tides" &&
      prosePieces .lean scopedSrc == #["/-! # Tides -/"] &&
      codePieces .lean scopedSrc == #["module\npublic section\nnamespace Tide\ndef x := 1\n"])
  t "code files: a module doc opening on a paragraph leaves the file's name as the title"
    ((elabCode "t.lean" "/-! Text first.\n\n# Later -/\ndef x := 1\n").1.info.title == some "t.lean")
  t "code files: a later module doc's heading stays a heading of the body"
    ((elabCode "t.lean" "/-! # First -/\ndef a := 1\n/-! # Second -/\ndef b := 2\n").1.body.filterMap
      (fun (b : Ir.Block) => match b with
        | .section level _ _ _ => some level
        | _ => none) == #[Ir.HeadingLevel.title, .h1])
  -- The directive.
  t "code files: the directive declares the output formats"
    (leanDoc.output.formats == #["pdf", "html"])
  let themed := (elabCode "t.py" "# leantex: theme = daylight\nx = 1\n").1
  let plain := (elabCode "t.py" "x = 1\n").1
  t "code files: the directive's theme installs as \\theme does" (themed.palette != plain.palette)
  t "code files: a directive after a #! line is read"
    ((elabCode "t.sh" "#!/bin/sh\n# leantex: formats = html\necho x\n").1.output.formats == #["html"])
  t "code files: a directive past the leading comments is a comment of the code"
    (let (d, ds) := elabCode "t.sh" "#!/bin/sh\necho x\n# leantex: formats = html\n"
     d.output.formats.isEmpty && !ds.any (·.kind == .W0387))
  let (strayDoc, strayDs) := elabCode "t.py"
    "#!/usr/bin/env python3\n# -*- coding: utf-8 -*-\n# leantex: formats = html\nx = 1\n"
  t "code files: a directive among the leading comments past its line is named once where it stands"
    (strayDoc.output.formats.isEmpty && (strayDs.filter (·.kind == .W0387)).size == 1 &&
      strayDs.any fun d => d.kind == .W0387 && d.span.map (·.pos.line) == some 3)
  t "code files: a directive key neither declaration takes is named by the declaration"
    ((elabCode "t.lean" "-- leantex: colour = blue\ndef x := 1\n").2.any (·.kind == .E0322))
  t "code files: the directive's entries cross to the declaration as written"
    (Code.outputSource? ["formats = pdf", "html", "md = \"a, b\""] ==
      some "formats = pdf, html, md = \"a, b\"" &&
     Code.outputSource? ["css = own"] == some "css = own")
  -- Where prose stands.
  t "code files: a Python docstring stands above its def, its header and body one listing"
    (prosePieces .python "def f():\n    \"\"\"Doc.\"\"\"\n    return 1\n" == #["\"\"\"Doc.\"\"\""] &&
      codePieces .python "def f():\n    \"\"\"Doc.\"\"\"\n    return 1\n" == #["def f():\n    return 1\n"])
  t "code files: a decorated class's docstring stands above its decorators"
    (codePieces .python "x = 1\n\n@dataclass\nclass A:\n    '''Doc.'''\n    y: int\n" ==
      #["x = 1\n", "@dataclass\nclass A:\n    y: int\n"])
  t "code files: a one-line def and a docstring that is not alone on its line stay in the code"
    (prosePieces .python "def f(): return 1\ndef g():\n    \"a\" \"b\"\n" == #[])
  t "code files: f-strings and bytes are no docstrings, and a string's quotes do not open one"
    (prosePieces .python "def f():\n    f\"x\"\ndef g():\n    b\"y\"\nz = 'def h():'\n" == #[])
  t "code files: an f-string's replacement field may hold the string's own quote"
    (prosePieces .python "s = f\"{d[\"k\"]}\"\ndef f():\n    \"\"\"Doc.\"\"\"\n" == #["\"\"\"Doc.\"\"\""])
  t "code files: a format spec's quotes are its text, and a field inside it closes"
    (prosePieces .python "s = f\"{w:'>{w}}|{'}':>3}\"\ndef f():\n    \"\"\"Doc.\"\"\"\n" ==
      #["\"\"\"Doc.\"\"\""])
  t "code files: Lean's strings, characters and comments hide what they hold"
    (prosePieces .lean
      "def a := \"/-- x -/\"\ndef c := '\"'\n/-- Doc. -/\ndef b := 'x'\n-- /-- not -/\n" ==
      #["/-- Doc. -/"])
  t "code files: a Lean block comment nests, and an indented docstring stays in the code"
    (prosePieces .lean "/- /- -/ /-- no -/ -/\nstructure S where\n  /-- field -/\n  x : Nat\n" == #[])
  t "code files: an interpolated string's quoted terms do not end it"
    (prosePieces .lean "def s := s!\"{\"-/\"}\"\n/-! # M -/\n" == #["/-! # M -/"])
  t "code files: the first module doc stands above the code before it, a later one in place"
    (prosePieces .lean "import A\n/-! # One -/\ndef x := 1\n/-! Two -/\n" == #["/-! # One -/", "/-! Two -/"] &&
      codePieces .lean "import A\n/-! # One -/\ndef x := 1\n/-! Two -/\n" == #["import A\ndef x := 1\n"])
  t "code files: a shell script's leading block stands above its #! line"
    (prosePieces .bash "#!/bin/sh\n\n# Desc.\n# More.\nset -e\n" == #["# Desc.\n# More."] &&
      codePieces .bash "#!/bin/sh\n\n# Desc.\n# More.\nset -e\n" == #["#!/bin/sh\nset -e\n"])
  -- What the prose reads as.
  t "code files: a docstring's prose is its text, the first line's spaces and the rest's margin gone"
    (proseOf .lean "/-- Doubles.\n    Twice over. -/" == "Doubles.\nTwice over." &&
      proseOf .lean "/-!\n# Title\n\nText.\n-/" == "# Title\n\nText.")
  t "code files: a Python docstring's escapes read as Python reads them, a raw one's do not"
    (proseOf .python "\"\"\"a\\x41 \\\\ b\\\nc\"\"\"" == "aA \\ bc" &&
      proseOf .python "r'''a\\tb'''" == "a\\tb")
  t "code files: a doctest at a docstring's margin reads as a code block, after prose or a blank line"
    (proseOf .python "\"\"\"Doubles.\n>>> double(2)\n4\n\nAfter.\"\"\"" ==
        "Doubles.\n\n    >>> double(2)\n    4\n\nAfter." &&
      (preTexts (elabCode "t.py" "def double(n):\n    \"\"\"Doubles.\n\n    >>> double(2)\n    4\n    \"\"\"\n").1).contains
        ">>> double(2)\n4")
  t "code files: an unterminated docstring keeps its last characters"
    (proseOf .python "\"\"\"Runs to the end" == "Runs to the end")
  t "code files: a shell comment block reads without its markers"
    (proseOf .bash "# One\n#\n#  Two" == "One\n\n Two" &&
      proseOf .bash "  # Usage:\n#   run -h" == "Usage:\n  run -h")
  -- The docstring dialect.
  let doctest := (elabCode "t.py" ("def double(n):\n    \"\"\"Doubles a count.\n\n    For example:\n\n" ++
    "        >>> double(2)\n        4\n    \"\"\"\n    return 2 * n\n")).1
  t "code files: an indented block in a docstring is a code block"
    ((preTexts doctest).contains ">>> double(2)\n4")
  let (lazy, lazyDs) := elabCode "t.lean" "/-- Two cases:\n- the first,\nstill the first\n- the second -/\ndef x := 1\n"
  t s!"code files: a docstring's lazy line continues its list item ({elemTexts "li" lazy})"
    (lazyDs.isEmpty && (elemTexts "li" lazy).size == 2 &&
      ((elemTexts "li" lazy)[0]?.map (·.contains "still the first")).getD false)
  let (ph, phDs) := elabCode "t.lean" "/-- Pass <name> here. -/\ndef x := 1\n"
  t s!"code files: an angle-bracketed word in a docstring is its text ({elemTexts "p" ph})"
    (phDs.isEmpty && (elemTexts "p" ph).any (·.contains "Pass <name> here."))
  t "code files: an autolink in a docstring is a link"
    ((hrefs (elabCode "t.lean" "/-- See <https://example.org>. -/\ndef x := 1\n").1).contains
      "https://example.org")
  -- A word opening on '<' is text after a list item's marker and after emphasis.
  let mdItem := (elabMd "- <3 or >5 items here.\n").1
  let docItem := (elabCode "t.lean" "/-- Cases:\n\n- <name>.pth files extend the path. -/\ndef x := 1\n").1
  t s!"code files: an item opening on '<' keeps the word, in both dialects ({elemTexts "li" mdItem}, {elemTexts "li" docItem})"
    ((elemTexts "li" mdItem).any (·.contains "<3 or >5") &&
      (elemTexts "li" docItem).any (·.contains "<name>.pth"))
  let mdEmph := (elabMd "See _a.b_<3 here.\n").1
  let docEmph := (elabCode "t.lean" "/-- See _a.b_<c>(x) here. -/\ndef x := 1\n").1
  t s!"code files: a word opening on '<' after emphasis keeps its text, in both dialects ({elemTexts "p" mdEmph}, {elemTexts "p" docEmph})"
    ((elemTexts "p" mdEmph).any (·.contains "<3 here") && (elemTexts "p" docEmph).any (·.contains "<c>(x)"))
  -- Positions.
  let (_, ruleDs) := elabCode "t.lean" "def x := 1\n\n/-! Above.\n\n---\n-/\n"
  t "code files: a markdown diagnostic in a doc comment names the source line it stands on"
    (ruleDs.any fun d => d.kind == .W0307 && d.span.map (·.pos.line) == some 5)

end Tests.CodeDoc
