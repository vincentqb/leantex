module

public import Tests.Support

public section

open LeanTex.Core

/-! The code-file reader, on invented words: documentation comments read as markdown and code as
listings, every source character in one segment and every code character shipped as written. -/

namespace Tests.CodeDoc

/-- The listings a source assembles into, in page order. -/
def codePieces (lang : Ir.CodeLang) (src : String) : Array String :=
  (Code.assemble (Code.segmentsOf lang src)).filterMap fun p => (Code.Piece.code? p).map String.ofList

/-- The documentation comments a source assembles into, in page order. -/
def prosePieces (lang : Ir.CodeLang) (src : String) : Array String :=
  (Code.assemble (Code.segmentsOf lang src)).filterMap fun p =>
    (Code.Piece.prose? p).map (String.ofList ·.text)

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
  for dir in ["testdata/codedoc/cases", "testdata/codedoc/langs"] do
    for e in ← System.FilePath.readDir dir do
      match Ir.Surface.ofPath e.fileName with
      | .code lang => exactnessChecks t e.fileName lang (← fixtureText e.path.toString)
      | .tex | .markdown => pure ()
  -- The rows.
  t "code files: every language's every extension selects it, and its listing is its own"
    (Ir.CodeLang.all.all fun l => l.row.extensions.all fun e =>
      Ir.Surface.ofInput? s!"dir/f.{e}" == some (.code l) && Ir.Surface.inputExtensions.contains e)
  t "code files: a language's directive is written in its line comment"
    ((elabCode "t.c" "// leantex: formats = html\nint x;\n").1.output.formats == #["html"] &&
      (elabCode "t.rs" "#![no_std]\n// leantex: formats = html\nfn f() {}\n").1.output.formats.isEmpty)
  let rust ← fixtureText "testdata/codedoc/langs/rust-docs.rs"
  t "code files: rustdoc's inner docs describe the file, its outer docs stand in place, its plain comments stay code"
    (prosePieces .rust rust == #["//! # Tide tables\n//!\n//! Invented tides, read as a page: inner docs describe the file.",
        "/// A reading in metres.\n///\n/// Its height is invented too.", "/// Writes the height.",
        "/** A block doc /* with a nested comment */ still the doc. */"] &&
      (elabCode "rust-docs.rs" rust).1.info.title == some "Tide tables" &&
      (codePieces .rust rust).any (·.startsWith "pub struct Reading {"))
  t "code files: a line doc's prose keeps its indented code, its markers and shared margin gone"
    (proseOf .rust "/// One\n///\n///     code" == "One\n\n    code" &&
      proseOf .rust "//!  Two\n//!  lines" == "Two\nlines")
  t "code files: a block doc's prose drops its stars and margin, and its closing spaces"
    (proseOf .java "/**\n * Adds.\n *\n *   kept\n */" == "Adds.\n\n  kept" &&
      proseOf .c "/** One line. */" == "One line.")
  let java ← fixtureText "testdata/codedoc/langs/java-docs.java"
  t "code files: Javadoc stands where it is written, indented too, and strings and plain comments hide nothing"
    ((prosePieces .java java).size == 3 &&
      (codePieces .java java).any (·.contains "/* A plain comment. */") &&
      (codePieces .java java).any (·.contains "\"/** not a doc */\""))
  t "code files: a doc form inside a plain block comment or C's `#if 0` stays code"
    (prosePieces .rust "/*\n/// x\nfn f() {}\n*/\nfn g() {}\n" == #[] &&
      prosePieces .rust "/*\n/** y */\n*/\nfn g() {}\n" == #[] &&
      prosePieces .c "#if 0\n/// x\n/** y */\n#endif\nint z;\n" == #[])
  t "code files: a doc right after a line comment, or after another doc, opens its own comment"
    (prosePieces .c "// x\n/// y\nint f();\n" == #["/// y"] &&
      prosePieces .c "int a; // t\n/// b\nint b;\n" == #["/// b"] &&
      prosePieces .cpp "// leantex: formats = html\n//! A shelf.\nclass S {};\n" == #["//! A shelf."] &&
      prosePieces .rust "//! m\n/// i\nfn f() {}\n" == #["//! m", "/// i"] &&
      prosePieces .rust "/// a\n/** b */\nfn f() {}\n" == #["/// a", "/** b */"] &&
      prosePieces .c "/** a /* b */\n/** c */\nint x;\n" == #["/** a /* b */", "/** c */"])
  t "code files: a block doc ends at its closer, nested ones balanced where the lexer nests them"
    (prosePieces .c "/** a */ int x;\n/** b /* c */\nint y;\n" == #["/** a */", "/** b /* c */"] &&
      prosePieces .rust "/** a /* b */ c */\nfn f() {}\n" == #["/** a /* b */ c */"])
  t "code files: a line doc's carriage returns and its text's tabs read as written, its margin's tabs as columns"
    (proseOf .rust "/// One\r\n///\r\n///     code" == "One\n\n    code" &&
      proseOf .rust "///\tTabbed\tinside" == "Tabbed\tinside" &&
      proseOf .java "/**\r\n * Adds.\r\n */" == "Adds.")
  let (strayC, strayCDs) := elabCode "t.c" "/* An invented licence. */\n// leantex: formats = html\nint x;\n"
  t "code files: a directive after a leading block comment is named, not read"
    (strayC.output.formats.isEmpty && strayCDs.any (·.kind == .W0387) &&
      (elabCode "t.c" "/* An invented licence. */\n// leantex: formats = html\n").2.any (·.kind == .W0387))
  let cSrc ← fixtureText "testdata/codedoc/langs/c-docs.c"
  t "code files: a C doc comment after a macro on its line stays in the macro"
    ((prosePieces .c cSrc).size == 3 &&
      (codePieces .c cSrc).any (·.contains "#define WIDTH 4 /** a comment after a macro stays in it */"))
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

/-- Each dialect's reader, on invented comments: its tags and commands as markdown, its code blocks in
the language they name or the file's, and each construct it does not read named once. -/
def docMarkupChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let kinds (ds : Array Diag) : Array String := ds.map (·.kind.code)
  -- Javadoc.
  let (jdoc, jds) := elabCode "t.java" ("/**\n * Adds an <b>amount</b> to the {@code List<T>}; a * stays.\n" ++
    " * <p>Then {@link java.util.List#add(Object) add} it.\n * <ul><li>one</li><li>two</li></ul>\n" ++
    " * <pre>{@code\n *   int x = 1 < 2;\n * }</pre>\n * @param amount the amount\n *   to add\n" ++
    " * @return whether it was added\n * @throws IllegalStateException when full\n */\n" ++
    "boolean add(int amount) { return true; }\n")
  t s!"javadoc: inline code and HTML read as markdown, a star literal ({elemTexts "p" jdoc})"
    ((elemTexts "code" jdoc).contains "List<T>" && (elemTexts "strong" jdoc).contains "amount" &&
      (elemTexts "p" jdoc).any (·.contains "; a * stays."))
  t s!"javadoc: a list and a pre block read as a list and a Java listing ({listings jdoc})"
    ((elemTexts "li" jdoc).size ≥ 4 &&
      (listings jdoc).any fun (l, c) => l == some "java" && c.contains "int x = 1 < 2;")
  t s!"javadoc: block tags set as the standard doclet's sections ({elemTexts "p" jdoc})"
    ((elemTexts "strong" jdoc).contains "Parameters:" && (elemTexts "strong" jdoc).contains "Returns:" &&
      (elemTexts "strong" jdoc).contains "Throws:" &&
      (elemTexts "li" jdoc).any (·.contains "the amount to add"))
  t s!"javadoc: a link to a program element sets its text and is named ({kinds jds})"
    ((elemTexts "code" jdoc).contains "add" && (jds.filter (·.kind == .W0454)).size == 1 &&
      !jds.any (·.kind == .W0453) && !jds.any (·.kind == .E0390))
  let (_, inherit) := elabCode "t.java" "class A {\n    /** {@inheritDoc} */\n    void f() {}\n}\n"
  t "javadoc: an inline tag the reader does not read is named where it stands"
    (inherit.any fun d => d.kind == .W0453 && d.span.map (·.pos.line) == some 2)
  let (md, mdDs) := elabCode "t.java" "/// Adds *one* to {@code x}.\n///\n/// @param x a number\nint inc(int x) { return x + 1; }\n"
  t s!"javadoc: a markdown comment reads its markdown and its tags ({elemTexts "em" md})"
    ((elemTexts "em" md).contains "one" && (elemTexts "code" md).contains "x" &&
      (elemTexts "strong" md).contains "Parameters:" && mdDs.isEmpty)
  -- Doxygen.
  let (cdoc, cds) := elabCode "t.c" ("/**\n * \\file\n * \\brief Invented gauges.\n */\n#include <stddef.h>\n" ++
    "/**\n * Folds \\p xs, see \\ref other.\n * \\param[in] xs the levels\n * \\return their sum\n" ++
    " * \\note Takes \\c O(n).\n * \\code{.py}\n * print(1)\n * \\endcode\n */\nint fold(int *xs);\n")
  t s!"doxygen: a comment holding \\file describes the file ({cdoc.info.title})"
    ((elabCode "t.c" "/** \\file\n * # Gauges\n */\nint x;\n").1.info.title == some "Gauges")
  t s!"doxygen: commands read as markdown, sections as Doxygen labels them ({elemTexts "strong" cdoc})"
    ((elemTexts "code" cdoc).contains "xs" && (elemTexts "code" cdoc).contains "O(n)" &&
      (elemTexts "strong" cdoc).contains "Parameters:" && (elemTexts "strong" cdoc).contains "Returns:" &&
      (elemTexts "strong" cdoc).contains "Note:" && (elemTexts "li" cdoc).any (·.contains "the levels"))
  t s!"doxygen: a code block reads in the language its extension names ({listings cdoc})"
    ((listings cdoc).any fun (l, c) => l == some "python" && c.contains "print(1)")
  t s!"doxygen: a reference sets its name unlinked, named once ({kinds cds})"
    ((cds.filter (·.kind == .W0454)).size == 1 && !cds.any (·.kind == .W0453))
  let (_, unknown) := elabCode "t.cpp" "/// Uses \\frobnicate here.\nint f();\n"
  t "doxygen: a command the reader does not read is named"
    (unknown.any fun d => d.kind == .W0453)
  -- rustdoc.
  let (rdoc, rds) := elabCode "t.rs" ("/// Uses [`Vec`] and [a page](https://example.org).\n///\n" ++
    "/// ```\n/// # fn main() {\n/// let x = 1;\n/// # }\n/// ```\n///\n/// ```text\n/// # kept\n/// ```\nfn f() {}\n")
  t s!"rustdoc: a code block naming no language is Rust, its # lines hidden ({listings rdoc})"
    ((listings rdoc).any (fun (l, c) => l == some "rust" && c.contains "let x = 1;" && !c.contains "fn main") &&
      (listings rdoc).any fun (l, c) => l == some "text" && c.contains "# kept")
  t s!"rustdoc: an intra-doc link sets its text, a URL stays a link ({hrefs rdoc}, {kinds rds})"
    ((elemTexts "code" rdoc).contains "Vec" && (hrefs rdoc).contains "https://example.org" &&
      (rds.filter (·.kind == .W0454)).size == 1)
  let (lit, litDs) := elabCode "t.java" "/** a_b_c, 2 * 3, [x] and #y; one<br>two. */\nint z;\n"
  t s!"javadoc: a comment's text is literal, markdown's punctuation in it too, and a break breaks ({elemTexts "p" lit})"
    ((elemTexts "p" lit).any (·.contains "a_b_c, 2 * 3, [x] and #y; one") && !litDs.any (·.kind == .E0390))
  let (esc, escDs) := elabCode "t.c" "/// a \\@b and \\\\ c\nint z;\n"
  t s!"doxygen: an escaped scalar is its text ({elemTexts "p" esc})"
    ((elemTexts "p" esc).any (·.contains "a @b and \\ c") && escDs.isEmpty)
  let (defs, defsDs) := elabCode "t.rs" "/// See [Foo].\n///\n/// [Foo]: crate::Foo\nfn f() {}\n"
  t s!"rustdoc: a reference definition naming an item sets its uses' text unlinked ({elemTexts "p" defs})"
    ((elemTexts "p" defs).any (·.contains "See Foo.") && !(elemTexts "p" defs).any (·.contains "crate::") &&
      defsDs.any (·.kind == .W0454))
  let (disc, discDs) := elabCode "t.rs" "/// <details>\n/// <summary>More</summary>\n///\n/// Hidden.\n///\n/// </details>\nfn f() {}\n"
  t s!"rustdoc: a disclosure's tags drop, named, and its text sets ({elemTexts "p" disc})"
    ((elemTexts "p" disc).any (·.contains "Hidden.") && (elemTexts "p" disc).any (·.contains "More") &&
      discDs.any (·.kind == .W0453) && !discDs.any (·.kind == .E0390))
  let (secs, secsDs) := elabCode "t.c" ("/**\n * \\param a first\n * \\param b second\n *\n * More text.\n */\n" ++
    "int f(int a, int b);\n/// \\param a x\n/// \\return y\n///\n/// Next.\nint g(int a);\n")
  t s!"doxygen: a blank line ends a section, the text after it a paragraph of its own ({elemTexts "p" secs})"
    ((elemTexts "p" secs).contains "More text." && (elemTexts "p" secs).contains "Next." &&
      (elemTexts "li" secs).size == 3 && secsDs.isEmpty)
  let (html, htmlDs) := elabCode "t.cpp" "/// <b>Bold</b> start.\nint x;\n"
  t s!"doxygen: a comment opening on HTML keeps its first scalar ({elemTexts "strong" html})"
    ((elemTexts "strong" html).contains "Bold" && htmlDs.isEmpty)
  let (fence, fenceDs) := elabCode "t.java" ("/// Example:\n///\n/// ```\n/// @Override\n/// void f() {}\n" ++
    "/// ```\nvoid g() {}\n")
  t s!"javadoc: a markdown comment's code block holds no block tag ({listings fence})"
    ((listings fence).any (fun (l, c) => l == some "java" && c.contains "@Override") &&
      !fenceDs.any (·.kind == .W0453))
  let (ind, indDs) := elabCode "t.rs" ("/// Index a[i] here, and [x] is no link.\n///\n" ++
    "///     let v: Vec<u8> = a[i];\n///     # let hidden = 1;\nfn f() {}\n")
  t s!"rustdoc: an indented code block is Rust, its hidden lines dropped, and plain brackets stay text ({listings ind})"
    ((listings ind).any (fun (l, c) => l == some "rust" && c.contains "let v: Vec<u8> = a[i];" &&
        !c.contains "hidden") &&
      (elemTexts "p" ind).any (·.contains "a[i] here, and [x] is no link.") && indDs.isEmpty)
  let (br, _) := elabCode "t.java" "/** one<br>two */\nint z;\n"
  t s!"javadoc: a break breaks its line ({elemTexts "p" br})"
    ((elemTexts "p" br).any fun p => p.contains "one" && p.contains "two" && !p.contains "<br>")
  let (links, linksDs) := elabCode "t.java" "/// See [java.util.List] and [List#add(Object)].\nvoid f() {}\n"
  t s!"javadoc: a markdown comment's links to program elements set their text, named ({kinds linksDs})"
    ((elemTexts "p" links).any (·.contains "See java.util.List and List#add(Object).") &&
      (linksDs.filter (·.kind == .W0454)).size == 2)
  let (num, _) := elabCode "t.java" "/** 1. First step, as 2020. was. */\nint z;\n"
  t s!"javadoc: digits and a period opening the comment are text, no list ({elemTexts "p" num})"
    ((elemTexts "li" num).isEmpty && (elemTexts "p" num).any (·.contains "1. First step"))
  let (nest, _) := elabCode "t.java" "/** <ol><li>a<ul><li>b</li></ul></li><li>c</li></ol> */\nint z;\n"
  t s!"javadoc: a list inside an item nests under it, and an ordered list counts ({elemTexts "li" nest})"
    ((elemTexts "li" nest).size == 3 && (elemTexts "ol" nest).size == 1 && (elemTexts "ul" nest).size == 1)
  let (tick, _) := elabCode "t.c" "/// Don`t use it.\n///\n/// \\param a x\nint f(int a);\n"
  t s!"doxygen: an unpaired backtick ends at its paragraph ({elemTexts "strong" tick})"
    ((elemTexts "strong" tick).contains "Parameters:")
  let (indTag, indTagDs) := elabCode "t.java" "/// Example:\n///\n///     @Override\n///     void f() {}\nvoid g() {}\n"
  t "javadoc: a markdown comment's indented code holds no block tag"
    (!indTagDs.any (·.kind == .W0453) && (preTexts indTag).any (·.contains "@Override"))
  let (_, imgDs) := elabCode "t.rs" "/// A ![logo](Logo) here.\nfn f() {}\n"
  t "rustdoc: an image is no intra-doc link" (!imgDs.any (·.kind == .W0454))
  -- Citations.
  for (n, lang) in [("java-cite", Ir.CodeLang.java), ("c-cite", .c)] do
    let src ← fixtureText s!"testdata/codedoc/langs/{n}.{lang.extension}"
    let (d, ds) ← elabCodeFixture n lang src (dir := "testdata/codedoc/langs")
    let shown := String.intercalate " " ((elemTexts "p" d) ++ (elemTexts "li" d)).toList
    t s!"citations: {n}'s documentation cites into its declared bibliography ({kinds ds})"
      (shown.contains "An Invented Almanac of Tides" && !shown.contains "[Almanac12]")
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "pkg" / "docs")
    IO.FS.writeFile (dir / "pkg" / "pyproject.toml") "[project]\nname = \"tides\"\n"
    IO.FS.writeFile (dir / "pkg" / "docs" / "references.bib") (← fixtureText "testdata/codedoc/langs/cite.bib")
    let src := "\"\"\"Tides follow [Almanac12].\"\"\"\n"
    let (d, _) ← elabCodeFixture "m" .python src (dir := (dir / "pkg").toString) (driver := true)
    t "citations: a Python file's docstring cites into its project's docs/references.bib"
      (String.intercalate " " (elemTexts "li" d).toList |>.contains "An Invented Almanac of Tides")
    IO.FS.removeFile (dir / "pkg" / "pyproject.toml")
    let (d, _) ← elabCodeFixture "m" .python src (dir := (dir / "pkg").toString) (driver := true)
    t "citations: a folder holding no project marker gives its docs/references.bib to no file"
      ((elemTexts "li" d).isEmpty && (elemTexts "p" d).any (·.contains "[Almanac12]"))
  let citeSrc ← fixtureText "testdata/codedoc/langs/rust-cite.rs"
  let (cited, citedDs) ← elabCodeFixture "rust-cite" .rust citeSrc (dir := "testdata/codedoc/langs")
  let shown := String.intercalate " " ((elemTexts "p" cited) ++ (elemTexts "li" cited)).toList
  t s!"citations: a Rust page's documentation cites into its declared bibliography ({kinds citedDs})"
    (shown.contains "An Invented Almanac of Tides" && !shown.contains "[Almanac12]" &&
      !citedDs.any (·.kind == .W0351) && !citedDs.any (·.kind == .W0110))

end Tests.CodeDoc
