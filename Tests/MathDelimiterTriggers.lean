module

public import LeanTex.Core.Compat
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.FontDiscovery
import all LeanTex.Cli.Driver

open LeanTex.Core

namespace Tests

private structure DelimiterSite where
  line : Nat
  col : Nat
  spelling : String

private structure DelimiterFixture where
  name : String
  source : String
  sites : Array DelimiterSite

private def delimiterFixtures : Array DelimiterFixture := #[
  { name := "inline", source := "First\n  \\(\\mathcal{A}\\)"
    sites := #[⟨2, 3, "\\("⟩] },
  { name := "display", source := "First\n  \\[\\mathcal{A}\\]"
    sites := #[⟨2, 3, "\\["⟩] },
  { name := "nested", source := "\\begin{center}\n{\\[x\\]}\n\\end{center}"
    sites := #[⟨2, 2, "\\["⟩] },
  { name := "backend", source :=
      "\\begin{ifbackend}{html,pdf}\n  \\(x\\)\n\\end{ifbackend}"
    sites := #[⟨2, 3, "\\("⟩] },
  { name := "caption", source :=
      "\\begin{figure}\n\\caption{Text \\(x\\)}\n\\end{figure}"
    sites := #[⟨2, 15, "\\("⟩] },
  { name := "running-head", source := "\\runninghead{Text \\(x\\)}"
    sites := #[⟨1, 19, "\\("⟩] },
  { name := "definition", source := "\\newcommand{\\request}{\\[x\\]}\n\\request"
    sites := #[⟨1, 23, "\\["⟩] },
  { name := "mixed", source := "\\(x\\) \\[y\\]"
    sites := #[⟨1, 1, "\\("⟩, ⟨1, 7, "\\["⟩] }]

private def delimiterCheck (ref : IO.Ref (List String)) (name : String)
    (ok : Bool) : IO Unit := do
  unless ok do ref.modify (("math delimiter triggers: " ++ name) :: ·)

/-- The source index must retain a math opener's stored lexical evidence,
at its exact file, line and column. Delayed typed records use positions
read by the real lexer; neither their message nor the math display flag
supplies a spelling. The collector must not invent evidence for synthetic
math, and it must continue to descend into the formula's body. -/
public def mathDelimiterTriggerChecks (ref : IO.Ref (List String)) : IO Unit := do
  for f in delimiterFixtures do
    let file := "synthetic/delimiter-" ++ f.name ++ ".tex"
    let (tokens, lexDs) := Lex.lex file f.source
    let (raws, parseDs) := Parse.parse file tokens
    let sources := (Compat.execute file raws).sourceTriggers
    let t := fun name ok => delimiterCheck ref (f.name ++ ": " ++ name) ok
    t "authored fixture parses without recovery" (lexDs.isEmpty && parseDs.isEmpty)
    for site in f.sites do
      let some token := tokens.find? (fun token =>
          token.pos.line == site.line && token.pos.col == site.col) |
        t "expected opener exists at the authored coordinates" false
        continue
      t "lexer retains the literal opener" (token.pos.command == some site.spelling)
      t "collector retains the literal opener"
        (sources[(file, site.line, site.col)]? == some site.spelling)
      for kind in [DiagCode.N0016, .N0018] do
        let original := Diag.of kind "The formula needs font resolution."
          (some ⟨file, token.pos⟩) (subject := "math-request")
        let attributed := sources.attribute original
        t (kind.code ++ " restores the exact opener")
          (attributed.trigger == some site.spelling)
        t (kind.code ++ " preserves the entire position and other fields")
          (decide (attributed.span = original.span) &&
            { attributed with trigger := original.trigger } == original)
        -- An interior character of the opener is not its source position.
        let adjacent := { original with
          span := some ⟨file, { token.pos with col := token.pos.col + 1 }⟩ }
        t (kind.code ++ " never borrows a nearby opener")
          ((sources.attribute adjacent).trigger.isNone)
        let foreign := { original with span := some ⟨file ++ ".other", token.pos⟩ }
        t (kind.code ++ " never borrows another file's opener")
          ((sources.attribute foreign).trigger.isNone)
    if f.name == "inline" || f.name == "display" then
      t "math-body controls retain their own source"
        (sources[(file, 2, 5)]? == some "\\mathcal")
    if f.name == "definition" then
      t "the macro invocation retains its written owner"
        (sources[(file, 2, 1)]? == some "\\request")
  -- Input wrappers are the driver's parsed-file boundary. The same
  -- coordinates in two files must keep distinct delimiter spellings.
  let root := "synthetic/delimiter-root.tex"
  let child := "synthetic/delimiter-child.tex"
  let rootSource := "\n  \\(x\\)"
  let childSource := "\n  \\[y\\]"
  let rootTokens := (Lex.lex root rootSource).1
  let childTokens := (Lex.lex child childSource).1
  let rootRaws := (Parse.parse root rootTokens).1
  let childRaws := (Parse.parse child childTokens).1
  let sources := (Compat.execute root
    (#[.env (Parse.inputEnv child) childRaws {}] ++ rootRaws)).sourceTriggers
  for (file, tokens, spelling) in
      [(root, rootTokens, "\\("), (child, childTokens, "\\[")] do
    let t := fun name ok => delimiterCheck ref ("include " ++ file ++ ": " ++ name) ok
    t "collector retains file ownership" (sources[(file, 2, 3)]? == some spelling)
    let some token := tokens.find? (fun token =>
        token.pos.line == 2 && token.pos.col == 3) |
      t "expected opener exists at the authored coordinates" false
      continue
    for kind in [DiagCode.N0016, .N0018] do
      let original := Diag.of kind "The formula needs font resolution."
        (some ⟨file, token.pos⟩)
      let attributed := sources.attribute original
      t (kind.code ++ " retains the file, exact position and opener")
        (decide (attributed.span = original.span) && attributed.trigger == some spelling)
  -- A display flag is not lexical evidence. Erasing the evidence from
  -- a real opener must not turn either kind of synthetic math into a
  -- guessed dollar or escaped delimiter.
  let some token := rootTokens.find? (·.pos.command == some "\\(") |
    delimiterCheck ref "synthetic guard has a real source position" false
    return
  for display in [false, true] do
    let p := { token.pos with command := none }
    let sources := (Compat.execute root #[.math display #[] p]).sourceTriggers
    delimiterCheck ref s!"synthetic display={display}: no invented opener"
      sources.isEmpty
    let d := Diag.of .N0016 "The formula needs font resolution." (some ⟨root, p⟩)
    delimiterCheck ref s!"synthetic display={display}: no invented diagnostic trigger"
      ((sources.attribute d).trigger.isNone)
    let explicit := { d with trigger := some "\\request" }
    delimiterCheck ref s!"synthetic display={display}: explicit producer evidence survives"
      ((sources.attribute explicit) == explicit)

private structure DollarFixture where
  name : String
  preamble : String := ""
  body : String
  formulas : Array (Bool × String)
  sites : Array DelimiterSite
  alphabet : Option DelimiterSite := none
  needsFace : Bool := true
  equivalent : Option String := none

private def dollarFixtures : Array DollarFixture := #[
  { name := "inline", body := "First $x$.\nLater $\\mathcal{A}$."
    formulas := #[(false, "x"), (false, "\\mathcal {A}")]
    sites := #[⟨4, 7, "$"⟩, ⟨5, 7, "$"⟩], alphabet := some ⟨5, 7, "$"⟩
    equivalent := some "First \\(x\\).\nLater \\(\\mathcal{A}\\)." },
  { name := "display", body := "Before.\n$$\\mathcal{A}+x$$\nAfter."
    formulas := #[(true, "\\mathcal {A}+x")]
    sites := #[⟨5, 1, "$$"⟩], alphabet := some ⟨5, 1, "$$"⟩
    equivalent := some "Before.\n\\[\\mathcal{A}+x\\]\nAfter." },
  { name := "mixed", body := "$x$ $$y$$ $z$"
    formulas := #[(false, "x"), (true, "y"), (false, "z")]
    sites := #[⟨4, 1, "$"⟩, ⟨4, 5, "$$"⟩, ⟨4, 11, "$"⟩] },
  { name := "adjacent-inline", body := "$x$$y$"
    formulas := #[(false, "x"), (false, "y")]
    sites := #[⟨4, 1, "$"⟩, ⟨4, 4, "$"⟩] },
  { name := "inline-display", body := "$x$$$y$$"
    formulas := #[(false, "x"), (true, "y")]
    sites := #[⟨4, 1, "$"⟩, ⟨4, 4, "$$"⟩] },
  { name := "display-inline", body := "$$x$$$y$"
    formulas := #[(true, "x"), (false, "y")]
    sites := #[⟨4, 1, "$$"⟩, ⟨4, 6, "$"⟩] },
  { name := "adjacent-display", body := "$$x$$$$y$$"
    formulas := #[(true, "x"), (true, "y")]
    sites := #[⟨4, 1, "$$"⟩, ⟨4, 6, "$$"⟩] },
  { name := "wrappers", body :=
      "\\begin{ifbackend}{html,pdf}\n\\begin{center}\n$$\\mathcal{A}$$\n\
      \\end{center}\n\\end{ifbackend}"
    formulas := #[(true, "\\mathcal {A}")]
    sites := #[⟨6, 1, "$$"⟩], alphabet := some ⟨6, 1, "$$"⟩ },
  { name := "caption", body :=
      "\\begin{figure}\n\\caption{Caption $\\mathcal{A}$}\n\\end{figure}"
    formulas := #[(false, "\\mathcal {A}")]
    sites := #[⟨5, 18, "$"⟩], alphabet := some ⟨5, 18, "$"⟩ },
  { name := "running-head", preamble := "\\runninghead{Header $\\mathcal{A}$}\n"
    body := "Body.", formulas := #[(false, "\\mathcal {A}")]
    sites := #[⟨3, 21, "$"⟩], alphabet := some ⟨3, 21, "$"⟩ },
  { name := "macro-call", preamble := "\\newcommand{\\request}{$\\mathcal{A}$}\n"
    body := "Plain.\n\\request", formulas := #[(false, "\\mathcal {A}")]
    sites := #[⟨6, 1, "\\request"⟩], alphabet := some ⟨6, 1, "\\request"⟩ },
  { name := "comment-separated-shifts", body :=
      "$% The two shifts are not one written delimiter.\n$\\mathcal{A}$$"
    formulas := #[(true, "\\mathcal {A}")]
    sites := #[⟨4, 1, "$"⟩], alphabet := some ⟨4, 1, "$"⟩ },
  { name := "unicode-prefix", body := "Café $$x$$"
    formulas := #[(true, "x")], sites := #[⟨4, 6, "$$"⟩] },
  { name := "empty-display", body := "$$$$"
    formulas := #[(true, "")], sites := #[⟨4, 1, "$$"⟩], needsFace := false },
  { name := "escaped-and-verbatim", body :=
      "Escaped \\$5 and \\$\\$.\n\\verb|$x$$y$|\n% $\\mathcal{A}$$\nDone."
    formulas := #[], sites := #[], needsFace := false }]

private def dollarSource (preamble body : String) : String :=
  "\\documentclass{article}\n\\fonts{body=\"Open Sans\"}\n" ++
    preamble ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

private def dollarFormulas (doc : Ir.Doc) : Array (Bool × String) :=
  Ir.foldDoc (fun out x => match x with
    | .formula display source _ => out.push (display, source)
    | _ => out) #[] doc

private def dollarAt (file : String) (site : DelimiterSite) (source : Option Span) : Bool :=
  source.any fun s => s.file == file && s.pos.line == site.line &&
    s.pos.col == site.col && s.pos.command == some site.spelling

/-- Read real files through the frontend used by `leantex build` and `dump`:
UTF-8 decoding, extension selection, input execution, preparation and
elaboration all participate. Formula modes and original opening delimiters
must then survive the same font assembly that produces N0016 and N0018.
Escaped, commented, verbatim and Markdown dollars remain outside this path. -/
public def mathDollarSurfaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let faces ← LeanTex.Cli.FontDiscovery.scanRootsIn none ["testdata/corpus/fonts"]
  let scan : LeanTex.Cli.FontAssembly.FaceScan :=
    { faces, docDirs := [], dirs := #[], diags := #[] }
  let cache ← LeanTex.Cli.FontEnv.Cache.mk'
  IO.FS.withTempDir fun dir => do
    for f in dollarFixtures do
      let file := (dir / (f.name ++ ".tex")).toString
      IO.FS.writeFile file (dollarSource f.preamble f.body)
      let ui ← LeanTex.Cli.Driver.Ui.mk' { cmd := .build file, color := .never }
      let t := fun name ok => delimiterCheck ref ("CLI " ++ f.name ++ ": " ++ name) ok
      let some front ← LeanTex.Cli.Driver.frontend ui file |
        t "the authored file reaches the CLI frontend" false
        continue
      t "the authored file needs no parse or math recovery"
        (!front.diags.any fun d => d.severity == .error || d.kind == .W0012)
      t s!"formula bodies and inline/display modes agree; got {repr (dollarFormulas front.doc)}"
        (dollarFormulas front.doc == f.formulas)
      let requests := Ir.mathRequests .face front.doc
      t "every expected formula retains its exact source"
        (requests.size == f.sites.size &&
          (requests.zip f.sites).all fun (r, site) => dollarAt file site r.source)
      for site in f.sites do
        t "the source index contains the actual written opener"
          (front.prepared.sourceTriggers[(file, site.line, site.col)]? == some site.spelling)
      if f.name == "escaped-and-verbatim" then
        let text := String.intercalate "" (Ir.textLeaves front.doc.body)
        t "literal dollar text survives"
          ((text.splitOn "$5").length == 2 && (text.splitOn "$x$$y$").length == 2)
      if let some body := f.equivalent then
        let mirror := (dir / (f.name ++ "-escaped.tex")).toString
        IO.FS.writeFile mirror (dollarSource f.preamble body)
        let some escaped ← LeanTex.Cli.Driver.frontend ui mirror |
          t "the equivalent escaped-delimiter source reaches the frontend" false
          continue
        t "dollar and escaped delimiters elaborate the same document"
          (Ir.eraseLocations front.doc == Ir.eraseLocations escaped.doc)
      let .ok (_, _, diags, _) ← LeanTex.Cli.FontAssembly.buildFontSet
          front.doc scan cache .settled |
        t "font assembly succeeds" false
        continue
      let notes := diags.filter (·.kind == .N0016)
      t "only actual nonempty formulas request an automatic face"
        (notes.size == if f.needsFace then 1 else 0)
      if f.needsFace then
        t "N0016 keeps the first formula's source and written trigger"
          ((notes.zip f.sites).any fun (d, site) =>
            dollarAt file site d.span && d.trigger == some site.spelling)
      let alphas := diags.filter (·.kind == .N0018)
      t "only actual alphabet requests produce alphabet notes"
        (alphas.size == if f.alphabet.isSome then 1 else 0)
      if let some site := f.alphabet then
        t "N0018 keeps the failing formula's source and written trigger"
          (alphas.any fun d => d.subject == some "math-alpha:cal" &&
            dollarAt file site d.span && d.trigger == some site.spelling)
    -- Includes traverse Input.readInput, rather than an invented Raw wrapper.
    let child := (dir / "child.tex").toString
    IO.FS.writeFile child "First $x$.\nThen $$\\mathcal{A}$$."
    let root := (dir / "root.tex").toString
    IO.FS.writeFile root (dollarSource "" "\\input{child}")
    let ui ← LeanTex.Cli.Driver.Ui.mk' { cmd := .build root, color := .never }
    let some front ← LeanTex.Cli.Driver.frontend ui root |
      delimiterCheck ref "CLI include: root reaches the frontend" false
      return
    let sites : Array DelimiterSite := #[⟨1, 7, "$"⟩, ⟨2, 6, "$$"⟩]
    delimiterCheck ref "CLI include: inline and display modes survive file expansion"
      (dollarFormulas front.doc == #[(false, "x"), (true, "\\mathcal {A}")])
    let requests := Ir.mathRequests .face front.doc
    delimiterCheck ref "CLI include: formula sources retain the included file"
      (requests.size == sites.size &&
        (requests.zip sites).all fun (r, site) => dollarAt child site r.source)
    for site in sites do
      delimiterCheck ref "CLI include: source index retains included-file delimiters"
        (front.prepared.sourceTriggers[(child, site.line, site.col)]? == some site.spelling)
    let .ok (_, _, diags, _) ← LeanTex.Cli.FontAssembly.buildFontSet
        front.doc scan cache .settled |
      delimiterCheck ref "CLI include: font assembly succeeds" false
      return
    for (kind, site) in #[DiagCode.N0016, .N0018].zip sites do
      delimiterCheck ref s!"CLI include: {kind.code} retains child source and delimiter"
        (diags.any fun d => d.kind == kind && dollarAt child site d.span &&
          d.trigger == some site.spelling)
    let markdown := (dir / "literal.md").toString
    IO.FS.writeFile markdown "Price $5. Written $x$ and $$y$$."
    let some front ← LeanTex.Cli.Driver.frontend ui markdown |
      delimiterCheck ref "CLI Markdown: file reaches the frontend" false
      return
    delimiterCheck ref "CLI Markdown: dollars remain text, never inferred TeX math"
      ((dollarFormulas front.doc).isEmpty &&
        String.intercalate "" (Ir.textLeaves front.doc.body) ==
          "Price $5. Written $x$ and $$y$$.")
    for opener in ["$", "$$"] do
      let file := (dir / (if opener == "$" then "unclosed-inline.tex"
        else "unclosed-display.tex")).toString
      IO.FS.writeFile file (dollarSource "" (opener ++ "x"))
      let some front ← LeanTex.Cli.Driver.frontend ui file |
        delimiterCheck ref ("CLI unclosed " ++ opener ++ ": frontend exists") false
        continue
      delimiterCheck ref ("CLI unclosed " ++ opener ++ ": actual opener owns the error")
        (front.diags.any fun d => d.kind == .E0201 && dollarAt file ⟨4, 1, opener⟩ d.span)

end Tests
