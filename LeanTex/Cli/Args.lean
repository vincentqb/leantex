module

namespace LeanTex.Cli

/-- Which backends to run. -/
public inductive Emit where
  | pdf
  | html
  /-- Markdown: the llms.txt convention's plain-text twin of the page. -/
  | md
  deriving Repr, @[expose] BEq

/-- Which stylesheet the HTML backend writes. -/
public inductive CssChoice where
  | own
  | bulma
  | none
  deriving Repr, BEq

public inductive ColorMode where
  | auto
  | always
  | never
  deriving Repr, BEq

public inductive Cmd where
  | help
  | version
  | build (file : String)
  | dump (file : String)
  | hyphenate (words : List String) (file : Option String)
  /-- List installed font families, one per line. -/
  | fonts
  /-- List the built-in theme bundles, one per line. -/
  | themes
  deriving Repr, BEq

public structure Config where
  cmd : Cmd
  verbosity : Nat := 0
  quiet : Bool := false
  porcelain : Bool := false
  color : ColorMode := .auto
  /-- `-o`: an output file (its extension picks the backend) or a directory. -/
  output : Option String := none
  watch : Bool := false
  /-- `--best-effort`: accept every loss, as `\allow` of every code would —
  port mode for documents written against another engine. -/
  bestEffort : Bool := false
  /-- `--werror`: exit 1 when any warning was emitted. Output is still
  written — the flag changes the exit code, never the rendering — and an
  accepted loss (`\allow`, `--best-effort`) is not a warning for this
  purpose: that is the point of accepting it. Notes never count. -/
  werror : Bool := false
  /-- The one remaining flag that shapes the artifact — a recorded debt, not
  a design: it dies when `\output` grows a key for the math renderer, and
  the matching hypothesis in `artifact_flag_free` dies with it. -/
  mathBoundary : Option String := none
  /-- Extra font directories, added to the built-in locations. -/
  fontDirs : Array String := #[]
  deriving Repr, BEq

private def vCount (s : String) : Option Nat :=
  match s.toList with
  | '-' :: vs => if !vs.isEmpty && vs.all (· == 'v') then some vs.length else none
  | _ => none

private def emitOne : String → Option Emit
  | "pdf" => some .pdf
  | "html" => some .html
  | "md" => some .md
  | _ => none

private def cssChoice : String → Option CssChoice
  | "own" => some .own
  | "bulma" => some .bulma
  | "none" => some .none
  | _ => none

private def colorMode : String → Option ColorMode
  | "auto" => some .auto
  | "always" => some .always
  | "never" => some .never
  | _ => none

public def parse (argv : List String) : Except String Config := do
  let mut cfg : Config := { cmd := .help }
  let mut cmd : Option Cmd := none
  let mut hyphenWords : List String := []
  let mut hyphenFile : Option String := none
  let mut wantsFile : Option String := none
  let mut args := argv
  repeat
    match args with
    | [] => break
    | a :: rest =>
      args := rest
      match a with
      | "-q" | "--quiet" => cfg := { cfg with quiet := true }
      | "--porcelain" => cfg := { cfg with porcelain := true }
      | "--watch" => cfg := { cfg with watch := true }
      | "--best-effort" => cfg := { cfg with bestEffort := true }
      | "--werror" => cfg := { cfg with werror := true }
      | "-h" | "--help" => return { cfg with cmd := .help }
      | "--version" => return { cfg with cmd := .version }
      | "-o" | "--output" =>
        match rest with
        | m :: rest' =>
          cfg := { cfg with output := some m }
          args := rest'
        | [] => throw "'-o' needs a file or directory"
      | "--color" =>
        match rest with
        | m :: rest' =>
          let some c := colorMode m | throw s!"invalid color mode '{m}'"
          cfg := { cfg with color := c }
          args := rest'
        | [] => throw "'--color' needs a mode: auto | always | never"
      | "--emit" =>
        throw "'--emit' is not a flag; the document declares what to build: \\output{ formats = pdf, html, md }"
      | "--css" =>
        throw "'--css' is not a flag; the document declares its stylesheet: \\output{ css = own | bulma | none }"
      | "--math-boundary" =>
        match rest with
        | m :: rest' =>
          cfg := { cfg with mathBoundary := some m }
          args := rest'
        | [] => throw "'--math-boundary' needs a tool URL or path"
      | "--font-dir" =>
        match rest with
        | m :: rest' =>
          cfg := { cfg with fontDirs := cfg.fontDirs.push m }
          args := rest'
        | [] => throw "'--font-dir' needs a directory"
      | "--file" =>
        match cmd, rest with
        | some (.hyphenate _ _), f :: rest' =>
          hyphenFile := some f
          args := rest'
        | some (.hyphenate _ _), [] => throw "'--file' needs a path"
        | _, _ => throw "'--file' applies to 'hyphenate'"
      | _ =>
        if let some n := vCount a then
          cfg := { cfg with verbosity := min 3 (cfg.verbosity + n) }
        else if a.startsWith "--emit=" then
          throw "'--emit' is not a flag; the document declares what to build: \\output{ formats = pdf, html, md }"
        else if a.startsWith "--css=" then
          throw "'--css' is not a flag; the document declares its stylesheet: \\output{ css = own | bulma | none }"
        else if a.startsWith "--output=" then
          cfg := { cfg with output := some (a.drop "--output=".length).toString }
        else if a.startsWith "--font-dir=" then
          cfg := { cfg with
            fontDirs := cfg.fontDirs.push (a.drop "--font-dir=".length).toString }
        else if a.startsWith "--color=" then
          let m := (a.drop "--color=".length).toString
          let some c := colorMode m | throw s!"invalid color mode '{m}'"
          cfg := { cfg with color := c }
        else if a.startsWith "-" then
          throw s!"unknown flag '{a}'"
        else
          match cmd, wantsFile with
          | some (.hyphenate _ _), _ => hyphenWords := hyphenWords ++ [a]
          | some _, _ => throw s!"unexpected argument '{a}'"
          -- A command that needs a file takes the next positional, not the
          -- next token: flags belong after the command, where people type them.
          | none, some k => cmd := some (if k == "build" then .build a else .dump a)
          | none, none =>
            match a with
            | "help" => cmd := some .help
            | "version" => cmd := some .version
            | "hyphenate" => cmd := some (.hyphenate [] none)
            | "fonts" => cmd := some .fonts
            | "themes" => cmd := some .themes
            | "build" | "dump" => wantsFile := some a
            | _ =>
              -- The file is the command: `leantex doc.tex` builds it.
              -- `.md` is reserved for the markdown surface.
              if a.endsWith ".tex" || a.endsWith ".md" then
                cmd := some (.build a)
              else if a.toList.contains '.' || a.toList.contains '/' then
                throw s!"'{a}' is not a .tex or .md document"
              else
                throw s!"unknown command '{a}'"
  if cfg.quiet && cfg.verbosity > 0 then
    throw "choose one of -q and -v"
  if let some k := wantsFile then
    if cmd.isNone then
      throw s!"'{k}' needs a file"
  match cmd with
  | some (.hyphenate _ _) =>
    if hyphenWords.isEmpty && hyphenFile.isNone then
      throw "'hyphenate' needs words or --file <path>"
    return { cfg with cmd := .hyphenate hyphenWords hyphenFile }
  | _ => return { cfg with cmd := cmd.getD .help }

public def Emit.ext : Emit → String
  | .pdf => "pdf"
  | .html => "html"
  | .md => "md"

/-- The backend an output name asks for, when it names one. -/
public def emitOfPath (o : String) : Option Emit :=
  if o.endsWith ".pdf" then some .pdf
  else if o.endsWith ".html" then some .html
  else if o.endsWith ".md" then some .md
  else none

/-- Backends to run: the output name (`-o out.html`) > the document's
`\output{ formats = ... }` > PDF. -/
public def Config.effectiveEmit (cfg : Config) (docFormats : Array String) : Array Emit :=
  if let some e := cfg.output.bind emitOfPath then #[e]
  else
    let ds := docFormats.filterMap emitOne
    if ds.isEmpty then #[.pdf] else ds

/-- Stylesheet: the document's `\output{ css = ... }` or the default. Takes
no `Config`, by design — see `artifact_flag_free`. -/
public def cssFor (docCss : Option String) : CssChoice :=
  (docCss.bind cssChoice).getD .own

/-- **The artifact is a function of the document and the font environment;
flags are not arguments to it.** Two parsed configurations that agree on
`-o` make the same backend decisions, whatever every other flag says.
`-o` is exempted by hypothesis because the output NAME picks which
backends run (`-o out.html`), never what any backend emits; `--font-dir`
needs no hypothesis because it extends the font environment the invariant
conditions on, and the planning functions cannot see it. `--math-boundary`
is exempted as the one recorded remainder: it dies when the document grows
an `\output` key for the math renderer, and its hypothesis dies with it.
Stated over the driver's planning functions rather than `main`, which is
IO: these are the only places a `Config` value meets a backend decision —
`cssFor`, `Pdf.write`, `MarkdownDoc.emit`, and `HtmlDoc.emit` take no
`Config` by type, and the pre-commit gate keeps `Config` reads in the
driver on a declared allowlist. A future flag that shapes the artifact
must be read here, and then this proof breaks — the invariant is a build
error, not a convention. -/
public theorem artifact_flag_free (cfg cfg' : Config)
    (ho : cfg.output = cfg'.output) (hm : cfg.mathBoundary = cfg'.mathBoundary)
    (docFormats : Array String) :
    (cfg.effectiveEmit docFormats, cfg.mathBoundary)
      = (cfg'.effectiveEmit docFormats, cfg'.mathBoundary) := by
  simp only [Config.effectiveEmit, ho, hm]

/-- Where a backend writes. A directory keeps the source's stem; a file
naming this backend's extension is used as-is; anything else (the other
backend's file, when `\output` declares several formats) falls back
beside the source. -/
public def outPath (output : Option String) (outputIsDir : Bool) (source : String)
    (e : Emit) : String :=
  let besideSource := (System.FilePath.mk source).withExtension e.ext |>.toString
  match output with
  | none => besideSource
  | some o =>
    if o.endsWith "/" || outputIsDir then
      let stem := (System.FilePath.mk source).fileStem.getD "out"
      let dir := String.ofList (o.toList.reverse.dropWhile (· == '/')).reverse
      (System.FilePath.mk dir / stem).withExtension e.ext |>.toString
    else if emitOfPath o == some e then o
    else besideSource

/-- The exit-code contract, one total function so the driver and the tests
read the same answer: errors win, then failed assertions, then — only under
`--werror` — warnings. An accepted loss was already downgraded to a note
before it reached these counts, so `\allow` composes with `--werror` by
construction. -/
public def exitFor (errors assertFailures warnings : Nat) (werror : Bool) : UInt32 :=
  if errors > 0 then 1
  else if assertFailures > 0 then 2
  else if werror && warnings > 0 then 1
  else 0

public def helpText : String :=
  "leantex — compile a .tex document to PDF or HTML, fast, with no setup

usage: leantex <file> [flags] · leantex <command> [args]

examples:
  leantex doc.tex                 build doc.pdf beside the source
  leantex doc.tex -o out.html     the output name picks the backend
  leantex doc.tex -o build/       write build/doc.pdf
  leantex doc.tex --watch         rebuild on every change

a document declares what to build — \\output{ formats = pdf, html } — so
the command line stays bare: flags say where output lands and how the run
reports, not what the artifact is.

commands:
  build <file>            same as `leantex <file>`
  dump <file>             print the elaborated document structure (debugging)
  hyphenate <word>...     show hyphenation points (--file <path> for a list)
  fonts                   list the font families leantex can see
  themes                  list the built-in theme bundles (\\theme{name})
  version · help

flags:
  -o, --output <path>     output file (.pdf | .html | .md) or directory
  --watch                 rebuild when the source changes (Ctrl-C stops)
  --best-effort           accept every loss (as \\allow of every code); the
                          summary prints what was accepted
  --werror                exit 1 when any warning was emitted; output is
                          still written, and accepted losses (\\allow,
                          --best-effort) and notes never count
  --math-boundary <tool>  attach a client-side math renderer to HTML output
  --font-dir <d>          also look for fonts here (repeatable)
  -q, --quiet             errors only
  -v -vv -vvv             phases · decisions · trace (on stderr)
  --porcelain             JSONL events on stdout, for machines
  --color <m>             auto | always | never (NO_COLOR respected)

exit codes: 0 ok · 1 document errors (with --werror, warnings too) · 2 assertions failed · 3 usage · 4 internal"

end LeanTex.Cli
