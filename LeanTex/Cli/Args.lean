namespace LeanTex.Cli

/-- Which backends to run. -/
inductive Emit where
  | pdf
  | html
  /-- Markdown: the llms.txt convention's plain-text twin of the page. -/
  | md
  deriving Repr, BEq

/-- Which stylesheet the HTML backend writes. -/
inductive CssChoice where
  | own
  | bulma
  | none
  deriving Repr, BEq

inductive ColorMode where
  | auto
  | always
  | never
  deriving Repr, BEq

inductive Cmd where
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

structure Config where
  cmd : Cmd
  verbosity : Nat := 0
  quiet : Bool := false
  porcelain : Bool := false
  color : ColorMode := .auto
  /-- Backends from an explicit `--emit`, which outranks the output name and
  the document's `\output`; `none` when the flag was not given. The resolved
  answer is `effectiveEmit`. -/
  emit : Option (Array Emit) := none
  /-- Stylesheet from an explicit `--css`; `none` when the flag was not
  given. The resolved answer is `effectiveCss`. -/
  css : Option CssChoice := none
  /-- `-o`: an output file (its extension picks the backend) or a directory. -/
  output : Option String := none
  watch : Bool := false
  mathBoundary : Option String := none
  /-- Extra font directories, added to the built-in locations. -/
  fontDirs : Array String := #[]
  deriving Repr, BEq

private def vCount (s : String) : Option Nat :=
  match s.toList with
  | '-' :: vs => if !vs.isEmpty && vs.all (· == 'v') then some vs.length else none
  | _ => none

def emitOne : String → Option Emit
  | "pdf" => some .pdf
  | "html" => some .html
  | "md" => some .md
  | _ => none

private def emitList (s : String) : Option (Array Emit) := do
  let parts := (s.splitOn ",").filterMap fun w =>
    let t := w.trimAscii.toString
    if t.isEmpty then none else some t
  if parts.isEmpty then none else
    let mut out : Array Emit := #[]
    for p in parts do
      match emitOne p with
      | some e => out := out.push e
      | none => failure
    some out

def cssChoice : String → Option CssChoice
  | "own" => some .own
  | "bulma" => some .bulma
  | "none" => some .none
  | _ => none

private def colorMode : String → Option ColorMode
  | "auto" => some .auto
  | "always" => some .always
  | "never" => some .never
  | _ => none

def parse (argv : List String) : Except String Config := do
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
        match rest with
        | m :: rest' =>
          let some es := emitList m
            | throw s!"invalid --emit '{m}'; expected a comma-separated list of: pdf, html, md"
          cfg := { cfg with emit := some es }
          args := rest'
        | [] => throw "'--emit' needs a list: pdf, html, md"
      | "--css" =>
        match rest with
        | m :: rest' =>
          let some c := cssChoice m
            | throw s!"invalid --css '{m}'; expected own, bulma, or none"
          cfg := { cfg with css := some c }
          args := rest'
        | [] => throw "'--css' needs a mode: own | bulma | none"
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
          let m := (a.drop "--emit=".length).toString
          let some es := emitList m
            | throw s!"invalid --emit '{m}'; expected a comma-separated list of: pdf, html, md"
          cfg := { cfg with emit := some es }
        else if a.startsWith "--css=" then
          let m := (a.drop "--css=".length).toString
          let some c := cssChoice m | throw s!"invalid --css '{m}'; expected own, bulma, or none"
          cfg := { cfg with css := some c }
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

def Emit.ext : Emit → String
  | .pdf => "pdf"
  | .html => "html"
  | .md => "md"

/-- The backend an output name asks for, when it names one. -/
def emitOfPath (o : String) : Option Emit :=
  if o.endsWith ".pdf" then some .pdf
  else if o.endsWith ".html" then some .html
  else if o.endsWith ".md" then some .md
  else none

/-- Backends to run: explicit `--emit` > the output name > the document's
`\output{ formats = ... }` > PDF. -/
def Config.effectiveEmit (cfg : Config) (docFormats : Array String) : Array Emit :=
  match cfg.emit with
  | some es => es
  | none =>
    if let some e := cfg.output.bind emitOfPath then #[e]
    else
      let ds := docFormats.filterMap emitOne
      if ds.isEmpty then #[.pdf] else ds

/-- Stylesheet: explicit `--css` > the document's `\output{ css = ... }` >
the default. -/
def Config.effectiveCss (cfg : Config) (docCss : Option String) : CssChoice :=
  match cfg.css with
  | some c => c
  | none => (docCss.bind cssChoice).getD .own

/-- Where a backend writes. A directory keeps the source's stem; a file
naming this backend's extension is used as-is; anything else (the other
backend's file, under `--emit pdf,html`) falls back beside the source. -/
def outPath (output : Option String) (outputIsDir : Bool) (source : String)
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

def helpText : String :=
  "leantex — compile a .tex document to PDF or HTML, fast, with no setup

usage: leantex <file> [flags] · leantex <command> [args]

examples:
  leantex doc.tex                 build doc.pdf beside the source
  leantex doc.tex -o out.html     the output name picks the backend
  leantex doc.tex -o build/       write build/doc.pdf
  leantex doc.tex --watch         rebuild on every change

a document can declare its own outputs — \\output{ formats = pdf, html } —
so the command line stays bare; flags override the document.

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
  --emit <list>           backends: pdf, html, md — several at once
  --css <mode>            HTML stylesheet: own | bulma | none (default own)
  --math-boundary <tool>  attach a client-side math renderer to HTML output
  --font-dir <d>          also look for fonts here (repeatable)
  -q, --quiet             errors only
  -v -vv -vvv             phases · decisions · trace (on stderr)
  --porcelain             JSONL events on stdout, for machines
  --color <m>             auto | always | never (NO_COLOR respected)

exit codes: 0 ok · 1 document errors · 2 assertions failed · 3 usage · 4 internal"

end LeanTex.Cli
