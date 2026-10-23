module

public import LeanTex.Core.SurfaceKind

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

/-- The colour source a theme is imported from. -/
public inductive ThemeSource where
  /-- A beamer colour theme (`beamercolortheme<x>.sty`). -/
  | beamer
  /-- A stylesheet's `:root` custom properties. -/
  | css
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
  /-- Write a theme file from a beamer colour theme or a stylesheet, each `--map name=key` naming
  the palette key a custom property declares. -/
  | themeImport (source : ThemeSource) (file : String) (maps : List (String × String))
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
  /-- `--best-effort`: accept every loss, as `\allow` of every code would. -/
  bestEffort : Bool := false
  /-- `--werror`: exit 1 when an unaccepted warning is emitted; output is still written. -/
  werror : Bool := false
  /-- `--math-boundary`: a local script file the HTML page carries inline. -/
  mathBoundary : Option String := none
  /-- Extra font directories, added to the built-in locations. -/
  fontDirs : Array String := #[]
  deriving Repr, BEq

private def vCount (s : String) : Option Nat :=
  match s.toList with
  | '-' :: vs => if !vs.isEmpty && vs.all (· == 'v') then some vs.length else none
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

/-- The extensions a document may end in, as a refusal lists them. -/
public def inputKinds : String :=
  match (LeanTex.Core.Ir.Surface.inputExtensions.map ("." ++ ·)).reverse with
  | [] => ""
  | [one] => one
  | last :: rest => ", ".intercalate rest.reverse ++ " or " ++ last

/-- `theme import`'s arguments: its source and file, its maps and `-o`. -/
private def themeImportArgs (cfg : Config) : List String → Except String Config
  | "import" :: rest => go rest none [] cfg.output
  | _ => throw "'theme' takes 'import --beamer <file.sty>' or 'import --css <file.css>'"
where
  go : List String → Option (ThemeSource × String) → List (String × String) → Option String →
      Except String Config
    | [], some (.beamer, _), _ :: _, _ =>
      throw "'--map' names a stylesheet's property; a beamer colour theme's colours name their roles"
    | [], some (src, f), maps, out =>
      pure { cfg with cmd := .themeImport src f maps.reverse, output := out }
    | [], none, _, _ => throw "'theme import' needs --beamer <file.sty> or --css <file.css>"
    | "--beamer" :: f :: rest, none, maps, out => go rest (some (.beamer, f)) maps out
    | "--css" :: f :: rest, none, maps, out => go rest (some (.css, f)) maps out
    | "--map" :: m :: rest, src, maps, out =>
      match m.splitOn "=" with
      | [n, k] => go rest src ((n.trimAscii.toString, k.trimAscii.toString) :: maps) out
      | _ => throw s!"'--map' takes name=key, got '{m}'"
    | "-o" :: o :: rest, src, maps, _ => go rest src maps (some o)
    | a :: _, _, _, _ => throw s!"unexpected argument '{a}' for 'theme import'"

/-- What the arguments read so far set. -/
private structure ArgsRead where
  cfg : Config
  cmd : Option Cmd
  hyphenWords : List String
  hyphenFile : Option String
  wantsFile : Option String

/-- Reads one argument `a` before `rest`: a configuration it settles at once, or what the
arguments set with it and the ones left. -/
private def readArg (a : String) (rest : List String) (st : ArgsRead) :
    Except String (Config ⊕ ArgsRead × { l : List String // l.length ≤ rest.length }) := do
  let mut cfg := st.cfg
  let mut cmd := st.cmd
  let mut hyphenWords := st.hyphenWords
  let mut hyphenFile := st.hyphenFile
  let mut wantsFile := st.wantsFile
  let mut left : { l : List String // l.length ≤ rest.length } := ⟨rest, Nat.le_refl _⟩
  match a with
  | "-q" | "--quiet" => cfg := { cfg with quiet := true }
  | "--porcelain" => cfg := { cfg with porcelain := true }
  | "--watch" => cfg := { cfg with watch := true }
  | "--best-effort" => cfg := { cfg with bestEffort := true }
  | "--werror" => cfg := { cfg with werror := true }
  | "-h" | "--help" => return .inl { cfg with cmd := .help }
  | "--version" => return .inl { cfg with cmd := .version }
  | "-o" | "--output" =>
    match hr : rest with
    | m :: rest' =>
      cfg := { cfg with output := some m }
      left := ⟨rest', by simp [hr]⟩
    | [] => throw "'-o' needs a file or directory"
  | "--color" =>
    match hr : rest with
    | m :: rest' =>
      let some c := colorMode m | throw s!"invalid color mode '{m}'"
      cfg := { cfg with color := c }
      left := ⟨rest', by simp [hr]⟩
    | [] => throw "'--color' needs a mode: auto | always | never"
  | "--emit" =>
    throw "'--emit' is not a flag; the document declares what to build: \\output{ formats = pdf, html, md }"
  | "theme" =>
    if cmd.isNone && wantsFile.isNone then return .inl (← themeImportArgs cfg rest)
    throw "unexpected argument 'theme'"
  | "--css" =>
    throw "'--css' is not a flag; the document declares its stylesheet: \\output{ css = own | bulma | none }"
  | "--math-boundary" =>
    match hr : rest with
    | m :: rest' =>
      cfg := { cfg with mathBoundary := some m }
      left := ⟨rest', by simp [hr]⟩
    | [] => throw "'--math-boundary' needs a math renderer's script file"
  | "--font-dir" =>
    match hr : rest with
    | m :: rest' =>
      cfg := { cfg with fontDirs := cfg.fontDirs.push m }
      left := ⟨rest', by simp [hr]⟩
    | [] => throw "'--font-dir' needs a directory"
  | "--file" =>
    match cmd, hr : rest with
    | some (.hyphenate _ _), f :: rest' =>
      hyphenFile := some f
      left := ⟨rest', by simp [hr]⟩
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
          if (LeanTex.Core.Ir.Surface.ofInput? a).isSome then
            cmd := some (.build a)
          else if a.toList.contains '.' || a.toList.contains '/' then
            throw s!"'{a}' is not a document leantex reads: {inputKinds}"
          else
            throw s!"unknown command '{a}'"
  return .inr (⟨cfg, cmd, hyphenWords, hyphenFile, wantsFile⟩, left)

private def readArgs (args : List String) (st : ArgsRead) : Except String (Config ⊕ ArgsRead) :=
  match args with
  | [] => pure (.inr st)
  | a :: rest => do
    match ← readArg a rest st with
    | .inl cfg => pure (.inl cfg)
    | .inr (st, ⟨left, h⟩) =>
      have : left.length < (a :: rest).length := by simp; omega
      readArgs left st
termination_by args.length

public def parse (argv : List String) : Except String Config := do
  let st ← match ← readArgs argv ⟨{ cmd := .help }, none, [], none, none⟩ with
    | .inl cfg => return cfg
    | .inr st => pure st
  let cfg := st.cfg
  let cmd := st.cmd
  let hyphenWords := st.hyphenWords
  let hyphenFile := st.hyphenFile
  let wantsFile := st.wantsFile
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

/-- Every backend, in listing order. -/
public def Emit.all : List Emit := [.pdf, .html, .md]

public theorem Emit.all_complete (e : Emit) : e ∈ Emit.all := by
  cases e <;> simp [Emit.all]

/-- The backend whose extension ends the output name. -/
public def emitOfPath (o : String) : Option Emit :=
  Emit.all.find? fun e => o.endsWith ("." ++ e.ext)

/-- Every backend's extension, as a refusal lists them. -/
public def Emit.extensions : String :=
  match (Emit.all.map fun e => "'." ++ e.ext ++ "'").reverse with
  | [] => ""
  | [one] => one
  | last :: rest => ", ".intercalate rest.reverse ++ " or " ++ last

/-- Backends to run: the output name (`-o out.html`) > the document's
`\output{ formats = ... }` > PDF. -/
public def Config.effectiveEmit (cfg : Config) (docFormats : Array String) : Array Emit :=
  if let some e := cfg.output.bind emitOfPath then #[e]
  else
    let ds := docFormats.filterMap fun f => Emit.all.find? (·.ext == f)
    if ds.isEmpty then #[.pdf] else ds

/-- The stylesheet the document's `\output{ css = ... }` names, or the default. -/
public def cssFor (docCss : Option String) : CssChoice :=
  (docCss.bind cssChoice).getD .own

/-- Flags are not arguments to the artifact: configurations agreeing on `-o` and
`--math-boundary` make the same backend decisions. -/
public theorem artifact_flag_free (cfg cfg' : Config)
    (ho : cfg.output = cfg'.output) (hm : cfg.mathBoundary = cfg'.mathBoundary)
    (docFormats : Array String) :
    (cfg.effectiveEmit docFormats, cfg.mathBoundary)
      = (cfg'.effectiveEmit docFormats, cfg'.mathBoundary) := by
  simp only [Config.effectiveEmit, ho, hm]

/-- Where backend `e` writes: into a directory under the source's stem, to `output` when it
names `e`'s extension, else beside the source. -/
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

/-- The exit code: errors first, then failed assertions, then warnings under `--werror`. -/
public def exitFor (errors assertFailures warnings : Nat) (werror : Bool) : UInt32 :=
  if errors > 0 then 1
  else if assertFailures > 0 then 2
  else if werror && warnings > 0 then 1
  else 0

public def helpText : String :=
  "leantex — compile a .tex, .md or code file to PDF or HTML, fast, with no setup

usage: leantex <file> [flags] · leantex <command> [args]

examples:
  leantex doc.tex                 build doc.pdf beside the source
  leantex doc.tex -o out.html     the output name picks the backend
  leantex doc.tex -o build/       write build/doc.pdf
  leantex doc.tex --watch         rebuild on every change
  leantex Foo.lean -o Foo.html    a .md, or a Lean, Python, shell, C, C++, Rust or
                                  Java file, reads as a document too

a document declares what to build — \\output{ formats = pdf, html } — so
the command line stays bare: flags say where output lands and how the run
reports, not what the artifact is.

commands:
  build <file>            same as `leantex <file>`
  dump <file>             print the elaborated document structure (debugging)
  hyphenate <word>...     show hyphenation points (--file <path> for a list)
  fonts                   list the font families leantex can see
  themes                  list the built-in theme bundles (\\theme{name})
  theme import --beamer <file.sty> | --css <file.css> [--map name=key]...
                          write a theme file (\\palette) from a beamer colour
                          theme or a stylesheet's custom properties
  version · help

flags:
  -o, --output <path>     output file (.pdf | .html | .md) or directory
  --watch                 rebuild when the source changes (Ctrl-C stops)
  --best-effort           accept every loss (as \\allow of every code); the
                          summary prints what was accepted
  --werror                exit 1 when any warning was emitted; output is
                          still written, and accepted losses (\\allow,
                          --best-effort) and notes never count
  --math-boundary <file>  carry a math renderer's script inline in HTML output
  --font-dir <d>          also look for fonts here (repeatable)
  -q, --quiet             errors only
  -v -vv -vvv             phases · decisions · trace (on stderr)
  --porcelain             JSONL events on stdout, for machines
  --color <m>             auto | always | never (NO_COLOR respected)

exit codes: 0 ok · 1 document errors (with --werror, warnings too) · 2 assertions failed · 3 usage · 4 internal"

end LeanTex.Cli
