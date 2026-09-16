namespace LeanTex.Cli

/-- Which backends to run. -/
inductive Emit where
  | pdf
  | html
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
  deriving Repr, BEq

structure Config where
  cmd : Cmd
  verbosity : Nat := 0
  quiet : Bool := false
  porcelain : Bool := false
  color : ColorMode := .auto
  emit : Array Emit := #[.pdf]
  css : CssChoice := .own
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
      | "-h" | "--help" => return { cfg with cmd := .help }
      | "--version" => return { cfg with cmd := .version }
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
            | throw s!"invalid --emit '{m}'; expected a comma-separated list of: pdf, html"
          cfg := { cfg with emit := es }
          args := rest'
        | [] => throw "'--emit' needs a list: pdf, html"
      | "--css" =>
        match rest with
        | m :: rest' =>
          let some c := cssChoice m
            | throw s!"invalid --css '{m}'; expected own, bulma, or none"
          cfg := { cfg with css := c }
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
            | throw s!"invalid --emit '{m}'; expected a comma-separated list of: pdf, html"
          cfg := { cfg with emit := es }
        else if a.startsWith "--css=" then
          let m := (a.drop "--css=".length).toString
          let some c := cssChoice m | throw s!"invalid --css '{m}'; expected own, bulma, or none"
          cfg := { cfg with css := c }
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
            | "build" | "dump" => wantsFile := some a
            | _ => throw s!"unknown command '{a}'"
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

def helpText : String :=
  "leantex — a fast, certified, modern LaTeX-lookalike engine

usage: leantex [flags] <command>

commands:
  build <file>            compile a document to PDF
  dump <file>             print the elaborated document structure (debugging)
  hyphenate <word>...     show hyphenation points, one word per line
  hyphenate --file <path> hyphenate each word in a file
  version                 print version
  help                    show this help

flags:
  --emit <list>  backends: pdf, html (default pdf)
  --css <mode>   HTML stylesheet: own | bulma | none (default own)
  --math-boundary <tool>
                 attach a client-side math renderer to HTML output
  --font-dir <d> also look for fonts here (repeatable; see LEANTEX_FONT_PATH)
  -q, --quiet    errors only
  -v -vv -vvv    phases · decisions · trace (on stderr)
  --porcelain    JSONL events on stdout, for machines
  --color <m>    auto | always | never (NO_COLOR respected)

exit codes:
  0 ok · 1 document errors · 2 assertions failed · 3 usage · 4 internal"

end LeanTex.Cli
