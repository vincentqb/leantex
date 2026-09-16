namespace LeanTex.Cli

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
  deriving Repr, BEq

structure Config where
  cmd : Cmd
  verbosity : Nat := 0
  quiet : Bool := false
  porcelain : Bool := false
  color : ColorMode := .auto
  deriving Repr, BEq

private def vCount (s : String) : Option Nat :=
  match s.toList with
  | '-' :: vs => if !vs.isEmpty && vs.all (· == 'v') then some vs.length else none
  | _ => none

private def colorMode : String → Option ColorMode
  | "auto" => some .auto
  | "always" => some .always
  | "never" => some .never
  | _ => none

def parse (argv : List String) : Except String Config := do
  let mut cfg : Config := { cmd := .help }
  let mut cmd : Option Cmd := none
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
      | _ =>
        if let some n := vCount a then
          cfg := { cfg with verbosity := min 3 (cfg.verbosity + n) }
        else if a.startsWith "--color=" then
          let m := (a.drop "--color=".length).toString
          let some c := colorMode m | throw s!"invalid color mode '{m}'"
          cfg := { cfg with color := c }
        else if a.startsWith "-" then
          throw s!"unknown flag '{a}'"
        else
          match cmd with
          | some _ => throw s!"unexpected argument '{a}'"
          | none =>
            match a with
            | "help" => cmd := some .help
            | "version" => cmd := some .version
            | "build" | "dump" =>
              match args with
              | f :: rest' =>
                cmd := some (if a == "build" then .build f else .dump f)
                args := rest'
              | [] => throw s!"'{a}' needs a file"
            | _ => throw s!"unknown command '{a}'"
  if cfg.quiet && cfg.verbosity > 0 then
    throw "choose one of -q and -v"
  return { cfg with cmd := cmd.getD .help }

def helpText : String :=
  "leantex — a fast, certified, modern LaTeX-lookalike engine

usage: leantex [flags] <command>

commands:
  build <file>   compile a document to PDF
  dump <file>    print the elaborated document structure (debugging)
  version        print version
  help           show this help

flags:
  -q, --quiet    errors only
  -v -vv -vvv    phases · decisions · trace (on stderr)
  --porcelain    JSONL events on stdout, for machines
  --color <m>    auto | always | never (NO_COLOR respected)

exit codes:
  0 ok · 1 document errors · 2 assertions failed · 3 usage · 4 internal"

end LeanTex.Cli
