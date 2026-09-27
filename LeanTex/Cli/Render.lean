import LeanTex.Core.Diag

namespace LeanTex.Cli.Render

open LeanTex.Core

private def sgr (color : Bool) (code : String) (s : String) : String :=
  if color then s!"\x1b[{code}m{s}\x1b[0m" else s

private def severityColor : Severity → String
  | .error => "1;31"
  | .warning => "1;33"
  | .note => "1;36"

def human (color : Bool) (d : Diag) : String :=
  let head := sgr color (severityColor d.severity) s!"{d.severity.label}[{d.code}]"
  -- A once-per-document loss shows one line, so the line carries the total:
  -- the further sites ride beside it as notes and read under -v.
  let count := if d.sites ≤ 1 then "" else sgr color "1" s!" ({d.sites} sites)"
  let base := s!"{head}: {d.message}{count}"
  let withSpan := match d.span with
    | some sp => base ++ "\n" ++ sgr color "1;34" "  --> " ++ s!"{sp.file}:{sp.pos.line}:{sp.pos.col}"
    | none => base
  match d.help with
  | some h => withSpan ++ "\n  " ++ sgr color "1" "help:" ++ " " ++ h
  | none => withSpan

def humanSummary (color : Bool) (file : String) (errors : Nat) (ms : Nat) : String :=
  if errors == 0 then
    s!"{sgr color "1;32" "✔"} {file} ({ms} ms)"
  else
    let noun := if errors == 1 then "error" else "errors"
    s!"{sgr color "1;31" "✖"} {file} — {errors} {noun} ({ms} ms)"

def humanDone (color : Bool) (file output : String) (pages ms : Nat) (notes : Nat := 0) :
    String :=
  let noun := if pages == 1 then "page" else "pages"
  -- A translated idiom is not a problem, so it does not print by default; the
  -- count says there is something to read, and -v is where to read it.
  let hint := if notes == 0 then "" else
    sgr color "2" s!" · {notes} {if notes == 1 then "note" else "notes"} (-v)"
  s!"{sgr color "1;32" "✔"} {file} → {output} — {pages} {noun} ({ms} ms){hint}"

def humanAccepted (color : Bool) (counts : List (String × Nat)) : String :=
  let parts := counts.map fun (c, n) => if n == 1 then c else s!"{c} ×{n}"
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let noun := if total == 1 then "loss" else "losses"
  s!"{sgr color "1;33" "accepted"}: {total} {noun} ({String.intercalate ", " parts})"

/-- The `--werror` verdict, printed after the outputs (which were written:
the flag changes the exit code, never the rendering). -/
def humanWerror (color : Bool) (file : String) (warnings ms : Nat) : String :=
  let noun := if warnings == 1 then "warning" else "warnings"
  s!"{sgr color "1;31" "✖"} {file} — {warnings} {noun} (--werror) ({ms} ms)"

private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c =>
      if c.toNat < 0x20 then
        let hex := "0123456789abcdef".toList
        acc ++ "\\u00" ++ String.ofList [hex[c.toNat >>> 4]!, hex[c.toNat &&& 0xF]!]
      else
        acc.push c

private def jstr (s : String) : String := "\"" ++ jsonEscape s ++ "\""

private def obj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

/-- One diagnostic as a JSON line. `loss` is the declared class, so a reader
bands without a table and without trusting `severity`, which demotion
rewrites; `subject` is the structured key a census groups by, so no
consumer has to group by message text. -/
def porcelainDiag (d : Diag) : String :=
  let base := [("event", jstr "diagnostic"), ("severity", jstr d.severity.label),
    ("code", jstr d.code), ("loss", jstr d.kind.loss.label), ("message", jstr d.message)]
  let withSpan := match d.span with
    | some sp => base ++ [("file", jstr sp.file), ("line", toString sp.pos.line),
        ("col", toString sp.pos.col)]
    | none => base
  let all := match d.help with
    | some h => withSpan ++ [("help", jstr h)]
    | none => withSpan
  let all := match d.subject with
    | some s => all ++ [("subject", jstr s)]
    | none => all
  let all := if d.sites ≤ 1 then all else all ++ [("sites", toString d.sites)]
  obj all

def porcelainPhase (name detail : String) (ms : Nat) : String :=
  obj [("event", jstr "phase"), ("name", jstr name), ("detail", jstr detail),
    ("ms", toString ms)]

def porcelainSummary (file : String) (ok : Bool) (errors ms : Nat) : String :=
  obj [("event", jstr "summary"), ("file", jstr file),
    ("ok", if ok then "true" else "false"), ("errors", toString errors),
    ("ms", toString ms)]

def porcelainDone (file output : String) (pages ms : Nat) : String :=
  obj [("event", jstr "summary"), ("file", jstr file), ("ok", "true"),
    ("output", jstr output), ("pages", toString pages), ("errors", "0"),
    ("ms", toString ms)]

def porcelainAccepted (counts : List (String × Nat)) : String :=
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let codes := counts.map fun (c, n) => obj [("code", jstr c), ("count", toString n)]
  obj [("event", jstr "accepted"), ("count", toString total),
    ("codes", "[" ++ String.intercalate "," codes ++ "]")]

def porcelainWerror (file : String) (warnings ms : Nat) : String :=
  obj [("event", jstr "summary"), ("file", jstr file), ("ok", "false"),
    ("errors", "0"), ("warnings", toString warnings), ("ms", toString ms)]

end LeanTex.Cli.Render
