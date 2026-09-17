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
  let base := s!"{head}: {d.message}"
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

def porcelainDiag (d : Diag) : String :=
  let base := [("event", jstr "diagnostic"), ("severity", jstr d.severity.label),
    ("code", jstr d.code), ("message", jstr d.message)]
  let withSpan := match d.span with
    | some sp => base ++ [("file", jstr sp.file), ("line", toString sp.pos.line),
        ("col", toString sp.pos.col)]
    | none => base
  let all := match d.help with
    | some h => withSpan ++ [("help", jstr h)]
    | none => withSpan
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

end LeanTex.Cli.Render
