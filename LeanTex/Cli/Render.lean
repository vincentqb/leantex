module

public import LeanTex.Core.Diag

namespace LeanTex.Cli.Render

open LeanTex.Core

private def sgr (color : Bool) (code : String) (s : String) : String :=
  if color then s!"\x1b[{code}m{s}\x1b[0m" else s

private def severityColor : Severity → String
  | .error => "1;31"
  | .warning => "1;33"
  | .note => "1;36"

/-- Keep a diagnostic's continuations attached to its header. A filename
and trigger use literal newline escapes; other fields use indented continuations.
Terminal controls are data, including an escape supplied by an external tool. -/
private def humanText (newline : String) (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '\n' => acc ++ newline
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | '\u2028' => acc ++ "\\u2028"
    | '\u2029' => acc ++ "\\u2029"
    | c =>
      if c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) then
        let hex := String.ofList (Nat.toDigits 16 c.toNat)
        acc ++ "\\x" ++ (if hex.length < 2 then "0" else "") ++ hex
      else acc.push c

/-- Severity icons share the completion line's visual vocabulary. Output
labels distinguish formats only when the run requests several outputs.
Internal loss categories stay in porcelain records; codes and acceptance
policy are unchanged.

Formatting is separate from filtering, as in Python warnings and logging:
https://docs.python.org/3/library/warnings.html#warnings.formatwarning
https://docs.python.org/3/library/logging.html#formatter-objects
Loguru likewise keeps record fields, format, filtering and serialization
separate: https://loguru.readthedocs.io/en/stable/api/logger.html
Only the renderer supplies terminal styling. Message text is never a format
template. Like a Loguru callable format, newline ownership is explicit:
this returns no final newline; the CLI sink supplies exactly one. -/
public def human (color : Bool) (d : Diag) (showOutput : Bool := false) : String :=
  let icon := match d.severity with
    | .error => "✖"
    | .warning => "⚠"
    | .note => "ℹ"
  let head := sgr color (severityColor d.severity) s!"{icon} [{d.code}]"
  let scope := if showOutput then
      match d.output with
      | some output => s!" ({output.label.toUpper})"
      | none => ""
    else ""
  let location := match d.span with
    | some sp => " - " ++ sgr color "1;34"
        s!"{humanText "\\n" sp.file}:{sp.pos.line}:{sp.pos.col}"
    | none => ""
  let trigger := match d.trigger with
    | some text => if text.isEmpty then "" else " - " ++ humanText "\\n" text
    | none => ""
  -- The first carrier of a censused loss keeps its total; later sites
  -- retain their existing note/verbosity policy at the typed CLI sink.
  let count := if d.sites ≤ 1 then "" else sgr color "1" s!" ({d.sites} sites)"
  let reason := if d.message.isEmpty then "" else
    "\n  " ++ humanText "\n  " (d.message.replace "\r\n" "\n")
  let recovery := match d.recovery with
    | none => ""
    | some .ignored => "\n  ignored"
    | some .skipped => "\n  skipped"
    | some (.replacedBy text) =>
        if text.isEmpty then "\n  replaced" else
          "\n  " ++ sgr color "1" "replaced by:" ++ " " ++
            humanText "\n    " (text.replace "\r\n" "\n")
  let suggestion := match d.help with
    | some text => if text.isEmpty then "" else
        "\n  " ++ sgr color "1" "suggestion:" ++ " " ++
          humanText "\n    " (text.replace "\r\n" "\n")
    | none => ""
  head ++ scope ++ location ++ trigger ++ count ++ reason ++ recovery ++ suggestion

/-- A run's verdict line. `written` names the artifacts a failed run still
wrote, so a reader can tell them from stale ones. -/
public def humanSummary (color : Bool) (file : String) (errors : Nat) (ms : Nat)
    (written : Array String := #[]) : String :=
  let file := humanText "\\n" file
  if errors == 0 then
    s!"{sgr color "1;32" "✔"} {file} ({ms} ms)"
  else
    let noun := if errors == 1 then "error" else "errors"
    let wrote := if written.isEmpty then "" else
      s!"; wrote {humanText "\\n" (", ".intercalate written.toList)}"
    s!"{sgr color "1;31" "✖"} {file} — {errors} {noun}{wrote} ({ms} ms)"

public def humanDone (color : Bool) (file output : String) (pages ms : Nat) (notes : Nat := 0) :
    String :=
  let file := humanText "\\n" file
  let output := humanText "\\n" output
  let noun := if pages == 1 then "page" else "pages"
  -- A translated idiom is not a problem, so it does not print by default; the
  -- count says there is something to read, and -v is where to read it.
  let hint := if notes == 0 then "" else
    sgr color "2" s!" · {notes} {if notes == 1 then "note" else "notes"} (-v)"
  s!"{sgr color "1;32" "✔"} {file} → {output} — {pages} {noun} ({ms} ms){hint}"

public def humanAccepted (color : Bool) (counts : List (String × Nat)) : String :=
  let parts := counts.map fun (c, n) => if n == 1 then c else s!"{c} ×{n}"
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let noun := if total == 1 then "loss" else "losses"
  s!"{sgr color "1;33" "accepted"}: {total} {noun} ({String.intercalate ", " parts})"

/-- The `--werror` verdict, printed after the outputs (which were written:
the flag changes the exit code, never the rendering). -/
public def humanWerror (color : Bool) (file : String) (warnings ms : Nat) : String :=
  let file := humanText "\\n" file
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
    | '\u2028' => acc ++ "\\u2028"
    | '\u2029' => acc ++ "\\u2029"
    | c =>
      if c.toNat < 0x20 || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F) then
        let hex := "0123456789abcdef".toList
        acc ++ "\\u00" ++ String.ofList [hex[c.toNat >>> 4]!, hex[c.toNat &&& 0xF]!]
      else
        acc.push c

private def jstr (s : String) : String := "\"" ++ jsonEscape s ++ "\""

private def obj (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (k, v) => jstr k ++ ":" ++ v) ++ "}"

private def recoveryJson : Diag.Recovery → String
  | .ignored => obj [("kind", jstr "ignored")]
  | .skipped => obj [("kind", jstr "skipped")]
  | .replacedBy replacement =>
      obj [("kind", jstr "replacedBy"), ("replacement", jstr replacement)]

/-- One diagnostic as a JSON line. `loss` is the declared class, so a reader
bands without a table and without trusting `severity`, which demotion
rewrites; `subject` is the structured key a census groups by, so no
consumer has to group by message text. `sites` is how many of the run's
sites the line accounts for, absent when it is 1: the first line of a loss
carries them all and each later one 0, so the lines' counts add up to the
run's sites (`Diag.tallySites_sum_exact`). -/
public def porcelainDiag (d : Diag) : String :=
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
  let all := if d.sites == 1 then all else all ++ [("sites", toString d.sites)]
  let all := match d.trigger with
    | some text => all ++ [("trigger", jstr text)]
    | none => all
  let all := match d.recovery with
    | some recovery => all ++ [("recovery", recoveryJson recovery)]
    | none => all
  let all := match d.output with
    | some output => all ++ [("output", jstr output.label)]
    | none => all
  obj all

/-- A `-v` phase line. `detail` can carry a tool's own words (a version
line, a renderer's last line of standard error), so its control characters
are spelled out as a diagnostic's are. -/
public def humanPhase (name detail : String) (ms : Nat) : String :=
  s!"{humanText "\\n" name}: {humanText "\\n" detail} ({ms} ms)"

public def porcelainPhase (name detail : String) (ms : Nat) : String :=
  obj [("event", jstr "phase"), ("name", jstr name), ("detail", jstr detail),
    ("ms", toString ms)]

public def porcelainSummary (file : String) (ok : Bool) (errors ms : Nat)
    (written : Array String := #[]) : String :=
  obj ([("event", jstr "summary"), ("file", jstr file),
    ("ok", if ok then "true" else "false")] ++
    (if written.isEmpty then [] else [("output", jstr (", ".intercalate written.toList))]) ++
    [("errors", toString errors), ("ms", toString ms)])

public def porcelainDone (file output : String) (pages ms : Nat) : String :=
  obj [("event", jstr "summary"), ("file", jstr file), ("ok", "true"),
    ("output", jstr output), ("pages", toString pages), ("errors", "0"),
    ("ms", toString ms)]

public def porcelainAccepted (counts : List (String × Nat)) : String :=
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let codes := counts.map fun (c, n) => obj [("code", jstr c), ("count", toString n)]
  obj [("event", jstr "accepted"), ("count", toString total),
    ("codes", "[" ++ String.intercalate "," codes ++ "]")]

public def porcelainWerror (file : String) (warnings ms : Nat) : String :=
  obj [("event", jstr "summary"), ("file", jstr file), ("ok", "false"),
    ("errors", "0"), ("warnings", toString warnings), ("ms", toString ms)]

end LeanTex.Cli.Render
