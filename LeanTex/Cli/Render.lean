module

public import LeanTex.Core.Diag
import LeanTex.Core.Hex

namespace LeanTex.Cli.Render

open LeanTex.Core

private def sgr (color : Bool) (code : String) (s : String) : String :=
  if color then s!"\x1b[{code}m{s}\x1b[0m" else s

private def severityColor : Severity → String
  | .error => "1;31"
  | .warning => "1;33"
  | .note => "1;36"

/-- The bidirectional formatting characters, which reorder what a reader sees without
being seen. -/
private def bidiControl (c : Char) : Bool :=
  let n := c.toNat
  n == 0x061C || n == 0x200E || n == 0x200F || (0x202A ≤ n && n ≤ 0x202E) ||
    (0x2066 ≤ n && n ≤ 0x2069)

/-- `acc`, then `\u` and the four upper-case hexadecimal digits of `c`. -/
private def pushEscape (acc : String) (c : Char) : String :=
  acc ++ s!"\\u{Hex.digits true 4 c.toNat}"

/-- A diagnostic field for the terminal: each newline written as `newline`, and terminal
controls and bidirectional formatting characters escaped as data. -/
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
        acc ++ "\\x" ++ Hex.digits false 2 c.toNat
      else if bidiControl c then pushEscape acc c
      else acc.push c

/-- The one note a diagnostic shows: its detail, else its help, else what replaced the construct. -/
public def note? (d : Diag) : Option String :=
  let nonEmpty (s : Option String) : Option String := s.filter (!·.isEmpty)
  match nonEmpty d.detail, nonEmpty d.help, d.recovery with
  | some text, _, _ => some text
  | none, some text, _ => some text
  | none, none, some (.replacedBy text) => nonEmpty (some text)
  | none, none, _ => none

/-- One diagnostic as `file:line:col: severity: message [code]`, then at most one note line, with
no final newline; output labels appear only when the run writes several outputs. -/
public def human (color : Bool) (d : Diag) (showOutput : Bool := false) : String :=
  let location := match d.span with
    | some sp => sgr color "1" s!"{humanText "\\n" sp.file}:{sp.pos.line}:{sp.pos.col}:" ++ " "
    | none => ""
  let severity := sgr color (severityColor d.severity) (d.severity.label ++ ":")
  let scope := if showOutput then
      match d.output with
      | some output => s!" ({output.label.toUpper})"
      | none => ""
    else ""
  let count := if d.sites ≤ 1 then "" else s!" ({d.sites} sites)"
  let message := humanText "\n  " (d.message.replace "\r\n" "\n")
  let note := match note? d with
    | some text => "\n  " ++ sgr color "1" "note:" ++ " " ++
        humanText "\n    " (text.replace "\r\n" "\n")
    | none => ""
  let message := if message.isEmpty then "" else " " ++ message
  location ++ severity ++ message ++ " [" ++ d.code ++ "]" ++ scope ++ count ++ note

/-- A run's verdict line; `written` names the artifacts a failed run still wrote, and `pages`
their page count. -/
public def humanSummary (color : Bool) (file : String) (errors : Nat) (ms : Nat)
    (written : Array String := #[]) (pages : Option Nat := none) : String :=
  let file := humanText "\\n" file
  if errors == 0 then
    s!"{sgr color "1;32" "✔"} {file} ({ms} ms)"
  else
    let noun := if errors == 1 then "error" else "errors"
    let set := match pages with
      | some n => s!", {n} {if n == 1 then "page" else "pages"}"
      | none => ""
    let wrote := if written.isEmpty then "" else
      s!"; wrote {humanText "\\n" (", ".intercalate written.toList)}{set}"
    s!"{sgr color "1;31" "✖"} {file} — {errors} {noun}{wrote} ({ms} ms)"

public def humanDone (color : Bool) (file output : String) (pages : Option Nat) (ms : Nat)
    (notes : Nat := 0) : String :=
  let file := humanText "\\n" file
  let output := humanText "\\n" output
  let set := match pages with
    | some n => s!" — {n} {if n == 1 then "page" else "pages"}"
    | none => ""
  -- Notes print only under -v; the summary counts them.
  let hint := if notes == 0 then "" else
    sgr color "2" s!" · {notes} info (-v)"
  s!"{sgr color "1;32" "✔"} {file} → {output}{set} ({ms} ms){hint}"

public def humanAccepted (color : Bool) (counts : List (String × Nat)) : String :=
  let parts := counts.map fun (c, n) => if n == 1 then c else s!"{c} ×{n}"
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let noun := if total == 1 then "loss" else "losses"
  s!"{sgr color "1;33" "accepted"}: {total} {noun} ({String.intercalate ", " parts})"

/-- The `--werror` verdict, printed after the outputs were written. -/
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
        acc ++ "\\u00" ++ Hex.digits false 2 c.toNat
      else if bidiControl c then pushEscape acc c
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

/-- One diagnostic as a JSON line: `loss` its declared class, `subject` its census key,
`sites` the sites it accounts for (absent when 1), `offsets` every byte offset it names,
`detail` the site's particulars, and `carries` the codes whose losses it accounts for. -/
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
    | some t => all ++ [("trigger", jstr t.text)]
    | none => all
  let all := match d.recovery with
    | some recovery => all ++ [("recovery", recoveryJson recovery)]
    | none => all
  let all := match d.output with
    | some output => all ++ [("output", jstr output.label)]
    | none => all
  let all := match d.detail with
    | some text => all ++ [("detail", jstr text)]
    | none => all
  let all := if d.offsets.isEmpty then all
    else all ++ [("offsets", "[" ++ ",".intercalate (d.offsets.toList.map toString) ++ "]")]
  let all := if d.carries.isEmpty then all
    else all ++ [("carries", "[" ++ ",".intercalate (d.carries.map (jstr ·.code)) ++ "]")]
  obj all

/-- A `-v` phase line, its control characters spelled out as a diagnostic's are. -/
public def humanPhase (name detail : String) (ms : Nat) : String :=
  s!"{humanText "\\n" name}: {humanText "\\n" detail} ({ms} ms)"

public def porcelainPhase (name detail : String) (ms : Nat) : String :=
  obj [("event", jstr "phase"), ("name", jstr name), ("detail", jstr detail),
    ("ms", toString ms)]

/-- The `font` phase, with the face files the settled font set loaded, in its
order, and how many faces the scan it chose from found. -/
public def porcelainFontPhase (detail : String) (ms : Nat) (paths : Array String)
    (scanned : Nat) : String :=
  obj [("event", jstr "phase"), ("name", jstr "font"), ("detail", jstr detail),
    ("ms", toString ms), ("faces", "[" ++ String.intercalate "," (paths.toList.map jstr) ++ "]"),
    ("scanned", toString scanned)]

/-- A summary's cost: wall milliseconds, then the peak resident memory in KiB where
measured. -/
private def costFields (ms : Nat) (rssKiB : Option Nat) : List (String × String) :=
  ("ms", toString ms) :: (rssKiB.map fun k => [("rssKiB", toString k)]).getD []

public def porcelainSummary (file : String) (ok : Bool) (errors ms : Nat)
    (written : Array String := #[]) (rssKiB : Option Nat := none) (pages : Option Nat := none) :
    String :=
  obj ([("event", jstr "summary"), ("file", jstr file),
    ("ok", if ok then "true" else "false")] ++
    (if written.isEmpty then [] else [("output", jstr (", ".intercalate written.toList))]) ++
    (pages.map fun n => ("pages", toString n)).toList ++
    [("errors", toString errors)] ++ costFields ms rssKiB)

public def porcelainDone (file output : String) (pages : Option Nat) (ms : Nat)
    (rssKiB : Option Nat := none) : String :=
  obj ([("event", jstr "summary"), ("file", jstr file), ("ok", "true"),
    ("output", jstr output)] ++ (pages.map fun n => ("pages", toString n)).toList ++
    [("errors", "0")] ++ costFields ms rssKiB)

public def porcelainAccepted (counts : List (String × Nat)) : String :=
  let total := counts.foldl (fun t (_, n) => t + n) 0
  let codes := counts.map fun (c, n) => obj [("code", jstr c), ("count", toString n)]
  obj [("event", jstr "accepted"), ("count", toString total),
    ("codes", "[" ++ String.intercalate "," codes ++ "]")]

public def porcelainWerror (file : String) (warnings ms : Nat)
    (rssKiB : Option Nat := none) : String :=
  obj ([("event", jstr "summary"), ("file", jstr file), ("ok", "false"),
    ("errors", "0"), ("warnings", toString warnings)] ++ costFields ms rssKiB)

end LeanTex.Cli.Render
