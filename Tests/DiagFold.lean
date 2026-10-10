module

public import Tests.Support
public import Tests.Diag
import all LeanTex.Cli.Driver

public section

open LeanTex.Core LeanTex.Cli

/-! **One loss, one line, on the log a run prints.** A warning repeated at
many sites printed once per site when its emitter named no subject: the
census groups by subject, and the sink printed every record that was not a
note. A listing option the engine does not honour was such a loss, one line
per listing. The invariant is over what the driver's own sink writes: a
phase's repeats of one loss in the same words print one line carrying their
count, `-v` prints every site, porcelain keeps every site, and the counts add
up to the records, a loss's to its own. Every word here is invented. -/

namespace Tests.DiagFold

/-- What the driver's sink writes for one phase: stderr, stdout and the
phase's accounting. -/
def sink (cfg : Config) (allowed : Array String) (ds : Array Diag) :
    IO (String × String × Resolution) := do
  let err ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let ui : Driver.Ui := {
    cfg := cfg, color := false
    errStream := IO.FS.Stream.ofBuffer err, outStream := IO.FS.Stream.ofBuffer out }
  let r ← ui.resolve allowed false ds
  let text (b : IO.FS.Stream.Buffer) := String.fromUTF8? b.data |>.getD ""
  return (text (← err.get), text (← out.get), r)

/-- The record lines a human log holds for a code: each starts with the
severity icon and the bracketed code. -/
def headLines (log code : String) : List String :=
  (log.splitOn "\n").filter fun l =>
    (l.startsWith "⚠ " || l.startsWith "✖ " || l.startsWith "ℹ ") && hasStr l s!"[{code}]"

def warningLines (log code : String) : List String :=
  (headLines log code).filter (·.startsWith "⚠ ")

/-- The porcelain records for a code, each line's `sites` (absent is 1) and
severity. -/
def porcelainRows (log code : String) : List (Nat × String) :=
  (log.splitOn "\n").filterMap fun l =>
    if !hasStr l s!"\"code\":\"{code}\"" then none else
    let sites := match l.splitOn "\"sites\":" with
      | [_, rest] => (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat!
      | _ => 1
    let sev := match l.splitOn "\"severity\":\"" with
      | [_, rest] => String.ofList (rest.toList.takeWhile (· != '"'))
      | _ => ""
    some (sites, sev)

def span (line : Nat) : Option Span := some ⟨"deck.tex", { line, col := 1 }⟩

def foldChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let plain : Config := { cmd := .build "deck.tex", color := .never }
  -- A listing option the engine does not honour, at five listings.
  let listing := "\\begin{lstlisting}[zzfoldkey=on]\nalpha\n\\end{lstlisting}\n\n"
  let (_, ds) := elabStr (dvDoc "\\usepackage{listings}"
    (String.join (List.replicate 5 listing)))
  let w0110 := ds.filter (·.kind == .W0110)
  t s!"a listing key's five sites are five records ({w0110.size})" (w0110.size == 5)
  t "a listing key's sites carry their words as their subject"
    (w0110.all fun d => d.subject == some ("lstopt:" ++ d.message))
  t "the census counts a listing key's sites on its first record"
    ((w0110.map (·.sites)).toList == [5, 0, 0, 0, 0])
  let (err, _, _) ← sink plain #[] ds
  t s!"a listing key repeated at five listings prints one warning ({(warningLines err "W0110").length})"
    ((warningLines err "W0110").length == 1 && (headLines err "W0110").length == 1)
  t "the line it prints carries the five sites"
    ((warningLines err "W0110").all (hasStr · "(5 sites)"))
  let (verbose, _, _) ← sink { plain with verbosity := 1 } #[] ds
  t "-v prints every site, one warning and four notes"
    ((headLines verbose "W0110").length == 5 && (warningLines verbose "W0110").length == 1)
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] ds
  t "porcelain keeps every site, the first carrying the count"
    ((porcelainRows porcelain "W0110").map (·.1) == [5, 0, 0, 0, 0])
  -- Each listing arm keys its loss by its words: two sites share a subject
  -- exactly when they print the same.
  let arms := ["zzfoldkey=on", "zzfoldkey", "numbers=zzbad", "fontsize=", "fontsize={}",
    "tabsize=0", "tabsize=zz", "breaklines=zz", "basicstyle", "basicstyle=\\bfseries",
    "language={zz zz}", "style=zzstyle"]
  let armDoc := String.join ((arms ++ arms).map fun a =>
    s!"\\begin\{lstlisting}[{a}]\nalpha\n\\end\{lstlisting}\n\n")
  let armDs := (elabStr (dvDoc "\\usepackage{listings}" armDoc)).2.filter (·.kind == .W0110)
  t s!"every listing arm names its loss ({armDs.size} records)"
    (armDs.size == 2 * arms.length && armDs.all (·.subject.isSome))
  t "a listing arm's subject and its words determine each other"
    (armDs.all fun a => armDs.all fun b => (a.subject == b.subject) == (a.message == b.message))
  let (err, _, _) ← sink plain #[] (elabStr (dvDoc "\\usepackage{listings}" armDoc)).2
  -- `zzfoldkey=on` and a bare `zzfoldkey` print the same words.
  t s!"each listing arm's words print once ({(warningLines err "W0110").length} lines)"
    ((warningLines err "W0110").length == arms.length - 1 &&
      (armDs.map (·.message)).toList.eraseDups.length == arms.length - 1 &&
      ((warningLines err "W0110").filter (hasStr · "(4 sites)")).length == 1 &&
      ((warningLines err "W0110").filter (hasStr · "(2 sites)")).length == arms.length - 2)
  -- A siunitx command's option, at three sites.
  let (_, siDs) := elabStr (dvDoc "\\usepackage{siunitx}"
    "One \\num[zzopt=1]{1}, two \\num[zzopt=2]{2}, three \\num[zzopt=3]{3}.")
  let siW := siDs.filter (·.kind == .W0110)
  t s!"a siunitx command's options are one loss, keyed by the command ({siW.size})"
    (siW.size == 3 && siW.all (·.subject == some "siopt:num"))
  let (err, _, _) ← sink plain #[] siDs
  t "a siunitx command's options print once, with their sites"
    ((warningLines err "W0110").length == 1 && (warningLines err "W0110").all (hasStr · "(3 sites)"))
  -- The class, whatever the emitter: a warning repeated in the same words
  -- with no subject is one loss.
  let same := (List.range 4).toArray.map fun k =>
    Diag.of .W0110 "the zzsink option is not honoured; ignored" (span (k + 3))
  let other := Diag.of .W0110 "the zzother option is not honoured; ignored" (span 9)
  let (err, _, r) ← sink plain #[] (same.push other)
  t s!"a subjectless warning repeated in the same words prints once ({(warningLines err "W0110").length} lines)"
    ((warningLines err "W0110").length == 2 &&
      ((warningLines err "W0110").filter (hasStr · "(4 sites)")).length == 1)
  t "the line shown is the first site"
    ((warningLines err "W0110").any fun l => hasStr l "deck.tex:3:1" && hasStr l "(4 sites)")
  t "a repeat is one warning under --werror, as a census repeat is, and its sites are notes"
    (r.warnings == 2 && r.notes == 3)
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] (same.push other)
  t "porcelain: the first site carries the count and the later ones none"
    ((porcelainRows porcelain "W0110").map (·.1) == [4, 0, 0, 0, 1])
  t "porcelain: the later sites read note, the first warning"
    ((porcelainRows porcelain "W0110").map (·.2) ==
      ["warning", "note", "note", "note", "warning"])
  -- What a record says beyond its message is its words too.
  let advised := #[Diag.of .W0110 "zzsame words" (span 1) (help := some "zzone"),
    Diag.of .W0110 "zzsame words" (span 2) (help := some "zztwo")]
  let (err, _, _) ← sink plain #[] advised
  t "the same message with different advice keeps both lines"
    ((warningLines err "W0110").length == 2)
  -- One loss in different words keeps each wording, each with its own count.
  let boxes := #[Diag.of .W0110 "box keys zzalpha are not applied" (span 1) (subject := some "zzbox"),
    Diag.of .W0110 "box keys zzbeta are not applied" (span 2) (subject := some "zzbox"),
    Diag.of .W0110 "box keys zzbeta are not applied" (span 3) (subject := some "zzbox")]
  let (err, _, _) ← sink plain #[] boxes
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] boxes
  t s!"a loss's wordings each keep a line carrying their own count ({warningLines err "W0110"})"
    ((warningLines err "W0110").length == 2 &&
      (warningLines err "W0110").any (fun l => hasStr l "deck.tex:1:1" && !hasStr l "sites)") &&
      (warningLines err "W0110").any (fun l => hasStr l "deck.tex:2:1" && hasStr l "(2 sites)") &&
      (porcelainRows porcelain "W0110").map (·.1) == [1, 2, 0])
  -- A repeat at another output scope is another loss.
  let scopes := (same.map fun d => { d with output := some .pdf }).push
    (Diag.of .W0110 "the zzsink option is not honoured; ignored" (span 3) (output := some .html))
  let (err, _, _) ← sink plain #[] scopes
  t "a repeat at another output scope keeps its own line"
    ((warningLines err "W0110").length == 2)
  -- An error is never folded: each site fails the build and prints.
  let errs := (List.range 3).toArray.map fun k => Diag.of .E0304 "a zzmissing argument" (span k)
  let named := (List.range 3).toArray.map fun k =>
    Diag.of .E0304 "a zzmissing argument" (span k) (subject := some "zzarg")
  let (err, _, r) ← sink plain #[] (errs ++ named)
  t "a repeated error prints at every site and counts every site, named or not"
    ((headLines err "E0304").length == 6 && r.errors == 6)
  -- Acceptance reads the folded phase, as it reads a census repeat.
  let (err, _, r) ← sink plain #["W0110"] (same.push other)
  t "an accepted repeat prints nothing and is accepted once per loss"
    ((headLines err "W0110").isEmpty && r.accepted.size == 2 && r.warnings == 0)
  -- The law the theorems state, read off the folded records.
  let log := same.push other ++ errs ++ named ++ boxes ++ advised ++ ds
  let folded := Diag.foldRepeats log
  t "folding keeps every record, in order, rewriting only counts and demotion"
    (folded.size == log.size &&
      (folded.zip log).all fun (f, d) => { f with sites := d.sites }.demote == d.demote)
  t "folding: the sites in are the sites out"
    ((folded.toList.map (·.sites)).sum == log.size)
  t "a census loss's folded counts add up to the census's"
    (ds.all fun d => d.subject.isNone ||
      ((((Diag.foldRepeats ds).filter (Diag.sameLoss d)).map (·.sites)).toList.sum ==
        (((Diag.tallySites ds).filter (Diag.sameLoss d)).map (·.sites)).toList.sum))
  -- A loss that opens on a note keeps that record's count there, and its
  -- warning shows with its own.
  let quiet := #[(Diag.of .W0110 "the zzquiet option is not honoured; ignored" (span 1)
      (subject := some "zzquiet")).demote,
    Diag.of .W0110 "the zzquiet option is not honoured; ignored" (span 2)
      (subject := some "zzquiet")]
  let (err, _, _) ← sink plain #[] quiet
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] quiet
  t "a loss that opens on a note still shows its warning, the loss's sites all counted"
    ((warningLines err "W0110").length == 1 && (warningLines err "W0110").all (hasStr · "deck.tex:2:1") &&
      (porcelainRows porcelain "W0110") == [(1, "note"), (1, "warning")])

/-- The doors a diagnostic is made through, by their call heads, and whether
each takes a subject: a door named before its receiver (`diag ctx .`,
`diagOf s.ctx .`, `warn st .`), one applied to its code directly (`say .`,
`Diag.of .`), and a record literal (`kind := .`). Elab's `diag` and Layout's
`warn` take no subject. -/
def receiverDoors : List (String × Bool) := [("diag", false), ("diagOf", true), ("warn", false)]

def directDoors : List (String × Bool) := [("say", true), ("Diag.of", true)]

/-- A line's indentation. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- A token with the brackets that open an argument or a literal dropped. -/
def headTok (t : String) : String :=
  String.ofList (t.toList.dropWhile fun c => c == '(' || c == '[' || c == '#' || c == '{')

/-- The code a token applies (`.W0110`, `.W0110)`), if it applies one. -/
def codeOfTok (t : String) : Option String :=
  if t.startsWith "." then
    let tok := String.ofList ((t.toList.drop 1).takeWhile Char.isAlphanum)
    if isDiagCode tok then some tok else none
  else none

/-- Does a call's text name a subject: by keyword with a value, or by position? -/
def namesSubject (call : String) : Bool :=
  (hasStr call "subject :=" && !hasStr call "subject := none") || hasStr call "(some subject)"

/-- **Every direct emission of a counted loss names it.** A degraded or
pending code is counted by its subject, at every emission or as a debt row;
the census gate reads one witness per code, and a listing option shipped as
a second door for a code whose witness was subjected, so its sites printed
one line each. Read off a stripped source: a counted code applied at a door
must name a subject within the call, by keyword or by position, or be in
`subjectDebt`; a door that takes no subject carries no counted code outside
the debt. The reading is syntactic: a call's extent is its own line and the
deeper-indented lines under it, a record literal's its fields to the closing
brace, and a subject is named when the call writes one other than `none`. -/
def doorOffences (src : String) : Array String := Id.run do
  let lines := ((stripNonCode src).splitOn "\n").toArray
  let mut out : Array String := #[]
  for h : i in [0:lines.size] do
    let line := lines[i]
    let toks := ((line.splitOn " ").filter (!·.isEmpty)).toArray.map headTok
    for k in [0:toks.size] do
      let t0 := toks[k]?.getD ""
      let door : Option (String × Bool × Bool) :=
        match receiverDoors.lookup t0 with
        | some takes =>
          if (toks[k + 1]?.getD ".").startsWith "." then none
          else (toks[k + 2]?.bind codeOfTok).map (·, takes, false)
        | none =>
          match directDoors.lookup t0 with
          | some takes => (toks[k + 1]?.bind codeOfTok).map (·, takes, false)
          | none =>
            if t0 == "kind" && toks[k + 1]? == some ":=" then
              (toks[k + 2]?.bind codeOfTok).map (·, true, true)
            else none
      let some (tok, takes, literal) := door | continue
      let some code := DiagCode.ofString? tok | continue
      unless code.censused && !subjectDebt.contains tok do continue
      let below := (lines.extract (i + 1) lines.size).toList
      let rest := if literal then
          if hasStr line "}" then [] else
          let fields := below.takeWhile fun l => !l.trimAscii.isEmpty && indentOf l ≥ indentOf line
          let n := (fields.findIdx (hasStr · "}")) + 1
          fields.take n
        else below.takeWhile fun l => !l.trimAscii.isEmpty && indentOf l > indentOf line
      unless takes && namesSubject (String.intercalate "\n" (line :: rest)) do
        out := out.push tok
  return out

def subjectDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut offences : Array String := #[]
  for (file, _) in ← codeSources do
    for tok in doorOffences (← IO.FS.readFile file) do
      offences := offences.push s!"{file} {tok}"
  check ref s!"every direct emission of a counted loss names its subject ({offences})"
    offences.isEmpty
  -- The scan reads what it claims to, at each door it names.
  let hit (src : String) : Bool := !(doorOffences src).isEmpty
  let t := check ref
  t "door scan: the subjectless door, under each receiver it is called with"
    (hit "  diag ctx .W0110 \"m\" (some pos)\n" && hit "  diag s.ctx .W0110 \"m\" none\n" &&
      hit "  (diag ctx' .W0110 \"m\" none)\n" && hit "  warn st .W0110 \"m\"\n")
  t "door scan: a subject-taking door whose call names none"
    (hit "  say .W0110 \"m\" pos\n    (help := \"h\")\n" &&
      hit "  diagOf ctx .W0110 \"m\" (some pos)\n" &&
      hit "  ds.push (Diag.of .W0110 \"m\" (span := sp))\n" &&
      hit "  say .W0110 \"m\" pos (subject := none)\n")
  t "door scan: a call naming its subject on a later line, by keyword or position"
    (!hit "  say .W0110 \"m\" pos\n    (subject := some \"k\")\n" &&
      !hit "  #[Diag.of .W0110 message span (some help) (some subject)]\n" &&
      !hit "  diagOf s.ctx .W0110 \"m\" (some pos) (subject := key)\n")
  t "door scan: a record literal names its subject among its fields, or is an offence"
    (hit "  ds.push {\n    kind := .W0110\n    message := \"m\" }\n" &&
      !hit "  ds.push {\n    kind := .W0110\n    message := \"m\"\n    subject := some k }\n" &&
      hit "  ds.push {\n    kind := .W0110\n    message := \"m\" }\n  ds.push {\n    kind := .W0110\n    subject := some k }\n")
  t "door scan: a debt code, an uncounted code and an accumulator are not offences"
    (!hit "  diag ctx .W0311 \"m\" (some pos)\n" && !hit "  diag ctx .W0350 \"m\" (some pos)\n" &&
      !hit "  st.diag .W0334 \"m\"\n")
  t "door scan: a code named in a string or a comment is not an emission"
    (!hit "  -- diag ctx .W0110\n  let s := \"say .W0110\"\n")

end Tests.DiagFold
