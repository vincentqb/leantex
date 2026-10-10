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
phase's repeats of one loss print one line carrying the count, `-v` prints
every site, porcelain keeps every site, and the counts add up to the
records. Every word here is invented. -/

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
  t "a listing key's sites carry the key as their subject"
    (w0110.all (·.subject == some "lstopt:zzfoldkey"))
  t "the census counts a listing key's sites on its first record"
    ((w0110.map (·.sites)).toList == [5, 0, 0, 0, 0])
  let (err, _, r) ← sink plain #[] ds
  t s!"a listing key repeated at five listings prints one warning ({(warningLines err "W0110").length})"
    ((warningLines err "W0110").length == 1 && (headLines err "W0110").length == 1)
  t "the line it prints carries the five sites"
    ((warningLines err "W0110").all (hasStr · "(5 sites)"))
  t "the repeat sites are notes the completion line counts" (r.notes ≥ 4)
  let (verbose, _, _) ← sink { plain with verbosity := 1 } #[] ds
  t "-v prints every site, one warning and four notes"
    ((headLines verbose "W0110").length == 5 && (warningLines verbose "W0110").length == 1)
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] ds
  t "porcelain keeps every site, the first carrying the count"
    ((porcelainRows porcelain "W0110").map (·.1) == [5, 0, 0, 0, 0])
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
  t "a repeat is one warning under --werror, as a census repeat is"
    (r.warnings == 2 && r.notes == 3)
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] (same.push other)
  t "porcelain: the counts add up to the records"
    (((porcelainRows porcelain "W0110").map (·.1)).sum == 5 &&
      (porcelainRows porcelain "W0110").length == 5)
  t "porcelain: the later sites read note, the first warning"
    ((porcelainRows porcelain "W0110").map (·.2) ==
      ["warning", "note", "note", "note", "warning"])
  -- A repeat at another output scope is another loss.
  let scopes := (same.map fun d => { d with output := some .pdf }).push
    (Diag.of .W0110 "the zzsink option is not honoured; ignored" (span 3) (output := some .html))
  let (err, _, _) ← sink plain #[] scopes
  t "a repeat at another output scope keeps its own line"
    ((warningLines err "W0110").length == 2)
  -- An error is never folded: each site fails the build and prints.
  let errs := (List.range 3).toArray.map fun k => Diag.of .E0304 "a zzmissing argument" (span k)
  let (err, _, r) ← sink plain #[] errs
  t "a repeated error prints at every site and counts every site"
    ((headLines err "E0304").length == 3 && r.errors == 3)
  -- Acceptance reads the folded phase, as it reads a census repeat.
  let (err, _, r) ← sink plain #["W0110"] (same.push other)
  t "an accepted repeat prints nothing and is accepted once per loss"
    ((headLines err "W0110").isEmpty && r.accepted.size == 2 && r.warnings == 0)
  -- The law the theorems state, read off the folded records.
  let folded := Diag.foldRepeats (same.push other ++ errs ++ ds)
  t "folding keeps every record, in order, rewriting only counts and demotion"
    (folded.size == (same.push other ++ errs ++ ds).size &&
      (folded.zip (same.push other ++ errs ++ ds)).all fun (f, d) =>
        { f with sites := d.sites }.demote == d.demote)
  t "folding: the sites in are the sites out"
    ((folded.toList.map (·.sites)).sum == (same.push other ++ errs ++ ds).size)
  t "folding moves no count the census wrote"
    (((Diag.foldRepeats ds).zip ds).all fun (f, d) => d.subject.isNone || f.sites == d.sites)

/-- The doors a diagnostic is made through, as their call heads read in a
stripped source, and whether each takes a subject: Elab's `diag` takes none. -/
def subjectDoors : List (String × Bool) :=
  [("diag ctx .", false), ("diagOf ctx .", true), ("say .", true), ("Diag.of .", true)]

/-- A line's indentation. -/
def indentOf (l : String) : Nat := (l.toList.takeWhile (· == ' ')).length

/-- **Every direct emission of a counted loss names it.** A degraded or
pending code is counted by its subject, at every emission or as a debt row;
the census gate reads one witness per code, and a listing option shipped as
a second door for a code whose witness was subjected, so its sites printed
one line each. Read off a stripped source: a counted code applied at a door
must name a subject within the call, by keyword or by position, or be in
`subjectDebt`; a door that takes no subject carries no counted code outside
the debt. -/
def doorOffences (src : String) : Array String := Id.run do
  let lines := ((stripNonCode src).splitOn "\n").toArray
  let mut out : Array String := #[]
  for h : i in [0:lines.size] do
    let line := lines[i]
    for (head, takes) in subjectDoors do
      for part in (line.splitOn head).drop 1 do
        let tok := String.ofList (part.toList.takeWhile Char.isAlphanum)
        let some code := DiagCode.ofString? tok | continue
        unless code.censused && !subjectDebt.contains tok do continue
        let rest := (lines.extract (i + 1) lines.size).toList.takeWhile fun l =>
          !l.trimAscii.isEmpty && indentOf l > indentOf line
        unless takes && hasStr (String.intercalate "\n" (part :: rest)) "subject" do
          out := out.push tok
  return out

def subjectDoorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut offences : Array String := #[]
  for (file, _) in ← codeSources do
    for tok in doorOffences (← IO.FS.readFile file) do
      offences := offences.push s!"{file} {tok}"
  check ref s!"every direct emission of a counted loss names its subject ({offences})"
    offences.isEmpty
  -- The scan reads what it claims to.
  let hit (src : String) : Bool := !(doorOffences src).isEmpty
  check ref "door scan: a subjectless door with a counted code is an offence"
    (hit "  diag ctx .W0110 \"m\" (some pos)\n")
  check ref "door scan: a door whose call names no subject is an offence"
    (hit "  say .W0110 \"m\" pos\n    (help := \"h\")\n")
  check ref "door scan: a door whose call names its subject on a later line is not"
    (!hit "  say .W0110 \"m\" pos\n    (subject := some \"k\")\n")
  check ref "door scan: a subject passed by position names it"
    (!hit "  Diag.of .W0110 message span (some help) (some subject)\n")
  check ref "door scan: a debt code is not an offence"
    (!hit "  diag ctx .W0311 \"m\" (some pos)\n")
  check ref "door scan: a code named in a string or a comment is not an emission"
    (!hit "  -- diag ctx .W0110\n  let s := \"say .W0110\"\n")

end Tests.DiagFold
