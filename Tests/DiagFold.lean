module

public import Tests.Support
public import Tests.Diag
import all LeanTex.Cli.Driver

public section

open LeanTex.Core LeanTex.Cli

/-! One loss, one line, on the log a run prints: a phase's repeats of one loss in the same words
print one line with their count, `-v` and porcelain keep every site, and the counts add up. -/

namespace Tests.DiagFold

/-- What the driver's sink writes for one phase: stderr, stdout and the phase's accounting. -/
def sink (cfg : Config) (allowed : Array String) (ds : Array Diag)
    (outputs : Array Diag.Output := #[.pdf, .html]) :
    IO (String × String × Resolution) := do
  let err ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let ui : Driver.Ui := {
    cfg := cfg, color := false
    errStream := IO.FS.Stream.ofBuffer err, outStream := IO.FS.Stream.ofBuffer out }
  let r ← ui.resolve allowed false ds outputs
  let text (b : IO.FS.Stream.Buffer) := String.fromUTF8? b.data |>.getD ""
  return (text (← err.get), text (← out.get), r)

/-- Does a human line carry this severity: after its location, or opening the line. -/
def severityAt (l sev : String) : Bool :=
  l.startsWith (sev ++ ": ") || hasStr l s!": {sev}: "

/-- The record lines a human log holds for a code, each with a severity and the bracketed code. -/
def headLines (log code : String) : List String :=
  (log.splitOn "\n").filter fun l =>
    ["error", "warning", "info"].any (severityAt l ·) && hasStr l s!"[{code}]"

def warningLines (log code : String) : List String :=
  (headLines log code).filter (severityAt · "warning")

/-- The porcelain records for a code: each line's `sites` (absent is 1) and severity. -/
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

/-- How a phase's log counts what it folds, read off the driver's own sink: in the same words, under
`--werror`, `-v`, porcelain and acceptance. -/
def foldChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let plain : Config := { cmd := .build "deck.tex", color := .never }
  let listing := "\\begin{lstlisting}[zzfoldkey=on]\nalpha\n\\end{lstlisting}\n\n"
  let (_, ds) := elabStr (dvDoc "\\usepackage{listings}"
    (String.join (List.replicate 5 listing)))
  let w0110 := ds.filter (·.kind == .W0110)
  t s!"a listing key's five sites are five records ({w0110.size})" (w0110.size == 5)
  t "a listing key's sites carry their words and their key as their subject"
    (w0110.all fun d => d.subject.any (·.startsWith ("lstopt:" ++ d.message ++ ":")))
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
  -- A listing arm keys its loss by its words: sites share a subject exactly when they print alike.
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
  t s!"each listing arm's words print once ({(warningLines err "W0110").length} lines)"
    ((warningLines err "W0110").length == arms.length - 1 &&
      (armDs.map (·.message)).toList.eraseDups.length == arms.length - 1 &&
      ((warningLines err "W0110").filter (hasStr · "(4 sites)")).length == 1 &&
      ((warningLines err "W0110").filter (hasStr · "(2 sites)")).length == arms.length - 2)
  let (_, siDs) := elabStr (dvDoc "\\usepackage{siunitx}"
    "One \\num[zzopt=1]{1}, two \\num[zzopt=2]{2}, three \\num[zzopt=3]{3}.")
  let siW := siDs.filter (·.kind == .W0110)
  t s!"a siunitx command's options are one loss, keyed by the command ({siW.size})"
    (siW.size == 3 && siW.all (·.subject == some "siopt:num"))
  let (err, _, _) ← sink plain #[] siDs
  t "a siunitx command's options print once, with their sites"
    ((warningLines err "W0110").length == 1 && (warningLines err "W0110").all (hasStr · "(3 sites)"))
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
  t "porcelain: the later sites read info, the first warning"
    ((porcelainRows porcelain "W0110").map (·.2) ==
      ["warning", "info", "info", "info", "warning"])
  let advised := #[Diag.of .W0110 "zzsame words" (span 1) (help := some "zzone"),
    Diag.of .W0110 "zzsame words" (span 2) (help := some "zztwo")]
  let (err, _, _) ← sink plain #[] advised
  t "the same message with different advice keeps both lines"
    ((warningLines err "W0110").length == 2)
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
  let scopes := (same.map fun d => { d with output := some .pdf }).push
    (Diag.of .W0110 "the zzsink option is not honoured; ignored" (span 3) (output := some .html))
  let (err, _, _) ← sink plain #[] scopes
  t "a repeat at another output scope keeps its own line"
    ((warningLines err "W0110").length == 2)
  let errs := (List.range 3).toArray.map fun k => Diag.of .E0304 "a zzmissing argument" (span k)
  let named := (List.range 3).toArray.map fun k =>
    Diag.of .E0304 "a zzmissing argument" (span k) (subject := some "zzarg")
  let (err, _, r) ← sink plain #[] (errs ++ named)
  t "a repeated error prints at every site and counts every site, named or not"
    ((headLines err "E0304").length == 6 && r.errors == 6)
  -- Acceptance counts each loss once: a subjectless repeat in the same words is one loss.
  let (err, _, r) ← sink plain #["W0110"] (same.push other)
  t "an accepted repeat prints nothing and is accepted once per loss"
    ((headLines err "W0110").isEmpty && Diag.acceptedLosses r.accepted == #["W0110", "W0110"] &&
      r.accepted.size == 5 && r.warnings == 0 && r.notes == 0)

  let log := same.push other ++ errs ++ named ++ boxes ++ advised ++ ds
  let folded := Diag.foldRepeats log
  t "folding keeps every record, in order, rewriting only counts and demotion"
    (folded.size == log.size &&
      (folded.zip log).all fun (f, d) => { f with sites := d.sites }.demote == d.demote)
  t "folding: the sites in are the sites out"
    ((folded.toList.map (·.sites)).sum == log.size)
  t "a shown line counts exactly what it stands for, a census loss's notes with it"
    ((List.range log.size).all fun i =>
      match folded[i]?, log[i]? with
      | some f, some d =>
        !f.severity.isWarning ||
          f.sites == (log.filter (Diag.countsOn log.toList d)).size
      | _, _ => false)
  let quiet := #[(Diag.of .W0110 "the zzquiet option is not honoured; ignored" (span 1)
      (subject := some "zzquiet")).demote,
    Diag.of .W0110 "the zzquiet option is not honoured; ignored" (span 2)
      (subject := some "zzquiet")]
  let (err, _, _) ← sink plain #[] quiet
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] quiet
  t "a loss that opens on a note still shows its warning, the loss's sites all counted"
    ((warningLines err "W0110").length == 1 && (warningLines err "W0110").all (hasStr · "deck.tex:2:1") &&
      (porcelainRows porcelain "W0110") == [(1, "info"), (1, "warning")])
  -- The line is the wording, never the census key, and a wording prints once.
  let keyed := (List.range 5).toArray.map fun k =>
    Diag.of .W0005 "overfull line" (span (k + 2))
      (subject := some s!"overfull:deck.tex:{k + 2}:1")
  let (err, _, r) ← sink plain #[] keyed
  t s!"a wording whose census keys tell its sites apart prints once ({(warningLines err "W0005").length} lines)"
    ((warningLines err "W0005").length == 1 &&
      (warningLines err "W0005").all (fun l => hasStr l "deck.tex:2:1" && hasStr l "(5 sites)") &&
      r.warnings == 1 && r.notes == 4)
  let (_, porcelain, _) ← sink { plain with porcelain := true } #[] keyed
  t "porcelain keeps every keyed site, the first carrying the count"
    ((porcelainRows porcelain "W0005").map (·.1) == [5, 0, 0, 0, 0])
  let (err, _, r) ← sink plain #["W0005"] keyed
  t s!"accepted keyed sites are each a loss accepted ({Diag.acceptedLosses r.accepted})"
    ((headLines err "W0005").isEmpty && Diag.acceptedLosses r.accepted == #["W0005", "W0005",
      "W0005", "W0005", "W0005"] && r.notes == 0 && r.warnings == 0)
  let once (key : String) (k : Nat) (first : Bool) : Diag :=
    let d := Diag.of .W0110 "the zzkeyed option is not honoured; ignored" (span k)
      (subject := some key)
    if first then d else d.demote
  let pair := #[once "zzone" 1 true, once "zzone" 2 false, once "zztwo" 3 true,
    once "zztwo" 4 false, once "zztwo" 5 false]
  let (err, _, _) ← sink plain #[] pair
  t "two constructs in one wording print one line carrying both constructs' sites"
    ((warningLines err "W0110").length == 1 &&
      (warningLines err "W0110").all (hasStr · "(5 sites)"))
  let errKeyed := (List.range 3).toArray.map fun k =>
    Diag.of .E0304 "a zzmissing argument" (span k) (subject := some s!"zzarg:{k}")
  let (err, _, r) ← sink plain #[] errKeyed
  t "an error keyed per site still prints at every site"
    ((headLines err "E0304").length == 3 && r.errors == 3)

/-- A re-flowed declared line is one W0386 per paragraph, carrying any overrun of its lines (W0005's
loss), so every line past its margin is accounted once, in the PDF's output only. -/
def reflowAccountChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some font ← loadTestFont "OpenSans-Regular.ttf"
    | t "reflow account: the face loads" false
  let fs := oneFaceOf font
  let file := "reflow.tex"
  let wide := String.ofList (List.replicate 70 'w')
  let wider := String.ofList (List.replicate 90 'w')
  let prose (n : Nat) := String.intercalate " " (List.replicate n "alpha beta gamma delta")
  let located (src : String) : Ir.Doc := (elabLocated file src).1
  let siteOf (d : Diag) := d.span.map fun s => (s.pos.line, s.pos.col)
  -- The overruns the paragraphs' re-flowed lines hold, and how far each runs past.
  let carriedOf (o : Layout.Out) : Nat :=
    o.paragraphBreaks.foldl (fun n p => p.lines.foldl (fun m l => m + l.over.size) n) 0
  let excesses (o : Layout.Out) : Array Dim.Length :=
    o.paragraphBreaks.flatMap fun p => p.lines.flatMap fun l => l.over.map (·.excess)
  let runsPast (d : Diag) : Bool := d.carries.contains .W0005
  let source := String.intercalate "\n" [
    "\\documentclass{article}", "\\page{ width = 220pt, margin = 20pt }",
    "\\begin{document}",
    "Short opening line.\\\\", prose 4 ++ ".\\\\", "Short closing line.", "",
    "Another short line.\\\\", prose 2 ++ " " ++ wide ++ " tail.\\\\", "End.", "",
    wide ++ "\\\\", "After.", "\\end{document}"]
  let doc := located source
  let out := layoutOf fs doc
  let reflows := out.diags.filter (·.kind == .W0386)
  let overfull := out.diags.filter (·.kind == .W0005)
  t s!"reflow account: each re-flowed paragraph has one W0386 at its re-flowed line ({reflows.map siteOf})"
    (reflows.map siteOf == #[some (5, 1), some (9, 1)] &&
      reflows.all fun d => d.span.any (·.file == file) && d.trigger.isNone &&
        d.detail.any (hasStr · "it ships as") &&
          (d.message == "overfull line" || d.message == "overfull measure"))
  t s!"reflow account: the re-flow that runs past the measure says so, carries it and names \
where it opens ({reflows.map (·.detail)})"
    (reflows.map runsPast == #[false, true] &&
      reflows.all (fun d => runsPast d == d.detail.any (hasStr · "past the measure") &&
        runsPast d == (d.message == "overfull measure")) &&
      (reflows[1]?.bind (·.detail)).any (hasStr · ", at 9:47"))
  t "reflow account: the porcelain record of a re-flow says what it carries"
    (reflows.all fun d =>
      hasStr (Render.porcelainDiag d) "\"carries\":[\"W0005\"]" == runsPast d)
  t s!"reflow account: W0005 names only the overrun no re-flow accounts for ({overfull.map siteOf})"
    (overfull.map siteOf == #[some (12, 1)] && overfull.all (·.trigger.isNone))
  let right := doc.page.width - doc.page.hmargin
  let past := (bodyLines out).filter fun l => l.x + l.setWidth > right + Dim.pt 3
  t s!"reflow account: the page's overruns are W0005's and the re-flows' counts ({past.size})"
    (past.size == overfull.size + carriedOf out && carriedOf out == 1 &&
      past.all (fun l => hasStr (lineText l) wide))
  let plain : Config := { cmd := .build file, color := .never }
  let (err, _, _) ← sink plain #[] out.diags
  t "reflow account: the default log names every re-flow and every overrun, located"
    ((headLines err "W0386").length == 2 && (headLines err "W0005").length == 1 &&
      (warningLines err "W0386").any (fun l => hasStr l s!"{file}:5:1") &&
      (warningLines err "W0386").any (fun l => hasStr l s!"{file}:9:1") &&
      hasStr err "overfull measure" &&
      (headLines err "W0005").all (fun l => hasStr l s!"{file}:12:1"))
  let (htmlErr, _, _) ← sink plain #[] out.diags #[.html]
  let (pdfErr, _, _) ← sink plain #[] out.diags #[.pdf]
  t "reflow account: an HTML build prints neither page loss, a PDF build both"
    ((headLines htmlErr "W0386").isEmpty && (headLines htmlErr "W0005").isEmpty &&
      (headLines pdfErr "W0386").length == 2 && (headLines pdfErr "W0005").length == 1 &&
      (reflows ++ overfull).all (·.output == some .pdf))
  let (err, _, r) ← sink plain #["W0386"] out.diags
  t s!"reflow account: accepting the re-flow accepts the overrun it carries and no other \
({Diag.acceptedLosses r.accepted})"
    ((headLines err "W0386").isEmpty && (warningLines err "W0005").length == 1 &&
      (warningLines err "W0005").all (hasStr · s!"{file}:12:1") &&
      Diag.acceptedLosses r.accepted == #["W0386", "W0386"])
  let carriedOnly := out.diags.filter fun d => d.kind != .W0005
  let (_, _, rc) ← sink plain #["W0005"] carriedOnly
  t "reflow account: an overrun a re-flow carries fires W0005, so its acceptance is not stale"
    (Diag.unfired #["W0005"] rc.fired == #[])
  let collide := String.intercalate "\n" [
    "\\documentclass{article}", "\\page{ width = 220pt, margin = 20pt }",
    "\\begin{document}",
    "Short opening line.\\\\", wide ++ " " ++ prose 2 ++ ".\\\\", "Short closing line.", "",
    "Two wide words.\\\\", wide ++ " " ++ wide ++ "\\\\", "End.", "",
    "A short line.\\\\", prose 4 ++ ".\\\\", prose 2 ++ " " ++ wide ++ ".\\\\", "Last.",
    "\\end{document}"]
  let cOut := layoutOf fs (located collide)
  let cReflows := cOut.diags.filter (·.kind == .W0386)
  t s!"reflow account: a paragraph's re-flowed lines and their overruns are one diagnostic, \
which names where each overrun opens ({cReflows.map siteOf}, {cReflows.map (·.detail)}, \
{(cOut.diags.filter (·.kind == .W0005)).map siteOf})"
    (cReflows.map siteOf == #[some (5, 1), some (9, 1), some (13, 1)] &&
      cReflows.map runsPast == #[true, true, true] &&
      (cReflows[2]?.bind (·.detail)).any (fun s =>
        hasStr s "2 declared lines ship as" && hasStr s "1 line runs past" &&
          hasStr s ", at 14:47") &&
      !cOut.diags.any (·.kind == .W0005) && siteCollisions cOut.diags == #[])
  let cRight := doc.page.width - doc.page.hmargin
  let cPast := (bodyLines cOut).filter fun l => l.x + l.setWidth > cRight + Dim.pt 3
  t s!"reflow account: the re-flows carry every overrun the page shows ({cPast.size})"
    (cPast.size == carriedOf cOut && carriedOf cOut == 4)
  let deckOf (body : List String) : Layout.Out :=
    layoutOf fs (located (String.intercalate "\n"
      (["\\documentclass{slides}", "\\begin{document}", "\\begin{frame}"] ++ body ++
        ["\\end{frame}", "\\end{document}"])))
  let deckOut := deckOf ["Opening.\\\\", prose 6 ++ ".\\\\", "Closing.", "\\pause", "", "One.",
    "\\pause", "", "Two."]
  let deckReflows := deckOut.diags.filter (·.kind == .W0386)
  t s!"reflow account: a paragraph three steps set is one W0386 ({deckOut.pages.size} pages, \
{deckReflows.map siteOf})"
    (deckOut.pages.size == 3 && deckReflows.size == 1 && deckReflows.all (siteOf · == some (5, 1)))
  let measured := deckOf ["Opening.\\\\",
    prose 2 ++ " \\alt<2>{" ++ wider ++ "}{" ++ wide ++ "} " ++ prose 1 ++ ".\\\\",
    "Closing.", "\\pause", "", "One."]
  let mReflows := measured.diags.filter (·.kind == .W0386)
  let mSteps := excesses measured
  let mMost := mSteps.foldl max 0
  t s!"reflow account: steps measuring one declared line's overrun apart are one record, at \
the most ({mSteps.map (·.toPtString)}, {mReflows.map (·.detail)})"
    (mSteps.size == 2 && mSteps[0]? != mSteps[1]? && mReflows.size == 1 &&
      mReflows.all fun d => runsPast d &&
        d.detail.any (hasStr · s!"by up to {mMost.toPtString}pt, at 5:55"))
  let onlyOne := deckOf ["Opening.\\\\",
    prose 6 ++ " \\alt<2>{" ++ wide ++ "}{short} end.\\\\", "Closing.", "\\pause", "", "One."]
  let oReflows := onlyOne.diags.filter (·.kind == .W0386)
  t s!"reflow account: a step alone running a declared line past still has the one record \
carry it ({oReflows.map (·.message)})"
    ((excesses onlyOne).size == 1 && oReflows.size == 1 &&
      oReflows.all (fun d => runsPast d && d.message == "overfull measure"))
  let shifting := deckOf ["Opening.\\\\", "\\alt<2>{Short.}{" ++ prose 6 ++ ".}\\\\",
    prose 6 ++ ".\\\\", "Closing.", "\\pause", "", "One."]
  let sReflows := shifting.diags.filter (·.kind == .W0386)
  let (sErr, _, _) ← sink plain #[] shifting.diags
  t s!"reflow account: steps re-flowing different declared lines are one record naming both \
({sReflows.map siteOf}, {sReflows.map (·.detail)})"
    (sReflows.size == 1 && sReflows.all (siteOf · == some (5, 17)) &&
      sReflows.all (fun d => d.detail.any (hasStr · "2 declared lines ship as")) &&
      (headLines sErr "W0386").length == 1 && !hasStr sErr "sites)")

/-- A stage's line or columns past its measure, overfull or re-flowed, is named in its stage's words
by an HTML build too, once per site at the furthest any step set it, as TeX's Overfull \hbox states
how far past its protrusion; a footnote's, a flow page's and a poster's are the PDF's. -/
def frameOverfullChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some font ← loadTestFont "OpenSans-Regular.ttf"
    | t "frame overfull: the face loads" false
  let fs := oneFaceOf font
  let file := "frame-overfull.tex"
  let wide := String.ofList (List.replicate 90 'w')
  let prose (n : Nat) := String.intercalate " " (List.replicate n "alpha beta gamma delta")
  let located (src : String) : Ir.Doc := (elabLocated file src).1
  let plain : Config := { cmd := .build file, color := .never }
  let deckDoc := located (String.intercalate "\n" [
    "\\documentclass{slides}", "\\begin{document}", "\\begin{frame}", "Opening.", "",
    wide ++ "\\only<2>{www}", "\\end{frame}", "\\begin{frame}", "Opening.\\\\", prose 6 ++ ".\\\\",
    "Closing.", "\\end{frame}", "\\end{document}"])
  let deck := layoutOf fs deckDoc
  let flowDoc := located (String.intercalate "\n" [
    "\\documentclass{article}", "\\page{ width = 220pt, margin = 20pt }", "\\begin{document}",
    "Opening.", "", wide, "\\end{document}"])
  let flow := layoutOf fs flowDoc
  let poster := layoutOf fs (located (String.intercalate "\n" [
    "\\documentclass{poster}", "\\begin{document}", wide ++ wide ++ wide, "\\end{document}"]))
  let overfull (o : Layout.Out) := o.diags.filter (·.kind == .W0005)
  let furthest (o : Layout.Out) (right : Dim.Length) : Dim.Length :=
    (bodyLines o).foldl (fun m l => if hasStr (lineText l) wide then max m (l.x + l.setWidth - right)
      else m) 0
  let (deckHtml, _, _) ← sink plain #[] deck.diags #[.html]
  let deckRight := deckDoc.page.width - deckDoc.page.hmargin
  t s!"frame overfull: a stage's line past its measure is one record for both artifacts, in its own \
words, at the furthest its steps set it ({(overfull deck).map (·.detail)}, \
{(furthest deck deckRight).toPtString})"
    ((overfull deck).size == 1 && (overfull deck).all fun d =>
      d.output.isNone && d.message == "overfull line for frame" &&
      d.detail == some s!"frame 1: {(furthest deck deckRight).toPtString}pt too wide")
  t "frame overfull: an HTML build of the deck prints it once"
    ((headLines deckHtml "W0005").length == 1 && hasStr deckHtml "frame 1: " &&
      hasStr deckHtml "pt too wide")
  t s!"frame overfull: a stage's re-flowed declared line is named for both artifacts \
({(deck.diags.filter (·.kind == .W0386)).map (·.output.map (·.label))})"
    ((deck.diags.filter (·.kind == .W0386)).size == 1 &&
      (deck.diags.filter (·.kind == .W0386)).all (fun d =>
        d.output.isNone && d.detail.any (·.startsWith "in frame 2: ")) &&
      (headLines deckHtml "W0386").length == 1)
  let flowRight := flowDoc.page.width - flowDoc.page.hmargin
  t s!"frame overfull: a flow page's overfull line states how far it runs and names no frame \
({(overfull flow).map (·.detail)}, {(furthest flow flowRight).toPtString})"
    ((overfull flow).size == 1 && (overfull flow).all fun d =>
      d.message == "overfull line" &&
      d.detail == some s!"{(furthest flow flowRight).toPtString}pt too wide")
  t s!"frame overfull: a poster, a face the web page re-flows, keeps its lines the PDF's \
({(overfull poster).map (·.output.map (·.label))})"
    (!(overfull poster).isEmpty && (overfull poster).all (·.output == some .pdf))
  -- A footnote, a row of columns and a section page's title past their measure, in their stage's
  -- words; the web page sets the notes apart, so theirs are the PDF's.
  let stagedDoc := located (String.intercalate "\n" [
    "\\documentclass{slides}", "\\theme{moloch}", "\\begin{document}", "\\begin{frame}",
    "Opening.\\footnote{" ++ wide ++ "}", "\\end{frame}", "\\begin{frame}",
    "\\begin{columns}\\column{0.7\\textwidth}Left words.\\column{0.7\\textwidth}Right words.",
    "\\end{columns}", "\\end{frame}", "\\section{" ++ wide ++ "}", "\\begin{frame}", "Closing.",
    "\\end{frame}", "\\end{document}"])
  let staged := layoutOf fs stagedDoc
  let said (words : String) (lead : String) := (overfull staged).filter fun d =>
    d.message.startsWith words && (d.detail.getD "").startsWith lead
  let tooWide (lead : String) (d : Diag) := (d.detail.getD "").startsWith lead &&
    (d.detail.getD "").endsWith "pt too wide"
  t s!"frame overfull: a frame's footnote past its measure says so, with its frame and how far \
({(said "overfull footnote" "").map (·.detail)})"
    ((said "overfull footnote" "frame 1: ").size == 1 &&
      (said "overfull footnote" "").all fun d => tooWide "frame 1: " d && d.output == some .pdf)
  t s!"frame overfull: columns wider together than their frame's measure overrun it in both \
artifacts, a record of their own ({(said "overfull column" "").map (·.detail)})"
    ((said "overfull column" "frame 2: ").size == 1 &&
      (said "overfull column" "").all fun d => tooWide "frame 2: " d && d.output.isNone &&
        d.subject.any (·.startsWith "columns:"))
  t s!"frame overfull: a section page's line past its measure names the section page, no frame \
({(said "overfull line" "the section page").map (·.detail)})"
    ((said "overfull line" "the section page").size == 1 &&
      (said "overfull line" "the section page").all fun d => tooWide "the section page: " d &&
        d.output.isNone && (said "overfull line" "frame").isEmpty)
  -- Protrusion hangs a line's first quote into the margin; the overrun is what runs past it.
  let zeds := String.ofList (List.replicate 90 'z')
  let protruded := layoutOf fs (located (String.intercalate "\n" [
    "\\documentclass{article}", "\\usepackage{microtype}", "\\page{ width = 220pt, margin = 20pt }",
    "\\begin{document}", "Opening.", "", "``" ++ zeds ++ " and more words after it.",
    "\\end{document}"]))
  let hung := (bodyLines protruded).filter fun l => hasStr (lineText l) zeds
  let ran := hung.foldl (fun m l => max m (l.x + l.setWidth - flowRight)) 0
  t s!"frame overfull: a protruding line states how far its ink runs past the measure, as TeX's \
margin kerns stand inside its box ({(overfull protruded).map (·.detail)}, {ran.toPtString}, \
{hung.map (·.x.toPtString)})"
    ((overfull protruded).size == 1 && hung.any (·.x < Dim.pt 20) &&
      (overfull protruded).all fun d => d.detail == some s!"{ran.toPtString}pt too wide")

/-- The doors a diagnostic is made through, by their call heads, with whether each takes a subject. -/
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

/-- Whether a call's text names a subject, by keyword with a value or by position. -/
def namesSubject (call : String) : Bool :=
  (hasStr call "subject :=" && !hasStr call "subject := none") || hasStr call "(some subject)"

/-- Every direct emission of a counted loss names its subject within the call, or its code is in
`subjectDebt`, read off a stripped source. -/
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
