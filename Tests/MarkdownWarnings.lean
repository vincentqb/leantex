module

public import Tests.Support
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.SlotLoss

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly FontScan

/-! **A markdown document sets its code in a typewriter face and names each
loss once.**

A markdown source declares no faces, so nothing named a typewriter family:
its code set in the proportional text face, hyphenated like prose, and every
repeat of one loss printed its own warning — two and a half thousand lines
for a handful of losses on a long generated report. The invariants are over
what ships and what the default log shows: the face the typewriter slot
resolves to through the driver's own assembly, two builds apart; the line
ends of code on `Layout.Out`; and the lines `Diag.foldRepeats` leaves at
warning and error severity. The suite's own font files stand in for the
default families under the scan records' names. Every word here is
invented. -/

namespace Tests.MarkdownWarnings

/-- The suite's faces under the default families' names: Open Sans's four
files as the default text family, Source Code Pro as its designed
typewriter companion. -/
def relabeled : Array FontDb.Face :=
  #[face "Nimbus Sans" false (path := testFonts ++ "/OpenSans-Regular.ttf"),
    face "Nimbus Sans" false (bold := true) (path := testFonts ++ "/OpenSans-Bold.ttf"),
    face "Nimbus Sans" false (italic := true) (path := testFonts ++ "/OpenSans-Italic.ttf"),
    face "Nimbus Sans" false (bold := true) (italic := true)
      (path := testFonts ++ "/OpenSans-BoldItalic.ttf")] ++
  family4 "Nimbus Mono PS" (testFonts ++ "/SourceCodePro-Regular.otf") true

/-- **The typewriter companion default, and its premise two builds apart.**
The default is a decision over sourced rows, never a guess; it fills the
slot only where the scan serves the companion whole and fixed-pitch, on
either surface; and with the companion and without it, one markdown
document ships its code in different faces while only the second names
W0390 — the default moves ink, it does not silence a loss. The platform
list's checks are `Tests.MonoDefault`'s. -/
def markdownMonoChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pick := FontDb.monoCompanion
  t "the default text family's designed companion is its markdown typewriter face"
    (pick (#[face "DejaVu Sans" false] ++ family4 "DejaVu Sans Mono" "m.ttf" true)
      "DejaVu Sans" == some "DejaVu Sans Mono")
  t "a companion missing a corner is no default"
    (pick #[face "DejaVu Sans" false, face "DejaVu Sans Mono" true] "DejaVu Sans" == none)
  t "a companion whose face is not fixed-pitch is no default"
    (pick (#[face "DejaVu Sans" false] ++ family4 "DejaVu Sans Mono" "m.ttf" false)
      "DejaVu Sans" == none)
  t "a text family with no sourced row takes no installed fixed-pitch face by guess"
    (pick (#[face "Open Sans" false] ++ family4 "Aardvark Mono" "a.ttf" true)
      "Open Sans" == none)
  t "every default text family is a decided row: a companion or no companion, never both"
    (FontDb.defaultFamilies.all fun f =>
      (FontDb.companionRow FontDb.monoCompanions f).isSome != FontDb.monoUnpaired.contains f)
  -- The driver's own assembly, over the suite's files under the default
  -- families' names.
  let cache ← FontEnv.Cache.mk'
  let withMono : FaceScan := { faces := relabeled, docDirs := [], dirs := #[], diags := #[] }
  let without : FaceScan :=
    { withMono with faces := relabeled.filter (·.family != "Nimbus Mono PS") }
  let src := "Words with `inline code` beside them.\n\n```\nfenced code\n```\n"
  let (doc, _) := elabMd src
  let assemble (d : Ir.Doc) (scan : FaceScan) :=
    buildFontSet d scan cache .settled
  match ← assemble doc withMono, ← assemble doc without with
  | .ok (fsA, docA, diagsA, _), .ok (fsB, docB, diagsB, _) =>
    let lossA := SlotLoss.diags docA.fonts fsA docA (SlotLoss.carries #[.pdf, .html] docA.fontPolicy)
    let lossB := SlotLoss.diags docB.fonts fsB docB (SlotLoss.carries #[.pdf, .html] docB.fontPolicy)
    t "markdown fonts: the typewriter slot is the companion's fixed-pitch face"
      (fsA.slotIsFixedPitch 2 && !fsA.slotCollapsed 2 && lossA.isEmpty)
    t "markdown fonts: the default substitutes no corner"
      (!diagsA.any (·.kind == .W0006))
    t "markdown fonts: without the companion the slot is the text face and W0390 names it"
      (fsB.slotCollapsed 2 && lossB.any (·.kind == .W0390) && !diagsB.any (·.kind == .W0006))
    let codeA := runFace (layoutOf fsA docA) "fenced"
    let codeB := runFace (layoutOf fsB docB) "fenced"
    t "markdown fonts: the two builds ship the code in different faces"
      (codeA == some (fsA.lookup 2 400 false) && codeB == some (fsB.lookup 0 400 false)
        && (fsA.get (fsA.lookup 2 400 false)).isFixedPitch
        && !(fsB.get (fsB.lookup 0 400 false)).isFixedPitch)
  | _, _ => t "markdown fonts: both assemblies succeed" false
  -- A tex document that declares no typewriter face takes the same
  -- default: the same scan serves its undeclared slot with the companion,
  -- and there is no loss to name.
  let (texDoc, _) := elabStr (dvDoc "" "Words with \\texttt{inline code} beside them.")
  match ← assemble texDoc withMono with
  | .ok (fs, resolved, _, _) =>
    t "a tex document's undeclared typewriter slot takes the companion as a markdown one does"
      (fs.slotIsFixedPitch 2 && !fs.slotCollapsed 2 && (SlotLoss.diags resolved.fonts fs resolved
        (SlotLoss.carries #[.pdf] resolved.fontPolicy)).isEmpty)
  | .error d => t s!"tex fonts: the assembly succeeds ({d.message})" false

/-- The default log and the line ends of code. -/
def markdownWarningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- One warning, one line, counted.
  let three := "[Ash](https://example.org/a \"Birch\")\n\n\
[Cedar](https://example.org/c \"Dogwood\")\n\n[Elm](https://example.org/e \"Fir\")\n"
  -- Each artifact is told once, its warning carrying the three sites.
  for o in [Diag.Output.html, .md, .pdf] do
    let folded := Diag.foldRepeats (Diag.forOutputs #[o] (dvMd three))
    let routes := folded.filter (·.subject == some "md:link-title")
    t s!"a loss repeated three times shows the {o.label} build one warning carrying \
three sites ({routes.size})"
      (routes.size == 3 && (routes.filter (·.severity == .warning)).size == 1
        && routes.toList.map (·.sites) == [3, 0, 0]
        && (routes.filter (·.severity == .note)).size == 2)
  let folded := Diag.foldRepeats (dvMd three)
  t "folding keeps every site in the census"
    ((folded.toList.map (·.sites)).sum == (dvMd three).size)
  -- An error is never folded: each refused site fails the build.
  let refused := "a\n\n    one\n\nb\n\n    two\n\nc\n\n    three\n"
  let errs := (Diag.foldRepeats (dvMd refused)).filter (·.kind == .E0390)
  t s!"a repeated error stays an error at every site ({errs.size})"
    (errs.size == 3 && errs.all (·.severity == .error))
  let some font ← loadTestFont "SourceCodePro-Regular.otf"
    | t "markdown log: the fixed-pitch face loads" false
  -- A typewriter run is never hyphenated, as no LaTeX typewriter family is:
  -- the text sets in one face and the code in another, so a line's last run
  -- in the code face is code, and it never ends in a hyphen the breaker put
  -- there. Long hyphenatable words in both faces make breaks likely in both.
  let some text ← loadTestFont "OpenSans-Regular.ttf"
    | t "markdown log: the text face loads" false
  let split := monoSlotOf text font
  let longWords := ["internationalization", "characterization", "institutionalization",
    "incomprehensibility", "counterrevolutionary", "representativeness"]
  let coded := String.intercalate " " ((List.range 160).map fun k =>
    let w := longWords[(k * 7 + k / 3) % longWords.length]!
    if k % 3 == 0 then "`" ++ w ++ "`" else if k % 5 == 0 then "of" else w)
  let codedDoc := (elabMd (coded ++ "\n")).1
  let codeOut := layoutOf split codedDoc (pats := Hyphen.forTag codedDoc.info.locale.tag)
  let lastRuns := (bodyLines codeOut).filterMap fun l => (lineRuns l).back?
  let textBreaks := lastRuns.filter fun (f, s, _, _) => f == 0 && s.endsWith "-"
  let codeEnds := lastRuns.filter fun (f, _, _, _) => f == 1
  t s!"a typewriter run never ends a line in a hyphen ({codeEnds.size} lines end in code, \
{textBreaks.size} text lines end hyphenated)"
    (!codeEnds.isEmpty && !textBreaks.isEmpty && codeEnds.all fun (_, s, _, _) => !s.endsWith "-")
  -- Four paragraphs, each holding one token no measure line can hold: four
  -- overfull lines, each a site of its own in the census, and one wording on
  -- the log — one warning carrying the four sites, each listed under -v.
  let wide := String.ofList (List.replicate 90 '7')
  let paras := String.intercalate "\n\n" (List.replicate 4 s!"Before {wide} after.") ++ "\n"
  -- The located document, as the driver lays it out: every overfull line
  -- names its own source line.
  let (raws, readDiags) := Md.read "t.md" paras
  let (located, _, _) := Elab.runRawsSpanned "t.md" raws readDiags
  let out := layoutOf (oneFaceOf font) located
  let overfull := out.diags.filter (·.kind == .W0005)
  t s!"every overfull line is reported at its own source line ({overfull.size})"
    (overfull.size == 4
      && (overfull.map (·.span.map (·.pos.line))).toList == [some 1, some 3, some 5, some 7]
      && (overfull.toList.filterMap (·.subject)).eraseDups.length == 4)
  let folded := Diag.foldRepeats overfull
  let shown := folded.filter (·.severity == .warning)
  t "the default log shows the four overfull lines as one warning at the first, carrying four sites"
    (shown.size == 1 && shown.all (fun d => d.sites == 4 &&
        d.span.map (·.pos.line) == some 1) &&
      (folded.filter (·.severity == .note)).size == 3)
  -- A markdown hard break is HTML's `<br>`: it ends a line and declares
  -- nothing about the line it ends. Two builds apart, the page is its tex
  -- twin's — the measure set equal, the break held, the long line before it
  -- wrapped — and only the tex twin's `\\` names W0386; LaTeX names
  -- neither.
  let longLine := String.intercalate " " (List.replicate 40 "gadget")
  let mdHard := (elabMd (longLine ++ "\\\nlast words\n")).1
  let texHard := (elabStr (dvDoc "\\page{ hmargin = 114pt }" (longLine ++ "\\\\\nlast words"))).1
  let mdOut := layoutOf split mdHard
  let texOut := layoutOf split texHard
  let texts (o : Layout.Out) := (bodyLines o).map lineText
  t s!"a markdown hard break sets its tex twin's page, and only the tex twin names W0386 ({(texts mdOut).size} lines)"
    (mdHard.page.hmargin == texHard.page.hmargin && texts mdOut == texts texOut
      && (texts mdOut).size ≥ 3 && (texts mdOut).back? == some "last words"
      && !mdOut.diags.any (·.kind == .W0386) && texOut.diags.any (·.kind == .W0386))
  -- A fenced block's code stands at its own source lines, with an info word
  -- or without one: the overrun of its first line is named at the line
  -- after the fence, column one, and the code ships as written, its first
  -- line first. Without an info word it was named on the fence's own line,
  -- past the column a verbatim opener would end at.
  let code := String.intercalate "_" (List.replicate 24 "gadget")
  let fence (src : String) : Layout.Out :=
    let (fRaws, fReads) := Md.read "f.md" src
    let (fDoc, _, _) := Elab.runRawsSpanned "f.md" fRaws fReads
    layoutOf split fDoc
  let sitesOf (o : Layout.Out) := (o.diags.filter (·.kind == .W0005)).map
    (·.span.map fun s => (s.pos.line, s.pos.col))
  for (info, label) in [("", "bare"), ("python", "python"), ("a]b", "routed")] do
    let fOut := fence s!"Prose.\n\n```{info}\n{code}\nshort\n```\n"
    let shipped := (bodyLines fOut).map lineText
    t s!"a {label} fence names its code at its own line ({sitesOf fOut})"
      (sitesOf fOut == #[some (4, 1)] && shipped.contains "short" &&
        shipped.findIdx? (hasStr · "gadget") == some 1)
  -- A fence whose code opens on a blank line keeps it, as CommonMark reads
  -- it: the page sets the blank line before the code, and the code's
  -- overrun is named at its own line, after the blank one.
  let blankOut := fence s!"Prose.\n\n```\n\n{code}\n```\n"
  let blankLines := (bodyLines blankOut).map lineText
  t s!"a fence whose code opens on a blank line ships the blank line ({sitesOf blankOut})"
    (sitesOf blankOut == #[some (5, 1)] && blankLines[0]? == some "Prose." &&
      blankLines[1]? == some "" && (blankLines[2]?.any (hasStr · "gadget")))

end Tests.MarkdownWarnings
