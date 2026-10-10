module

public import Tests.Support
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.SlotLoss

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

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

/-- A scan record for the pick: a family, a corner and its pitch, nothing
read from a file. -/
def face (family : String) (fixed : Bool) (bold italic : Bool := false)
    (path : String := family ++ ".otf") : FontDb.Face :=
  { path, family, subfamily := "Regular", bold, italic, fixedPitch := fixed
    weight := if bold then 700 else 400 }

/-- A family's four corners, all from one file. -/
def family4 (family path : String) (fixed : Bool) : Array FontDb.Face :=
  #[face family fixed (path := path), face family fixed (bold := true) (path := path),
    face family fixed (italic := true) (path := path),
    face family fixed (bold := true) (italic := true) (path := path)]

/-- The suite's faces under the default families' names: Open Sans's four
files as the default text family, Source Code Pro as its designed
typewriter companion. -/
def relabeled : Array FontDb.Face :=
  #[face "DejaVu Sans" false (path := testFonts ++ "/OpenSans-Regular.ttf"),
    face "DejaVu Sans" false (bold := true) (path := testFonts ++ "/OpenSans-Bold.ttf"),
    face "DejaVu Sans" false (italic := true) (path := testFonts ++ "/OpenSans-Italic.ttf"),
    face "DejaVu Sans" false (bold := true) (italic := true)
      (path := testFonts ++ "/OpenSans-BoldItalic.ttf")] ++
  family4 "DejaVu Sans Mono" (testFonts ++ "/SourceCodePro-Regular.otf") true

/-- The face index a shipped run holding `needle` sets in, if one does. -/
def runFace (out : Layout.Out) (needle : String) : Option Nat :=
  (bodyLines out).findSome? fun l =>
    (lineRuns l).findSome? fun (f, s, _, _) => if hasStr s needle then some f else none

/-- **The markdown typewriter default, and its premise two builds apart.**
The default is a decision over sourced rows, never a guess; it fills the
slot only where the scan serves the companion whole and fixed-pitch; a tex
document is untouched; and with the companion and without it, one
markdown document ships its code in different faces while only the second
names W0390 — the default moves ink, it does not silence a loss. -/
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
    { withMono with faces := relabeled.filter (·.family != "DejaVu Sans Mono") }
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
  -- A tex document declares its own faces: the same scan leaves its
  -- undeclared typewriter slot to the body family, and the loss is named.
  let (texDoc, _) := elabStr (dvDoc "" "Words with \\texttt{inline code} beside them.")
  match ← assemble texDoc withMono with
  | .ok (fs, resolved, _, _) =>
    t "a tex document's undeclared typewriter slot keeps the body family"
      (fs.slotCollapsed 2 && (SlotLoss.diags resolved.fonts fs resolved
        (SlotLoss.carries #[.pdf] resolved.fontPolicy)).any (·.kind == .W0390))
  | .error d => t s!"tex fonts: the assembly succeeds ({d.message})" false

/-- The default log and the line ends of code. -/
def markdownWarningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- One warning, one line, counted.
  let three := "<details>\n<summary>Ash</summary>\nBirch\n</details>\n\n\
<details>\n<summary>Cedar</summary>\nDogwood\n</details>\n\n\
<details>\n<summary>Elm</summary>\nFir\n</details>\n"
  -- Each artifact that loses the collapse is told once, its warning
  -- carrying the three sites; the PDF loses nothing and is told nothing.
  for (o, n) in [(Diag.Output.html, 3), (.md, 3), (.pdf, 0)] do
    let folded := Diag.foldRepeats (Diag.forOutputs #[o] (dvMd three))
    let routes := folded.filter (·.subject == some "md:disclosure")
    t s!"a loss repeated three times shows the {o.label} build one warning carrying \
three sites ({routes.size})"
      (routes.size == n && (routes.filter (·.severity == .warning)).size == min n 1
        && routes.toList.map (·.sites) == (if n == 0 then [] else [3, 0, 0])
        && (routes.filter (·.severity == .note)).size == n - min n 1)
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
  -- overfull lines, each its own loss with its own fix, as TeX logs each.
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
  let shown := (Diag.foldRepeats overfull).filter (·.severity == .warning)
  t "the default log shows each overfull line, none folded into another"
    (shown.size == 4 && shown.all (·.sites == 1))
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

end Tests.MarkdownWarnings
