import Tests.Support
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.SlotLoss

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

/-! **A markdown document sets its code in a typewriter face and names each
loss once.**

A markdown source declares no faces, so nothing named a typewriter family:
its code set in the proportional text face, hyphenated like prose, and every
repeat of one loss printed its own warning — two and a half thousand lines
for a handful of losses on a long generated report. The invariants are over
what ships and what the default log shows: the face the typewriter slot
resolves to through the driver's own assembly over the suite's fonts, the
line ends of code on `Layout.Out`, and the lines `Diag.foldRepeats` leaves
at warning severity. Every word here is invented. -/

namespace Tests.MarkdownWarnings

/-- A face record for the pick: its family and whether it declares fixed
pitch, nothing read from a file. -/
def face (family : String) (fixed : Bool) : FontDb.Face :=
  { path := family ++ ".otf", family, subfamily := "Regular", bold := false
    italic := false, fixedPitch := fixed, weight := 400 }

/-- The typewriter slot, its line ends, and the default log. -/
def markdownWarningChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The pick, over face records: the companion first, then the least
  -- fixed-pitch face, and nothing when none is installed.
  let faces := #[face "DejaVu Sans" false, face "DejaVu Sans Mono" true,
    face "Aardvark Mono" true, face "Open Sans" false]
  t "an undeclared typewriter slot takes the text family's designed companion"
    ((FontDb.pickMono faces "DejaVu Sans").map (·.family) == some "DejaVu Sans Mono")
  t "with no companion row it takes the least installed fixed-pitch face"
    ((FontDb.pickMono faces "Open Sans").map (·.family) == some "Aardvark Mono")
  t "with no fixed-pitch face installed it takes none"
    ((FontDb.pickMono (faces.filter (!·.fixedPitch)) "Open Sans").isNone)
  -- The driver's own assembly over the suite's fonts: a markdown document
  -- setting code has a fixed-pitch typewriter face and no slot loss.
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FaceScan := { faces := scanned, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let src := "Words with `inline code` beside them.\n\n```\nfenced code\n```\n"
  let (doc, _) := elabMd src
  match ← buildFontSet doc scan cache .settled with
  | .error d => t s!"markdown fonts: the assembly succeeds ({d.message})" false
  | .ok (fs, resolved, _, _) =>
    t "markdown fonts: the typewriter slot is set in a fixed-pitch face"
      (fs.slotIsFixedPitch 2 && !fs.slotCollapsed 2)
    t "markdown fonts: no slot loss is reported for a markdown document"
      (SlotLoss.diags resolved.fonts fs resolved
        (SlotLoss.carries #[.pdf, .html] resolved.fontPolicy)).isEmpty
  -- A scan with no fixed-pitch face still names the loss: the default
  -- fills the slot only from what is installed.
  let proportional := { scan with faces := scanned.filter (!·.fixedPitch) }
  match ← buildFontSet doc proportional cache .settled with
  | .error d => t s!"markdown fonts: the proportional assembly succeeds ({d.message})" false
  | .ok (fs, resolved, _, _) =>
    t "markdown fonts: with no fixed-pitch face the typewriter loss is still named"
      ((SlotLoss.diags resolved.fonts fs resolved
        (SlotLoss.carries #[.pdf] resolved.fontPolicy)).any (·.kind == .W0390))
  -- The default log: one loss, one line, counted.
  let three := "<details>\n<summary>Ash</summary>\nBirch\n</details>\n\n\
<details>\n<summary>Cedar</summary>\nDogwood\n</details>\n\n\
<details>\n<summary>Elm</summary>\nFir\n</details>\n"
  let folded := Diag.foldRepeats (dvMd three)
  let routes := folded.filter (·.subject == some "md:disclosure")
  t s!"a loss repeated three times shows one warning carrying three sites ({routes.size})"
    (routes.size == 3 && (routes.filter (·.severity == .warning)).size == 1
      && routes.toList.map (·.sites) == [3, 0, 0]
      && (routes.filter (·.severity == .note)).size == 2)
  t "folding keeps every site in the census"
    ((folded.toList.map (·.sites)).sum == (dvMd three).size)
  let some font ← loadTestFont "SourceCodePro-Regular.otf"
    | t "markdown log: the fixed-pitch face loads" false
  -- A typewriter run is never hyphenated, as no LaTeX typewriter family is:
  -- the text sets in one face and the code in another, so a line's last run
  -- in the code face is code, and it never ends in a hyphen the breaker put
  -- there. Long hyphenatable words in both faces make breaks likely in both.
  let some text ← loadTestFont "OpenSans-Regular.ttf"
    | t "markdown log: the text face loads" false
  let corners (slot face : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), face), ((slot, 700, false), face),
     ((slot, 400, true), face), ((slot, 700, true), face)]
  let split : Font.FontSet :=
    { fonts := #[text, font], index := (corners 0 0 ++ corners 1 0 ++ corners 2 1).toArray }
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
  -- Four paragraphs, each holding one token no measure line can hold.
  let wide := String.ofList (List.replicate 90 '7')
  let paras := String.intercalate "\n\n" (List.replicate 4 s!"Before {wide} after.") ++ "\n"
  -- The located document, as the driver lays it out: every overfull line
  -- names its own source line.
  let (raws, readDiags) := Md.read "t.md" paras
  let (located, _, _) := Elab.runRawsSpanned "t.md" raws readDiags
  let out := layoutOf (oneFaceOf font) located
  let overfull := out.diags.filter (·.kind == .W0005)
  t s!"every overfull line is a site of one counted loss ({overfull.size})"
    (overfull.size == 4 && overfull.all (·.subject == some "line:overfull")
      && (overfull.map (·.span.map (·.pos.line))).toList == [some 1, some 3, some 5, some 7])
  let shown := (Diag.foldRepeats overfull).filter (·.severity == .warning)
  t "the default log shows the overfull lines once, carrying the count"
    (shown.size == 1 && shown.toList.map (·.sites) == [4])

end Tests.MarkdownWarnings
