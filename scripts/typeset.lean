/-
The typographic quality of the pages a document ships, committed as numbers.
Run from the repository root:

  lake env lean --run scripts/typeset.lean              regenerate the baseline
  lake env lean --run scripts/typeset.lean --check      gate against testdata/scoreboard/typeset.tsv
  lake env lean --run scripts/typeset.lean --selftest   break each judge once
  lake env lean --run scripts/typeset.lean --report     every fixture's counts, losses and worst lines
  lake env lean --run scripts/typeset.lean --report <f> one fixture's
  lake env lean --run scripts/typeset.lean --lines <f>  one fixture's lines, judged
  lake env lean --run scripts/typeset.lean --pages <f>  one fixture's pages and what ends each

A fixture is a document under `testdata/typeset/` (`.tex`, or `.md` through
the markdown reader), invented, representative of what a class or a surface
sets: an article, a report, a deck, a poster, a markdown report, and the
probes that isolate one defect each.

**What is built.** Each fixture is built as the driver builds a PDF and its
HTML page — the plan `\output{ formats = pdf, html }` declares — whatever
the fixture declares, because the tier reads both artifacts; a fixture whose
`\output` leaves one of them out is a fault. The stages are the driver's:
its reader, `\input` and `\data` beside it, one preparation, a picture's
labels measured against the provisional face and settled against the final
one, the bibliography and the reference judge, the face set by the driver's
own resolution (`FontAssembly.buildFontSet`), the images with their ledger,
layout, and the losses the plan decides (`PlanLoss`, which `Driver.build`
runs too) — over the shipped faces of `testdata/corpus/fonts` only, then the
page emitted to its typed HTML tree, in process. The page omits the label
and math measures, which shape a picture's `viewBox` and a formula's marks
and neither the faces the head ships nor a diagnostic. Hermetic: no tool
runs and no host font is scanned, so a fixture that needs a tool — a listing
in a language no built-in highlighter reads, a picture outside the rendered
subset — is a fault, and so is `LEANTEX_FONT`, which substitutes a face for
an undeclared document. A fixture the driver would refuse to ship (an error
its `\allow` does not accept, an assertion that fails) is a fault, never a
row.

**What is judged**, per fixture, as headroom (`cap - count`):

  overfull       body lines past the text area beyond their protrusion
  overflow-pt    the largest such overflow, in whole points
  off-medium     lines, paths and fills with ink off the page and its bleed
  club           a paragraph's first line alone at the foot of a page
  widow          a paragraph's last line alone at the head of a page
  page-hyphen    a page turn inside a hyphenated word
  ladder         hyphenated lines following two hyphenated lines
  runt           one-word last lines of paragraphs of two lines or more
  split-row      table rows a page break cuts
  split-block    headings, titles, captions, figures, displays a break cuts
  stranded-head  a heading, or a one-line paragraph set wholly in bold or
                 introducing a display block (a lead-in), that ends a page
                 while what it introduces opens the next
  short-page     a page the flow continues from whose body ends more than
                 three lines of prose above its floor
  fallback       text runs set in a face no text slot names
  edge-step      flush-left lines whose opening glyph hangs other than the
                 protrusion table grants
  degraded       loss sites the build names whose loss is `degraded`
  pending        loss sites the build names whose loss is `pending`
  font-dupe      font programs the HTML page ships more than once

`degraded` and `pending` count the build's own diagnostics, by site, an
accepted one included: accepting a loss quiets the report, never the fact.
Every other judge reads the artifact alone, so a W0005 naming an overfull
line never excuses it. A count reaching the cap is a fault: headroom must
stay positive for the ratchet to read it.

Blind spots, declared: `overfull` judges the text area, not a line's own
measure, which `LineOut` does not carry, so a line overrunning a list's,
a quote's or a column's narrower measure inside the area is not seen; the
paragraph judges read the galley's paragraphs only (a table cell, a note, a
float are not paragraphs here); `fallback` does not see a glyph borrowed
from another text slot's face; `short-page` and `stranded-head` know a
declared boundary only as a top-level `\newpage` or `\pagebreak`, so one
nested in a group reads as a page the flow continues from; `stranded-head`
reads bold off the face a line is set in, so a lead-in written bold and set
in a regular face (no bold face shipped) counts only by the display block it
introduces. Parity with
lualatex and the rhythm tier stay gated beside this one; this tier reads the
page, not its distance from another engine's.
-/
import scripts.Board
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.FontFix
import LeanTex.Cli.PlanLoss
import LeanTex.Core.Layout.Quality

open LeanTex.Core LeanTex.Cli Scoreboard

namespace Typeset

open LeanTex.Core.Layout.Quality

/-- Where the fixtures live, and the only faces they set in. -/
def typesetDir : System.FilePath := "testdata/typeset"
def fontsDir : System.FilePath := "testdata/corpus/fonts"

/-- The tier's headroom ceiling: a constant, since raising it would raise
every item at once. The worst count on record is the `overflow-pt` row of
the formula paragraph; `measureAll` faults any count that reaches the cap. -/
def cap : Int := 10000

/-- The plan every fixture is built under: a PDF and its HTML page. -/
def plan : Array Emit := #[.pdf, .html]

/-- One fixture, built. -/
structure Built where
  geom : Layout.Geom
  fs : Font.FontSet
  doc : Ir.Doc
  out : Layout.Out
  diags : Array Diag
  head : Array Html.Node

/-- Every fixture's file name, in name order. -/
def fixtureFiles : IO (Array String) := do
  let mut out : Array String := #[]
  for e in ← typesetDir.readDir do
    let n := e.fileName
    if n.endsWith ".tex" || n.endsWith ".md" then out := out.push n
  return out.qsort (· < ·)

/-- A fixture's item name: its file name without the extension. -/
def stem (file : String) : String :=
  ((System.FilePath.mk file).fileStem).getD file

/-- The surface reader a path's extension selects, as the driver selects it. -/
def readSurface (file src : String) : Array Parse.Raw × Array Diag :=
  if file.endsWith ".md" then Md.read file src
  else
    let (toks, lexDiags) := Lex.lex file src
    let (raws, parseDiags) := Parse.parse file toks
    (raws, lexDiags ++ parseDiags)

/-- What a document needs that only a tool supplies, in words: a listing in a
language no built-in highlighter reads, a picture outside the rendered subset. -/
def toolNeeds (doc : Ir.Doc) : Array String :=
  let listings := (ListingReply.requests doc).size
  let pictures := ((Ir.imageRequests doc).filter (·.src.startsWith Ir.picSrcPrefix)).size
  (if listings == 0 then #[] else
    #[s!"{listings} listing(s) in a language no built-in highlighter reads"]) ++
  (if pictures == 0 then #[] else #[s!"{pictures} picture(s) outside the rendered subset"])

/-- The assertions the build holds a document to, judged on the pages it
ships (`Check.all` over `Check.Shipped.ofOut`, as the driver's gate reads
them), as failure messages. An assertion over the PDF's bytes needs a
written file, which this tier does not write, so it is a failure here too. -/
def assertFailures (geom : Layout.Geom) (fs : Font.FontSet) (doc : Ir.Doc) (out : Layout.Out)
    (sourceDiags : Array Diag) : Array String :=
  if doc.asserts.isEmpty then #[] else
  let bytes := doc.asserts.filter fun a => match a.kind with
    | .fontsAllEmbedded | .pdfProfile _ => true
    | .pages _ _ | .textInArea | .minXHeight _ | .accessibilityAA => false
  let shipped := Check.Shipped.ofOut geom fs out (fontsEmbedded := true)
  let shipped := if doc.asserts.any (·.kind == .accessibilityAA) then
      { shipped with a11y := Check.pdfA11ySummary doc sourceDiags geom fs out }
    else shipped
  (bytes.map fun a => s!"{a.kind.source}: reads the PDF's bytes, which this tier does not write") ++
    (Check.all shipped doc.asserts).map (·.message)

/-- The driver's sequence over the shipped faces, for the plan's two
artifacts, with no tool and no host scan. -/
def build (cache : FontEnv.Cache) (faces : Array FontDb.Face) (file : String) :
    IO (Except String Built) := do
  let src ← IO.FS.readFile file
  let (raws, front) := readSurface file src
  let (executed, inputDiags, spliced) ← Input.expandInputs file raws
  let (raws, dataDiags) ← Input.resolveData file executed.raws
  let earlier := front ++ inputDiags ++ dataDiags
  let prepared := Elab.prepareExecuted file (executed.withRaws raws)
  let scanOf (d : Ir.Doc) : FontAssembly.FaceScan :=
    { faces, docDirs := [fontsDir.toString], dirs := d.fonts.dirs, diags := #[] }
  let pre := Elab.preambleDoc file prepared
  let wants := Elab.picWants prepared.raws
  let provisional ← if !wants.draws then pure none else
    match ← FontAssembly.buildFontSet pre (scanOf pre) cache (.provisional wants.math) with
    | .ok (fsPre, _, _, _) => pure (some (Layout.labelMetric (Layout.Geom.ofPage pre.page) fsPre))
    | .error _ => pure none
  -- `Driver.elaborate` with its phases off: one elaboration, the `.sty`
  -- records, the bibliography and the reference judge.
  let elaborate (metric : Ir.Pic.LabelMetric) :
      IO (Ir.Doc × Array Diag × Elab.ReqSpans) := do
    let (doc, ds, spans) := Elab.runPrepared file prepared earlier metric
    let ds := ds ++ spliced.map fun (sty, s, pos) => Compat.styRead (s.getD file) sty pos ds
    let (doc, bibDiags) ← Input.resolveBibliography file doc spans.bib
    return (doc, ds ++ bibDiags ++ Ir.refDiags spans.labels (Elab.ReqSpans.spanOf spans.refs) doc,
      spans)
  let (doc, elabDiags, spans) ← elaborate (provisional.getD fun _ _ => {})
  let needs := toolNeeds doc
  unless needs.isEmpty do
    return .error s!"{file}: needs a tool, and this tier runs none: {", ".intercalate needs.toList}"
  let declared := ({ cmd := .help } : Config).effectiveEmit doc.output.formats
  unless doc.output.formats.isEmpty || plan.all declared.contains do
    return .error s!"{file}: declares formats = {doc.output.formats}, and this tier builds \
and judges both a PDF and an HTML page"
  match ← FontAssembly.buildFontSet doc (scanOf doc) cache .settled with
  | .error d => return .error s!"{file}: no font set: {d.message}"
  | .ok (fs, doc, fontDiags, _) =>
    -- The settle step: elaborate again where the provisional face measured
    -- a picture's labels differently from the settled one.
    let metric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs
    let settled := match provisional with
      | some m => FontFix.agree m metric (FontFix.probes doc.body)
      | none => Elab.enginePictures doc.body == 0
    let doc ← if settled then pure doc else do
      let (doc2, _, _) ← elaborate metric
      let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
      pure (Ir.resolveMathAlphas fs.mathAlphabets family doc2).1
    let dir := (System.FilePath.mk file).parent.getD "."
    let (store, imgDiags, _) ← Hermetic.storeFor dir doc
    let ledger := PlanLoss.ledger store
    let alts := PlanLoss.pictureAlts doc spans.images store
    let imgDiags := imgDiags ++ ledger ++ alts
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom fs (Hyphen.forTag doc.info.locale.tag) doc store
    let css : HtmlDoc.CssMode := match cssFor doc.output.css with
      | .own => .own
      | .bulma => .bulma
      | .none => .none
    let cfg : HtmlDoc.Config :=
      { css, imgs := Hermetic.facedStore store
        fonts := if doc.fontPolicy == .embedded then some fs else none }
    let cfg ← match ← Publication.captureHtmlResources file cfg doc with
      | .ok c => pure c
      | .error e => return .error s!"{file}: {e}"
    let (head, _, htmlDiags) := HtmlDoc.emitTree cfg doc
    let sourceDiags := elabDiags ++ fontDiags ++ imgDiags
    let diags := Diag.forOutputs #[.pdf, .html]
      (sourceDiags ++ out.diags ++ PlanLoss.ofPlan plan fs doc ++ htmlDiags)
    let resolved := Diag.resolveAll doc.allow false diags
    if resolved.errors > 0 then
      return .error s!"{file}: {resolved.errors} error(s) stop the build: \
{(diags.filter (·.severity == .error)).toList.take 3 |>.map (·.code)}"
    let failed := assertFailures geom fs doc out (elabDiags ++ imgDiags)
    unless failed.isEmpty do
      return .error s!"{file}: an assertion fails, so the build ships nothing: \
{"; ".intercalate failed.toList}"
    return .ok { geom, fs, doc, out, diags, head }

/-- One built fixture, as the judges read it. -/
structure Fixture where
  geom : Layout.Geom
  fs : Font.FontSet
  roles : Array LeafRole
  opens : Array Nat
  pages : Array Layout.PageOut
  diags : Array Diag
  head : Array Html.Node

def Built.fixture (b : Built) : Fixture :=
  { geom := b.geom, fs := b.fs, roles := leafRoles (Struct.ofDoc (Layout.pdfView b.doc))
    opens := declaredOpenings b.doc, pages := b.out.pages, diags := b.diags, head := b.head }

/-- The loss sites a set of diagnostics names in one class: each record's
`sites`, so a folded record counts every site it carries. -/
def lossSites (l : Loss) (ds : Array Diag) : Nat :=
  ds.foldl (fun n d => if d.kind.loss == l then n + d.sites else n) 0

/-- The judges, in the order rows are written: each item's suffix, and what
it counts over a built fixture. -/
def judges : List (String × (Fixture → Nat)) := [
  ("overfull", fun f => (overflows f.geom f.pages).size),
  ("overflow-pt", fun f => maxOverflowPt f.geom f.pages),
  ("off-medium", fun f => offMediumCount f.geom f.fs f.pages),
  ("club", fun f => clubs (straddles f.roles f.pages)),
  ("widow", fun f => widows (straddles f.roles f.pages)),
  ("page-hyphen", fun f => pageHyphens (straddles f.roles f.pages)),
  ("ladder", fun f => ladderLines f.roles f.pages),
  ("runt", fun f => runts f.roles f.pages),
  ("split-row", fun f => splitRows f.roles f.pages),
  ("split-block", fun f => splitBlocks f.roles f.pages),
  ("stranded-head", fun f => strandedHeads f.fs f.roles f.opens f.pages),
  ("short-page", fun f => shortPages f.geom f.roles f.opens f.pages),
  ("fallback", fun f => fallbackRuns f.fs f.pages),
  ("edge-step", fun f => edgeSteps f.geom f.roles f.pages),
  ("degraded", fun f => lossSites .degraded f.diags),
  ("pending", fun f => lossSites .pending f.diags),
  ("font-dupe", fun f => duplicatePrograms f.head)]

/-- What one fixture's pages show, judge by judge, in row order. -/
def countsOf (f : Fixture) : List (String × Nat) :=
  judges.map fun (j, judge) => (j, judge f)

/-- A fixture's rows: `<fixture>.<judge>`, as headroom. -/
def rowsOf (name : String) (counts : List (String × Nat)) : Array Row :=
  counts.toArray.map fun (j, n) => { item := s!"{name}.{j}", value := cap - (n : Int) }

/-- The counts that leave no headroom: each reaches the cap. -/
def capFaults (measured : Array (String × List (String × Nat))) : Array String :=
  measured.foldl (fun acc (name, cs) => cs.foldl (fun acc (j, n) =>
    if (n : Int) ≥ cap then acc.push s!"{name}.{j} counts {n}, at or past the cap of {cap}: \
the headroom encoding cannot read it" else acc) acc) #[]

/-- Every fixture built and judged; a fixture that does not build, or a
count the cap cannot hold, is a fault of the run, never a row. -/
def measureAll : IO (Except (Array String) (Array (String × List (String × Nat)))) := do
  if (← IO.getEnv "LEANTEX_FONT").isSome then
    return .error #["LEANTEX_FONT is set: it substitutes a host face for an undeclared \
document, and this tier measures the shipped faces only; unset it"]
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  let mut faults : Array String := #[]
  let mut out : Array (String × List (String × Nat)) := #[]
  for f in ← fixtureFiles do
    match ← build cache faces (typesetDir / f).toString with
    | .ok b => out := out.push (stem f, countsOf b.fixture)
    | .error e => faults := faults.push e
  let capped := capFaults out
  let all := faults ++ capped
  return (if all.isEmpty then .ok out else .error all)

def tierMeasure : IO (Array String × Array Row) := do
  match ← measureAll with
  | .error faults =>
    for f in faults do IO.eprintln s!"typeset: fault: {f}"
    return (#[], #[])
  | .ok cs =>
    let total (j : String) : Nat := cs.foldl (fun n (_, c) => n + ((c.lookup j).getD 0)) 0
    let summary := ", ".intercalate (judges.map fun (j, _) => s!"{j} {total j}")
    return (#[s!"# source: {cs.size} fixtures under {typesetDir}, each built in process as a \
PDF and its HTML page over the shipped faces and judged on Layout.Out and the typed HTML tree; \
totals: {summary}"],
      cs.foldl (fun acc (n, c) => acc ++ rowsOf n c) #[])

/-- The loss sites of one class, by code: `W0005×4 W0390`. -/
def lossCensus (l : Loss) (ds : Array Diag) : String :=
  let codes := ds.foldl (fun (acc : Array (String × Nat)) d =>
    if d.kind.loss != l then acc else
    match acc.findIdx? (·.1 == d.code) with
    | some i => acc.modify i fun (c, n) => (c, n + d.sites)
    | none => acc.push (d.code, d.sites)) #[]
  " ".intercalate ((codes.qsort (·.1 < ·.1)).toList.map fun (c, n) =>
    if n == 1 then c else s!"{c}×{n}")

/-- Every fixture's counts (or one fixture's, by item name), its losses by
code, and the lines behind its overflow. -/
def report (only : Option String := none) : IO UInt32 := do
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  for f in ← fixtureFiles do
    if only.any (· != stem f) then continue
    let t0 ← IO.monoMsNow
    match ← build cache faces (typesetDir / f).toString with
    | .error e =>
      IO.println s!"{f}: fault: {e}"
    | .ok b =>
      let c := countsOf b.fixture
      IO.println s!"{stem f} ({b.out.pages.size} pages, {(← IO.monoMsNow) - t0} ms): \
{" ".intercalate (c.map fun (j, n) => s!"{j}={n}")}"
      IO.println s!"  degraded: {lossCensus .degraded b.diags}; pending: {lossCensus .pending b.diags}"
      let mut shown := 0
      for h : i in [0:b.out.pages.size] do
        for l in b.out.pages[i].lines do
          let o := overflow b.geom l
          if o > 0 && shown < 5 then
            shown := shown + 1
            let text := String.ofList (Layout.LineOut.glyphChars l)
            IO.println s!"  p{i + 1} +{(o + 65535) / 65536} pt: {text.take 72}"
  return 0

/-- A segment, spelled for a reader. -/
def segText : Layout.Seg → String
  | .run idx _ _ w gs _ m _ _ _ attr =>
    let kind := match attr with
      | .leaf k => s!"leaf {k}"
      | .block k => s!"block {k}"
      | .hyphen => "hyphen"
      | .label => "label"
      | .noteMark n => s!"note {n}"
      | .unattributed => "unattributed"
    s!"run(face {idx}, {w.toPtString} pt, {gs.size} glyphs{if m.math.isSome then ", math" else ""}, {kind})"
  | .gap w word => s!"gap({w.toPtString}{if word then ", word" else ""})"
  | .decoratedGap w word _ => s!"gap({w.toPtString}{if word then ", word" else ""}, decorated)"
  | .decoration _ w _ _ _ => s!"decoration({w.toPtString})"
  | .rule w t _ _ => s!"rule({w.toPtString} × {t.toPtString})"
  | .image _ w h => s!"image({w.toPtString} × {h.toPtString})"
  | .poly pts _ => s!"poly({pts.size} points)"

/-- Build one fixture by its item name. -/
def buildNamed (name : String) : IO (Except String Built) := do
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  let some f := (← fixtureFiles).find? (stem · == name)
    | return .error s!"no fixture '{name}' under {typesetDir}"
  build cache faces (typesetDir / f).toString

/-- One fixture's lines: where each stands, what it sets, and what the
judges make of it. -/
def lines (name : String) : IO UInt32 := do
  match ← buildNamed name with
  | .error e => IO.eprintln s!"typeset: fault: {e}"; return 1
  | .ok b =>
    let roles := leafRoles (Struct.ofDoc (Layout.pdfView b.doc))
    let steps := edgeStepLines b.geom roles b.out.pages
    let stepped (l : Layout.LineOut) : Bool :=
      steps.any fun m => m.y == l.y && m.x == l.x && m.leaf == l.leaf
    IO.println s!"faces: {b.fs.fonts.toList.map (·.psName)}; text slots {b.fs.index.toList.map (·.2) |>.eraseDups}; \
math {b.fs.math}; text area {b.geom.hmargin.toPtString}–{(b.geom.pageW - b.geom.hmargin).toPtString} pt"
    for h : i in [0:b.out.pages.size] do
      for l in b.out.pages[i].lines do
        let role := (l.leaf.bind (roles[·]?)).map (fun r => s!"{repr r.kind}") |>.getD "-"
        let marks := (if l.furniture then " furniture" else "") ++ (if l.note then " note" else "") ++
          (if l.counted then " counted" else "") ++ (if endsHyphenated l then " hyphen" else "")
        let o := overflow b.geom l
        IO.println s!"p{i + 1} y {l.y.toPtString} x {l.x.toPtString} advance {(advance l).toPtString} \
hang {l.hang.toPtString}{if o > 0 then s!" OVER {o.toPtString}" else ""}\
{if offMedium b.geom b.fs l then " OFF-MEDIUM" else ""}{if stepped l then " EDGE-STEP" else ""} \
[{role}{marks}] \
{String.ofList (Layout.LineOut.glyphChars l) |>.take 60}"
        if o > 0 then IO.println s!"    {String.intercalate " " (l.segs.toList.map segText)}"
    return 0

/-- The structure leaves a page's body sets, in line order. -/
def bodyLeaves (p : Layout.PageOut) : Array Nat :=
  (p.lines.filter fun l => !l.furniture && !l.note).filterMap (·.leaf)

/-- One fixture's pages: the leaves each sets, the room under its body, and
what the boundary judges make of the turn into the next. -/
def pagesOf (name : String) : IO UInt32 := do
  match ← buildNamed name with
  | .error e => IO.eprintln s!"typeset: fault: {e}"; return 1
  | .ok b =>
    let f := b.fixture
    let pitch := linePitch f.roles f.pages
    IO.println s!"floor {b.geom.bodyBottom.toPtString} pt; prose pitch \
{(pitch.map (·.toPtString)).getD "none"} pt; declared openings at leaves {f.opens}"
    for h : i in [0:f.pages.size] do
      let p := f.pages[i]
      let body := p.lines.filter fun (l : Layout.LineOut) => !l.furniture && !l.note
      let leaves := bodyLeaves p
      let role (k : Nat) := ((f.roles[k]?).map fun r => s!"{repr r.kind}").getD "-"
      let first := leaves.foldl min (leaves[0]?.getD 0)
      let last := leaves.foldl max 0
      let room := match pitch with
        | some pt => ((roomAt f.geom pt p).map fun (r : Dim.Sp) => s!"{r.toPtString} pt").getD "-"
        | none => "-"
      let next := match f.pages[i + 1]? with
        | some q =>
          let qLeaves := bodyLeaves q
          let opening := qLeaves.foldl min (qLeaves[0]?.getD 0)
          s!"; into p{i + 2} ({role opening}): {if flowsAcross f.opens p q then "flows on" else "breaks"}\
{if pitch.any (shortAt f.geom f.opens · p q) then ", SHORT" else ""}\
{if strandedAt f.fs f.roles f.opens f.pages p q then ", STRANDED" else ""}"
        | none => ""
      IO.println s!"p{i + 1}: {body.size} lines, leaves {first}–{last} (last {role last}), \
room {room}{next}"
    return 0


/-! ## Selftest -/

/-- A text run of `w` points setting `cs`, its advance shared by its glyphs. -/
def stRun (w : Int) (cs : String) (attr : Layout.Attribution := .leaf 0) (face : Nat := 0)
    (math : Bool := false) : Layout.Seg :=
  let n : Int := max 1 cs.length
  .run face Ir.Color.black none (Dim.pt w)
    (cs.toList.toArray.map fun c => (0, c, Dim.pt w / n)) (Dim.pt 10)
    (if math then { math := some { size := 0, ascent := 0, descent := 0, top := 0, bottom := 0 } }
     else {}) {} 0 none attr

/-- A line at `x` points on baseline `y` points. -/
def stLine (x y : Int) (segs : Array Layout.Seg) (leaf : Option Nat := some 0)
    (counted : Bool := true) : Layout.LineOut :=
  { x := Dim.pt x, y := Dim.pt y, size := Dim.pt 10, segs, setWidth := 0, leaf, counted }

/-- A page of lines. -/
def stPage (lines : Array Layout.LineOut) (origin : Option Layout.FrameOrigin := none) :
    Layout.PageOut :=
  { lines, frameOrigin := origin }

/-- A paragraph leaf, a heading leaf, a table row's two cells, three more
paragraphs and a listing: roles 0–7. -/
def stTree : Struct.Tree :=
  { children := #[.node .paragraph #[.leaf 0 (.text "p")],
                  .node (.heading .h2) #[.leaf 1 (.text "h")],
                  .node .table #[.node .row #[.node .cell #[.leaf 2 (.text "a")],
                                              .node .cell #[.leaf 3 (.text "b")]]],
                  .node .paragraph #[.leaf 4 (.text "q")],
                  .node .paragraph #[.leaf 5 (.text "r")],
                  .node .paragraph #[.leaf 6 (.text "s")],
                  .node .code #[.leaf 7 (.text "c")]] }

/-- A fixture of hand-built pages over `stTree`. -/
def stFixture (geom : Layout.Geom) (fs : Font.FontSet) (pages : Array Layout.PageOut)
    (diags : Array Diag := #[]) (head : Array Html.Node := #[]) (opens : Array Nat := #[]) :
    Fixture :=
  { geom, fs, roles := leafRoles stTree, opens, pages, diags, head }

/-- Does `s` contain `sub`? -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- A document in a scratch directory, built as a fixture is: the tier's own
sequence over the shipped faces. -/
def buildScratch (cache : FontEnv.Cache) (faces : Array FontDb.Face) (name body : String) :
    IO (Except String Built) := do
  let fonts := (← IO.currentDir) / fontsDir
  IO.FS.withTempDir fun dir => do
    let file := dir / name
    IO.FS.writeFile file (body.replace "@FONTS@" fonts.toString)
    build cache faces file.toString

def selftest : IO UInt32 := tierSelftest "typeset" fun no => do
  let geom : Layout.Geom := { pageW := Dim.pt 600, pageH := Dim.pt 800, hmargin := Dim.pt 100 }
  let words (n : Nat) : Array Layout.Seg :=
    (List.range n).toArray.flatMap fun _ => #[stRun 40 "page", .gap (Dim.pt 4) true]
  -- overfull: past the text area's right edge, whatever a diagnostic says.
  let inside := stLine 100 100 #[stRun 400 "fits"]
  let past := stLine 100 100 #[stRun 405 "runs"]
  no "overfull: a line on the measure is not overfull" (overflow geom inside == 0)
  no "overfull: a line 5 pt past the right edge overflows by 5 pt"
    (overflow geom past == Dim.pt 5)
  let out : Layout.Out := { pages := #[stPage #[past]], diags := #[Diag.of .W0005 "named"] }
  no "overfull: a line a W0005 names is counted all the same"
    (overflows geom out.pages == overflows geom #[stPage #[past]] &&
      (overflows geom out.pages).size == 1)
  no "overfull: a period hanging into the margin by its protrusion is not overfull"
    (overflow geom (stLine 100 100 #[stRun 398 "ends", stRun 3 "."]) == 0)
  no "overfull: a period hanging past its protrusion is"
    (overflow geom (stLine 100 100 #[stRun 400 "ends", stRun 3 "."]) > 0)
  no "overfull: a centred line wider than the measure overflows on the left"
    (overflow geom (stLine 97 100 #[stRun 406 "wide"]) == Dim.pt 3)
  no "overfull: furniture in the margin is not a line of the text"
    (overflow geom { stLine 20 790 #[stRun 30 "foot"] with furniture := true } == 0)
  no "overfull: a decoration's rider past the edge stands with its line"
    (overflow geom (stLine 100 100 #[.decoration .underline (Dim.pt 410) 1 0 Ir.Color.black]) == 0)
  no "overfull: a fill after the text is not ink"
    (overflow geom (stLine 100 100 #[stRun 300 "text", .gap (Dim.pt 150) false]) == 0)
  -- overflow-pt: the largest overflow, rounded up to a whole point.
  let overBy (pt : Int) := stLine 100 100 #[stRun (400 + pt) "runs"]
  no "overflow-pt: lines 5 pt and 12 pt over give 12, the larger"
    (maxOverflowPt geom #[stPage #[overBy 5, overBy 12, overBy 7]] == 12)
  no "overflow-pt: a hair past the edge is a whole point"
    (maxOverflowPt geom #[stPage #[stLine 100 100 #[.gap (Dim.pt 400) false,
      .rule (Dim.pt 1 / 10) 1 0 Ir.Color.black]]] == 1)
  no "overflow-pt: no overfull line is zero" (maxOverflowPt geom #[stPage #[inside]] == 0)
  -- off-medium: the page and its bleed hold the ink.
  let fs : Font.FontSet ← do
    match Font.parse (← IO.FS.readBinFile (fontsDir / "OpenSans-Regular.ttf").toString) with
    | .ok f => pure { fonts := #[f, f, f], index := #[((0, 400, false), 0)], math := some 2 }
    | .error e => throw (IO.userError s!"OpenSans-Regular.ttf: {e}")
  no "off-medium: ink on the page is on the medium" (!offMedium geom fs inside)
  no "off-medium: ink past the page's right edge is off it"
    (offMedium geom fs (stLine 100 100 #[stRun 520 "long"]))
  no "off-medium: inside a declared bleed it is on it"
    (!offMedium { geom with bleed := Dim.pt 30 } fs (stLine 100 100 #[stRun 520 "long"]))
  no "off-medium: below the page's bottom edge it is off it"
    (offMedium geom fs (stLine 100 805 #[stRun 50 "low"]))
  no "off-medium: a path past the edge is counted"
    (offMediumCount geom fs #[{ lines := #[], paths := #[{ path := .rect (Dim.pt 590) 0 (Dim.pt 20) (Dim.pt 5) }] }] == 1)
  let fill (x w : Int) : Layout.Fill :=
    { x := Dim.pt x, y := 0, w := Dim.pt w, h := Dim.pt 10, color := Ir.Color.black }
  no "off-medium: a fill past the edge is counted, a page ground is not"
    (offMediumCount geom fs #[{ lines := #[], fills := #[geom.ground Ir.Color.black, fill 590 20] }] == 1)
  -- club, widow, page-hyphen: a paragraph across a page boundary.
  let roles := leafRoles stTree
  no s!"roles: paragraph, heading, cells of one row: {repr roles}"
    ((roles.extract 0 4).map (·.kind) == #[.paragraph, .heading .h2, .cell, .cell] &&
      roles[2]?.bind (·.row) == roles[3]?.bind (·.row) && (roles[2]?.bind (·.row)).isSome &&
      (roles[1]?.bind (·.group)).isSome && (roles[0]?.bind (·.group)).isNone &&
      (roles[7]?.bind (·.display)).isSome && (roles[2]?.bind (·.display)).isSome &&
      (roles[0]?.bind (·.display)).isNone)
  let lineOf (y : Int) (hyph : Bool := false) (leaf : Nat := 0) :=
    stLine 100 y (words 9 ++ (if hyph then #[stRun 4 "-" .hyphen] else #[])) (leaf := some leaf)
  let a := stPage #[lineOf 700, lineOf 712 (hyph := true)]
  let b1 := stPage #[lineOf 100]
  let b3 := stPage #[lineOf 100, lineOf 112, lineOf 124]
  let club := straddles roles #[stPage #[lineOf 712], b3]
  no "club: a paragraph's first line alone at a page's foot" (clubs club == 1 && widows club == 0)
  let widow := straddles roles #[a, b1]
  no "widow: its last line alone at the next page's head" (widows widow == 1 && clubs widow == 0)
  no "page-hyphen: the page turns inside a hyphenated word" (pageHyphens widow == 1)
  no "page-hyphen: an unhyphenated turn is not counted"
    (pageHyphens (straddles roles #[stPage #[lineOf 700, lineOf 712], b1]) == 0)
  no "club: an overlay's next step continues nothing"
    (straddles roles #[stPage #[lineOf 712] (some ⟨0, 1⟩), stPage #[lineOf 100] (some ⟨0, 2⟩)]).isEmpty
  no "club: the page a step spilled onto continues it"
    ((straddles roles #[stPage #[lineOf 712] (some ⟨0, 1⟩), stPage (b3.lines) (some ⟨0, 1⟩)]).size == 1)
  no "club: a table cell is not a paragraph"
    (straddles roles #[stPage #[{ lineOf 712 with leaf := some 2 }],
      stPage #[{ lineOf 100 with leaf := some 2 }]]).isEmpty
  -- ladder: the third hyphenated line in a row.
  let ladder := stPage #[lineOf 100 true, lineOf 112 true, lineOf 124 true, lineOf 136 true,
    lineOf 148]
  no "ladder: four hyphenated lines carry two past the second" (ladderLines roles #[ladder] == 2)
  no "ladder: two hyphenated lines are not a ladder"
    (ladderLines roles #[stPage #[lineOf 100 true, lineOf 112 true, lineOf 124]] == 0)
  -- runt: a one-word last line.
  no "runt: a paragraph ending on one word"
    (runts roles #[stPage #[lineOf 100, stLine 100 112 #[stRun 30 "end."]]] == 1)
  no "runt: two words are not a runt"
    (runts roles #[stPage #[lineOf 100, stLine 100 112 (words 2)]] == 0)
  no "runt: a one-line paragraph has no last line to strand"
    (runts roles #[stPage #[stLine 100 100 #[stRun 30 "alone."]]] == 0)
  -- split-row, split-block: a row or a heading across a page break.
  let cell (k : Nat) (y : Int) := stLine 100 y #[stRun 50 "cell"] (leaf := some k)
  no "split-row: a row's cells on two pages"
    (splitRows roles #[stPage #[cell 2 700], stPage #[cell 3 100]] == 1)
  no "split-row: a row on one page is whole"
    (splitRows roles #[stPage #[cell 2 700, cell 3 700], stPage #[lineOf 100]] == 0)
  no "split-row: overlay steps repeating a row do not split it"
    (splitRows roles #[stPage #[cell 2 700, cell 3 700] (some ⟨0, 1⟩),
      stPage #[cell 2 700, cell 3 700] (some ⟨0, 2⟩)] == 0)
  no "split-block: a heading's lines on two pages"
    (splitBlocks roles #[stPage #[cell 1 712], stPage #[cell 1 100]] == 1)
  -- stranded-head: a heading, or a bold lead-in, at a page's foot.
  let boldFs : Font.FontSet ← do
    match Font.parse (← IO.FS.readBinFile (fontsDir / "OpenSans-Bold.ttf").toString) with
    | .ok f => pure { fs with fonts := fs.fonts.push f, index := fs.index.push ((0, 700, false), 3) }
    | .error e => throw (IO.userError s!"OpenSans-Bold.ttf: {e}")
  let heading := stLine 100 712 #[stRun 80 "Heading"] (leaf := some 1)
  let nextPara := stPage #[lineOf 100 (leaf := 4), lineOf 112 (leaf := 4)]
  no "stranded-head: a heading ending a page, its section opening the next"
    (strandedHeads boldFs roles #[] #[stPage #[lineOf 688, lineOf 700, heading], nextPara] == 1)
  no "stranded-head: a heading kept with its section strands nothing"
    (strandedHeads boldFs roles #[] #[stPage #[lineOf 688, lineOf 700],
      stPage #[{ heading with y := Dim.pt 100 }, lineOf 112 (leaf := 4)]] == 0)
  no "stranded-head: a declared boundary after the heading is the author's"
    (strandedHeads boldFs roles #[4] #[stPage #[lineOf 688, heading], nextPara] == 0)
  let leadIn (face : Nat) := stLine 100 712 #[stRun 80 "Lead-in." (face := face)] (leaf := some 5)
  no "stranded-head: a one-line bold paragraph ending a page is a lead-in stranded"
    (strandedHeads boldFs roles #[] #[stPage #[lineOf 700, leadIn 3],
      stPage #[lineOf 100 (leaf := 6)]] == 1)
  no "stranded-head: a one-line paragraph in the regular face before prose is not"
    (strandedHeads boldFs roles #[] #[stPage #[lineOf 700, leadIn 0],
      stPage #[lineOf 100 (leaf := 6)]] == 0)
  no "stranded-head: a one-line paragraph ending a page, the listing it introduces opening the next"
    (strandedHeads boldFs roles #[] #[stPage #[lineOf 700, leadIn 0],
      stPage #[stLine 100 100 #[stRun 200 "code"] (leaf := some 7)]] == 1)
  -- short-page: room for more than three lines of prose at a page's foot.
  let fullPage := stPage ((List.range 4).toArray.map fun (i : Nat) => lineOf (100 + 12 * (i : Int)))
  let floor : Int := 800 - 72
  no "short-page: a page ending more than three lines above its floor, the flow continuing"
    (shortPages geom roles #[] #[stPage #[lineOf 100, lineOf 112, lineOf (floor - 40)],
      stPage #[lineOf 100 (leaf := 4)]] == 1)
  no "short-page: three lines of room is not short"
    (shortPages geom roles #[] #[stPage #[lineOf 100, lineOf 112, lineOf (floor - 36)],
      stPage #[lineOf 100 (leaf := 4)]] == 0)
  no "short-page: the last page is not short" (shortPages geom roles #[] #[fullPage] == 0)
  no "short-page: a page a declared boundary closes is not short"
    (shortPages geom roles #[4] #[fullPage, stPage #[lineOf 100 (leaf := 4)]] == 0)
  no "short-page: a page the next frame follows is not short"
    (shortPages geom roles #[] #[stPage fullPage.lines (some ⟨0, 1⟩),
      stPage #[lineOf 100 (leaf := 4)] (some ⟨1, 1⟩)] == 0)
  no "declared openings: the leaves after each top-level page break"
    (declaredOpenings { body := #[.para #[.text "a"], .pagebreak, .para #[.text "b"],
      .para #[.text "c"], .pagebreak] } == #[1, 3])
  -- fallback: a text run in a face no slot names.
  let fallbackPage (s : Layout.Seg) := #[stPage #[stLine 100 100 #[s]]]
  no "fallback: a text run in the body face is not a fallback"
    (fallbackRuns fs (fallbackPage (stRun 10 "a")) == 0)
  no "fallback: a text run in another face is"
    (fallbackRuns fs (fallbackPage (stRun 10 "∀" (face := 2))) == 1)
  no "fallback: a formula's run in the math face is not"
    (fallbackRuns fs (fallbackPage (stRun 10 "∀" (face := 2) (math := true))) == 0)
  no "fallback: an icon's private-use glyph is not"
    (fallbackRuns fs (fallbackPage (stRun 10 "\uE001" (face := 1))) == 0)
  -- edge-step: a flush-left paragraph whose quote-led line does not hang.
  let q := "“"
  let hung := { stLine 98 112 #[stRun 4 q, stRun 300 "quoted"] with hang := Dim.pt 2 }
  let unhung := stLine 100 124 #[stRun 4 q, stRun 100 "quoted"]
  no "edge-step: a quote that hangs by its protrusion is on the edge"
    (edgeSteps geom roles #[stPage #[lineOf 100, hung, lineOf 136]] == 0)
  no "edge-step: a quote that does not hang steps out of it"
    (edgeSteps geom roles #[stPage #[lineOf 100, hung, unhung]] == 1)
  no "edge-step: where the page does not protrude there is no step"
    (edgeSteps { geom with protrude := false } roles #[stPage #[lineOf 100, hung, unhung]] == 0)
  no "edge-step: a page set ragged keeps its exact margin, and no line steps"
    (edgeSteps { geom with justify := false } roles #[stPage #[lineOf 100, hung, unhung]] == 0)
  no "edge-step: a centred paragraph has no one edge"
    (edgeSteps geom roles #[stPage #[lineOf 100, stLine 140 112 (words 3), unhung]] == 0)
  -- font-dupe: one program shipped twice.
  let face (src : String) := s!"@font-face \{ font-family: \"a\"; src: url(\"{src}\") format(\"truetype\"); }\n"
  let head (css : String) : Array Html.Node := #[.elem "head" #[] #[.style css]]
  no "font-dupe: one program per face is no duplicate"
    (duplicatePrograms (head (face "data:x;base64,AAAA" ++ face "data:x;base64,BBBB")) == 0)
  no "font-dupe: the same program twice is one"
    (duplicatePrograms (head (face "data:x;base64,AAAA" ++ face "data:x;base64,AAAA")) == 1)
  -- degraded, pending: the losses the build names, by class and by site.
  no "losses: two degraded sites and one pending"
    (lossSites .degraded #[Diag.of .W0005 "a", Diag.of .W0005 "b", Diag.of .W0307 "c"] == 2 &&
      lossSites .pending #[Diag.of .W0005 "a", Diag.of .W0307 "c"] == 1)
  no "losses: a folded record counts every site it carries"
    (lossSites .degraded #[{ Diag.of .W0005 "a" with sites := 3 }, { Diag.of .W0005 "a" with sites := 0 }] == 3)
  -- The rows: every judge once, each reading its own count. One fixture of
  -- gadgets, each page pair on a frame origin of its own so no boundary
  -- joins two gadgets, whose seventeen counts are pairwise distinct: a
  -- judge wired to another's row, or two rows swapped, reads a number its
  -- row does not hold. Leaves: paragraphs 0 and 1, headings 2–12, and ten
  -- table rows of two cells, 13–32.
  let mapTree : Struct.Tree :=
    { children := #[.node .paragraph #[.leaf 0 (.text "p")], .node .paragraph #[.leaf 1 (.text "q")]] ++
        (List.range 11).toArray.map (fun i => .node (.heading .h2) #[.leaf (2 + i) (.text "h")]) ++
        #[.node .table ((List.range 10).toArray.map fun r =>
          .node .row #[.node .cell #[.leaf (13 + 2 * r) (.text "a")],
                       .node .cell #[.leaf (14 + 2 * r) (.text "b")]])] }
  let mapRoles := leafRoles mapTree
  let origin := fun (k : Nat) => some (⟨100 + k, 0⟩ : Layout.FrameOrigin)
  let pair (k : Nat) (a b : Array Layout.LineOut) : Array Layout.PageOut :=
    #[stPage a (origin k), stPage b (origin k)]
  let bare (l : Layout.LineOut) : Layout.LineOut := { l with counted := false, leaf := none }
  let lineAt (y : Int) (leaf : Nat) (txt : String := "Heading") :=
    stLine 100 y #[stRun 50 txt] (leaf := some leaf)
  let ys (n : Nat) (top : Int) : Array Int :=
    (List.range n).toArray.map fun (i : Nat) => top + 12 * (i : Int)
  let pages : Array Layout.PageOut :=
    -- seven lines past the text area by 13, 1 … 6 pt; two lines below the
    -- page, two paths and two fills past its edge
    #[{ stPage ((#[13, 1, 2, 3, 4, 5, 6].map fun pt => bare (overBy pt)) ++
          #[bare (stLine 100 805 #[stRun 50 "low"]), bare (stLine 300 805 #[stRun 50 "low"])])
        (origin 0) with
        paths := #[{ path := .rect (Dim.pt 590) 0 (Dim.pt 20) (Dim.pt 5) },
                   { path := .rect (Dim.pt 590) (Dim.pt 50) (Dim.pt 20) (Dim.pt 5) }]
        fills := #[fill 590 20, fill 595 20] }] ++
    -- four clubs
    (List.range 4).toArray.flatMap (fun i => pair (1 + i) #[lineOf 712] (b3.lines)) ++
    -- five widows, the first a page turn inside a hyphenated word
    (List.range 5).toArray.flatMap (fun i => pair (5 + i)
      #[lineOf 688, lineOf 700, lineOf 712 (hyph := i == 0)] #[lineOf 100]) ++
    -- two headings stranded at a page's foot
    (List.range 2).toArray.flatMap (fun i => pair (10 + i)
      #[lineOf 676, lineOf 688, lineOf 700, lineAt 712 (2 + i)] #[lineOf 100 (leaf := 1), lineOf 112 (leaf := 1)]) ++
    -- three short pages
    (List.range 3).toArray.flatMap (fun i => pair (12 + i)
      #[lineOf 100, lineOf 112] #[lineOf 100 (leaf := 1)]) ++
    -- one paragraph of ten hyphenated lines: eight past the second
    #[stPage ((ys 10 100).map (lineOf · true) |>.push (lineOf 220)) (origin 15)] ++
    -- nine paragraphs ending on one word, alternating leaves so none joins the next
    #[stPage ((List.range 9).toArray.flatMap fun (i : Nat) =>
        #[lineOf (100 + 24 * (i : Int)) (leaf := (i + 1) % 2),
          stLine 100 (112 + 24 * (i : Int)) #[stRun 30 "end."] (leaf := some ((i + 1) % 2))])
      (origin 16)] ++
    -- ten table rows, each cut by a page break
    pair 17 ((ys 10 604).mapIdx fun r y => lineAt y (13 + 2 * r) "cell")
      ((ys 10 100).mapIdx fun r y => lineAt y (14 + 2 * r) "cell") ++
    -- eleven headings, each cut by a page break
    pair 18 ((ys 11 592).mapIdx fun i y => lineAt y (2 + i)) ((ys 11 100).mapIdx fun i y => lineAt y (2 + i)) ++
    -- twelve runs in a face no text slot names
    #[stPage #[bare (stLine 100 100 ((List.range 12).toArray.map fun _ => stRun 10 "a" (face := 2)))]
      (origin 19)]
  let f : Fixture :=
    { geom, fs := boldFs, roles := mapRoles, opens := #[], pages
      diags := (List.range 15).toArray.map (fun _ => Diag.of .W0005 "d") ++
        (List.range 14).toArray.map (fun _ => Diag.of .W0307 "p")
      head := head ((List.range 17).foldl (fun s _ => s ++ face "data:x;base64,AAAA") "") }
  let got := countsOf f
  let want : List (String × Nat) := [
    ("overfull", 7), ("overflow-pt", 13), ("off-medium", 6), ("club", 4), ("widow", 5),
    ("page-hyphen", 1), ("ladder", 8), ("runt", 9), ("split-row", 10), ("split-block", 11),
    ("stranded-head", 2), ("short-page", 3), ("fallback", 12), ("edge-step", 0),
    ("degraded", 15), ("pending", 14), ("font-dupe", 16)]
  no "rows: the gadgets' counts are pairwise distinct"
    ((want.map (·.2)).eraseDups.length == want.length)
  no s!"rows: each judge reads its own count: {got}" (got == want)
  no "rows: one per judge, each named once"
    (judges.length == 17 && (judges.map (·.1)).eraseDups.length == 17)
  no "rows: headroom is the cap less the count"
    (((rowsOf "f" got).find? (·.item == "f.overflow-pt")).map (·.value) == some (cap - 13))
  no "cap: a count at the cap is a fault, one below it is not"
    ((capFaults #[("f", [("overfull", 10000)])]).size == 1 &&
      (capFaults #[("f", [("overfull", 9999)])]).isEmpty)
  -- The build: the driver's own stages, faulting where the driver would not ship.
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  let doc (pre body : String) :=
    s!"\\documentclass\{article}\n\\fonts\{ dir = \"@FONTS@\", body = \"Source Serif Pro\" }\n\
{pre}\n\\begin\{document}\n{body}\n\\end\{document}\n"
  match ← buildScratch cache faces "slot.tex" (doc "" "Prose with \\texttt{code} in it.") with
  | .ok b =>
    no s!"build: a typewriter run with no mono family declared is the build's W0390: \
{b.diags.map (·.code)}" (b.diags.any (·.code == "W0390") && lossSites .degraded b.diags ≥ 1)
  | .error e => no s!"build: the slot probe builds: {e}" false
  match ← buildScratch cache faces "formats.tex" (doc "\\output{ formats = pdf }" "Prose.") with
  | .ok _ => no "build: a fixture declaring a PDF alone is a fault" false
  | .error e => no s!"build: a fixture declaring a PDF alone is a fault: {e}" (mentions e "formats")
  match ← buildScratch cache faces "assert.tex" (doc "\\assert{ pages == 2 }" "Prose.") with
  | .ok _ => no "build: a failing assertion is a fault" false
  | .error e => no s!"build: a failing assertion is a fault: {e}" (mentions e "assertion")
  match ← buildScratch cache faces "tool.tex"
      (doc "\\usepackage{minted}" "\\begin{minted}{haskell}\nmain = pure ()\n\\end{minted}") with
  | .ok _ => no "build: a listing only a highlighter reads is a fault" false
  | .error e => no s!"build: a listing only a highlighter reads is a fault: {e}"
                    (mentions e "needs a tool")

end Typeset

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--report"] => Typeset.report
  | ["--report", name] => Typeset.report (some name)
  | ["--lines", name] => Typeset.lines name
  | ["--pages", name] => Typeset.pagesOf name
  | _ => tierMain "typeset" (.headroom Typeset.cap) Typeset.tierMeasure Typeset.selftest args
