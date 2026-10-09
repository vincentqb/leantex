/-
The typographic quality of the pages a document ships, committed as numbers.
Run from the repository root:

  lake env lean --run scripts/typeset.lean              regenerate the baseline
  lake env lean --run scripts/typeset.lean --check      gate against testdata/scoreboard/typeset.tsv
  lake env lean --run scripts/typeset.lean --selftest   break each judge once
  lake env lean --run scripts/typeset.lean --report     every fixture's counts and its worst lines

A fixture is a document under `testdata/typeset/` (`.tex`, or `.md` through
the markdown reader), invented, representative of what a class or a surface
sets: an article, a report, a deck, a poster, a markdown report, and the
probes that isolate one defect each. Each is built the way the driver
builds it — its own reader, `\input` and `\data` beside it, a picture's
labels measured against the provisional face and settled against the final
one, the bibliography, the fonts assembled by the driver's own resolution —
over the shipped faces of `testdata/corpus/fonts` only, then laid out and
emitted to its typed HTML tree in process. Hermetic: no tool runs, so a
listing is set without a highlighter's reply and a boundary picture is the
rendered subset's, as on a host with neither; no host font is scanned, and
`LEANTEX_FONT` (which substitutes a face for an undeclared document) is a
fault rather than an input.

The judges are `LeanTex.Core.Layout.Quality`'s, over `Layout.Out` and the
HTML tree, and none reads a diagnostic: an overfull line is counted whether
or not a W0005 names it. Per fixture, as headroom (`cap - count`):

  overfull      body lines past the text area beyond their protrusion
  overflow-pt   the largest such overflow, in whole points
  off-medium    lines and paths with ink off the page and its bleed
  club          a paragraph's first line alone at the foot of a page
  widow         a paragraph's last line alone at the head of a page
  page-hyphen   a page turn inside a hyphenated word
  ladder        hyphenated lines following two hyphenated lines
  runt          one-word last lines of paragraphs of two lines or more
  split-row     table rows a page break cuts
  split-block   headings, titles, captions, figures, displays a break cuts
  fallback      text runs set in a face no text slot names
  edge-step     flush-left lines whose opening glyph hangs other than the
                protrusion table grants
  degraded      diagnostics of the build whose loss is `degraded`
  pending       diagnostics of the build whose loss is `pending`
  font-dupe     font programs the HTML page ships more than once

Blind spots, declared: `overfull` judges the text area, not a line's own
measure, so a line overrunning a list's or a column's narrower measure
inside the area is not seen; the paragraph judges read the galley's
paragraphs only (a table cell, a note, a float are not paragraphs here);
`fallback` does not see a glyph borrowed from another text slot's face.
Parity with lualatex and the rhythm tier stay gated beside this one; this
tier reads the page, not its distance from another engine's.
-/
import scripts.Board
import LeanTex.Cli.FontAssembly
import LeanTex.Cli.FontFix
import LeanTex.Core.Layout.Quality

open LeanTex.Core LeanTex.Cli Scoreboard

namespace Typeset

open LeanTex.Core.Layout.Quality

/-- Where the fixtures live, and the only faces they set in. -/
def typesetDir : System.FilePath := "testdata/typeset"
def fontsDir : System.FilePath := "testdata/corpus/fonts"

/-- The tier's headroom ceiling. Above every count and every overflow in
points a fixture here reaches (the worst line on record runs 7,526 pt past
the text area), so `cap - count` stays positive; a constant, since raising
it would raise every item at once. -/
def cap : Int := 10000

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

/-- The driver's sequence over the shipped faces (`Main.frontend` and
`Driver.build`, with no tool and no host scan). -/
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
  -- One elaboration, then the rendered subset's withdrawal where no tool
  -- drew, the bibliography and the reference judge: `Driver.elaborate`.
  let elaborate (metric : Ir.Pic.LabelMetric) : IO (Ir.Doc × Array Diag) := do
    let pass (withdrawn : Array String) := Elab.runPrepared file prepared earlier metric withdrawn
    let first := pass #[]
    let (doc, ds, spans) := if first.2.2.fallbacks.isEmpty then first
      else pass first.2.2.fallbacks
    let ds := ds ++ spliced.map fun (sty, s, pos) => Compat.styRead (s.getD file) sty pos ds
    let (doc, bibDiags) ← Input.resolveBibliography file doc spans.bib
    return (doc, ds ++ bibDiags ++ Ir.refDiags spans.labels (Elab.ReqSpans.spanOf spans.refs) doc)
  let (doc, elabDiags) ← elaborate (provisional.getD fun _ _ => {})
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
      let (doc2, _) ← elaborate metric
      let family := fs.math.bind (fs.fonts[·]?) |>.map (·.family) |>.getD "math face"
      pure (Ir.resolveMathAlphas fs.mathAlphabets family doc2).1
    let dir := (System.FilePath.mk file).parent.getD "."
    let (store, imgDiags, _) ← Hermetic.storeFor dir doc
    let diags := elabDiags ++ fontDiags ++ imgDiags
    let errors := (Diag.resolveAll doc.allow false diags).errors
    if errors > 0 then
      return .error s!"{file}: {errors} error(s) stop the build: \
{(diags.filter (·.severity == .error)).toList.take 3 |>.map (·.code)}"
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
    return .ok { geom, fs, doc, out, diags := diags ++ out.diags ++ htmlDiags, head }

/-- What one fixture's pages show, judge by judge. -/
structure Counts where
  overfull : Nat
  overflowPt : Nat
  offMedium : Nat
  club : Nat
  widow : Nat
  pageHyphen : Nat
  ladder : Nat
  runt : Nat
  splitRow : Nat
  splitBlock : Nat
  fallback : Nat
  edgeStep : Nat
  degraded : Nat
  pending : Nat
  fontDupe : Nat
  deriving Repr, BEq, Inhabited

/-- sp in a whole point, rounding up: a hair over the edge is a point. -/
def ceilPt (v : Int) : Nat := ((v + 65535) / 65536).toNat

/-- The judges over one built fixture. -/
def countsOf (geom : Layout.Geom) (fs : Font.FontSet) (doc : Ir.Doc) (out : Layout.Out)
    (diags : Array Diag) (head : Array Html.Node) : Counts :=
  let roles := leafRoles (Struct.ofDoc (Layout.pdfView doc))
  let pages := out.pages
  let over := overflows geom pages
  let ss := straddles roles pages
  let loss (l : Loss) : Nat := (diags.filter (·.kind.loss == l)).size
  { overfull := over.size
    overflowPt := ceilPt (over.foldl max 0)
    offMedium := offMediumCount geom fs pages
    club := clubs ss
    widow := widows ss
    pageHyphen := pageHyphens ss
    ladder := ladderLines roles pages
    runt := runts roles pages
    splitRow := splitRows roles pages
    splitBlock := splitBlocks roles pages
    fallback := fallbackRuns fs pages
    edgeStep := edgeSteps geom roles pages
    degraded := loss .degraded
    pending := loss .pending
    fontDupe := duplicatePrograms head }

/-- The judges' names, the item suffixes, in the order rows are written. -/
def Counts.named (c : Counts) : List (String × Nat) :=
  [("overfull", c.overfull), ("overflow-pt", c.overflowPt), ("off-medium", c.offMedium),
   ("club", c.club), ("widow", c.widow), ("page-hyphen", c.pageHyphen),
   ("ladder", c.ladder), ("runt", c.runt), ("split-row", c.splitRow),
   ("split-block", c.splitBlock), ("fallback", c.fallback), ("edge-step", c.edgeStep),
   ("degraded", c.degraded), ("pending", c.pending), ("font-dupe", c.fontDupe)]

/-- A fixture's rows: `<fixture>.<judge>`, as headroom. -/
def rowsOf (name : String) (c : Counts) : Array Row :=
  c.named.toArray.map fun (j, n) => { item := s!"{name}.{j}", value := cap - (n : Int) }

/-- Every fixture built and judged; a fixture that does not build is a
fault of the run, never a row. -/
def measureAll : IO (Except (Array String) (Array (String × Counts))) := do
  if (← IO.getEnv "LEANTEX_FONT").isSome then
    return .error #["LEANTEX_FONT is set: it substitutes a host face for an undeclared \
document, and this tier measures the shipped faces only; unset it"]
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  let mut faults : Array String := #[]
  let mut out : Array (String × Counts) := #[]
  for f in ← fixtureFiles do
    match ← build cache faces (typesetDir / f).toString with
    | .ok b => out := out.push (stem f, countsOf b.geom b.fs b.doc b.out b.diags b.head)
    | .error e => faults := faults.push e
  return (if faults.isEmpty then .ok out else .error faults)

def tierMeasure : IO (Array String × Array Row) := do
  match ← measureAll with
  | .error faults =>
    for f in faults do IO.eprintln s!"typeset: fault: {f}"
    return (#[], #[])
  | .ok cs =>
    let total (j : String) : Nat := cs.foldl (fun n (_, c) =>
      n + ((c.named.lookup j).getD 0)) 0
    let summary := String.intercalate ", " ((cs[0]?.map (·.2.named)).getD [] |>.map fun (j, _) =>
      s!"{j} {total j}")
    return (#[s!"# source: {cs.size} fixtures under {typesetDir}, built in process over the \
shipped faces and judged on Layout.Out and the typed HTML tree; totals: {summary}"],
      cs.foldl (fun acc (n, c) => acc ++ rowsOf n c) #[])

/-- Every fixture's counts, and the lines behind its overflow. -/
def report : IO UInt32 := do
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  for f in ← fixtureFiles do
    let t0 ← IO.monoMsNow
    match ← build cache faces (typesetDir / f).toString with
    | .error e =>
      IO.println s!"{f}: fault: {e}"
    | .ok b =>
      let c := countsOf b.geom b.fs b.doc b.out b.diags b.head
      IO.println s!"{stem f} ({b.out.pages.size} pages, {(← IO.monoMsNow) - t0} ms): \
{String.intercalate " " (c.named.map fun (j, n) => s!"{j}={n}")}"
      let mut shown := 0
      for h : i in [0:b.out.pages.size] do
        for l in b.out.pages[i].lines do
          let o := overflow b.geom l
          if o > 0 && shown < 5 then
            shown := shown + 1
            let text := String.ofList (Layout.LineOut.glyphChars l)
            IO.println s!"  p{i + 1} +{ceilPt o} pt: {text.take 72}"
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

/-- One fixture's lines: where each stands, what it sets, and what the
judges make of it. -/
def lines (name : String) : IO UInt32 := do
  let faces ← Hermetic.shippedFaces fontsDir
  let cache ← FontEnv.Cache.mk'
  let some f := (← fixtureFiles).find? (stem · == name)
    | IO.eprintln s!"typeset: no fixture '{name}' under {typesetDir}"; return 1
  match ← build cache faces (typesetDir / f).toString with
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

/-- A paragraph leaf, a heading leaf, a table row's two cells: roles 0–3. -/
def stTree : Struct.Tree :=
  { children := #[.node .paragraph #[.leaf 0 (.text "p")],
                  .node (.heading .h2) #[.leaf 1 (.text "h")],
                  .node .table #[.node .row #[.node .cell #[.leaf 2 (.text "a")],
                                              .node .cell #[.leaf 3 (.text "b")]]]] }

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
  no "overflow-pt: a hair past the edge is a whole point" (ceilPt 1 == 1 && ceilPt (Dim.pt 1) == 1)
  no "overflow-pt: a point and a hair is two" (ceilPt (Dim.pt 1 + 1) == 2)
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
  -- club, widow, page-hyphen: a paragraph across a page boundary.
  let roles := leafRoles stTree
  no s!"roles: paragraph, heading, cells of one row: {repr roles}"
    (roles.map (·.kind) == #[.paragraph, .heading .h2, .cell, .cell] &&
      roles[2]?.bind (·.row) == roles[3]?.bind (·.row) && (roles[2]?.bind (·.row)).isSome &&
      (roles[1]?.bind (·.group)).isSome && (roles[0]?.bind (·.group)).isNone)
  let lineOf (y : Int) (hyph : Bool := false) :=
    stLine 100 y (words 9 ++ (if hyph then #[stRun 4 "-" .hyphen] else #[]))
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
  no "edge-step: a centred paragraph has no one edge"
    (edgeSteps geom roles #[stPage #[lineOf 100, stLine 140 112 (words 3), unhung]] == 0)
  -- font-dupe: one program shipped twice.
  let face (src : String) := s!"@font-face \{ font-family: \"a\"; src: url(\"{src}\") format(\"truetype\"); }\n"
  let head (css : String) : Array Html.Node := #[.elem "head" #[] #[.style css]]
  no "font-dupe: one program per face is no duplicate"
    (duplicatePrograms (head (face "data:x;base64,AAAA" ++ face "data:x;base64,BBBB")) == 0)
  no "font-dupe: the same program twice is one"
    (duplicatePrograms (head (face "data:x;base64,AAAA" ++ face "data:x;base64,AAAA")) == 1)
  -- degraded, pending: the losses the build names, by class.
  let c := countsOf geom fs default { pages := #[], diags := #[] }
    #[Diag.of .W0005 "a", Diag.of .W0005 "b", Diag.of .W0307 "c"] #[]
  no s!"losses: two degraded and one pending: {c.degraded} {c.pending}"
    (c.degraded == 2 && c.pending == 1)
  -- The rows: every judge once, as headroom.
  let rs := rowsOf "f" { c with overfull := 3 }
  no "rows: one per judge, each named once"
    (rs.size == 15 && (rs.map (·.item)).toList.eraseDups.length == 15)
  no "rows: headroom is the cap less the count"
    ((rs.find? (·.item == "f.overfull")).map (·.value) == some (cap - 3))

end Typeset

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--report"] => Typeset.report
  | ["--lines", name] => Typeset.lines name
  | _ => tierMain "typeset" (.headroom Typeset.cap) Typeset.tierMeasure Typeset.selftest args
