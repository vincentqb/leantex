import LeanTex

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def failures : IO.Ref (List String) → String → IO Unit :=
  fun ref name => ref.modify (name :: ·)

def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit := do
  unless ok do failures ref name

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- The PNG row filters forward (ISO/IEC 15948 §9.2), one type per row via
`ft`: the synthesizer that hands the engine's unfilter and residual split
every filter, every geometry, so their statements can be exercised on
inputs the engine never wrote itself. -/
def pngFilter (px : ByteArray) (pxH rowBytes bpp : Nat) (ft : Nat → Nat) : ByteArray := Id.run do
  let sample (r i : Nat) : Nat := (px[r * rowBytes + i]?.getD 0).toNat
  let mut out := ByteArray.emptyWithCapacity (px.size + pxH)
  for r in [0:pxH] do
    let f := ft r
    out := out.push (UInt8.ofNat f)
    for i in [0:rowBytes] do
      let left := if bpp ≤ i then sample r (i - bpp) else 0
      let up := if 1 ≤ r then sample (r - 1) i else 0
      let upLeft := if 1 ≤ r ∧ bpp ≤ i then sample (r - 1) (i - bpp) else 0
      let pred :=
        if f == 0 then 0 else if f == 1 then left else if f == 2 then up
        else if f == 3 then (left + up) / 2
        else
          let p : Int := (left : Int) + up - upLeft
          let pa := (p - left).natAbs
          let pb := (p - up).natAbs
          let pc := (p - upLeft).natAbs
          if pa ≤ pb && pa ≤ pc then left else if pb ≤ pc then up else upLeft
      out := out.push (UInt8.ofNat ((sample r i + 256 - pred) % 256))
  return out

/-! Synthetic PNGs, byte by byte: the decoder reads structure, not CRCs or
pixel data, so CRC slots are zero and an IDAT payload may be arbitrary. -/

def be32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

def pngChunk (tag : String) (data : List UInt8) : List UInt8 :=
  be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++ [0, 0, 0, 0]

def pngIhdr (w h bd ct interlace : Nat) : List UInt8 :=
  be32 w ++ be32 h ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, UInt8.ofNat interlace]

def pngSigBytes : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]

def mkPng (chunks : List UInt8) : ByteArray := bytes (pngSigBytes ++ chunks)

/-- Does `needle` occur verbatim inside `hay`? The pass-through witness: a
source stream reaching the artifact byte for byte. -/
def containsBytes (hay needle : ByteArray) : Bool := Id.run do
  if needle.size == 0 || hay.size < needle.size then return false
  for i in [0:hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0:needle.size] do
      if hay[i + j]! != needle[j]! then
        ok := false
        break
    if ok then return true
  return false

/-- xorshift64*: deterministic, dependency-free (as in scripts/kp-fuzz.lean).
Returns the new state and the output value. -/
def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let x := s ^^^ (s >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x, x * 2685821657736338717)

/-- Draw a value below `bound`, threading the state. -/
def rand (s : UInt64) (bound : Nat) : Nat × UInt64 :=
  let (s', v) := nextRand s
  ((v % UInt64.ofNat bound).toNat, s')

def errKindAt (bs : ByteArray) : Option (Nat × ErrKind) :=
  (validate bs).map fun e => (e.offset, e.kind)

def toks (s : String) : List Lex.Tok :=
  ((Lex.lex "t" s).1.map (·.tok)).toList

def elabStr (s : String) : Ir.Doc × Array Diag :=
  Elab.run "t" s

/-- The first elaborated formula in a document's paragraphs, equations,
and centred display blocks (a display alignment sets under `.center`):
enough reach for a one-formula snippet. -/
def blockFormula (b : Ir.Block) : Option Math.MList :=
  let inls := match b with
    | .para content => content
    | .equation _ content => content
    | _ => #[]
  inls.findSome? fun x => match x with
    | .formula _ _ body => some body
    | _ => none

def firstFormula (d : Ir.Doc) : Option Math.MList :=
  d.body.findSome? fun b => match b with
    | .center bs => bs.findSome? blockFormula
    | b => blockFormula b

/-- A *markdown* source through the one elaborator: the reader, the
desugaring, then `Elab.runRaws` — the same path `leantex doc.md` takes. -/
def elabMd (s : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Md.read "t.md" s
  Elab.runRaws "t.md" raws ds

/-- Diagnostics of a markdown source. -/
def dvMd (s : String) : Array Diag := (elabMd s).2

def errCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .error)).toList.map (·.code)

def warnCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .warning)).toList.map (·.code)

def noteCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .note)).toList.map (·.code)

def dvDoc (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def dvDeck (pre body : String) : String :=
  "\\documentclass{slides}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169 (pre body : String) : String :=
  "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169Body (body : String) : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\theme{default}\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169Frame (body : String) : String :=
  deck169Body ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}")

/-- The golden set: every fixture `runGoldens` elaborates and every name
`censusTable` must carry a row for. Written out rather than globbed so a
golden run's membership is visible here, and held to `tests/corpus` by
`corpusCoverageChecks` — a fixture on disk is in this list or its own header
says why not. -/
def goldenNames : List String :=
  ["affine-lengths", "paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk", "deck", "deck1610", "themed", "latex-idioms", "wrapper",
   "centering", "columns", "overlays", "overlays-blocks", "overprint", "notes", "furniture",
   "chrome", "footer-left", "footer-mixed", "footer-collide", "lists",
   "lists-styled", "lists-deck", "headroom",
   "marker-styled", "marker-content",
   "trio-page", "trio-deck", "trio-card", "valign", "images", "figures", "math",
   "webpage", "quotes", "quote-deck", "outline", "outline-gap", "webnav",
   "bibliography", "resume-data",
   "icons",
   "diagram", "diagram-boundary", "diagram-overflow", "diagram-refused", "diagram-scm",
   "diagram-tikzset",
   "tables", "tables-ragged", "subfigures", "float-center", "box-sides",
   "math-companion", "math-first", "math-text", "math-cancel", "greek-literal", "abstract", "crossref", "eqnum", "footnotes",
   "redefine", "titlebars", "titleground", "daylight", "blocks", "poster", "poster-headline", "listings",
   "algorithm", "lineno", "lineno-modulo",
   "cond-newif", "cond-ifdefined", "cond-ifx", "cond-ifnum", "cond-loaded"]

-- KP test helpers: word/glue/forced-break item builders and a brute-force
-- optimum to cross-check the DP against.

/-- The fonts the repository ships, beside the fixtures that name them. Every
font-dependent check runs on these and only these, so `lake test` sees the
same faces on every host — a Mac with nothing installed included. -/
def testFonts : String := "tests/corpus/fonts"

def findFont : IO (Option ByteArray) := do
  let p := testFonts ++ "/OpenSans-Regular.ttf"
  if ← System.FilePath.pathExists p then
    return some (← IO.FS.readBinFile p)
  return none

/-- Does a produced file contain this ASCII run? PDF content streams are the
only witness that a face or a size reached the output, and the file as a whole
is not valid UTF-8, so the search is over bytes. -/
def bytesContain (hay : ByteArray) (needle : String) : Bool := Id.run do
  let n := needle.toUTF8
  if n.size == 0 || hay.size < n.size then return false
  for i in [0:hay.size - n.size + 1] do
    let mut ok := true
    for j in [0:n.size] do
      if hay[i + j]! != n[j]! then
        ok := false
        break
    if ok then return true
  return false

/-- The written PDF with every `/FlateDecode` stream the writer emitted
inflated and appended: the view a `bytesContain` assertion reads now that
content, object and metadata streams really compress. Raw facts (header,
xref spelling, filter names) stay visible — the raw bytes lead — and
every compressed stream's plain text follows. The writer's own spelling
(`/Length {n} >>\nstream\n`) is the anchor; a stream whose dictionary
names no flate filter is skipped as already plain. -/
def pdfText (pdf : ByteArray) : ByteArray := Id.run do
  let pat := " >>\nstream\n".toUTF8
  let mut out := pdf
  let mut i := 0
  for _ in [0:pdf.size] do
    if i + pat.size > pdf.size then break
    let mut ok := true
    for k in [0:pat.size] do
      if pdf[i + k]! != pat[k]! then
        ok := false
        break
    if !ok then
      i := i + 1
    else
      -- Walk back over the dictionary to `obj` for the filter and length.
      let dictStart := if i > 400 then i - 400 else 0
      let head := String.ofList (((pdf.extract dictStart i).toList).map fun v =>
        Char.ofNat (min v.toNat 127))
      let dataOff := i + pat.size
      let len? := do
        let part ← (head.splitOn " /Length ").getLast?
        (part.splitOn " ").head?.bind (·.toNat?)
      match len? with
      | none => i := i + 1
      | some len =>
        if (head.splitOn "/FlateDecode").length ≥ 2 then
          let z := pdf.extract dataOff (dataOff + len)
          if let .ok plain := LeanTex.Core.Flate.inflate z (len * 400 + 65536) then
            out := out ++ plain
        i := dataOff + len
  return out

/-- Re-verify a produced PDF through the engine's own reader
(`PdfRead.objects`): the cross-reference followed, every listed object
fetched and checked against the number the file spells for it
(`objects_num_covers` — direct offsets and object-stream headers alike,
where the earlier byte walk read type-1 rows only), and every stream the
reader can decode inflated. Returns the number of objects verified at a
direct offset — the count the byte walk returned. -/
def checkXref (pdf : ByteArray) : Except String Nat := do
  let es ← PdfRead.objects pdf
  let mut verified := 0
  for e in es.val do
    if let .direct _ := e.loc then
      verified := verified + 1
    -- Streams under the filters the reader owns decode, or the file is
    -- refused where the byte walk would have read past the fault. Foreign
    -- filters (an image's DCT) are data the census records, not decodes.
    let fs := PdfCensus.filtersOf e.val
    if fs.all (· == "FlateDecode") then
      if let .error err := e.decoded then
        throw s!"object {e.num}: {err}"
  return verified

/-- A `tests/corpus/sty-parity` fixture run the way the driver runs it: the
splice fixpoint (`Input.expandInputs`) first, so a local `.sty` beside the
fixture is read, then elaboration, then the N0020 records built from the
splice records exactly as `Main.frontend` builds them — the counts do not
exist before elaboration. Shared because two blocks drive this directory:
the `\input`-parity cases and the theme-loading family. -/
def runStyParity (name : String) :
    IO (Ir.Doc × Array Diag × Array (String × Option String × Pos)) := do
  let path := s!"tests/corpus/sty-parity/{name}.tex"
  let src ← IO.FS.readFile path
  let (raws, _) := Parse.parse path (Lex.lex path src).1
  let (raws, inputDs, spliced) ← Input.expandInputs path raws
  let (doc, ds) := Elab.runRaws path raws
  let ds := ds ++ spliced.map fun (sty, srcF, pos) =>
    Compat.styRead (srcF.getD path) sty pos ds
  return (doc, inputDs ++ ds, spliced)

/-- A fixture elaborated the way the driver builds it: the `\data` effect
fulfilled from the corpus directory before elaboration (the expansion
needs the records where `\begin{foreach}` stands), then elaboration, then
the `.bib` bibliography effect — the same fulfilments `Main` performs, so
a data or bibliography fixture exercises the pipeline the documents run.
Fixtures that request neither pass through untouched. -/
def elabFixture (n src : String) : IO (Ir.Doc × Array Diag) := do
  let file := s!"{n}.tex"
  let (toks, lexDiags) := Lex.lex file src
  let (raws, parseDiags) := Parse.parse file toks
  let mut dataSources : Array (String × String) := #[]
  for (srcName, _) in Data.fileRefs raws do
    let name := Data.sourceName srcName
    let path := s!"tests/corpus/{name}"
    if ← System.FilePath.pathExists path then
      dataSources := dataSources.push (srcName, ← IO.FS.readFile path)
  let (raws, dataDiags) := Data.expandData file dataSources raws
  let (doc, diags) := Elab.runRaws file raws (lexDiags ++ parseDiags ++ dataDiags)
  let requested := Ir.bibRefs doc
  if requested.isEmpty then return (doc, diags)
  let mut sources : Array (String × String) := #[]
  for srcName in requested do
    let name := Bib.sourceName srcName
    let path := s!"tests/corpus/{name}"
    if ← System.FilePath.pathExists path then
      sources := sources.push (srcName, ← IO.FS.readFile path)
  let (doc, bibDiags) := Bib.apply sources doc
  return (doc, diags ++ bibDiags)

def firstDiff (expected actual : String) : String := Id.run do
  let e := expected.splitOn "\n"
  let a := actual.splitOn "\n"
  for i in [0:max e.length a.length] do
    let el := e[i]?.getD "<missing>"
    let al := a[i]?.getD "<missing>"
    if el != al then
      return s!"line {i + 1}:\n  expected: {el.quote}\n  actual:   {al.quote}"
  return "no difference"

def runGoldens (update : Bool) (fail : String → IO Unit) : IO Unit := do
  if update then
    IO.FS.createDirAll "tests/golden"
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, diags) ← elabFixture n src
    let out := Ir.dump doc diags -- ir tier: goldens witness elaboration, not the artifact
    let path := s!"tests/golden/{n}.txt"
    if update then
      IO.FS.writeFile path out
      IO.println s!"updated {path}"
    else
      let golden ← try
        pure (some (← IO.FS.readFile path))
      catch _ =>
        pure none
      match golden with
      | none => fail s!"golden {n}: missing {path} (run: lake exe Tests --update)"
      | some g =>
        unless g == out do
          fail s!"golden {n}: mismatch, {firstDiff g out} (if intended, run: lake exe Tests --update)"

/-- The shipped-page census over `Layout.Out`: the observable facts a page
claim may cite (AGENTS.md, the page-claim rule). Chars come from the set
glyph runs — gaps become single spaces and lines join with one space, so a
phrase survives a line break but not a hyphenation. `covered` collects the
runs painted in one of the document's own covered colours
(`coveredColorsOf`: the plain cover plus the per-colour cover of every
palette entry). Deliberately thin: it grows toward
the role census `Check.Shipped` is heading for; what `censusChecks`
enforces today is coverage — no fixture enters the golden set witnessed by
its IR dump alone. -/
structure CensusLine where
  x : Dim.Sp
  /-- The line's baseline, in layout coordinates (y grows downward): what a
  fact about vertical order or a declared gap reads. -/
  y : Dim.Sp
  /-- The largest set size among the line's glyph runs (0 on a glyphless
  line): what a fact about a declared display size reads. -/
  size : Dim.Sp
  /-- The line's set width, so a fact can judge its right edge — where a
  footer's right slot must sit whatever the left slot holds. -/
  width : Dim.Sp
  text : String
  /-- The line stands in the reserved margin band by design
  (`Layout.LineOut.furniture`): running head and foot, chrome slots, the
  logo — and the margin line numbers. -/
  furniture : Bool := false
  /-- A counted body line (`Layout.LineOut.counted`): a galley text line
  the line-number census counts — what a margin number attaches to. -/
  counted : Bool := false
  /-- The face every glyph run on the line sets in, in run order: the
  `FontSet` index the layout resolved. What a fact about *which family*
  ink sets in reads — a picture's node label must set in the face the
  body sets in, and only the shipped run can say which face that was
  (`Picture.labelFace_agree`'s page side). Under a one-face set every
  entry is 0 and the channel says nothing; `twoSlotOf` is the set that
  distinguishes the slots. -/
  runFonts : Array Nat := #[]

structure CensusPage where
  lines : Array CensusLine
  covered : String
  rules : Nat
  /-- Every rule segment shipped on the page, in line order: its line's
  baseline and its thickness — what the title-bar facts read (a bar at its
  declared weight, above or below the title's line). -/
  ruleSegs : Array (Dim.Sp × Dim.Sp) := #[]
  fills : Nat
  /-- Every fill rectangle shipped on the page, in paint order — what the
  cut-mark facts read (marks inside the bleed strip, none in the gap,
  duplex-symmetric). -/
  fillRects : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- Picture paths shipped on the page: node outlines and edges. -/
  paths : Nat
  /-- Every shipped path's stroke, in paint order: its colour and width.
  What a fact about an inherited picture-level key reads — a key set on
  the picture and again on the path must leave the path's own value on the
  page (`Picture.inherit_inner_exact`), and only the artifact can say so.
  An unstroked path (a node's fill alone) contributes nothing. -/
  pathStrokes : Array (Ir.Color × Dim.Sp) := #[]
  /-- Every shipped path's extent, in paint order: a circle's diameter, a
  rectangle's own width and height, a segment chain's or a tip's bounding
  box. What a fact about a size key set at more than one level reads — a
  node whose `minimum size` is declared by the picture, by `every node`,
  and by its own bracket ships exactly one of the three
  (`Picture.merge_own_exact`, `Picture.merge_every_exact`), and only the
  page can say which. -/
  pathSpans : Array (Dim.Sp × Dim.Sp) := #[]
  /-- Every shipped path's bounding box, in paint order: `(x, y, w, h)` in
  page coordinates. `pathSpans` is its extent half; this adds *where* the
  path stands, which is what a fact about relative node placement reads —
  `left=of` and `right=of` are claims about position, and a node's
  resolved centre is only visible on the page
  (`Picture.placeRel_exact`, `Picture.place_order_agree`). -/
  pathBoxes : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- Image boxes shipped on the page: an embedded figure, or a boundary
  request's box (fulfilled or placeholder) — what the diagram-boundary
  row reads to pin that the request ships ink where the picture stood. -/
  images : Nat := 0
  /-- Filled polygons shipped in the page's lines — a formula's cancel
  strikes and arrowheads — as their points in page coordinates (y down):
  what the cancel facts read, the strike's corners and the arrowhead's
  tip against the struck ink. -/
  polys : Array (Array (Dim.Sp × Dim.Sp)) := #[]

def CensusPage.text (p : CensusPage) : String :=
  String.intercalate " " (p.lines.toList.map (·.text))

/-- The colours covering can paint in a document: the plain cover (runs
with no colour of their own) and the per-colour cover of every palette
entry — computed from the same `Design.cover` layout reads. A fixed point
(`cov.of c == c`, e.g. the page colour itself: covering toward `bg` moves
nothing) is excluded: it covers nothing, and keeping it would read active
ink painted in that colour as covered. -/
def coveredColorsOf (doc : Ir.Doc) : Array Ir.Color :=
  let cov := (Ir.Design.ofDoc doc).cover
  (doc.palette.entries.filterMap fun (_, c) =>
    let covered := cov.of c
    if covered == c then none else some covered).push cov.plain

def censusOf (coveredColors : Array Ir.Color) (out : Layout.Out) :
    Array CensusPage := Id.run do
  let mut pages : Array CensusPage := #[]
  for p in out.pages do
    let mut lines : Array CensusLine := #[]
    let mut covered := ""
    let mut rules := 0
    let mut ruleSegs : Array (Dim.Sp × Dim.Sp) := #[]
    let mut images := 0
    let mut polys : Array (Array (Dim.Sp × Dim.Sp)) := #[]
    for l in p.lines do
      let mut px := l.x
      let mut chars := ""
      let mut runSize : Dim.Sp := 0
      let mut runFonts : Array Nat := #[]
      for seg in l.segs do
        match seg with
        | .run idx color _ w glyphs size _ _ _ _ _ =>
          px := px + w
          runSize := max runSize size
          runFonts := runFonts.push idx
          if coveredColors.contains color then
            for (_, c, _) in glyphs do
              chars := chars.push c
              covered := covered.push c
          else
            for (_, c, _) in glyphs do
              chars := chars.push c
            covered := covered.push ' '
        | .gap w _ =>
          px := px + w
          chars := chars.push ' '
          covered := covered.push ' '
        | .rule w th _ _ =>
          px := px + w
          rules := rules + 1
          ruleSegs := ruleSegs.push (l.y, th)
        -- an image is decorative ink to the text census, like a rule
        | .image _ w _ =>
          px := px + w
          images := images + 1
        | .poly pts _ => polys := polys.push (pts.map fun (x, y) => (px + x, l.y - y))
      -- The census asks where the text block stands, so a protruded
      -- line reports its measure edge: the ink deliberately hangs
      -- `l.hang` left of it (`Layout.protrudeLeft`).
      lines := lines.push { x := l.x + l.hang, y := l.y, size := runSize
                            width := l.setWidth, text := chars
                            furniture := l.furniture, counted := l.counted
                            runFonts := runFonts }
      covered := covered.push ' '
    pages := pages.push { lines := lines
                          covered := covered
                          rules := rules
                          ruleSegs := ruleSegs
                          polys := polys
                          fills := p.fills.size
                          fillRects := p.fills.map fun f => (f.x, f.y, f.w, f.h)
                          paths := p.paths.size
                          pathStrokes := p.paths.filterMap fun q =>
                            q.stroke.map fun s => (s.color, s.width)
                          pathSpans := p.paths.map fun q =>
                            match q.path with
                            | .circle _ _ r => (2 * r, 2 * r)
                            | .rect _ _ w h => (w, h)
                            | .tri x1 y1 x2 y2 x3 y3 =>
                              (max x1 (max x2 x3) - min x1 (min x2 x3),
                               max y1 (max y2 y3) - min y1 (min y2 y3))
                            | .segs segs =>
                              let xs := segs.flatMap fun s => match s with
                                | .line x1 _ x2 _ => #[x1, x2]
                                | .cubic x1 _ _ _ _ _ x2 _ => #[x1, x2]
                              let ys := segs.flatMap fun s => match s with
                                | .line _ y1 _ y2 => #[y1, y2]
                                | .cubic _ y1 _ _ _ _ _ y2 => #[y1, y2]
                              (xs.foldl max (xs[0]?.getD 0) - xs.foldl min (xs[0]?.getD 0),
                               ys.foldl max (ys[0]?.getD 0) - ys.foldl min (ys[0]?.getD 0))
                          pathBoxes := p.paths.map fun q =>
                            match q.path with
                            | .circle x y r =>
                              let r := max r (-r)
                              (x - r, y - r, 2 * r, 2 * r)
                            | .rect x y w h => (x, y, w, h)
                            | .tri x1 y1 x2 y2 x3 y3 =>
                              let lo := (min x1 (min x2 x3), min y1 (min y2 y3))
                              (lo.1, lo.2, max x1 (max x2 x3) - lo.1,
                                max y1 (max y2 y3) - lo.2)
                            | .segs segs =>
                              let xs := segs.flatMap fun s => match s with
                                | .line x1 _ x2 _ => #[x1, x2]
                                | .cubic x1 _ _ _ _ _ x2 _ => #[x1, x2]
                              let ys := segs.flatMap fun s => match s with
                                | .line _ y1 _ y2 => #[y1, y2]
                                | .cubic _ y1 _ _ _ _ _ y2 => #[y1, y2]
                              let x0 := xs.foldl min (xs[0]?.getD 0)
                              let y0 := ys.foldl min (ys[0]?.getD 0)
                              (x0, y0, xs.foldl max (xs[0]?.getD 0) - x0,
                                ys.foldl max (ys[0]?.getD 0) - y0)
                          images := images }
  return pages

def hasStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- Does a compat-index row's call load the row's own package? Then the
scaffold does not load it a second time: a duplicate load puts the call's
whole effect in the baseline as well, and a `\usepackage{times}` row could
not witness anything. The decision is read off the row's own text — never a
list of package names here, which would drift from the directory. -/
def compatRowSelfLoads (pkg call : String) : Bool :=
  hasStr call "\\usepackage" && hasStr call ("{" ++ pkg ++ "}")

/-- The document a compat-index row elaborates as: the call at its declared
place, with the package loaded unless the call loads it itself. -/
def compatRowSrc (pkg place call : String) : String :=
  let load := if compatRowSelfLoads pkg call then "" else s!"\\usepackage\{{pkg}}\n"
  if place == "pre" then
    s!"\\documentclass\{article}\n{load}{call}\n\\begin\{document}\nx\n\\end\{document}"
  else if place == "frame" then
    s!"\\documentclass\{{pkg}}\n\\begin\{document}\n\\begin\{frame}\n{call}\n\\end\{frame}\n\\end\{document}"
  else
    s!"\\documentclass\{article}\n{load}\\begin\{document}\n{call}\n\\end\{document}"

/-- How many times `word` stands in `text` as a whole name: not inside a
longer identifier, and not as a field after a dot — a call to
`pdfStreamChecks` is no call to `StreamChecks`. -/
def wordCount (text word : String) : Nat := Id.run do
  let parts := (text.splitOn word).toArray
  let nameChar (c : Char) : Bool :=
    c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.'
  let mut n := 0
  for i in [0:parts.size - 1] do
    let before := parts[i]?.getD ""
    let after := parts[i + 1]?.getD ""
    let leftOk := if before.isEmpty then i == 0 else !nameChar before.back
    let rightOk := if after.isEmpty then i + 2 == parts.size else !nameChar after.front
    if leftOk && rightOk then n := n + 1
  return n

def censusText (c : Array CensusPage) : String :=
  String.intercalate " " (c.toList.map (·.text))

def pageHas (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.text needle).getD false

/-- How many times `needle` is inked on page `i`. The census counts what
shipped, so a construct that put its content on the page twice reads as 2
here — `pageHas` cannot tell one copy from two. -/
def pageOccurs (c : Array CensusPage) (i : Nat) (needle : String) : Nat :=
  (c[i]?.map fun p => (p.text.splitOn needle).length - 1).getD 0

def pageCovered (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.covered needle).getD false

def pageAllRevealed (c : Array CensusPage) (i : Nat) : Bool :=
  (c[i]?.map fun p => (p.covered.trimAscii.toString).isEmpty).getD false

/-- The x of the first shipped line on page `i` containing `needle`. -/
def lineXOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.x)

/-- The baseline of the first shipped line on page `i` containing `needle`. -/
def lineYOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.y)

/-- The largest run size of the first shipped line on page `i` containing
`needle`: what a declared display size sets. -/
def lineSizeOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.size)

/-- The rule segments shipped on page `i`, in line order: (baseline,
thickness) pairs. -/
def pageRuleSegs (c : Array CensusPage) (i : Nat) : Array (Dim.Sp × Dim.Sp) :=
  (c[i]?.map (·.ruleSegs)).getD #[]

/-- The right edge (x plus set width) of the first shipped line on page `i`
containing `needle`: where a footer's right slot must end. -/
def lineRightOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map
    fun l => l.x + l.width

/-- The glyph text of one shipped line: each run's characters in order,
a gap as one space (`gapAsSpace := false` reads the bare glyphs — a page
number's centring gaps are not its text). -/
def lineText (l : Layout.LineOut) (gapAsSpace : Bool := true) : String :=
  l.segs.foldl (fun s seg => match seg with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.foldl (fun s (_, c, _) => s.push c) s
    | .gap _ _ => if gapAsSpace then s.push ' ' else s
    | _ => s) ""

/-- A shipped line's runs, left to right: the face index, the glyphs, and the
run's left edge and width on the page. -/
def lineRuns (l : Layout.LineOut) : Array (Nat × String × Dim.Sp × Dim.Sp) := Id.run do
  let mut out := #[]
  let mut x := l.x
  for seg in l.segs do
    match seg with
    | .run idx _ _ w gs _ _ _ _ _ _ =>
      out := out.push (idx, String.ofList (gs.map (·.2.1)).toList, x, w)
      x := x + w
    | .gap w _ => x := x + w
    | .rule w _ _ _ => x := x + w
    | .poly _ _ => pure ()
    | .image _ w _ => x := x + w
  return out

/-- Whether a shipped line sets any glyph: a link's underline or a rule ships
as a line of its own that sets none. -/
def hasGlyphRun (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
    | _ => false

/-- A line's text as a reader sees it: `lineText`, but a glyphless run — a
tie, which ships as a box a space wide (Layout's no-break-space arm) —
reads as the space the page shows. -/
def lineInk (l : Layout.LineOut) : String := l.segs.foldl (fun s seg => match seg with
  | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
    if glyphs.isEmpty then s.push ' ' else glyphs.foldl (fun s (_, c, _) => s.push c) s
  | .gap _ _ => s.push ' '
  | _ => s) ""

/-- The furniture baselines (head y, foot y) a geometry owes under `font`'s
ink and a declared gap: functions of the geometry alone
(`furnHeadY`/`furnFootY` take no content) — what the shipped furniture
lines must stand at (`furniture_symmetric`'s realisation). -/
def furnYs (font : Font.Font) (geom : Layout.Geom)
    (gap : Option Dim.Sp := none) : Dim.Sp × Dim.Sp :=
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let band := Layout.furnitureBand geom.vmargin
    (scale font.ascent + scale (-font.descent)) gap
  (Layout.furnHeadY band (scale font.ascent),
   Layout.furnFootY band geom.pageH (scale (-font.descent)))

mutual

/-- The text content of an emitted HTML node, for the agreement census: the
typed tree's characters with the markup stripped — the HTML side of what
`censusOf` reads off the PDF's shipped lines. -/
def nodeTextOne (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ _ kids => nodeTextList acc kids.toList

def nodeTextList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => nodeTextList (nodeTextOne acc k) rest

end

mutual

/-- The first `mathvariant` attribute an emitted tree declares, in document
order: the MathML `.styled` arm sets `("mathvariant", style.mathvariant)` on
the `mi`/`mn` leaf, so this pulls the semantic variant a resolved text-style
scalar carries (the twin of the PDF face-slot selection). `none` when no node
declares one. -/
def mathvariantOne : Html.Node → Option String
  | .text _ => none
  | .style _ => none
  | .script _ _ => none
  | .elem _ attrs kids =>
    match attrs.find? (fun (k, _) => k == "mathvariant") with
    | some (_, v) => some v
    | none => mathvariantList kids.toList

def mathvariantList : List Html.Node → Option String
  | [] => none
  | k :: rest => match mathvariantOne k with
    | some v => some v
    | none => mathvariantList rest

end

mutual

/-- The first `style` attribute an emitted tree declares, in document order:
the MathML `.styled` arm sets `("style", style.css)` on the leaf, so this
pulls the CSS a resolved text-style scalar carries (the browser-honoured
twin of the PDF face-slot selection). `none` when no node declares one. -/
def styleOne : Html.Node → Option String
  | .text _ => none
  | .style _ => none
  | .script _ _ => none
  | .elem _ attrs kids =>
    match attrs.find? (fun (k, _) => k == "style") with
    | some (_, v) => some v
    | none => styleList kids.toList

def styleList : List Html.Node → Option String
  | [] => none
  | k :: rest => match styleOne k with
    | some v => some v
    | none => styleList rest

end

mutual

/-- The text an emitted page *shows*, as the artifact itself says it: the
typed tree's characters with every `hidden` subtree dropped — what the UA
stylesheet's `[hidden] { display: none }` removes, and so the HTML twin of
a shipped PDF page's ink. `nodeTextOne` reads the whole tree, which is the
declaration; this reads what a reader with no snap state sees, which is
step 1. The distinction is what the census could not make when overlay
alternation put both groups inside one visible wrapper. -/
def shownTextOne (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ attrs kids =>
    if attrs.any (fun (k, _) => k == "hidden") then acc
    else shownTextList acc kids.toList

def shownTextList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => shownTextList (shownTextOne acc k) rest

end

/-- How many times `needle` is declared in an emitted tree: `pageOccurs`'s
twin over the HTML artifact. -/
def treeOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((nodeTextList "" nodes.toList).splitOn needle).length - 1

/-- How many times `needle` is *shown* by an emitted tree, hidden subtrees
excluded: the HTML side of `pageOccurs`, and the check that was missing
when an alternation shipped both its groups on one page. -/
def treeShownOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((shownTextList "" nodes.toList).splitOn needle).length - 1

mutual

/-- Every chrome footer in the emitted deck, in document order, as its two
slots' text: the HTML side of the footline fact. The spans carry their
declared side as a class (`Ir.Chrome.footBand` through `emitTree`), and the
stylesheet pins each to its edge. -/
def slideFootsOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    if tag == "footer" &&
        attrs.any (fun (k, v) => k == "class" && (v.splitOn "slide-foot").length > 1) then
      let slotText (cls : String) : String :=
        kids.foldl (fun s k => match k with
          | .elem _ kattrs _ =>
            if kattrs.any (fun (a, v) => a == "class" && v == cls) then
              nodeTextOne s k
            else s
          | _ => s) ""
      acc.push ((slotText "band-left").trimAscii.toString,
        (slotText "band-right").trimAscii.toString)
    else slideFootsList acc kids.toList

def slideFootsList (acc : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => slideFootsList (slideFootsOne acc k) rest

end

/-- Every chrome footer the PDF ships, in page order, as its two slots' text:
`PageOut.foot` is the one footline declaration resolved per page
(`Ir.Chrome.footBand`), each slot naming its side, and the physical pass
applied exactly as the final layout pass applies it. -/
def pdfFoots (out : Layout.Out) : Array (String × String) := Id.run do
  let mut res : Array (String × String) := #[]
  let total := out.pages.size
  for h : i in [0:out.pages.size] do
    if let some band := out.pages[i].foot then
      let text (side : Ir.BandSide) : String :=
        (band.filter (·.side == side)).foldl (fun acc s =>
          acc ++ (Ir.plainText (Layout.substPage (i + 1) total s.content))) ""
      res := res.push ((text .left).trimAscii.toString,
        (text .right).trimAscii.toString)
  return res

/-- Adjacent equal pairs collapsed: the pages of one stepped frame share
their footer, and the HTML has one section per frame. -/
def dedupConsecutive (xs : Array (String × String)) : Array (String × String) :=
  xs.foldl (fun acc p => if acc.back? == some p then acc else acc.push p) #[]

mutual

/-- Every element of an emitted tree with its subtree text and its own
style attribute, for the epoch checks: which node carries a redefinition
is a fact of the typed tree, never of a rendered string. -/
def elemStylesOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := acc.push (nodeTextOne "" (.elem t attrs kids),
      (((attrs.find? (·.1 == "style")).map (·.2)).getD ""))
    elemStylesList acc kids.toList

def elemStylesList (acc : Array (String × String)) : List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => elemStylesList (elemStylesOne acc k) rest

end

/-- The source with string literals, char literals, and comments blanked, so
the emission scan below reads code proper: a code named in a docstring or a
help text is a mention, not an emission. Line comments, nested block
comments, `\"` escapes, and char literals (whose `'\"'` would otherwise read
as opening a string) are tracked. -/
def stripNonCode (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut depth := 0
  let mut inStr := false
  let mut inLine := false
  let mut esc := false
  for _ in [0:cs.size] do
    if h : i < cs.size then
      let c := cs[i]
      if inStr then
        if esc then esc := false
        else if c == '\\' then esc := true
        else if c == '"' then inStr := false
        out := out.push ' '
        i := i + 1
      else if inLine then
        if c == '\n' then
          inLine := false
          out := out.push '\n'
        else
          out := out.push ' '
        i := i + 1
      else if depth > 0 then
        if c == '-' && cs[i + 1]? == some '/' then
          depth := depth - 1
          i := i + 2
        else if c == '/' && cs[i + 1]? == some '-' then
          depth := depth + 1
          i := i + 2
        else
          out := out.push (if c == '\n' then '\n' else ' ')
          i := i + 1
      else if c == '/' && cs[i + 1]? == some '-' then
        depth := 1
        i := i + 2
      else if c == '-' && cs[i + 1]? == some '-' then
        inLine := true
        i := i + 2
      else if c == '\'' && cs[i + 1]? == some '\\' then
        -- an escaped char literal ('\n', '\\', '\"', '\u00a0'): skip to its
        -- closing quote
        let mut j := i + 2
        for _ in [0:8] do
          if cs[j]? == some '\'' then break
          j := j + 1
        for _ in [i:j+1] do
          out := out.push ' '
        i := j + 1
      else if c == '\'' && cs[i + 2]? == some '\'' && cs[i + 1]? != some '\'' then
        -- a plain char literal ('x')
        out := out ++ "   "
        i := i + 3
      else if c == '"' then
        inStr := true
        out := out.push ' '
        i := i + 1
      else
        out := out.push c
        i := i + 1
    else break
  return out

/-- Is this token one diagnostic code (`E0330`)? -/
def isDiagCode (s : String) : Bool :=
  match s.toList with
  | [k, a, b, c, d] =>
    (k == 'E' || k == 'W' || k == 'N') && [a, b, c, d].all Char.isDigit
  | _ => false

/-- The `DiagCode` constructors a stripped source applies: every dot-applied
code-shaped token (`.E0304`, `DiagCode.E0502`). -/
def appliedCodes (stripped : String) : List String := Id.run do
  let mut out : List String := []
  for part in (stripped.splitOn ".").drop 1 do
    let tok := String.ofList (part.toList.takeWhile Char.isAlphanum)
    if isDiagCode tok && !out.contains tok then
      out := tok :: out
  return out

/-- The engine's sources as the emission scans read them: every `LeanTex/`
module and the driver, path-sorted, with the codes each applies. The
registry itself (`Diag.lean`) names every code and emits none, so it is
left out. -/
def codeSources : IO (Array (String × List String)) := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  let mut out : Array (String × List String) := #[]
  for f in files.qsort (·.toString < ·.toString) do
    if f.toString == "LeanTex/Core/Diag.lean" then continue
    out := out.push (f.toString, appliedCodes (stripNonCode (← IO.FS.readFile f)))
  return out

/-- A document laid out as the driver hands it to the backends: math
alphabet scopes resolve against the selected face before the fallback census
or layout sees their scalars. Resolution diagnostics lead layout diagnostics,
as they do in the driver. -/
def layoutOf (fonts : Font.FontSet) (doc : Ir.Doc)
    (geom : Layout.Geom := Layout.Geom.ofPage doc.page)
    (pats : Option Hyphen.Patterns := none)
    (imgs : Image.Store := {}) : Layout.Out :=
  let family := fonts.math.bind (fonts.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (doc, alphaDiags) := Ir.resolveMathAlphas fonts.mathAlphabets family doc
  let out := Layout.run geom fonts pats doc imgs
  { out with diags := alphaDiags ++ out.diags }

/-- The font set a golden fixture lays out under in the suite: `oneFace`,
plus the math face a build would resolve — `mathSet` (the shipped Fira
Math) when the fixture declares a math face, else `FontDb.pickMathFace`
over the shipped corpus faces when the document reaches math — plus a
fallback face per Private Use Area scalar an icon needs, found the way a
build finds it (the scan over the shipped corpus). Everything else keeps
the deliberately minimal set: the stand-in degradations are themselves
under test (`listChecks`), and a broader map would silently upgrade them.
The census and the attribution checks both lay out the corpus through
this one resolution. -/
def fixtureFontSet (oneFace mathSet : Font.FontSet) (shipped : Array FontDb.Face)
    (doc : Ir.Doc) : IO Font.FontSet := do
  let fs ← if doc.fonts.math.isSome then pure mathSet
    else if (Layout.docMathScalars doc).isEmpty then pure oneFace
    else do
      match ← FontDb.pickMathFace shipped (doc.fonts.body.getD "") with
      | some (face, _) =>
        match Font.parse (← IO.FS.readBinFile face.path) with
        | .ok f => pure { oneFace with
            fonts := oneFace.fonts.push f
            math := some oneFace.fonts.size }
        | .error _ => pure oneFace
      | none => pure oneFace
  let fs := match fs.math.bind (fs.fonts[·]?) with
    | some f => { fs with mathAlphabets := f.mathAlphabetCoverage doc.fonts.mathSources }
    | none => fs
  let uncovered := (Layout.docScalars doc).filter fun ch =>
    0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF &&
      fs.fonts.all fun f => (f.gid ch).isNone
  if uncovered.isEmpty then return fs
  let mut fs := fs
  for (ch, path) in ← FontDb.fallbackPicks shipped uncovered do
    match Font.parse (← IO.FS.readBinFile path) with
    | .ok f =>
      let idx := match fs.fonts.zipIdx.find? (fun p => p.1.family == f.family) with
        | some (_, i) => i
        | none => fs.fonts.size
      let fs' := if idx == fs.fonts.size then
          { fs with fonts := fs.fonts.push f } else fs
      fs := { fs' with fallback := fs'.fallback.push (ch, idx) }
    | .error _ => pure ()
  return fs

/-- The shipped Fira Math beside `oneFace` in the math slot: what a fixture
that declares a math face lays out under. -/
def mathSetOf (oneFace : Font.FontSet) : IO Font.FontSet := do
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"fixture fonts: FiraMath unparsable: {e}")
  return { oneFace with
    fonts := oneFace.fonts.push fira
    math := some oneFace.fonts.size
    mathAlphabets := fira.mathAlphabetCoverage {} }

/-- The four shipped Source Serif faces in every slot — regular 0, bold 1,
italic 2, bold italic 3 — and Fira Math as the math face, 4: a set in which
a run's face index says its weight, its slant, and whether it is maths.
`none` when a face does not load. -/
def serifFacesSet : IO (Option Font.FontSet) := do
  let mut loaded : Array Font.Font := #[]
  for n in #["SourceSerifPro-Regular.otf", "SourceSerifPro-Bold.otf",
      "SourceSerifPro-RegularIt.otf", "SourceSerifPro-BoldIt.otf", "FiraMath-Regular.otf"] do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    match Font.parse (← IO.FS.readBinFile p) with
    | .ok f => loaded := loaded.push f
    | .error _ => return none
  return some {
    fonts := loaded
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 2), ((slot, 700, true), 3)]).toArray
    math := some 4
    mathAlphabets := loaded[4]!.mathAlphabetCoverage {} }

/-- Every shipped line, furniture included, in page order: what a claim
about absolute placement (a fil sandwich, a frame's vertical distribution)
reads. `bodyLines` is this with the furniture filtered out. -/
def allLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines)

/-- The document's own flow lines, shipped: every line except engine-placed
furniture (`LineOut.furniture` — running content, the plain page number).
What a claim about the body's setting means; a furniture claim reads the
flag this filters out. -/
def bodyLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines.filter (!·.furniture))

/-- The x each glyph run of a shipped line starts at, with its text. -/
def metricRunsAt (l : Layout.LineOut) : Array (String × Dim.Sp) := Id.run do
  let mut x := l.x
  let mut out : Array (String × Dim.Sp) := #[]
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      unless glyphs.isEmpty do
        out := out.push (String.ofList (glyphs.toList.map (·.2.1)), x)
      x := x + w
    | .gap w _ => x := x + w
    | .rule w _ _ _ => x := x + w
    | .poly _ _ => pure ()
    | .image _ w _ => x := x + w
  return out

/-- Gaps that stand before glyph ink, excluding a paragraph's closing fill. -/
def metricInnerGaps (l : Layout.LineOut) : Array Dim.Sp := Id.run do
  let mut out : Array Dim.Sp := #[]
  let mut pending : Array Dim.Sp := #[]
  for s in l.segs do
    match s with
    | .gap w _ => pending := pending.push w
    | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
      unless glyphs.isEmpty do
        out := out ++ pending
        pending := #[]
    | .rule _ _ _ _ | .poly _ _ | .image _ _ _ => pure ()
  return out

/-- Painted inline rules on shipped body pages. -/
def metricRuleSegs (out : Layout.Out) : Array (Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .rule w h raise color => some (w, h, raise, color)
    | _ => none

/-- Sizes of glyph runs on shipped body pages. -/
def metricRunSizes (out : Layout.Out) : Array Dim.Sp :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ _ _ _ glyphs size _ _ _ _ _ => if glyphs.isEmpty then none else some size
    | _ => none

/-- A compact article wrapper for metric command checks. -/
def metricDoc (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- A metric check's source through elaboration and shipped layout. -/
def metricOut (oneFace : Font.FontSet) (body : String) : Layout.Out :=
  layoutOf oneFace (elabStr (metricDoc body)).1

/-- The glyphs a source's body lines ship, in page order — the instrument for
a claim about what a page shows, read off `Layout.Out` rather than an IR
dump. `geom` defaults to the document's own page; pass one to judge a source
against a fixed measure. -/
def pageTextOf (fonts : Font.FontSet) (src : String)
    (geom : Option Layout.Geom := none) : String :=
  let (d, _) := elabStr src
  String.join ((bodyLines (layoutOf fonts d (geom.getD (Layout.Geom.ofPage d.page)))).toList.map
    (lineText ·))

/-- The same over *every* line, furniture included: what a title bar or a
running foot ships is on the page too, so an absence claim belongs here
rather than in `pageTextOf`. -/
def allTextOf (fonts : Font.FontSet) (src : String)
    (geom : Option Layout.Geom := none) : String :=
  let (d, _) := elabStr src
  String.join ((allLines (layoutOf fonts d (geom.getD (Layout.Geom.ofPage d.page)))).toList.map
    (lineText ·))

/-- Elaboration diagnostics of a source. -/
def dvE (src : String) : Array Diag := (elabStr src).2

/-- The shipped-page census of a source laid out with `fonts`: which ink
each page carries, the artifact a claim about a branch or a label reads. -/
def censusOfSrc (fonts : Font.FontSet) (src : String) : Array CensusPage :=
  let (doc, _) := elabStr src
  censusOf (coveredColorsOf doc) (layoutOf fonts doc)

/-- The laid-out lines of a source, baseline and text: what a claim that two
spellings set one page reads. -/
def pageLines (fonts : Font.FontSet) (src : String) : Array (Array (Dim.Sp × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.text))

/-- Every shipped line of a source, position, size and text: what a claim
that two spellings ship one page reads, horizontal placement included. -/
def shippedLines (fonts : Font.FontSet) (src : String) :
    Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (censusOfSrc fonts src).flatMap fun p => p.lines.map fun l => (l.x, l.y, l.size, l.text)

/-- A source elaborated as the driver elaborates it: against the label
measurement layout sets with (`Layout.labelMetric`), so a node's extent is
measured from its letters rather than taken as nothing. -/
def elabMeasured (fonts : Font.FontSet) (s : String) : Ir.Doc × Array Diag :=
  let (toks, lds) := Lex.lex "t" s
  let (raws, pds) := Parse.parse "t" toks
  Elab.runRaws "t" raws (lds ++ pds)
    (Layout.labelMetric (Layout.Geom.ofPage (Elab.run "t" s).1.page) fonts)

/-- Does a block of the document's title block satisfy `p`? The block may
stand inside its alignment wrapper, so the probe looks one level into
`.center`. -/
def inTitleBlock (doc : Ir.Doc) (p : Ir.Block → Bool) : Bool :=
  doc.body.any fun b => p b ||
    (match b with | .center xs => xs.any p | _ => false)

/-- Diagnostics after layout too, through the same pre-layout alphabet
resolution as every test artifact. -/
def dvL (fonts : Font.FontSet) (src : String) : Array Diag :=
  let (doc, ds) := elabStr src
  ds ++ (layoutOf fonts doc).diags

/-- Diagnostics after the HTML backend. -/
def dvH (src : String) : Array Diag :=
  let (doc, ds) := elabStr src
  ds ++ (HtmlDoc.emit {} doc).2

/-- A one-face set: every slot and variant maps to index 0. Both
fontSuiteChecks and the layout dispatch build their set through this one
def, so the two can never drift. -/
def oneFaceOf (font : Font.Font) : Font.FontSet := {
  fonts := #[font]
  index := ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
}

/-- Two faces in two slots: the roman slot (0) and the sans slot (1) hold
different files, so a claim about *which family* ink set in has something
to read. `oneFaceOf` maps every slot to one file and cannot tell a serif
run from a sans one — the set a font-role fact needs is this one.
`CensusLine.runFonts` is the channel. -/
def twoSlotOf (roman sans : Font.Font) : Font.FontSet := {
  fonts := #[roman, sans]
  index := ((List.range 3).flatMap fun slot =>
    let f := if slot == 1 then 1 else 0
    [((slot, 400, false), f), ((slot, 700, false), f),
     ((slot, 400, true), f), ((slot, 700, true), f)]).toArray
}

mutual

/-- The stylesheet text the typed tree ships, in tree order. -/
def treeCssList (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => treeCssList (treeCssOne acc n) rest

def treeCssOne (acc : String) : Html.Node → String
  | .style css => acc.append css
  | .elem _ _ kids => treeCssList acc kids.toList
  | .text _ => acc
  | .script _ _ => acc

end

/-- The declarations of every stylesheet rule whose selector is `sel`
exactly, in order: the texts between their braces. -/
def cssRulesOf (css sel : String) : List String :=
  (css.splitOn "}").filterMap fun chunk =>
    match chunk.splitOn "{" with
    | [s, decls] =>
      if (s.splitOn "\n").getLast!.trimAscii.toString == sel then some decls else none
    | _ => none

/-- The declarations of the first stylesheet rule whose selector is `sel`
exactly: the text between its braces. -/
def cssRuleOf (css sel : String) : Option String := (cssRulesOf css sel).head?

/-- Read a CSS stage length and compare its share to the shipped PDF
length. One printed milli-percent is the rounding bound, independently of
viewport height. -/
def cssStageLength (style key : String) (length height : Dim.Sp) : Bool :=
  ((style.splitOn ";").findSome? fun decl => do
    let [name, value] := decl.splitOn ":" | none
    if name.trimAscii.toString != key then none else
    let value := value.trimAscii.toString
    if !value.endsWith "vh" then none else
    let (m, sc) ← Decl.parseDecimal (value.dropEnd 2).toString
    return m * 1000 / (sc : Int)).any fun m =>
      m * height ≤ length * 100000 && length * 100000 < (m + 1) * height

/-- The read-side census of produced PDF bytes, for a claim about what a
file carries (fonts embedded, filters, page count) — `PdfCensus.census`
with its refusal surfaced as the test's own failure text. -/
def pdfCensusOf (pdf : ByteArray) : Except String PdfCensus.Census :=
  PdfCensus.census pdf


mutual

/-- Every element of a tree whose tag `want` accepts, with its attributes,
in document order. -/
def elemAttrsOne (want : String → Bool) (acc : Array (String × Array (String × String))) :
    Html.Node → Array (String × Array (String × String))
  | .elem tag attrs kids =>
    elemAttrsList want (if want tag then acc.push (tag, attrs) else acc) kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def elemAttrsList (want : String → Bool) (acc : Array (String × Array (String × String))) :
    List Html.Node → Array (String × Array (String × String))
  | [] => acc
  | k :: rest => elemAttrsList want (elemAttrsOne want acc k) rest

end

/-- Every value the elements `want` accepts declare for attribute `key`, in
document order: `elemAttrsOne`'s elements, read for one attribute. -/
def attrValuesOf (want : String → Bool) (key : String) (n : Html.Node) : Array String :=
  (elemAttrsOne want #[] n).filterMap fun (_, attrs) => (attrs.find? (·.1 == key)).map (·.2)


/-- Every innermost declaration block a stylesheet carries, as its selector
text paired with its declarations. Brace-depth scanned rather than split on
`}`, so a nested at-rule's inner blocks come out under their own selectors
(the backend writes the paged deck's bar inside `@media screen`) and the
at-rule's prelude never reads as one. Total by construction: the loop is
bounded by the length and every step advances the position. -/
def artCssBlocks (css : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut sels : Array String := #[]
  let mut cur := ""
  for c in css.toList do
    if c == '{' then
      sels := sels.push cur.trimAscii.toString
      cur := ""
    else if c == '}' then
      let decls := cur.trimAscii.toString
      if decls.contains ':' then
        out := out.push ((sels.back?.getD "").trimAscii.toString, decls)
      sels := sels.pop
      cur := ""
    else
      cur := cur.push c
  return out


/-! ### The natbib fixtures the bibliography check blocks share -/

/-- The synthetic bibliography natbib's rows cite: invented people and
venues, one entry per name shape a citation prints differently — three
authors (`et al.`, and all three starred), one, two, and a lowercase
particle (`\Citet` capitalizes it). -/
def natbibBib : String :=
  "@article{alpha2019, author = {Ann Alpha and Bob Beta and Cy Gamma},\n\
    title = {A study of invented widgets}, journal = {Journal of Examples},\n\
    year = {2019}, volume = {3}, number = {2}, pages = {10--20}}\n\
  @book{delta2021, author = {Dee Delta}, title = {Placeholder Methods},\n\
    publisher = {Example Press}, year = {2021}}\n\
  @inproceedings{eps2020, author = {Eve Epsilon and Finn Zeta},\n\
    title = {On synthetic benchmarks},\n\
    booktitle = {Proceedings of the Example Workshop}, year = {2020}, pages = {1--8}}\n\
  @article{pome2018, author = {Quill de Pome}, title = {Lowercase particles},\n\
    journal = {Example Letters}, year = {2018}}\n"

/-- Entries whose label names and year coincide, so plainnat.bst's
`forward.pass`/`reverse.pass` give them letters, one more year by the same
names, one other author, and two entries the `\nocite` rows name:
invented people and titles. -/
def natbibLabelBib : String :=
  "@article{gam2019a, author = {Gil Gamma and Hal Eta}, title = {An early invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2019b, author = {Gil Gamma and Hal Eta}, title = {A later invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2020, author = {Gil Gamma and Hal Eta}, title = {A third invented result},\n\
    journal = {Journal of Examples}, year = {2020}}\n\
  @book{iota2018, author = {Ivy Iota}, title = {An Invented Book}, publisher = {Example Press},\n\
    year = {2018}}\n\
  @misc{kap2017, author = {Kai Kappa}, title = {An invented note}, year = {2017}}\n\
  @misc{lam2016, author = {Lu Lambda}, title = {An entry no citation names}, year = {2016}}\n"

/-- The calls as one document, each in its own paragraph `Lk <call> end.`;
the style is declared in the preamble, where natbib reads it back at
`\begin{document}`. -/
def natbibSrc (pre style : String) (calls : List String) : String := Id.run do
  let mut body := ""
  for call in calls, k in [1:calls.length + 1] do
    body := body ++ s!"L{k} {call} end.\n\n"
  return s!"\\documentclass\{article}\n{pre}\n\\bibliographystyle\{{style}}\n\
    \\begin\{document}\n{body}\\bibliography\{refs}\n\\end\{document}\n"

/-- An HTML page's text as a reader gets it: tags dropped, the entities
the escaper writes read back, a no-break space a space. -/
def htmlVisibleText (page : String) : String := Id.run do
  let mut out := ""
  let mut inTag := false
  for c in page.toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return ((((out.replace "&lt;" "<").replace "&gt;" ">").replace "&nbsp;" " ").replace
    "&amp;" "&").replace "\u00A0" " "

/-- The reference list's shipped lines, one array per entry: the lines after
the References heading that set glyphs (a link's underline ships as a
sibling line of rules), split where the leaf changes. -/
def bibEntryLines (lines : Array Layout.LineOut) : Array (Array Layout.LineOut) := Id.run do
  let start := ((lines.findIdx? (lineText · == "References")).map (· + 1)).getD lines.size
  let mut out : Array (Array Layout.LineOut) := #[]
  let mut cur : Array Layout.LineOut := #[]
  for l in (lines.extract start lines.size).filter hasGlyphRun do
    if !cur.isEmpty && cur.back?.map (·.leaf) != some l.leaf then
      out := out.push cur
      cur := #[]
    cur := cur.push l
  return if cur.isEmpty then out else out.push cur
