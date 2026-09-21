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

def goldenNames : List String :=
  ["paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk", "deck", "deck1610", "themed", "latex-idioms", "wrapper",
   "centering", "columns", "overlays", "overlays-blocks", "notes", "furniture",
   "chrome", "footer-left", "footer-mixed", "footer-collide", "lists",
   "lists-styled", "lists-deck", "headroom",
   "marker-styled", "marker-content",
   "trio-page", "trio-deck", "trio-card", "valign", "images", "figures", "math",
   "webpage", "quotes", "quote-deck", "outline", "outline-gap", "webnav",
   "bibliography", "resume-data",
   "icons",
   "diagram", "diagram-boundary", "diagram-overflow", "diagram-refused", "diagram-scm",
   "tables", "tables-ragged", "subfigures", "float-center",
   "math-companion", "math-first", "abstract", "crossref", "eqnum", "footnotes",
   "redefine", "titlebars", "daylight", "blocks", "poster", "listings",
   "algorithm", "lineno", "lineno-modulo"]

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

/-- Re-verify a produced PDF's cross-reference stream: every type-1 entry
must point at `N 0 obj`. Returns the number of verified offsets. -/
def checkXref (pdf : ByteArray) : Except String Nat := do
  let ascii (a b : Nat) : String :=
    String.ofList (((pdf.extract a (min b pdf.size)).toList).map fun v =>
      Char.ofNat (min v.toNat 127))
  let findLast (pat : String) : Option Nat := Id.run do
    let p := pat.toUTF8
    if pdf.size < p.size then
      return none
    for back in [0:pdf.size - p.size + 1] do
      let i := pdf.size - p.size - back
      let mut ok := true
      for k in [0:p.size] do
        if pdf[i + k]! != p[k]! then
          ok := false
          break
      if ok then
        return some i
    return none
  let find (start : Nat) (pat : String) : Option Nat := Id.run do
    let p := pat.toUTF8
    for i in [start:pdf.size - p.size + 1] do
      let mut ok := true
      for k in [0:p.size] do
        if pdf[i + k]! != p[k]! then
          ok := false
          break
      if ok then
        return some i
    return none
  let some sx := findLast "startxref" | throw "no startxref"
  let numStr := (ascii (sx + 10) (sx + 30)).splitOn "\n" |>.head!
  let some xrefOff := numStr.toNat? | throw s!"bad startxref '{numStr}'"
  let head := ascii xrefOff (xrefOff + 300)
  unless (head.splitOn " 0 obj").length ≥ 2 do
    throw "startxref does not point at an object"
  unless (head.splitOn "/Type /XRef").length ≥ 2 do
    throw "xref object is not an XRef stream"
  let some sizePart := (head.splitOn "/Size ").getLast? | throw "no /Size"
  let some size := (sizePart.splitOn " ").head?.bind (·.toNat?) | throw "bad /Size"
  let some streamAbs := find xrefOff "stream\n" | throw "no stream data"
  let dataOff := streamAbs + "stream\n".length
  -- The xref stream compresses like any writer-owned stream: the rows are
  -- read through the declared filter.
  let some lenPart := (head.splitOn " /Length ").getLast? | throw "no /Length"
  let some dataLen := (lenPart.splitOn " ").head?.bind (·.toNat?) | throw "bad /Length"
  let rows ← if (head.splitOn "/FlateDecode").length ≥ 2 then
      LeanTex.Core.Flate.inflate (pdf.extract dataOff (dataOff + dataLen)) (7 * size)
    else
      pure (pdf.extract dataOff (dataOff + dataLen))
  let mut verified := 0
  for id in [1:size] do
    let row := 7 * id
    let kind := (rows[row]!).toNat
    if kind == 1 then
      let off := ((rows[row+1]!).toNat * 256 + (rows[row+2]!).toNat) * 65536 +
        (rows[row+3]!).toNat * 256 + (rows[row+4]!).toNat
      let expect := s!"{id} 0 obj"
      let got := ascii off (off + expect.utf8ByteSize)
      unless got == expect do
        throw s!"object {id}: offset {off} holds {got.quote}, expected {expect.quote}"
      verified := verified + 1
  return verified

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
  /-- Image boxes shipped on the page: an embedded figure, or a boundary
  request's box (fulfilled or placeholder) — what the diagram-boundary
  row reads to pin that the request ships ink where the picture stood. -/
  images : Nat := 0

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
    for l in p.lines do
      let mut chars := ""
      let mut runSize : Dim.Sp := 0
      for seg in l.segs do
        match seg with
        | .run _ color _ _ glyphs size _ _ _ =>
          runSize := max runSize size
          if coveredColors.contains color then
            for (_, c) in glyphs do
              chars := chars.push c
              covered := covered.push c
          else
            for (_, c) in glyphs do
              chars := chars.push c
            covered := covered.push ' '
        | .gap _ =>
          chars := chars.push ' '
          covered := covered.push ' '
        | .rule _ th _ _ =>
          rules := rules + 1
          ruleSegs := ruleSegs.push (l.y, th)
        -- an image is decorative ink to the text census, like a rule
        | .image .. => images := images + 1
      -- The census asks where the text block stands, so a protruded
      -- line reports its measure edge: the ink deliberately hangs
      -- `l.hang` left of it (`Layout.protrudeLeft`).
      lines := lines.push { x := l.x + l.hang, y := l.y, size := runSize
                            width := l.setWidth, text := chars
                            furniture := l.furniture, counted := l.counted }
      covered := covered.push ' '
    pages := pages.push { lines := lines
                          covered := covered
                          rules := rules
                          ruleSegs := ruleSegs
                          fills := p.fills.size
                          fillRects := p.fills.map fun f => (f.x, f.y, f.w, f.h)
                          paths := p.paths.size
                          images := images }
  return pages

def hasStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def censusText (c : Array CensusPage) : String :=
  String.intercalate " " (c.toList.map (·.text))

def pageHas (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.text needle).getD false

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
    | .run _ _ _ _ glyphs _ _ _ _ => glyphs.foldl (fun s (_, c) => s.push c) s
    | .gap _ => if gapAsSpace then s.push ' ' else s
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

/-- The layout spelling nearly every test claim uses: geometry from the
document's own page, no hyphenation, no images — each overridable where a
claim needs a narrower measure, patterns, or a store. -/
def layoutOf (fonts : Font.FontSet) (doc : Ir.Doc)
    (geom : Layout.Geom := Layout.Geom.ofPage doc.page)
    (pats : Option Hyphen.Patterns := none)
    (imgs : Image.Store := {}) : Layout.Out :=
  Layout.run geom fonts pats doc imgs

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

/-- Elaboration diagnostics of a source. -/
def dvE (src : String) : Array Diag := (elabStr src).2

/-- Diagnostics after layout too. -/
def dvL (fonts : Font.FontSet) (src : String) : Array Diag :=
  let (doc, ds) := elabStr src
  ds ++ (Layout.run (Layout.Geom.ofPage doc.page) fonts none doc).diags

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

