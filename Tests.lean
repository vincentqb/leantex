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

/-- The class hook: a semantic distinction the author declares as a named
wrapper survives into the artifact as an addressable annotation. Its absence
was the audited defect — `HtmlDoc.emit ∘ elab` of `\muted{x}` and of `x`
were byte-identical, so no stylesheet could address the author's own role. -/
def classHookChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let (mutedDoc, mutedDs) :=
    elabStr (wrap "\\define \\muted(word: content) {\\word}\n" "\\muted{quiet} words")
  let (bareDoc, bareDs) := elabStr (wrap "" "quiet words")
  t "role sources clean" (mutedDs.isEmpty && bareDs.isEmpty)
  let mutedPage := (HtmlDoc.emit {} mutedDoc).1
  t "an authored role is recoverable from the artifact"
    (mutedPage != (HtmlDoc.emit {} bareDoc).1)
  t "an authored role's class reaches the page"
    ((mutedPage.splitOn "class=\"u-muted\"").length == 2)
  -- Arity reads the definition: a 0-ary command is a spelling, not a role,
  -- and splices transparently.
  let (abbrevDoc, _) :=
    elabStr (wrap "\\define \\brand {Example Corp}\n" "\\brand{} words")
  t "a zero-ary command is a spelling, not a role"
    (((HtmlDoc.emit {} abbrevDoc).1.splitOn "u-brand").length == 1)
  -- The census reads through the annotation (role_plaintext): the markdown
  -- twin renders the words, never the wrapper.
  t "the markdown twin reads through a role"
    ((((MarkdownDoc.emit mutedDoc).splitOn "quiet words").length) == 2)
  -- Both halves on one page, judged on the typed tree: a palette role
  -- resolves to its var reference, an authored role to its class — a name
  -- the palette knows adapts, a name it does not becomes addressable, and
  -- neither is silently lost.
  let (bothDoc, bothDs) := elabStr (wrap
    ("\\palette{ accent = #205E3B }\n\\define \\entry(word: content) {\\word}\n")
    "\\accent{coloured} and \\entry{classed}")
  t "both halves source clean" bothDs.isEmpty
  let bothTree := HtmlDoc.blockNode {} bothDoc.body[0]!
  let hasSpan (want : String × String) : Html.Node → Bool
    | .elem _ attrs kids => attrs.contains want || kids.any fun k =>
        match k with
        | .elem _ attrs2 kids2 => attrs2.contains want || kids2.any fun k2 =>
            match k2 with
            | .elem _ attrs3 _ => attrs3.contains want
            | _ => false
        | _ => false
    | _ => false
  t "a palette role and an authored role share a page, each addressable"
    (hasSpan ("style", "color: var(--accent, #205e3b)") bothTree &&
     hasSpan ("class", "u-entry") bothTree)
  -- The block half: a command whose expansion is block content keeps its
  -- name on a flow container.
  let (blockRoleDoc, _) := elabStr
    (wrap "\\define \\entry(a: content) {\\a\\par}\n" "\\entry{First}\n\\entry{Second}")
  t "a block-level role is an addressable div"
    (((HtmlDoc.emit {} blockRoleDoc).1.splitOn "<div class=\"u-entry\">").length == 3)

def goldenNames : List String :=
  ["paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk", "deck", "themed", "latex-idioms", "wrapper",
   "centering", "columns", "overlays", "overlays-blocks", "notes", "furniture",
   "chrome", "footer-left", "footer-mixed", "footer-collide", "lists",
   "lists-styled", "lists-deck", "headroom",
   "marker-styled", "marker-content",
   "trio-page", "trio-deck", "trio-card", "valign", "images", "math",
   "webpage", "quotes", "quote-deck", "outline", "outline-gap", "webnav",
   "icons",
   "diagram", "diagram-overflow", "tables", "tables-ragged",
   "math-companion", "math-first"]

-- KP test helpers: word/glue/forced-break item builders and a brute-force
-- optimum to cross-check the DP against.

inductive Piece where
  | W (w : Int)
  | G
  | H (w : Int)
  | B

open Piece in
def mkItems (ps : List Piece) : Array Layout.Item := Id.run do
  let mut items : Array Layout.Item := #[]
  for p in ps do
    match p with
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10) false 0)
    | .G => items := items.push (.glue { width := Dim.pt 10, stretch := Dim.pt 5, shrink := Dim.pt 3 })
    | .H w => items := items.push (.pen (Dim.pt w) Layout.hyphenPenalty true 0 Ir.Color.black #[])
    | .B =>
      items := items.push (.glue { fil := true })
      items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  items := items.push (.glue { fil := true })
  items := items.push (.pen 0 Layout.forcedCost false 0 Ir.Color.black #[])
  return items

def W (w : Int) : Piece := .W w
def G : Piece := .G
def H (w : Int := 3) : Piece := .H w
def BRK : List Piece := [.B]

/-- Total demerits of a specific break sequence (must end at the final
forced penalty), or none when it spans a forced break. -/
def seqCost (items : Array Layout.Item) (target : Dim.Sp) (breaks : List Nat) :
    Option Int := Id.run do
  let mut prev : Nat := 0
  let mut first := true
  let mut prevFlagged := false
  let mut total : Int := 0
  for b in breaks do
    let a := if first then Layout.lineStart items 0 else Layout.lineStart items (prev + 1)
    for k in [a:b] do
      if Layout.isForced items k then
        return none
    let m := Layout.measure items a b
    total := total + Layout.lineDemerits items m target b
    if prevFlagged && Layout.isFlagged items b then
      total := total + Layout.doubleHyphenDemerits
    prev := b
    prevFlagged := Layout.isFlagged items b
    first := false
  if breaks.getLast? != some (items.size - 1) then
    return none
  return some total

/-- Minimum cost over every legal break sequence (exponential; tiny inputs). -/
def bruteBest (items : Array Layout.Item) (target : Dim.Sp) : Option Int := Id.run do
  let n := items.size
  let legal := (List.range n).filter (Layout.canBreakAt items)
  let mut best : Option Int := none
  -- enumerate subsets of legal breakpoints that end at the final penalty
  let optional' := legal.filter (· != n - 1)
  let m := optional'.length
  for mask in [0:2 ^ m] do
    let mut chosen : List Nat := []
    for (b, idx) in optional'.zipIdx do
      if mask / 2 ^ idx % 2 == 1 then
        chosen := chosen ++ [b]
    match seqCost items target (chosen ++ [n - 1]) with
    | some c =>
      match best with
      | some b0 => if c < b0 then best := some c
      | none => best := some c
    | none => pure ()
  return best

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
  let mut verified := 0
  for id in [1:size] do
    let row := dataOff + 7 * id
    let kind := (pdf[row]!).toNat
    if kind == 1 then
      let off := ((pdf[row+1]!).toNat * 256 + (pdf[row+2]!).toNat) * 65536 +
        (pdf[row+3]!).toNat * 256 + (pdf[row+4]!).toNat
      let expect := s!"{id} 0 obj"
      let got := ascii off (off + expect.utf8ByteSize)
      unless got == expect do
        throw s!"object {id}: offset {off} holds {got.quote}, expected {expect.quote}"
      verified := verified + 1
  return verified

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
    let (doc, diags) := Elab.run s!"{n}.tex" src
    let out := Ir.dump doc diags
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

/-- List marking over the positioned page: enumerate shows its order per
level and a nested list resets while the enclosing counter resumes; itemize
marks depth, degrading to a stand-in only where no face covers the class
glyph; an overlay-stepped item keeps its marker on every handout page (the
slides bug); declared markers override per level and fall back to the base
element; depth past four warns and still renders. Own function: `main`'s
elaboration budget. -/
def listChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (font : Font.Font) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let runOn (src : String) : Array Layout.LineOut × Array Diag :=
    let (d, _) := Elab.run "t" src
    let out := Layout.run geom oneFace none d
    (out.pages.flatMap (·.lines), out.diags)
  let markerOf (l : Layout.LineOut) : String :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ _ _ _ glyphs _ _ _) => String.ofList (glyphs.toList.map (·.2))
    | _ => ""
  -- The numbering functions and their decoders (`\labelenum*`, classes.dtx).
  t "enum labels match the class defaults"
    (ListMark.enumLabel 1 1 == "1." && ListMark.enumLabel 2 1 == "(a)" &&
     ListMark.enumLabel 3 4 == "iv." && ListMark.enumLabel 4 2 == "B." &&
     ListMark.enumLabel 1 12 == "12." && ListMark.enumLabel 2 26 == "(z)")
  t "alph past its range degrades to arabic, distinctly"
    (ListMark.enumLabel 2 27 == "(27)")
  -- Roman injectivity, the one level the theorems leave to a decoder check:
  -- the round-trip over LaTeX's whole counter range implies it.
  t "roman round-trips over the counter range"
    ((List.range 32767).all fun k =>
      ListMark.romanVal (ListMark.romanN (k + 1)).toList == k + 1)
  -- Order is shown on the page.
  let (enumLines, _) := runOn
    "\\begin{enumerate}\\item alpha\\item beta\\item gamma\\end{enumerate}"
  t "enumerate numbers its items in order"
    (enumLines.map markerOf == #["1.", "2.", "3."])
  -- Nesting resets, the enclosing counter resumes, the level styles differ.
  let (nestLines, _) := runOn ("\\begin{enumerate}\\item one\\item two" ++
    "\\begin{enumerate}\\item inner\\item inner too\\end{enumerate}" ++
    "\\item three\\end{enumerate}")
  t "nested enumerate resets and the outer resumes"
    (nestLines.map markerOf == #["1.", "2.", "(a)", "(b)", "3."])
  -- Depth is shown: four itemize levels, each marker nonempty, adjacent
  -- levels distinct. Whether level 3 is the class asterisk or its stand-in
  -- follows the face, which is what keeps this hermetic.
  let (itemLines, _) := runOn ("\\begin{itemize}\\item a" ++
    "\\begin{itemize}\\item b\\begin{itemize}\\item c" ++
    "\\begin{itemize}\\item d\\end{itemize}\\end{itemize}\\end{itemize}\\end{itemize}")
  let marks := itemLines.map markerOf
  let lvl3 := if (font.gid '∗').isSome then "∗" else "*"
  t "itemize marks the four class levels"
    (marks == #["•", "–", lvl3, "·"])
  t "no itemize marker is empty" (marks.all (!·.isEmpty))
  t "adjacent itemize levels differ"
    (marks[0]! != marks[1]! && marks[1]! != marks[2]! && marks[2]! != marks[3]!)
  -- A stepped item keeps its marker: two items, two handout pages, a
  -- marker on every item line of both (this is the deck's page-3 bug).
  let (stepLines, _) := runOn ("\\documentclass{beamer}\n\\begin{document}\n" ++
    "\\begin{frame}\\begin{itemize}\\item<1-> alpha\\item<2-> beta" ++
    "\\end{itemize}\\end{frame}\n\\end{document}")
  t "stepped items keep their markers on every page"
    (stepLines.size == 4 && (stepLines.map markerOf).all (· == "•"))
  -- Dim-not-hide dims the marker with its item: on the first handout page
  -- the second item is covered, marker included.
  let markerColor (l : Layout.LineOut) : Option Ir.Color :=
    match l.segs[0]? with
    | some (Layout.Seg.run _ c _ _ _ _ _ _) => some c
    | _ => none
  t "a covered item's marker dims with it"
    (markerColor stepLines[1]! == some (Ir.Design.ofDoc {}).cover.plain &&
     markerColor stepLines[0]! == some Ir.Color.black)
  -- Declared markers: the base element styles every level; a level style
  -- overrides its own level only.
  let (ovLines, _) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize}{ marker = {x} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}\\end{itemize}\n" ++
    "\\end{document}")
  t "a base marker override styles every level"
    (ovLines.map markerOf == #["x", "x"])
  let (lvLines, _) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize2}{ marker = {+} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}\\end{itemize}\n" ++
    "\\end{document}")
  t "a level marker override styles its level alone"
    (lvLines.map markerOf == #["•", "+"])
  -- Depth past the class's four levels warns and still renders, reusing
  -- the fourth level's marker.
  let (deepLines, deepDiags) := runOn ("\\begin{itemize}\\item a" ++
    "\\begin{itemize}\\item b\\begin{itemize}\\item c\\begin{itemize}\\item d" ++
    "\\begin{itemize}\\item e\\end{itemize}\\end{itemize}\\end{itemize}" ++
    "\\end{itemize}\\end{itemize}")
  t "a fifth level warns W0010" (deepDiags.any (·.code == "W0010"))
  t "a fifth level still renders the fourth's marker"
    (deepLines.size == 5 && markerOf deepLines[4]! == "·")
  -- A declared marker whose glyph no face covers warns rather than
  -- vanishing silently: the diagnostics ride with the paragraph's.
  let (_, glyphDiags) := runOn ("\\documentclass{article}\n" ++
    "\\style{itemize}{ marker = {✦} }\n\\begin{document}\n" ++
    "\\begin{itemize}\\item a\\end{itemize}\n\\end{document}")
  t "an uncoverable marker glyph warns" (glyphDiags.any (·.code == "E0405"))
  -- The scalar walk offers the default marker glyphs to the driver's
  -- fallback scan, per level actually reached.
  let scalars := Layout.docScalars (Elab.run "t"
    ("\\begin{itemize}\\item a\\begin{itemize}\\item b\\end{itemize}" ++
     "\\end{itemize}")).1
  t "docScalars carries the reached default markers"
    (scalars.contains '•' && scalars.contains '–' &&
     scalars.contains '*' && scalars.contains '-' && !scalars.contains '∗')

/-- Line-level typesetting checks against a one-face set. Its own function:
`main` is a single `do` block, and Lean's elaboration budget for one block
runs out long before the tests do. -/
def lineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  -- Fixed-width spaces are kerns. Looking up a glyph at U+2009 drops the
  -- space, because a Type 1-derived face has none -- and warns instead of
  -- setting it.
  let widthOf (src : String) : Dim.Sp :=
    let (d, _) := Elab.run "t" src
    (((Layout.run geom oneFace none d).pages.flatMap (·.lines))[0]?.map
      (·.setWidth)).getD 0
  let plainW := widthOf "ab"
  let thinW := widthOf "a\\,b"
  t "thin space widens the line" (thinW == plainW + geom.fontSize / 6)
  t "thin space warns about nothing"
    ((Layout.run geom oneFace none (Elab.run "t" "a\\,b").1).diags.isEmpty)
  t "no-break space is an unbreakable interword space"
    (widthOf "a\\nbsp b" > plainW)
  -- `~` is what LaTeX authors actually type for it.
  t "tilde is a no-break space"
    ((Elab.run "t" "a~b").1.body == #[.para #[.text "a\u00a0b"]])
  t "tilde does not break the line" (widthOf "a~b" == widthOf "a\u00a0b")
  t "escaped tilde is a literal tilde"
    ((Elab.run "t" "a\\~b").1.body == #[.para #[.text "a~b"]])

  -- Small caps are synthesised: lowercase raised and set smaller, in runs
  -- that carry their own size. `\scshape` used to do nothing at all.
  let scOut := Layout.run geom oneFace none (Elab.run "t" "\\scshape aB").1
  let scRuns := (scOut.pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
    match s with
    | .run _ _ _ _ glyphs size _ _ => some (glyphs.map (·.2), size)
    | _ => none)
  t "small caps raises lowercase"
    (scRuns.all fun (cs, _) => cs.all fun c => !c.isLower)
  t "small caps sets the raised run smaller"
    (scRuns.any (·.2 == geom.fontSize * Layout.smallCapScale / 1000) &&
     scRuns.any (·.2 == geom.fontSize))

  -- `\hfill` on a paragraph's last line must reach the margin. The
  -- line-running fill is also fil glue, and sharing the leftover with it
  -- puts the right-hand text halfway there -- which is what LaTeX does and
  -- what nobody setting a row of dates wants.
  let measureOf (src : String) : Array Dim.Sp :=
    let (d, _) := Elab.run "t" src
    ((Layout.run geom oneFace none d).pages.flatMap (·.lines)).map (·.setWidth)
  -- A paragraph ending in `\\` used to vanish whole: the break's own
  -- forced penalty and the paragraph terminator left an empty last line
  -- with no feasible predecessor, and the breaker returned no lines.
  t "paragraph ending in a break keeps its content"
    ((measureOf "first line\\\\\n\nsecond").size == 2)
  let lastLine := measureOf "Left \\hfill Right"
  t "hfill reaches the margin on a final line"
    (lastLine.size == 1 && lastLine[0]! == geom.textWidth)
  let brokenLine := measureOf "Left \\hfill Right\\\\Second"
  t "hfill reaches the margin before a break"
    (brokenLine.size == 2 && brokenLine[0]! == geom.textWidth)
  -- Without an \hfill the last line stays ragged: the fill still fills.
  t "no hfill leaves the last line short"
    (brokenLine.size == 2 && brokenLine[1]! < geom.textWidth)
  -- Verbatim: one set line per code line, interior blank lines included —
  -- a blank line inside a code block used to have no feasible break and
  -- could vanish with everything after it.
  t "verbatim sets one line per code line, blanks included"
    ((measureOf "\\begin{verbatim}\na\n\nb\n\\end{verbatim}").size == 3)

/-- `\\style` and its two backends. Its own function: `main` is a single `do`
block and Lean's elaboration budget for one block is spent. -/
def styleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \style: every visual constant a backend applies to an element is a token
  -- the document can name. The font value is a template with a hole.
  let styled := elabStr ("\\documentclass{article}\\palette{ink = #112233}" ++
    "\\tokens{ sep = 3pt }" ++
    "\\style{section}{ font = {\\large\\sffamily\\ink}, before = 2 * sep, after = sep, rule = ink }" ++
    "\\style{itemize}{ indent = 1.2em, gap = sep, marker = {\\ink\\textendash} }" ++
    "\\begin{document}\\section{Head}\\begin{itemize}\\item a\\end{itemize}\\end{document}")
  t "style source clean" (styled.2.all (·.severity == .note))
  let secStyle := styled.1.styles.find? "section"
  t "style section font is a template with a hole"
    ((secStyle.bind (·.font)) == some #[.styled (.size "large") #[.styled .sans
      #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[]]]])
  t "style section spacing reads tokens"
    ((secStyle.bind (·.before)).map (·.width) == some { sp := Dim.pt 6 } &&
     (secStyle.bind (·.after)).map (·.width) == some { sp := Dim.pt 3 })
  t "style section rule names the palette entry"
    ((secStyle.bind (·.rule)).map (·.2) == some (some "ink"))
  let listStyle := styled.1.styles.find? "itemize"
  t "style itemize marker is content"
    ((listStyle.bind (·.marker)) == some #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[.text "–"]])
  -- A declared marker either reaches HTML as declared or the substitution
  -- is named (W0331): the résumé's colour-and-size shape is expressible in
  -- a ::marker rule (CSS Pseudo-Elements 4 §4.1), arbitrary inline content
  -- is not. `markerCss?_text` is the theorem that the expressed content is
  -- exactly the declared characters.
  let dash : Ir.Color := { r := 0x20, g := 0x5E, b := 0x3B }
  t "markerCss? expresses colour and size around text"
    (HtmlDoc.markerCss? #[.colored dash (some "markerink")
        #[.styled (.size "small") #[.text "–"]]] ==
      some { text := "–"
             decls := #["color: var(--markerink, #205e3b);", "font-size: 0.9em;"] })
  t "markerCss? expresses bold plain text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "»"]] ==
      some { text := "»", decls := #["font-weight: 600;"] })
  t "markerCss? refuses an image marker"
    (HtmlDoc.markerCss? #[.image "rects.png" {} ""] == none)
  t "markerCss? refuses a link marker"
    (HtmlDoc.markerCss? #[.link "https://example.org" #[.text "x"]] == none)
  t "markerCss? refuses a wrapper beside text"
    (HtmlDoc.markerCss? #[.styled .bold #[.text "a"], .text "b"] == none)
  let markerDoc (m : String) : Ir.Doc :=
    (elabStr ("\\documentclass{article}\\palette{ markerink = #205E3B }" ++
      s!"\\style\{itemize}\{ marker = \{{m}} }" ++
      "\\begin{document}\\begin{itemize}\\item a\\end{itemize}\\end{document}")).1
  let (styledMarkerPage, styledMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\textcolor{markerink}{\\small\\endash}")
  t "html styled marker reaches ::marker with its colour and size"
    ((styledMarkerPage.splitOn
      "{ content: \"–  \"; color: var(--markerink, #205e3b); font-size: 0.9em; }").length == 2)
  t "html styled marker is clean" (styledMarkerDs.all (·.code != "W0331"))
  let (contentMarkerPage, contentMarkerDs) :=
    HtmlDoc.emit {} (markerDoc "\\includegraphics{rects.png}")
  t "html inexpressible marker is named, not silently defaulted"
    (contentMarkerDs.any fun d => d.code == "W0331" && d.severity == .warning &&
      (d.message.splitOn "itemize").length > 1)
  t "html inexpressible marker emits no ::marker override"
    ((contentMarkerPage.splitOn "rects.png").length == 1)
  -- The content string is escaped: marker text cannot end its own CSS
  -- string (CSS Syntax 3 §4.3.7).
  t "css marker string escapes its delimiters"
    (HtmlDoc.cssString "a\"b\\c" == "a\\\"b\\\\c")
  t "style unknown element" (errCodes ("\\documentclass{article}\\style{footer}{ before = 1pt }" ++
    "\\begin{document}x\\end{document}") == ["E0328"])
  t "style unknown key" (errCodes ("\\documentclass{article}\\style{section}{ colour = 1pt }" ++
    "\\begin{document}x\\end{document}") == ["E0322"])
  t "fillTemplate fills the innermost hole"
    (Ir.fillTemplate #[.styled .bold #[.styled .sans #[]]] #[.text "x"] ==
      #[.styled .bold #[.styled .sans #[.text "x"]]])
  t "fillTemplate leaves plain content alone"
    (Ir.fillTemplate #[.text "–"] #[.text "x"] == #[.text "–"])
  -- The styles reach HTML as CSS on the element, with the template wrapping
  -- the heading and the rule as a class the stylesheet draws.
  let (stylePage, _) := HtmlDoc.emit {} styled.1
  t "html styled heading wraps in the template"
    ((stylePage.splitOn "<h2 class=\"ruled\"><span class=\"size-large\"><span class=\"sans\">").length == 2)
  t "html styled heading spacing" ((stylePage.splitOn "h2 { margin-top: 6pt; margin-bottom: 3pt;").length == 2)
  t "html styled list indent and gap"
    ((stylePage.splitOn "ul { padding-left: 1.2em; }").length == 2 &&
     (stylePage.splitOn "ul > li { margin-top: 3pt; }").length == 2)
  -- Font-relative lengths keep their unit. `1.2em` once became `120%`, which
  -- for padding is a fraction of the container: every styled list left the page.
  t "css em keeps its unit" (HtmlDoc.cssLength { em := 1200 } == "1.2em")
  t "css ex keeps its unit" (HtmlDoc.cssLength { ex := 1500 } == "1.5ex")
  t "css whole em has no fraction" (HtmlDoc.cssLength { em := 2000 } == "2em")
  t "css mixed length sums" (HtmlDoc.cssLength { sp := Dim.pt 3, em := 500 } == "calc(3pt + 0.5em)")
  -- \runninghead[from = 2]: the opening page carries no furniture.
  let (fromDoc, fromDs) := elabStr ("\\documentclass{article}\\runninghead[from = 2]{x}" ++
    "\\begin{document}y\\end{document}")
  t "running from clean" (fromDs.isEmpty && fromDoc.runningFrom == 2)

/-- The HTML article layout is a faithful degradation of the PDF page: the
measure, fill rows, link colour, and heading rules all follow the IR. Its own
function, same elaboration-budget reason. -/
def htmlLayoutChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The measure is the page's text width over the base font size, in em so
  -- it scales with the browser font. It used to be a fixed 68ch, an
  -- unrelated design the PDF page never asked for.
  t "html measure derives from the default page"
    (HtmlDoc.measureEm {} == "46.8em")
  let (narrowDoc, narrowDs) := elabStr ("\\documentclass{article}" ++
    "\\page{ hmargin = 0.75in }\\begin{document}x\\end{document}")
  t "html measure follows a declared page" (narrowDs.isEmpty &&
    ((HtmlDoc.emit {} narrowDoc).1.splitOn "--measure: 50.4em;").length == 2)
  -- Exactly two fill groups reserve the right group's max-content width,
  -- then let the left group wrap in what remains. More groups retain the
  -- general flex semantics instead of pretending to be a two-column row.
  let hasClass (name : String) (attrs : Array (String × String)) : Bool :=
    attrs.any fun (key, value) =>
      key == "class" && (value.splitOn " ").contains name
  let (entryDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left label \\hfill 2021\\end{document}")
  let entryTree := HtmlDoc.blockNode {} entryDoc.body[0]!
  let entryPage := (HtmlDoc.emit {} entryDoc).1
  t "html two-group fill row selects the pair contract"
    (match entryTree with
    | .elem "p" attrs kids =>
      hasClass "entry-pair" attrs && kids.size == 2 && kids.all fun child =>
        match child with
        | .elem "span" childAttrs _ => hasClass "group" childAttrs
        | _ => false
    | _ => false)
  t "html pair allocates the right max-content column first"
    ((entryPage.splitOn
      "grid-template-columns: minmax(0, 1fr) max-content;").length == 2)
  t "html pair stacks to one column only at a narrow viewport"
    ((entryPage.splitOn "@media (max-width: 30rem)").length == 2 &&
     (entryPage.splitOn "grid-template-columns: minmax(0, 1fr);").length == 2)
  t "html a stacked last group right-aligns"
    ((entryPage.splitOn ".group:last-child { text-align: right; }").length == 2)
  let (manyDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill middle \\hfill right\\end{document}")
  t "html three-group fill row retains general semantics"
    (match HtmlDoc.blockNode {} manyDoc.body[0]! with
    | .elem "p" attrs kids =>
      hasClass "entry" attrs && !hasClass "entry-pair" attrs && kids.size == 3
    | _ => false)
  let (rowsDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "a \\hfill b\\\\c \\hfill d\\end{document}")
  t "html broken two-group rows select the pair contract"
    (((HtmlDoc.emit {} rowsDoc).1.splitOn
      "<span class=\"entry-row entry-pair\"><span class=\"group\">").length == 3)
  -- The anchor itself carries inheritance, so a host framework cannot remap
  -- links away from the document or enclosing IR colour.
  let (linkDoc, linkDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{https://example.org}{invented link}\\end{document}")
  let inheritedLink :=
    "<a href=\"https://example.org\" style=\"color: inherit\">invented link</a>"
  t "html link source is clean" linkDs.isEmpty
  t "html links inherit in every CSS mode"
    ([HtmlDoc.CssMode.own, .bulma, .none].all fun mode =>
      (((HtmlDoc.emit { css := mode } linkDoc).1.splitOn inheritedLink).length == 2))
  let bulmaPage := (HtmlDoc.emit { css := .bulma } linkDoc).1
  t "bulma does not remap links to the accent"
    ((bulmaPage.splitOn "--bulma-link:").length == 1)
  t "html link keeps a visible focus"
    ((entryPage.splitOn "a:focus-visible { outline:").length == 2)
  -- A heading rule sits on the text baseline, where the PDF draws it, not at
  -- the heading's vertical middle.
  let (ruledDoc, _) := elabStr ("\\documentclass{article}\\palette{ ink = #112233 }" ++
    "\\style{section}{ rule = ink }\\begin{document}\\section{H}\\end{document}")
  t "html heading rule aligns at the baseline"
    (((HtmlDoc.emit {} ruledDoc).1.splitOn
      "h2 { display: flex; align-items: baseline;").length == 2)

/-- Article sections become anchored containers: `<section id="slug">` wraps
the heading and its content, ids stay unique under repeated titles, and an
in-page `\href{#...}` has a real target. Invented titles throughout. -/
def anchorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Opening paragraph.\\section*{Signal Path}First.\\section*{Noise}Second." ++
    "\\section*{Noise}Third.\\end{document}")
  let page := (HtmlDoc.emit {} doc).1
  t "html anchors source is clean" ds.isEmpty
  t "html level-1 sections become containers with slug ids"
    ((page.splitOn "<section id=\"signal-path\">").length == 2 &&
     (page.splitOn "<section id=\"noise\">").length == 2)
  t "html a repeated title takes a numbered anchor"
    ((page.splitOn "<section id=\"noise-2\">").length == 2)
  t "html content before the first section stays outside the containers"
    (match (page.splitOn "Opening paragraph.")[0]? with
     | some before => (before.splitOn "<section").length == 1
     | none => false)
  t "html every container closes" ((page.splitOn "</section>").length == 4)
  -- Identifier fidelity: HTML §3.2.6 forbids only ASCII whitespace in an id
  -- and the WHATWG URL fragment percent-encode set excludes non-ASCII, so a
  -- title's own letters — accented or CJK — survive into its anchor instead
  -- of degrading to hyphens. Invented titles.
  let (intlDoc, intlDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Café Notes}First.\\section*{概要}Second." ++
    "\\section*{Caf Notes}Third.\\end{document}")
  let (intlPage, intlDiags) := HtmlDoc.emit {} intlDoc
  t "html accented anchors keep their letters" (intlDs.isEmpty &&
    (intlPage.splitOn "<section id=\"café-notes\">").length == 2)
  t "html cjk anchors keep their characters"
    ((intlPage.splitOn "<section id=\"概要\">").length == 2)
  t "html titles that folded together under the ascii rule stay distinct"
    ((intlPage.splitOn "<section id=\"caf-notes\">").length == 2 &&
     intlDiags.isEmpty)
  -- Two distinct titles that still fold to the same slug: the ids stay
  -- unique and W0320 names the collision, because a link written from the
  -- second title's text would silently reach the first section.
  let (clashDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Signal Path}One.\\section*{Signal, Path}Two.\\end{document}")
  let (clashPage, clashDiags) := HtmlDoc.emit {} clashDoc
  t "html a folded collision of distinct titles warns W0327"
    (clashDiags.any (·.code == "W0327"))
  t "html the colliding sections still take distinct anchors"
    ((clashPage.splitOn "<section id=\"signal-path\">").length == 2 &&
     (clashPage.splitOn "<section id=\"signal-path-2\">").length == 2)
  t "html a repeated identical title numbers quietly"
    (!ds.any (·.code == "W0327") &&
     !(HtmlDoc.emit {} doc).2.any (·.code == "W0327"))
  -- The numbered fallback is itself an id: a title whose own slug is
  -- `noise-2` must not collide with the number handed to a repeated
  -- `Noise`. Uniqueness is per assigned id, not per base.
  let (numDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\section*{Noise}A.\\section*{Noise}B.\\section*{Noise 2}C.\\end{document}")
  let numPage := (HtmlDoc.emit {} numDoc).1
  t "html a numbered fallback never collides with a real title"
    ((numPage.splitOn "<section id=\"noise-2\">").length == 2 &&
     (numPage.splitOn "<section id=\"noise-2-2\">").length == 2)
  let (navDoc, navDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{#trailhead}{jump}\\section*{Trailhead}Body.\\end{document}")
  let navPage := (HtmlDoc.emit {} navDoc).1
  t "html an in-page link reaches its section anchor" (navDs.isEmpty &&
    (navPage.splitOn "<a href=\"#trailhead\"").length == 2 &&
    (navPage.splitOn "<section id=\"trailhead\">").length == 2)
  -- Slides keep their own sectioning: one <section> per frame, none per title.
  let (deck, _) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "html slides sectioning is untouched"
    (((HtmlDoc.emit {} deck).1.splitOn "<section id=").length == 1)
  -- The declared stylesheet: named by the document, linked after the inline
  -- styles in every css mode, and quoted or bare spellings agree.
  let sheetSrc (v : String) := "\\documentclass{article}" ++
    s!"\\output\{ stylesheet = {v} }\\begin\{document}x\\end\{document}"
  let (sheetDoc, sheetDs) := elabStr (sheetSrc "\"site.css\"")
  let (bareDoc, bareDs) := elabStr (sheetSrc "site.css")
  let link := "<link rel=\"stylesheet\" href=\"site.css\">"
  t "output stylesheet parses quoted and bare" (sheetDs.isEmpty && bareDs.isEmpty &&
    sheetDoc.output.stylesheet == some "site.css" &&
    bareDoc.output.stylesheet == some "site.css")
  t "html links the declared stylesheet in every css mode"
    ([HtmlDoc.CssMode.own, .bulma, .none].all fun mode =>
      ((HtmlDoc.emit { css := mode } sheetDoc).1.splitOn link).length == 2)
  t "html declared stylesheet follows the inline styles"
    (match ((HtmlDoc.emit {} sheetDoc).1.splitOn link)[0]? with
     | some before => (before.splitOn "</style>").length == 2
     | none => false)
  t "html no stylesheet, no link"
    (((HtmlDoc.emit {} doc).1.splitOn "<link rel=\"stylesheet\"").length == 1)

/-- The markdown backend: the llms.txt twin comes from the same IR as the
page. Metadata is the preamble, structure maps, decoration degrades to its
text, and a speaker note stays a side channel. Invented content. -/
def markdownChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, PhD\", subject = \"An invented person.\" }" ++
    "\\begin{document}" ++
    "Intro with \\textbf{weight} and \\href{https://example.org}{a link}." ++
    "\\section*{Field Notes}" ++
    "Label \\hfill 2021\\par" ++
    "\\begin{itemize}\\item One thing\\item Another\\end{itemize}" ++
    "\\end{document}")
  let md := MarkdownDoc.emit doc
  t "markdown source is clean" ds.isEmpty
  t "markdown metadata renders as the llms.txt preamble"
    (md.startsWith "# Alex Doe, PhD\n\n> An invented person.\n\n")
  t "markdown keeps meaning and degrades decoration"
    ((md.splitOn "Intro with **weight** and [a link](https://example.org).").length == 2)
  t "markdown reserves # for the title"
    ((md.splitOn "\n## Field Notes\n").length == 2 && (md.splitOn "\n# ").length == 1)
  t "markdown fill separates as an em dash"
    ((md.splitOn "Label — 2021").length == 2)
  t "markdown lists are lists"
    ((md.splitOn "- One thing\n- Another\n").length == 2)
  t "markdown ends with exactly one newline"
    (md.endsWith "\n" && !(md.endsWith "\n\n"))
  let (bare, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Just a body: https://example.org text.\\end{document}")
  t "markdown without metadata has no preamble"
    ((MarkdownDoc.emit bare).startsWith "Just a body:")
  let (deck, _) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}{Opening}Visible.\\note{hidden aside}\\end{frame}\\end{document}")
  let deckMd := MarkdownDoc.emit deck
  t "markdown frames are sections, notes stay out"
    ((deckMd.splitOn "## Opening").length == 2 &&
     (deckMd.splitOn "hidden aside").length == 1)
  let (esc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "under\\_score and 2*3\\end{document}")
  t "markdown escapes what would read as markup"
    (((MarkdownDoc.emit esc).splitOn "under\\_score and 2\\*3").length == 2)
  -- The declared text alternative (graphicx's alt key, LaTeX News 37)
  -- reaches both backends, and a caption does not overwrite it.
  let (img, imgDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\includegraphics[width=32pt, alt={An invented portrait}]{face.png}" ++
    "\\end{document}")
  t "image alt declares and reaches both backends" (imgDs.isEmpty &&
    (((HtmlDoc.emit {} img).1.splitOn "alt=\"An invented portrait\"").length == 2) &&
    (((MarkdownDoc.emit img).splitOn "![An invented portrait](face.png)").length == 2))
  let (figImg, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{figure}\\includegraphics[alt={Declared wins}]{face.png}" ++
    "\\caption{A caption}\\end{figure}\\end{document}")
  t "figure caption fills only an undeclared alt"
    (((HtmlDoc.emit {} figImg).1.splitOn "alt=\"Declared wins\"").length == 2)

/-- The quotation node: `{quote}` and `{quotation}` elaborate to the one
`Block.quote` (classes.dtx defines both as `\list{}{\rightmargin
\leftmargin}`; they differ only in a paragraph indent the engine cannot
spell yet). The PDF sets it inside both margins, HTML as `<blockquote>`
through the escaper, markdown as one `> `-marked block. Own function:
`main`'s elaboration budget. -/
def quoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Before.\\begin{quote}One invented line.\\end{quote}" ++
    "\\begin{quotation}First paragraph.\n\nSecond paragraph.\\end{quotation}" ++
    "After.\\end{document}")
  t "quote source is clean" ds.isEmpty
  t "quote and quotation elaborate to the one quote node"
    (doc.body.size == 4 &&
      (match doc.body[1]?, doc.body[2]? with
       | some (Ir.Block.quote q1), some (Ir.Block.quote q2) =>
         q1.size == 1 && q2.size == 2
       | _, _ => false))
  -- Markdown: `> ` marks the quoted line, and the separator between two
  -- quoted paragraphs keeps a bare `>` so the quotation stays one block
  -- (CommonMark §5.1: a block quote does not continue across a blank line).
  let md := MarkdownDoc.emit doc
  t "markdown sets the quotation as > lines"
    ((md.splitOn "> One invented line.").length == 2)
  t "markdown keeps a two-paragraph quotation one block"
    ((md.splitOn "> First paragraph.\n>\n> Second paragraph.").length == 2)
  -- HTML: the platform's own construct, built through the typed tree.
  let page := (HtmlDoc.emit {} doc).1
  t "html sets the quotation as a blockquote"
    (match (page.splitOn "<blockquote>")[1]? with
     | some rest =>
       ((rest.splitOn "</blockquote>")[0]?.map fun inner =>
         (inner.splitOn "<p>One invented line.</p>").length == 2).getD false
     | none => false)
  let (esc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{quote}2 < 3\\end{quote}\\end{document}")
  t "html escapes quoted content like any other"
    ((((HtmlDoc.emit {} esc).1.splitOn "2 &lt; 3").length == 2))
  -- Both margins move in (classes.dtx: `\rightmargin\leftmargin`): the
  -- quoted line starts one list indent past the left margin and its set
  -- width never reaches past the narrowed right edge.
  let geom : Layout.Geom := {}
  let out := Layout.run geom oneFace none doc
  let lines := out.pages.flatMap (·.lines)
  let quoted := lines.filter fun l => l.x == geom.hmargin + geom.listIndent
  t "pdf quotation indents from the left margin" (quoted.size ≥ 1)
  t "pdf quotation keeps inside the narrowed right margin"
    (quoted.all fun l =>
      decide (l.x + l.setWidth ≤ geom.hmargin + geom.textWidth - geom.listIndent))
  t "pdf prose around the quotation keeps the full measure"
    (lines.any fun l => l.x == geom.hmargin)

/-- One fact, three renderings: a heading's level maps to the same rank in
every backend — `#`-count and `h`-number are both level + 1 (the PDF side
is the census assertion that the title text ships as furniture). Stated
over the two functions the backends actually run. -/
theorem heading_renderings_agree :
    (MarkdownDoc.headingMarker 0 = "#" ∧ HtmlDoc.headingTag 0 = "h1") ∧
    (MarkdownDoc.headingMarker 1 = "##" ∧ HtmlDoc.headingTag 1 = "h2") ∧
    (MarkdownDoc.headingMarker 2 = "###" ∧ HtmlDoc.headingTag 2 = "h3") ∧
    (MarkdownDoc.headingMarker 3 = "####" ∧ HtmlDoc.headingTag 3 = "h4") := by
  decide

/-- The document title is a level-0 heading (`\maketitle`): one per
document by construction — the elaborator disables a second `\maketitle`
exactly as LaTeX does (classes.dtx: `\global\let\maketitle\relax`) — and
each backend renders the same fact: `<h1>` in HTML, `#` first in markdown
(the metadata preamble never doubles it), the LARGE bold furniture in the
PDF (census rows for outline and the deck fixtures). Own function:
`main`'s elaboration budget. -/
def titleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\title{An Invented Title}\\author{Alex Doe}\\begin{document}" ++
    "\\maketitle Body text.\\section{First}More.\\end{document}")
  t "maketitle source is clean" ds.isEmpty
  t "the title elaborates as a level-0 heading before the sections"
    (Ir.headingLevels doc.body == #[0, 1])
  let page := (HtmlDoc.emit {} doc).1
  t "html sets the title as the one h1"
    ((page.splitOn "<h1>An Invented Title</h1>").length == 2 &&
      (page.splitOn "<h1").length == 2)
  let md := MarkdownDoc.emit doc
  t "markdown opens with the title as the one # line"
    (md.startsWith "# An Invented Title\n\n" &&
      (md.splitOn "\n# ").length == 1)
  -- The metadata preamble falls back to the declared \title; with the
  -- body carrying the level-0 heading it must not state the title twice.
  t "markdown never doubles the title"
    ((md.splitOn "# An Invented Title").length == 2)
  -- A second \maketitle is a no-op, named: LaTeX typesets the title once.
  let second := "\\documentclass{article}\\title{Once}\\begin{document}" ++
    "\\maketitle\\maketitle x\\end{document}"
  t "a second maketitle warns W0322" (warnCodes second == ["W0322"])
  t "a second maketitle sets no second level-0 heading"
    (Ir.headingLevels (elabStr second).1.body == #[0])
  -- A \maketitle with nothing declared (W0309) spends nothing: the title
  -- declared later still sets.
  let late := "\\documentclass{article}\\begin{document}" ++
    "\\maketitle\\title{Late}\\maketitle x\\end{document}"
  t "an empty maketitle does not spend the title"
    (warnCodes late == ["W0309"] && Ir.headingLevels (elabStr late).1.body == #[0])
  -- Slides: the title heading stands inside the golden title frame and is
  -- still the deck's one h1.
  let (deck, deckDs) := elabStr ("\\documentclass{slides}" ++
    "\\title{An Invented Deck}\\begin{document}\\maketitle" ++
    "\\begin{frame}{One}a\\end{frame}\\end{document}")
  t "deck title source is clean" deckDs.isEmpty
  t "the deck's title frame carries the one h1"
    ((((HtmlDoc.emit {} deck).1.splitOn "<h1>An Invented Deck</h1>").length == 2) &&
      (((HtmlDoc.emit {} deck).1.splitOn "<h1").length == 2))

/-- The outline diagnostics: heading levels must not skip as the outline
descends (HTML §4.3.11's conformance rule; WCAG G141), and the title comes
first. Warnings over the IR, firing once per document; a proper ladder and
a climb back up fire nothing. Own function: `main`'s elaboration budget. -/
def outlineChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let body (s : String) := s!"\\documentclass\{article}\\begin\{document}{s}\\end\{document}"
  t "a section-to-subsubsection gap warns W0320 once"
    (warnCodes (body "\\section{A}x\\subsubsection{B}y\\subsubsection{C}z")
      == ["W0320"])
  t "a title-to-subsection gap warns W0320"
    (warnCodes ("\\documentclass{article}\\title{T}\\begin{document}" ++
      "\\maketitle\\subsection{S}x\\end{document}") == ["W0320"])
  t "a title after another heading warns W0321"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\section{A}x\\title{T}\\maketitle\\end{document}") == ["W0321"])
  t "a proper ladder warns nothing"
    (warnCodes (body "\\section{A}x\\subsection{B}y\\subsubsection{C}z") == [])
  t "climbing back up warns nothing"
    (warnCodes (body "\\section{A}x\\subsection{B}y\\section{C}z") == [])
  t "a document whose first heading is deep warns nothing"
    (warnCodes (body "\\subsection{Fragment}x") == [])


/-- `{ifbackend}`: content addressed to a subset of the backends. One IR,
elaborated once; each backend keeps or drops through `Ir.keepFor` at its own
entry. The diagnostics, the `orphanFree` correspondence (the hypothesis of
`Ir.keepFor_covers`, checked here on a real elaboration), and each backend's
kept view are pinned. Invented content. Its own function: `main` is one `do`
block and its elaboration budget is spent. -/
def backendChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "Shared opening.\\begin{ifbackend}{html}Only the page carries this." ++
    "\\end{ifbackend}\\begin{ifbackend}{pdf,md}Print and twin carry this." ++
    "\\end{ifbackend}\\end{document}")
  t "ifbackend source is clean" ds.isEmpty
  t "ifbackend carries its target set"
    (match doc.body[1]? with
     | some (Ir.Block.only targets _) => targets == #["html"]
     | _ => false)
  let htmlBody := Ir.keepFor "html" doc.body
  let mdBody := Ir.keepFor "md" doc.body
  t "keepFor keeps the addressed subtree and drops the other"
    (has (Ir.blocksText htmlBody) "Only the page carries this." &&
     !has (Ir.blocksText htmlBody) "Print and twin" &&
     has (Ir.blocksText mdBody) "Print and twin carry this." &&
     !has (Ir.blocksText mdBody) "Only the page")
  -- The theorem's hypothesis holds on the elaborated document, and its
  -- conclusion is observable: every declared leaf survives in some backend.
  t "declared content is orphan-free and every leaf survives somewhere"
    (Ir.orphanFree Ir.backendNames doc.body &&
     (Ir.textLeaves doc.body).all fun leaf =>
        Ir.backendNames.any fun b =>
          (Ir.textLeaves (Ir.keepFor b doc.body)).contains leaf)
  let page := (HtmlDoc.emit {} doc).1
  t "html emits only its own conditional content"
    (has page "Only the page carries this." && !has page "Print and twin")
  t "html marks conditional content with its target set"
    (has page "<div data-backend=\"html\">")
  let md := MarkdownDoc.emit doc
  t "markdown emits only its own conditional content"
    (has md "Print and twin carry this." && !has md "Only the page")
  -- Diagnostics: an unknown backend name (W0323), and content no backend
  -- answers (E0334) — flat by typo, or nested by empty intersection.
  t "unknown backend name warns, and an emptied set errors with it"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}{web}x\\end{ifbackend}\\end{document}")
      == ["W0323"] &&
     errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}{web}x\\end{ifbackend}\\end{document}")
      == ["E0334"])
  let nested := "\\documentclass{article}\\begin{document}" ++
    "\\begin{ifbackend}{html}\\begin{ifbackend}{pdf}Orphaned.\\end{ifbackend}" ++
    "\\end{ifbackend}\\end{document}"
  t "nested conditionals intersect to nothing and error"
    (errCodes nested == ["E0334"])
  t "orphanFree mirrors W0321 on the same document"
    (!Ir.orphanFree Ir.backendNames (elabStr nested).1.body)
  t "a missing backends group is an error"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{ifbackend}text\\end{ifbackend}\\end{document}") == ["E0304"])

/-- The navigation landmark and its two artifact-judged contracts: at most
one unlabeled `<nav>` per page (W0325 — ARIA Authoring Practices, Landmark
Regions: a repeated landmark role needs unique labels, and the engine has
no label mechanism yet) and every in-page link resolving to an anchor the
page emits (W0326 — with '#' and any-ASCII-case '#top' exempt, which the
HTML spec's fragment navigation scrolls to the top of the document). Both
judged over the emitted tree, never the IR: a backend conditional may keep
a nav on one surface only, and only the tree knows what this page carries.
Invented content. -/
def landmarkChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#field-notes}{Notes} \\href{#top}{Top}\\end{nav}" ++
    "\\section*{Field Notes}Body text.\\end{document}")
  let (page, pds) := HtmlDoc.emit {} doc
  t "nav source and page are clean" (ds.isEmpty && pds.isEmpty)
  t "nav emits the landmark element around its links"
    (has page "<nav>" && has page "</nav>" && has page "<a href=\"#field-notes\""
      && has page "<section id=\"field-notes\">")
  t "markdown keeps a nav's content transparent"
    (has (MarkdownDoc.emit doc) "[Notes](#field-notes)")
  let (two, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#a-head}{A}\\end{nav}\\begin{nav}\\href{#a-head}{B}\\end{nav}" ++
    "\\section*{A Head}x\\end{document}")
  t "a second nav landmark warns"
    (((HtmlDoc.emit {} two).2.filter (·.code == "W0325")).size == 1)
  let (kept, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#a-head}{A}\\end{nav}" ++
    "\\begin{ifbackend}{pdf}\\begin{nav}\\href{#a-head}{B}\\end{nav}\\end{ifbackend}" ++
    "\\section*{A Head}x\\end{document}")
  t "a nav another backend owns does not count against this page"
    (((HtmlDoc.emit {} kept).2.filter (·.code == "W0325")).size == 0)
  let (dangle, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\href{#nowhere}{broken} \\href{#nowhere}{again} \\href{#}{up} " ++
    "\\href{#TOP}{Top}\\section*{Somewhere}x\\end{document}")
  let ddiags := ((HtmlDoc.emit {} dangle).2.filter (·.code == "W0326"))
  t "a dangling in-page link is diagnosed once, by name, with the anchors"
    (ddiags.size == 1 &&
     ddiags.all (fun d => (d.message.splitOn "#nowhere").length > 1 &&
       ((d.help.getD "").splitOn "#somewhere").length > 1))
  t "the spec's top fragments resolve without anchors"
    (!ddiags.any fun d =>
      (d.message.splitOn "#TOP").length > 1 || (d.message.splitOn "'#'").length > 1)

/-- The markdown twin's declared name: `\output{ md = "llms.txt" }` rides
the one OutputSpec, so the driver writes the twin as served and the head's
alternate link cannot drift from the file. -/
def mdNameChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\output{ formats = html, md, md = \"llms.txt\" }" ++
    "\\begin{document}x\\end{document}")
  t "md name source clean" ds.isEmpty
  t "the declared twin name is on the output spec" (doc.output.md == some "llms.txt")
  let (page, _) := HtmlDoc.emit { mdHref := some "llms.txt" } doc
  t "the head's alternate link names the served file"
    (((page.splitOn "rel=\"alternate\" type=\"text/markdown\" href=\"llms.txt\"").length) ≥ 2)
  t "an unknown output key is still named"
    (errCodes ("\\documentclass{article}\\output{ pdfx = yes }" ++
      "\\begin{document}x\\end{document}") == ["E0322"])

/-- The pinned placement and the declared reveal: a labeled nav names its
landmark instance (so it never counts toward W0325), a pin becomes
`position: fixed` at the declared corner and offset — read by the HTML
backend alone, the PDF has no viewport — and a declared reveal ships the
scroll-driven CSS (`@supports`, declarative where the platform has it) and
the constant script fallback, judged over the emitted tree. Invented
content. -/
def pinChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let pinnedSrc := "\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#one-head}{One}\\end{nav}" ++
    "\\begin{nav}[label = Return to top, pin = bottom right, " ++
    "offset = 1.5em, reveal = 300px]\\href{#top}{Up}\\end{nav}" ++
    "\\section*{One Head}x\\end{document}"
  let (doc, ds) := elabStr pinnedSrc
  let (page, pds) := HtmlDoc.emit {} doc
  t "pinned nav source and page are clean" (ds.isEmpty && pds.isEmpty)
  t "a labeled nav names its landmark and never counts toward W0325"
    (has page "<nav aria-label=\"Return to top\"" &&
      !pds.any (·.code == "W0325"))
  t "the pin is fixed positioning at the declared corner and offset"
    (has page "position: fixed; bottom: 1.5em; right: 1.5em")
  t "the declared reveal range rides as a custom property, in points"
    (has page "--reveal-range: 225pt")
  t "the reveal ships its declarative form, and only that"
    (has page "@supports (animation-timeline: scroll())" &&
      has page "@keyframes ltx-reveal")
  -- Compatibility is the framework's job, not the engine's: where the
  -- platform lacks scroll-driven animations the control is simply visible,
  -- and no backend emits script to hide that.
  t "no backend emits script for the reveal"
    (!has page "CSS.supports" && !has page "js-reveal" &&
      !has page "addEventListener")
  -- No reveal declared: none of the machinery ships.
  let (plain, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{nav}\\href{#one-head}{One}\\end{nav}\\section*{One Head}x\\end{document}")
  let (plainPage, _) := HtmlDoc.emit {} plain
  t "no declared reveal, no reveal css"
    (!has plainPage "ltx-reveal" && !has plainPage "CSS.supports")
  -- A reveal another backend owns ships nothing here: judged over the tree.
  let (kept, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "\\begin{ifbackend}{pdf}\\begin{nav}[label = Up, pin = bottom right, " ++
    "reveal = scroll]\\href{#one-head}{Up}\\end{nav}\\end{ifbackend}" ++
    "\\section*{One Head}x\\end{document}")
  let (keptPage, _) := HtmlDoc.emit {} kept
  t "a reveal another backend owns ships nothing on this page"
    (!has keptPage "ltx-reveal" && !has keptPage "CSS.supports")
  -- The markdown twin keeps a pinned nav transparent, as any nav.
  t "markdown keeps a pinned nav transparent" (has (MarkdownDoc.emit doc) "[Up](#top)")
  -- Declaration mistakes are named, never silent.
  t "offset or reveal without a pin is named as ignored"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[reveal = scroll]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["W0110"])
  t "a corner that is not two edge words is E0321"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[pin = sideways]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["E0321"])
  t "an unknown nav key is E0322"
    (errCodes ("\\documentclass{article}\\begin{document}" ++
      "\\begin{nav}[sticky = yes]\\href{#a-head}{A}\\end{nav}" ++
      "\\section*{A Head}x\\end{document}") == ["E0322"])

/-- Interaction states are style keys, not a subsystem: `hover`/`focus`
colour an element's links in that state, `motion` is the transition between
them, and a declared motion cannot ship unguarded (`HtmlDoc.motionCss`;
WCAG 2.2 SC 2.3.3 with sufficient technique C39, the
`prefers-reduced-motion` query of CSS Media Queries 5 §12.1). The PDF path
reads none of the three keys. Invented content. -/
def interactionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let has (hay needle : String) : Bool := (hay.splitOn needle).length > 1
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\palette{ ink = #1D4ED8 }" ++
    "\\style{nav}{ hover = ink, focus = ink, motion = 150ms }" ++
    "\\begin{document}\\begin{nav}\\href{#one-head}{One}\\end{nav}" ++
    "\\section*{One Head}x\\end{document}")
  t "interaction keys parse" (ds.isEmpty &&
    ((doc.styles.find? "nav").bind (·.hover)).map (·.2) == some (some "ink") &&
    ((doc.styles.find? "nav").bind (·.motion)) == some 150)
  -- css = none ships only the declared rules, so the guard must ride with
  -- the declaration: both halves are checked on the emitted page.
  let (page, pds) := HtmlDoc.emit { css := .none } doc
  t "declared hover and focus land on the nav's links" (pds.isEmpty &&
    has page "nav a:hover { color: var(--ink, #1d4ed8); }" &&
    has page "nav a:focus-visible { outline-color: var(--ink, #1d4ed8); }")
  t "a declared motion ships with its guard even without the base sheet"
    (has page "nav a { transition: color 150ms, outline-color 150ms; }" &&
     has page ("@media (prefers-reduced-motion: reduce) " ++
       "{ nav a { transition: none; } }"))
  t "an unreadable motion duration is an error"
    (errCodes ("\\documentclass{article}\\style{nav}{ motion = fast }" ++
      "\\begin{document}x\\end{document}") == ["E0323"])

/-- The single-emission-site check for `transition:`: nothing but
`HtmlDoc.motionCss` and the base stylesheet's global reduce guard — both in
HtmlDoc.lean — may spell a transition into emitted styles. This is the
architectural half of the by-construction claim `motionCss_guarded`
states; the scan is the same shape as `diagChecks`'. -/
def motionSiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  for f in files do
    let src ← IO.FS.readFile f
    if (src.splitOn "transition:").length > 1 then
      check ref s!"transition is spelled only in HtmlDoc ({f})"
        (f.toString.endsWith "HtmlDoc.lean")

/-- Declared once, derived everywhere: every metadata fact lives in the one
`Ir.Meta` record and each surface derives its own rendering of it — the HTML
head, the llms.txt preamble, and the PDF's Info dictionary and XMP read the
same field, so no surface can drift from another (the report's principle 3).
Invented facts, example.org throughout. -/
def webMetaChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Alex Doe, PhD\", subject = \"An invented person.\"," ++
    " author = \"Alex Doe\", url = \"https://example.org/alex\"," ++
    " image = \"https://example.org/alex/card.png\", favicon = \"favicon.svg\" }" ++
    "\\begin{document}Body text.\\end{document}")
  t "web meta source is clean" ds.isEmpty
  t "web meta declares the record once"
    (doc.info.url == some "https://example.org/alex" &&
     doc.info.image == some "https://example.org/alex/card.png" &&
     doc.info.favicon == some "favicon.svg")
  let page := (HtmlDoc.emit {} doc).1
  let has (s : String) : Bool := (page.splitOn s).length ≥ 2
  t "html head links the canonical url"
    (has "<link rel=\"canonical\" href=\"https://example.org/alex\">")
  t "html head links the favicon" (has "<link rel=\"icon\" href=\"favicon.svg\">")
  t "html og facts derive from the one record"
    (has "<meta property=\"og:title\" content=\"Alex Doe, PhD\">" &&
     has "<meta property=\"og:description\" content=\"An invented person.\">" &&
     has "<meta property=\"og:url\" content=\"https://example.org/alex\">" &&
     has "<meta property=\"og:image\" content=\"https://example.org/alex/card.png\">" &&
     has "<meta property=\"og:type\" content=\"website\">")
  t "html twitter derives only its card kind; the facts fall back to og"
    (has "<meta name=\"twitter:card\" content=\"summary\">" && !has "twitter:title")
  -- The llms.txt twin is discoverable from the page: when the driver
  -- writes one beside the html, the head links it (rel=alternate,
  -- HTML §4.6.6.1; text/markdown, RFC 7763).
  let mdPage := (HtmlDoc.emit { mdHref := some "profile.md" } doc).1
  t "html links its markdown twin as the alternate representation"
    ((mdPage.splitOn ("<link rel=\"alternate\" type=\"text/markdown\" " ++
        "href=\"profile.md\">")).length == 2 &&
     !has "rel=\"alternate\"")
  let md := MarkdownDoc.emit doc
  let pdf := Pdf.write geom oneFace (Layout.run geom oneFace none doc).pages doc.info
  t "the one declared title reaches all three surfaces"
    (has "<title>Alex Doe, PhD</title>" &&
     md.startsWith "# Alex Doe, PhD\n" &&
     bytesContain pdf "/Title (Alex Doe, PhD)")
  t "the one declared url reaches the pdf as XMP dc:identifier"
    (bytesContain pdf "<dc:identifier>https://example.org/alex</dc:identifier>")
  -- JSON-LD is the same record again, as a data block. Values pass the
  -- certified JSON escaper, so a hostile title can neither end its own
  -- string nor close the script element.
  let (bare, _) := elabStr ("\\documentclass{article}" ++
    "\\pdfmeta{ title = \"Quiet Page\" }\\begin{document}x\\end{document}")
  t "html json-ld derives from the one record"
    (has "<script type=\"application/ld+json\">" &&
     has "\"@type\": \"WebPage\"" &&
     has "\"name\": \"Alex Doe, PhD\"" &&
     has "\"url\": \"https://example.org/alex\"" &&
     has "\"author\": {\"@type\": \"Person\", \"name\": \"Alex Doe\"}")
  let hostile := { bare with info := { bare.info with
    url := some "https://example.org/x"
    title := some "a\"</script><b>b" } }
  let hostilePage := (HtmlDoc.emit {} hostile).1
  t "html json-ld escapes a hostile value and survives the payload guard"
    ((hostilePage.splitOn
        "\"name\": \"a\\u0022\\u003c/script>\\u003cb>b\"").length == 2 &&
     (hostilePage.splitOn "/* removed */").length == 1)
  let barePage := (HtmlDoc.emit {} bare).1
  t "html without a declared web identity emits none of the web head"
    ((barePage.splitOn "og:").length == 1 &&
     (barePage.splitOn "rel=\"canonical\"").length == 1 &&
     (barePage.splitOn "twitter:").length == 1 &&
     (barePage.splitOn "ld+json").length == 1)

/-- `\newenvironment` wrappers: the definition binds, the halves contribute
around the content, and nothing warns. Its own function: `main` is one `do`
block and its elaboration budget is spent. -/
def wrapperChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (defs body : String) : String :=
    "\\documentclass{article}\n" ++ defs ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (doc, ds) := elabStr (pre
    "\\newenvironment{labeled}[1]{\\textbf{#1:}}{\\emph{(end)}}"
    "\\begin{labeled}{First} body \\end{labeled}")
  t "newenvironment defines a wrapper, warning nothing"
    (ds.all (·.severity == .note))
  t "wrapper argument binds and both halves contribute"
    (doc.body.size == 1 && (doc.body[0]?.map fun b => match b with
      | .para content =>
        Ir.plainText content == "First: body (end)" &&
        content.any (fun x => x == .styled .bold #[.text "First:"]) &&
        content.any (fun x => x == .styled .emph #[.text "(end)"])
      | _ => false) == some true)  -- The optional-argument spelling binds like \newcommand's.
  let (opt, optDs) := elabStr (pre
    "\\newenvironment{tag}[2][?]{\\textbf{#1/#2}}{}"
    "\\begin{tag}[a]{b} body\\end{tag}")
  t "wrapper optional argument binds" (optDs.all (·.severity == .note) &&
    (opt.body[0]?.map fun b => match b with
      | .para content => Ir.plainText content == "a/b body"
      | _ => false) == some true)
  -- \renewenvironment redefines: the last definition wins.
  let (re, _) := elabStr (pre
    "\\newenvironment{aside}{old:}{}\\renewenvironment{aside}{new:}{}"
    "\\begin{aside} body\\end{aside}")
  t "renewenvironment wins"
    ((re.body[0]?.map fun b => match b with
      | .para content => Ir.plainText content == "new: body"
      | _ => false) == some true)
  -- A built-in environment cannot be redefined, and says so.
  t "a built-in environment cannot be redefined"
    (warnCodes (pre "\\newenvironment{itemize}{x}{y}" "z") == ["W0303"])
  -- A wrapper whose content is block-shaped keeps its blocks.
  let (blk, blkDs) := elabStr (pre
    "\\newenvironment{boxed}{}{}"
    "\\begin{boxed}first\n\nsecond\\end{boxed}")
  t "wrapper around block content keeps the blocks"
    (blkDs.all (·.severity == .note) && blk.body.size == 2)

/-- `\centering` is a declaration: it centres the rest of its scope, the way
`\bfseries` sets bold. Own function, same reason. -/
def centeringChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (c1, ds1) := elabStr "{\\centering x\\par} y"
  t "centering centres the rest of its group" (ds1.isEmpty &&
    c1.body == #[.center #[.para #[.text "x"]], .para #[.text "y"]])
  -- The declaration survives a paragraph end inside the scope, as \bfseries
  -- does: both paragraphs centre.
  t "centering carries across par like other declarations"
    ((elabStr "{\\centering a\\par b}").1.body ==
      #[.center #[.para #[.text "a"]], .center #[.para #[.text "b"]]])
  -- The frame spelling, which is how every deck asks for a standout layout.
  let (fr, frDs) := elabStr ("\\documentclass{slides}\\begin{document}" ++
    "\\begin{frame}\\centering Questions?\\end{frame}\\end{document}")
  t "centering inside a frame centres its content" (frDs.isEmpty &&
    fr.body == #[.frame #[] false .center #[.center #[.para #[.text "Questions?"]]]])
  -- Inside inline content there is no block to centre; the warning stays.
  t "centering in an argument still warns"
    (warnCodes "\\textbf{\\centering x}" == ["W0108"])

/-- Units and control-name lexing: TeX's `true` units, the didot pair, and
`@` as a name character. -/
def unitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  -- TeX's true units are unscaled-by-\mag spellings of their plain
  -- counterparts (TeXbook ch. 10); with no magnification they are equal.
  t "truein is in: a \\setlength in true units declares the token"
    (let (doc, ds) := elabStr (pre "\\newlength{\\a}\\setlength{\\a}{1.75truein}\
\\newlength{\\b}\\setlength{\\b}{1.75in}")
     ds.all (·.severity != .error) &&
       (doc.tokens.find? "a").isSome && doc.tokens.find? "a" == doc.tokens.find? "b")
  t "truebp scales a decimal exactly like bp"
    (Decl.parseLength "0.5truebp" == Decl.parseLength "0.5bp")
  -- The didot and cicero keep TeX's own relation: 1 cc = 12 dd.
  t "a cicero is twelve didots"
    ((Decl.parseLength "1cc").isSome &&
      Decl.parseLength "12dd" == Decl.parseLength "1cc")
  -- `@` is a control-name character always: `\vqb@bp` is one (unknown)
  -- name, never `\vqb` followed by stray text `@bp`.
  t "@ in a control name lexes as one name"
    (toks "\\vqb@bp" == [.ctrl "vqb@bp"])
  t "an unknown @-name is one diagnostic naming it, with no stray text"
    (let (doc, ds) := elabStr "x \\vqb@bp y"
     ds.any (fun d => d.code == "W0301" && (d.message.splitOn "vqb@bp").length > 1) &&
       doc.body == #[.para #[.text "x y"]])
  -- LaTeX's starred forms: the star means "no \par in the arguments"
  -- (definers) or "survives a page break" (\vspace*) — neither modelled,
  -- so the star is consumed with its command, never left as content.
  t "newcommand* defines like newcommand"
    ((elabStr "\\newcommand*{\\hi}{world}\\begin{document}\\hi\\end{document}").1.body
      == #[.para #[.text "world"]])
  t "renewcommand* redefines like renewcommand"
    ((elabStr "\\newcommand{\\x}{a}\\renewcommand*{\\x}{b}\\begin{document}\\x\\end{document}").1.body
      == #[.para #[.text "b"]])
  t "DeclareRobustCommand* defines like newcommand"
    ((elabStr "\\DeclareRobustCommand*{\\x}{a}\\begin{document}\\x\\end{document}").1.body
      == #[.para #[.text "a"]])
  t "vspace* becomes the same block as vspace"
    ((elabStr "\\begin{document}a\\vspace*{4pt}\nb\\end{document}").1.body ==
     (elabStr "\\begin{document}a\\vspace{4pt}\nb\\end{document}").1.body)
  -- The recovery invariant: best-effort recovery never turns a warning
  -- into an error. An unknown starred command in the preamble is one
  -- W0301; its star and arguments go with it, never surviving as content
  -- that E0313 then rejects.
  t "an unknown starred command in the preamble stays a warning"
    (let ds := (elabStr (pre "\\mystery*{a}{b}")).2
     ds.any (·.code == "W0301") && ds.all (·.severity != .error))
  t "an unknown starred command in the body keeps its argument text only"
    ((elabStr "\\begin{document}x \\mystery*{y} z\\end{document}").1.body ==
      #[.para #[.text "x y z"]])

/-- The length expression language: `\dimexpr`'s shape over declared
tokens — sums, differences, coefficients, parentheses — with eager
resolution, so absence is diagnosed and cycles are unrepresentable. -/
def exprChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  -- The chain the brief's card writes: sum of tokens, difference, TeX's
  -- coefficient form, and parentheses, all exact in sp.
  let (doc, ds) := elabStr (pre
    "\\tokens{ bleed = 9pt, safe = 9pt, w = 240pt, margin = bleed + safe, \
full = w + 2bleed, gap = bleed - 3pt, half = 0.5 * (bleed + safe) }")
  t "token arithmetic evaluates without errors" (ds.all (·.severity != .error))
  t "a + b is exact in sp"
    (doc.tokens.find? "margin" == some { width := .ofSp (Dim.pt 18) })
  t "a + 2b reads TeX's coefficient form"
    (doc.tokens.find? "full" == some { width := .ofSp (Dim.pt 258) })
  t "a - b subtracts exactly"
    (doc.tokens.find? "gap" == some { width := .ofSp (Dim.pt 6) })
  t "parentheses group before scaling"
    (doc.tokens.find? "half" == some { width := .ofSp (Dim.pt 9) })
  -- Absent is diagnosed, never defaulted: the unknown name appears in the
  -- message, and nothing resolves to zero.
  t "an unknown token in an expression is named"
    (let ds := (elabStr (pre "\\tokens{ a = b + 1pt }")).2
     ds.any fun d => d.code == "E0321" && (d.message.splitOn "'b' is not a declared token").length > 1)
  -- References resolve eagerly against what is declared so far, the
  -- \setlength{\x}{2\x} rule — so a would-be cycle is a forward
  -- reference, and a forward reference is diagnosed by name.
  t "a token cycle is a diagnosed forward reference, not a hang"
    (let ds := (elabStr (pre "\\tokens{ a = b + 1pt, b = a + 1pt }")).2
     ds.any fun d => d.code == "E0321" && (d.message.splitOn "'b'").length > 1)
  t "a self-reference reads the earlier value, as TeX's 2\\x does"
    ((elabStr (pre "\\tokens{ a = 4pt, a = 2a }")).1.tokens.find? "a"
      == some { width := .ofSp (Dim.pt 8) })
  t "a bare number in an expression needs a unit"
    (let ds := (elabStr (pre "\\tokens{ a = 3 + 2pt }")).2
     ds.any (·.code == "E0321"))
  t "expressions work through \\setlength's TeX spelling"
    (let (d2, ds2) := elabStr (pre
      "\\newlength{\\ca}\\setlength{\\ca}{4pt}\\newlength{\\cb}\
\\setlength{\\cb}{2pt}\\newlength{\\cm}\\setlength{\\cm}{\\ca+\\cb}\
\\newlength{\\ch}\\setlength{\\ch}{\\ca+2\\cb}")
     ds2.all (·.severity != .error) &&
       d2.tokens.find? "cm" == some { width := .ofSp (Dim.pt 6) } &&
       d2.tokens.find? "ch" == some { width := .ofSp (Dim.pt 8) })

/-- `\vspace{\fill}` and `\vfill`: TeX's first-order infinite glue, whose
share of the page's leftover is what places the content. Asserted over
`Layout.Out` — the claim is about where lines land, never about an IR
dump. -/
def filChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let linesOf (src : String) : Array Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    (Layout.run geom oneFace none d).pages.flatMap (·.lines)
  let doc (body : String) : String :=
    s!"\\documentclass\{article}\\begin\{document}{body}\\end\{document}"
  let top := linesOf (doc "hello")
  let mid := linesOf (doc "\\vspace*{\\fill}\nhello\n\\vspace*{\\fill}")
  let low := linesOf (doc "\\vspace*{\\fill}\nhello")
  t "the fill sandwich centres its page"
    (match top[0]?, mid[0]?, low[0]? with
     | some a, some b, some c =>
       -- strictly between top-flush and bottom-flush, and nearer neither
       -- edge than a line of text: the two fils split the leftover.
       a.y < b.y && b.y < c.y &&
         (b.y - a.y - (c.y - b.y)).natAbs ≤ 1
     | _, _, _ => false)
  t "a leading fill alone pushes content to the bottom"
    (match low[0]?, mid[0]? with
     | some c, some b => c.y > b.y
     | _, _ => false)
  t "a trailing fill alone moves nothing"
    ((linesOf (doc "hello\n\\vspace*{\\fill}")).map (·.y) == top.map (·.y))
  -- A minipage is one column of declared width: the column model reused,
  -- not a parallel box model.
  t "minipage is one column of its declared width"
    ((elabStr (doc "\\begin{minipage}{0.5\\textwidth}x\\end{minipage}")).1.body ==
      #[.columns #[(some 500, #[.para #[.text "x"]])]])
  t "a bare textwidth minipage takes the whole measure"
    ((elabStr (doc "\\begin{minipage}{\\textwidth}x\\end{minipage}")).1.body ==
      #[.columns #[(some 1000, #[.para #[.text "x"]])]])
  t "minipage alignment options are a note, never an error"
    (let ds := (elabStr (doc "\\begin{minipage}[c][2cm][t]{\\textwidth}x\\end{minipage}")).2
     ds.all (·.severity != .error) && ds.any (·.code == "N0102"))
  -- \pagebreak: the declared boundary, asserted over the shipped pages.
  let pagesOf (src : String) : Nat :=
    let (d, _) := Elab.run "t" src
    (Layout.run geom oneFace none d).pages.size
  t "pagebreak opens a fresh page"
    (pagesOf (doc "one\\pagebreak\ntwo") == 2)
  t "newpage and clearpage are the same boundary"
    (pagesOf (doc "one\\newpage\ntwo") == 2 &&
     pagesOf (doc "one\\clearpage\ntwo") == 2)
  t "adjacent pagebreaks never make a blank page"
    (pagesOf (doc "one\\pagebreak\\pagebreak\ntwo") == 2)
  t "a trailing pagebreak adds no empty page"
    (pagesOf (doc "one\\pagebreak") == 1)
  -- Native declarations in the body: \palette and \tokens apply where
  -- they stand (LaTeX's \colorlet and \setlength are body-legal); the
  -- preamble-only rest are named as misplaced declarations, never as
  -- unknown commands.
  t "a body palette colours what follows and reaches the document"
    (let (d, ds) := elabStr (doc "\\palette{ accent2 = #7C3AED }\\textcolor{accent2}{x}")
     ds.all (·.severity != .error) && ds.all (·.code != "W0304") &&
       d.palette.find? "accent2" == some { r := 0x7C, g := 0x3A, b := 0xED })
  t "a body colorlet aliases a preamble colour"
    (let (d, _) := elabStr
      "\\documentclass{article}\\definecolor{a}{HTML}{112233}\
\\begin{document}\\colorlet{b}{a}x\\end{document}"
     d.palette.find? "b" == some { r := 0x11, g := 0x22, b := 0x33 })
  t "a body setlength declares its token"
    ((elabStr (doc "\\setlength{\\x}{4pt}y")).1.tokens.find? "x"
      == some { width := .ofSp (Dim.pt 4) })
  t "a preamble-only declaration in the body is W0340, not unknown"
    (let ds := (elabStr (doc "x\n\n\\page{ size = a5 }\n\ny")).2
     ds.any (·.code == "W0340") && ds.all (·.code != "W0301") &&
       ds.all (·.severity != .error))
  -- CMYK: the print model survives as declared. The PDF paints DeviceCMYK
  -- with the declared components (asserted over the written bytes); the
  -- screen preview is the CSS Color 4 device-cmyk naive conversion, pinned
  -- here so it cannot drift silently.
  let (cdoc, cds) := elabStr
    "\\documentclass{article}\\definecolor{ink}{cmyk}{0,.83,.76,.07}\
\\begin{document}\\textcolor{ink}{x}\\end{document}"
  t "a cmyk definecolor lands in the palette with its components"
    (cds.all (·.severity != .error) && cds.all (·.code != "W0102") &&
      cdoc.palette.find? "ink" == some (Ir.Color.ofCmyk 0 830 760 70))
  t "the cmyk screen preview is the CSS device-cmyk conversion"
    (Ir.Color.ofCmyk 0 830 760 70 ==
      { r := 237, g := 40, b := 57, cmyk := some (0, 830, 760, 70) })
  let cpdf := Pdf.write geom oneFace (Layout.run geom oneFace none cdoc).pages cdoc.info
  t "the pdf paints a cmyk colour in DeviceCMYK, components as declared"
    (bytesContain cpdf "0 0.83 0.76 0.07 k")
  t "the html backend converts, explicitly, to the preview"
    (((HtmlDoc.emit {} cdoc).1.splitOn
        (HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70))).length ≥ 2 &&
      HtmlDoc.cssColor (Ir.Color.ofCmyk 0 830 760 70) == "#ed2839")
  -- The print boxes follow from the declared bleed: pageBoxes_nest proves
  -- TrimBox ⊆ BleedBox ⊆ MediaBox with the trim at the declared size;
  -- this pins that the written page dictionary carries all three.
  let (bdoc, bds) := elabStr
    "\\documentclass{card}\\page{ bleed = 3mm }\\begin{document}x\\end{document}"
  let bgeom := Layout.Geom.ofPage bdoc.page
  let bpdf := Pdf.write bgeom oneFace (Layout.run bgeom oneFace none bdoc).pages bdoc.info
  let (media, bleedBox, trim) := Pdf.pageBoxes bgeom.pageW bgeom.pageH bgeom.bleed
  t "a declared bleed writes trim, bleed and art boxes as consequences"
    (bds.all (·.severity != .error) &&
     bytesContain bpdf s!"/TrimBox {trim.render}" &&
     bytesContain bpdf s!"/BleedBox {bleedBox.render}" &&
     bytesContain bpdf s!"/ArtBox {trim.render}" &&
     bytesContain bpdf s!"/MediaBox {media.render}")
  t "zero bleed writes no boxes: the defaults already say all boxes coincide"
    (let (zdoc, _) := elabStr "\\documentclass{card}\\begin{document}x\\end{document}"
     let zgeom := Layout.Geom.ofPage zdoc.page
     let zpdf := Pdf.write zgeom oneFace (Layout.run zgeom oneFace none zdoc).pages zdoc.info
     !bytesContain zpdf "/TrimBox" && !bytesContain zpdf "/BleedBox")

/-- LaTeX idioms translate to native declarations. Own function, same reason. -/
def compatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- LaTeX idioms translate to native declarations, each with a note that
  -- shows the shorter spelling. The document compiles as written.
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  let (geoDoc, geoDs) := elabStr (pre "\\usepackage[letterpaper,vmargin=0.5in,hmargin=0.75in,headsep=1in]{geometry}")
  t "compat geometry becomes page" (geoDs.all (·.severity != .error) &&
    geoDoc.page.vmargin == Dim.inch 1 / 2 && geoDoc.page.hmargin == Dim.inch 3 / 4)
  -- Dropped geometry keys change the page: a config loss, a warning, never
  -- a note buried behind -v.
  t "compat geometry names what it dropped as a warning"
    ((elabStr (pre "\\usepackage[headsep=1in]{geometry}")).2.any fun d =>
      d.code == "W0101" && d.severity == .warning && d.message.endsWith "headsep")
  t "compat known package is a note, unknown a warning"
    ((elabStr (pre "\\usepackage{hyperref}")).2.all (·.severity == .note) &&
     warnCodes (pre "\\usepackage{pgfplots}") == ["W0103"])
  -- The picture subset renders, so loading tikz loses nothing at the load:
  -- a shape outside the subset is named where it is drawn (W0334, E0333),
  -- never at the `\usepackage` line.
  t "compat tikz package is native; the loss lives at the picture"
    ((elabStr (pre "\\usepackage{tikz}")).2.all (·.severity == .note))
  t "compat appendixnumberbeamer is native; \\appendix warns where it stands"
    ((elabStr (pre "\\usepackage{appendixnumberbeamer}")).2.all (·.severity == .note) &&
     warnCodes ("\\documentclass{article}\n\\usepackage{appendixnumberbeamer}\n" ++
       "\\begin{document}\n\\appendix\nx\n\\end{document}") == ["W0301"])
  t "compat definecolor" ((elabStr (pre "\\definecolor{c}{HTML}{0F766E}")).1.palette.find? "c" ==
    some { r := 0x0F, g := 0x76, b := 0x6E })
  -- \setbeamercovered{transparent} asks for what the engine always does
  -- (dim-not-hide): agreement, not missing configuration — no warning.
  -- A percentage declares the covered colour; anything else (invisible,
  -- dynamic) keeps the warning naming the divergence.
  let themedPre (decls : String) : String :=
    "\\documentclass{beamer}\n\\usetheme{moloch}\n" ++ decls ++
    "\n\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  t "compat setbeamercovered transparent agrees, warning nothing"
    (warnCodes (themedPre "\\setbeamercovered{transparent}") == [])
  t "compat setbeamercovered transparent=n sets the covered fraction"
    ((elabStr (themedPre "\\setbeamercovered{transparent=25}")).1.palette.coveredFraction
      == some 25)
  -- The boundary: labMix above 100 extrapolates with a negative surface
  -- weight (color-factor F9), so no parse path may hand a fraction past
  -- the clamp. The palette route errors E0332 (tested with the palette
  -- key); this pins the compat route: out-of-range keeps the fraction
  -- unset and warns instead of forwarding the number. Unthemed, so the
  -- only possible source of a fraction is the rejected declaration.
  let barePre (decls : String) : String :=
    "\\documentclass{beamer}\n" ++ decls ++
    "\n\\begin{document}\\begin{frame}x\\end{frame}\\end{document}"
  t "compat setbeamercovered transparent=100 never reaches the fraction"
    ((elabStr (barePre "\\setbeamercovered{transparent=100}")).1.palette.coveredFraction
      == none &&
     (warnCodes (barePre "\\setbeamercovered{transparent=100}")).contains "W0104")
  t "compat setbeamercovered transparent=0 never reaches the fraction"
    ((elabStr (barePre "\\setbeamercovered{transparent=0}")).1.palette.coveredFraction
      == none)
  t "compat setbeamercovered invisible keeps the honest warning"
    (warnCodes (themedPre "\\setbeamercovered{invisible}") == ["W0104"])
  -- `professionalfonts` and `hide notes` each ask for what the engine
  -- already does — declared fonts kept, notes off the delivered pages —
  -- so both are agreement; any other argument keeps the warning.
  t "compat usefonttheme professionalfonts agrees, warning nothing"
    (warnCodes (themedPre "\\usefonttheme{professionalfonts}") == [])
  t "compat usefonttheme serif keeps the honest warning"
    (warnCodes (themedPre "\\usefonttheme{serif}") == ["W0104"])
  t "compat setbeameroption hide notes agrees, warning nothing"
    (warnCodes (themedPre "\\setbeameroption{hide notes}") == [])
  t "compat setbeameroption show notes keeps the honest warning"
    (warnCodes (themedPre "\\setbeameroption{show notes on second screen=right}")
      == ["W0104"])
  -- `\ifdefined` is decidable from the document's own definitions, so it
  -- resolves to its taken branch with a note — nothing nothing defines is
  -- undefined, which is the honest answer for another engine's primitives
  -- too. Any other `\if…` head (open-ended family, undecidable here)
  -- invalidates the extent and the skip-whole warning stays.
  t "compat ifdefined undefined keeps the else branch"
    (let (doc, ds) := elabStr "\\ifdefined\\nope A\\else B\\fi"
     doc.body == #[.para #[.text "B"]] && ds.any (·.code == "N0114") &&
       ds.all (·.severity == .note))
  t "compat ifdefined defined keeps the first branch"
    ((elabStr "\\def\\yep{1}\\ifdefined\\yep A\\else B\\fi").1.body ==
      #[.para #[.text "A"]])
  t "compat ifdefined nested resolves inside the kept branch"
    ((elabStr "\\ifdefined\\nope A\\else\\ifdefined\\nada B\\else C\\fi\\fi").1.body ==
      #[.para #[.text "C"]])
  t "compat a foreign conditional inside keeps the skip-whole warning"
    (let ds := (elabStr "\\ifdefined\\a\\ifx\\b\\c\\fi\\fi x").2
     ds.any (·.code == "W0104") && ds.all (·.code != "N0114"))
  t "compat definecolor rgb" ((elabStr (pre "\\definecolor{c}{rgb}{1,0,0.5}")).1.palette.find? "c" ==
    some { r := 255, g := 0, b := 127 })
  t "compat colorlet aliases"
    ((elabStr (pre "\\definecolor{a}{HTML}{112233}\\colorlet{b}{a}")).1.palette.find? "b" ==
      some { r := 0x11, g := 0x22, b := 0x33 })
  t "compat setlength becomes a token"
    ((elabStr (pre "\\newlength{\\r}\\setlength{\\r}{2ex}\\setlength{\\s}{0.5\\r}")).1.tokens.find? "s" ==
      some { width := { ex := 1000 } })
  t "compat hypersetup becomes pdfmeta"
    ((elabStr (pre "\\hypersetup{pdfauthor={A. Doe},pdftitle=T,colorlinks=false}")).1.info.author ==
      some "A. Doe")
  t "compat scrartcl is article"
    ((elabStr "\\documentclass{scrartcl}\\begin{document}x\\end{document}").1.docClass == "article")
  t "compat linespread is leading"
    ((elabStr (pre "\\linespread{1.04}")).1.page.leading == 1040)
  t "compat heads become one running head"
    ((elabStr (pre "\\ihead{L}\\ohead{\\thepage}")).1.head.map (·.any (· == .pageNumber)) == some true)
  -- `\par` ends a paragraph inside a scope group, with the group's
  -- declarations carried into what follows; a command's argument group is
  -- not a scope and is left to the command.
  t "par in a scope group ends the paragraph"
    ((elabStr "{\\Huge a \\par} b").1.body ==
      #[.para #[.styled (.size "Huge") #[.text "a "]], .para #[.text "b"]])
  t "par in a scope group carries the declarations"
    ((elabStr "{\\bfseries a \\par b}").1.body ==
      #[.para #[.styled .bold #[.text "a "]], .para #[.styled .bold #[.text "b"]]])
  t "a blank line in a scope group is a paragraph end too"
    ((elabStr "{\\bfseries a\n\nb}").1.body.size == 2)
  t "par in an argument group is the command's"
    ((elabStr "\\emph{a \\par b}").1.body.size == 1)
  -- A defined command whose body ends its paragraph produces one when
  -- called between paragraphs, as LaTeX's `\newcommand{\entry}[1]{...\par}`
  -- does; and a forced break at a paragraph's end is dropped, since the end
  -- already says it (it was an empty line in the PDF, an empty row in HTML).
  let (entry, _) := elabStr ("\\documentclass{article}\\define \\entry(a: content) {\\textbf{\\a}\\par}" ++
    "\\begin{document}\\entry{x}\\entry{y}\\end{document}")
  t "a body ending in par is a block" (entry.body ==
    #[.role "entry" #[.para #[.styled .bold #[.text "x"]]],
      .role "entry" #[.para #[.styled .bold #[.text "y"]]]])
  t "a trailing forced break is dropped" ((elabStr "a\\\\ \n\nb").1.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  -- The document's definitions win over every built-in it may redefine;
  -- the ones it may not are refused with W0303, never shadowed silently.
  let (own, ownDs) := elabStr ("\\documentclass{article}" ++
    "\\define \\link(u: text, l: text) {\\href{\\u}{\\underline{\\l}}}" ++
    "\\begin{document}\\link{https://example.org}{here}\\end{document}")
  t "a defined link wins over the built-in"
    (ownDs.isEmpty && own.body ==
      #[.para #[.role "link" #[.link "https://example.org" #[.underline #[.text "here"]]]]])
  t "a parameter inside a URL is the caller's text"
    (own.body == #[.para #[.role "link"
      #[.link "https://example.org" #[.underline #[.text "here"]]]]])
  t "a reserved built-in cannot be redefined"
    ((warnCodes ("\\documentclass{article}\\define \\textbf(x: content) {\\emph{\\x}}" ++
      "\\begin{document}\\textbf{a}\\end{document}")) == ["W0303"])
  -- LaTeX classes space paragraphs by indent: their parskip is zero unless
  -- KOMA's option or the parskip package says otherwise.
  t "compat koma class declares parskip zero"
    ((elabStr ("\\documentclass{scrartcl}\\begin{document}x\\end{document}")).1.page.parskip ==
      some { width := Dim.Length.ofSp 0 })
  t "compat koma parskip=half is half a line"
    (((elabStr ("\\documentclass[parskip=half]{scrartcl}\\begin{document}x\\end{document}")).1.page.parskip.map
      (·.width.em)) == some 600)
  t "compat parskip package"
    (((elabStr ("\\documentclass{article}\\usepackage{parskip}\\begin{document}x\\end{document}")).1.page.parskip.map
      (·.width.em)) == some 600)
  t "compat setlength parskip"
    ((elabStr (pre "\\setlength{\\parskip}{4pt}")).1.page.parskip == some { width := Dim.Length.ofSp (Dim.pt 4) })
  t "a native article keeps the engine's parskip"
    ((elabStr "\\documentclass{article}\\begin{document}x\\end{document}").1.page.parskip == none)
  -- \newcommand and \NewDocumentCommand become \define, with #k as \ak.
  let (ndc, ndcDs) := elabStr ("\\documentclass{article}" ++
    "\\NewDocumentCommand{\\role}{m o}{\\textbf{#1}\\IfValueT{#2}{ (#2)}}" ++
    "\\begin{document}\\role{A}[B] \\role{C}\\end{document}")
  t "compat xparse command clean" (ndcDs.all (·.severity == .note))
  t "compat xparse command expands with optional"
    (ndc.body == #[.para #[.role "role" #[.styled .bold #[.text "A"], .text " (B)"],
      .text " ", .role "role" #[.styled .bold #[.text "C"]]]])
  let (nc, _) := elabStr ("\\documentclass{article}\\newcommand{\\two}[2]{#1+#2}" ++
    "\\begin{document}\\two{a}{b}\\end{document}")
  t "compat newcommand expands" (nc.body == #[.para #[.role "two" #[.text "a+b"]]])
  -- Outside a macro body, # is a colour, not a parameter.
  t "compat hash outside a body is literal"
    ((elabStr (pre "\\palette{ p = #7C3AED }")).1.palette.find? "p" == some { r := 0x7C, g := 0x3A, b := 0xED })
  -- Body-side idioms.
  t "compat color is the declaration form"
    ((elabStr ("\\documentclass{article}\\palette{m = #888888}\\begin{document}" ++
      "a {\\color{m}b} c\\end{document}")).1.body ==
      #[.para #[.text "a ", .colored { r := 0x88, g := 0x88, b := 0x88 } (some "m") #[.text "b"], .text " c"]])
  t "compat text symbols" ((elabStr "a\\textbar b\\textperiodcentered c").1.body ==
    #[.para #[.text "a|b·c"]])
  t "compat vspace is a spaced block"
    ((elabStr "a\n\n\\vspace{3pt}\nb").1.body.any fun b => match b with
      | .spaced _ _ => true
      | _ => false)
  t "compat expl3 is skipped whole"
    (warnCodes (pre "\\ExplSyntaxOn \\cs_new:Npn \\x { } \\ExplSyntaxOff") == ["W0106"])
  t "compat inert commands vanish"
    ((elabStr "a\\noindent\\relax b").2.isEmpty)
  -- The silent list is only for constructs that change nothing the engine
  -- models; one that does (justification, hyphenation language, furniture)
  -- must name its loss instead of vanishing.
  t "compat raggedright names its loss instead of vanishing"
    ((elabStr "a\\raggedright b").2.any (·.code == "W0104"))
  t "compat pagestyle names its loss and eats its argument"
    (let (doc, ds) := elabStr "\\pagestyle{headings}a"
     ds.any (·.code == "W0104") && doc.body == #[.para #[.text "a"]])
  -- Unsupported configuration is skipped as a whole construct — command,
  -- options, arguments — with one warning naming it. It must never leak its
  -- arguments into elaboration as stray content (that was an E0313 per
  -- construct, an error cascade from a preamble the body never needed).
  -- \usetheme is no longer skipped: it rewrites to \theme (M5b).
  let beamerPre := pre ("\\usetheme{moloch}\\usefonttheme{professionalfonts}" ++
    "\\setbeamercovered{transparent}\\addtobeamertemplate{block begin}{}{\\smallskip}" ++
    "\\setbeameroption{hide notes}")
  t "compat beamer config skipped without errors" (errCodes beamerPre == [])
  -- \setbeamercovered{transparent}, \usefonttheme{professionalfonts}, and
  -- \setbeameroption{hide notes} no longer count: each agrees with what
  -- the engine already does and warns nothing. \addtobeamertemplate is
  -- the one construct left asking for templating that is not here.
  t "compat beamer config warns once per construct"
    ((warnCodes beamerPre).length == 1 && (warnCodes beamerPre).all (· == "W0104"))
  t "compat usetheme selects the bundle instead of warning"
    ((elabStr beamerPre).1.palette.find? "frametitlebg" |>.isSome)
  t "compat beamer warnings name the native spelling"
    ((elabStr (pre "\\setbeamercolor{normal text}{fg=black}")).2.any fun d =>
      d.code == "W0104" && ((d.help.getD "").splitOn "\\palette").length == 2)
  t "compat ifdefined resolves instead of skipping; untaken branch is silent"
    (warnCodes (pre "\\ifdefined\\x\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") == [])
  t "compat undecidable tex conditional skipped whole, contents included"
    (warnCodes (pre "\\ifx\\x\\y\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") ==
      ["W0104"])
  t "compat def skipped through its body"
    (errCodes (pre "\\makeatletter\\def\\verbatim@font{\\footnotesize\\ttfamily}\\makeatother") == [])
  t "compat newenvironment defines; its titlegraphic content is a dropped loss"
    (let src := pre "\\newenvironment{wrap}[1]{\\titlegraphic{#1}}{\\titlegraphic{}}"
     errCodes src == ["E0112"] && warnCodes src == ["W0104"])
  -- Overlay specifications elaborate to steps; the content stays.
  t "uncover wraps its content in a step"
    ((elabStr "a \\uncover<2>{shown} b").1.body ==
      #[.para #[.text "a ", .step 2 (some 2) #[.text "shown"], .text " b"]])
  t "pause between words steps the rest of the scope"
    ((elabStr "a \\pause b").1.body ==
      #[.para #[.text "a"], .step 2 none #[.para #[.text "b"]]])
  t "unnumbered overlay specs warn once for the whole document"
    ((warnCodes "\\uncover<+->{a} \\uncover<.->{b}").length == 1)
  t "item overlay spec wraps the item"
    ((elabStr "\\begin{itemize}\\item<1-> one\\end{itemize}").1.body ==
      #[.list false #[#[.step 1 none #[.para #[.text "one"]]]]])
  t "compat alert is textbf"
    ((elabStr "\\alert{hot}").1.body == #[.para #[.styled .bold #[.text "hot"]]])
  t "compat bigskip is a spaced block"
    ((elabStr "a\n\n\\bigskip\nb").1.body.any fun b => match b with
      | .spaced _ _ => true
      | _ => false)
  let koma := elabStr (pre ("\\definecolor{ink}{HTML}{112233}\\newlength{\\s}\\setlength{\\s}{3pt}" ++
    "\\setkomafont{section}{\\large\\sffamily\\color{ink}}" ++
    "\\RedeclareSectionCommand[beforeskip=2\\s,afterskip=1\\s]{section}" ++
    "\\setlist[itemize]{leftmargin=1.2em,itemsep=\\s,label={\\color{ink}\\textendash}}" ++
    "\\makeatletter\\renewcommand\\sectionlinesformat[4]{#3#4 \\textcolor{ink}{\\leaders\\hrule\\hfill}}\\makeatother" ++
    "\\thispagestyle{empty}\\ihead{L}"))
  t "compat koma section font" ((koma.1.styles.find? "section").bind (·.font) ==
    some #[.styled (.size "large") #[.styled .sans #[.colored { r := 0x11, g := 0x22, b := 0x33 } (some "ink") #[]]]])
  t "compat koma section spacing"
    (((koma.1.styles.find? "section").bind (·.before)).map (·.width) == some { sp := Dim.pt 6 })
  t "compat koma section rule" (((koma.1.styles.find? "section").bind (·.rule)).map (·.2) == some (some "ink"))
  t "compat enumitem list" (((koma.1.styles.find? "itemize").bind (·.gap)).map (·.width) == some { sp := Dim.pt 3 } &&
    ((koma.1.styles.find? "itemize").bind (·.marker)).isSome)
  t "compat thispagestyle empty starts running content on page 2" (koma.1.runningFrom == 2)
  -- A \sectionlinesformat body that is not the rule idiom is a dropped
  -- loss and errors; an empty body asks for no decoration and is silent.
  t "compat unrecognised sectionlinesformat body is a dropped loss"
    (errCodes (pre "\\renewcommand\\sectionlinesformat[4]{\\raisebox{-1pt}{#3}}") ==
      ["E0113"])
  t "compat empty sectionlinesformat body is deliberate silence"
    ((elabStr (pre "\\renewcommand\\sectionlinesformat[4]{}")).2.all
      (·.severity == .note))

  -- A diagnostic inside an \input file names that file, not the including
  -- one, in the body and in the preamble both.
  let sub (file src : String) : Array Parse.Raw :=
    (Parse.parse file (Lex.lex file src).1).1
  let (inDoc, inDs) := Elab.runRaws "main.tex"
    #[Parse.Raw.env (Parse.inputEnv "sub.tex")
        (sub "sub.tex" "\\begin{mystery}kept\\end{mystery}") ⟨1, 1⟩]
  t "input body diagnostics name the included file"
    ((inDs.filterMap (·.span)).any (·.file == "sub.tex") &&
     inDoc.body == #[.para #[.text "kept"]])
  let (_, preDs) := Elab.runRaws "main.tex"
    (#[Parse.Raw.env (Parse.inputEnv "pre.tex") (sub "pre.tex" "\\mystery{x}") ⟨1, 1⟩] ++
      sub "main.tex" "\\begin{document}y\\end{document}")
  t "input preamble diagnostics name the included file"
    ((preDs.filterMap (·.span)).any (·.file == "pre.tex") &&
     !(preDs.filterMap (·.span)).any (·.file == "main.tex"))

  styleChecks ref
  htmlLayoutChecks ref
  classHookChecks ref
  anchorChecks ref
  markdownChecks ref
  backendChecks ref
  landmarkChecks ref
  pinChecks ref
  mdNameChecks ref
  interactionChecks ref
  motionSiteChecks ref

/-- A synthetic face for resolution-order tests: pure data, no host fonts. -/
def synthFace (family : String) (path : String := "") : FontDb.Face :=
  { path := if path.isEmpty then "/x/" ++ family ++ ".ttf" else path
    family := family
    subfamily := "Regular"
    bold := false
    italic := false
    fixedPitch := false
    weight := 400 }

/-- The font diagnostics: a missing family suggests its neighbours instead of
dumping a thousand names, and `families` is linear in the face count. -/
def fontDiagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fams := #["Nimbus Sans L", "Nimbus Mono", "Latin Modern Roman", "Arial",
    "Libertinus Serif", "Libertinus Sans", "DejaVu Sans"]
  let near := FontDb.nearest fams "Nimbus Roman"
  t "nearest shares a word" (near.contains "Nimbus Sans L" && near.contains "Nimbus Mono")
  t "nearest ranks two shared words first"
    ((FontDb.nearest fams "Libertinus Serif Display")[0]? == some "Libertinus Serif")
  t "nearest omits the unrelated" (!near.contains "Arial" && !near.contains "DejaVu Sans")
  t "nearest of nothing alike is empty" ((FontDb.nearest fams "Zapfino").isEmpty)
  t "nearest caps at eight"
    ((FontDb.nearest ((List.range 20).map fun i => s!"Test Face {i}").toArray "Test").size ≤ 8)
  -- families must be linear in the face count. The shape that made the
  -- quadratic version cost two seconds was a TeX Live tree: ~3000 faces in
  -- ~1000 families, so `seen` grew to a thousand names re-normalised for
  -- every face. Synthesised here in that shape — the suite reads no host
  -- fonts — with distinct families, so dedupe is checked exactly too.
  let many := ((List.range 3000).map fun i => synthFace s!"Family {i / 3}" s!"/x/{i}.otf").toArray
  let t0 ← IO.monoMsNow
  let fams' := FontDb.families many
  -- Consumed before the clock is read again: a pure `let` floats to its
  -- first use, so a timing with nothing between the two reads measures
  -- nothing (the quadratic version "took 0 ms" that way; forced, 21 s).
  t "families dedupes" (fams'.size == 1000)
  let ms := (← IO.monoMsNow) - t0
  t s!"families is linear ({ms} ms for {many.size} faces)" (ms < 200)
  -- A fontspec name like "Alpha Sans Light" is no family, but it names a
  -- face: family plus subfamily matches it, its italic sibling comes along,
  -- and its true bold is honestly unsatisfied rather than silently heavier.
  let light : FontDb.Face := { synthFace "Alpha Sans" "/x/as-l.otf" with
    subfamily := "Light", weight := 300 }
  let lightIt : FontDb.Face := { light with
    path := "/x/as-li.otf", subfamily := "Light Italic", italic := true }
  let faces := #[synthFace "Alpha Sans", light, lightIt]
  t "family plus subfamily names a face"
    ((FontDb.resolve faces "Alpha Sans Light" {}).map (·.1.subfamily) == some "Light")
  t "the named face's italic sibling resolves satisfied"
    ((FontDb.resolve faces "Alpha Sans Light" { italic := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Light Italic", true))
  t "the named face's bold is unsatisfied, never silently heavier"
    ((FontDb.resolve faces "Alpha Sans Light" { bold := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Light", false))
  t "a real family name still resolves its regular"
    ((FontDb.resolve faces "Alpha Sans" {}).map (·.1.subfamily) == some "Regular")

/-- fontspec's per-variant face options (`BoldFont=` and siblings) reach the
font spec and win over the family's own variant; a declared face the host
lacks degrades with a message that says the declaration could not be met and
names the face actually used. -/
def declaredFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  -- The compat layer carries the four face options into the spec.
  let d := (elabStr (pre ++ "\\setsansfont[ItalicFont={Alpha Sans Light Italic}, " ++
    "BoldFont={Alpha Sans}, BoldItalicFont={Alpha Sans Italic}]{Alpha Sans Light}" ++
    post)).1.fonts
  t "compat sans family" (d.sans == some "Alpha Sans Light")
  t "compat BoldFont" (d.faceFor 1 true false == some "Alpha Sans")
  t "compat ItalicFont" (d.faceFor 1 false true == some "Alpha Sans Light Italic")
  t "compat BoldItalicFont" (d.faceFor 1 true true == some "Alpha Sans Italic")
  t "compat no UprightFont declared" (d.faceFor 1 false false == none)
  -- ...from either side of the name, a file name included.
  let d2 := (elabStr (pre ++
    "\\setsansfont{Open Sans}[Path = fonts/, BoldFont = OpenSans-Bold.ttf]" ++ post)).1.fonts
  t "compat BoldFont after the name" (d2.faceFor 1 true false == some "OpenSans-Bold.ttf")
  -- The native spelling.
  let d3 := (elabStr (pre ++ "\\fonts{ body = \"X\", body.bold = \"Y\", " ++
    "mono.upright = \"Z\" }" ++ post)).1.fonts
  t "fonts body.bold" (d3.faceFor 0 true false == some "Y")
  t "fonts mono.upright" (d3.faceFor 2 false false == some "Z")
  t "fonts unknown variant key" (errCodes (pre ++ "\\fonts{ body.slanted = \"Y\" }" ++ post)
    == ["E0322"])
  t "fonts variant wrong type" (errCodes (pre ++ "\\fonts{ body.bold = 12 }" ++ post)
    == ["E0323"])
  -- Resolution: the declared face wins over the family's own variant.
  let light : FontDb.Face := { synthFace "Alpha Sans" "/x/as-l.otf" with
    subfamily := "Light", weight := 300 }
  let lightIt : FontDb.Face := { light with
    path := "/x/as-li.otf", subfamily := "Light Italic", italic := true }
  let faces := #[synthFace "Alpha Sans", light, lightIt]
  t "declared bold face is honoured, no warning"
    ((FontDb.resolveVariant faces "Alpha Sans Light" (some "Alpha Sans") { bold := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Regular", none))
  t "declared italic face is honoured"
    ((FontDb.resolveVariant faces "Alpha Sans" (some "Alpha Sans Light Italic")
      { italic := true }).map (fun r => (r.1.subfamily, r.2)) == some ("Light Italic", none))
  -- A declared face the host lacks: family fallback, message says so.
  t "declared face the host lacks degrades and says so"
    ((FontDb.resolveVariant faces "Alpha Sans Light" (some "Nope Sans") { bold := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Light", some
        ("'Alpha Sans Light' declares 'Nope Sans' as its bold face, " ++
         "which is not installed; 'Alpha Sans Light' substitutes")))
  -- No declaration: the substitution message names the face actually used.
  t "substitution names the face actually used"
    ((FontDb.resolveVariant faces "Alpha Sans Light" none { bold := true }).map (·.2) ==
      some (some "'Alpha Sans Light' has no bold face; 'Alpha Sans Light' substitutes"))
  t "a satisfied variant carries no message"
    ((FontDb.resolveVariant faces "Alpha Sans" none {}).map (·.2) == some none)
  t "a missing family is still the caller's E0403"
    ((FontDb.resolveVariant faces "Nope Sans" (some "Also Nope") { bold := true }).isNone)
  -- A declared file name denotes that exact scanned face.
  let shipped ← FontDb.scanRoots [testFonts]
  t "a declared file name denotes that exact face"
    ((FontDb.resolveVariant shipped "Open Sans" (some "SourceSerifPro-Bold.otf")
      { bold := true }).map (fun r => (r.1.path, r.2)) ==
      some (testFonts ++ "/SourceSerifPro-Bold.otf", none))

/-- Icons: the fontawesome5 spellings elaborate to `Inline.icon` — the
package's own name-to-scalar table, a required text alternative — layout
sets the glyph from whichever face the per-scalar chain covers it with,
deliberately and without the W0009 substitution warning, and an icon no
face covers is the ordinary coverage loss (E0405). HTML hides the glyph
from assistive technology and names the icon on its wrapper (WCAG 2.2
SC 1.1.1); the markdown twin renders the text alternative itself. -/
def iconChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (doc, ds) := elabStr (wrap
    "\\faGithub{} \\faIcon{arrow-up} \\faIcon[label = Return to top]{arrow-up} x")
  t "icons source clean" ds.isEmpty
  let icons : Array (Char × String) := match doc.body[0]? with
    | some (Ir.Block.para xs) => xs.filterMap fun x => match x with
      | Ir.Inline.icon c label => some (c, label)
      | _ => none
    | _ => #[]
  t "the per-icon command carries the package's scalar and Font Awesome's label"
    (icons[0]? == some ('\uF09B', "GitHub"))
  t "the generic spelling resolves by icon name"
    (icons[1]? == some ('\uF062', "arrow-up"))
  t "label = overrides the default text alternative"
    (icons[2]? == some ('\uF062', "Return to top"))
  t "an unknown icon name is E0340, dropped"
    (errCodes (wrap "\\faIcon{no-such-icon} x") == ["E0340"])
  t "an unmodelled \\faIcon option is named W0110"
    (warnCodes (wrap "\\faIcon[regular]{envelope} x") == ["W0110"])
  -- HTML: the glyph is aria-hidden, the accessible name rides the wrapper.
  let page := (HtmlDoc.emit {} doc).1
  let has (n : String) : Bool := (page.splitOn n).length ≥ 2
  t "html hides the glyph and names the icon"
    (has ("<span class=\"icon\" role=\"img\" aria-label=\"GitHub\">" ++
      "<span aria-hidden=\"true\">\uF09B</span></span>"))
  t "html carries the overridden name"
    (has "aria-label=\"Return to top\"")
  -- Every icon has an accessible name: an empty aria-label is
  -- unrepresentable upstream (the constructor requires a label), and the
  -- rendered page witnesses it.
  t "no icon renders with an empty accessible name" (!has "aria-label=\"\"")
  -- The markdown twin renders the text alternative.
  let md := MarkdownDoc.emit doc
  t "markdown renders the text alternative, never the raw scalar"
    ((md.splitOn "GitHub").length ≥ 2 && (md.splitOn "\uF09B").length == 1)
  -- Layout: the icon sets from the covering face without a substitution
  -- warning; no coverage is the ordinary E0405.
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"icons: {name} unparsable: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let iconsFace ← load "ExampleIcons-Regular.ttf"
  -- post.italicAngle is the PDF descriptor's derivation: the parser reads
  -- the face's own declared slant, zero when it declares none.
  let italicFace ← load "OpenSans-Italic.ttf"
  t "the parser reads the declared slant from post"
    (italicFace.italicAngle == -12 && sans.italicAngle == 0)
  t "coverage premise: only the invented icon face has U+F09B"
    ((sans.gid '\uF09B').isNone && (iconsFace.gid '\uF09B').isSome)
  let allVariants (slot idx : Nat) : List ((Nat × Bool × Bool) × Nat) :=
    [((slot, false, false), idx), ((slot, true, false), idx),
     ((slot, false, true), idx), ((slot, true, true), idx)]
  let bare : Font.FontSet := {
    fonts := #[sans, iconsFace]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let mapped : Font.FontSet := { bare with fallback := #[('\uF09B', 1)] }
  let geom : Layout.Geom := {}
  let (glyphDoc, _) := elabStr (wrap "\\faGithub{} beside words")
  let out := Layout.run geom mapped none glyphDoc
  let runs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  t "the icon glyph ships from the covering face"
    (runs.any fun s => match s with
      | .run 1 _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '\uF09B')
      | _ => false)
  t "a deliberate icon face is not a substitution warning"
    (!out.diags.any (·.code == "W0009"))
  let dropOut := Layout.run geom bare none glyphDoc
  t "an uncovered icon is the ordinary coverage loss, naming the scalar"
    ((dropOut.diags.filter (·.code == "E0405")).any
      fun d => (d.message.splitOn "U+F09B").length ≥ 2)
  -- The icon scalar enters the same fallback precompute text does.
  t "docScalars carries the icon scalar" ((Layout.docScalars glyphDoc).contains '\uF09B')

/-- Per-glyph fallback: a scalar the styled face lacks is set from the face
the driver's map names, at the same size; the diagnostic is one line per
family+glyph, naming both families; a scalar no face covers is still an
honest E0405 naming the family; and a document whose faces cover their text
is untouched by the map — byte-identical output. The pick order over scanned
faces is the documented one, not scan order. -/
def fallbackChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"fallback: {name} unparsable: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let code ← load "SourceCodePro-Regular.otf"
  t "coverage premise: only the code face has U+2200"
    ((sans.gid '∀').isNone && (code.gid '∀').isSome)
  t "coverage premise: no shipped face has U+27E8"
    ((sans.gid '⟨').isNone && (code.gid '⟨').isNone)
  let geom : Layout.Geom := {}
  let allVariants (slot idx : Nat) : List ((Nat × Bool × Bool) × Nat) :=
    [((slot, false, false), idx), ((slot, true, false), idx),
     ((slot, false, true), idx), ((slot, true, true), idx)]
  let bare : Font.FontSet := {
    fonts := #[sans, code]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 1).toArray
  }
  let mapped : Font.FontSet := { bare with fallback := #[('∀', 1)] }
  -- The mapped face sets the glyph, at the styled size, in its own run.
  let (faDoc, faDs) := Elab.run "t" "for all is ∀ set\n\nagain ∀ here"
  t "fallback source clean" faDs.isEmpty
  let out := Layout.run geom mapped none faDoc
  let runs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  t "fallback sets the glyph from the mapped face"
    (runs.any fun s => match s with
      | .run 1 _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '∀')
      | _ => false)
  t "fallback reports once per family+glyph, naming both faces"
    ((out.diags.filter (·.code == "W0009")).map (·.message) ==
      #["'Open Sans' has no glyph for '∀' (U+2200); set from 'Source Code Pro'"])
  t "a covered scalar raises no E0405" (!out.diags.any (·.code == "E0405"))
  -- No face covers it: dropped once per family+glyph, family named.
  let (dropDoc, _) := Elab.run "t" "lost ⟨ here\n\nand ⟨ there"
  let dropOut := Layout.run geom mapped none dropDoc
  t "an uncovered scalar drops once, naming the family"
    ((dropOut.diags.filter (·.code == "E0405")).map (·.message) ==
      #["'Open Sans' has no glyph for '⟨' (U+27E8); dropped"])
  -- A document whose faces cover their text is untouched by the map.
  let (plainDoc, _) := Elab.run "t" "plain words only"
  let noMap := Pdf.write geom bare (Layout.run geom bare none plainDoc).pages
  let withMap := Pdf.write geom
    { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
    (Layout.run geom { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
      none plainDoc).pages
  t "a covered document is byte-identical under any map" (noMap == withMap)
  -- The document's scalars: text and titles, uppercase for small caps,
  -- verbatim content, no whitespace and no fixed-space kerns.
  let (scDoc, _) := Elab.run "t"
    "\\section{Tz}\n\n{\\scshape hi}\\,x\n\n\\begin{verbatim}q r\\end{verbatim}"
  let scalars := Layout.docScalars scDoc
  t "docScalars carries text, titles, and verbatim"
    (scalars.contains 'T' && scalars.contains 'z' && scalars.contains 'x' &&
      scalars.contains 'q' && scalars.contains 'r')
  t "docScalars carries the uppercase small caps set"
    (scalars.contains 'H' && scalars.contains 'I')
  t "docScalars excludes whitespace and kerns"
    (!scalars.contains ' ' && !scalars.contains '\u2009' && !scalars.contains '\u00a0')
  t "docScalars is sorted" (scalars == scalars.qsort (· < ·))
  -- The scanned-face pick order is documented: families in normalised order,
  -- upright regular first — never scan luck.
  let shipped ← FontDb.scanRoots [testFonts]
  let picks ← FontDb.fallbackPicks shipped #['∀', '₿', '𓀀']
  t "picks the first covering family in sorted order"
    (picks.contains ('∀', testFonts ++ "/FiraMath-Regular.otf"))
  t "picks the regular face of a family with variants"
    (picks.contains ('₿', testFonts ++ "/SourceSerifPro-Regular.otf"))
  t "a scalar no face covers is absent from the picks"
    (!picks.any (·.1 == '𓀀'))
  -- The undeclared-math resolution over the shipped faces, branch by
  -- branch: a body with a sourced pairing row and its companion installed
  -- gets the companion; one with no row gets the first MATH-table face
  -- under the documented order; a scan with no MATH face at all gets none
  -- (and layout degrades with W0003, pinned in mathChecks).
  t "companion branch: Fira Sans finds Fira Math with its sourced row"
    ((← FontDb.pickMathFace shipped "Fira Sans").map
        (fun (f, r) => (f.family, (r.map (·.license)).getD "")) ==
      some ("Fira Math", "SIL Open Font License"))
  t "no-companion branch: the first MATH-table face serves, rowless"
    ((← FontDb.pickMathFace shipped "Source Serif Pro").map
        (fun (f, r) => (f.family, r.isNone)) == some ("Fira Math", true))
  t "no MATH face anywhere: the pick is none"
    ((← FontDb.pickMathFace
        (shipped.filter fun f => !(f.path.endsWith "FiraMath-Regular.otf"))
        "Fira Sans").isNone)
  t "every pairing row names a face, a source, and a licence"
    (FontDb.mathCompanions.all fun p =>
      !p.body.isEmpty && !p.companion.isEmpty && !p.source.isEmpty && !p.license.isEmpty)
  -- The order axioms pickCompanion_set_eq assumes — faceLt transitive,
  -- asymmetric, total — hold over the shipped faces, and the pick really is
  -- scan-order independent there: the theorem's hypotheses, witnessed.
  t "faceLt is asymmetric over the shipped faces"
    (shipped.all fun f => shipped.all fun g =>
      !(FontDb.faceLt f g && FontDb.faceLt g f))
  t "faceLt is total over the shipped faces"
    (shipped.all fun f => shipped.all fun g =>
      f.path == g.path || FontDb.faceLt f g || FontDb.faceLt g f)
  t "faceLt is transitive over the shipped faces"
    (shipped.all fun f => shipped.all fun g => shipped.all fun h =>
      !(FontDb.faceLt f g && FontDb.faceLt g h) || FontDb.faceLt f h)
  t "pickCompanion answers the same for the reversed scan"
    ((FontDb.pickCompanion shipped.reverse "Fira Sans").map (·.2.path) ==
      (FontDb.pickCompanion shipped "Fira Sans").map (·.2.path))
  -- Malformed and missing candidates stay total: no answer, never an abort.
  t "tableImage of a missing file is none"
    ((← FontDb.tableImage "/nonexistent/leantex-x.otf" (fun _ => true)).isNone)
  let corrupt := System.FilePath.mk "/tmp" / "leantex-test-corrupt-fallback.otf"
  IO.FS.writeBinFile corrupt ("OTTO".toUTF8 ++ ByteArray.mk (Array.replicate 40 0xff))
  t "a corrupt candidate yields no cmap image"
    ((← FontDb.tableImage corrupt.toString (· == "cmap")).isNone)
  IO.FS.removeFile corrupt

  -- The document's own faces outrank the host's: the documented order
  -- picks Fira Math for '∀' (asserted above), but a preference on the
  -- Source Code Pro path — a document that ships that face — wins.
  let prefPicks ← FontDb.fallbackPicksPreferring
    (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['∀']
  t "a preferred (document-shipped) face answers first for what it covers"
    (prefPicks.contains ('∀', testFonts ++ "/SourceCodePro-Regular.otf"))
  t "what a preferred face leaves uncovered still reaches the full scan"
    (((← FontDb.fallbackPicksPreferring
        (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['\uF09B']).find?
      (·.1 == '\uF09B')).any (fun e => (e.2.splitOn "ExampleIcons").length ≥ 2))

/-- The band projection over synthetic outlines: the invariant is that no
ink inside the band escapes the reported intervals, whatever its shape —
wholly inside the band, spanning it, or dipping into it at a curve
extremum. Scanline sampling missed the first and clipped the extent of
slanted strokes; the projection cannot. Band `[-100, -50]` matches the
shipped CFF faces' scale. -/
def inkGeometryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let iv (cmds : Array Ink.Cmd) (minY : Int) : Array (Int × Int) :=
    Ink.bandIntervals ⟨cmds, minY⟩ (-100) (-50)
  -- A rectangle wholly inside the band, spanning no scanline a sampler
  -- would choose: its projection is still its full width.
  let floatRectCmds : Array Ink.Cmd := #[.move 100 (-60), .line 200 (-60),
    .line 200 (-70), .line 100 (-70)]
  let floatRect := iv floatRectCmds (-70)
  t "ink: contour wholly inside the band is covered"
    (floatRect.size == 1 && floatRect.all fun (lo, hi) => lo ≤ 100 && hi ≥ 200)
  -- A tall rectangle spanning the band: the interior comes from the midline
  -- fill, not just the side edges.
  let tallRectCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .line 400 (-200), .line 300 (-200)]
  let tallRect := iv tallRectCmds (-200)
  t "ink: contour spanning the band covers its full width"
    (tallRect.size == 1 && tallRect.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  -- A band-spanning contour with a curved side: chord vertices come from
  -- flattening, and one landing on the fill scanline drops the crossing
  -- pair there, so the stroke's interior vanishes from the report. The
  -- control point is chosen so a flattener that does not force even doubled
  -- coordinates puts its k=4 chord vertex exactly on the band's midline
  -- scanline (doubled y −149).
  let curvedSpanCmds : Array Ink.Cmd := #[.move 300 0, .line 400 0,
    .quad 405 (-49) 400 (-200), .line 300 (-200)]
  let curvedSpan := iv curvedSpanCmds (-200)
  t "ink: curve-sided contour spanning the band covers its full width"
    (curvedSpan.size == 1 && curvedSpan.all fun (lo, hi) => lo ≤ 300 && hi ≥ 400)
  -- A shallow curve dipping into the band: the lens between the quadratic
  -- and its chord lies inside, and its whole x-extent is reported even
  -- though only the extremum neighbourhood reaches the band's midline.
  let dipCmds : Array Ink.Cmd := #[.move 500 (-60), .quad 550 (-90) 600 (-60)]
  let dip := iv dipCmds (-75)
  t "ink: curve extremum reports the whole lens extent"
    (dip.size == 1 && dip.all fun (lo, hi) => lo ≤ 502 && hi ≥ 598)
  -- A slanted stroke through the band: ink between the entry and exit
  -- depths is continuous, so the report is one interval over the whole
  -- crossing, not samples with gaps.
  let slantCmds : Array Ink.Cmd := #[.move 700 (-40), .line 750 (-110),
    .line 770 (-110), .line 720 (-40)]
  let slant := iv slantCmds (-110)
  t "ink: slanted stroke is one gap-free interval"
    (slant.size == 1 && slant.all fun (lo, hi) => lo ≤ 709 && hi ≥ 761)
  -- Contours clear of the band report nothing.
  t "ink: contour above the band is empty"
    ((iv #[.move 0 0, .line 50 0, .line 50 (-40), .line 0 (-40)] (-40)).isEmpty)
  t "ink: contour below the band is empty"
    ((iv #[.move 0 (-120), .line 50 (-120), .line 50 (-160), .line 0 (-160)]
      (-160)).isEmpty)
  -- The coverage invariant against an oracle that shares nothing with the
  -- implementation: Float flattening at 32 chords and a half-open crossing
  -- rule, which counts exactly one of two edges meeting at a vertex on the
  -- scanline and so cannot lose a crossing pair there. Every ink run the
  -- oracle finds, at any height inside the band, must lie inside the
  -- reported intervals (2 font units of slack for the flattening
  -- difference).
  let oracleRuns (cmds : Array Ink.Cmd) (y : Float) : Array (Float × Float) := Id.run do
    let mut edges : Array (Float × Float × Float × Float) := #[]
    let mut cx : Float := 0
    let mut cy : Float := 0
    let mut sx : Float := 0
    let mut sy : Float := 0
    let mut opened := false
    for c in cmds do
      match c with
      | .move x yv =>
        if opened && (cx != sx || cy != sy) then
          edges := edges.push (cx, cy, sx, sy)
        cx := Float.ofInt x
        cy := Float.ofInt yv
        sx := cx
        sy := cy
        opened := true
      | .line x yv =>
        edges := edges.push (cx, cy, Float.ofInt x, Float.ofInt yv)
        cx := Float.ofInt x
        cy := Float.ofInt yv
      | .quad qx qy x yv =>
        let x0 := cx
        let y0 := cy
        let x1 := Float.ofInt qx
        let y1 := Float.ofInt qy
        let x2 := Float.ofInt x
        let y2 := Float.ofInt yv
        for k in [1:33] do
          let s := Float.ofNat k / 32
          let u := 1 - s
          let px := u * u * x0 + 2 * u * s * x1 + s * s * x2
          let py := u * u * y0 + 2 * u * s * y1 + s * s * y2
          edges := edges.push (cx, cy, px, py)
          cx := px
          cy := py
      | .cube ax ay bx by' x yv =>
        let x0 := cx
        let y0 := cy
        let x1 := Float.ofInt ax
        let y1 := Float.ofInt ay
        let x2 := Float.ofInt bx
        let y2 := Float.ofInt by'
        let x3 := Float.ofInt x
        let y3 := Float.ofInt yv
        for k in [1:33] do
          let s := Float.ofNat k / 32
          let u := 1 - s
          let px := u*u*u*x0 + 3*u*u*s*x1 + 3*u*s*s*x2 + s*s*s*x3
          let py := u*u*u*y0 + 3*u*u*s*y1 + 3*u*s*s*y2 + s*s*s*y3
          edges := edges.push (cx, cy, px, py)
          cx := px
          cy := py
    if opened && (cx != sx || cy != sy) then
      edges := edges.push (cx, cy, sx, sy)
    let mut xs : Array (Float × Int) := #[]
    for (x0, y0, x1, y1) in edges do
      if (y0 ≤ y && y < y1) || (y1 ≤ y && y < y0) then
        xs := xs.push (x0 + (x1 - x0) * (y - y0) / (y1 - y0),
          if y0 < y1 then 1 else -1)
    let sorted := xs.qsort fun a b => a.1 < b.1
    let mut runs : Array (Float × Float) := #[]
    let mut wind : Int := 0
    let mut lo : Float := 0
    for (x, d) in sorted do
      let w := wind + d
      if wind == 0 && w != 0 then
        lo := x
      if wind != 0 && w == 0 then
        runs := runs.push (lo, x)
      wind := w
    return runs
  let shapes : Array (String × Array Ink.Cmd × Int) :=
    #[("floatRect", floatRectCmds, -70), ("tallRect", tallRectCmds, -200),
      ("curvedSpan", curvedSpanCmds, -200), ("dip", dipCmds, -75),
      ("slant", slantCmds, -110)]
  for (name, cmds, minY) in shapes do
    let reported := iv cmds minY
    let mut escaped := false
    for j in [1:10] do
      let y : Float := -100 + 5 * Float.ofNat j
      for (a, b) in oracleRuns cmds y do
        if a + 2 < b - 2 then
          unless reported.any fun (rlo, rhi) =>
              Float.ofInt rlo ≤ a + 2 && b - 2 ≤ Float.ofInt rhi do
            escaped := true
    t s!"ink oracle: no {name} ink in the band escapes the report" (!escaped)
  -- Budget-exceeded outlines are undecodable, never silently truncated: a
  -- glyph declaring more contours or points than the decoder's budget is
  -- `none`, so the consumer clears its whole advance instead of trusting an
  -- incomplete decode. Minimal hand-built sfnts, one glyph each, yMin dipped
  -- below the band so the header shortcut cannot mask the decode.
  let mkSfnt (tables : Array (String × ByteArray)) : ByteArray := Id.run do
    let pushU16 (d : ByteArray) (v : Nat) : ByteArray :=
      (d.push (UInt8.ofNat (v / 256 % 256))).push (UInt8.ofNat (v % 256))
    let pushU32 (d : ByteArray) (v : Nat) : ByteArray :=
      pushU16 (pushU16 d (v / 65536)) (v % 65536)
    let mut d := pushU32 ByteArray.empty 0x00010000
    d := pushU16 d tables.size
    d := pushU16 (pushU16 (pushU16 d 0) 0) 0
    let mut off := 12 + 16 * tables.size
    for (tag, body) in tables do
      d := d ++ tag.toUTF8
      d := pushU32 d 0
      d := pushU32 d off
      d := pushU32 d body.size
      off := off + body.size
    for (_, body) in tables do
      d := d ++ body
    return d
  -- indexToLocFormat 0 at offset 50: short loca.
  let head52 : ByteArray := ⟨Array.replicate 52 (0 : UInt8)⟩
  let srcOf (glyf : Array UInt8) : Ink.Src :=
    let loca : ByteArray := ⟨#[0, 0, UInt8.ofNat (glyf.size / 2 / 256),
      UInt8.ofNat (glyf.size / 2 % 256)]⟩
    Ink.Src.make (mkSfnt #[("head", head52), ("loca", loca), ("glyf", ⟨glyf⟩)])
      false 1
  -- numberOfContours 200 (budget 128); yMin -200.
  let overContours : Array UInt8 :=
    #[0, 200, 0, 0, 0xFF, 0x38] ++ Array.replicate 14 (0 : UInt8)
  t "ink: contour budget exceeded is undecodable"
    ((srcOf overContours).inkAt 0 (-100) (-50) |>.isNone)
  -- one contour whose endPtsOfContours declares 5001 points (budget 4096).
  let overPoints : Array UInt8 :=
    #[0, 1, 0, 0, 0xFF, 0x38, 0, 0, 0, 0, 19, 136] ++ Array.replicate 8 (0 : UInt8)
  t "ink: point budget exceeded is undecodable"
    ((srcOf overPoints).inkAt 0 (-100) (-50) |>.isNone)
  -- A composite whose declared bbox lies: the header says yMin 0, clear of
  -- the band, but its component (glyph 0, a square reaching y −200) spans
  -- it. The declared box is only the glyph's own point bbox for a simple
  -- glyph; a composite's must be decoded, so a yMin shortcut trusting it
  -- would paint a rule through ink.
  let g0 : Array UInt8 :=
    -- one contour, bbox (0,−200)–(100,0), 4 on-curve points
    #[0, 1,  0, 0,  0xFF, 0x38,  0, 100,  0, 0,
      0, 3,  0, 0,
      0x31, 0x33, 0x15, 0x23,
      100, 100, 200,
      0]  -- pad to even length for short loca
  let g1 : Array UInt8 :=
    -- numberOfContours −1; bbox declares yMin 0; one component: glyph 0,
    -- word xy args (0,0), no MORE_COMPONENTS
    #[0xFF, 0xFF,  0, 0,  0, 0,  0, 100,  0, 0,
      0, 3,  0, 0,  0, 0,  0, 0]
  let compSrc : Ink.Src :=
    let glyf := g0 ++ g1
    let loca : ByteArray := ⟨#[0, 0,
      0, UInt8.ofNat (g0.size / 2),
      0, UInt8.ofNat (glyf.size / 2)]⟩
    Ink.Src.make (mkSfnt #[("head", head52), ("loca", loca), ("glyf", ⟨glyf⟩)])
      false 2
  t "ink: composite with a lying bbox is decoded, not trusted"
    (compSrc.inkAt 1 (-100) (-50) == some #[(0, 100)])
  t "ink: the lying composite's simple component answers for itself"
    (compSrc.inkAt 0 (-100) (-50) == some #[(0, 100)])

/-- Native underline: a decoration never breaks a glyph. Drawn from the
font's own `post` metrics and interrupted where a glyph's outline ink
crosses the rule's band, with clearance either side — `q` keeps its rule
under the bowl and clears it at the stem; `text-decoration-skip-ink` is the
browser's spelling of the same invariant. Undecodable outlines clear their
whole advance. Both outline formats are exercised: Open Sans is TrueType
`glyf`, Source Serif Pro is CFF Type 2 charstrings. Own function, same
elaboration-budget reason as the others. -/
def linkSignalChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Colour is never the only signal (WCAG 2.2 SC 1.4.1). A link's
  -- affordance is the underline in both backends -- the HTML anchor keeps
  -- the browser's, and the PDF path draws one: before this, a PDF link had
  -- no visual signal at all, not even colour.
  let out := Layout.run geom oneFace none
    (Elab.run "t" "see \\href{https://example.org/}{the example} here").1
  let segs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  let linkRuns := segs.filterMap fun s => match s with
    | .run _ _ (some _) _ _ _ ul _ => some ul
    | _ => none
  t "pdf link runs exist" (!linkRuns.isEmpty)
  t "pdf link runs are underlined" (linkRuns.all (· == true))
  t "pdf link draws its underline rule" (segs.any fun s => match s with
    | .rule .. => true
    | _ => false)

def underlineChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  -- IR shape
  t "underline ir shape" ((elabStr "\\underline{a}").1.body ==
    #[.para #[.underline #[.text "a"]]])
  t "uline is underline" ((elabStr "\\uline{b}").1.body ==
    #[.para #[.underline #[.text "b"]]])
  -- The font's own glyph outlines decide what interrupts the rule.
  let gidOf (c : Char) : Nat := (font.gid c).getD 0
  let hasInk (c : Char) : Bool := !(font.inkAt (gidOf c)).isEmpty
  t "g has ink in the band" (hasInk 'g')
  t "y has ink in the band" (hasInk 'y')
  t "a has no ink in the band" (!hasInk 'a')
  t "x-height b has no ink in the band" (!hasInk 'b')
  t "comma has ink in the band" (hasInk ',')
  t "parens have ink in the band" (hasInk '(' && hasInk ')')
  -- Ink is an interval, not the whole advance: q's stem crosses the band on
  -- the right of its bowl, so its interval starts past the advance midpoint
  -- and is far narrower than the glyph.
  let qAdv : Int := font.widths[gidOf 'q']?.getD 0
  let qInk := font.inkAt (gidOf 'q')
  t "q ink is a narrow interval, not the advance"
    (qInk.size == 1 && qInk.all fun (lo, hi) =>
      lo > qAdv / 2 && hi - lo < qAdv / 3)
  -- Double-storey g crosses the band twice: the ear side and the tail loop.
  t "g ink is two intervals" ((font.inkAt (gidOf 'g')).size == 2)
  -- ç is a composite (c plus a cedilla component): composites decode
  -- through their components, so the obstruction is the cedilla's narrow
  -- crossing, not a conservative whole advance.
  let cedAdv : Int := font.widths[gidOf 'ç']?.getD 0
  let cedInk := font.inkAt (gidOf 'ç')
  t "composite ç ink is the cedilla, not the advance"
    (cedInk.size == 1 && cedInk.all fun (lo, hi) => lo > 0 && hi < cedAdv)
  -- The lazy per-glyph decode is memoized: Lean's `Thunk` is call-by-need
  -- (`Thunk.get` caches in the runtime object), so a repeated glyph decodes
  -- once however often layout asks. 100k forced reads must land orders of
  -- magnitude under 100k fresh decodes (tens of µs each) — the bound fails
  -- by more than an order of magnitude if each read decoded afresh.
  let t0 ← IO.monoMsNow
  let mut inkReads := 0
  for _ in [0:100000] do
    inkReads := inkReads + (font.inkAt (gidOf 'q')).size
  let inkMs := (← IO.monoMsNow) - t0
  t s!"repeated glyph ink is memoized ({inkMs} ms for {inkReads} reads)"
    (inkReads == 100000 && inkMs < 500)
  -- Layout: rule segs under the underlined run, split around actual ink.
  let outOf (fs : Font.FontSet) (src : String) : Layout.Out :=
    Layout.run geom fs none (Elab.run "t" src).1
  let rulesOf (fs : Font.FontSet) (src : String) : Array (Dim.Sp × Dim.Sp) :=
    ((outOf fs src).pages.flatMap (·.lines)).flatMap (·.segs.filterMap fun s =>
      match s with
      | .rule w th _ _ => some (w, th)
      | _ => none)
  let widthOf (fs : Font.FontSet) (src : String) : Dim.Sp :=
    (((outOf fs src).pages.flatMap (·.lines))[0]?.map (·.setWidth)).getD 0
  let coverage (fs : Font.FontSet) (src : String) : Dim.Sp × Dim.Sp :=
    ((rulesOf fs src).foldl (fun acc (w, _) => acc + w) (0 : Dim.Sp),
     widthOf fs src)
  t "underline emits a rule" ((rulesOf oneFace "\\underline{ab}").size ≥ 1)
  t "plain text emits no rule" ((rulesOf oneFace "ab").isEmpty)
  -- A descender inside the word splits the rule into pieces around its
  -- stroke, so a one-word underline with an interior 'q' carries at least
  -- two, and the pieces cover strictly less than the set width.
  t "underline splits around a descender" ((rulesOf oneFace "\\underline{aqa}").size ≥ 2)
  let (aqaRules, aqaWidth) := coverage oneFace "\\underline{aqa}"
  t "underline leaves a gap at the descender" (0 < aqaRules && aqaRules < aqaWidth)
  -- The load-bearing shape of the invariant: a lone underlined q keeps its
  -- rule under the bowl — most of the advance — rather than losing all of
  -- it, and the gap at the stem is real.
  let (qRules, qWidth) := coverage oneFace "\\underline{q}"
  t "underlined q keeps rule under its bowl" (qRules > qWidth * 2 / 5)
  t "underlined q still clears its stem" (qRules < qWidth)
  -- Adjacent descenders each interrupt only at their own stroke: gy keeps
  -- rule under g's bowl and between the strokes, where the whole-advance
  -- skip left nothing at all.
  let (gyRules, gyWidth) := coverage oneFace "\\underline{gy}"
  t "underline under gy keeps some rule" (0 < gyRules && gyRules < gyWidth)
  -- Punctuation that reaches down interrupts too.
  t "underline splits at a comma" ((rulesOf oneFace "\\underline{a,a}").size ≥ 2)
  -- A longer word with spread descenders: interrupted more than once, most
  -- of the rule intact.
  let (genRules, genWidth) := coverage oneFace "\\underline{genuinely}"
  t "genuinely keeps most of its rule"
    ((rulesOf oneFace "\\underline{genuinely}").size ≥ 3 &&
     genRules > genWidth / 2 && genRules < genWidth)
  -- The rules ride their own line at the text line's baseline, so the PDF
  -- writer's x-tracking stays linear and link rectangles see no extra runs.
  let abLines := ((outOf oneFace "\\underline{ab}").pages.flatMap (·.lines))
  t "underline rules ride a second line at the same y"
    (abLines.size == 2 && abLines[0]!.y == abLines[1]!.y &&
     abLines[1]!.segs.all fun s => match s with
      | .run .. => false
      | _ => true)
  -- The CFF path (Type 2 charstrings) answers the same questions from its
  -- own outlines.
  let serifPath := testFonts ++ "/SourceSerifPro-Regular.otf"
  if ← System.FilePath.pathExists serifPath then
    match Font.parse (← IO.FS.readBinFile serifPath) with
    | .error e => failures ref s!"underline cff parse: {e}"
    | .ok serif =>
      let sgid (c : Char) : Nat := (serif.gid c).getD 0
      let sqAdv : Int := serif.widths[sgid 'q']?.getD 0
      let sqInk := serif.inkAt (sgid 'q')
      t "cff q ink is a narrow interval, not the advance"
        (sqInk.size == 1 && sqInk.all fun (lo, hi) =>
          lo > sqAdv / 2 && hi - lo < sqAdv / 3)
      t "cff g ink is two intervals" ((serif.inkAt (sgid 'g')).size == 2)
      t "cff a has no ink in the band" ((serif.inkAt (sgid 'a')).isEmpty)
      let serifSet : Font.FontSet := {
        fonts := #[serif]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
      }
      let (cqRules, cqWidth) := coverage serifSet "\\underline{q}"
      t "cff underlined q keeps rule under its bowl"
        (cqRules > cqWidth * 2 / 5 && cqRules < cqWidth)
      -- Obstructions live in line coordinates, so ink reaching over a run
      -- boundary clears the neighbouring rule. Both directions: the italic
      -- g's negative left sidebearing reaches back into the upright a's
      -- rule, and an upright g's clearance spills forward past its advance
      -- into the underlined a that follows it.
      let itPath := testFonts ++ "/SourceSerifPro-RegularIt.otf"
      if ← System.FilePath.pathExists itPath then
        match Font.parse (← IO.FS.readBinFile itPath) with
        | .error e => failures ref s!"underline italic parse: {e}"
        | .ok serifIt =>
          let mixedSet : Font.FontSet := {
            fonts := #[serif, serifIt]
            index := ((List.range 3).flatMap fun slot =>
              [((slot, false, false), 0), ((slot, true, false), 0),
               ((slot, false, true), 1), ((slot, true, true), 1)]).toArray
          }
          let firstRunAndRule (src : String) : Dim.Sp × Dim.Sp := Id.run do
            let lines := ((outOf mixedSet src).pages.flatMap (·.lines))
            let runW := ((lines[0]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .run _ _ _ w _ _ _ _ => some w
              | _ => none
            let ruleW := ((lines[1]?.map (·.segs)).getD #[]).filterMap fun s =>
              match s with
              | .rule w _ _ _ => some w
              | _ => none
            return (runW[0]?.getD 0, ruleW[0]?.getD 0)
          let (aW, aRule) := firstRunAndRule "\\underline{a\\textit{g}}"
          t "italic overhang clears the rule across the style boundary"
            (aW > 0 && aRule > 0 && aRule < aW)
          let (gW, gRule) := firstRunAndRule "\\textit{g}\\underline{a}"
          t "a neighbouring run's descender clears the adjacent rule"
            (gW > 0 && gRule > 0 && gRule < (firstRunAndRule "\\textit{a}\\underline{a}").2)
  else
    failures ref s!"underline: {serifPath} missing from the checkout"
  -- Truncated font data: forcing the lazy ink of every descender-ish glyph
  -- on every truncation that still parses must return a verdict, never
  -- panic — and the verdict is conservative: what the intact outline tables
  -- say for that font's own normalized band (a cut can drop `post`, moving
  -- the band to the default) when the outlines survived, the whole advance
  -- when they did not. A rule through ink is never among the outcomes.
  match ← findFont with
  | some fontData =>
    match Font.parse fontData with
    | .error e => failures ref s!"underline: full font parse: {e}"
    | .ok full =>
      let intact := Ink.Src.make fontData full.isCff full.numGlyphs
      let mut checked := 0
      let mut conservative := true
      for k in [0:64] do
        match Font.parse (fontData.extract 0 (fontData.size * k / 64)) with
        | .error _ => pure ()
        | .ok f =>
          let (bpos, bthick) := f.band
          for c in "gqy,()".toList do
            let g := (f.gid c).getD 0
            let whole := #[((0 : Int), (f.widths[g]?.getD 0 : Int))]
            checked := checked + 1
            unless f.inkAt g == whole ||
                some (f.inkAt g) == intact.inkAt g (bpos - bthick) bpos do
              conservative := false
      t s!"truncated ink is the intact intervals or the whole advance ({checked} checked)"
        (checked > 0 && conservative)
  | none => pure ()
  -- Undecodable outline tables are conservative for every glyph: corrupt
  -- the outline table's directory entry (length past the file) and the font
  -- still parses, but 'a' — no descender, not on any character list — now
  -- obstructs its whole advance, because a rule cannot be trusted over ink
  -- the decoder cannot see.
  let corruptTable (tag : String) (d0 : ByteArray) : ByteArray := Id.run do
    let mut d := d0
    let n := Ink.u16 d 4
    for k in [0:n] do
      let entry := 12 + 16 * k
      if entry + 16 ≤ d.size && d.extract entry (entry + 4) == tag.toUTF8 then
        for j in [0:4] do
          d := d.set! (entry + 12 + j) 0xFF
    return d
  match ← findFont with
  | some fontData =>
    match Font.parse (corruptTable "loca" fontData) with
    | .error e => failures ref s!"underline: corrupt loca parse: {e}"
    | .ok f =>
      let g := (f.gid 'a').getD 0
      t "corrupt loca: a obstructs its whole advance"
        (f.inkAt g == #[(0, (f.widths[g]?.getD 0 : Int))])
  | none => pure ()
  if ← System.FilePath.pathExists serifPath then
    match Font.parse (corruptTable "CFF " (← IO.FS.readBinFile serifPath)) with
    | .error e => failures ref s!"underline: corrupt CFF parse: {e}"
    | .ok f =>
      let g := (f.gid 'a').getD 0
      t "corrupt CFF: a obstructs its whole advance"
        (f.inkAt g == #[(0, (f.widths[g]?.getD 0 : Int))])
  -- Underline metrics normalize through one helper shared by ink extraction
  -- and rule placement: a `post` table declaring an implausible position
  -- (above the baseline, or below half the em) or thickness (nonpositive,
  -- or over a quarter em) falls back to the convention, each independently.
  t "band: declared plausible values pass" (Font.underlineBand 2048 (-154) 102 == (-154, 102))
  t "band: zero position falls back" ((Font.underlineBand 1000 0 50).1 == -100)
  t "band: positive position falls back" ((Font.underlineBand 1000 200 50).1 == -100)
  t "band: absurdly deep position falls back" ((Font.underlineBand 1000 (-30000) 50).1 == -100)
  t "band: zero thickness falls back" ((Font.underlineBand 1000 (-50) 0).2 == 50)
  t "band: negative thickness falls back" ((Font.underlineBand 1000 (-50) (-80)).2 == 50)
  t "band: absurdly thick falls back" ((Font.underlineBand 1000 (-50) 900).2 == 50)
  t "band: one bad value keeps the other" (Font.underlineBand 1000 (-50) (-80) == (-50, 50))
  -- End to end: a font whose post table declares a positive position and a
  -- negative thickness still draws a positive-thickness rule below the
  -- baseline.
  match ← findFont with
  | some fontData =>
    let patched := Id.run do
      let mut d := fontData
      match Ink.findTable d "post" with
      | some post =>
        -- underlinePosition at offset 8, underlineThickness at 10: put
        -- +200 and -80 (big-endian FWords).
        d := d.set! (post.offset + 8) 0x00
        d := d.set! (post.offset + 9) 200
        d := d.set! (post.offset + 10) 0xFF
        d := d.set! (post.offset + 11) (0x100 - 80)
        return d
      | none => return d
    match Font.parse patched with
    | .error e => failures ref s!"underline: patched post parse: {e}"
    | .ok bad =>
      t "band: patched font reads the absurd metrics"
        (bad.underlinePosition == 200 && bad.underlineThickness == -80)
      let badSet : Font.FontSet := {
        fonts := #[bad]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
      }
      let badRules := ((outOf badSet "\\underline{ab}").pages.flatMap
        (·.lines)).flatMap (·.segs.filterMap fun s =>
          match s with
          | .rule w th raise _ => some (w, th, raise)
          | _ => none)
      t "band: absurd post metrics still rule below the baseline"
        (badRules.size ≥ 1 && badRules.all fun (w, th, raise) =>
          w > 0 && th > 0 && raise < 0)
  | none => pure ()
  -- HTML: <u> plus the skip-ink stylesheet; links get the same treatment.
  let (uPage, _) := HtmlDoc.emit {} (elabStr "\\underline{x}").1
  t "html underline is u" ((uPage.splitOn "<u>x</u>").length == 2)
  t "html u skips ink"
    ((uPage.splitOn "u { text-decoration: underline; text-decoration-skip-ink: auto;").length == 2)
  t "html links skip ink" ((uPage.splitOn "text-decoration-skip-ink").length ≥ 3)
  -- Compat: soul's \ul and the xparse \varul spelling become the native.
  t "compat ul" ((elabStr "\\ul{x}").1.body == #[.para #[.underline #[.text "x"]]])
  t "compat varul drops its options"
    ((elabStr "\\varul<5>[0.2ex][0.1ex]{x}").1.body ==
      #[.para #[.underline #[.text "x"]]])
  t "compat varul without options"
    ((elabStr "\\varul{x}").1.body == #[.para #[.underline #[.text "x"]]])
  t "compat soul is a note"
    ((elabStr ("\\documentclass{article}\\usepackage{soul}" ++
      "\\begin{document}x\\end{document}")).2.all (·.severity == .note))
  -- A document's own \varul definition loses to the native, with the
  -- existing built-in warning saying so.
  let redef := elabStr ("\\documentclass{article}" ++
    "\\NewDocumentCommand{\\varul}{ O{} m }{#2}" ++
    "\\begin{document}\\varul{y}\\end{document}")
  t "document varul definition is ignored"
    ((redef.2.filter (·.severity == .warning)).any (·.code == "W0303") &&
     redef.1.body == #[.para #[.underline #[.text "y"]]])

/-- The default-family choice and the search roots are what make a fresh
machine work with no configuration, so they are pinned here on synthetic
faces: preference order beats scan order among preferred names; then the
first family calling itself sans; then any face; none only when nothing is
installed. Ties between duplicate installs go to scan order. -/
def defaultFontChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "default prefers listed names over scan order"
    (FontDb.defaultFamily #[synthFace "Arial", synthFace "Helvetica"] == some "Helvetica")
  t "default takes the first preferred name present"
    (FontDb.defaultFamily #[synthFace "Helvetica", synthFace "DejaVu Sans"] ==
      some "DejaVu Sans")
  t "default falls back to the first sans family"
    (FontDb.defaultFamily
      #[synthFace "Example Serif", synthFace "Foo Sans", synthFace "Bar Sans"] ==
      some "Foo Sans")
  t "default falls back to any face"
    (FontDb.defaultFamily #[synthFace "Example Serif"] == some "Example Serif")
  t "default is none only without any face" (FontDb.defaultFamily #[] == none)
  t "resolve breaks duplicate-install ties by scan order"
    ((FontDb.resolve #[synthFace "Tie Sans" "/z/tie.ttf", synthFace "Tie Sans" "/a/tie.ttf"]
      "Tie Sans" {}).map (·.1.path) == some "/z/tie.ttf")
  for d in ["/System/Library/Fonts", "/System/Library/Fonts/Supplemental",
      "/Library/Fonts", "/opt/homebrew/share/fonts", "/usr/local/share/fonts"] do
    t s!"searchDirs covers {d}" (FontDb.searchDirs.contains d)
  if let some home ← IO.getEnv "HOME" then
    t "extraDirs covers ~/Library/Fonts"
      ((← FontDb.extraDirs).contains (home ++ "/Library/Fonts"))
  -- A .ttc never reaches probe via the scan (isFontFile skips it), but probe
  -- fed one directly must classify it as unusable, never abort: its reads
  -- are bounded checks, not trusted offsets.
  let ttc := System.FilePath.mk "/tmp" / "leantex-test-synthetic.ttc"
  IO.FS.writeBinFile ttc ("ttcf".toUTF8 ++ ByteArray.mk (Array.replicate 64 0x7f))
  t "probe rejects a ttc without aborting" ((← FontDb.probe ttc.toString).isNone)
  IO.FS.removeFile ttc

/-- The shipped fonts make the suite hermetic: what `lake test` sees is a
function of the checkout, not of the host. Pinned here: scan order is sorted
path order (so ties resolve the same everywhere), a font file name denotes
its face's family (fontspec's `Path=` idiom), the compat layer carries
`Path=` into `dir` from either side of the name, the default family over the
shipped faces is the sans, and a plain face beats a condensed sibling. -/
def shippedFontChecks (ref : IO.Ref (List String)) (faces : Array FontDb.Face) : IO Unit := do
  let t := check ref
  let paths := faces.map (·.path)
  t "scan order is sorted path order" (paths == paths.qsort (· < ·))
  t "scanning again gives the same faces" ((← FontDb.scanRoots [testFonts]).map (·.path) == paths)
  t "a file name denotes its family"
    (FontDb.familyOf faces "SourceSerifPro-Regular.otf" == "Source Serif Pro")
  t "an unknown file name denotes itself" (FontDb.familyOf faces "Nope.otf" == "Nope.otf")
  t "resolve by file name finds the bold beside it"
    ((FontDb.resolve faces "OpenSans-Regular.ttf" { bold := true }).map (·.1.path) ==
      some (testFonts ++ "/OpenSans-Bold.ttf"))
  t "default over the shipped faces is the first sans in listing order"
    (FontDb.defaultFamily faces == some "Fira Sans")
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  let d1 := (elabStr (pre ++ "\\setmainfont[Path=fonts/]{SourceSerifPro-Regular.otf}" ++ post)).1.fonts
  t "compat Path before the name"
    (d1.dirs == #["fonts/"] && d1.body == some "SourceSerifPro-Regular.otf")
  let d2 := (elabStr (pre ++ "\\setsansfont{Open Sans}[Path = fonts/, BoldFont = OpenSans-Bold.ttf]"
    ++ post)).1.fonts
  t "compat Path after the name" (d2.dirs == #["fonts/"] && d2.sans == some "Open Sans")
  let d3 := (elabStr (pre ++ "\\babelfont{rm}[Path=fonts/]{SourceSerifPro-Regular.otf}" ++ post)).1.fonts
  t "compat babelfont Path" (d3.dirs == #["fonts/"] && d3.body == some "SourceSerifPro-Regular.otf")
  let d5 := (elabStr (pre ++ "\\setmainfont{A.otf}[Path=serif/]\\setsansfont{B.otf}[Path=sans/]" ++ post)).1.fonts
  t "a Path per face keeps every directory" (d5.dirs == #["serif/", "sans/"])
  let d4 := (elabStr (pre ++ "\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }" ++ post)).1.fonts
  t "fonts dir" (d4.dirs == #["fonts"] && d4.body == some "Source Serif Pro")
  t "fonts dir wrong type" (errCodes (pre ++ "\\fonts{ dir = 12 }" ++ post) == ["E0323"])
  let plain : FontDb.Face := {
    path := "/x/a.otf"
    family := "X"
    subfamily := "Bold"
    bold := true
    italic := false
    fixedPitch := false
    weight := 700 }
  let condensed : FontDb.Face := { plain with path := "/x/b.otf", subfamily := "Condensed Bold" }
  t "plain face beats a condensed sibling"
    ((FontDb.resolve #[condensed, plain] "X" { bold := true }).map (·.1.path) == some "/x/a.otf")

/-- Vertical spacing is TeX's, checked on the placed lines. Own function,
same elaboration-budget reason as the others. -/
def spacingChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  let ysOf (g : Layout.Geom) (src : String) : Array Dim.Sp :=
    -- Text lines only: an underline rule rides a sibling line at the same y.
    ((Layout.run g oneFace none (Elab.run "t" src).1).pages.flatMap (·.lines)).filterMap fun l =>
      if l.segs.any (fun s => match s with | .run .. => true | _ => false) then some l.y else none
  let pagesOf (g : Layout.Geom) (src : String) : Nat :=
    (Layout.run g oneFace none (Elab.run "t" src).1).pages.size
  let body := geom.fontSize
  let leading := Layout.leadingFor body geom.leading
  let scaled (sz : Dim.Sp) (units : Int) : Dim.Sp := units * sz / font.unitsPerEm
  -- Interline: body lines sit one leading apart, and a body line after a
  -- Huge one is one body leading below it plus what the Huge line hangs
  -- under its baseline — not a Huge leading.
  let plain := ysOf geom "a\n\nb"
  t "peers sit a leading plus parskip apart"
    (plain.size == 2 && plain[1]! - plain[0]! == leading + (geom.parskip.resolve body 0).width)
  let huge := ysOf geom "{\\Huge Title \\par}\n\nbody"
  let hugeSize := body * 2488 / 1000
  let hugeDepth := scaled hugeSize (-font.descent)
  let bodyHeight := scaled body font.capHeight
  t "a Huge title ends one paragraph, not two lines" (huge.size == 2)
  t "the line after a Huge title is spaced by TeX's rule"
    (huge.size == 2 && huge[1]! - huge[0]! ==
      max leading (hugeDepth + bodyHeight + Dim.pt 1) + (geom.parskip.resolve body 0).width)
  t "the line after a Huge title is not a Huge leading away"
    (huge.size == 2 && huge[1]! - huge[0]! < Layout.leadingFor hugeSize geom.leading)
  t "the first line hangs the title's own height below the margin"
    (huge.size == 2 && huge[0]! == geom.vmargin + max (scaled body font.ascent) (scaled hugeSize font.capHeight))
  -- Gaps: `\vspace` is the gap in place of parskip and adds to other declared
  -- glue; an element's own space (a list's topsep, a heading's before) takes
  -- the larger against what is owed, as LaTeX's `\addvspace` does.
  let vs := ysOf geom "a\n\n\\vspace{20pt}\nb"
  t "a bare vspace replaces parskip" (vs.size == 2 && vs[1]! - vs[0]! == leading + Dim.pt 20)
  let blk := ysOf geom "a\n\n\\block[before = 20pt]{b}"
  t "block before is the gap" (blk.size == 2 && blk[1]! - blk[0]! == leading + Dim.pt 20)
  let listSrc (mid : String) := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\begin{document}a\\begin{itemize}\\item b\\end{itemize}" ++ mid ++ "c\\end{document}"
  let ls := ysOf geom (listSrc "")
  t "list topsep stands above the list" (ls.size == 3 && ls[1]! - ls[0]! == leading + Dim.pt 10)
  t "list topsep stands below the list too" (ls.size == 3 && ls[2]! - ls[1]! == leading + Dim.pt 10)
  let lv := ysOf geom (listSrc "\\vspace{7pt}")
  t "a vspace after a list adds to its topsep"
    (lv.size == 3 && lv[2]! - lv[1]! == leading + Dim.pt 17)
  let secSrc := "\\documentclass{article}\\style{itemize}{ before = 10pt }" ++
    "\\style{section}{ before = 15pt, after = 4pt }" ++
    "\\begin{document}\\begin{itemize}\\item b\\end{itemize}\\section{S}c\\end{document}"
  let sec := ysOf geom secSrc
  t "a heading after a list takes the larger space, not the sum"
    (sec.size == 3 && sec[1]! - sec[0]! ==
      max (Layout.leadingFor (Layout.sectionSize geom 1) geom.leading)
        (scaled body (-font.descent) + scaled (Layout.sectionSize geom 1) font.capHeight + Dim.pt 1)
      + Dim.pt 15)
  -- parskip is a page property with rubber.
  let g0 := ysOf { geom with parskip := { width := Dim.Length.ofSp 0 } } "a\n\nb"
  t "parskip zero sets peers one leading apart" (g0.size == 2 && g0[1]! - g0[0]! == leading)
  let (pDoc, pDs) := elabStr ("\\documentclass{article}\\page{ parskip = 3pt plus 1pt minus 1pt }" ++
    "\\begin{document}x\\end{document}")
  t "page parskip declared" (pDs.isEmpty && pDoc.page.parskip ==
    some { width := Dim.Length.ofSp (Dim.pt 3), stretch := Dim.Length.ofSp (Dim.pt 1),
           shrink := Dim.Length.ofSp (Dim.pt 1) })
  -- A page is set like a line: skips shrink, within their limits, before a
  -- break is taken; beyond them the page breaks.
  let firstY := geom.vmargin + scaled body font.ascent
  let three := "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc"
  let natural := firstY + 2 * (leading + Dim.pt 20) + scaled body (-font.descent)
  let tight : Layout.Geom := { geom with pageH := natural - Dim.pt 10 + geom.vmargin }
  t "within its shrink the page holds" (pagesOf tight three == 1)
  let ys := ysOf tight three
  t "the shrunk page moves later lines up, in proportion"
    (ys.size == 3 && ys[0]! == firstY && ys[2]! < firstY + 2 * (leading + Dim.pt 20) &&
      ys[1]! - ys[0]! == leading + Dim.pt 20 - Dim.pt 5 && ys[2]! - ys[1]! == leading + Dim.pt 20 - Dim.pt 5)
  t "a shrunk page says so"
    ((Layout.run tight oneFace none (Elab.run "t" three).1).diags.any (·.code == "N0200"))
  let tooTight : Layout.Geom := { geom with pageH := natural - Dim.pt 20 + geom.vmargin }
  t "beyond its shrink the page breaks" (pagesOf tooTight three == 2)
  t "an unshrunk page says nothing"
    (!(Layout.run geom oneFace none (Elab.run "t" three).1).diags.any (·.code == "N0200"))

/-- The content stream a strict viewer accepts. Own function, same
elaboration-budget reason as the others. -/
def pdfStreamChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- The pen is moved by `Tm` when a gap is wide; a `TJ` adjustment is
  -- thousandths of the font size and macOS Preview drops an array holding
  -- one past ±32767 — which is how two headings vanished from a resume.
  -- And an array with no glyphs (a rule-only line) is never written.
  let asciiText (pdf : ByteArray) : String :=
    String.fromUTF8! ⟨pdf.data.map fun b => if b < 128 then b else 46⟩
  let tjNumbers (text : String) : List Int × Nat := Id.run do
    let mut nums : List Int := []
    let mut emptyArrays := 0
    for arr in (text.splitOn "] TJ").dropLast do
      let body := (arr.splitOn "[").getLast?.getD ""
      if !body.any (· == '<') then emptyArrays := emptyArrays + 1
      -- Outside <...> strings, the numbers are adjustments.
      let mut inHex := false
      let mut cur := ""
      for c in body.toList ++ [' '] do
        if c == '<' then inHex := true
        else if c == '>' then inHex := false
        else if !inHex then
          if c.isDigit || c == '-' then cur := cur.push c
          else
            if !cur.isEmpty then
              if let some n := cur.toInt? then nums := n :: nums
              cur := ""
    return (nums, emptyArrays)
  let wide : Layout.Geom := { pageW := Dim.pt 1200, hmargin := Dim.pt 20 }
  let (gapDoc, _) := Elab.run "t" "a\\hfill b\n\n\\underline{x}"
  let gapText := asciiText (Pdf.write wide oneFace (Layout.run wide oneFace none gapDoc).pages)
  let (adjs, empties) := tjNumbers gapText
  t "pdf never writes a TJ adjustment past sixteen bits"
    (adjs.all fun n => n.natAbs ≤ 32767)
  t "pdf writes no glyphless TJ array" (empties == 0)
  -- Three pen placements: the first line, `b` across the fill, the second
  -- line; the underline's rule-only sibling line places nothing.
  t "pdf moves the pen across a wide gap with Tm" ((gapText.splitOn " Tm\n").length == 4)

/-- Dimension evidence beyond the fixed vectors in `main`.

Cross-unit tests: every unit the table relates must parse to the same sp
(the theorem `Decl.unitScale_consistent` pins the table's fractions; these
pin the string-level wiring, including signs and `sp` itself).

Round-trip property test (generator: xorshift64*, 2000 values uniform in
±2³¹ sp): `toPtString` rounds to the nearest thousandth of a pt, so parsing
the printed value back must land within 33 sp (32.768 sp of print rounding
plus under 1 sp of parse truncation) and must never change unit kind. -/
def dimChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "dim 1pc is 12pt" (Decl.parseValue "1pc" == Decl.parseValue "12pt")
  t "dim 6pc is 1in" (Decl.parseValue "6pc" == Decl.parseValue "1in")
  t "dim 72bp is 1in" (Decl.parseValue "72bp" == Decl.parseValue "1in")
  t "dim 65536sp is 1pt" (Decl.parseValue "65536sp" == Decl.parseValue "1pt")
  t "dim 10mm is 1cm" (Decl.parseValue "10mm" == Decl.parseValue "1cm")
  t "dim negative is exact" (Decl.parseValue "-0.5in" == some (.dim (-(Dim.inch 1) / 2)))
  t "dim negative em is exact"
    (Decl.parseLength "-0.25em" == some { em := -250 })

  -- toPtString: exact thirds round to the nearest thousandth, tiny values
  -- collapse to "0" without a stray sign, halves round away from zero.
  t "sp pt string thirds" ((Dim.pt 1 / 3).toPtString == "0.333")
  t "sp pt string negative thirds" ((-(Dim.pt 1) / 3).toPtString == "-0.333")
  t "sp pt string eighth" (((8192 : Dim.Sp)).toPtString == "0.125")
  t "sp pt string tiny is unsigned zero" (((-26 : Dim.Sp)).toPtString == "0")
  t "sp pt string half milli rounds up" (((4096 : Dim.Sp)).toPtString == "0.063")

  let mut s : UInt64 := 0xA0761D6478BD642F
  let mut worst : Nat := 0
  let mut failed : Option String := none
  for _ in [0:2000] do
    let (mag, s') := rand s (2 ^ 32)
    s := s'
    let x : Dim.Sp := (mag : Int) - 2 ^ 31
    match Decl.parseLength (x.toPtString ++ "pt") with
    | some l =>
      let err := (l.sp - x).natAbs
      worst := max worst err
      unless l.em == 0 && l.ex == 0 && err ≤ 33 do
        failed := some s!"dim round-trip: {x} printed {x.toPtString}, reparsed {l.sp} (err {err})"
    | none => failed := some s!"dim round-trip: {x} printed {x.toPtString}, which did not parse"
  if let some msg := failed then failures ref msg
  t "dim round-trip error reaches the print rounding bound" (worst > 20)

/-- Faces and sizes have to survive into the content stream, and only the
bytes can say so: a regression once embedded one face where six belonged
while every other test still passed. Its own function: `main`'s do block
has no elaboration budget left. -/
def pdfFaceChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) (font : Font.Font) : IO Unit := do
  let t := check ref
  let twoFace : Font.FontSet := {
    fonts := #[font, font]
    index := ((List.range 3).flatMap fun slot =>
      let idx := if slot == 1 then 1 else 0
      [((slot, false, false), idx), ((slot, true, false), idx),
       ((slot, false, true), idx), ((slot, true, true), idx)]).toArray
  }
  let (bigDoc, bigDs) := Elab.run "t"
    "plain {\\sffamily other face} and {\\Huge big} and {\\small little}"
  t "size scale source clean" bigDs.isEmpty
  let bigPdf := Pdf.write geom twoFace (Layout.run geom twoFace none bigDoc).pages
  t "pdf references a second face" (bytesContain bigPdf "/F2 ")
  t "pdf sets Huge at 2.488x" (bytesContain bigPdf "24.88 Tf")
  t "pdf sets small at 0.9x" (bytesContain bigPdf "9 Tf")
  t "pdf keeps the body size" (bytesContain bigPdf "10 Tf")
  -- One face only: nothing unused is embedded, so no /F2 exists.
  let plainPdf := Pdf.write geom oneFace (Layout.run geom oneFace none bigDoc).pages
  t "pdf embeds no unused face" (!bytesContain plainPdf "/F2 ")
  -- The descriptor states the parsed metrics (ISO 32000-2 §9.8.1:
  -- CapHeight is the cap height), never a stand-in: the fixture face
  -- declares a cap height under its ascent, so the old CapHeight := ascent
  -- is distinguishable and must stay dead.
  let cap1000 := font.capHeight * 1000 / (font.unitsPerEm : Int)
  let asc1000 := font.ascent * 1000 / (font.unitsPerEm : Int)
  t "pdf descriptor CapHeight is the face's own, not the ascent"
    (cap1000 != asc1000 && bytesContain plainPdf s!"/CapHeight {cap1000}" &&
     !bytesContain plainPdf s!"/CapHeight {asc1000}")
  pdfStreamChecks ref oneFace

/-- Differential fuzz of the UTF-8 validator against the core decoder
(generator: xorshift64*, 400 byte strings — half raw random bytes of length
0–15, half a valid encoded string with one byte overwritten): `validate`
must accept exactly what `String.fromUTF8?` decodes. The fixed vectors in
`main` pin the error kinds and offsets; this pins the accept/reject boundary
where no fixed vector was written. -/
def utf8FuzzChecks (ref : IO.Ref (List String)) : IO Unit := do
  let samples : Array String :=
    #["hello", "naïve", "αβγδε", "🎉🌍", "a\nb\nc", "τεχ — done", "𝔸𝔹ℂ"]
  let mut s : UInt64 := 0xE7037ED1A0B428DB
  let mut failed : Option String := none
  for i in [0:400] do
    let (mode, s') := rand s 2
    s := s'
    let mut v : ByteArray := ByteArray.empty
    if mode == 0 then
      let (len, s') := rand s 16
      s := s'
      for _ in [0:len] do
        let (b, s') := rand s 256
        s := s'
        v := v.push (UInt8.ofNat b)
    else
      let (which, s') := rand s samples.size
      s := s'
      v := samples[which]!.toUTF8
      let (at_, s') := rand s v.size
      s := s'
      let (b, s'') := rand s' 256
      s := s''
      v := v.set! at_ (UInt8.ofNat b)
    unless (validate v == none) == (String.fromUTF8? v).isSome do
      failed := some s!"utf8 fuzz case {i}: validate and core decoder disagree on {v.toList}"
  if let some msg := failed then failures ref msg

def rawPayloadChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Browsers match end tags ASCII-case-insensitively, so the terminator guard
  -- must too; the lowercase spelling is pinned beside the printers' tests,
  -- these pin the case variants in both printers.
  t "html style payload cannot close its own tag in upper case"
    (((Html.render (Html.Node.style "x</STYLE>bad") 0).splitOn "</STYLE").length == 1)
  t "html style payload cannot close its own tag in mixed case inline"
    (((Html.render (Html.elem "p" #[Html.Node.style "x</Style>bad"]) 0).splitOn
      "</Style").length == 1)
  t "html script payload cannot close its own tag in upper case inline"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</SCRIPT>bad"]) 0).splitOn
      "</SCRIPT").length == 1)
  -- The terminator literal omits the closing `>`, which is what catches a
  -- spaced or self-closed end tag; pinned so the case fix cannot regress it.
  t "html script payload with a spaced terminator is removed"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</script >bad"]) 0).splitOn
      "/* removed */").length == 2)

/-- The pre-commit gate's own predicates, exercised through the script's
`--selftest` mode: a gate that does not catch the shape it commemorates
grants false confidence. -/
def precommitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let out ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/precommit.lean", "--selftest"] }
  check ref s!"precommit selftest:\n{out.stderr}" (out.exitCode == 0)
  let owed ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/owed.lean", "--selftest"] }
  check ref s!"owed selftest:\n{owed.stderr}" (owed.exitCode == 0)

/-- `columns`/`column`: side-by-side blocks with declared widths, in the IR
and both backends. Own function: `main`'s do block has no budget left. -/
def columnsChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n\\begin{frame}\n" ++
    body ++ "\n\\end{frame}\n\\end{document}"
  let src := deck ("\\begin{columns}[T]\n\\begin{column}{0.6\\textwidth}\nleft\n\\end{column}\n" ++
    "\\begin{column}{0.4\\textwidth}\nright\n\\end{column}\n\\end{columns}")
  let (doc, ds) := elabStr src
  t "columns elaborate with widths, its option a note" (ds.all (·.severity == .note) &&
    doc.body == #[.frame #[] false .center #[.columns #[
      (some 600, #[.para #[.text "left"]]),
      (some 400, #[.para #[.text "right"]])]]])
  -- PDF: the columns' first lines share a baseline, and the second sits
  -- past the first one's measure — visibly two columns, by geometry.
  let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
  t "pdf columns share a baseline side by side"
    (match (out.pages[0]?.map (·.lines)).getD #[] with
     | #[l, r] => l.y == r.y && r.x > l.x && r.x ≥ l.x + l.setWidth
     | _ => false)
  -- A column keeps its measure: its paragraph breaks at the column width,
  -- not the text width.
  let wide := deck ("\\begin{columns}\\begin{column}{0.5\\textwidth}\n" ++
    "several words that cannot possibly fit one half measure line\n" ++
    "\\end{column}\\begin{column}{0.5\\textwidth}\nright\n\\end{column}\\end{columns}")
  let (wDoc, _) := elabStr wide
  let wOut := Layout.run (Layout.Geom.ofPage wDoc.page) oneFace none wDoc
  t "a column breaks lines at its own measure"
    (((wOut.pages[0]?.map (·.lines)).getD #[]).size > 2)
  -- HTML: a grid whose tracks carry the declared widths.
  let (html, _) := HtmlDoc.emit {} doc
  t "html columns are a grid with the declared widths"
    ((html.splitOn "grid-template-columns: 60% 40%").length == 2)
  -- An unreadable width warns and shares the leftover instead.
  let (aDoc, aDs) := elabStr (deck ("\\begin{columns}\\begin{column}{3cm}\na\n\\end{column}" ++
    "\\begin{column}{0.5\\textwidth}\nb\n\\end{column}\\end{columns}"))
  t "an absolute column width warns and degrades to a share"
    (aDs.any (·.code == "W0314") &&
     (match aDoc.body with
      | #[.frame _ _ _ #[.columns cols]] => cols.map (·.1) == #[none, some 500]
      | _ => false))

/-- Overlays, dim-not-hide (PLAN M5): steps ride the IR, the PDF handout
gets one page per step with pending content dimmed and no reflow, HTML
carries the step data with everything visible (the no-JS deliverable).
Own function: `main`'s do block has no budget left. -/
def overlayChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n\\begin{frame}\n" ++
    body ++ "\n\\end{frame}\n\\end{document}"
  -- \item<n-> wraps its item; \uncover<n>{...} wraps inline content.
  let src := deck ("\\begin{itemize}\n\\item<1-> first\n\\item<2-> second\n\\end{itemize}\n" ++
    "\\uncover<2>{tail}")
  let (doc, ds) := elabStr src
  t "overlay specs elaborate to steps, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center #[
      .list false #[
        #[.step 1 none #[.para #[.text "first"]]],
        #[.step 2 none #[.para #[.text "second"]]]],
      .para #[.step 2 (some 2) #[.text "tail"]]]])
  -- \pause steps the rest of the scope.
  let (pDoc, pDs) := elabStr (deck "one\n\n\\pause\ntwo\n\n\\pause\nthree")
  t "pause steps the rest, cumulatively" (pDs.isEmpty &&
    pDoc.body == #[.frame #[] false .center #[
      .para #[.text "one"],
      .step 2 none #[.para #[.text "two"], .step 3 none #[.para #[.text "three"]]]]])
  -- PDF: one page per step; pending content dims, nothing moves.
  let out := Layout.run (Layout.Geom.ofPage pDoc.page) oneFace none pDoc
  t "pdf emits one page per step" (out.pages.size == 3)
  let coords (p : Layout.PageOut) : Array (Dim.Sp × Dim.Sp) :=
    p.lines.map fun l => (l.x, l.y)
  t "pdf steps do not reflow"
    (match out.pages[0]?, out.pages[2]? with
     | some p1, some p3 => coords p1 == (coords p3).extract 0 (coords p1).size
     | _, _ => false)
  let lineColors (p : Layout.PageOut) : Array Ir.Color :=
    p.lines.filterMap fun l => l.segs.findSome? fun s => match s with
      | .run _ c _ _ _ _ _ _ => some c
      | _ => none
  t "pdf pending content is dimmed, then undimmed"
    (match out.pages[0]?, out.pages[2]? with
     | some p1, some p3 =>
       let c1 := lineColors p1
       let c3 := lineColors p3
       c1.size == 3 && c3.size == 3 &&
       c1[0]? == some Ir.Color.black && c1[1]? != some Ir.Color.black &&
       c1[2]? != some Ir.Color.black && c3.all (· == Ir.Color.black)
     | _, _ => false)
  -- HTML: the steps ride as data, everything visible.
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries step data"
    ((html.splitOn "data-step=\"2\"").length ≥ 2)
  -- A spec the model cannot number keeps the honest warning.
  t "an unnumberable spec still warns W0105"
    (warnCodes (deck "\\begin{itemize}\\item<+-> x\\end{itemize}") == ["W0105"])
  -- The range's end is modelled: <2> covers on 1 AND again from 3, exactly
  -- as beamer's transparent covering does; <2-3> reads the same way.
  t "a range spec carries its end"
    ((elabStr (deck "\\uncover<2-3>{ranged}")).1.body ==
      #[.frame #[] false .center #[.para #[.step 2 (some 3) #[.text "ranged"]]]])
  let (rDoc, rDs) := elabStr (deck ("\\begin{itemize}\n\\item<1> opening\n" ++
    "\\item<2-> second\n\\item<3-> third\n\\end{itemize}"))
  let rOut := Layout.run (Layout.Geom.ofPage rDoc.page) oneFace none rDoc
  t "content past its range end dims again" (rDs.isEmpty &&
    rOut.pages.size == 3 &&
    (match rOut.pages[0]?, rOut.pages[2]? with
     | some p1, some p3 =>
       let colorOf (p : Layout.PageOut) (k : Nat) : Option Ir.Color :=
         p.lines[k]?.bind fun l => l.segs.findSome? fun s => match s with
           | .run _ c _ _ _ _ _ _ => some c
           | _ => none
       -- Page 1: the <1> item crisp, the rest dimmed. Page 3: the <1> item
       -- dimmed again — its range ended — and the rest crisp.
       colorOf p1 0 == some Ir.Color.black && colorOf p1 1 != some Ir.Color.black &&
       colorOf p3 0 != some Ir.Color.black && colorOf p3 1 == some Ir.Color.black &&
       colorOf p3 2 == some Ir.Color.black
     | _, _ => false))
  -- Covered means covered: a pending step's own colours (an alert, a
  -- palette name) are repainted by the shade — beamer's transparent
  -- covering mutes coloured text too — and pending code dims like any
  -- other text.
  let runColors (p : Layout.PageOut) : Array Ir.Color :=
    p.lines.flatMap fun l => l.segs.filterMap fun s => match s with
      | .run _ c _ _ _ _ _ _ => some c
      | _ => none
  let colorSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ hot = #AA0000 }\n\\begin{document}\n\\begin{frame}\n" ++
    "opening\n\n\\pause\n\\hot{closing beat}\n\\end{frame}\n\\end{document}"
  let (cDoc, cDs) := elabStr colorSrc
  let cOut := Layout.run (Layout.Geom.ofPage cDoc.page) oneFace none cDoc
  let hotCover := (Ir.Design.ofDoc cDoc).cover.of { r := 0xAA, g := 0, b := 0 }
  t "a pending step's explicit colours are covered as themselves, quieter"
    (cDs.isEmpty && cOut.pages.size == 2 &&
     (match cOut.pages[0]?, cOut.pages[1]? with
      | some p1, some p2 =>
        !(runColors p1).contains { r := 0xAA, g := 0, b := 0 } &&
        -- the covered run is the ink's own cover, not the plain grey
        (runColors p1).contains hotCover &&
        hotCover != (Ir.Design.ofDoc cDoc).cover.plain &&
        (runColors p2).contains { r := 0xAA, g := 0, b := 0 }
      | _, _ => false))
  let (vDoc, vDs) := elabStr
    (deck "opening\n\n\\pause\n\\begin{verbatim}\ncode line\n\\end{verbatim}")
  let vOut := Layout.run (Layout.Geom.ofPage vDoc.page) oneFace none vDoc
  t "pending verbatim dims like any other text"
    (vDs.isEmpty && vOut.pages.size == 2 &&
     (match vOut.pages[0]?, vOut.pages[1]? with
      | some p1, some p2 =>
        (runColors p1).size ≥ 2 &&
        (runColors p1).count Ir.Color.black == 1 &&
        (runColors p2).all (· == Ir.Color.black)
      | _, _ => false))

/-- Block content inside overlay commands, the block/inline agreement, and
`\pause` where a deck actually puts it. Own function: `main`'s do block has
no budget left. -/
def overlayBlockChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n\\begin{frame}\n" ++
    body ++ "\n\\end{frame}\n\\end{document}"
  -- A list inside an overlay group: the step wrapper survives at block
  -- level (this was E0312).
  let (lDoc, lDs) := elabStr (deck
    "\\onslide<2->{\n\\begin{itemize}\n\\item Stepped item.\n\\end{itemize}\n}")
  t "a list inside an overlay group steps whole, erroring nothing"
    (lDs.isEmpty && lDoc.body == #[.frame #[] false .center #[
      .step 2 none #[.list false #[#[.para #[.text "Stepped item."]]]]]])
  -- A multi-paragraph group: every paragraph stays inside the step (the
  -- par splice used to strip all but the first).
  let (mDoc, mDs) := elabStr (deck "\\uncover<2>{\nFirst covered.\n\nSecond covered.\n}")
  t "every paragraph of an overlay group stays inside its step"
    (mDs.isEmpty && mDoc.body == #[.frame #[] false .center #[
      .step 2 (some 2) #[.para #[.text "First covered."],
        .para #[.text "Second covered."]]]])
  -- Block and inline agree: the same spec around the same words reaches the
  -- same step, whether the content is a paragraph or a list item.
  let (iDoc, _) := elabStr (deck "\\uncover<2->{same words}")
  let (bDoc, _) := elabStr (deck
    "\\uncover<2->{\n\\begin{itemize}\n\\item same words\n\\end{itemize}\n}")
  t "block and inline agree on steps"
    (match iDoc.body, bDoc.body with
     | #[.frame _ _ _ ib], #[.frame _ _ _ bb] =>
       Ir.maxStepBlocks ib == 2 && Ir.maxStepBlocks bb == 2
     | _, _ => false)
  -- The open form between blocks: the rest of the scope steps (it used to
  -- produce an empty step and leave the content unstepped).
  let (oDoc, oDs) := elabStr (deck "shown\n\n\\onslide<2->\nlater one\n\nlater two")
  t "bare onslide between blocks steps the rest of the scope"
    (oDs.isEmpty && oDoc.body == #[.frame #[] false .center #[
      .para #[.text "shown"],
      .step 2 none #[.para #[.text "later one"], .para #[.text "later two"]]]])
  -- \pause between items steps the rest of the list, not nothing.
  let (pDoc, pDs) := elabStr (deck
    "\\begin{itemize}\n\\item first\n\\pause\n\\item second\n\\pause\n\\item third\n\\end{itemize}")
  t "pause between items steps the later items"
    (pDs.isEmpty && pDoc.body == #[.frame #[] false .center #[
      .list false #[
        #[.para #[.text "first"]],
        #[.step 2 none #[.para #[.text "second"]]],
        #[.step 3 none #[.para #[.text "third"]]]]]])
  let pOut := Layout.run (Layout.Geom.ofPage pDoc.page) oneFace none pDoc
  t "a paused list gets one handout page per step" (pOut.pages.size == 3)
  -- \pause inside a column steps the column's remaining blocks.
  let (cDoc, cDs) := elabStr (deck
    ("\\begin{columns}\n\\begin{column}{0.5\\textwidth}\nabove\n\n\\pause\nbelow\n" ++
     "\\end{column}\n\\begin{column}{0.5\\textwidth}\nsteady\n\\end{column}\n\\end{columns}"))
  t "pause inside a column steps the column's rest"
    (cDs.isEmpty && (match cDoc.body with
      | #[.frame _ _ _ #[.columns cols]] =>
        (match cols[0]? with
         | some (_, body) => body == #[.para #[.text "above"],
             .step 2 none #[.para #[.text "below"]]]
         | none => false) &&
        (match cols[1]? with
         | some (_, body) => body == #[.para #[.text "steady"]]
         | none => false)
      | _ => false))
  -- \alt: both alternatives are on the page — the active one crisp within
  -- its spec, the other before it.
  let (aDoc, aDs) := elabStr (deck "\\alt<2>{after}{before}")
  t "alt inline yields the step and its complement"
    (aDs.isEmpty && aDoc.body == #[.frame #[] false .center #[.para #[
      .step 2 (some 2) #[.text "after"],
      .step 1 (some 1) #[.text "before"]]]])
  let (abDoc, abDs) := elabStr (deck
    "\\alt<2->{\nAfter one.\n\nAfter two.\n}{\nBefore.\n}")
  t "alt with block alternatives steps both at block level"
    (abDs.isEmpty && abDoc.body == #[.frame #[] false .center #[
      .step 2 none #[.para #[.text "After one."], .para #[.text "After two."]],
      .step 1 (some 1) #[.para #[.text "Before."]]]])
  -- A spec the model cannot number keeps W0105 and shows the block content.
  let (uDoc, uDs) := elabStr (deck
    "\\onslide<+->{\n\\begin{itemize}\n\\item shown anyway\n\\end{itemize}\n}")
  t "an unnumberable spec on a block group warns and shows the content"
    ((uDs.map (·.code)) == #["W0105"] && uDoc.body == #[.frame #[] false .center #[
      .list false #[#[.para #[.text "shown anyway"]]]]])

/-- Speaker notes: a side channel — never slide content, omitted from the
PDF handout, an inert hidden aside in HTML for the coming speaker view.
Own function: `main`'s do block has no budget left. -/
def noteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n\\begin{frame}\n" ++
    body ++ "\n\\end{frame}\n\\end{document}"
  let (doc, ds) := elabStr (deck "Visible words.\n\\note{Hidden speaker words.}")
  t "note elaborates to a side channel, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false .center #[
      .para #[.text "Visible words."],
      .note #[.para #[.text "Hidden speaker words."]]]])
  -- PDF: the note adds nothing — the page is the page without it.
  let (bare, _) := elabStr (deck "Visible words.")
  let noted := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
  let plain := Layout.run (Layout.Geom.ofPage bare.page) oneFace none bare
  t "pdf omits the note entirely"
    (noted.pages.map (·.lines.size) == plain.pages.map (·.lines.size))
  -- HTML: an inert hidden aside, available to a speaker view.
  let (html, _) := HtmlDoc.emit {} doc
  t "html carries the note as a hidden aside"
    ((html.splitOn "<aside class=\"note\" hidden=").length == 2 &&
     (html.splitOn "Hidden speaker words.").length == 2)
  -- The generic body-preservation path must never leak a note into
  -- content: inside an argument it vanishes too.
  let (inl, inlDs) := elabStr (deck "\\textbf{bold \\note{never shown} text}")
  t "a mid-sentence note leaves its paragraph whole and drains to the frame"
    (inlDs.isEmpty &&
     (match inl.body with
      | #[.frame _ _ _ #[.para content, .note nbody]] =>
        Ir.plainText content == "bold text" &&
        ((Ir.dumpBlocks "" nbody).splitOn "never shown").length == 2
      | _ => false))

  -- A note body is absorbed, as beamer absorbs it: a reserved character
  -- there (a bare code-ish underscore is the common case) stays literal
  -- and must not fail the build.
  let (resv, resvDs) := elabStr (deck "Shown.\n\\note{name_with_underscores & more}")
  t "reserved characters in a note stay literal, erroring nothing"
    (resvDs.isEmpty &&
     (match resv.body with
      | #[.frame _ _ _ #[_, .note nbody]] =>
        ((Ir.dumpBlocks "" nbody).splitOn "name_with_underscores & more").length == 2
      | _ => false))

/-- The theme × frame-furniture reconciliation invariants: standout and
overlay steps are orthogonal (the flag rides onto every step page), the
furniture belongs to the frame rather than the step (a stepped frame's
pages share one progress position), and a note stays silent through the
themed paths too. -/
def themeReconcileChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let themed (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ fg = #23373B, bg = #FFFFFF, alert = #EB811B,\n" ++
    "  progressfg = alert, standoutfg = bg, standoutbg = fg }\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- A standout frame carrying steps: one page per step, every page still
  -- inverted, its text still in standoutfg.
  let (soDoc, soDs) := elabStr (themed
    ("\\begin{frame}[standout]\nOne.\n\n\\pause\nTwo.\n\\end{frame}"))
  t "stepped standout source clean" soDs.isEmpty
  let geom := Layout.Geom.ofPage soDoc.page
  let so := Layout.run geom oneFace none soDoc
  t "a stepped standout frame gets one page per step" (so.pages.size == 2)
  let fg : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg : Ir.Color := { r := 0xFF, g := 0xFF, b := 0xFF }
  t "every step page of a standout frame stays inverted"
    (so.pages.all fun p => p.fills.any fun f =>
      f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH && f.color == fg)
  t "standout text keeps standoutfg on every step page"
    (so.pages.all fun p => p.lines.any fun l => l.segs.any fun s => match s with
      | .run _ c _ _ _ _ _ _ => c == bg
      | _ => false)
  -- The furniture is the frame's, not the step's: three step pages advance
  -- the deck position by ONE frame, so the section page after them shows
  -- 1 of 2 elapsed — not 3 of 2.
  let (pDoc, pDs) := elabStr (themed
    ("\\begin{frame}{Steps}\na\n\n\\pause\nb\n\n\\pause\nc\n\\end{frame}\n" ++
     "\\section{Mid}\n\\begin{frame}{After}\nd\n\\end{frame}"))
  t "stepped deck source clean" pDs.isEmpty
  let pOut := Layout.run (Layout.Geom.ofPage pDoc.page) oneFace none pDoc
  t "step pages plus divider plus frame" (pOut.pages.size == 5)
  let alert : Ir.Color := { r := 0xEB, g := 0x81, b := 0x1B }
  let mp : Dim.Sp := (Layout.Geom.ofPage pDoc.page).textWidth * 7875 / 10000
  t "the progress position belongs to the frame, not the step"
    (match pOut.pages[3]? with
     | some p => p.fills.any fun f => f.w == mp / 2 && f.color == alert
     | none => false)
  -- A note through the themed standout path: the page is the page
  -- without it.
  let (nDoc, _) := elabStr (themed
    "\\begin{frame}[standout]\nShown.\n\\note{never printed}\n\\end{frame}")
  let (bDoc, _) := elabStr (themed "\\begin{frame}[standout]\nShown.\n\\end{frame}")
  let nOut := Layout.run (Layout.Geom.ofPage nDoc.page) oneFace none nDoc
  let bOut := Layout.run (Layout.Geom.ofPage bDoc.page) oneFace none bDoc
  t "a themed standout frame does not print its speaker note"
    (nOut.pages.map (·.lines.size) == bOut.pages.map (·.lines.size))

/-- `\chrome` and the bundles' chrome: page furniture as declared data, a
slot naming a per-page datum, redeclaration replacing — a theme's chrome is
a default exactly as its palette is. -/
def chromeDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let frame := "\\begin{frame}{T}\nx\n\\end{frame}"
  let (mDoc, mDs) := elabStr (deck "\\theme{moloch}" frame)
  t "chrome moloch source clean" mDs.isEmpty
  t "moloch declares the footer slots"
    (mDoc.chrome.footerLeft == some .sectionTitle &&
     mDoc.chrome.footerRight == some .frameNumber)
  t "moloch declares the muted step"
    (mDoc.palette.find? "muted" == some { r := 0x64, g := 0x72, b := 0x74 })
  t "plain declares the same footer"
    ((elabStr (deck "\\theme{plain}" frame)).1.chrome.hasFooter)
  t "an unthemed deck has no chrome"
    (!(elabStr (deck "" frame)).1.chrome.hasFooter)
  -- A later \chrome replaces the theme's whole footer, as \palette entries
  -- replace: the theme is a default, never a lock.
  let (oDoc, oDs) := elabStr (deck
    "\\theme{moloch}\\chrome{ footer = { right = \\slidenumber } }" frame)
  t "a document's chrome overrides the theme's whole footer" (oDs.isEmpty &&
    oDoc.chrome.footerLeft.isNone && oDoc.chrome.footerRight == some .frameNumber)
  -- The sketch's spelling and the beamer lineage's name one datum.
  t "slidenumber and framenumber are one datum"
    ((elabStr (deck "\\chrome{ footer = { right = \\framenumber } }" frame)).1.chrome ==
     (elabStr (deck "\\chrome{ footer = { right = \\slidenumber } }" frame)).1.chrome)
  t "unknown chrome key names the known one"
    ((elabStr (deck "\\chrome{ logo = x }" frame)).2.any fun d =>
      d.code == "E0322" && ((d.help.getD "").splitOn "footer").length == 2)
  t "unknown slot key names left and right"
    ((elabStr (deck "\\chrome{ footer = { top = \\framenumber } }" frame)).2.any
      (·.code == "E0322"))
  t "an unreadable slot names the data"
    ((elabStr (deck "\\chrome{ footer = { left = \\pagenumber } }" frame)).2.any fun d =>
      d.code == "E0321" && ((d.help.getD "").splitOn "sectiontitle").length == 2)
  t "a non-block footer is a type error"
    ((elabStr (deck "\\chrome{ footer = 3pt }" frame)).2.any (·.code == "E0323"))
  t "chrome outside slides warns"
    ((elabStr ("\\documentclass{article}\\chrome{ footer = { right = \\framenumber } }" ++
      "\\begin{document}x\\end{document}")).2.any (·.code == "W0318"))
  -- FINDINGS F4: the frame and physical sequences share a band only by
  -- declaration. A theme-installed frame slot plus \framefoot{\pagenumber}
  -- is undeclared mixing (W0332); the document naming its own \chrome slots
  -- IS the declaration, so the same band is then silent.
  let mixedBody := "\\framefoot{p. \\pagenumber}\n\\begin{frame}{T}\nx\n\\end{frame}"
  t "undeclared sequence mixing warns by name"
    ((elabStr (deck "\\theme{moloch}" mixedBody)).2.any fun d =>
      d.code == "W0332" && d.severity == .warning)
  t "a document that declares its chrome has declared the mixing"
    (!(elabStr (deck "\\theme{moloch}\\chrome{ footer = { right = \\framenumber } }"
      mixedBody)).2.any (·.code == "W0332"))
  t "no frame slot, no mixing"
    (!(elabStr (deck "" mixedBody)).2.any (·.code == "W0332"))
  t "a physical-free framefoot mixes nothing"
    (!(elabStr (deck "\\theme{moloch}"
      "\\framefoot{note}\n\\begin{frame}{T}\nx\n\\end{frame}")).2.any
      (·.code == "W0332"))
  -- The sequences cannot quietly fuse: the physical pass leaves a rendered
  -- frame slot untouched on every page (`substPage_leaves_frame_slot` is
  -- the theorem; this pins one instance executably).
  t "substPage leaves a rendered frame slot alone"
    (Layout.substPage 7 9 (Ir.ChromeSlot.frameFraction.render #[] 2 5) ==
      Ir.ChromeSlot.frameFraction.render #[] 2 5)
  -- The muted rule is load-bearing: one step weaker (fg!60!bg) fails the
  -- bundle contract the theorems hold.
  let weaker : Ir.Palette := { entries :=
    Theme.moloch.palette.entries.map fun (k, c) =>
      if k == "muted" then (k, { r := 121, g := 133, b := 135 }) else (k, c) }
  t "the palette contract rejects a muted one step weaker"
    (!Contrast.paletteContract weaker)

/-- The footer band is reserved, never overlaid: `Geom.bodyBottom` is the one
place a footer's band comes out of the page, placement reads the bottom only
from there, and `bodyBottom_clears_footer` is the arithmetic that the
reservation suffices. This pins layout to actually reading it, on a page
whose margin is too small to hold the foot line. -/
def footerBandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let para := String.intercalate " " (List.replicate 300 "filler words run on")
  let src := "\\page{ vmargin = 2pt }\n\\runningfoot{quiet foot}\n" ++
    "\\begin{document}\n" ++ para ++ "\n\n" ++ para ++ "\n\\end{document}"
  let (doc, ds) := elabStr src
  t "band source clean" (ds.filter (·.severity == .error)).isEmpty
  let geom0 := Layout.Geom.ofPage doc.page
  let out := Layout.run geom0 oneFace none doc
  let font := oneFace.body
  let ascent : Dim.Sp := font.ascent * geom0.fontSize / (font.unitsPerEm : Int)
  let descent : Dim.Sp := (-font.descent) * geom0.fontSize / (font.unitsPerEm : Int)
  let geom := { geom0 with footBand := Layout.footBandFor geom0.vmargin ascent }
  t "a 6pt margin cannot hold the foot line, so the band bites"
    (geom.footBand > (0 : Dim.Sp))
  let footY := geom.pageH - geom.vmargin / 2
  t "the foot line is laid on every page"
    (!out.pages.isEmpty && out.pages.all fun p => p.lines.any (·.y == footY))
  t "body ink stops above the reserved band"
    (out.pages.all fun p => p.lines.all fun l =>
      l.y == footY || l.y + descent ≤ geom.bodyBottom)
  -- The check is load-bearing: without the reservation, this document's
  -- last body line reaches into the footer's band.
  let (bare, _) := elabStr ("\\page{ vmargin = 2pt }\n\\begin{document}\n" ++
    para ++ "\n\n" ++ para ++ "\n\\end{document}")
  let bareOut := Layout.run (Layout.Geom.ofPage bare.page) oneFace none bare
  t "the fixture reaches the band it is about"
    (bareOut.pages.any fun p => p.lines.any fun l => l.y + descent > geom.bodyBottom)

/-- The chrome footer through layout and the HTML backend: frame pages carry
the section in force and their frame's own number, furniture pages carry
none, a stepped frame's pages share one number, `\runningfoot` overrides the
whole footer, and an unthemed deck is untouched. -/
def chromeFooterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let body :=
    "\\begin{frame}{One}\na\n\\end{frame}\n" ++
    "\\section{Topic}\n" ++
    "\\begin{frame}{Two}\nb\n\n\\pause\nc\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nQ\n\\end{frame}"
  let (doc, ds) := elabStr (deck "\\theme{moloch}" body)
  t "chrome deck source clean" ds.isEmpty
  let geom0 := Layout.Geom.ofPage doc.page
  let out := Layout.run geom0 oneFace none doc
  t "chrome deck five pages" (out.pages.size == 5)
  t "frame pages carry a footer, furniture pages none"
    (out.pages.map (·.foot.isSome) == #[true, false, true, true, false])
  t "the footer shows the frame's own number"
    ((out.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "1")
  t "the footer shows the section in force beside the number"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic2")
  t "a stepped frame's pages share one footer"
    (out.pages[2]?.bind (·.foot) == out.pages[3]?.bind (·.foot))
  let font := oneFace.body
  let footSize := geom0.fontSize * ((Ir.sizeScale.lookup "small").getD 1000) / 1000
  let footAscent : Dim.Sp := font.ascent * footSize / (font.unitsPerEm : Int)
  let descent : Dim.Sp := (-font.descent) * geom0.fontSize / (font.unitsPerEm : Int)
  let footY := geom0.pageH - geom0.vmargin / 2
  t "the foot line lands in the margin at the small step, in muted"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.y == footY && l.size == footSize &&
         l.segs.any fun s => match s with
           | .run _ c _ _ _ _ _ _ => c == ({ r := 0x64, g := 0x72, b := 0x74 } : Ir.Color)
           | _ => false
     | none => false)
  -- Invariant (a) of the footer: body ink never reaches the footer's ink,
  -- on a frame whose body demonstrably fills the page.
  let para := String.intercalate " " (List.replicate 120 "filler words run on")
  let (tallDoc, _) := elabStr (deck "\\theme{moloch}"
    ("\\begin{frame}{Tall}\n" ++ para ++ "\n\n" ++ para ++ "\n\\end{frame}"))
  let tallOut := Layout.run geom0 oneFace none tallDoc
  t "a tall frame spills and every spill page keeps its footer"
    (tallOut.pages.size > 1 && tallOut.pages.all (·.foot.isSome))
  t "body ink never reaches the footer ink"
    (tallOut.pages.all fun p => p.lines.all fun l =>
      l.y == footY || l.y + descent ≤ footY - footAscent - Layout.lineskip)
  t "the tall frame demonstrably fills the body area"
    (tallOut.pages.any fun p => p.lines.any fun l =>
      l.y != footY && l.y + descent + Layout.leadingFor geom0.fontSize >
        (Layout.Geom.ofPage tallDoc.page).bodyBottom)
  -- \runningfoot is the author's whole footer: chrome yields entirely.
  let (rDoc, _) := elabStr (deck "\\theme{moloch}\\runningfoot{own foot}" body)
  let rOut := Layout.run (Layout.Geom.ofPage rDoc.page) oneFace none rDoc
  t "runningfoot suppresses the chrome footer"
    (rOut.pages.all (·.foot.isNone))
  t "runningfoot itself is laid on every page"
    (rOut.pages.all fun p => p.lines.any (·.y == footY))
  -- No theme, no footer: the unthemed deck's output is untouched.
  let (uDoc, _) := elabStr (deck "" body)
  let uOut := Layout.run (Layout.Geom.ofPage uDoc.page) oneFace none uDoc
  t "an unthemed deck carries no footer at all"
    (uOut.pages.all fun p => p.foot.isNone && p.lines.all (·.y != footY))
  -- The HTML backend reads the same declarations: each non-standout frame
  -- section closes with the footer, styled by the muted token and the
  -- shared size scale.
  let (html, _) := HtmlDoc.emit {} doc
  t "html frames close with the footer, standout none"
    ((html.splitOn "class=\"slide-foot size-small\"").length == 3)
  t "html footer carries the frame number"
    ((html.splitOn ">2</span>").length == 2)
  t "html footer styling comes from the tokens"
    ((html.splitOn "section.slide > footer.slide-foot").length == 2 &&
     (((html.splitOn "footer.slide-foot {")[1]?.getD "").splitOn
       "var(--muted)").length == 2)
  let (rHtml, _) := HtmlDoc.emit {} rDoc
  t "html drops the chrome footer under runningfoot too"
    ((rHtml.splitOn "slide-foot").length == 1)
  -- \chrome without a theme: the declaration alone is enough.
  let (cDoc, cDs) := elabStr (deck "\\chrome{ footer = { right = \\framenumber } }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  let cOut := Layout.run (Layout.Geom.ofPage cDoc.page) oneFace none cDoc
  t "a bare chrome declaration draws its footer" (cDs.isEmpty &&
    ((cOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "1"))

/-- One numbering, every consumer: the numbering audit's constructed
disagreements, pinned. The title page bears no footer and no number and the
first content frame is 1 (moloch: `\maketitle` is
`\frame[plain,noframenumbering]{\titlepage}`); the section-page progress
reads the same numbering, 0/N before any content frame; a stepped frame's
pages share one number and a `\framefoot` note sits beside it; the chrome
frame number and the physical `\pagenumber`/`\pagecount` stay two declared
sequences; and the PDF footer text is the HTML footer text, frame for
frame — both read `Ir.frameNumbers` and neither counts. -/
def numberingChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- The HTML tree pretty-prints, so tags and indentation are stripped and
  -- the comparison is over the footer's own characters.
  let strip (s : String) : String := Id.run do
    let mut out := ""
    let mut inTag := false
    for c in s.toList do
      if c == '<' then inTag := true
      else if c == '>' then inTag := false
      else if !inTag && !c.isWhitespace then out := out.push c
    return out
  let htmlFoots (html : String) : List String :=
    ((html.splitOn "class=\"slide-foot size-small\">").drop 1).map fun s =>
      strip ((s.splitOn "</footer>")[0]?.getD "")
  -- Consecutive pages sharing one footer are one frame (steps, spills):
  -- the frame-level sequence both backends must agree on.
  let pdfFoots (out : Layout.Out) : List String :=
    (out.pages.foldl (fun (acc : List String) p =>
      match p.foot with
      | some f =>
        let s := strip (Ir.plainText (Ir.bandInlines f))
        if acc.head? == some s then acc else s :: acc
      | none => acc) []).reverse
  -- The headline disagreement: the title page carried footer "1" and the
  -- first content frame showed "2"; the progress fraction counted both.
  let (doc, ds) := elabStr (deck "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n\\begin{frame}{One}\na\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "numbering deck source clean" ds.isEmpty
  t "the numbering skips title and standout and reaches its count"
    (doc.frameCount == 1 && doc.frameNumbers.toList.filterMap id == [1])
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom oneFace none doc
  t "numbering deck four pages" (out.pages.size == 4)
  t "the title page and the standout carry no footer, the content frame does"
    (out.pages.map (·.foot.isSome) == #[false, false, true, false])
  t "the content frame is frame 1, not 2"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "S1")
  t "the progress bar shows 0 of 1 before any content frame"
    (match out.pages[1]? with
     | some p => (p.fills.any fun f => f.color == ({ r := 0xCB, g := 0xC0, b := 0xB6 } : Ir.Color)) &&
         !(p.fills.any fun f => f.color == ({ r := 0xA5, g := 0x5A, b := 0x13 } : Ir.Color))
     | none => false)
  let (html, _) := HtmlDoc.emit {} doc
  t "html gives the title and standout frames no footer"
    ((html.splitOn "class=\"slide-foot size-small\"").length == 2)
  t "html numbers the content frame 1"
    ((html.splitOn ">1</span>").length == 2)
  t "html progress is 0% before any content frame"
    ((html.splitOn "width: 0%").length == 2)
  t "pdf and html footers are the same text" (pdfFoots out == htmlFoots html)
  -- Steps, a \framefoot note, and the two-sequences deck: the note takes
  -- the left slot beside the frame's number, a stepped frame's pages share
  -- one number, and the backends agree frame for frame.
  let (dDoc, dDs) := elabStr (deck "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n" ++
     "\\begin{frame}{A}\na\n\n\\pause\nb\n\\end{frame}\n" ++
     "\\section{S}\n\\framefoot{note}\n" ++
     "\\begin{frame}{B}\nc\n\\end{frame}\n" ++
     "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "two-sequences deck source clean" dDs.isEmpty
  t "two content frames count 1 and 2"
    (dDoc.frameCount == 2 && dDoc.frameNumbers.toList.filterMap id == [1, 2])
  let dOut := Layout.run (Layout.Geom.ofPage dDoc.page) oneFace none dDoc
  t "two-sequences deck six pages" (dOut.pages.size == 6)
  t "a stepped frame's pages share one footer"
    (dOut.pages[1]?.bind (·.foot) == dOut.pages[2]?.bind (·.foot))
  t "the framefoot note sits beside the frame's own number"
    ((dOut.pages[4]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "note2")
  let (dHtml, _) := HtmlDoc.emit {} dDoc
  t "pdf and html footers agree across steps and notes"
    (pdfFoots dOut == htmlFoots dHtml && htmlFoots dHtml == ["1", "note2"])
  -- \pagenumber/\pagecount stay the physical sequence: a \runningfoot deck
  -- numbers its pages 1..pages.size (title page included), while the frame
  -- count is its own declared sequence — two models, both stated.
  let (rDoc, rDs) := elabStr (deck
    ("\\theme{moloch}\\title{T}\\author{A}" ++
     "\\runningfoot{page \\pagenumber\\ of \\pagecount}")
    ("\\maketitle\n\\begin{frame}{One}\na\n\\end{frame}"))
  t "physical deck source clean" rDs.isEmpty
  let rOut := Layout.run (Layout.Geom.ofPage rDoc.page) oneFace none rDoc
  t "runningfoot suppresses chrome and the physical count is the page count"
    (rOut.pages.size == 2 && rOut.pages.all (·.foot.isNone) && rDoc.frameCount == 1)
  t "the physical sequence substitutes per page"
    (Ir.plainText (Layout.substPage 2 2 (rDoc.foot.getD #[])) == "page 2 of 2")
  -- The clamps are gone because they cannot fire: the position is a some
  -- of the numbering, ≤ the count by theorem. The bar fills exactly at the
  -- end, and a deck with no countable frame draws no bar at all.
  let (fDoc, _) := elabStr (deck "\\theme{moloch}\\title{T}\\author{A}"
    ("\\begin{frame}{One}\na\n\\end{frame}\n\\section{End}"))
  let fGeom := Layout.Geom.ofPage fDoc.page
  let fOut := Layout.run fGeom oneFace none fDoc
  let mp : Dim.Sp := fGeom.textWidth * 7875 / 10000
  t "a section after every frame fills the bar exactly"
    (fOut.pages.any fun p => p.fills.any fun f =>
      f.w == mp && f.color == ({ r := 0xA5, g := 0x5A, b := 0x13 } : Ir.Color))
  let (zDoc, zDs) := elabStr (deck "\\theme{moloch}\\title{T}\\author{A}"
    ("\\maketitle\n\\section{S}\n\\begin{frame}[standout]\nQ\n\\end{frame}"))
  t "zero-count deck source clean" zDs.isEmpty
  t "a deck with no countable frame draws no progress bar"
    (zDoc.frameCount == 0 &&
     (Layout.run (Layout.Geom.ofPage zDoc.page) oneFace none zDoc).pages.all fun p =>
       !(p.fills.any fun f => f.color == ({ r := 0xCB, g := 0xC0, b := 0xB6 } : Ir.Color)))
  t "html draws no progress bar with no countable frame"
    (((HtmlDoc.emit {} zDoc).1.splitOn "class=\"progress\"").length == 1)
  -- The fraction slot: moloch's numbering=fraction, reachable as
  -- \framefraction, rendered by the one Ir.ChromeSlot.render site on both
  -- backends — the denominator is the same frameCount everywhere.
  let (cDoc, cDs) := elabStr (deck
    "\\chrome{ footer = { right = \\framefraction } }"
    ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}"))
  t "framefraction parses to its slot" (cDs.isEmpty &&
    cDoc.chrome.footerRight == some .frameFraction)
  let cOut := Layout.run (Layout.Geom.ofPage cDoc.page) oneFace none cDoc
  t "the fraction footer reads n / N"
    (cOut.pages.map (fun p => (p.foot.map (fun f => Ir.plainText (Ir.bandInlines f))).getD "") ==
      #["1 / 2", "2 / 2"])
  let (cHtml, _) := HtmlDoc.emit {} cDoc
  t "pdf and html agree on the fraction form"
    (pdfFoots cOut == htmlFoots cHtml && htmlFoots cHtml == ["1/2", "2/2"])
  -- The physical gate does not silence frame furniture: \runninghead's
  -- [from = 2] keeps the head off the opening page (the physical model),
  -- while the opening frame's own chrome footer — the frame model — stays.
  let (gDoc, gDs) := elabStr (deck
    "\\theme{moloch}\\runninghead[from = 2]{An Invented Head}"
    ("\\begin{frame}{A}\na\n\\end{frame}\n\\begin{frame}{B}\nb\n\\end{frame}"))
  t "gated deck source clean" gDs.isEmpty
  let gGeom := Layout.Geom.ofPage gDoc.page
  let gOut := Layout.run gGeom oneFace none gDoc
  let gFont := oneFace.body
  let headY := gGeom.vmargin / 2 + gFont.ascent * gGeom.fontSize / (gFont.unitsPerEm : Int)
  let footY := gGeom.pageH - gGeom.vmargin / 2
  t "runningFrom keeps the head off page 1 and on page 2"
    ((gOut.pages.map fun p => p.lines.any (·.y == headY)) == #[false, true])
  t "runningFrom does not gate the frame's chrome footer"
    (gOut.pages.all fun p => p.lines.any (·.y == footY))
  -- A running line that wraps is a named diagnostic, never a silent
  -- truncation to its first line.
  let longFoot := String.intercalate " " (List.replicate 40 "an overlong footer")
  let (wDoc, _) := elabStr (deck s!"\\runningfoot\{{longFoot}}"
    "\\begin{frame}{A}\na\n\\end{frame}")
  let wOut := Layout.run (Layout.Geom.ofPage wDoc.page) oneFace none wDoc
  t "a wrapping running line warns by name"
    (wOut.diags.any (·.code == "W0328"))
  t "a one-line running line does not warn"
    (!rOut.diags.any (·.code == "W0328"))

/-- The deck's own footer route: `\setbeamertemplate{frame footer}` — alone
or expanded from a `\newenvironment` wrapper — reaches the chrome footer's
left slot as `\framefoot`, instead of dying with W0104. The note holds for
the frames that follow, an empty one clears back to the default, and the
frame number keeps its slot throughout. -/
def frameFootChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  -- The wrapper exactly as a beamer deck defines it, through compat.
  let wrapper := "\\newenvironment{framefooter}[1]" ++
    "{\\setbeamertemplate{frame footer}{#1}}{\\setbeamertemplate{frame footer}{}}"
  let body :=
    "\\section{Topic}\n" ++
    "\\begin{frame}{One}\na\n\\end{frame}\n" ++
    "\\begin{framefooter}{origin: example.org}\n" ++
    "\\begin{frame}{Two}\nb\n\\end{frame}\n" ++
    "\\end{framefooter}\n" ++
    "\\begin{frame}{Three}\nc\n\\end{frame}"
  let (doc, ds) := elabStr (deck ("\\theme{moloch}" ++ wrapper) body)
  t "framefooter deck raises no W0104" (!ds.any (·.code == "W0104"))
  t "framefooter deck source clean" (ds.filter (·.severity == .error)).isEmpty
  let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
  -- pages: section page, One, Two, Three
  t "framefooter deck four pages" (out.pages.size == 4)
  t "before the wrapper the default footer stands"
    ((out.pages[1]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic1")
  t "the wrapped frame carries the note beside its number"
    ((out.pages[2]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "origin: example.org2")
  t "the wrapper's end clears back to the default"
    ((out.pages[3]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "Topic3")
  -- The bare template call, no wrapper, no theme: the note alone is a
  -- footer — an unthemed deck's framefooter is not silently dropped.
  let (bDoc, bDs) := elabStr (deck ""
    ("\\setbeamertemplate{frame footer}{quiet note}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a bare frame footer template is clean" (!bDs.any (·.code == "W0104"))
  let bOut := Layout.run (Layout.Geom.ofPage bDoc.page) oneFace none bDoc
  t "the unthemed note still lands"
    ((bOut.pages[0]?.bind (·.foot)).map (fun f => Ir.plainText (Ir.bandInlines f)) == some "quiet note")
  -- Other templates drop their body; a body carrying content is a dropped
  -- loss (footline carries the frame number), named with the native spelling.
  let (_, fDs) := elabStr (deck ""
    ("\\setbeamertemplate{footline}{\\insertframenumber}\n" ++
     "\\begin{frame}{T}\nx\n\\end{frame}"))
  t "a content-carrying template drops as an error naming framefoot"
    (fDs.any fun d => d.code == "E0111" && d.severity == .error &&
      ((d.help.getD "").splitOn "framefoot").length == 2)
  -- The HTML backend reads the same override.
  let (html, _) := HtmlDoc.emit {} doc
  t "html wrapped frame carries the note"
    ((html.splitOn "origin: example.org").length == 2)
  t "html unwrapped frames keep the section title"
    ((html.splitOn ">Topic</span>").length == 3)

/-- The themed slides furniture, keyed on the semantic palette entries: page
background and text colour, the frame-title bar, the section page with its
progress bar. No theme machinery here — the keys are the API, so a theme
stays a table of values. -/
def themeFurnitureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{ fg = #23373B, bg = black!2, alert = #EB811B,\n" ++
    "  frametitlefg = bg, frametitlebg = fg,\n" ++
    "  progressfg = alert, progressbg = progressfg!50!black!30 }\n" ++
    "\\tokens{ progressheight = 2pt }\n" ++
    "\\begin{document}\n" ++
    "\\begin{frame}{First}\nalpha\n\\end{frame}\n" ++
    "\\section{Middle}\n" ++
    "\\begin{frame}{Second}\nbeta\n\\end{frame}\n" ++
    "\\end{document}"
  let (doc, ds) := elabStr src
  t "furniture source clean" ds.isEmpty
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom oneFace none doc
  t "furniture three pages: frame, divider, frame" (out.pages.size == 3)
  let bg : Ir.Color := { r := 0xFA, g := 0xFA, b := 0xFA }
  let fg : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  t "every page carries the background"
    (out.pages.all fun p => p.fills.any fun f =>
      f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH && f.color == bg)
  t "frame title is a colour bar"
    (match out.pages[0]? with
     | some p => p.fills.any fun f =>
        f.color == fg && f.w == geom.pageW && f.y == 0 && f.h < geom.pageH / 3
     | none => false)
  t "frame title text takes frametitlefg"
    (match out.pages[0]?.bind (·.lines[0]?) with
     | some l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ _ => c == bg
        | _ => false
     | none => false)
  t "body text takes fg"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ _ => c == fg
        | _ => false
     | none => false)
  let mp : Dim.Sp := geom.textWidth * 7875 / 10000
  let alert : Ir.Color := { r := 0xEB, g := 0x81, b := 0x1B }
  t "section page draws the progress track in the mixed colour"
    (match out.pages[1]? with
     | some p => p.fills.any fun f =>
        f.w == mp && f.h == Dim.pt 2 &&
        f.color == ((alert.mix 50 Ir.Color.black).mix 30 Ir.Color.white)
     | none => false)
  t "the elapsed share is the deck position (1 of 2 frames)"
    (match out.pages[1]? with
     | some p => p.fills.any fun f => f.w == mp / 2 && f.h == Dim.pt 2 && f.color == alert
     | none => false)
  t "section page centres vertically"
    (match out.pages[1]?.bind (·.lines[0]?), out.pages[0]?.bind (·.lines[0]?) with
     | some sl, some fl => sl.y > fl.y + geom.pageH / 4
     | _, _ => false)
  let (html, _) := HtmlDoc.emit {} doc
  t "html body takes bg and fg"
    ((html.splitOn "body { background: var(--bg); }").length == 2 &&
     (html.splitOn "body { color: var(--fg); }").length == 2)
  t "html frame header is a bar"
    ((html.splitOn "section.slide > header { background: var(--frametitlebg);").length == 2)
  t "html section page carries its position"
    ((html.splitOn "class=\"section-page\"").length == 2 &&
     (html.splitOn "width: 50%").length == 2)
  -- Unthemed output is untouched: no keys, no fills, black text.
  let (plainDoc, _) := elabStr ("\\documentclass[aspectratio=169]{slides}\n" ++
    "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")
  let plainOut := Layout.run (Layout.Geom.ofPage plainDoc.page) oneFace none plainDoc
  t "unthemed pages carry no fills" (plainOut.pages.all (·.fills.isEmpty))

/-- Recovery emits the author's content, never the source's syntax. An
unknown command's leading `[...]` run is how the author addressed the
command — a parameter, not content — so no character of it reaches the
shipped page, while every `{...}` group survives, and no space the author
never wrote is fabricated after the kept text. Judged over `Layout.Out`'s
glyphs, never the IR dump: a bracketed number once shipped in front of a
URL while the suite was green. This invariant is a test, not a theorem:
it ranges over `elabInlines`, whose recursion the checker cannot yet see
(one of the three sanctioned exceptions), so no proof can unfold it. -/
def recoveryChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let pageText (src : String) : String :=
    let (d, _) := elabStr src
    let lines := (Layout.run geom oneFace none d).pages.flatMap (·.lines)
    String.join (lines.toList.map fun l =>
      String.ofList (l.segs.toList.flatMap fun s =>
        match s with
        | .run _ _ _ _ glyphs _ _ _ => (glyphs.map (·.2)).toList
        | .gap _ => [' ']
        | _ => []))
  let has (page part : String) : Bool := (page.splitOn part).length > 1
  -- The user's own case: a bracketed number in front of a URL, and one in
  -- front of an email address.
  let url := pageText "\\textls[16]{placeholder}.example.org"
  t "an unknown command's option run ships no character"
    (!has url "[" && !has url "]" && !has url "16")
  t "the kept group stays fused to what follows it"
    (has url "placeholder.example.org")
  let mail := pageText "\\textls[16]{someone}@example.org"
  t "an option run before an email address ships nothing"
    (!has mail "[" && has mail "someone@example.org")
  t "the drop is visible, named by its own code"
    ((warnCodes "\\textls[16]{placeholder}.example.org").contains "W0341")
  -- Consecutive runs are one parameter train; both groups are content.
  let par := pageText "\\parbox[c][2cm]{alpha}{beta}"
  t "consecutive option runs all go with the command"
    (!has par "[" && !has par "2cm" && has par "alpha beta")
  -- An unclosed run is malformed content, not an option: kept and named.
  let open_ := pageText "\\foo[16 oops"
  t "an unclosed bracket run stays on the page"
    (has open_ "[16 oops" &&
     (warnCodes "\\foo[16 oops").contains "W0310" &&
     !(warnCodes "\\foo[16 oops").contains "W0341")
  -- A bracket on a later line is content, where LaTeX stops looking too.
  let later := pageText "\\foo\n[note] stays"
  t "a bracket run on the next line is content"
    (has later "[note] stays" && !(warnCodes "\\foo\n[note] stays").contains "W0341")
  -- No fabricated space: the give-back happens only when one was written.
  t "no space is fabricated after a kept group"
    (pageText "\\foo{a}.b" == "a.b")
  t "a written space after a kept group survives"
    (pageText "\\foo{a} b" == "a b")
  -- The starred form's `*` still belongs to the command, options after it.
  t "a starred unknown command drops its options too"
    (let s := pageText "\\foo*[1]{x}"; s == "x")

/-- Vertical distribution: beamer's frame options select the split, the
default centres (beamer user guide §8.1), and a titled frame's page-top
chrome never moves with the body. -/
def vdistChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++ body ++
    "\n\\end{document}"
  let linesOf (src : String) : Array Layout.LineOut :=
    (Layout.run geom oneFace none (elabStr src).1).pages.flatMap (·.lines)
  let firstY (body : String) : Dim.Sp :=
    ((linesOf (deck body))[0]?.map (·.y)).getD 0
  let yT := firstY "\\begin{frame}[t]\nhello\n\\end{frame}"
  let yC := firstY "\\begin{frame}\nhello\n\\end{frame}"
  let yB := firstY "\\begin{frame}[b]\nhello\n\\end{frame}"
  t "a frame centres by default, [t] sits above it" (yT < yC)
  t "[b] sits below the centre" (yC < yB)
  -- 1:1 is the halving and 1:0 the whole leftover: centre is halfway
  -- between top and bottom, up to the division's rounding.
  t "centre is halfway between [t] and [b]"
    (yB - yC == yC - yT || yB - yC == yC - yT + 1)
  -- Ratio 0:1 reproduces the undistributed placement exactly
  -- (VDist.top_is_flush at page level): a [t] frame's first line sits
  -- where an article's does.
  t "[t] is the old top-flush placement"
    (yT == firstY "hello")
  t "[t] parses to top"
    ((elabStr (deck "\\begin{frame}[t]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .top #[.para #[.text "x"]]])
  t "[b] parses to bottom"
    ((elabStr (deck "\\begin{frame}[b]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] false .bottom #[.para #[.text "x"]]])
  t "[t,standout] keeps both"
    ((elabStr (deck "\\begin{frame}[t,standout]\nx\n\\end{frame}")).1.body ==
      #[.frame #[] true .top #[.para #[.text "x"]]])
  -- A titled frame's title is page-top chrome: distributing the body must
  -- not move the title line, and the title bar keeps its height.
  let titled (opt : String) : String :=
    deck ("\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}")
  let tLines := linesOf (titled "[t]")
  let cLines := linesOf (titled "")
  t "a titled frame has title and body lines" (tLines.size ≥ 2 && cLines.size ≥ 2)
  t "the title never moves with the distribution"
    (((tLines[0]?).map (·.y)) == ((cLines[0]?).map (·.y)))
  t "the body distributes below the title"
    ((((tLines[1]?).map (·.y)).getD 0) < (((cLines[1]?).map (·.y)).getD 0))
  -- With a frametitlebg palette the title is a colour bar; centring the
  -- body must not stretch it.
  let barH (opt : String) : Dim.Sp :=
    let src := "\\documentclass[aspectratio=169]{slides}\n" ++
      "\\palette{frametitlebg = #23373B}\n\\begin{document}\n" ++
      "\\begin{frame}" ++ opt ++ "{Head}\nbody text\n\\end{frame}\n\\end{document}"
    (((Layout.run geom oneFace none (elabStr src).1).pages.flatMap
      (·.fills))[0]?.map (·.h)).getD 0
  t "the title bar keeps its height under centring" (barH "" == barH "[t]")
  -- The title frame: golden distribution, and the titlepage style decides
  -- the horizontal alignment and the separator.
  let titled := deck "\\title{A Deck}\\author{Pat Placeholder}\n\\maketitle"
  t "the title frame declares the golden split"
    (match (elabStr titled).1.body with
     | #[.frame _ _ .golden _] => true
     | _ => false)
  t "an undeclared title page centres"
    (match (elabStr titled).1.body with
     | #[.frame _ _ _ #[.center _]] => true
     | _ => false)
  let styledSrc := "\\documentclass[aspectratio=169]{slides}\n" ++
    "\\palette{sep = #445566}\n" ++
    "\\style{titlepage}{align = left, separator = sep}\n" ++
    "\\begin{document}\n\\title{A Deck}\\author{Pat Placeholder}\n\\maketitle\n" ++
    "\\end{document}"
  t "a left title page is ragged and carries the separator"
    (match (elabStr styledSrc).1.body with
     | #[.frame _ _ .golden inner] =>
       inner.size ≥ 2 && inner.any (fun b => match b with
         | .rule _ (some "sep") _ => true
         | _ => false) && !inner.any (fun b => match b with
         | .center _ => true
         | _ => false)
     | _ => false)
  -- The separator lays out as a full-measure rule line.
  t "the separator sets as a full-measure rule"
    ((linesOf styledSrc).any fun l => l.segs.any fun sg =>
      match sg with
      | .rule w _ _ _ => w == geom.textWidth
      | _ => false)

/-- The running head's reserved band (`headBandFor`/`Geom.bodyTop`): with a
top margin too small to hold the head line, body ink still starts at least
`lineskip` below the head's ink bottom — `bodyTop_clears_head` is the
sufficiency proof; this is its witness over the shipped lines, the
invariant whose absence let the head collide with the first body line. The
mirrored default is also pinned: at the default margins the band is zero,
so an undeclared page is unchanged. -/
def headBandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let tight := "\\documentclass{article}\\page{ vmargin = 14pt }" ++
    "\\runninghead{Invented Notes \\hfill p. \\pagenumber}" ++
    "\\begin{document}Body text under a tight margin.\\end{document}"
  let (doc, _) := elabStr tight
  let geom := Layout.Geom.ofPage doc.page
  let out := Layout.run geom oneFace none doc
  let lines := (out.pages[0]?.map (·.lines)).getD #[]
  let font := oneFace.body
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let headY := geom.vmargin / 2 + scale font.ascent
  t "the tight-margin page ships its head line" (lines.any fun l => l.y == headY)
  let headBottom := headY + scale (-font.descent)
  let bodyInkTops := lines.filterMap fun l =>
    if l.y == headY then none else some (l.y - scale font.capHeight)
  t "body ink clears the head's ink by lineskip under a tight margin"
    (!bodyInkTops.isEmpty &&
      bodyInkTops.all fun top => headBottom + Layout.lineskip ≤ top)
  -- The default margin holds the head whole: the band is zero and the
  -- first body line sits exactly where a headless page puts it.
  let dflt (head : Bool) : Option Dim.Sp := Id.run do
    let src := "\\documentclass{article}" ++
      (if head then "\\runninghead{Invented Notes}" else "") ++
      "\\begin{document}Body text at the default margin.\\end{document}"
    let (doc, _) := elabStr src
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom oneFace none doc
    let lines := (out.pages[0]?.map (·.lines)).getD #[]
    return (lines.filter fun l => l.y ≠ geom.vmargin / 2 + scale font.ascent)
      |>.foldl (fun acc l => match acc with
        | none => some l.y
        | some y => some (min y l.y)) none
  t "the default margin reserves no band: the body does not move"
    (dflt true == dflt false && (dflt false).isSome)
  -- `slides_lines_survive_bands` allows each running line two em of ink;
  -- the shipped test faces sit inside that bound, so the theorem's
  -- hypothesis is real, not aspirational.
  for name in ["OpenSans-Regular.ttf", "SourceSerifPro-Regular.otf",
               "SourceCodePro-Regular.otf"] do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f =>
      t s!"{name} line ink stays under two em"
        (f.ascent + (-f.descent) ≤ 2 * (f.unitsPerEm : Int))
    | .error e => failures ref s!"headBand font parse {name}: {e}"

/-- The IR-to-IR walks are exhaustive, and each arm below was a wildcard
drop once: the fact checked is the behaviour the walk owes the constructor
it used to drop silently (PLAN 2026-09-17, the obligation table). -/
def walkChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- A font template's hole may sit inside any body-carrying wrapper: a
  -- link or step wrapper is filled exactly like styled/colored/underline.
  t "fillTemplate fills a hole inside a link"
    (Ir.fillTemplate #[.link "https://example.org" #[]] #[.text "x"] ==
      #[.link "https://example.org" #[.text "x"]])
  t "fillTemplate fills a hole inside a step"
    (Ir.fillTemplate #[.step 2 none #[]] #[.text "x"] == #[.step 2 none #[.text "x"]])
  -- Furniture sits outside the overlay model: the dim walks keep a section
  -- title whole, so a step there must not multiply handout pages either.
  -- A deliberate answer, pinned; the wildcard used to decide it silently.
  t "maxStep keeps furniture outside the overlay model"
    (Ir.maxStepBlocks #[.section 1 false #[.step 2 none #[.text "t"]]] == 1)

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
  /-- The line's set width, so a fact can judge its right edge — where a
  footer's right slot must sit whatever the left slot holds. -/
  width : Dim.Sp
  text : String

structure CensusPage where
  lines : Array CensusLine
  covered : String
  rules : Nat
  fills : Nat

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
    for l in p.lines do
      let mut chars := ""
      for seg in l.segs do
        match seg with
        | .run _ color _ _ glyphs _ _ _ =>
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
        | .rule .. => rules := rules + 1
        -- an image is decorative ink to the text census, like a rule
        | .image .. => pure ()
      lines := lines.push { x := l.x, width := l.setWidth, text := chars }
      covered := covered.push ' '
    pages := pages.push { lines := lines
                          covered := covered
                          rules := rules
                          fills := p.fills.size }
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

/-- The right edge (x plus set width) of the first shipped line on page `i`
containing `needle`: where a footer's right slot must end. -/
def lineRightOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map
    fun l => l.x + l.width

/-- Census assertions, one row per golden fixture: what each fixture's
shipped pages must show, judged from `Layout.Out` — never from the IR dump,
which witnesses elaboration only. `censusChecks` fails when a fixture in
`goldenNames` has no row here, so a fixture cannot enter the suite
witnessed by its golden alone. Facts are observable page claims: text
shipped (or deliberately not, for a note), covered-coloured runs on step
pages, rules and fills drawn, line positions for centring and columns. -/
def censusTable :
    List (String × (Layout.Geom → Array CensusPage → List (String × Bool))) := [
  ("paragraphs", fun _ c => [
    ("one page", c.size == 1),
    ("the opening sentence ships", hasStr (censusText c) "Typesetting is the arrangement of type"),
    ("it wraps to at least four lines", (c[0]?.map fun p => decide (p.lines.size ≥ 4)).getD false)]),
  ("layout", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "The first section"),
    ("a list marker ships beside its item", hasStr (censusText c) "• One concise point")]),
  ("declared", fun _ c => [
    ("one page, as the fixture asserts", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared geometry")]),
  ("fonts", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Faces"),
    ("the body claim ships", hasStr (censusText c) "Body text is set in the serif family")]),
  ("palette", fun _ c => [
    ("one page", c.size == 1),
    ("the coloured heading ships", hasStr (censusText c) "A coloured heading")]),
  ("tokens", fun _ c => [
    ("one page", c.size == 1),
    ("the heading ships", hasStr (censusText c) "Declared spacing")]),
  ("fill", fun _ c => [
    ("one page", c.size == 1),
    ("hfill sets both edges on one line",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Left edge").map
        fun l => hasStr l.text "right edge").getD false)]),
  ("links", fun _ c => [
    ("one page", c.size == 1),
    ("the running foot resolves page number and count", hasStr (censusText c) "page 1 of 1"),
    ("link underlines ship as rules", (c[0]?.map fun p => decide (p.rules ≥ 1)).getD false)]),
  ("resume", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Alex Doe"),
    ("the contact line ships", hasStr (censusText c) "alex@example.org")]),
  ("talk", fun _ c => [
    ("a page per overlay step plus one per remaining frame", c.size == 6),
    ("the first step page dims the pending lines in place",
      pageCovered c 0 "Metrics are queryable"),
    ("the dimmed text still ships", pageHas c 0 "Metrics are queryable"),
    ("the final step page has nothing covered", pageAllRevealed c 2)]),
  ("deck", fun _ c => [
    ("a page per frame, divider, and step", c.size == 8),
    ("the title frame ships the title", pageHas c 0 "A Certified Deck"),
    ("the standout frame fills its background", (c[7]?.map (·.fills == 1)).getD false),
    ("the standout content ships", pageHas c 7 "Questions?")]),
  ("themed", fun _ c => [
    ("pages", c.size == 6),
    ("the section page carries its progress-bar fills", (c[1]?.map fun p => decide (p.fills ≥ 2)).getD false),
    ("the frame-title bar fills", (c[2]?.map fun p => decide (p.fills ≥ 1)).getD false),
    ("the covered step dims the alert and example beats in place",
      pageCovered c 3 "alert beat" && pageCovered c 3 "teal example beat"),
    ("the covered beats still ship", pageHas c 3 "alert beat"),
    ("the second step reveals them", pageAllRevealed c 4),
    ("the standout frame fills its background", (c[5]?.map fun p => decide (p.fills ≥ 1)).getD false)]),
  ("latex-idioms", fun _ c => [
    ("one page", c.size == 1),
    ("the running head ships", hasStr (censusText c) "Alex Doe"),
    ("the section rules draw", c.any fun p => decide (p.rules ≥ 1))]),
  ("headroom", fun geom c => [
    ("one page", c.size == 1),
    ("the head ships with its page number", hasStr (censusText c) "Invented Field Notes"),
    ("the body ships under it", hasStr (censusText c) "reserves a band below the margin"),
    ("the head keeps its own line: no body text beside it",
      ((c[0]?.bind fun p => p.lines.find? fun l => hasStr l.text "Invented Field Notes").map
        fun l => !hasStr l.text "tight margin").getD false),
    ("body lines sit at the margin, not in the band",
      lineXOf c 0 "The running head above this page" == some geom.hmargin)]),
  ("wrapper", fun _ c => [
    ("both wrapper halves ship around the body",
      hasStr (censusText c) "First: body one (end First)"),
    ("the renewed environment ships its new half", hasStr (censusText c) "Aside. body two")]),
  ("centering", fun geom c => [
    ("the lead line sits at the margin",
      lineXOf c 0 "Left-aligned lead." == some geom.hmargin),
    ("the centred line sits past the margin",
      (lineXOf c 0 "One centred line.").any fun x => decide (x > geom.hmargin)),
    ("the standout line is centred",
      (lineXOf c 1 "Questions?").any fun x => decide (x > geom.hmargin))]),
  ("columns", fun geom c => [
    ("two frames, two pages", c.size == 2),
    ("the narrow column sets right of the wide one",
      (lineXOf c 0 "A narrow aside.").any fun x => decide (x > geom.hmargin)),
    ("both equal shares ship", pageHas c 1 "left half" && pageHas c 1 "right half")]),
  ("overlays-blocks", fun _ c => [
    ("a page per step across all frames", c.size == 12),
    ("a list revealed whole is covered whole",
      pageCovered c 0 "Placeholder point one." && pageCovered c 0 "Placeholder point two."),
    ("the covered list still ships its markers", pageHas c 0 "• Placeholder point one."),
    ("alt shows its second beat covered first", pageCovered c 9 "The second beat."),
    ("alt covers the first beat on the later step", pageCovered c 10 "The first beat."),
    ("a pause inside a column dims below it", pageCovered c 7 "Below the pause.")]),
  ("chrome", fun geom c => [
    ("pages", c.size == 5),
    -- The title page is `\frame[plain,noframenumbering]` (moloch): no chrome,
    -- and it does not advance the count — so the first content frame is 1, not
    -- 2, and nothing on page 1 carries the section title or a number.
    ("the title page carries no footer",
      !pageHas c 0 "Footers" &&
        ((c[0]?.map fun p => p.lines.all (·.text != "1")).getD false)),
    ("numbering starts at the first countable frame",
      pageHas c 2 "Footers" && lineRightOf c 2 "1" == some (geom.pageW - geom.hmargin)),
    ("a framefoot note takes the left slot", pageHas c 3 "source: example.org/data"),
    ("the default footer returns when the wrapper ends",
      pageHas c 4 "Footers" && lineRightOf c 4 "3" == some (geom.pageW - geom.hmargin))]),
  -- The footline's slots have fixed positions (FINDINGS F5 correction): a
  -- slot's box is a function of the declared layout and the geometry alone
  -- (`Layout.bandSlotX`), so the number holds the right edge whatever the
  -- left slot holds — an empty left slot is not a case.
  ("footer-left", fun geom c => [
    ("pages", c.size == 4),
    ("the sectionless frame still numbers at the right edge",
      lineRightOf c 1 "1" == some (geom.pageW - geom.hmargin)),
    ("the number is a line of its own, whole and unmoved",
      ((c[1]?.bind fun p => p.lines.find? fun l => hasStr l.text "1").map
        fun l => l.text == "1").getD false),
    ("the section title takes the left slot flush left",
      lineXOf c 3 "Placement" == some geom.hmargin),
    ("the sectioned frame numbers at the same right edge",
      lineRightOf c 3 "2" == some (geom.pageW - geom.hmargin))]),
  -- FINDINGS F4: the two sequences share a band only by declaration. The
  -- stepped frame is where they visibly disagree: its pages advance the
  -- physical number and hold the frame number — one counter could never
  -- ship these pages.
  ("footer-mixed", fun _ c => [
    ("pages", c.size == 5),
    ("the step pages advance the physical number",
      pageHas c 2 "p. 3" && pageHas c 3 "p. 4"),
    ("and hold the frame number across the step",
      (lineRightOf c 2 "p. 3").isSome && pageHas c 2 "1" && pageHas c 3 "1"),
    ("the plain frame carries the next of both",
      pageHas c 4 "p. 5" && pageHas c 4 "2")]),
  -- The F5 correction's collision half: the boxes overlap and the number —
  -- lower priority — yields IN PLACE: still at the right margin, painted
  -- first so the note paints over it. The yield's diagnostic (W0333) and
  -- the paint order are asserted in bandChecks; the census states the
  -- boxes.
  ("footer-collide", fun geom c => [
    ("pages", c.size == 2),
    ("the number still ends at the right margin",
      lineRightOf c 1 "1" == some (geom.pageW - geom.hmargin)),
    ("the overlong note still ships flush left",
      lineXOf c 1 "0123456789" == some geom.hmargin)]),
  ("lists", fun _ c => [
    ("one page", c.size == 1),
    ("four itemize levels ship their four marks",
      ["• Outer point one", "– Second level", "* Third level", "· Fourth level"].all
        fun m => hasStr (censusText c) m),
    ("enumerate marks per level", ["1. First", "(a) Nested resets to one",
      "i. Third level", "A. Fourth level"].all fun m => hasStr (censusText c) m),
    ("the enclosing counter resumes", hasStr (censusText c) "3. Third")]),
  ("lists-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the base override ships", hasStr (censusText c) "– The base override"),
    ("the level override ships", hasStr (censusText c) "• The level override")]),
  -- The two marker fixtures carry FINDINGS F1: a declared marker either
  -- reaches a backend as declared or the substitution has a name (W0331).
  -- The PDF side is judged here; the HTML side and the agreement between
  -- them are judged in agreeChecks.
  ("marker-styled", fun _ c => [
    ("one page", c.size == 1),
    ("the declared en-dash marker ships beside each item",
      pageHas c 0 "– First invented point" && pageHas c 0 "– Second invented point")]),
  ("marker-content", fun _ c => [
    ("one page", c.size == 1),
    ("the items ship", pageHas c 0 "An item marked by a picture"),
    ("no default text marker substitutes for the image",
      !pageHas c 0 "• An item" && !pageHas c 0 "– An item")]),
  ("lists-deck", fun _ c => [
    ("pages", c.size == 4),
    ("nesting shows through the theme", pageHas c 1 "– Nested under the stepped item"),
    ("ordered marks on a slide", pageHas c 3 "1. First placeholder")]),
  -- the census carries x and text, not y; the [t]/[c]/[b] geometry itself
  -- is pinned by vdistChecks over Layout.LineOut
  ("valign", fun _ c => [
    ("five frames, the overflow spilling once", c.size == 6),
    ("each declared frame ships its body",
      pageHas c 0 "A short body sits midway" && pageHas c 1 "This body hugs its title"
        && pageHas c 2 "This body sits on the bottom margin"),
    ("the spill page carries the overflow", pageHas c 5 "resolved to enumerate")]),
  ("images", fun _ c => [
    ("one page", c.size == 1),
    ("the sentence around the inline image ships",
      hasStr (censusText c) "sits in the line"),
    ("the figure caption ships", hasStr (censusText c) "Three rectangles, fitted")]),
  ("webpage", fun _ c => [
    ("one page", c.size == 1),
    ("the name ships", hasStr (censusText c) "Doe"),
    ("the section headings ship",
      hasStr (censusText c) "Experience" && hasStr (censusText c) "Education")]),
  ("webnav", fun _ c => [
    ("one page", c.size == 1),
    ("the shared content ships", hasStr (censusText c) "appears on every surface"),
    ("the print-only conditional ships on the page",
      hasStr (censusText c) "This sentence is set only on the printed page."),
    ("the web-only nav never reaches the page",
      !hasStr (censusText c) "Back to top")]),
  ("icons", fun _ c => [
    ("one page", c.size == 1),
    ("the contact words ship", hasStr (censusText c) "Email"),
    ("the icon glyphs ship as ink",
      hasStr (censusText c) "\uF09B" && hasStr (censusText c) "\uF0E0" &&
      hasStr (censusText c) "\uF08C" && hasStr (censusText c) "\uF19D" &&
      hasStr (censusText c) "\uF062")]),
  ("diagram", fun geom c => [
    ("one page", c.size == 1),
    ("the 4×4 grid ships its sixteen fills",
      (c[0]?.map (·.fills == 16)).getD false),
    ("every diagonal label ships",
      ["aa", "bb", "cc", "dd"].all fun l => hasStr (censusText c) l),
    ("the labels step up the diagonal",
      (((lineXOf c 0 "aa").bind fun xa => (lineXOf c 0 "dd").map fun xd =>
        decide (xa < xd)).getD false)),
    ("the centred picture stands past the margin",
      ((lineXOf c 0 "aa").map fun x => decide (x > geom.hmargin)).getD false),
    ("the prose around the diagram ships",
      hasStr (censusText c) "Before the diagram" &&
        hasStr (censusText c) "After the diagram")]),
  ("diagram-overflow", fun _ c => [
    ("one page", c.size == 1),
    ("the band ships as a fill", (c[0]?.map (·.fills == 1)).getD false),
    ("its label ships", hasStr (censusText c) "wide band")]),
  ("tables", fun geom c => [
    ("one page", c.size == 1),
    ("the header row ships", hasStr (censusText c) "Construct"
      && hasStr (censusText c) "Meaning"),
    ("every body cell ships", hasStr (censusText c) "invented row"
      && hasStr (censusText c) "alpha" && hasStr (censusText c) "beta"),
    ("both table captions ship",
      hasStr (censusText c) "A booktabs table with declared spacing."
        && hasStr (censusText c) "The caption above: the table convention."),
    ("the figure caption ships",
      hasStr (censusText c) "A figure’s caption, bound below what it captions."),
    -- top + mid + bottom, then top + cmid + bottom: six drawn rules.
    ("the booktabs rules draw", ((c[0]?.map (·.rules)).getD 0) == 6),
    ("cells sit in their declared columns: the second column right of the first",
      ((lineXOf c 0 "Construct").bind fun a =>
        (lineXOf c 0 "Meaning").map fun b => decide (a < b)).getD false),
    ("the floated table centres: its first cell sits past the margin",
      (lineXOf c 0 "invented row").any fun x => decide (x > geom.hmargin))]),
  ("tables-ragged", fun _ c => [
    ("one page", c.size == 1),
    ("every declared cell ships, the ragged row's included",
      hasStr (censusText c) "alpha" && hasStr (censusText c) "gamma"
        && hasStr (censusText c) "delta" && hasStr (censusText c) "epsilon"),
    ("the rules draw", ((c[0]?.map (·.rules)).getD 0) == 2)]),
  ("math", fun _ c => [
    ("one page", c.size == 1),
    ("prose around the display ships",
      hasStr (censusText c) "The paragraph continues after the display"),
    ("the display-size sum ships as a glyph", hasStr (censusText c) "∑"),
    ("an align row ships aligned glyphs", hasStr (censusText c) "=(𝑥−1)(𝑥+1)"),
    ("every fraction bar and overbar ships as a rule",
      ((c[0]?.map (·.rules)).getD 0) == 8),
    ("the out-of-scope accent keeps its source", hasStr (censusText c) "\\hat")]),
  ("math-companion", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display sum ships as a glyph", hasStr (censusText c) "∑"),
    ("the fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1),
    ("prose after the display ships",
      hasStr (censusText c) "The paragraph continues after the display")]),
  ("math-first", fun _ c => [
    ("one page", c.size == 1),
    ("the inline formula ships italic math glyphs", hasStr (censusText c) "𝑥"),
    ("the display fraction bar ships as a rule", ((c[0]?.map (·.rules)).getD 0) == 1)]),
  ("quotes", fun geom c => [
    ("one page", c.size == 1),
    ("the quotation's text ships", hasStr (censusText c) "A short invented epigraph"),
    ("the quotation's second paragraph ships",
      hasStr (censusText c) "The second paragraph of the same quotation"),
    ("prose sits at the margin",
      lineXOf c 0 "A paragraph before the quotation" == some geom.hmargin),
    ("the quotation indents from the margin by the list indent",
      lineXOf c 0 "A short invented epigraph"
        == some (geom.hmargin + geom.listIndent))]),
  ("quote-deck", fun geom c => [
    ("one frame, one page", c.size == 1),
    ("the quotation ships on the slide",
      pageHas c 0 "Typesetting is invisible until it fails"),
    ("the slide's quotation indents from the margin",
      (lineXOf c 0 "Typesetting is invisible").any fun x =>
        decide (x == geom.hmargin + geom.listIndent))]),
  ("outline", fun _ c => [
    ("one page", c.size == 1),
    ("the level-0 title ships as the title furniture",
      hasStr (censusText c) "An Invented Field Guide"),
    ("the author line ships under it", hasStr (censusText c) "Alex Doe"),
    ("every rung of the heading ladder ships",
      ["Habitats", "Wetlands", "Reed Beds", "Migration"].all
        fun h => hasStr (censusText c) h)]),
  ("outline-gap", fun _ c => [
    ("one page", c.size == 1),
    ("the diagnosed document still ships every heading",
      hasStr (censusText c) "Field Notes" &&
        hasStr (censusText c) "A Detail Too Deep")]),
  ("overlays", fun _ c => [
    ("one handout page per step", c.size == 5),
    ("step one dims the later beats in place",
      pageCovered c 0 "Second beat." && pageCovered c 0 "Third beat."),
    ("the dimmed beats still ship", pageHas c 0 "Second beat."),
    ("the last step reveals everything", pageAllRevealed c 2),
    ("pause dims what follows it", pageCovered c 3 "After the pause.")]),
  ("notes", fun _ c => [
    ("one page", c.size == 1),
    ("the note never ships on the handout", !hasStr (censusText c) "Say hello"),
    ("the paragraph flows on unbroken", hasStr (censusText c) "never breaks the flow")]),
  ("furniture", fun _ c => [
    ("pages", c.size == 6),
    ("the title ships", pageHas c 0 "Frame Furniture"),
    ("the centred line ships", hasStr (censusText c) "This line is centred."),
    ("the step page dims its pending beats", pageCovered c 3 "Second beat."),
    ("the narrow column ships", hasStr (censusText c) "The narrow column.")]),
  ("trio-page", fun _ c => [
    ("one page", c.size == 1),
    ("the studio name ships", hasStr (censusText c) "Cardamom Press"),
    ("the shared section style draws its rules", (c[0]?.map (·.rules == 2)).getD false)]),
  ("trio-deck", fun _ c => [
    ("pages", c.size == 4),
    ("the title ships", pageHas c 0 "Cardamom Press"),
    ("the divider draws the section rule", (c[2]?.map (·.rules == 1)).getD false)]),
  ("trio-card", fun _ c => [
    ("two faces, two pages", c.size == 2),
    ("the front ships the name", pageHas c 0 "Pat Placeholder"),
    ("the back ships the contact", pageHas c 1 "press@example.org")])]

/-- The census tier: every golden fixture also appears in `censusTable`,
and each row's facts hold on the pages the engine actually ships. A
fixture that declares a math face renders its census with the shipped
Fira Math in the math slot — the assertions over fraction bars and grown
glyphs are exactly what `oneFace` alone could never witness. -/
def censusChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"census: FiraMath unparsable: {e}")
  let mathSet : Font.FontSet := { oneFace with
    fonts := oneFace.fonts.push fira
    math := some oneFace.fonts.size }
  for n in goldenNames do
    check ref s!"census covers {n}" (censusTable.any (·.1 == n))
  for (n, _) in censusTable do
    check ref s!"census row {n} names a golden fixture" (goldenNames.contains n)
  -- A fixture that reaches math without declaring a face resolves it the
  -- way the driver does (FontDb.pickMathFace over the shipped faces), so
  -- the census exercises the same decision a build runs.
  let shipped ← FontDb.scanRoots [testFonts]
  for (n, facts) in censusTable do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) := Elab.run s!"{n}.tex" src
    let geom := Layout.Geom.ofPage doc.page
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
    -- The driver's per-scalar precompute, mirrored for the Private Use
    -- Area only: an icon glyph has no stand-in and no meaning outside its
    -- face, so the census finds its face the way a build does (the scan
    -- over the shipped corpus). Everything else keeps the deliberately
    -- minimal census set — the stand-in degradations are themselves under
    -- test (`listChecks`), and a broader map would silently upgrade them.
    let uncovered := (Layout.docScalars doc).filter fun ch =>
      0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF &&
        fs.fonts.all fun f => (f.gid ch).isNone
    let fs ← do
      if uncovered.isEmpty then pure fs
      else do
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
        pure fs
    let out := Layout.run geom fs (some pats) doc
    let c := censusOf (coveredColorsOf doc) out
    for (label, ok) in facts geom c do
      check ref s!"census {n}: {label}" ok

/-- The F5 correction, executably: a slot's box is a function of the
declared layout and the geometry alone (`Layout.bandSlotX` — the other
slot is not an argument), priorities decide who yields
(`Ir.ChromeSlot.priority`, total by `priority_injective` and
`BandSlot.rank_ne_of_side_ne`), and yielding is in place and named. One
deck, three left slots — empty, a section title, an unbreakable overlong
note — and the number's line must be byte-identical in x and width across
all three. On the collision the number is painted first (under), still at
the right margin, and W0333 names both the slot that yielded and the slot
that displaced it. -/
def bandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let longTok := String.ofList (List.replicate 10 "0123456789".toList).flatten
  let frame := "\\begin{frame}{F}\nx\n\\end{frame}"
  let run (left : String) : Layout.Out × Array CensusPage :=
    let (doc, _) := elabStr (deck "\\theme{moloch}\\title{T}\\author{A}"
      (s!"\\maketitle\n{left}{frame}"))
    let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
    (out, censusOf (coveredColorsOf doc) out)
  -- The number's box on the frame's page: the line whose text is exactly
  -- the number, as (x, width).
  let numBox (c : Array CensusPage) (page : Nat) : Option (Dim.Sp × Dim.Sp) :=
    (c[page]?.bind fun p => p.lines.find? (·.text == "1")).map fun l => (l.x, l.width)
  let (emptyOut, emptyC) := run ""
  let (secOut, secC) := run "\\section{S}\n"
  let (noteOut, noteC) := run s!"\\framefoot\{{longTok}}\n"
  t "band: the empty and filled left slots leave the number's box unmoved"
    (numBox emptyC 1 == numBox secC 2 && (numBox emptyC 1).isSome)
  t "band: the colliding left slot leaves the number's box unmoved too"
    (numBox noteC 1 == numBox emptyC 1)
  t "band: no collision, no yield" ((emptyOut.diags ++ secOut.diags).all
    (·.code != "W0333"))
  t "band: the yield is named with both slots"
    (noteOut.diags.any fun d => d.code == "W0333" && d.severity == .warning &&
      hasStr d.message "framenumber" && hasStr d.message "framefoot note")
  t "band: the yielding number is painted first, under the note"
    ((noteC[1]?.map fun p =>
      match p.lines.findIdx? (·.text == "1"),
            p.lines.findIdx? (fun l => hasStr l.text longTok) with
      | some ni, some ti => ni < ti
      | _, _ => false).getD false)
  -- The section-title case of the same order: an unbreakable overlong
  -- section title displaces the number, never the reverse.
  let (secCollideOut, secCollideC) := run s!"\\section\{{longTok}}\n"
  t "band: the number yields to the section title by declared priority"
    (secCollideOut.diags.any fun d => d.code == "W0333" &&
      hasStr d.message "framenumber yields" && hasStr d.message "sectiontitle")
  t "band: and holds the right margin while yielding"
    (numBox secCollideC 2 == numBox emptyC 1)

-- Cross-backend agreement -------------------------------------------------

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

/-- The cross-backend agreement tier, over every golden fixture: a declared
fact both backends render — a footer's slot contents and their sides, a
list item's marker — renders the same from `Layout.Out` and from the typed
HTML tree, or a diagnostic names the divergence (W0007 physical furniture
omitted, W0331 marker substituted, W0332 sequences mixed). This is the
general form of FINDINGS F1 and F5: the next divergence in any fixture
fails here without anyone looking at a page. -/
def agreeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let namingCodes := ["W0007", "W0331", "W0332"]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, docDs) := Elab.run s!"{n}.tex" src
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom oneFace (some pats) doc
    let (_, body, htmlDs) := HtmlDoc.emitTree {} doc
    let naming := (docDs ++ out.diags ++ htmlDs).any (namingCodes.contains ·.code)
    let pdf := dedupConsecutive (pdfFoots out)
    let html := slideFootsList #[] body.toList
    check ref s!"agree {n}: footer slots match across backends, or are named"
      (pdf == html || naming)
    for (element, st) in doc.styles.entries do
      if let some m := st.marker then
        match HtmlDoc.markerCss? m with
        | some r =>
          -- The expressible marker shows the declared characters — the
          -- executable face of `markerCss?_text`, judged per fixture.
          check ref s!"agree {n}: the '{element}' marker's HTML text is the declared text"
            (r.text == Ir.plainText m)
        | none =>
          check ref s!"agree {n}: the '{element}' marker's substitution is named"
            (htmlDs.any (·.code == "W0331"))


/- One diagnostic code, one meaning: `DiagCode` in Diag.lean is the single
place a code lives — an unregistered code is unrepresentable, because every
emission site passes a constructor, and a new code is forced through the
`DiagCode.spec` match, where a collision with an existing number is visible
before it ships. The defect class is real twice over: the card slice nearly
renumbered W0315 over the contrast pairing (PLAN 2026-09-17), and the old
string registry's first run found W0314 meaning both a column width and an
unknown theme. What is left to check at runtime: the spec's code strings are
unique (a constructor cannot claim another's number), each carries a
meaning, and no constructor outlives its last emission site. -/

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

def diagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let codes := DiagCode.all.map (·.code)
  for c in codes.eraseDups do
    check ref s!"diag {c}: one code, one meaning"
      ((codes.filter (· == c)).length == 1)
  for c in DiagCode.all do
    check ref s!"diag {c.code}: carries a meaning" (!c.meaning.isEmpty)
    check ref s!"diag {c.code}: code string is code-shaped" (isDiagCode c.code)
  -- No constructor outlives its last emission site, and an emitted
  -- constructor's code string is registered under its own name (a
  -- `spec` arm answering another arm's number would surface here).
  -- The compiler already holds the other direction: a code that is not
  -- a constructor cannot be emitted at all.
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  let mut emitted : List String := []
  for f in files do
    if f.toString == "LeanTex/Core/Diag.lean" then continue
    let src ← IO.FS.readFile f
    for c in appliedCodes (stripNonCode src) do
      if !emitted.contains c then
        emitted := c :: emitted
  for c in emitted do
    check ref s!"diag {c}: emitted by the engine but not in the registry"
      (codes.contains c)
  for c in codes do
    check ref s!"diag {c}: registered but no longer emitted"
      (emitted.contains c)

/- Every registered diagnostic renders into one golden a person can read
whole: tests/golden/diagnostics.txt. The witness table below holds one
firing input per code — an exhaustive match, so a new `DiagCode`
constructor does not build until it names the input that fires it, and the
coverage check holds each witness to actually firing its code. -/

def dvDoc (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def dvDeck (pre body : String) : String :=
  "\\documentclass{slides}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

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

/-- One firing input per code. `one` maps every slot to one face;
`mapped` adds a second face and a fallback map for the substitution codes.
The synthetic driver arguments mirror what Main.lean passes. -/
def diagWitness (one mapped : Font.FontSet) : DiagCode → Array Diag
  | .E0001 => #[DriverDiag.unreadableInput "doc.tex"
      "no such file or directory (error code: 2)"]
  | .E0002 =>
    match Utf8.validate (ByteArray.mk #[0xC3, 0x28]) with
    | some e => #[e.toDiag "doc.tex"]
    | none => #[]
  | .E0101 => dvE "a\\"
  | .E0102 => dvE "\\begin{verbatim}\nx"
  | .E0111 => dvE (dvDeck "" ("\\setbeamertemplate{footline}{\\insertframenumber}\n" ++
      "\\begin{frame}{T}\nx\n\\end{frame}"))
  | .E0112 => dvE (dvDoc "\\titlegraphic{\\includegraphics{logo.png}}\n" "x")
  | .E0113 => dvE (dvDoc
      "\\renewcommand\\sectionlinesformat[4]{\\raisebox{-1pt}{#3}}\n" "x")
  | .E0201 => dvE "{a"
  | .E0202 => dvE "a}"
  | .E0205 => dvE "\\begin{ x"
  | .E0303 => dvE (dvDoc "\\define \\x(a b {y}\n" "x")
  | .E0304 => dvE (dvDoc "\\page\n" "x")
  | .E0305 => dvE (dvDoc "\\define \\role(who: text) {\\textbf{\\who}}\n" "\\role{$x$}")
  | .E0306 => dvE (dvDoc "\\define \\x(a?: text) {\\ifgiven{\\b}{y}}\n" "\\x{z}")
  | .E0309 => dvE "\\documentclass{poster}\n\\begin{document}\nx\n\\end{document}"
  | .E0310 => dvE (dvDoc "" "\\begin{itemize}\nstray\n\\item x\n\\end{itemize}")
  | .E0311 => dvE "a & b"
  | .E0312 => dvE "\\textbf{\\section{x}}"
  | .E0313 => dvE "\\documentclass{article}\nstray text\n\\begin{document}\nx\n\\end{document}"
  | .E0316 => dvE (dvDoc "\\define \\x(a?: text) {\\a}\n" "\\x[oops")
  | .E0320 => dvE (dvDoc "\\page{ oops }\n" "x")
  | .E0321 => dvE "\\includegraphics[scale=big]{x.png}"
  | .E0322 => dvE (dvDoc "\\page{ zoom = 3 }\n" "x")
  | .E0323 => dvE (dvDoc "\\page{ vmargin = \"x\" }\n" "x")
  | .E0324 => dvE (dvDoc "\\page{ size = quarto }\n" "x")
  | .E0325 => dvE (dvDoc "\\assert{ pages =~ 1 }\n" "x")
  | .E0326 => dvE (dvDoc "\\palette{ a = missingname }\n" "x")
  | .E0327 => dvE (dvDoc "\\page{ header = x }\n" "x")
  | .E0328 => dvE (dvDoc "\\style{banana}{ color = ink }\n" "x")
  | .E0329 => dvE (dvDoc "\\allow{W9999}\n" "x")
  | .E0330 =>
    (Check.one { pages := 2, fontsEmbedded := true }
      { kind := .pages .eq 1, span := none }).toArray
  | .E0331 => dvE "\\includegraphics[width=banana]{x.png}"
  | .E0332 => dvE (dvDoc "\\palette{covered = 100\\%}\n" "x")
  | .E0333 => dvE (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\fill (\\nope,0) rectangle (1,1);\n\\end{tikzpicture}"))
  | .E0336 => dvE (dvDoc "" "\\begin{banner}{Logo}\nx\n\\end{banner}")
  | .E0340 => dvE "\\faIcon{no-such-icon}"
  | .E0334 => dvE (dvDoc "" ("\\begin{ifbackend}{html}\\begin{ifbackend}{pdf}\n" ++
      "orphaned\n\\end{ifbackend}\\end{ifbackend}"))
  | .E0401 => #[DriverDiag.noFont]
  | .E0402 => #[DriverDiag.envFontMissing "/tmp/face.ttf",
      DriverDiag.envFontUnusable "/tmp/face.ttf" "not a TrueType or OpenType file"]
  | .E0403 => #[DriverDiag.familyMissing "Sourse Serif Pro" ["Source Serif Pro"] 0,
      DriverDiag.familyMissing "Kaputt Grotesk" [] 12]
  | .E0404 => #[DriverDiag.fontFileUnusable "fonts/Broken-Regular.otf"
      "not a TrueType or OpenType file"]
  | .E0405 => dvL mapped "lost \u27e8 here"
  | .E0501 => #[DriverDiag.inputTooDeep]
  | .E0502 => #[DriverDiag.inputMissing "chapter1.tex" none]
  | .N0100 => dvE (dvDoc "\\usepackage[margin=1in]{geometry}\n" "x")
  | .N0102 => dvE (dvDeck "" "\\begin{frame}[fragile]{T}\nx\n\\end{frame}")
  | .N0103 => dvE (dvDoc "" "\\section[short]{A long title}\nx")
  | .N0114 =>
    dvE (dvDoc "\\ifdefined\\shiny\\sloppy\\else\\relax\\fi\n" "x") ++
    dvE (dvDoc "\\newcommand{\\shiny}{y}\\ifdefined\\shiny\\relax\\fi\n" "x")
  | .N0200 => dvL one (dvDoc "\\page{ height = 115pt, margin = 20pt }\n"
      "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc")
  | .N0016 => #[DriverDiag.mathFaceCompanion "TeX Gyre Pagella Math" "TeX Gyre Pagella",
      DriverDiag.mathFaceFirst "Fira Math"]
  | .W0001 => dvE (dvDoc "" "x\n\\end{document}\nleft over")
  | .W0003 => dvL one (dvDoc "" "$x^2$")
  | .W0005 => dvL one (dvDoc "\\page{ width = 60pt, margin = 10pt, justify = on }\n"
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  | .W0006 =>
    let face : FontDb.Face := { path := "fonts/DemoSerif-Regular.otf"
                                family := "Demo Serif"
                                subfamily := "Regular"
                                bold := false
                                italic := false
                                fixedPitch := false
                                weight := 400 }
    let ask (declared : Option String) : Array Diag :=
      match FontDb.resolveVariant #[face] "Demo Serif" declared { bold := true } with
      | some (_, some msg) => #[Diag.of .W0006 msg]
      | _ => #[]
    ask none ++ ask (some "DemoSerif-Bold.otf")
  | .W0007 => dvH (dvDoc "\\runninghead{name}\n" "x")
  | .W0008 => #[DriverDiag.fontsDirMissing "fonts" "/documents/fonts"]
  | .W0009 => dvL mapped "for all is \u2200 set"
  | .W0010 => dvL one (dvDoc "" (String.join
      ((List.range 5).map fun _ => "\\begin{itemize}\\item x\n") ++
      String.join ((List.range 5).map fun _ => "\\end{itemize}\n")))
  | .W0011 => #[DriverDiag.mathFaceNoTable "Demo Serif" "fonts/DemoSerif-Regular.otf"]
  | .W0012 => dvE "$\\hat{x}$"
  | .W0013 => #[DriverDiag.allowUnfired "E0333"]
  | .W0014 => dvE "\\begin{align*}a &= b \\\\ c\\end{align*}"
  | .W0015 => dvE "\\begin{align}a &= b\\end{align}"
  | .W0101 => dvE (dvDoc "\\usepackage[headsep=1in]{geometry}\n" "x")
  | .W0102 => dvE (dvDoc "\\definecolor{c}{hsb}{0.5,0.5,0.5}\n" "x")
  | .W0103 => dvE (dvDoc "\\usepackage{pgfplots}\n" "x")
  | .W0104 => dvE (dvDoc (String.intercalate "\n"
      ["\\directlua{tex.print('x')}", "\\def\\x{y}", "\\raggedright",
       "\\sloppy", "\\selectlanguage{german}", "\\pagestyle{scrheadings}",
       "\\ifx\\x\\y\\fi", "\\usecolortheme{dove}",
       "\\setbeamercovered{transparent}", "\\titlegraphic{}"] ++ "\n") "x")
  | .W0105 => dvE "\\uncover<zz>{x}"
  | .W0106 => dvE (dvDoc "\\ExplSyntaxOn \\cs_new:Npn \\x { } \\ExplSyntaxOff\n" "x")
  | .W0108 => dvE "\\textbf{\\centering x}"
  | .W0110 => dvE "\\includegraphics[angle=45]{x.png}"
  | .W0111 => dvE (dvDoc "\\setkomafont{banana}{\\bfseries}\n" "x")
  | .W0201 => dvL one (dvDoc "\\page{ hmargin = 1in }\n"
      (String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")))
  | .W0202 => dvL one (dvDoc "\\style{section}{ before = 2pt, after = 10pt }\n"
      "\\section{a}\nbody")
  | .W0301 => dvE "\\mystery{x}"
  | .W0307 => dvE (dvDoc "" "\\begin{external}\nx\n\\end{external}")
  | .W0302 => dvE (dvDoc "" "\\begin{banner}\nx\n\\end{banner}")
  | .W0303 => dvE (dvDoc "\\define \\textbf(a: content) {\\a}\n" "x")
  | .W0304 => dvE "\\textcolor{nope}{x}"
  | .W0309 => dvE (dvDoc "" "\\maketitle")
  | .W0310 => dvE (dvDoc "" "\\section[oops\nnever closed")
  | .W0311 => dvE (dvDeck "" ("\\begin{frame}\n\\frametitle{One}\n" ++
      "\\frametitle{Two}\nx\n\\end{frame}"))
  | .W0312 => dvE "\\title[never closes\n\\begin{document}\nx\n\\end{document}"
  | .W0314 => dvE (dvDeck "" ("\\begin{frame}{T}\\begin{columns}\n" ++
      "\\begin{column}{banana}\nx\n\\end{column}\n\\end{columns}\\end{frame}"))
  | .W0315 => dvE (dvDoc "\\palette{ washed = #DDDDDD }\n" "\\textcolor{washed}{faint}")
  | .W0316 => dvE (dvDoc "\\palette[dark]{ a = #101010 }\n" "x")
  | .W0317 => dvE ("\\documentclass{card}\n\\runninghead{name}\n" ++
      "\\begin{document}\nx\n\\end{document}")
  | .W0318 => dvE (dvDoc "\\chrome{ footer = { left = \\sectiontitle } }\n" "x")
  | .W0319 => dvE (dvDoc "\\theme{banana}\n" "x")
  | .W0320 => dvE (dvDoc "" "\\section{a}\n\n\\subsubsection{b}\nx")
  | .W0321 => dvE (dvDoc "\\title{T}\n" "\\section{a}\nx\n\n\\maketitle")
  | .W0322 => dvE (dvDoc "\\title{T}\n" "\\maketitle\n\n\\maketitle")
  | .W0323 => dvE (dvDoc "" "\\begin{ifbackend}{banana}\nx\n\\end{ifbackend}")
  | .W0325 => dvH (dvDoc "" ("\\begin{nav}\\link{#a}{A}\\end{nav}\n\n" ++
      "\\begin{nav}\\link{#b}{B}\\end{nav}\n\n\\section{a}\nx"))
  | .W0326 => dvH (dvDoc "" "\\link{#nowhere}{dead}")
  | .W0327 => dvH (dvDoc "" "\\section{Signal Path}\nx\n\n\\section{Signal, Path}\ny")
  | .W0328 => dvL one (dvDoc
      (s!"\\runningfoot\{{String.intercalate " " (List.replicate 40 "an overlong footer")}}\n")
      "x")
  | .W0329 => dvE (dvDoc "\\fontfallback{x}\n" "x")
  | .W0330 => dvE (dvDoc "\\palette{ bg = #18181B }\n" "x")
  | .W0331 => dvH (dvDoc
      "\\style{itemize}{ marker = {\\includegraphics{rects.png}} }\n"
      "\\begin{itemize}\n\\item a\n\\end{itemize}")
  | .W0332 => dvE (dvDeck "\\theme{moloch}\n"
      "\\framefoot{p. \\pagenumber}\n\\begin{frame}{T}\nx\n\\end{frame}")
  | .W0333 => dvL one (dvDeck "\\theme{moloch}\\title{T}\\author{A}\n"
      (s!"\\maketitle\n\\framefoot\{{String.ofList (List.replicate 100 '0')}}\n" ++
       "\\begin{frame}{F}\nx\n\\end{frame}"))
  | .W0334 => dvE (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\draw (0,0) circle (1);\n\\end{tikzpicture}"))
  | .W0335 => dvL one (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\fill (0,0) rectangle (40,1);\n\\end{tikzpicture}"))
  | .W0337 => dvE (dvDoc "" "\\begin{tabular}{ll}\na & b & c \\\\\nd \\\\\n\\end{tabular}")
  | .W0338 => dvL one (dvDoc "" ("\\begin{tabular}{p{0.8\\linewidth}p{0.8\\linewidth}}\n" ++
      "a & b \\\\\n\\end{tabular}"))
  | .W0339 =>
    -- The seam-break window is about one leading tall wherever the page
    -- bottom falls, so a 3pt `\vspace` sweep crosses it whatever the
    -- face's metrics say; the golden dedups the one rendered form.
    (List.range 50).foldl (init := #[]) fun acc k =>
      acc ++ dvL one (dvDoc "\\page{ size = a5 }\n"
        (s!"top\n\n\\vspace\{{350 + 3 * k}pt}\n\n\\begin\{table}\n" ++
         "\\begin{tabular}{l}\nalpha \\\\\n\\end{tabular}\n" ++
         "\\caption{Below the table}\n\\end{table}"))
  | .W0340 => dvE (dvDoc "" "x\n\n\\page{ size = a5 }\n\ny")
  | .W0341 => dvE "\\textls[16]{spaced}.example.org"
  | .W0342 => dvE (dvDoc "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n"
      "\\muted{x}")
  | .W0601 => #[DriverDiag.imageMissing "figures/plot.png" "/documents/figures/plot.png",
      DriverDiag.imageUnreadable "figures/plot.png" "permission denied (error code: 13)"]
  | .W0602 => #[DriverDiag.imageUndecodable "figures/plot.gif"
      "not a PNG or JPEG file"]

/-! The message lint: every fired message and help is judged mechanically.
Each check exists because the pasted real output violated it (the brief's
four defects); the golden covers what these cannot — tone, jargon, whether
a help actually helps. -/

/-- A reference only someone inside this repository can follow: a repo file,
a source path, or a milestone token (`M6`, `M8`). A diagnostic must be
actionable by someone holding only their own document. -/
def dvInternalRef (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "PLAN.md" || has "AGENTS.md" || has "LeanTex/" || has ".lean" ||
    (Id.run do
      let cs := s.toList.toArray
      for i in [0:cs.size] do
        if cs[i]! == 'M' && (cs[i+1]?.map Char.isDigit).getD false &&
            !((i > 0) && (cs[i-1]!.isAlphanum || cs[i-1]! == '_')) &&
            !(((cs[i+2]?.map (·.isAlphanum)).getD false)) then
          return true
      return false)

/-- A help either tells the reader what to write — a `\` spelling, a flag,
a `key = value`, a quoted literal, a backticked command, or a `:`-led
enumeration of the known values — or it should not exist. -/
def dvHasAction (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "\\" || has "--" || has "`" || has "=" || has ": " || has "{" ||
    (s.toList.filter (· == '\'')).length ≥ 2

/-- Message and help bounds, in characters, taken from the two longest
texts that read well rather than from a round number: the message bound is
W0315's fired message (121 characters, one clause with the ratio, the
threshold, and the source), the help bound E0328's list of every styleable
element (181 characters, generated from `styleableElements`; growing that
list means deciding this bound again). -/
def dvMsgMax : Nat := 121
def dvHelpMax : Nat := 181

/-- Sentence case: a message opens lowercase (or with a quoted construct)
unless its first word is a proper noun the engine speaks of. -/
def dvCaseOk (s : String) : Bool :=
  match s.toList with
  | [] => true
  | c :: _ =>
    !c.isUpper ||
      ["TeX", "LaTeX", "LEANTEX_FONT", "PNG", "JPEG", "WCAG", "HTML",
       "U+"].any (s.startsWith ·)

/-- One convention for terminal punctuation: none (a `?` may close a real
question). -/
def dvTerminalOk (s : String) : Bool :=
  !(s.endsWith "." || s.endsWith "!")

/-- Code-shaped tokens in prose: a reader cannot look a code up, so a
message or help may name only the code it is itself printed under. -/
def dvForeignCodes (own : String) (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut tok := ""
  for c in s.toList ++ [' '] do
    if c.isAlphanum then
      tok := tok.push c
    else
      if isDiagCode tok && tok != own && !out.contains tok then
        out := tok :: out
      tok := ""
  return out

/-- The lint over one fired diagnostic. `\allow`-teeth codes (W0013, E0329)
quote codes the user wrote in their own document, so the foreign-code check
does not apply to them. -/
def dvLint (fail : String → IO Unit) (d : Diag) : IO Unit := do
  let judge (part : String) (s : String) : IO Unit := do
    if dvInternalRef s then
      fail s!"{d.code} {part}: repo-internal reference: {s}"
    unless dvTerminalOk s do
      fail s!"{d.code} {part}: terminal punctuation: {s}"
    unless dvCaseOk s do
      fail s!"{d.code} {part}: starts uppercase without a proper noun: {s}"
    if (s.splitOn "\"\\").length > 1 then
      fail s!"{d.code} {part}: a construct is double-quoted; the convention is '...': {s}"
    unless d.code == "W0013" || d.code == "E0329" do
      for tok in dvForeignCodes d.code s do
        fail s!"{d.code} {part}: names {tok}, which the reader cannot look up: {s}"
  judge "message" d.message
  if d.message.startsWith "\\" then
    fail s!"{d.code} message: the construct it names is unquoted: {d.message}"
  unless d.message.length ≤ dvMsgMax do
    fail s!"{d.code} message: {d.message.length} chars, over {dvMsgMax}: {d.message}"
  if let some h := d.help then
    judge "help" h
    unless dvHasAction h do
      fail s!"{d.code} help: no action — nothing to write, no flag, no known values: {h}"
    unless h.length ≤ dvHelpMax do
      fail s!"{d.code} help: {h.length} chars, over {dvHelpMax}: {h}"

/-- The voice golden and its coverage: every registered code fires from its
witness, and every fired form renders into tests/golden/diagnostics.txt —
the one place the whole voice is reviewable in a diff. Spans are dropped:
the witnesses' line numbers are noise. -/
def diagVoiceChecks (ref : IO.Ref (List String)) (update : Bool) : IO Unit := do
  let load (name : String) : IO (Option Font.Font) := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure (some f)
    | .error _ => pure none
  let some sans ← load "OpenSans-Regular.ttf"
    | failures ref "diag voice: OpenSans-Regular.ttf missing"; return
  let some code ← load "SourceCodePro-Regular.otf"
    | failures ref "diag voice: SourceCodePro-Regular.otf missing"; return
  let allVariants (slot idx : Nat) : List ((Nat × Bool × Bool) × Nat) :=
    [((slot, false, false), idx), ((slot, true, false), idx),
     ((slot, false, true), idx), ((slot, true, true), idx)]
  let one : Font.FontSet := {
    fonts := #[sans]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let mapped : Font.FontSet := {
    fonts := #[sans, code]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 1).toArray
    fallback := #[('\u2200', 1)] }
  let lossLabel : Loss → String
    | .dropped => "dropped"
    | .pending => "pending"
    | .degraded => "degraded"
    | .config => "config"
    | .info => "info"
  let mut out := ""
  for c in DiagCode.all do
    let fired := (diagWitness one mapped c).filter (·.code == c.code)
    check ref s!"diag voice {c.code}: the witness fires it" (!fired.isEmpty)
    -- The registry meaning is prose too: self-contained, one convention.
    if dvInternalRef c.meaning then
      failures ref s!"diag voice {c.code} meaning: repo-internal reference: {c.meaning}"
    unless dvTerminalOk c.meaning do
      failures ref s!"diag voice {c.code} meaning: terminal punctuation: {c.meaning}"
    out := out ++ s!"── {c.code} ({lossLabel c.loss}) {c.meaning}\n"
    let mut seen : Array String := #[]
    for d in fired do
      dvLint (fun m => failures ref s!"diag voice {m}") d
      let r := Render.human false { d with span := none }
      unless seen.contains r do
        seen := seen.push r
        out := out ++ r ++ "\n"
  let path := "tests/golden/diagnostics.txt"
  if update then
    IO.FS.writeFile path out
    IO.println s!"updated {path}"
  else
    let golden ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
    match golden with
    | none => failures ref s!"diag voice: missing {path} (run: lake exe Tests --update)"
    | some g =>
      unless g == out do
        failures ref s!"diag voice: golden mismatch, {firstDiff g out} \
(if intended, run: lake exe Tests --update)"

/-- Tables and floats: the too-wide diagnostic, the caption's source side,
and the rule extents on the shipped page — a rule claim is judged from
`Layout.Out`, never the IR dump. Its own function: `main`'s do block has no
elaboration budget left. -/
def tableChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrap (tab : String) : String :=
    "\\documentclass{article}\n\\begin{document}\n" ++ tab ++ "\n\\end{document}"
  let layoutDiags (src : String) : Array Diag :=
    let doc := (elabStr src).1
    (Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc).diags
  t "a table wider than the measure is named, in points"
    ((layoutDiags (wrap "\\begin{tabular}{p{0.8\\linewidth}p{0.8\\linewidth}}a & b \\\\\\end{tabular}")).any
      (·.code == "W0338"))
  t "a fitting table is not named"
    (!(layoutDiags (wrap "\\begin{tabular}{ll}a & b \\\\\\end{tabular}")).any
      (·.code == "W0338"))
  t "a caption written above its table stands above"
    (match (elabStr (wrap "\\begin{table}\\caption{Above}\\begin{tabular}{l}a\\\\\\end{tabular}\\end{table}")).1.body with
     | #[.float .table true _ cap] => Ir.plainText cap == "Above"
     | _ => false)
  t "a caption written below its table stands below"
    (match (elabStr (wrap "\\begin{table}\\begin{tabular}{l}a\\\\\\end{tabular}\\caption{Below}\\end{table}")).1.body with
     | #[.float .table false _ cap] => Ir.plainText cap == "Below"
     | _ => false)
  -- The caption seam: nothing keeps a float and its caption on one page
  -- yet, so the break is reported (W0339, pending), never silent. The
  -- `\vspace` sweep parks the object at every position around the page
  -- bottom in 3pt steps: the seam-break window is about one leading tall,
  -- so some step lands the object on the page with the caption past it,
  -- whatever the face's metrics — and a small vspace leaves room for both.
  let tieDoc (pts : Nat) : String :=
    "\\documentclass{article}\n\\page{ size = a5 }\n\\begin{document}\n" ++
    s!"top\n\n\\vspace\{{pts}pt}\n\n\\begin\{table}\n" ++
    "\\begin{tabular}{l}\nalpha \\\\\n\\end{tabular}\n" ++
    "\\caption{Below the table}\n\\end{table}\n\\end{document}"
  t "a page break through the caption seam is named"
    ((List.range 50).any fun k =>
      (layoutDiags (tieDoc (350 + 3 * k))).any (·.code == "W0339"))
  t "a float that fits keeps its caption silently"
    (!(layoutDiags (tieDoc 12)).any (·.code == "W0339"))
  -- Rules span exactly their columns, judged on the page: the full rules
  -- share one left edge and one width; the trimmed \cmidrule lies strictly
  -- inside them. An executable check, not a theorem — the extents live in
  -- `collectTable`'s local arithmetic.
  let doc := (elabStr (wrap ("\\begin{tabular}{ll}\\toprule\na & b \\\\ \\cmidrule(lr){2-2}\nc & d \\\\ \\bottomrule\\end{tabular}"))).1
  let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
  let ruleSegs : Array (Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .rule w _ _ _ =>
            acc := acc.push (x, w)
            x := x + w
          | .gap g => x := x + g
          | .run _ _ _ w _ _ _ _ => x := x + w
          | .image _ w _ => x := x + w
    return acc
  t "the three rules ship" (ruleSegs.size == 3)
  t "toprule and bottomrule span the same extent"
    ((ruleSegs[0]?).isSome && ruleSegs[0]? == ruleSegs[2]?)
  t "the trimmed cmidrule lies strictly inside the full rules"
    (match ruleSegs[0]?, ruleSegs[1]? with
     | some (fx, fw), some (cx, cw) => decide (fx < cx && cx + cw < fx + fw)
     | _, _ => false)

/-- Frames as first-class blocks: the elaboration shape, the title forms,
the title frame, and the page-per-frame contract in layout. Its own
function: `main`'s do block has no elaboration budget left. -/
def slideChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++ body ++
    "\n\\end{document}"
  let (fDoc, fDs) := elabStr (deck "\\begin{frame}{T}\nbody\n\\end{frame}")
  t "frame source clean" fDs.isEmpty
  t "frame is first-class with its title"
    (fDoc.body == #[.frame #[.text "T"] false .center #[.para #[.text "body"]]])
  -- A group after a paragraph break is content, not a title: LaTeX's own
  -- argument scanning stops looking there too.
  t "frame title after a blank line is content"
    ((elabStr (deck "\\begin{frame}[plain]\n\n{scope group}\n\\end{frame}")).1.body ==
      #[.frame #[] false .center #[.para #[.text "scope group"]]])
  -- Options that say how beamer should cope (fragile, plain) are ignored
  -- with a registered note, never silently.
  t "an unmodelled frame option is a note"
    ((elabStr (deck "\\begin{frame}[fragile]{T}\nbody\n\\end{frame}")).2.any
      fun d => d.code == "N0102" && d.severity == .note)
  t "frametitle names the frame"
    ((elabStr (deck "\\begin{frame}\n\\frametitle{Named}\nbody\n\\end{frame}")).1.body ==
      #[.frame #[.text "Named"] false .center #[.para #[.text "body"]]])
  -- Two titles: the last wins, as in beamer, but never silently.
  let (dupDoc, dupDs) := elabStr
    (deck "\\begin{frame}\n\\frametitle{One}\n\\frametitle{Two}\nbody\n\\end{frame}")
  t "a second frametitle warns and wins"
    (dupDs.any (·.code == "W0311") &&
     match dupDoc.body with
     | #[.frame title _ _ _] => Ir.plainText title == "Two"
     | _ => false)
  -- \title and friends may sit in the body, as beamer documents do; an
  -- empty declaration (\date{}) is deliberately blank and sets nothing.
  let titled := deck ("\\title{A Deck}\\subtitle{Sub}\\author{Pat Placeholder}\\date{}\n" ++
    "\\maketitle\n\\begin{frame}{One}\nx\n\\end{frame}")
  let (tDoc, tDs) := elabStr titled
  t "maketitle source clean" tDs.isEmpty
  t "maketitle is a centered title frame with the empty date dropped"
    (match tDoc.body[0]? with
     | some (Ir.Block.frame title _ _ #[.center inner]) => title.isEmpty && inner.size == 3
     | _ => false)
  t "pdf metadata falls back to the title declarations"
    (tDoc.info.title == some "A Deck" && tDoc.info.author == some "Pat Placeholder")
  t "slides default to the 16:9 stage"
    (tDoc.page.width == Dim.mm 160 && tDoc.page.height == Dim.mm 90)
  t "slides without the option are 4:3"
    ((elabStr "\\documentclass{slides}\\begin{document}x\\end{document}").1.page.width ==
      Dim.mm 128)
  t "a declared page beats the stage"
    ((elabStr ("\\documentclass{slides}\\page{ width = 300pt, height = 200pt }" ++
      "\\begin{document}x\\end{document}")).1.page.width == Dim.pt 300)
  t "article keeps its page" ((elabStr "x").1.page.width == Dim.pt 612)
  -- Layout: a frame is a page of the handout, a section its own divider
  -- page, and content never flattens into the neighbouring frame.
  let threeFrames := deck ("\\begin{frame}{A}\na\n\\end{frame}\n" ++
    "\\begin{frame}{B}\nb\n\\end{frame}\n\\section{S}\n\\begin{frame}{C}\nc\n\\end{frame}")
  let (dDoc, dDs) := elabStr threeFrames
  t "deck source clean" dDs.isEmpty
  let out := Layout.run (Layout.Geom.ofPage dDoc.page) oneFace none dDoc
  t "one page per frame, one per section divider" (out.pages.size == 4)
  t "every slide leads with its title at the heading size"
    (out.pages.all fun p =>
      p.lines.any (·.size == Layout.sectionSize (Layout.Geom.ofPage dDoc.page) 1))
  let (html, _) := HtmlDoc.emit {} dDoc
  t "html gives each frame its own slide section"
    ((html.splitOn "<section class=\"slide\"").length == 4)
  -- Math environments carry their source whole — elaborating `&` and `\\`
  -- as text would shred the alignment; tables degrade to rows of cells and
  -- `&` never reaches inline elaboration as a reserved-character error.
  t "align* is one display-math grid, cells and rows intact"
    (match (elabStr "\\begin{align*}1 &= 1 \\\\ 2 &= 4\\end{align*}").1.body with
     | #[.center #[.para #[.formula true src
         (.cons (.atom _ (.grid .align rows) _ _ _) .nil)]]] =>
       (src.splitOn "&").length == 3 &&
         rows.rows.map (·.length) == [2, 2]
     | _ => false)
  let tabSrc := "\\begin{tabular}{ll}a & b \\\\ c & d\\end{tabular}"
  t "tabular elaborates to a rectangular table without errors"
    (errCodes tabSrc == [] &&
     match (elabStr tabSrc).1.body with
     | #[.table cols true true rows #[]] =>
       cols == #[{ width := .natural, align := .left },
                 { width := .natural, align := .left }] &&
       rows.map (·.map Ir.plainText) == #[#["a", "b"], #["c", "d"]]
     | _ => false)
  -- The classic rules, not just booktabs: \hline is a light rule, \cline a
  -- full-width subrule, and \multicolumn keeps its cell text without the
  -- span count or alignment spec leaking in beside it.
  let classicTab := "\\begin{tabular}{ll}\\hline\n" ++
    "\\multicolumn{2}{X}{Head} \\\\ \\cline{1-2}\na & b \\\\ \\hline\\end{tabular}"
  let (ctDoc, ctDs) := elabStr classicTab
  t "classic tabular rules are typed rules, not unknown commands"
    (!ctDs.any (·.code == "W0301") &&
     match ctDoc.body with
     | #[.table _ _ _ _ rules] =>
       rules == #[(0, .mid), (1, .cmid 1 2 false false), (2, .mid)]
     | _ => false)
  t "multicolumn keeps only its cell text"
    (match ctDoc.body with
     | #[.table cols _ _ rows _] =>
       let s := String.join (rows.toList.map fun r =>
         String.join (r.toList.map Ir.plainText))
       -- the span is lost, the short row padded to the grid, and W0337 says so
       (s.splitOn "Head").length == 2 && !s.toList.contains '2' &&
         !s.toList.contains 'X' &&
         rows.all (·.size == cols.size) && ctDs.any (·.code == "W0337")
     | _ => false)
  -- [standout]: the one frame option that says what the frame IS. It
  -- inverts, centres, and sets Large bold in both backends; the other
  -- options stay ignored, as notes.
  t "standout option marks the frame"
    (match (elabStr (deck "\\begin{frame}[fragile,standout]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ true _ _] => true
     | _ => false)
  t "other frame options do not mark it"
    (match (elabStr (deck "\\begin{frame}[plain]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ false _ _] => true
     | _ => false)
  let (sDoc, _) := elabStr (deck ("\\begin{frame}{A}\na\n\\end{frame}\n" ++
    "\\begin{frame}[standout]\nQ\n\\end{frame}"))
  let sGeom := Layout.Geom.ofPage sDoc.page
  let sOut := Layout.run sGeom oneFace none sDoc
  t "standout page carries a full-page background fill"
    (match sOut.pages[1]? with
     | some p => p.fills.any fun f =>
         f.x == 0 && f.y == 0 && f.w == sGeom.pageW && f.h == sGeom.pageH &&
         f.color == Ir.Color.black
     | none => false)
  t "the plain page beside it carries none"
    (match sOut.pages[0]? with
     | some p => p.fills.isEmpty
     | none => false)
  t "standout text is inverted and Large"
    (match sOut.pages[1]? with
     | some p => p.lines.any fun l =>
         l.size == sGeom.fontSize * 1440 / 1000 &&
         l.segs.any fun s => match s with
           | .run _ c _ _ _ _ _ _ => c == Ir.Color.white
           | _ => false
     | none => false)
  t "standout content centres vertically"
    (match sOut.pages[1]?.bind (·.lines[0]?), sOut.pages[0]?.bind (·.lines[0]?) with
     | some sl, some pl => sl.y > pl.y + sGeom.pageH / 4
     | _, _ => false)
  let (sHtml, _) := HtmlDoc.emit {} sDoc
  t "html standout section carries the class"
    ((sHtml.splitOn "class=\"slide standout\"").length == 2)

/-- The paragraph boundary, judged from a body's shape: an unknown
environment follows the same rule as the `@input:` wrapper — an inline body
stays in its sentence, block content breaks it. -/
def envBoundaryChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "an inline unknown environment stays in its paragraph"
    (match (elabStr "A sentence with \\begin{highlight}x\\end{highlight} in the middle.").1.body with
     | #[.para xs] => Ir.plainText xs == "A sentence with x in the middle."
     | _ => false)
  t "an unknown environment holding block content is a boundary"
    ((elabStr "before\n\\begin{aside}one\n\ntwo\n\\end{aside}\nafter").1.body ==
      #[.para #[.text "before"], .para #[.text "one"], .para #[.text "two"],
        .para #[.text "after"]])
  -- bodyIsBlock mirrors the boundary rule: verbatim is a first-class block
  -- on this branch, so it is block inside a body too — degrading it to
  -- inline <code> loses the literal lines
  t "a verbatim inside an unknown environment stays a block"
    (match (elabStr
        "\\begin{gizmo}\n\\begin{verbatim}\nliteral line one\n\\end{verbatim}\n\\end{gizmo}").1.body with
     | #[.verbatim none s] => s.trimAscii.toString == "literal line one"
     | _ => false)
  -- ...and the judgment descends into scope groups: block content one
  -- group deeper is still block content
  t "block content one group deeper still makes a body block"
    ((elabStr "before\n\\begin{gizmo}\n{one \\par two}\n\\end{gizmo}\nafter").1.body ==
      #[.para #[.text "before"], .para #[.text "one"], .para #[.text "two"],
        .para #[.text "after"]])
  t "an inline unknown environment's begin-line argument goes with the wrapper"
    (match (elabStr "Take \\begin{banner}{Logo}the text\\end{banner} along.").1.body with
     | #[.para xs] => Ir.plainText xs == "Take the text along."
     | _ => false)
  -- W0302 says the body is kept; when begin-line groups go with the
  -- wrapper, a warning must say exactly what went (the diagnostic and the
  -- behaviour agree, or one of them is lying)
  t "dropped begin-line groups are named precisely, count included"
    (let ds := (elabStr "Two: \\begin{card}{First}{Second}kept body\\end{card} end.").2
     ds.any fun d => d.code == "E0336" && d.message.startsWith "2 ")
  t "the block path warns about dropped begin-line groups too"
    ((elabStr "\\begin{wrap}{arg}\none\n\ntwo\n\\end{wrap}").2.any (·.code == "E0336"))
  t "no dropped-argument warning without begin-line groups"
    (!(elabStr "Take \\begin{banner}the text\\end{banner} along.").2.any (·.code == "E0336"))
  -- A spliced body's edge space is a separator, not wrapper furniture:
  -- dropping it glued `before` to `inner`, and keeping it twice would
  -- double the gap the author wrote once.
  t "an inline unknown environment's edge spaces still separate words"
    (match (elabStr "Glue check:before\\begin{gizmo} inner \\end{gizmo}after done.").1.body with
     | #[.para xs] => Ir.plainText xs == "Glue check:before inner after done."
     | _ => false)
  t "splicing an unknown environment never doubles a space"
    (match (elabStr "before\n\\begin{gizmo}\ninner\n\\end{gizmo}\nafter").1.body with
     | #[.para xs] => Ir.plainText xs == "before inner after"
     | _ => false)
  t "a paragraph never opens with a spliced body's leading space"
    (match (elabStr "\\begin{gizmo} inner \\end{gizmo} rest.").1.body with
     | #[.para xs] => Ir.plainText xs == "inner rest."
     | _ => false)

/-- The optional-argument recovery, fed the malformed across line breaks:
an unclosed `[` never turns into a fatal error however the lines fall — the
group the author wrote is found on its own line or the next, a command with
no group left is skipped whole (W0312), and a construct sharing the typo's
line is never consumed with it. -/
def optArgChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \title: the group on the NEXT line is the argument too, never a fatal
  -- E0304 + E0313
  let titleNl := "\\title[short never closes\n{The Real Title}\n\\begin{document}x\\end{document}"
  let (tnDoc, tnDs) := elabStr titleNl
  t "title survives an unclosed bracket with its group on the next line"
    (tnDoc.info.title == some "The Real Title")
  t "an unclosed title bracket across lines is a warning, not E0313"
    (!tnDs.any (·.severity == .error) && tnDs.any (·.code == "W0310"))
  -- ...and with no group anywhere, the declaration is skipped whole (W0312)
  -- and the next declaration survives
  let titleSkip := "\\title[never closes\n\\author{A. Placeholder}\n\\begin{document}x\\end{document}"
  let (tsDoc, tsDs) := elabStr titleSkip
  t "a title with no group after its unclosed bracket is skipped, never fatal"
    (!tsDs.any (·.severity == .error) && tsDs.any (·.code == "W0312"))
  t "the declaration after a skipped title survives"
    (tsDoc.info.author == some "A. Placeholder")
  -- ...and a BLANK line between the typo and the group is one more line
  -- arrangement, not a fatal E0313: never fatal means never
  let titleBlank := "\\title[short never closes\n\n{The Real Title}\n\\begin{document}x\\end{document}"
  let (tbDoc, tbDs) := elabStr titleBlank
  t "title survives an unclosed bracket with a blank line before its group"
    (tbDoc.info.title == some "The Real Title")
  t "an unclosed title bracket across a blank line is never fatal"
    (!tbDs.any (·.severity == .error) && tbDs.any (·.code == "W0310"))
  -- \section[short]{long}: the fifth optional-argument site obeys the
  -- shared scanner instead of a fatal E0304
  let (secDoc, secDs) := elabStr "\\section[Short]{Long Title}\n\nBody."
  t "section takes its short form and keeps the long title"
    (secDs.all (·.severity == .note) && match secDoc.body with
     | #[.section 1 false title, .para _] => Ir.plainText title == "Long Title"
     | _ => false)
  -- The short title is unused today, and that is registered, never silent.
  t "an unused short title is a note" (secDs.any (·.code == "N0103"))
  t "section recovers its title past an unclosed bracket"
    (match (elabStr "\\section[never closes {Recovered}\nBody.").1.body with
     | #[.para _, .section 1 false title, .para _] => Ir.plainText title == "Recovered"
     | _ => false)
  -- Principle 8: the malformed run W0310 calls content IS content in a
  -- content position, exactly as in the scanner's two sibling paths
  t "the malformed run before a recovered section title stays content"
    (match (elabStr "\\section[never closes IMPORTANTWORDS {Recovered}\nBody.").1.body with
     | #[.para junk, .section 1 false title, .para _] =>
       (Ir.plainText junk).endsWith "IMPORTANTWORDS" && Ir.plainText title == "Recovered"
     | _ => false)
  t "a body title's malformed run stays content, the title still taken"
    (let (doc, ds) := elabStr "\\title[junk words {Kept Title}\n\\maketitle"
     !ds.any (·.severity == .error) &&
       (match doc.body with
        | #[.para junk, .center _] => (Ir.plainText junk).endsWith "junk words"
        | _ => false))
  t "a section with no group after its unclosed bracket warns, never fatally"
    (let ds := (elabStr "\\section[never closes\nBody.").2
     !ds.any (·.severity == .error) && ds.any (·.code == "W0312"))

/-- The shared bracket scanner, fed the malformed and the merely leading:
an unclosed `[` is content, never an argument that consumes to the end of
its scan, and a bracket on a later line than its command is content too.
Each case here lost text silently — a frame body, a preamble declaration,
a title — when four copies of the scan disagreed about the guard. -/
def scannerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n\\begin{document}\n" ++ body ++
    "\n\\end{document}"
  let blockText (b : Ir.Block) : String :=
    match b with
    | .para xs => Ir.plainText xs
    | _ => ""
  -- an unclosed bracket must not consume the frame body
  let (fDoc, fDs) := elabStr (deck "\\begin{frame}[unclosed\nBody survives.\n\\end{frame}")
  t "unclosed bracket keeps the frame body"
    (match fDoc.body with
     | #[.frame _ _ _ body] => body.any fun b => (blockText b).endsWith "Body survives."
     | _ => false)
  t "unclosed bracket in a frame warns" (fDs.any (·.code == "W0310"))
  -- a bracket opening the frame's content is content, not an option
  t "frame content starting with a bracket survives"
    (match (elabStr (deck "\\begin{frame}\n[1] Reference survives.\n\\end{frame}")).1.body with
     | #[.frame _ _ _ #[.para xs]] => Ir.plainText xs == "[1] Reference survives."
     | _ => false)
  -- options on the begin line are still arguments, bracket runs included
  t "frame options on the begin line are consumed, never content"
    (match (elabStr (deck "\\begin{frame}[plain][t]{T}\nbody\n\\end{frame}")).1.body with
     | #[.frame title _ _ #[.para xs]] =>
       Ir.plainText title == "T" && Ir.plainText xs == "body"
     | _ => false)
  -- unknown environment: unclosed bracket keeps the body, later-line bracket is content
  let (uDoc, uDs) := elabStr "\\begin{mywrap}[unclosed\nkept body\n\\end{mywrap}"
  t "unclosed bracket keeps an unknown environment's body"
    (uDoc.body.any fun b => (blockText b).endsWith "kept body")
  t "unclosed bracket in an unknown environment warns" (uDs.any (·.code == "W0310"))
  t "unknown environment content starting with a bracket survives"
    (match (elabStr "\\begin{mywrap}\n[1] first line\nkept\n\\end{mywrap}").1.body with
     | #[.para xs] => Ir.plainText xs == "[1] first line kept"
     | _ => false)
  -- \title: the title survives its own malformed optional argument
  let titleSrc := "\\title[short never closes {The Real Title}\n\\begin{document}x\\end{document}"
  let (tDoc, tDs) := elabStr titleSrc
  t "title survives an unclosed optional argument"
    (tDoc.info.title == some "The Real Title")
  t "an unclosed title bracket is a warning, not E0313"
    (!tDs.any (·.severity == .error) && tDs.any (·.code == "W0310"))
  -- unknown preamble command: the next line's declaration must survive
  let preSrc := "\\unknowncmd[opts that never close\n\\palette{ accent = #ff0000 }\n" ++
    "\\begin{document}\\textcolor{accent}{x}\\end{document}"
  let (pDoc, pDs) := elabStr preSrc
  t "unclosed bracket does not eat the next preamble declaration"
    (pDoc.palette.find? "accent" |>.isSome)
  t "the swallowed palette warning is gone"
    (!pDs.any (·.code == "W0304") && !pDs.any (·.severity == .error))
  -- ...and a declaration SHARING the malformed command's line survives too
  let preSame := "\\unknowncmd[never closes \\palette{ accent = #00ff00 }\n" ++
    "\\begin{document}\\textcolor{accent}{x}\\end{document}"
  let (psDoc, psDs) := elabStr preSame
  t "unclosed bracket does not eat a declaration on its own line"
    (psDoc.palette.find? "accent" |>.isSome)
  t "no misdirecting palette warning for the shared line"
    (!psDs.any (·.code == "W0304") && !psDs.any (·.severity == .error))
  t "unclosed bracket does not eat the document on its own line"
    (match (elabStr "\\unknowncmd[junk \\begin{document}Body survives.\\end{document}").1.body with
     | #[.para xs] => Ir.plainText xs == "Body survives."
     | _ => false)
  -- reserved inline command: the sentence after the bracket survives
  t "unclosed bracket after a reserved command keeps the text"
    (match (elabStr "\\figure[unclosed and text continues").1.body with
     | #[.para xs] => (Ir.plainText xs).endsWith "and text continues"
     | _ => false)
  -- a reserved command's bracket on a later line is content
  t "bracket on the line after a reserved command is content"
    (match (elabStr "\\figure\n[1] a caption line").1.body with
     | #[.para xs] => Ir.plainText xs == "[1] a caption line"
     | _ => false)
  optArgChecks ref
  envBoundaryChecks ref

def utf8Checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- utf8: valid inputs
  t "utf8 empty" (validate (bytes []) == none)
  t "utf8 ascii" (validate "hello, world".toUTF8 == none)
  t "utf8 multibyte" (validate "naïve — αβγ — 🎉".toUTF8 == none)

  -- utf8: each error class, with offset
  t "utf8 bare continuation" (errKindAt (bytes [0x68, 0x80]) == some (1, .invalidStart 0x80))
  t "utf8 overlong 2-byte" (errKindAt (bytes [0xC0, 0x80]) == some (0, .overlong))
  t "utf8 overlong 3-byte" (errKindAt (bytes [0xE0, 0x9F, 0x80]) == some (0, .overlong))
  t "utf8 overlong 4-byte" (errKindAt (bytes [0xF0, 0x8F, 0x80, 0x80]) == some (0, .overlong))
  t "utf8 surrogate" (errKindAt (bytes [0xED, 0xA0, 0x80]) == some (0, .surrogate))
  t "utf8 out of range" (errKindAt (bytes [0xF4, 0x90, 0x80, 0x80]) == some (0, .outOfRange))
  t "utf8 truncated" (errKindAt (bytes [0x61, 0xC3]) == some (1, .truncated))
  t "utf8 bad continuation" (errKindAt (bytes [0xC3, 0x28]) == some (0, .invalidContinuation 0x28))

  -- utf8: error position tracks lines and columns
  let afterNewlines := bytes ("ab\ncd\n".toUTF8.toList ++ [0xFF])
  t "utf8 position" ((validate afterNewlines).map (fun e => (e.pos.line, e.pos.col)) == some (3, 1))

  -- utf8: agreement with core decoder on every vector above
  for (name, v) in [
      ("empty", bytes []), ("ascii", "hello".toUTF8), ("multi", "🎉é".toUTF8),
      ("cont", bytes [0x80]), ("overlong", bytes [0xC0, 0x80]),
      ("surrogate", bytes [0xED, 0xA0, 0x80]),
      ("range", bytes [0xF4, 0x90, 0x80, 0x80]), ("trunc", bytes [0xC3])] do
    t s!"utf8 agrees with core ({name})"
      ((validate v == none) == (String.fromUTF8? v).isSome)
  utf8FuzzChecks ref

def argsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- args
  t "args empty is help" (parse [] == .ok { cmd := .help })
  t "args build" (parse ["build", "a.tex"] == .ok { cmd := .build "a.tex" })
  t "args verbosity accumulates" (parse ["-v", "-vv", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", verbosity := 3 })
  t "args verbosity clamps" ((parse ["-vvvvv", "build", "a.tex"]).map (·.verbosity) == .ok 3)
  t "args porcelain quiet" (parse ["--porcelain", "-q", "build", "a.tex"] ==
    .ok { cmd := .build "a.tex", quiet := true, porcelain := true })
  t "args color eq" ((parse ["--color=never", "build", "a.tex"]).map (·.color) == .ok .never)
  t "args color sep" ((parse ["--color", "always", "version"]).map (·.color) == .ok .always)
  t "args color bad" ((parse ["--color=sometimes"]).isOk == false)
  t "args q v conflict" ((parse ["-q", "-v", "build", "a.tex"]).isOk == false)
  t "args unknown flag" ((parse ["--frobnicate"]).isOk == false)
  t "args build missing file" ((parse ["build"]).isOk == false)
  t "args trailing junk" ((parse ["build", "a.tex", "b.tex"]).isOk == false)
  t "args help flag wins" ((parse ["--help", "build", "a.tex"]).map (·.cmd) == .ok .help)
  -- Flags belong after the command too: a command takes the next positional,
  -- not the next token, or every flag written where people write it is eaten
  -- as the filename.
  t "args flag after command" (parse ["build", "--color", "never", "a.tex"] ==
    .ok { cmd := .build "a.tex", color := .never })
  t "args emit default is pdf"
    ((parse ["build", "a.tex"]).map (·.effectiveEmit #[]) == .ok #[.pdf])
  t "args css default is own" (cssFor none == .own)
  t "args math boundary"
    ((parse ["build", "--math-boundary", "katex", "a.tex"]).map (·.mathBoundary) ==
      .ok (some "katex"))
  -- The removed artifact-shaping flags fail as usage, and the message names
  -- the declaration that replaces each: a human under time pressure gets
  -- the spelling to paste, not just a refusal.
  let removed (argv : List String) (declKey : String) : Bool :=
    match parse argv with
    | .error m => (m.splitOn "\\output{").length ≥ 2 && (m.splitOn declKey).length ≥ 2
    | .ok _ => false
  t "args --css is usage error naming the declaration"
    (removed ["build", "--css", "bulma", "a.tex"] "css =")
  t "args --css= is usage error naming the declaration"
    (removed ["a.tex", "--css=bulma"] "css =")
  t "args --emit is usage error naming the declaration"
    (removed ["build", "--emit", "pdf,html", "a.tex"] "formats =")
  t "args --emit= is usage error naming the declaration"
    (removed ["a.tex", "--emit=html"] "formats =")
  -- args: the file is the command; the output name chooses the backend
  t "args file is the command" (parse ["a.tex"] == .ok { cmd := .build "a.tex" })
  t "args md reserved for markdown" (parse ["notes.md"] == .ok { cmd := .build "notes.md" })
  t "args flags after the file" (parse ["a.tex", "--color", "never"] ==
    .ok { cmd := .build "a.tex", color := .never })
  t "args non-document positional" ((parse ["nonsense.txt"]).isOk == false)
  t "args output flag" ((parse ["a.tex", "-o", "out.html"]).map (·.output) ==
    .ok (some "out.html"))
  t "args output infers html" ((parse ["a.tex", "-o", "out.html"]).map
    (·.effectiveEmit #[]) == .ok #[.html])
  t "args output infers pdf" ((parse ["a.tex", "-o", "b/x.pdf"]).map
    (·.effectiveEmit #[]) == .ok #[.pdf])
  t "args document formats apply" ((parse ["a.tex"]).map (·.effectiveEmit #["html"]) ==
    .ok #[.html])
  t "args output name beats document formats" ((parse ["a.tex", "-o", "out.pdf"]).map
    (·.effectiveEmit #["html"]) == .ok #[.pdf])
  t "args document css applies" (cssFor (some "bulma") == .bulma)
  t "args unknown document css falls back to own" (cssFor (some "tailwind") == .own)
  t "args output dir keeps stem" (outPath (some "out/") false "doc.tex" .pdf == "out/doc.pdf")
  t "args output other backend beside source"
    (outPath (some "out.html") false "doc.tex" .pdf == "doc.pdf")
  t "args watch" ((parse ["a.tex", "--watch"]).map (·.watch) == .ok true)

/-- The `\allow` escape hatch: declared acceptance of named losses, with its
three teeth — an unknown code is an error, a never-fired entry warns
(`Diag.unfired`, applied in the driver), and the acceptance prints. -/
def allowChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (pre : String) : String :=
    pre ++ "\n\\begin{document}\nx\n\\end{document}"
  t "allow stores its codes on the document"
    ((elabStr (doc "\\allow{W0307, E0502}")).1.allow == #["W0307", "E0502"])
  t "allow dedupes a repeated code"
    ((elabStr (doc "\\allow{W0307}\\allow{W0307}")).1.allow == #["W0307"])
  t "allow with an unknown code is an error"
    (errCodes (doc "\\allow{W9999}") == ["E0329"])
  t "allow dumps as a declaration"
    (((Ir.dump (elabStr (doc "\\allow{W0307}")).1 #[]).splitOn "allow W0307").length == 2)
  -- The total function severity resolution is: an allowed error or warning
  -- becomes a note — a declared document emits nothing at default
  -- verbosity — and the acceptance summary is what keeps it visible.
  let e := Diag.of .E0501 "gone"
  let w := Diag.of .W0338 "wide"
  t "accept downgrades an allowed error to a note, changing nothing else"
    (let (d, acc) := Diag.accept #["E0501"] false e
     acc && d.severity == .note && d.code == e.code && d.message == e.message
       && d.span == e.span && d.help == e.help)
  t "accept downgrades an allowed warning to a note"
    (let (d, acc) := Diag.accept #["W0338"] false w
     acc && d.severity == .note && d.code == w.code)
  t "accept leaves an unallowed error alone"
    (Diag.accept #["W0307"] false e == (e, false))
  t "accept leaves an unallowed warning alone"
    (Diag.accept #["E0501"] false w == (w, false))
  t "best-effort accepts every error and warning"
    (let (de, accE) := Diag.accept #[] true e
     let (dw, accW) := Diag.accept #[] true w
     accE && de.severity == .note && accW && dw.severity == .note)
  t "accept never touches a note"
    (let n := Diag.of .N0100 "idiom"
     Diag.accept #["N0100"] true n == (n, false))
  t "unfired names the stale entries only"
    (Diag.unfired #["W0307", "W0338"] #["W0338", "W0338"] == #["W0307"])
  t "accepted losses line prints codes with counts"
    (Render.humanAccepted false [("W0307", 2), ("E0502", 1)] ==
      "accepted: 3 losses (W0307 ×2, E0502)")

/-- The `--werror` exit-code matrix, over the same functions the driver
runs: diagnostics from a real elaboration are resolved against the
document's own `\allow`, and `exitFor` reads the counts. The contract:
errors are 1, failed assertions 2, and a warning is 1 only under the flag —
where an accepted loss is not a warning, which is the whole point of
accepting it. -/
def werrorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "args --werror parses" ((parse ["a.tex", "--werror"]).map (·.werror) == .ok true)
  t "args werror defaults off" ((parse ["a.tex"]).map (·.werror) == .ok false)
  let resolve (src : String) : Resolution :=
    let (doc, ds) := elabStr src
    Diag.resolveAll doc.allow false ds
  let clean := resolve "\\begin{document}\nx\n\\end{document}"
  let warned := resolve "\\sloppy\n\\begin{document}\nx\n\\end{document}"
  let allowed := resolve "\\allow{W0104}\n\\sloppy\n\\begin{document}\nx\n\\end{document}"
  t "matrix: clean document is 0 without the flag"
    (exitFor clean.errors 0 clean.warnings false == 0)
  t "matrix: clean document is 0 with the flag"
    (clean.warnings == 0 && exitFor clean.errors 0 clean.warnings true == 0)
  t "matrix: a warning is 0 without the flag"
    (warned.warnings > 0 && exitFor warned.errors 0 warned.warnings false == 0)
  t "matrix: a warning is 1 with the flag"
    (exitFor warned.errors 0 warned.warnings true == 1)
  t "matrix: an allowed loss is 0 without the flag"
    (exitFor allowed.errors 0 allowed.warnings false == 0)
  t "matrix: an allowed loss is 0 with the flag — acceptance composes"
    (allowed.warnings == 0 && allowed.accepted == #["W0104"] &&
      exitFor allowed.errors 0 allowed.warnings true == 0)
  t "matrix: an error is 1 whatever the flag"
    (exitFor 1 0 0 false == 1 && exitFor 1 0 0 true == 1)
  t "matrix: a failed assertion is 2, warnings or not"
    (exitFor 0 1 3 true == 2 && exitFor 0 1 0 false == 2)
  t "werror verdict line names the count and the flag"
    (Render.humanWerror false "a.tex" 3 17 == "✖ a.tex — 3 warnings (--werror) (17 ms)")
  t "werror porcelain summary is not ok and counts warnings"
    (Render.porcelainWerror "a.tex" 3 17 ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":0," ++
      "\"warnings\":3,\"ms\":17}")

def renderChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- render: porcelain is stable, escaped JSONL
  let d : Diag := Diag.of .E0002 "bad \"quote\"\nline" (some ⟨"a.tex", ⟨3, 7⟩⟩)
    (help := "fix it")
  t "porcelain diag" (Render.porcelainDiag d ==
    "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0002\"," ++
    "\"message\":\"bad \\\"quote\\\"\\nline\",\"file\":\"a.tex\",\"line\":3,\"col\":7," ++
    "\"help\":\"fix it\"}")
  t "porcelain summary" (Render.porcelainSummary "a.tex" false 2 17 ==
    "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":2,\"ms\":17}")

  -- render: human, no color
  t "human diag plain" (Render.human false d ==
    "error[E0002]: bad \"quote\"\nline\n  --> a.tex:3:7\n  help: fix it")

def lexChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- lex
  t "lex words and space" (toks "ab cd" == [.word "ab", .space, .word "cd"])
  t "lex par" (toks "a\n\nb" == [.word "a", .par, .word "b"])
  t "lex newline is space" (toks "a\nb" == [.word "a", .space, .word "b"])
  t "lex comment joins lines" (toks "a%c\nb" == [.word "a", .word "b"])
  t "lex ctrl word swallows space" (toks "\\emph  x" == [.ctrl "emph", .word "x"])
  t "lex ctrl word keeps blank line" (toks "\\par\n\nx" == [.ctrl "par", .par, .word "x"])
  t "lex ctrl symbol" (toks "\\%x" == [.ctrl "%", .word "x"])
  t "lex specials" (toks "{a}$m$[o]" ==
    [.lbrace, .word "a", .rbrace, .math, .word "m", .math, .sym '[', .word "o", .sym ']'])
  t "lex unicode word" (toks "naïve" == [.word "naïve"])
  t "lex position" (((Lex.lex "t" "a\nbé c").1.map fun tk => (tk.pos.line, tk.pos.col)).toList ==
    [(1, 1), (1, 2), (2, 1), (2, 3), (2, 4)])

def parseChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- parse
  let praw (s : String) : Array Parse.Raw × Array Diag :=
    let (tk, _) := Lex.lex "t" s
    Parse.parse "t" tk
  t "parse group nesting" (((praw "{a{b}}").1.map fun r =>
    match r with
    | .group body _ => s!"group/{body.size}"
    | _ => "?") == #["group/2"])
  t "parse unclosed group" (((praw "{a").2.map (·.code)) == #["E0201"])
  t "parse stray rbrace" (((praw "a}b").2.map (·.code)) == #["E0202"])
  t "parse env" (((praw "\\begin{itemize}\\item a\\end{itemize}").1.map fun r =>
    match r with
    | .env n body _ => s!"env {n}/{body.size}"
    | _ => "?") == #["env itemize/2"])
  t "parse env mismatch" (((praw "\\begin{a}x\\end{b}").2.map (·.code)) == #["E0205"])
  t "parse display math" (((praw "\\[x\\]").1.map fun r =>
    match r with
    | .math true _ _ => "display"
    | _ => "?") == #["display"])

def elabDocChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- elab: clean documents
  let (doc1, d1) := elabStr "hello $x$ world"
  t "elab snippet clean" (d1.isEmpty && doc1.body ==
    #[.para #[.text "hello ",
      .formula false "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil),
      .text " world"]])
  let (doc2, d2) := elabStr "\\textbf{a} {\\itshape b c} d"
  t "elab styles" (d2.isEmpty && doc2.body ==
    #[.para #[.styled .bold #[.text "a"], .text " ", .styled .italic #[.text "b c"], .text " d"]])
  let (doc3, d3) := elabStr "a\n\nb"
  t "elab paragraphs split" (d3.isEmpty && doc3.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  let (doc4, d4) := elabStr "\\section*{Work}\ntext"
  t "elab section star" (d4.isEmpty && doc4.body ==
    #[.section 1 true #[.text "Work"], .para #[.text "text"]])
  let (doc5, d5) := elabStr "\\begin{itemize}\\item a\\item b\\end{itemize}"
  t "elab itemize" (d5.isEmpty && doc5.body ==
    #[.list false #[#[.para #[.text "a"]], #[.para #[.text "b"]]]])
  let (doc6, d6) := elabStr "\\documentclass[x=1]{article}\n\\begin{document}\nhi\n\\end{document}"
  t "elab documentclass" (d6.isEmpty && doc6.docClass == "article" && doc6.classOptions == "x=1")
  let (doc9, d9) := elabStr
    "\\output{ formats = pdf, html, css = bulma }\n\\begin{document}x\\end{document}"
  t "elab output declaration" (d9.isEmpty && doc9.output.formats == #["pdf", "html"] &&
    doc9.output.css == some "bulma")
  t "elab output bad format" (errCodes
    "\\output{ formats = ps }\n\\begin{document}x\\end{document}" == ["E0321"])
  t "elab output unknown key" (errCodes
    "\\output{ paper = a4 }\n\\begin{document}x\\end{document}" == ["E0322"])

  -- elab: define and call
  let defRole := "\\documentclass{article}\n" ++
    "\\define \\role(who: text, team?: text) {\\textbf{\\who}\\ifgiven{\\team}{ (\\team)}}\n" ++
    "\\begin{document}\n"
  let (doc7, d7) := elabStr (defRole ++ "\\role{Ada}[Compute]\n\\end{document}")
  t "elab define call optional given" (d7.isEmpty && doc7.body ==
    #[.para #[.role "role" #[.styled .bold #[.text "Ada"], .text " (Compute)"]]])
  let (doc8, d8) := elabStr (defRole ++ "\\role{Ada}\n\\end{document}")
  t "elab define call optional omitted" (d8.isEmpty && doc8.body ==
    #[.para #[.role "role" #[.styled .bold #[.text "Ada"]]]])
  t "elab define text param rejects math" (errCodes (defRole ++ "\\role{$x$}\n\\end{document}") ==
    ["E0305"])
  t "elab self reference is unknown" (warnCodes
    ("\\define \\x() {\\x}\n\\begin{document}\\x\\end{document}") == ["W0301"])
  t "elab forward reference is unknown" (warnCodes
    ("\\define \\a() {\\b}\n\\define \\b() {y}\n\\begin{document}\\a\\end{document}") == ["W0301"])
  t "elab later definition sees earlier" (errCodes
    ("\\define \\b() {y}\n\\define \\a() {\\b}\n\\begin{document}\\a\\end{document}") == [])

  -- elab: diagnostics
  -- The non-blocking contract: an unknown command is a warning, its
  -- arguments are content, and content is never dropped for want of a command.
  t "elab unknown command warns" (warnCodes "\\frobnicate" == ["W0301"])
  t "elab unknown command keeps its arguments"
    ((elabStr "a \\frobnicate{kept}{too} b").1.body ==
      #[.para #[.text "a kept too b"]])
  t "elab unknown command warns once per name"
    ((warnCodes "\\zip{a} \\zip{b} \\zap{c}").length == 2)
  -- The warn-once keys are namespaced: an environment and a command sharing
  -- one name are two different unknown constructs, and neither may silence
  -- the other's warning.
  t "an environment and a command of one name both warn"
    ((warnCodes "\\begin{gizmo}body\\end{gizmo}\n\\gizmo{arg}").toArray ==
      #["W0302", "W0301"])
  -- A reserved command whose skipped arguments carry content loses that
  -- content -- but the construct is one a milestone owns, so the loss is
  -- `pending`: reported, and the rest of the document still renders. A
  -- document that wants the strict reading asks for it (`--werror`) rather
  -- than having every planned gap refuse to emit a page.
  t "elab reserved command dropping planned content warns" (warnCodes ("\\documentclass{article}\\figure{x}" ++
    "\\begin{document}y\\end{document}") == ["W0307"])
  t "elab reserved command dropping planned content still renders"
    ((elabStr ("\\documentclass{article}\\figure{x}" ++
      "\\begin{document}y\\end{document}")).1.body == #[.para #[.text "y"]])
  t "elab reserved layout-only command warns" (warnCodes ("\\documentclass{article}\\fontfallback{x}" ++
    "\\begin{document}y\\end{document}") == ["W0329"])
  -- Unknown environments keep their body: the wrapper's decoration is
  -- unknowable, the content inside it is not. Arguments on the \begin line
  -- go with the wrapper; a group on a later line is content.
  t "elab unknown environment keeps its body"
    ((elabStr "\\begin{wrap}{arg}\nkept\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab unknown environment warns once per name"
    ((warnCodes "\\begin{w}a\\end{w}\\begin{w}b\\end{w}") == ["W0302"])
  t "elab unknown environment keeps a group on a later line"
    ((elabStr "\\begin{wrap}\n{kept}\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab reserved environment content dropped is one pending warning"
    (warnCodes "\\begin{external}x\\end{external}" == ["W0307"] &&
     (elabStr "\\begin{external}x\\end{external}").1.body == #[])
  -- The tikz subset narrowed W0307: a picture is elaborated, and what it
  -- cannot render is named per construct instead of dropped whole.
  t "elab tikzpicture no longer earns the blanket W0307"
    (warnCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["W0334"])
  t "elab reserved char" (errCodes "a & b" == ["E0311"])
  t "elab redefine builtin warns and keeps the built-in"
    (warnCodes "\\define \\textbf() {x}\n\\begin{document}y\\end{document}" == ["W0303"])
  -- ...except a text symbol, whose name a document may want for itself.
  let (degDoc, degDs) := elabStr
    "\\define \\degree(a: text) {\\textbf{\\a}}\n\\begin{document}\\degree{PhD}\\end{document}"
  t "elab user definition shadows a symbol"
    (degDs.isEmpty && degDoc.body ==
      #[.para #[.role "degree" #[.styled .bold #[.text "PhD"]]]])
  t "elab trailing content warns" (((elabStr
    "\\begin{document}x\\end{document} y").2.map (·.code)) == #["W0001"])

  -- The synthetic \input wrapper carries provenance, and must not invent
  -- structure the file does not have: an inline fragment stays in its
  -- paragraph; a file with paragraph breaks is block content.
  let ip : Pos := {}
  let inlineInput : Array Parse.Raw :=
    #[.word "A" ip, .space,
      .env (Parse.inputEnv "sub.tex") #[.word "with" ip, .space, .word "words" ip] ip,
      .space, .word "B" ip]
  t "inline input does not split its paragraph"
    ((Elab.runRaws "t" inlineInput).1.body == #[.para #[.text "A with words B"]])
  let blockInput : Array Parse.Raw :=
    #[.word "A" ip, .space,
      .env (Parse.inputEnv "sub.tex") #[.word "one" ip, .par ip, .word "two" ip] ip]
  t "an input file with paragraphs is block content"
    ((Elab.runRaws "t" blockInput).1.body ==
      #[.para #[.text "A"], .para #[.text "one"], .para #[.text "two"]])

  -- verbatim: lexically blind content, kept literally as its own block.
  let verbSrc := "\\begin{verbatim}\ndef f(n):\n    return n\n\nf(2)  # two spaces\n\\end{verbatim}"
  t "elab verbatim is a block, content untouched"
    ((elabStr verbSrc).1.body == #[.verbatim none "\ndef f(n):\n    return n\n\nf(2)  # two spaces\n"] &&
     (elabStr verbSrc).2.isEmpty)
  t "verbatim lines trim the delimiters, keep blanks and indentation"
    (Ir.verbatimLines "\nabc\n  in\n\nz\n  " == #["abc", "  in", "", "z"])
  t "verbatim drops every trailing blank line, not one"
    (Ir.verbatimLines "\ncode\n\n\n  " == #["code"])
  t "verbatim inline form holds spaces as no-break spaces"
    (Ir.verbatimInlines "\na  b\n" == #[.text "a\u00a0\u00a0b"])

def kpChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- knuth–plass: DP result equals brute-force minimum over all break sequences
  let cases : List (String × Array Layout.Item × Dim.Sp) := [
    ("three words", mkItems [W 100, G, W 100, G, W 100], Dim.pt 250),
    ("four words", mkItems [W 50, G, W 60, G, W 70, G, W 80], Dim.pt 150),
    ("forced mid", mkItems ([W 100, G, W 100] ++ BRK ++ [W 100]), Dim.pt 250),
    ("overfull word", mkItems [W 300], Dim.pt 100),
    ("tight fit", mkItems [W 80, G, W 80, G, W 80, G, W 80, G, W 80], Dim.pt 170),
    ("hyphen choice", mkItems [W 60, G, W 40, H, W 50, G, W 60], Dim.pt 120),
    ("double hyphen", mkItems [W 70, H, W 70, H, W 70, H, W 70], Dim.pt 80),
    ("hyphen vs glue", mkItems [W 50, G, W 30, H, W 30, G, W 50, G, W 40], Dim.pt 100)]
  for (name, items, target) in cases do
    let kpBreaks := (Layout.kp items target).toList
    let kpCost := seqCost items target kpBreaks
    let brute := bruteBest items target
    t s!"kp optimal ({name})" (kpCost.isSome && kpCost == brute && !kpBreaks.isEmpty)

def hyphenChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- Hyphenation. Expectations are real TeX \showhyphens output with the SAME
  -- pattern set the engine embeds (luatex + hyph-en-us.tex, hyphenmins 2/3);
  -- plain lualatex is a different oracle because TeX Live maps `english` to
  -- hyphen.tex, Knuth's frozen subset. \showhyphens lists every admissible
  -- break, not one chosen rendering. Full 552-word check: scripts/hyphen-diff.lean
  let pats := Hyphen.load
  let hyph (w : String) : String := Id.run do
    let breaks := Hyphen.hyphenate pats w
    let mut out := ""
    for (c, i) in w.toList.zipIdx do
      if i > 0 && breaks.contains i then
        out := out.push '-'
      out := out.push c
    return out
  t "hyphen patterns loaded" (pats.map.size > 4000)
  t "hyphen incomprehensibility" (hyph "incomprehensibility" == "in-com-pre-hen-si-bil-ity")
  t "hyphen internationalization" (hyph "internationalization" == "in-ter-na-tion-al-iza-tion")
  t "hyphen algorithm" (hyph "algorithm" == "al-go-rithm")
  t "hyphen paragraph" (hyph "paragraph" == "para-graph")
  t "hyphen typesetting" (hyph "typesetting" == "type-set-ting")
  t "hyphen hyphenation" (hyph "hyphenation" == "hy-phen-ation")
  t "hyphen long word" (hyph "floccinaucinihilipilification" ==
    "floc-cin-aucini-hilip-il-i-fi-ca-tion")
  t "hyphen exception dictionary" (hyph "associate" == "as-so-ciate")
  t "hyphen short word untouched" (hyph "cat" == "cat")
  t "hyphen capitalized" (hyph "Paragraph" == "Para-graph")
  -- These three pin the pattern set: Knuth's hyphen.tex gives def-i-ni-tion,
  -- mono-tone, and no break at all in toolchain.
  t "hyphen set is ushyphmax (definition)" (hyph "definition" == "de-f-i-n-i-tion")
  t "hyphen set is ushyphmax (monotone)" (hyph "monotone" == "mo-not-one")
  t "hyphen set is ushyphmax (toolchain)" (hyph "toolchain" == "tool-chain")
  -- leftMin=2 / rightMin=3 are enforced, so no break may strand 1 letter or 2.
  t "hyphen respects hyphenmins" ((Hyphen.hyphenate pats "typesetting").all
    fun p => p ≥ 2 && p + 3 ≤ 11)

def declChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- declarations: \page, \pdfmeta, \assert
  let declSrc := "\\documentclass{article}\n" ++
    "\\page{ size = a5, margin = 0.5in }\n" ++
    "\\pdfmeta{ title = \"T\", author = \"A\" }\n" ++
    "\\assert{ pages == 1 }\n" ++
    "\\assert{ fonts.all_embedded }\n" ++
    "\\begin{document}hi\\end{document}"
  let (declDoc, declDs) := elabStr declSrc
  t "decl source clean" declDs.isEmpty
  t "decl page size" (declDoc.page.width == Dim.pt 420 && declDoc.page.height == Dim.pt 595)
  t "decl margin both axes"
    (declDoc.page.vmargin == Dim.inch 1 / 2 && declDoc.page.hmargin == Dim.inch 1 / 2)
  t "decl metadata" (declDoc.info.title == some "T" && declDoc.info.author == some "A")
  t "decl assertions parsed" (declDoc.asserts.size == 2)

  -- dimension parsing is exact
  t "decl dim in" (Decl.parseValue "0.5in" == some (.dim (Dim.inch 1 / 2)))
  t "decl dim pt" (Decl.parseValue "12pt" == some (.dim (Dim.pt 12)))
  t "decl dim cm" (Decl.parseValue "2.54cm" == some (.dim (Dim.inch 1)))
  t "decl dim mm" (Decl.parseValue "25.4mm" == some (.dim (Dim.inch 1)))
  t "decl string" (Decl.parseValue "\"a b\"" == some (.str "a b"))
  t "decl ident" (Decl.parseValue "letter" == some (.ident "letter"))
  t "decl int" (Decl.parseValue "3" == some (.int 3))
  t "decl rejects junk" (Decl.parseValue "12 furlongs" == none)

  -- declaration diagnostics, one code each
  t "decl unknown size" (errCodes ("\\documentclass{article}\n\\page{ size = tabloid }\n" ++
    "\\begin{document}x\\end{document}") == ["E0324"])
  t "decl unknown key" (errCodes ("\\documentclass{article}\n\\page{ bogus = 1pt }\n" ++
    "\\begin{document}x\\end{document}") == ["E0322"])
  t "decl wrong type" (errCodes ("\\documentclass{article}\n\\page{ vmargin = \"x\" }\n" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "decl bad assertion" (errCodes ("\\documentclass{article}\n\\assert{ pages =~ 1 }\n" ++
    "\\begin{document}x\\end{document}") == ["E0325"])
  t "decl needs a block" (errCodes ("\\documentclass{article}\n\\page\n" ++
    "\\begin{document}x\\end{document}") == ["E0304"])

  -- assertions are judged against what shipped
  let shipped : Check.Shipped := { pages := 2, fontsEmbedded := true }
  let mkAssert (k : Ir.AssertKind) : Ir.Assertion := { kind := k, span := none }
  t "assert pages eq holds" ((Check.one shipped (mkAssert (.pages .eq 2))).isNone)
  t "assert pages eq fails" ((Check.one shipped (mkAssert (.pages .eq 1))).isSome)
  t "assert pages le holds" ((Check.one shipped (mkAssert (.pages .le 3))).isNone)
  t "assert pages gt fails" ((Check.one shipped (mkAssert (.pages .gt 5))).isSome)
  t "assert fonts holds" ((Check.one shipped (mkAssert .fontsAllEmbedded)).isNone)
  t "assert fonts fails"
    ((Check.one { shipped with fontsEmbedded := false } (mkAssert .fontsAllEmbedded)).isSome)
  t "assert failure names the actual"
    (((Check.one shipped (mkAssert (.pages .eq 1))).map (·.message)).any
      fun m => (m.splitOn "actual: 2").length == 2)
  t "assert all reports every failure"
    ((Check.all shipped #[mkAssert (.pages .eq 1), mkAssert (.pages .eq 2),
      mkAssert (.pages .lt 1)]).size == 2)

def tokensChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \tokens: font-relative lengths, derived tokens, and \block spacing
  let tokSrc := "\\documentclass{article}\n" ++
    "\\tokens{ rhythm = 2ex plus 0.5ex, sep = 0.75 * rhythm, slab = 18pt }\n" ++
    "\\begin{document}\\block[before = sep]{x}\\end{document}"
  let (tokDoc, tokDs) := elabStr tokSrc
  t "tokens source clean" tokDs.isEmpty
  t "tokens ex is symbolic" (tokDoc.tokens.find? "rhythm" ==
    some { width := { ex := 2000 }, stretch := { ex := 500 } })
  t "tokens derived scales earlier" (tokDoc.tokens.find? "sep" ==
    some { width := { ex := 1500 }, stretch := { ex := 375 } })
  t "tokens absolute" (tokDoc.tokens.find? "slab" ==
    some { width := Dim.Length.ofSp (Dim.pt 18) })
  t "block carries declared spacing" (tokDoc.body.any fun b =>
    match b with
    | .spaced before _ => before.width.ex == 1500
    | _ => false)
  -- A bare name is a well-formed value of the wrong type (E0323); text that
  -- parses as nothing at all is E0321. Both rejected, code says which.
  t "tokens reject wrong type" (errCodes ("\\documentclass{article}\\tokens{ a = wat }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "tokens reject junk" (errCodes
    ("\\documentclass{article}\\tokens{ a = 3 furlongs }" ++
     "\\begin{document}x\\end{document}") == ["E0321"])
  t "block unknown key" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block[after = 1pt]{x}\\end{document}") == ["E0322"])
  t "block needs a body" (errCodes ("\\documentclass{article}" ++
    "\\begin{document}\\block\\end{document}") == ["E0304"])

  -- Length resolution against real font metrics
  t "length resolve ex" ((Dim.Length.mk 0 0 1000).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 5)
  t "length resolve em" ((Dim.Length.mk 0 1500 0).resolve (Dim.pt 10) (Dim.pt 5) ==
    Dim.pt 15)
  t "length resolve mixed"
    ((Dim.Length.mk (Dim.pt 2) 1000 1000).resolve (Dim.pt 10) (Dim.pt 4) == Dim.pt 16)

  -- text symbols keep the space after them, unlike other control words
  t "symbol keeps space" (toks "a \\middot b" ==
    [.word "a", .space, .ctrl "middot", .space, .word "b"])
  t "command still eats space" (toks "a \\textbf b" ==
    [.word "a", .space, .ctrl "textbf", .word "b"])
  let (symDoc, symDs) := elabStr "a \\middot b \\ldots"
  t "symbol elaborates" (symDs.isEmpty && symDoc.body ==
    #[.para #[.text "a · b …"]])

def smartChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- smart punctuation: what the author typed is what they meant
  t "smart en dash" ((elabStr "2021--2024").1.body == #[.para #[.text "2021–2024"]])
  t "smart em dash" ((elabStr "a---b").1.body == #[.para #[.text "a—b"]])
  t "smart ellipsis" ((elabStr "wait...").1.body == #[.para #[.text "wait…"]])
  t "smart quotes directional"
    ((elabStr "say \"hi\" and don't").1.body == #[.para #[.text "say “hi” and don’t"]])
  t "mono keeps punctuation literal"
    ((elabStr "\\texttt{a--b}").1.body ==
      #[.para #[.styled .mono #[.text "a--b"]]])

def linkHtmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- links, running content, and block-producing user commands
  let (linkDoc, linkDs) := elabStr "\\href{https://example.org}{text}"
  t "href source clean" linkDs.isEmpty
  t "href wraps body" (linkDoc.body ==
    #[.para #[.link "https://example.org" #[.text "text"]]])
  let (bareDoc, bareDs) := elabStr "\\href{https://example.org}"
  t "href bare prints its url" (bareDs.isEmpty && bareDoc.body ==
    #[.para #[.link "https://example.org" #[.text "https://example.org"]]])
  let runSrc := "\\documentclass{article}\n" ++
    "\\runninghead{Title \\hfill \\pagenumber}\n" ++
    "\\runningfoot{page \\pagenumber\\ of \\pagecount}\n" ++
    "\\begin{document}x\\end{document}"
  let (runDoc, runDs) := elabStr runSrc
  t "running content clean" runDs.isEmpty
  t "running head parsed" (runDoc.head.isSome && runDoc.foot.isSome)
  t "running head has a page number"
    ((runDoc.head.getD #[]).any fun x => x == .pageNumber)
  let blockMacro := "\\documentclass{article}\n" ++
    "\\define \\entry(a: text) {\\block[before = 3pt]{\\textbf{\\a}}}\n" ++
    "\\begin{document}\\entry{One}\\entry{Two}\\end{document}"
  let (bmDoc, bmDs) := elabStr blockMacro
  t "block-producing macro clean" bmDs.isEmpty
  t "block-producing macro yields blocks" (bmDoc.body.size == 2 &&
    bmDoc.body.all fun b => match b with
      | .role "entry" body => body.all fun inner => match inner with
        | .spaced _ _ => true
        | _ => false
      | _ => false)
  -- An inline-only macro must stay inline, or it would split the paragraph.
  let inlineMacro := "\\documentclass{article}\n" ++
    "\\define \\who(a: text) {\\textbf{\\a}}\n" ++
    "\\begin{document}\\who{Ada} wrote it\\end{document}"
  let (imDoc, _) := elabStr inlineMacro
  t "inline macro does not split the paragraph" (imDoc.body.size == 1)

  -- HTML backend
  let escaped := Html.escapeText "a <script> & \"x\""
  t "html escapes text" (escaped == "a &lt;script&gt; &amp; \"x\"")
  t "html escapes attributes" (Html.escapeAttr "a\"b<c" == "a&quot;b&lt;c")
  t "html void element has no closing tag"
    (Html.render (Html.elem "br" #[]) 0 == "<br>\n")
  t "html phrasing content stays on one line"
    (Html.render (Html.elem "p" #[Html.text "a ", Html.elem "em" #[Html.text "b"],
      Html.text ", c"]) 0 == "<p>a <em>b</em>, c</p>\n")
  t "html style payload cannot close its own tag"
    (((Html.render (Html.Node.style "x</style>bad") 0).splitOn "</style>").length == 2)
  -- The same contract inside a phrasing parent, where rendering goes through
  -- the inline printer instead.
  t "html style payload cannot close its own tag inline"
    (((Html.render (Html.elem "p" #[Html.Node.style "x</style>bad"]) 0).splitOn
      "</style>").length == 2)
  t "html script payload cannot close its own tag inline"
    (((Html.render (Html.elem "p" #[Html.Node.script #[] "x</script>bad"]) 0).splitOn
      "</script>").length == 2)
  rawPayloadChecks ref
  precommitChecks ref

  let (htmlDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED }\n" ++
    "\\pdfmeta{ title = \"T\" }\n" ++
    "\\begin{document}\n" ++
    "\\section{Head}\n" ++
    "A \\textbf{bold} word, \\textcolor{primary}{coloured}, and a " ++
    "\\href{https://example.org}{link}.\n\n" ++
    "\\begin{itemize}\\item One\\end{itemize}\n" ++
    "\\end{document}")
  let (page, pageDiags) := HtmlDoc.emit {} htmlDoc
  t "html emit clean" pageDiags.isEmpty
  t "html has doctype" (page.startsWith "<!DOCTYPE html>")
  t "html sets the title" ((page.splitOn "<title>T</title>").length == 2)
  t "html section becomes h2" ((page.splitOn "<h2>Head</h2>").length == 2)
  t "html bold becomes strong" ((page.splitOn "<strong>bold</strong>").length == 2)
  t "html colour references the token"
    ((page.splitOn "var(--primary, #7c3aed)").length == 2)
  t "html link has href"
    ((page.splitOn
      "<a href=\"https://example.org\" style=\"color: inherit\">link</a>").length == 2)
  t "html single-para item is not wrapped"
    ((page.splitOn "<li>One</li>").length == 2)
  t "html inlines the stylesheet" ((page.splitOn "<style>").length == 2)
  t "html declares the generator" ((page.splitOn "content=\"leantex\"").length == 2)

  -- Running content is paged furniture: HTML says so rather than dropping it.
  let (_, runHtmlDiags) := HtmlDoc.emit {} runDoc
  t "html warns about running content" (runHtmlDiags.any (·.code == "W0007"))

  -- Bulma interop binds our tokens to the framework's own properties.
  let (bulmaPage, _) := HtmlDoc.emit { css := .bulma } htmlDoc
  t "bulma mode binds primary" ((bulmaPage.splitOn "--bulma-primary").length == 2)
  t "bulma mode ships no base sheet" ((bulmaPage.splitOn "--measure").length == 1)
  let (barePage, _) := HtmlDoc.emit { css := .none } htmlDoc
  t "css none emits no style element" ((barePage.splitOn "<style>").length == 1)

  -- A stretched row broken by `\\` becomes a column of rows. A <br> cannot end
  -- a layout row, so the break has to be structural or the second line lands
  -- beside the first -- where the PDF puts it below.
  let (rowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\\\second\\end{document}")
  let (rowPage, _) := HtmlDoc.emit {} rowDoc
  t "broken stretched row becomes rows"
    ((rowPage.splitOn "<span class=\"entry-row").length == 3)
  t "broken stretched row keeps no br" ((rowPage.splitOn "<br>").length == 1)
  -- An unbroken one stays a single row.
  let (oneRowDoc, _) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "left \\hfill right\\end{document}")
  t "unbroken stretched row stays one row"
    (((HtmlDoc.emit {} oneRowDoc).1.splitOn "class=\"entry entry-pair\"").length == 2)

  -- \hfill and control-symbol spaces
  -- \hfill takes no argument but still swallows the following space: a space
  -- after the stretch would be visible at the far margin.
  let (fillDoc, fillDs) := elabStr "a \\hfill b"
  t "hfill source clean" fillDs.isEmpty
  t "hfill becomes an inline fill" (fillDoc.body ==
    #[.para #[.text "a ", .fill, .text "b"]])
  t "thin space escape" ((elabStr "a\\,b").1.body ==
    #[.para #[.text "a b"]])

def paletteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \palette and colour
  let palSrc := "\\documentclass{article}\n" ++
    "\\palette{ primary = #7C3AED, short = #123 }\n" ++
    "\\begin{document}\\textcolor{primary}{x} {\\short y} z\\end{document}"
  let (palDoc, palDs) := elabStr palSrc
  t "palette source clean" palDs.isEmpty
  t "palette parsed" (palDoc.palette.find? "primary" ==
    some { r := 0x7C, g := 0x3A, b := 0xED })
  t "palette short hex expands" (palDoc.palette.find? "short" ==
    some { r := 0x11, g := 0x22, b := 0x33 })
  t "palette textcolor wraps" (palDoc.body.any fun b =>
    match b with
    | .para content => content.any fun x =>
      match x with
      | .colored c name body => c.r == 0x7C && name == some "primary" && body.size == 1
      | _ => false
    | _ => false)
  t "palette unknown name warns and keeps the content"
    (warnCodes ("\\documentclass{article}\\palette{a = #fff}" ++
      "\\begin{document}\\textcolor{nope}{x}\\end{document}") == ["W0304"] &&
     (elabStr ("\\documentclass{article}\\palette{a = #fff}" ++
      "\\begin{document}\\textcolor{nope}{x}\\end{document}")).1.body ==
        #[.para #[.text "x"]])
  -- A palette name binds a following group as its argument. It used to colour
  -- everything to the end of the group, so `\primary{Alex} Doe` painted Doe too.
  let palSrc (body : String) : Ir.Doc :=
    (Elab.run "t" ("\\documentclass{article}\\palette{mut = #888888}" ++
      "\\begin{document}" ++ body ++ "\\end{document}")).1
  t "palette name takes its group as an argument"
    ((palSrc "\\mut{in} out").body == #[.para #[
      .colored { r := 0x88, g := 0x88, b := 0x88 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette name with no group runs to the end of the group"
    ((palSrc "{\\mut in} out").body == #[.para #[
      .colored { r := 0x88, g := 0x88, b := 0x88 } (some "mut") #[.text "in"],
      .text " out"]])
  t "palette covered fraction declares" (
    (elabStr ("\\documentclass{article}\\palette{covered = 21\\%}" ++
      "\\begin{document}x\\end{document}")).1.palette.coveredFraction == some 21)
  t "palette covered fraction out of range" (errCodes
    ("\\documentclass{article}\\palette{covered = 100\\%}" ++
     "\\begin{document}x\\end{document}") == ["E0332"])
  t "palette covered still accepts a colour" (
    (elabStr ("\\documentclass{article}\\palette{covered = #808080}" ++
      "\\begin{document}x\\end{document}")).1.palette.find? "covered"
      == some { r := 0x80, g := 0x80, b := 0x80 })
  t "palette wrong type" (errCodes ("\\documentclass{article}\\palette{a = 3pt}" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "palette cannot shadow builtin" (errCodes
    ("\\documentclass{article}\\palette{textbf = #fff}" ++
     "\\begin{document}x\\end{document}") == ["E0303"])
  t "color value parsed" (Decl.parseValue "#7C3AED" == some (.color 0x7C 0x3A 0xED))
  t "color rejects bad hex" (Decl.parseValue "#12345" == none)
  t "color pdf components" ((Ir.Color.mk 255 0 128 none).pdfComponents == "1 0 0.502")
  t "color black components" (Ir.Color.black.pdfComponents == "0 0 0")

/-- xcolor's `!` mixing in the palette. Its own def: `main`'s elaboration
budget is spent (see lineChecks). -/
def contrastChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- The channel table against the WCAG formula it tabulates, evaluated in
  -- Float: c' = c/255; c' ≤ 0.04045 → c'/12.92, else ((c'+0.055)/1.055)^2.4,
  -- scaled by 1e7 and rounded (w3.org/TR/WCAG22/#dfn-relative-luminance).
  let lin (c : Nat) : Nat :=
    let s := c.toFloat / 255.0
    let l := if s ≤ 0.04045 then s / 12.92
      else ((s + 0.055) / 1.055) ^ (2.4 : Float)
    (l * 10000000.0).round.toUInt32.toNat
  t "contrast table is the WCAG formula, all 256 channels"
    ((List.range 256).all fun c => Oklab.channelLinear.getD c 0 == lin c)
  -- The definition's own extremes: black on white is 21:1, self is 1:1.
  t "contrast black on white is 21:1"
    (Contrast.contrastMilli .black .white == 21000)
  t "contrast of a colour with itself is 1:1"
    (Contrast.contrastMilli Contrast.light.accent Contrast.light.accent == 1000)
  t "contrast does not care which side is the text"
    (Contrast.contrastMilli Contrast.light.muted Contrast.light.surface ==
     Contrast.contrastMilli Contrast.light.surface Contrast.light.muted)
  t "ratio string" (Contrast.ratioString 4627 == "4.62:1" &&
    Contrast.ratioString 21000 == "21.00:1" && Contrast.ratioString 1005 == "1.00:1")
  -- The contract check fires on a deliberately illegible bundle: the dark
  -- set with the light accent is the exact defect dark_contract guards
  -- against (2.64:1 focus ring, under SC 1.4.11's 3:1).
  t "contract rejects the illegible bundle"
    (!({ Contrast.dark with accent := Contrast.light.accent } :
      Contrast.ThemeColors).contractHolds)
  t "illegible bundle names its ratio" (Contrast.ratioString
    (Contrast.contrastMilli Contrast.light.accent Contrast.dark.surface) == "2.64:1")

  -- The covered contract fires on the finding it encodes: moloch at
  -- Material's 38% leaves alert (2.89:1) and example (2.75:1) under the
  -- 3:1 state change — the fraction is the bundle's, the bound is not.
  t "covered contract rejects moloch at 38%"
    (!Contrast.coveredContract
      { Theme.moloch.palette with coveredFraction := some 38 })
  -- Monotone quieting as a property over pseudo-random colours: covering
  -- never raises contrast against the page, and covering a cover quiets
  -- further (≤: equality is reachable at the page itself). The per-bundle
  -- strict form is the coverMonotone kernel checks.
  let quietingHolds := Id.run do
    let cov := (Ir.Design.ofDoc {}).cover
    let mut seed : Nat := 1
    for _ in [0:400] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let c : Ir.Color := { r := UInt8.ofNat (seed % 256)
                            g := UInt8.ofNat ((seed / 256) % 256)
                            b := UInt8.ofNat ((seed / 65536) % 256) }
      let c1 := cov.of c
      let c2 := cov.of c1
      if Contrast.contrastMilli c1 Ir.Color.white > Contrast.contrastMilli c Ir.Color.white
          || Contrast.contrastMilli c2 Ir.Color.white > Contrast.contrastMilli c1 Ir.Color.white then
        return false
    return true
  t "covering quiets monotonically over random colours" quietingHolds

  -- The stylesheet ships the proven token sets: the dark block overrides
  -- the accent (the light one reads 2.64:1 on the dark surface, under SC
  -- 1.4.11's 3:1), and both spellings come from the constants the
  -- contract theorems cover.
  let (page, _) := HtmlDoc.emit {} (elabStr "x").1
  let darkBlock := ((page.splitOn "prefers-color-scheme: dark")[1]?.getD "").splitOn "}"
    |>.headD ""
  t "dark block re-accents"
    ((darkBlock.splitOn s!"--accent: {HtmlDoc.cssColor Contrast.dark.accent}").length == 2)
  t "light accent comes from the proven constant"
    ((page.splitOn s!"--accent: {HtmlDoc.cssColor Contrast.light.accent}").length == 2)

  -- The pairing warning: a pale tint on the page fires W0315 with the
  -- ratio and threshold; declaring intent silences it; covered is exempt
  -- by role; large-scale text is held to 3:1 instead of 4.5:1; a declared
  -- fg is judged against a declared bg directly.
  let pale := "\\documentclass{article}\\palette{ washed = #DDDDDD }" ++
    "\\begin{document}\\textcolor{washed}{faint}\\end{document}"
  t "pale text pairing warns with ratio and threshold"
    ((elabStr pale).2.any fun d => d.code == "W0315" &&
      (d.message.splitOn "1.30:1").length == 2 &&
      (d.message.splitOn "4.50:1").length == 2)
  t "declared intent silences the pairing warning"
    (!(warnCodes ("\\documentclass{article}" ++
      "\\palette[decorative]{ washed = #DDDDDD }" ++
      "\\begin{document}\\textcolor{washed}{faint}\\end{document}")).contains "W0315")
  -- An anonymous use (a mixed colour) has no name, so the decorative
  -- escape matches it by value — the help's own printed line must be the
  -- line that silences the warning it rides on.
  let anon := "\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
    "\\begin{document}\\textcolor{fg!50!bg}{quiet}\\end{document}"
  let anonDiag := ((elabStr anon).2.filter (·.code == "W0315"))[0]?
  t "an anonymous mixed colour warns" anonDiag.isSome
  t "the help's own line silences the anonymous pairing"
    (match anonDiag.bind (·.help) with
     | some h =>
       let decl := ((h.splitOn ": ")[1]?).getD ""
       decl.startsWith "\\palette[decorative]" &&
         !(warnCodes ("\\documentclass{article}\\palette{ fg = #23373B, bg = #FAFAFA }" ++
           decl ++
           "\\begin{document}\\textcolor{fg!50!bg}{quiet}\\end{document}")).contains "W0315"
     | none => false)
  t "covered is exempt by role"
    (!(warnCodes ("\\documentclass{article}\\palette{ covered = #DDDDDD }" ++
      "\\begin{document}\\textcolor{covered}{later}\\end{document}")).contains "W0315")
  t "unknown palette option warns and skips the block"
    (warnCodes ("\\documentclass{article}\\palette[dark]{ a = #101010 }" ++
      "\\begin{document}x\\end{document}") == ["W0316"])
  -- #767676 on the shipped surface is 4.34:1 -- under 4.5 but over 3: as
  -- body text it warns, as Huge (24.9pt) large-scale text it passes.
  let grey (body : String) := "\\documentclass{article}" ++
    "\\palette{ grey = #767676 }\\begin{document}" ++ body ++ "\\end{document}"
  t "borderline grey warns as body text"
    ((warnCodes (grey "\\textcolor{grey}{x}")).contains "W0315")
  t "borderline grey passes as large-scale text"
    (!(warnCodes (grey "{\\Huge \\textcolor{grey}{x}}")).contains "W0315")
  -- The judge reads the layout's own scale (contrast_judges_what_layout_sets):
  -- at a 9 pt base a section sets at 12.96 pt — not WCAG large-scale — while
  -- the old absolute 14 pt bold was, so the judge passed text the page fails.
  -- #767676 reads at 4.34:1 on the shipped surface: over 3:1, under 4.5:1.
  -- At the 10 pt base the section sets at 14.4 pt bold, large-scale either
  -- way: the verdicts agree, which is why the drift went unseen.
  let sizedSection (size : String) := "\\documentclass{article}" ++
    "\\page{ fontsize = " ++ size ++ " }\\palette{ grey = #767676 }" ++
    "\\begin{document}\\section{\\textcolor{grey}{Head}}x\\end{document}"
  t "a 9pt-base section title is judged at the size the layout sets"
    ((warnCodes (sizedSection "9pt")).contains "W0315")
  t "a 10pt-base section title stays large-scale, judge and page agreeing"
    (!(warnCodes (sizedSection "10pt")).contains "W0315")
  t "a declared fg is judged against the declared bg"
    ((warnCodes ("\\documentclass{article}" ++
      "\\palette{ fg = #999999, bg = #888888 }" ++
      "\\begin{document}x\\end{document}")).contains "W0315")
  -- The effective pair (F3): the contract judges the pair the page ships,
  -- not only the pair the document spelled. A declared dark page with the
  -- ink left defaulted is black-on-dark in both backends — its own code
  -- (W0330), because its remedy is declaring the ink; declaring a legible
  -- ink silences it; a document that declares nothing ships the proven
  -- default pair and is not diagnosed.
  t "a declared dark page with a defaulted ink is diagnosed"
    ((elabStr ("\\documentclass{article}\\palette{ bg = #18181B }" ++
      "\\begin{document}x\\end{document}")).2.any fun d =>
        d.code == "W0330" && (d.message.splitOn "defaulted").length == 2)
  t "declaring a legible ink beside the dark page silences W0330"
    (!(warnCodes ("\\documentclass{article}" ++
      "\\palette{ fg = #FAFAF9, bg = #18181B }" ++
      "\\begin{document}x\\end{document}")).contains "W0330")
  t "an undeclared document is never diagnosed for its default pair"
    (((elabStr "\\documentclass{article}\\begin{document}x\\end{document}").2.filter
      fun d => d.code == "W0330" || d.code == "W0315").isEmpty)
  t "a defaulted ink on an undeclared page is fine: no pairing exists to fail"
    (!(warnCodes ("\\documentclass{article}\\palette{ washed = #DDDDDD }" ++
      "\\begin{document}x\\end{document}")).contains "W0330")
  t "a body use of the effective pair is not reported twice"
    ((((elabStr ("\\documentclass{article}" ++
      "\\palette{ fg = #999999, bg = #888888 }" ++
      "\\begin{document}\\textcolor{fg}{x}\\end{document}")).2.filter
        fun d => d.code == "W0315" || d.code == "W0330").size) == 1)
  t "the built-in themes raise no pairing warning"
    (!(warnCodes ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
      "\\begin{frame}x\\end{frame}\\end{document}")).contains "W0315")

  -- The built-in theme bundles, held to the same contract. The theorems
  -- range over the bundles' own typed values; this pin closes the chain:
  -- what \theme installs is exactly the bundle the theorems cover, and
  -- the live check passes.
  for th in Theme.builtin do
    let (thDoc, _) := elabStr ("\\documentclass{slides}\\theme{" ++ th.name ++
      "}\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")
    t s!"\\theme installs the {th.name} bundle's own values"
      (thDoc.palette == th.palette)
  t "every built-in bundle clears its thresholds"
    (Theme.builtin.all Contrast.Theme.contractHolds)
  -- The check fires on the illegible bundle it exists for: moloch's own
  -- alert (#EB811B, 2.61:1 as body text) fails the contract.
  t "the contract rejects moloch's original alert"
    (let badEntries := (Theme.moloch.palette.entries.filter (·.1 != "alert")).push
        ("alert", ({ r := 0xEB, g := 0x81, b := 0x1B } : Ir.Color))
     !Contrast.paletteContract { entries := badEntries })
  -- Themed \alert is colour AND bold: colour alone would be the run's only
  -- signal (WCAG 2.2 SC 1.4.1); unthemed it stays the bold stand-in.
  let themedAlert := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\begin{frame}\\alert{hot}\\end{frame}\\end{document}")
  t "themed alert is colour and bold" (themedAlert.1.body.any fun b =>
    match b with
    | .frame _ _ _ body => body.any fun blk =>
      match blk with
      | .para content => content.any fun x =>
        match x with
        | .colored _ (some "alert") inner => inner.any fun y =>
          match y with
          | .styled .bold _ => true
          | _ => false
        | _ => false
      | _ => false
    | _ => false)

def mixChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pal : Ir.Palette := { entries := #[("base", { r := 0x40, g := 0x00, b := 0x80 })] }
  t "mix toward white" (pal.resolve "base!50" == some { r := 0xA0, g := 0x80, b := 0xC0 })
  t "mix with black" (pal.resolve "base!50!black" == some { r := 0x20, g := 0x00, b := 0x40 })
  t "mix chain folds left" (pal.resolve "base!50!black!30" ==
    some ((({ r := 0x40, g := 0x00, b := 0x80 } : Ir.Color).mix 50 Ir.Color.black).mix 30 Ir.Color.white))
  t "mix black!2 is near-white"
    (({} : Ir.Palette).resolve "black!2" == some { r := 250, g := 250, b := 250 })
  t "mix plain name still resolves" (pal.resolve "base" == some { r := 0x40, g := 0x00, b := 0x80 })
  t "mix pct over 100 rejected" (pal.resolve "base!101" == none)
  t "mix unknown atom rejected" (pal.resolve "nope!50" == none)
  -- One resolving site: a declared entry wins over resolve's own black and
  -- white atoms, so a mix, \textcolor, and the role invocation cannot
  -- disagree about what a name means. Before the rule, a palette naming an
  -- entry 'black' painted the declared colour where find? resolved and
  -- pure black where resolve did — PDF ink and the HTML variable diverged.
  let shadow : Ir.Palette := { entries := #[("black", { r := 0x33, g := 0x33, b := 0x33 })] }
  t "a declared black wins over the built-in atom"
    (shadow.resolve "black" == shadow.find? "black")
  t "undeclared black and white stay available"
    (({} : Ir.Palette).resolve "black" == some Ir.Color.black &&
     ({} : Ir.Palette).resolve "white" == some Ir.Color.white)
  -- Declaration site: a mix value reads the entries declared so far.
  let doc (body : String) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ fg = #000000, bg = #ffffff, dim = bg!50!fg, faint = black!2 }\n" ++
    "\\begin{document}" ++ body ++ "\\end{document}")
  let (pDoc, pDs) := doc "x"
  t "palette mix entry clean" pDs.isEmpty
  t "palette mix entry value" (pDoc.palette.find? "dim" == some { r := 0x80, g := 0x80, b := 0x80 })
  t "palette black!2 entry" (pDoc.palette.find? "faint" == some { r := 250, g := 250, b := 250 })
  -- Use site: \textcolor takes a mix, `fg`/`bg` naming the current semantic
  -- foreground and background. A computed colour carries no var name.
  let (uDoc, uDs) := doc "\\textcolor{fg!50!bg}{x}"
  t "textcolor mix resolves without W0304" (!uDs.any (·.code == "W0304"))
  t "textcolor mix colours the content" (uDoc.body == #[.para #[
    .colored { r := 0x80, g := 0x80, b := 0x80 } none #[.text "x"]]])
  t "textcolor mix with unknown base still warns"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\textcolor{quiet!50}{x}\\end{document}") == ["W0304"])
  -- Later declarations override earlier ones, theme defaults included.
  let (oDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ a = #111111 }\\palette{ a = #222222 }\n" ++
    "\\tokens{ s = 4pt }\\tokens{ s = 8pt }\n" ++
    "\\begin{document}x\\end{document}")
  t "palette redeclare overrides" (oDoc.palette.find? "a" == some { r := 0x22, g := 0x22, b := 0x22 })
  t "tokens redeclare overrides"
    ((oDoc.tokens.find? "s").map (·.width) == some (Dim.Length.ofSp (Dim.pt 8)))
  t "palette redeclare keeps one entry"
    ((oDoc.palette.entries.filter (·.1 == "a")).size == 1)

/-- `\theme` and the built-in bundles: a theme is data applied through the
same declarations a document writes, and everything after the site
overrides it. -/
def themeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let deck (pre body : String) : String :=
    "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let (mDoc, mDs) := elabStr (deck "\\theme{moloch}" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "theme moloch source clean" mDs.isEmpty
  t "theme moloch declares the semantic keys"
    (["fg", "bg", "alert", "frametitlefg", "frametitlebg", "progressfg",
      "progressbg", "standoutfg", "standoutbg"].all
      fun k => (mDoc.palette.find? k).isSome)
  t "theme moloch resolves its own mixes"
    (mDoc.palette.find? "bg" == some { r := 0xFA, g := 0xFA, b := 0xFA } &&
     mDoc.palette.find? "frametitlebg" == some { r := 0x23, g := 0x37, b := 0x3B } &&
     mDoc.palette.find? "progressbg" == some { r := 0xCB, g := 0xC0, b := 0xB6 })
  t "theme moloch declares the progress token"
    (((mDoc.tokens.find? "progressheight").map (·.width)) ==
      some (Dim.Length.ofSp (Dim.pt 1)))
  t "theme moloch styles the frame title"
    ((mDoc.styles.find? "frametitle").bind (·.font) |>.isSome)
  -- The theme is a default: a later declaration replaces its entry, and
  -- only that entry.
  let (oDoc, _) := elabStr (deck "\\theme{moloch}\\palette{ alert = #C2185B }"
    "\\begin{frame}{T}\nx\n\\end{frame}")
  t "a document overrides the theme"
    (oDoc.palette.find? "alert" == some { r := 0xC2, g := 0x18, b := 0x5B } &&
     oDoc.palette.find? "frametitlebg" == some { r := 0x23, g := 0x37, b := 0x3B })
  -- The second bundle is a table of values, not new code: plainer keys,
  -- no title bar because the key is simply absent.
  let (pDoc, pDs) := elabStr (deck "\\theme{plain}" "\\begin{frame}{T}\nx\n\\end{frame}")
  t "theme plain source clean" pDs.isEmpty
  t "theme plain has no title bar key" ((pDoc.palette.find? "frametitlebg").isNone)
  t "theme plain still inverts standout"
    (pDoc.palette.find? "standoutbg" == pDoc.palette.find? "fg")
  -- Unknown names warn and leave the document unthemed.
  let (uDoc, uDs) := elabStr (deck "\\theme{vaporwave}" "x")
  t "unknown theme warns naming the bundles"
    (uDs.any fun d => d.code == "W0319" &&
      ((d.help.getD "").splitOn "moloch").length == 2 &&
      ((d.help.getD "").splitOn "plain").length == 2)
  t "unknown theme leaves the palette empty" (uDoc.palette.entries.isEmpty)
  -- \alert through the compat layer: a colour when themed, bold when not.
  let (aDoc, _) := elabStr (deck "\\usetheme{moloch}"
    "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")
  t "themed alert is the alert colour"
    (match aDoc.body with
     | #[.frame _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .colored c (some "alert") _ => c == { r := 0xA5, g := 0x5A, b := 0x13 }
          | _ => false
        | _ => false
     | _ => false)
  t "unthemed alert stays bold"
    (match (elabStr (deck "" "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")).1.body with
     | #[.frame _ _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .styled .bold _ => true
          | _ => false
        | _ => false
     | _ => false)

/-- The resolved `Design`: one construction site applies every default, so
these pin the values the record resolves to — the un-themed document, the
themed one, and the standout inversion a half-declared pair falls back to.
Totality itself is the record type, not a test. -/
def designChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let designOf (pre : String) : Ir.Design :=
    Ir.Design.ofDoc (elabStr ("\\documentclass{slides}" ++ pre ++
      "\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")).1
  let bare := designOf ""
  t "bare design inks black on white, undeclared"
    (bare.fg == Ir.Color.black && bare.bg == Ir.Color.white &&
     !bare.fgDeclared && !bare.bgDeclared)
  t "bare design has no bar and no themed sections"
    (bare.frametitle.isNone && bare.progress.isNone)
  t "bare design standout inverts the page"
    (bare.standout == { fg := Ir.Color.white, bg := Ir.Color.black })
  t "bare design declares no covered constant and takes the 38% fraction"
    (bare.covered == none && bare.coveredFraction == Ir.coveredFractionDefault)
  t "bare design covers plain runs to 38% of black over white"
    (bare.cover.plain == { r := 0x86, g := 0x86, b := 0x86 })
  t "bare design mutes to the ink" (bare.muted == bare.fg)
  t "bare design separator defaults to the ink" (bare.separator == bare.fg)
  t "bare design progress bar is 1pt thick"
    (bare.progressheight == { width := Dim.Length.ofSp (Dim.pt 1) })
  let themed := designOf "\\theme{moloch}"
  t "themed design carries the bundle's bar pair"
    (themed.frametitle == some { fg := { r := 0xFA, g := 0xFA, b := 0xFA }, bg := { r := 0x23, g := 0x37, b := 0x3B } })
  t "themed design carries the progress pair"
    (themed.progress == some { fg := { r := 0xA5, g := 0x5A, b := 0x13 }, bg := { r := 0xCB, g := 0xC0, b := 0xB6 } })
  t "themed design reads the declared separator"
    (themed.separator == { r := 0xA5, g := 0x5A, b := 0x13 })
  t "themed design reads the declared muted step"
    (themed.muted == { r := 0x64, g := 0x72, b := 0x74 })
  -- A half-declared standout keeps the declared half and defaults the rest
  -- from the page's own colours — the fallback Layout applied per site.
  let half := designOf "\\palette{ standoutbg = #102030 }"
  t "half-declared standout defaults its fg from the page"
    (half.standout == { fg := Ir.Color.white, bg := { r := 0x10, g := 0x20, b := 0x30 } })

/-- Every role a built-in bundle declares is read: either a backend consumes
its resolved `Design` field (`Ir.Design.consumedRoles`) or documents use it
as a content colour by name. A declared-but-unread role with a known coming
consumer is a named warning in the build output, never silence; one nobody
expects fails the suite. The ledger is empty today — `separator` left it
when the title-page rule landed with the vertical-distribution slice
(`Elab.titleBlocks` reads it through the titlepage style). -/
def roleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let contentColours := ["alert", "example"]
  let pendingConsumer : List (String × String) := []
  for th in Theme.builtin do
    for (role, _) in th.palette.entries do
      if contentColours.contains role || Ir.Design.consumedRoles.contains role then
        pure ()
      else match pendingConsumer.lookup role with
        | some consumer =>
          IO.println (s!"warning: theme '{th.name}' declares '{role}' and no " ++
            s!"backend reads it yet ({consumer} is its coming consumer)")
        | none =>
          failures ref s!"theme '{th.name}' declares '{role}', which no code reads"
  check ref "pending roles are really unread"
    (pendingConsumer.all fun (r, _) => !Ir.Design.consumedRoles.contains r)

/-- The executable half of `every_role_is_invocable` (Elab.lean): resolution
order lives in `elabInlines`, whose sanctioned recursion no theorem can
range over, so the fact that every shipped bundle's role really reaches the
palette arm — nothing earlier in the chain intercepts the name — is pinned
by elaborating an invocation of every key. An oracle, not a theorem:
reorder resolution or shadow a role with a new engine arm and this fails
naming the key. -/
def roleInvocationChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for th in Theme.builtin do
    for (key, c) in th.palette.entries do
      let (doc, _) := elabStr ("\\documentclass{article}\\theme{" ++ th.name ++
        s!"}\\begin\{document}\\{key}\{x}\\end\{document}")
      -- `\alert` is a compat idiom (colour and bold, W3C SC 1.4.1): the
      -- role must reach the words, whatever wrapper the idiom adds.
      t s!"role '{key}' of '{th.name}' is invocable"
        (match doc.body with
         | #[.para #[.colored c' (some n) inner]] =>
           c' == c && n == key && Ir.plainText inner == "x"
         | _ => false)
  -- The two halves of palette-dependence meet on the real page: the use
  -- references the token (role_use_names_its_token) and :root declares it
  -- (paletteVar, the site role_use_is_palette_dependent ranges over).
  let (qDoc, qDs) := elabStr ("\\documentclass{article}\\palette{ quiet = #123456 }" ++
    "\\begin{document}\\quiet{x}\\end{document}")
  t "role page source clean" qDs.isEmpty
  let qPage := (HtmlDoc.emit {} qDoc).1
  t "a role use references its token on the page"
    ((qPage.splitOn "color: var(--quiet, #123456)").length == 2)
  t "the page declares the token the use references"
    ((qPage.splitOn "--quiet: #123456;").length == 2)

/-- W0341: a definition that shadows a palette role is named, with the cost
in the reason — the palette (a variant, a host page's override) and the
contrast judge no longer reach the words the definition styles. Judged
against the final palette, so declaration order cannot hide it; shadowing
any other command stays silent, as in LaTeX. -/
def roleShadowChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let diags (pre : String) : Array Diag :=
    (elabStr ("\\documentclass{article}\n" ++ pre ++
      "\\begin{document}\nx\n\\end{document}")).2
  let fires (ds : Array Diag) : Bool := ds.any fun d =>
    d.code == "W0342" && d.severity == .warning &&
      (d.message.splitOn "palette").length > 1
  t "a definition shadowing a theme role is named"
    (fires (diags "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n"))
  t "declaration order cannot hide the shadow"
    (fires (diags "\\define \\muted(word: content) {\\word}\n\\palette{ muted = #607060 }\n"))
  t "the newcommand spelling is the same shadow"
    (fires (diags "\\palette{ muted = #607060 }\n\\newcommand{\\muted}[1]{\\textbf{#1}}\n"))
  t "a zero-ary shadow is the same freeze"
    (fires (diags "\\palette{ muted = #607060 }\n\\define \\muted {gray words}\n"))
  t "a definition of an unshadowed name is silent"
    (!fires (diags "\\theme{plain}\n\\define \\entry(word: content) {\\word}\n"))
  t "the warning points at the define site"
    (((diags "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n").filterMap
      (·.span)).any (·.pos.line == 3))

def fontsDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \fonts declarations and family resolution
  let fontsSrc := "\\documentclass{article}\n" ++
    "\\fonts{ body = \"DejaVu Serif\", sf = \"DejaVu Sans\" }\n" ++
    "\\begin{document}x\\end{document}"
  let (fDoc, fDs) := elabStr fontsSrc
  t "fonts source clean" fDs.isEmpty
  t "fonts body" (fDoc.fonts.body == some "DejaVu Serif")
  t "fonts sf alias maps to sans" (fDoc.fonts.sans == some "DejaVu Sans")
  t "fonts mono unset" (fDoc.fonts.mono == none)
  t "fonts wrong type" (errCodes ("\\documentclass{article}\\fonts{ body = 12 }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "fonts unknown key" (errCodes ("\\documentclass{article}\\fonts{ script = \"X\" }" ++
    "\\begin{document}x\\end{document}") == ["E0322"])

  -- Resolution runs on the shipped faces, never the host's.
  let faces ← FontDb.scanRoots [testFonts]
  t "fontdb finds the twelve shipped faces" (faces.size == 12)
  t "fontdb finds source serif" ((FontDb.families faces).any (· == "Source Serif Pro"))
  defaultFontChecks ref
  shippedFontChecks ref faces
  match FontDb.resolve faces "Source Serif Pro" { bold := true } with
  | some (face, exact) =>
    t "fontdb bold is exact" exact
    t "fontdb bold flagged" face.bold
  | none => failures ref "fontdb: Source Serif Pro Bold not found"
  match FontDb.resolve faces "Source Serif Pro" { bold := true, italic := true } with
  | some (face, exact) => t "fontdb bold italic" (exact && face.bold && face.italic)
  | none => failures ref "fontdb: Source Serif Pro BoldItalic not found"
  t "fontdb unknown family" (FontDb.resolve faces "No Such Family Here" {} |>.isNone)

/-- The measure band (W0201): fires on continuous text set too wide or too
narrow, is scoped to pages rather than slides, and is silenced by declaring
`\page{ measure = free }`. -/
def measureChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Long enough to set at least four full lines at any measure under test.
  let prose := String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")
  let diagsOf (pre : String) (body : String) (geom : Layout.Geom := {}) : Array Diag :=
    let src := pre ++ "\\begin{document}" ++ body ++ "\\end{document}"
    (Layout.run geom oneFace none (Elab.run "t" src).1).diags
  let w0201 (ds : Array Diag) : Array Diag := ds.filter (·.code == "W0201")
  -- The word-processor default this engine replaced: letter with 1in
  -- margins holds ~100 characters at 10pt, far outside 45–90.
  let wide := diagsOf "\\documentclass{article}\\page{ hmargin = 1in }" prose
  t "wide measure warns" ((w0201 wide).size == 1)
  t "wide measure says narrow"
    ((w0201 wide).all fun d => (d.help.getD "").startsWith "narrow")
  t "measure = free silences the band"
    ((w0201 (diagsOf "\\documentclass{article}\\page{ hmargin = 1in, measure = free }" prose)).isEmpty)
  t "slides are outside the rule's scope"
    ((w0201 (diagsOf "\\documentclass{slides}" prose)).isEmpty)
  -- A card is display text too, and its default measure (~214pt, under 45
  -- characters) would earn "widen" in an article: the band is about
  -- continuous reading and does not apply to the class.
  let (cardProse, _) := Elab.run "t" ("\\documentclass{card}\\begin{document}" ++
    prose ++ "\\end{document}")
  t "cards are outside the rule's scope"
    ((w0201 (Layout.run (Layout.Geom.ofPage cardProse.page) oneFace none cardProse).diags).isEmpty)
  t "short text is not continuous reading"
    ((w0201 (diagsOf "\\documentclass{article}\\page{ hmargin = 1in }" "one line.")).isEmpty)
  let narrowGeom : Layout.Geom :=
    { pageW := Dim.pt 200, pageH := Dim.pt 2000, hmargin := Dim.pt 10, vmargin := Dim.pt 10 }
  let narrow := diagsOf "\\documentclass{article}" prose narrowGeom
  t "narrow measure warns and says widen"
    ((w0201 narrow).size == 1 &&
     (w0201 narrow).all fun d => (d.help.getD "").startsWith "widen")
  -- The default article page carries Bringhurst's 26-pica text block, and
  -- the band it was chosen for holds on it.
  let (dfltDoc, _) := Elab.run "t" ("\\documentclass{article}\\begin{document}" ++
    prose ++ "\\end{document}")
  t "default article text block is 26 picas"
    (dfltDoc.page.width - 2 * dfltDoc.page.hmargin == Ir.articleTextBlock)
  t "default article measure is in band"
    ((w0201 (Layout.run (Layout.Geom.ofPage dfltDoc.page) oneFace none dfltDoc).diags).isEmpty)
  -- A document that declared any \page geometry keeps every value it named.
  let (declDoc, _) := Elab.run "t"
    "\\documentclass{article}\\page{ vmargin = 0.5in }\\begin{document}x\\end{document}"
  t "declared \\page keeps the named margins" (declDoc.page.hmargin == Dim.inch 1)
  t "measure key rejects a stray value"
    ((elabStr "\\documentclass{article}\\page{ measure = loose }\\begin{document}x\\end{document}").2.any
      (·.code == "E0323"))
  -- The body size: slides default to beamer's documented 11pt, articles to
  -- the 10pt base; a class option or \page{ fontsize } takes precedence.
  let pageOf (src : String) : Ir.PageSpec :=
    (elabStr (src ++ "\\begin{document}x\\end{document}")).1.page
  t "slides default to beamer's 11pt"
    ((pageOf "\\documentclass{slides}").fontSize == Ir.slidesFontSize)
  t "articles keep the 10pt base"
    ((pageOf "\\documentclass{article}").fontSize == Ir.baseFontSize)
  t "a bare size class option is honored"
    ((pageOf "\\documentclass[10pt]{slides}").fontSize == Dim.pt 10)
  t "a fontsize= class option is honored"
    ((pageOf "\\documentclass[paper=letter, fontsize=12pt]{article}").fontSize == Dim.pt 12)
  t "\\page fontsize wins over the class option"
    ((pageOf "\\documentclass[10pt]{article}\\page{ fontsize = 14pt }").fontSize == Dim.pt 14)
  -- The guard admits exactly what `Layout.heading_hierarchy` covers: its
  -- 1 pt floor. A sub-point base was reachable and outside the theorem
  -- before the guard aligned (the D2 gap: positive but below the floor).
  t "a sub-point \\page fontsize is rejected and keeps the base"
    (((elabStr ("\\documentclass{article}\\page{ fontsize = 0.4pt }" ++
        "\\begin{document}x\\end{document}")).2.any (·.code == "E0323")) &&
     (pageOf "\\documentclass{article}\\page{ fontsize = 0.4pt }").fontSize
       == Ir.baseFontSize)

/-- Vertical-rhythm diagnostics: a heading binds to the text it introduces,
so declared space below it must not exceed the declared space above. -/
def rhythmChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let layoutDiags (styleBlock : String) : Array Diag :=
    let src := "\\documentclass{article}\\tokens{ u = 4pt }" ++ styleBlock ++
      "\\begin{document}\\section{Head}Body\\end{document}"
    (Layout.run ({} : Layout.Geom) oneFace none (Elab.run "t" src).1).diags
  t "heading below-heavy spacing warns"
    ((layoutDiags "\\style{section}{ before = u, after = 2 * u }").any (·.code == "W0202"))
  t "heading above-heavy spacing is silent"
    (!(layoutDiags "\\style{section}{ before = 2 * u, after = u }").any (·.code == "W0202"))
  t "heading equal spacing is silent"
    (!(layoutDiags "\\style{section}{ before = u, after = u }").any (·.code == "W0202"))
  t "an undeclared side is not compared"
    (!(layoutDiags "\\style{section}{ after = 2 * u }").any (·.code == "W0202"))

/-- The `card` document class: trade-standard trim sizes, print safe-zone
margins, no hyphenation, no running furniture, bleed on request. -/
def cardChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (pats : Hyphen.Patterns) : IO Unit := do
  let t := check ref
  let card (opts body : String) (pre : String := "") : String :=
    s!"\\documentclass{opts}\{card}\n{pre}\\begin\{document}\n{body}\n\\end\{document}"
  let (cDoc, cDs) := elabStr (card "" "Pat Placeholder")
  t "card class parses clean" (!cDs.any (·.severity == .error))
  -- ISO/IEC 7810 ID-1, the size most business cards follow: 85.60 × 53.98 mm.
  t "card defaults to ISO/IEC 7810 ID-1"
    (cDoc.page.width == Dim.mm100 8560 && cDoc.page.height == Dim.mm100 5398)
  t "us option is the 3.5 × 2 in trade size"
    ((elabStr (card "[us]" "x")).1.page.width == Dim.pt 252 &&
     (elabStr (card "[us]" "x")).1.page.height == Dim.pt 144)
  t "jis option is the 91 × 55 mm meishi"
    ((elabStr (card "[jis]" "x")).1.page.width == Dim.mm 91 &&
     (elabStr (card "[jis]" "x")).1.page.height == Dim.mm 55)
  -- Margins default to the print safe zone: content there risks the trim.
  t "card margins default to the safe zone"
    (cDoc.page.hmargin == Dim.mm 5 && cDoc.page.vmargin == Dim.mm 5)
  t "a declared page beats the card defaults"
    ((elabStr (card "" "x" "\\page{ width = 100pt, height = 60pt, margin = 4pt }\n")).1.page.width
      == Dim.pt 100)
  t "card turns hyphenation off by default"
    (cDoc.page.hyphenate == some false)
  -- Below the 40-character working minimum for justified text the measure
  -- is set ragged (Bringhurst): forcing justification at card width gives
  -- the breaker only overfull answers.
  t "card sets ragged by default" (cDoc.page.justify == some false)
  t "justify is a page key any class may declare"
    ((elabStr "\\page{ justify = off }\\begin{document}x\\end{document}").1.page.justify
      == some false)
  let prose := String.intercalate " " (List.replicate 20 "placeholder words")
  let judgeOverfull (pre : String) : Bool :=
    let doc := (elabStr (card "" prose pre)).1
    let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace none doc
    out.diags.any (·.code == "W0005")
  t "ragged card prose breaks without overfull lines" (!judgeOverfull "")
  t "the same prose justified at card width cannot break"
    (judgeOverfull "\\page{ justify = on }\n")
  t "article leaves hyphenation to the class default"
    ((elabStr "x").1.page.hyphenate == none)
  t "hyphenate is a page key any class may declare"
    ((elabStr "\\page{ hyphenate = off }\\begin{document}x\\end{document}").1.page.hyphenate
      == some false)
  t "hyphenate rejects a value that is not on or off"
    (errCodes "\\page{ hyphenate = 5pt }\\begin{document}x\\end{document}" == ["E0323"])
  -- The gate lives in layout: the same narrow measure hyphenates as an
  -- article and must not as a card, whoever loaded the patterns.
  let hyphenRendered (doc : Ir.Doc) : Bool :=
    let out := Layout.run (Layout.Geom.ofPage doc.page) oneFace (some pats) doc
    out.pages.any fun p => p.lines.any fun l =>
      l.segs.any fun s => match s with
        | .run _ _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '-')
        | .gap _ | .rule .. | .image .. => false
  let narrowPage := "\\page{ width = 90pt, height = 400pt, margin = 10pt }\n"
  let word := "incomprehensibility incomprehensibility"
  t "an article at this measure does hyphenate"
    (hyphenRendered (elabStr (s!"{narrowPage}\\begin\{document}\n{word}\n\\end\{document}")).1)
  t "a card never hyphenates"
    (!hyphenRendered (elabStr (card "" word narrowPage)).1)
  -- A card carries no running furniture: the declaration is dropped loudly.
  let (rDoc, rDs) := elabStr (card "" "x" "\\runninghead{name \\pagenumber}\n")
  t "card drops running content with W0317"
    (rDs.any (·.code == "W0317") && rDoc.head.isNone)
  -- Two faces are two frames: one page each, through the same page-boundary
  -- mechanism every class shares.
  let two := card "" "\\begin{frame}front\\end{frame}\n\\begin{frame}back\\end{frame}"
  let (twoDoc, twoDs) := elabStr two
  t "card faces source clean" (!twoDs.any (·.severity == .error))
  t "two faces are two pages"
    ((Layout.run (Layout.Geom.ofPage twoDoc.page) oneFace none twoDoc).pages.size == 2)
  -- Bleed grows the medium and records the trim box; without it the page
  -- dictionaries stay exactly as they were.
  let (bDoc, bDs) := elabStr (card "" "x" "\\page{ bleed = 3mm }\n")
  t "bleed declaration is clean" (!bDs.any (·.severity == .error))
  t "bleed reaches the page spec" (bDoc.page.bleed == Dim.mm 3)
  let bGeom := Layout.Geom.ofPage bDoc.page
  let bOut := Layout.run bGeom oneFace none bDoc
  let bPdf := Pdf.write bGeom oneFace bOut.pages
  t "bleed writes a TrimBox 3mm in from the medium corner"
    (bytesContain bPdf "/TrimBox [8.504 8.504 251.15 161.518]")
  t "bleed grows the MediaBox by twice itself"
    (bytesContain bPdf "/MediaBox [0 0 259.654 170.022]")
  -- The ink shifts with the trim box: the first glyph sits at the margin
  -- measured from the trim corner (8.504 + 14.173 pt), not the medium corner.
  t "bleed shifts the content with the trim box"
    (bytesContain bPdf "1 0 0 1 22.677 ")
  let plainGeom := Layout.Geom.ofPage cDoc.page
  let plainPdf := Pdf.write plainGeom oneFace
    (Layout.run plainGeom oneFace none cDoc).pages
  t "no bleed, no TrimBox" (!bytesContain plainPdf "/TrimBox")
  -- What the class guarantees, stated as the assertions the engine already
  -- enforces. Declaring an assertion of the same form is intent and takes
  -- control of the bound.
  let cardAsserts (src : String) := (elabStr src).1.asserts
  let plainAsserts := cardAsserts (card "" "x")
  t "card implies its three guarantees"
    (plainAsserts.any (·.kind == .pages .le 1) &&
     plainAsserts.any (·.kind == .textInArea) &&
     plainAsserts.any (·.kind == .minXHeight Ir.cardXHeightFloor))
  t "two faces raise the fits bound" ((cardAsserts two).any (·.kind == .pages .le 2))
  t "declared intent silences the class default"
    (((cardAsserts (card "" "x" "\\assert{ pages <= 4 }\n")).filter
      (fun a => match a.kind with | .pages _ _ => true | _ => false)).size == 1)
  t "article never gets the card contract" ((elabStr "x").1.asserts.isEmpty)
  t "assert text.in_area is declarable anywhere"
    ((elabStr "\\assert{ text.in_area }\\begin{document}x\\end{document}").1.asserts.any
      (·.kind == .textInArea))
  t "assert text.xheight takes a dimension"
    ((elabStr "\\assert{ text.xheight >= 2mm }\\begin{document}x\\end{document}").1.asserts.any
      (·.kind == .minXHeight (Dim.mm 2)))
  t "assert text.xheight rejects a word"
    (errCodes "\\assert{ text.xheight >= wide }\\begin{document}x\\end{document}" == ["E0325"])
  -- Each guarantee fails on the card built to violate it, through the same
  -- judge-the-shipped-pages path the build uses.
  let judge (src : String) : Array Diag :=
    let doc := (elabStr src).1
    let geom := Layout.Geom.ofPage doc.page
    let out := Layout.run geom oneFace none doc
    Check.all (Check.Shipped.ofOut geom oneFace out true) doc.asserts
  let lorem := String.intercalate " " (List.replicate 60 "placeholder words fill the face")
  t "an over-full card fails its faces assertion"
    ((judge (card "" lorem)).any fun d => (d.message.splitOn "pages <= 1").length == 2)
  t "an unbreakable run past the safe margin fails text.in_area"
    ((judge (card "" ("W" ++ "".pushn 'm' 60))).any fun d =>
      (d.message.splitOn "text.in_area").length == 2 &&
      (d.message.splitOn "right margin").length == 2)
  t "tiny type fails the legibility floor"
    ((judge (card "" "{\\tiny Pat Placeholder}")).any fun d =>
      (d.message.splitOn "text.xheight").length == 2)
  t "a reasonable card passes its whole contract"
    ((judge (card "" "Pat Placeholder\\\\ {\\small pat@example.org}")).isEmpty)
  -- The card's base size resolves through the same PageSpec path every
  -- class uses: declared \page{fontsize} first, then the class option,
  -- then the shared 10pt base — never a card-private constant.
  t "card takes the shared base size" (cDoc.page.fontSize == Ir.baseFontSize)
  t "a card class option sets the base size through the shared path"
    ((elabStr (card "[12pt]" "x")).1.page.fontSize == Dim.pt 12)
  -- Contrast is the colour slice's contract, reused rather than restated:
  -- the pairing warning and its declared-intent silence reach a card
  -- through the same docDiags walk as every other class.
  t "an illegible card pairing earns the colour contract's W0315"
    ((warnCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette{ washed = #DDDDDD }\n")).contains "W0315")
  t "declared decorative intent silences it on a card too"
    (!(warnCodes (card "" "\\textcolor{washed}{faint}"
      "\\palette[decorative]{ washed = #DDDDDD }\n")).contains "W0315")

/-- Images: the decoders' verdicts over synthetic bytes and the shipped
fixtures, the sizing contract on placed pages, the placeholder path, the PDF
embedding, and the HTML emit. Decoder totality over truncations and random
bytes is fuzzed deeper in `scripts/img-fuzz.lean` (an oracle, not a
theorem). -/
def imageChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  -- Synthetic PNGs, byte by byte. The decoder reads structure, not CRCs or
  -- pixel data, so the CRC slots are zero and the IDAT payload arbitrary.
  let be32 (n : Nat) : List UInt8 :=
    [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
     UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]
  let chunk (tag : String) (data : List UInt8) : List UInt8 :=
    be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++
      [0, 0, 0, 0]
  let ihdr (w h bd ct interlace : Nat) : List UInt8 :=
    be32 w ++ be32 h ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, UInt8.ofNat interlace]
  let pngSig : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]
  let mkPng (chunks : List UInt8) : ByteArray := bytes (pngSig ++ chunks)
  let plain := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++ chunk "IDAT" [1, 2, 3] ++
    chunk "IEND" [])
  match Image.decodePng plain with
  | .error e => failures ref s!"png decode: {e}"
  | .ok inf =>
    t "png dimensions" (inf.pxW == 64 && inf.pxH == 40)
    t "png default density is one pixel per point"
      (inf.dpiX == 72 && inf.width == Dim.pt 64 && inf.height == Dim.pt 40)
    t "png space and depth" (inf.space == .rgb && inf.bitDepth == 8)
    t "png idat survives" (inf.data == bytes [1, 2, 3])
  -- pHYs at 5906 pixels per metre is 150 dpi to the spec's own rounding.
  let physed := mkPng (chunk "IHDR" (ihdr 64 40 8 2 0) ++
    chunk "pHYs" (be32 5906 ++ be32 5906 ++ [1]) ++ chunk "IDAT" [0] ++ chunk "IEND" [])
  t "png pHYs density read"
    (match Image.decodePng physed with
     | .ok inf => inf.dpiX == 150 && inf.width == Dim.pt 64 * 72 / 150
     | .error _ => false)
  -- Refusals and the decode path, each with its reason: 16-bit alpha and
  -- interlace refuse; 8-bit alpha really decodes — inflate, unfilter,
  -- split — and the alpha plane comes back as an SMask.
  t "png 16-bit alpha refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 16 6 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "16-bit").length == 2
     | .ok _ => false)
  -- 2×2 RGBA, row 0 filter None, row 1 filter Sub: known planes out.
  let rgbaRaw := bytes ([0, 10, 20, 30, 255, 40, 50, 60, 128] ++
    [1, 5, 5, 5, 7, 1, 2, 3, 9])
  let rgbaPng := mkPng (chunk "IHDR" (ihdr 2 2 8 6 0) ++
    chunk "IDAT" (Flate.deflateStored rgbaRaw).toList ++ chunk "IEND" [])
  t "png alpha decodes to colour plus smask"
    (match Image.decodePng rgbaPng with
     | .ok inf =>
       inf.space == .rgb && !inf.predictor && !inf.smask.isEmpty &&
       Flate.inflate inf.data 12 ==
         .ok (bytes [10, 20, 30, 40, 50, 60, 5, 5, 5, 6, 7, 8]) &&
       Flate.inflate inf.smask 4 == .ok (bytes [255, 128, 7, 16])
     | .error _ => false)
  -- The inflate under it round-trips its own stored encoder, and reads a
  -- real compressor's stream: rects.png's IDAT is zlib at level 9, and its
  -- unfiltered scanlines are 40 rows of 1+192 bytes.
  t "flate roundtrip on stored blocks"
    (Flate.inflate (Flate.deflateStored rgbaRaw) rgbaRaw.size == .ok rgbaRaw)
  t "png interlace refused"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 1) ++
      chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .error e => (e.splitOn "interlaced").length == 2
     | .ok _ => false)
  t "png indexed without PLTE refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png indexed with PLTE carries the palette"
    (match Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 3 0) ++
      chunk "PLTE" [0, 0, 0, 255, 255, 255] ++ chunk "IDAT" [0] ++ chunk "IEND" [])) with
     | .ok inf => inf.space == .indexed && inf.palette.size == 6
     | .error _ => false)
  t "png zero size refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 0 8 8 2 0) ++
      chunk "IDAT" [0] ++ chunk "IEND" []))).isOk == false)
  t "png lying chunk length refused"
    ((Image.decodePng (mkPng (chunk "IHDR" (ihdr 8 8 8 2 0) ++
      be32 99999 ++ ("IDAT".toList.map fun c => UInt8.ofNat c.toNat) ++ [0]))).isOk
      == false)
  -- A synthetic JPEG: SOI, JFIF APP0 declaring 144 dpi, SOF0 10×20 in three
  -- components, SOS. The scan data never has to exist for the header walk.
  let jfif (unit dx dy : Nat) : List UInt8 :=
    [0xFF, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, UInt8.ofNat unit,
     UInt8.ofNat (dx / 256), UInt8.ofNat (dx % 256),
     UInt8.ofNat (dy / 256), UInt8.ofNat (dy % 256), 0, 0]
  let sof0 (w h ncomp : Nat) : List UInt8 :=
    [0xFF, 0xC0, 0, UInt8.ofNat (8 + 3 * ncomp), 8,
     UInt8.ofNat (h / 256), UInt8.ofNat (h % 256),
     UInt8.ofNat (w / 256), UInt8.ofNat (w % 256), UInt8.ofNat ncomp] ++
     (List.range ncomp).flatMap fun k => [UInt8.ofNat (k + 1), 0x11, 0]
  let jpg := bytes ([0xFF, 0xD8] ++ jfif 1 144 144 ++ sof0 10 20 3 ++ [0xFF, 0xDA])
  match Image.decodeJpeg jpg with
  | .error e => failures ref s!"jpeg decode: {e}"
  | .ok inf =>
    t "jpeg dimensions" (inf.pxW == 10 && inf.pxH == 20)
    t "jpeg jfif density read" (inf.dpiX == 144 && inf.width == Dim.pt 10 * 72 / 144)
    t "jpeg embeds whole" (inf.data.size == jpg.size)
  t "jpeg cmyk refused"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ sof0 4 4 4 ++ [0xFF, 0xDA])) with
     | .error e => (e.splitOn "CMYK").length == 2
     | .ok _ => false)
  t "jpeg aspect-only density keeps the default"
    (match Image.decodeJpeg (bytes ([0xFF, 0xD8] ++ jfif 0 1 1 ++ sof0 4 4 1 ++
      [0xFF, 0xDA])) with
     | .ok inf => inf.dpiX == 72 && inf.space == .gray
     | .error _ => false)
  t "decode rejects foreign bytes" ((Image.decode (bytes [0, 1, 2, 3])).isOk == false)
  t "decode rejects empty" ((Image.decode (bytes [])).isOk == false)

  -- The shipped fixtures: what `lake test` sees on every host.
  let pngData ← IO.FS.readBinFile "tests/corpus/rects.png"
  let jpgData ← IO.FS.readBinFile "tests/corpus/rects.jpg"
  let alphaData ← IO.FS.readBinFile "tests/corpus/rects-alpha.png"
  let pngInfo := Image.decode pngData
  let jpgInfo := Image.decode jpgData
  let alphaInfo := Image.decode alphaData
  t "shipped png decodes 64x40 rgb"
    (match pngInfo with
     | .ok inf => inf.format == .png && inf.pxW == 64 && inf.pxH == 40 &&
        inf.space == .rgb && inf.width == Dim.pt 64
     | .error _ => false)
  t "shipped jpeg decodes 64x40"
    (match jpgInfo with
     | .ok inf => inf.format == .jpeg && inf.pxW == 64 && inf.pxH == 40 &&
        inf.width == Dim.pt 64
     | .error _ => false)
  -- The RGBA fixture went through a real compressor (zlib level 9), so
  -- decoding it exercises the Huffman paths of the inflater; its alpha
  -- fades 255 down to 15 across the rectangle and vanishes outside it.
  t "shipped alpha png decodes with its mask"
    (match alphaInfo with
     | .ok inf =>
       inf.pxW == 48 && inf.pxH == 32 && inf.space == .rgb && !inf.smask.isEmpty &&
       (match Flate.inflate inf.smask (48 * 32) with
        | .ok mask => mask.size == 48 * 32 && mask[0]?.getD 1 == 0 &&
            (mask[4 * 48 + 4]?.getD 0) == 255 && (mask[4 * 48 + 43]?.getD 0) == 21
        | .error _ => false)
     | .error _ => false)
  -- Totality over truncations of both, as for fonts: reaching the count is
  -- the property — a panic would take the run down.
  t "png decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (pngData.extract 0 (pngData.size * k / 64))).isOk).length == 64)
  t "jpeg decode total over truncations"
    (((List.range 64).map fun k =>
      (Image.decode (jpgData.extract 0 (jpgData.size * k / 64))).isOk).length == 64)

  let store : Image.Store := { entries := #[
    { src := "rects.png", info := pngInfo.toOption },
    { src := "rects.jpg", info := jpgInfo.toOption },
    { src := "rects-alpha.png", info := alphaInfo.toOption }] }
  let geom : Layout.Geom := {}
  let imageSegs (out : Layout.Out) : Array (Option Nat × Dim.Sp × Dim.Sp) := Id.run do
    let mut acc : Array (Option Nat × Dim.Sp × Dim.Sp) := #[]
    for p in out.pages do
      for l in p.lines do
        for s in l.segs do
          if let .image idx w h := s then acc := acc.push (idx, w, h)
    return acc
  let layoutOf (src : String) : Layout.Out :=
    let (doc, _) := Elab.run "t" src
    Layout.run geom oneFace none doc store

  -- Intrinsic: no keys, the box is the file's physical size.
  let outIntrinsic := layoutOf "\\includegraphics{rects.png}"
  t "layout intrinsic size"
    (imageSegs outIntrinsic == #[(some 0, Dim.pt 64, Dim.pt 40)])
  -- `width = 0.8\textwidth`: the spelling every deck sizes a figure with.
  let outTw := layoutOf "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let expectW := geom.textWidth * 800 / 1000
  t "layout width fraction of the measure"
    (imageSegs outTw == #[(some 0, expectW, expectW * Dim.pt 40 / Dim.pt 64)])
  -- Both dimensions declared win exactly.
  let outBoth := layoutOf "\\includegraphics[width=32pt, height=40pt]{rects.png}"
  t "layout declared size wins"
    (imageSegs outBoth == #[(some 0, Dim.pt 32, Dim.pt 40)])
  -- keepaspectratio fits inside the declared box: width binds (the image is
  -- wider than tall), the height follows the intrinsic ratio.
  let outKeep :=
    layoutOf "\\includegraphics[width=32pt, height=32pt, keepaspectratio]{rects.jpg}"
  t "layout keepaspect fits the box"
    (imageSegs outKeep == #[(some 1, Dim.pt 32, Dim.pt 32 * 40 / 64)])
  -- A source the store has no entry for is a placeholder box: the document
  -- still compiles, at the requested size.
  let outMissing := layoutOf "\\includegraphics[width=50pt]{missing.png}"
  t "layout missing image keeps requested width"
    (imageSegs outMissing == #[(none, Dim.pt 50, Dim.pt 50)] &&
     outMissing.pages.size == 1)
  t "layout missing image without a size is an inch square"
    (imageSegs (layoutOf "\\includegraphics{missing.png}") ==
      #[(none, Dim.inch 1, Dim.inch 1)])

  -- The figure environment: a float standing where written, the caption on
  -- its source side (below here) and the alt of the image it captions.
  let (figDoc, figDiags) := Elab.run "t"
    "\\begin{figure}[t]\\centering\\includegraphics{rects.png}\\caption{A mark}\\end{figure}"
  t "figure elaborates with its placement registered as a note"
    (figDiags.all (·.severity == .note) && figDiags.any (·.code == "N0102"))
  t "figure elaborates to a float carrying its caption"
    (match figDoc.body.toList with
     | [.float .figure false inner cap] =>
       match inner.toList with
       | [.para xs] =>
         (xs.any fun x => match x with
           | .image "rects.png" _ alt => alt == "A mark"
           | _ => false) &&
         Ir.plainText cap == "A mark"
       | _ => false
     | _ => false)
  t "figure image reaches the page"
    ((imageSegs (Layout.run geom oneFace none figDoc store)).size == 1)
  -- An image in a slide: the frame's page carries it.
  let (slideDoc, _) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\begin{frame}{T}\\includegraphics{rects.png}\\end{frame}\\end{document}"
  let slideGeom := Layout.Geom.ofPage slideDoc.page
  t "slide image reaches the frame page"
    ((imageSegs (Layout.run slideGeom oneFace none slideDoc store)).size == 1)
  -- The deck logo: same image node, placed at the lower-right corner of
  -- every page, its right edge on the margin.
  let (logoDoc, logoDiags) := Elab.run "t"
    "\\documentclass{slides}\\logo{\\includegraphics[height=8pt]{rects.png}}\
\\begin{document}\\begin{frame}{A}x\\end{frame}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declaration elaborates clean" (logoDiags.isEmpty)
  let logoGeom := Layout.Geom.ofPage logoDoc.page
  let logoOut := Layout.run logoGeom oneFace none logoDoc store
  let logoW := Dim.pt 8 * Dim.pt 64 / Dim.pt 40
  t "logo placed on every page at the right margin"
    (logoOut.pages.size == 2 && logoOut.pages.all fun p =>
      p.lines.any fun l =>
        l.x + l.setWidth == logoGeom.pageW - logoGeom.hmargin &&
        l.segs.any fun s => match s with
          | .image _ w h => w == logoW && h == Dim.pt 8
          | _ => false)

  -- The PDF: an XObject per used image, painted by a cm+Do pair; the xref
  -- theorem-test still holds with the new objects in the file.
  let (pdfDoc, _) := Elab.run "t"
    "\\includegraphics{rects.png} and \\includegraphics{rects.jpg} and \
\\includegraphics{rects-alpha.png}"
  let pdfOut := Layout.run geom oneFace none pdfDoc store
  let pdf := Pdf.write geom oneFace pdfOut.pages {} store
  t "pdf embeds the png as flate with the predictor"
    (bytesContain pdf "/Subtype /Image" && bytesContain pdf "/FlateDecode" &&
     bytesContain pdf "/Predictor 15")
  t "pdf embeds the jpeg as dct" (bytesContain pdf "/DCTDecode")
  t "pdf gives the alpha image a soft mask" (bytesContain pdf "/SMask")
  t "pdf paints all three images" (bytesContain pdf "/Im1 Do" &&
    bytesContain pdf "/Im2 Do" && bytesContain pdf "/Im3 Do")
  -- The cm matrix must carry the placed size: a Do behind a degenerate
  -- matrix is a blank box that every structural check would miss.
  t "pdf image matrix carries the placed size"
    (bytesContain pdf "q 64 0 0 40 ")
  t "pdf page resources name the xobjects" (bytesContain pdf "/XObject <<")
  match checkXref pdf with
  | .ok n => t "pdf xref valid with images" (n > 0)
  | .error e => failures ref s!"pdf xref with images: {e}"
  -- The raw IDAT bytes must reach the file unchanged: the stream is the
  -- pass-through, not a re-encoding.
  let containsBytes (hay needle : ByteArray) : Bool := Id.run do
    if needle.size == 0 || hay.size < needle.size then return false
    for i in [0:hay.size - needle.size + 1] do
      let mut ok := true
      for j in [0:needle.size] do
        if hay[i + j]! != needle[j]! then
          ok := false
          break
      if ok then return true
    return false
  t "pdf carries the png stream verbatim"
    (match pngInfo with
     | .ok inf => containsBytes pdf inf.data
     | .error _ => false)
  -- The placeholder: an outlined box, no image object, a valid file.
  let missOut := Layout.run geom oneFace none
    ((Elab.run "t" "\\includegraphics[width=50pt]{missing.png}").1) store
  let missPdf := Pdf.write geom oneFace missOut.pages {} store
  t "pdf placeholder draws an outline, embeds nothing"
    (bytesContain missPdf "re S" && !(bytesContain missPdf "/Subtype /Image"))
  match checkXref missPdf with
  | .ok _ => pure ()
  | .error e => failures ref s!"pdf xref with placeholder: {e}"

  -- The HTML: an <img> through the typed tree, intrinsic pixel size as
  -- attributes so the page never reflows, the caption as alt, the requested
  -- fraction as a percentage.
  let hcfg : HtmlDoc.Config := { imgs := store }
  let (figHtml, _) := HtmlDoc.emit hcfg figDoc
  t "html figure image with alt and intrinsic size"
    ((figHtml.splitOn "<img src=\"rects.png\" alt=\"A mark\" width=\"64\" height=\"40\">").length == 2)
  let (twDoc, _) := Elab.run "t" "\\includegraphics[width=0.8\\textwidth]{rects.png}"
  let (twHtml, _) := HtmlDoc.emit hcfg twDoc
  t "html width fraction becomes a percentage"
    ((twHtml.splitOn "style=\"width: 80%; height: auto\"").length == 2)
  let (missHtml, _) := HtmlDoc.emit hcfg
    ((Elab.run "t" "\\includegraphics{missing.png}").1)
  t "html missing image still emits the img with alt"
    ((missHtml.splitOn "<img src=\"missing.png\"").length == 2)

  -- The surface diagnostics: a length that does not parse, an option the
  -- engine does not model.
  t "includegraphics bad length is E0331"
    (errCodes "\\includegraphics[width=banana]{x.png}" == ["E0331"])
  t "includegraphics em length is E0331"
    (errCodes "\\includegraphics[width=2em]{x.png}" == ["E0331"])
  t "includegraphics unknown option warns W0110"
    (warnCodes "\\includegraphics[angle=45]{x.png}" == ["W0110"])
  t "includegraphics without a file group is E0304"
    (errCodes "\\includegraphics[width=3cm]" == ["E0304"])
  -- totalheight is height plus depth and an image has no depth: one key.
  t "includegraphics totalheight is height"
    (match (elabStr "\\includegraphics[totalheight=8pt]{x.png}").1.body.toList with
     | [.para xs] => xs.any fun x => match x with
        | .image _ spec _ => spec.height == some { sp := Dim.pt 8 }
        | _ => false
     | _ => false)
  -- \logo is a declaration in the body too, and it is stateful there, as
  -- in beamer: a deck scopes a logo to one frame with `\logo{...}` before
  -- it and `\logo{}` after.
  let (bodyLogoDoc, bodyLogoDiags) := Elab.run "t"
    "\\documentclass{slides}\\begin{document}\\logo{\\includegraphics[height=8pt]{rects.png}}\
\\begin{frame}{A}x\\end{frame}\\logo{}\\begin{frame}{B}y\\end{frame}\\end{document}"
  t "logo declared in the body binds" (bodyLogoDiags.isEmpty && bodyLogoDoc.logo.isNone)
  let blOut := Layout.run (Layout.Geom.ofPage bodyLogoDoc.page) oneFace none
    bodyLogoDoc store
  let pageHasImage (p : Layout.PageOut) : Bool :=
    p.lines.any fun l => l.segs.any fun s => match s with
      | .image .. => true
      | _ => false
  t "body logo scopes to its frame's page"
    (blOut.pages.size == 2 && pageHasImage blOut.pages[0]! &&
     !pageHasImage blOut.pages[1]!)
  -- A bare graphicx name gains the extension the file on disk has; the
  -- candidate order tries the name as written first.
  t "source candidates try the written name first"
    ((Image.sourceCandidates "figures/plot").take 2 ==
      ["figures/plot", "figures/plot.png"])
  t "html names the resolved file, not the bare spelling"
    (let store2 : Image.Store := { entries := #[
      { src := "figures/plot", href := "figures/plot.png", info := pngInfo.toOption }] }
     let (h, _) := HtmlDoc.emit { imgs := store2 }
       ((Elab.run "t" "\\includegraphics{figures/plot}").1)
     (h.splitOn "<img src=\"figures/plot.png\"").length == 2)

/-- The picture block through layout: shapes land as fills and label runs
through one `Pic.Place` transform. The transform and bounding-box facts are
theorems (`Pic.Place.ofPage_toPage`, `Pic.Picture.box_in_bbox`); what is
checked here is the placement they license — where the box lands, that the
label centres on its anchor, that `{center}` centres the box, and that
W0335 fires when the box cannot fit the text area (the diagnostic half of
the stays-in-its-box contract). -/
def pictureLayoutChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let geom : Layout.Geom := {}
  let red : Ir.Color := { r := 200, g := 40, b := 40 }
  let pic : Ir.Pic.Picture := { shapes := #[
    .rect 0 0 (Dim.pt 20) (Dim.pt 10) red,
    .label (Dim.pt 10) (Dim.pt 5) "7" Ir.Color.black 800] }
  t "picture bbox joins its shapes"
    (pic.bbox == ((0, 0), (Dim.pt 20, Dim.pt 10)))
  let run (body : Array Ir.Block) : Layout.Out :=
    Layout.run geom oneFace none { body := body }
  let out := run #[.picture pic]
  t "picture ships one page" (out.pages.size == 1)
  t "picture rect ships as one fill of its own size and colour"
    ((out.pages[0]?.bind fun p => p.fills[0]?.map fun f =>
      p.fills.size == 1 && f.x == geom.hmargin && f.y == geom.vmargin &&
      f.w == Dim.pt 20 && f.h == Dim.pt 10 && f.color == red).getD false)
  t "picture label ships its glyphs centred on the anchor"
    ((out.pages[0]?.map fun p =>
      match p.lines.toList with
      | [l] =>
        (match l.segs.toList with
         | [Layout.Seg.run _ _ _ _ glyphs _ _ _] =>
           String.ofList (glyphs.toList.map (·.2)) == "7"
         | _ => false)
        && l.x + l.setWidth / 2 == geom.hmargin + Dim.pt 10
      | _ => false).getD false)
  -- A fills-only picture is page content: the page ships.
  let bare := run #[.picture { shapes := #[.rect 0 0 (Dim.pt 5) (Dim.pt 5) red] }]
  t "a picture of fills alone still ships its page"
    ((bare.pages[0]?.map fun p => p.fills.size == 1).getD false)
  -- `{center}` centres the box, as it centres a paragraph's lines.
  let centered := run #[.center #[.picture pic]]
  t "a centred picture centres its box"
    ((centered.pages[0]?.bind fun p => p.fills[0]?.map fun f =>
      f.x == geom.hmargin + (geom.textWidth - Dim.pt 20) / 2).getD false)
  -- The diagnostic half of the contract: a box the text area cannot hold.
  let wide := run #[.picture { shapes :=
    #[.rect 0 0 (geom.textWidth + Dim.pt 50) (Dim.pt 10) red] }]
  t "a picture wider than the text area warns W0335"
    (wide.diags.any (·.code == "W0335"))
  t "a fitting picture does not warn W0335"
    (!out.diags.any (·.code == "W0335"))

/-- The picture subset's boundary is named, never silent: a construct
outside the subset is W0334 naming it, an unreadable expression, range, or
colour inside it is E0333 — and the supported shapes around either still
elaborate (the nothing-silently-skipped contract, as a test). The unroll
and arithmetic facts are checked through the IR the elaborator ships. -/
def pictureElabChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String :=
    "\\palette{ grid = #2A6F4E }\\begin{document}\\begin{tikzpicture}" ++
    body ++ "\\end{tikzpicture}\\end{document}"
  let picOf (src : String) : Option Ir.Pic.Picture :=
    (elabStr src).1.body.findSome? fun b => match b with
      | .picture p => some p
      | _ => none
  let cm := Dim.mm 10
  t "a foreach of fills unrolls to exactly its range's count"
    ((picOf (wrap "\\foreach \\x in {1,...,3}{\\fill (\\x,0) rectangle ++(1,1);}")).map
      (·.shapes.size) == some 3)
  t "the pair form binds both variables"
    ((picOf (wrap "\\foreach \\k/\\lbl in {1/aa,2/bb}{\\node at (\\k,0) {\\lbl};}")).map
      (·.shapes) == some #[.label cm 0 "aa" Ir.Color.black 1000,
                           .label (2 * cm) 0 "bb" Ir.Color.black 1000])
  t "truncatemacro floors to a whole unit"
    ((picOf (wrap "\\pgfmathtruncatemacro{\\k}{7/2}\\fill (0,0) rectangle (\\k,1);")).map
      (·.shapes) == some #[.rect 0 0 (3 * cm) cm Ir.Color.black])
  t "ifthenelse picks its branch by the comparison"
    ((picOf (wrap "\\foreach \\k in {1,2}{\
\\pgfmathsetmacro{\\c}{ifthenelse(\\k<2,\"black\",\"white\")}\
\\node[text=\\c] at (\\k,0) {x};}")).map
      (·.shapes) == some #[.label cm 0 "x" Ir.Color.black 1000,
                           .label (2 * cm) 0 "x" Ir.Color.white 1000])
  t "max and * evaluate inside a coordinate"
    ((picOf (wrap "\\fill (0,0) rectangle (max(1,2)*2, 1);")).map (·.shapes) ==
      some #[.rect 0 0 (4 * cm) cm Ir.Color.black])
  t "scale= scales every coordinate"
    ((picOf (wrap "[scale=0.5]\\fill (0,0) rectangle (2,2);")).map (·.shapes) ==
      some #[.rect 0 0 cm cm Ir.Color.black])
  t "a relative corner adds to its anchor"
    ((picOf (wrap "\\fill (1,1) rectangle ++(1,1);")).map (·.shapes) ==
      some #[.rect cm cm cm cm Ir.Color.black])
  t "a construct outside the subset is W0334, and the rest still draws"
    (warnCodes (wrap "\\draw (0,0) circle (1);\\fill (0,0) rectangle (1,1);") ==
        ["W0334"] &&
      (picOf (wrap "\\draw (0,0) circle (1);\\fill (0,0) rectangle (1,1);")).map
        (·.shapes.size) == some 1)
  t "a zero-step range is E0333, not a hang"
    (errCodes (wrap "\\foreach \\x in {1,1,...,5}{\\fill (\\x,0) rectangle ++(1,1);}") ==
      ["E0333"])
  t "a range walking away from its bound is E0333"
    (errCodes (wrap "\\foreach \\x in {5,4,...,9}{\\fill (\\x,0) rectangle ++(1,1);}") ==
      ["E0333"])
  t "division by zero is E0333 and loses only its shape"
    (errCodes (wrap "\\fill (1/0,0) rectangle (1,1);\\fill (0,0) rectangle (1,1);") ==
        ["E0333"] &&
      (picOf (wrap "\\fill (1/0,0) rectangle (1,1);\\fill (0,0) rectangle (1,1);")).map
        (·.shapes.size) == some 1)
  t "an unknown colour is E0333 naming the spelling"
    ((elabStr (wrap "\\fill[nosuch!30] (0,0) rectangle (1,1);")).2.any fun d =>
      d.code == "E0333" && hasStr d.message "nosuch!30")
  t "an unknown macro is E0333"
    (errCodes (wrap "\\fill (\\nope,0) rectangle (1,1);") == ["E0333"])
  t "an unsupported node option loses only the option"
    (warnCodes (wrap "\\node[draw] at (1,1) {x};") == ["W0334"] &&
      (picOf (wrap "\\node[draw] at (1,1) {x};")).map (·.shapes.size) == some 1)
  t "one construct looped forty times is one diagnostic, not forty"
    (warnCodes (wrap "\\foreach \\x in {1,...,40}{\\draw (\\x,0) circle (1);}") ==
      ["W0334"])
  t "an empty tikzpicture ships no block and no diagnostic"
    ((elabStr (wrap "")).2.isEmpty && (picOf (wrap "")).isNone)

/-- The block half of `role_transparent_layout`, pinned executably: a role
ships exactly the pages its content ships unwrapped — zero PDF bytes move.
An oracle over `Layout.run` and `Pdf.write`, not a theorem: the collector's
match resists equation-lemma generation (see the note beside its `.role`
arm), so the fact is held here, over the shipped bytes themselves. -/
def roleLayoutChecks (ref : IO.Ref (List String)) (geom : Layout.Geom)
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let wrapped : Ir.Doc := { body := #[.role "entry"
    #[.para #[.role "muted" #[.text "quiet"], .text " words"]]] }
  let plain : Ir.Doc := { body := #[.para #[.text "quiet", .text " words"]] }
  let out1 := Layout.run geom oneFace none wrapped
  let out2 := Layout.run geom oneFace none plain
  t "a role ships zero PDF bytes"
    ((Pdf.write geom oneFace out1.pages).data == (Pdf.write geom oneFace out2.pages).data)

def fontSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pats := Hyphen.load
  -- font parsing on the system font
  match ← findFont with
  | none =>
    failures ref s!"font: {testFonts}/OpenSans-Regular.ttf missing from the checkout"
  | some fontData =>
    match Font.parse fontData with
    | .error e => failures ref s!"font parse: {e}"
    | .ok font =>
      t "font name" (font.psName == "OpenSans-Regular")
      t "font upem" (font.unitsPerEm == 2048)
      t "font gid A" (font.gid 'A' |>.isSome)
      t "font advance A" (font.advance 'A' > 0)
      t "font greek" (font.gid 'α' |>.isSome)
      t "font missing emoji" (font.gid '🎉' |>.isNone)
      t "font family" (font.family == "Open Sans")
      t "font cap height from OS/2" (font.capHeight == 1462)
      t "font not bold" (!font.isBold && !font.isItalic)

      -- A parser is fed arbitrary files, so it has to be total over them. Every
      -- byte read used to go through `b[i]!`, which aborts the process: one
      -- font in a TeX Live tree took the whole run down with it.
      t "font parse rejects garbage"
        ((Font.parse (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])).isOk == false)
      t "font parse rejects an empty file" ((Font.parse (ByteArray.mk #[])).isOk == false)
      -- Truncation at every length must return a verdict rather than abort.
      -- Reaching the assertion at all is the property: a panic would take the
      -- whole run down. Some truncations parse legitimately -- the metrics
      -- tables can all survive when only glyph data is lost.
      let verdicts := (List.range 64).map fun k =>
        (Font.parse (fontData.extract 0 (fontData.size * k / 64))).isOk
      t "font parse is total over truncations" (verdicts.length == 64)
      t "font parse rejects short truncations" (verdicts.take 8 |>.all (· == false))
      -- A valid font with a table header claiming more than the file holds.
      let lying := Id.run do
        let mut b := fontData.extract 0 (min fontData.size 4096)
        -- the first table entry's length field, made absurd
        for i in [0:4] do
          b := b.set! (12 + 12 + i) 0x7f
        return b
      t "font parse rejects a table that overruns the file"
        ((Font.parse lying).isOk == false)
      -- `classify` is what a family scan uses, and it must agree with `parse`
      -- about what a face is called. It used to be `parse` fed a sparse image
      -- with the metric tables missing, which is how the scan read out of
      -- bounds in the first place.
      match Font.classify fontData with
      | .error e => failures ref s!"font classify: {e}"
      | .ok c =>
        t "classify agrees with parse on family" (c.family == font.family)
        t "classify agrees with parse on subfamily" (c.subfamily == font.subfamily)
        t "classify agrees with parse on style"
          (c.isBold == font.isBold && c.isItalic == font.isItalic &&
           c.weight == font.weight && c.isFixedPitch == font.isFixedPitch)
      t "classify is total over truncations"
        (((List.range 64).map fun k =>
          (Font.classify (fontData.extract 0 (fontData.size * k / 64))).isOk).length == 64)

      -- A one-face set: every slot and variant maps to index 0.
      let oneFace : Font.FontSet := {
        fonts := #[font]
        index := ((List.range 3).flatMap fun slot =>
          [((slot, false, false), 0), ((slot, true, false), 0),
           ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
      }
      t "fontset lookup body" (oneFace.lookup 0 false false == 0)
      t "fontset lookup falls back" (oneFace.lookup 2 true true == 0)

      -- layout: hyphenation is materialized only at a chosen break; headings
      -- and list markers carry visual structure into the positioned page.
      let (hyDoc, hyDs) := Elab.run "t" "incomprehensibility"
      t "layout hyphen source clean" hyDs.isEmpty
      let narrow : Layout.Geom := {
        pageW := Dim.pt 90
        pageH := Dim.pt 200
        hmargin := Dim.pt 10
        vmargin := Dim.pt 10
        fontSize := Dim.pt 10
      }
      let hyOut := Layout.run narrow oneFace (some pats) hyDoc
      let hyphenRendered := hyOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '-')
          | .gap _ | .rule .. | .image .. => false
      t "layout chosen hyphen renders" (hyOut.pages[0]!.lines.size > 1 && hyphenRendered)
      -- Display type never hyphenates (Butterick, "Hyphenation"): the same
      -- word that hyphenates as body text must set unbroken as a heading,
      -- a frame title, and the document title, patterns loaded or not.
      let hyphens (doc : Ir.Doc) : Bool :=
        (Layout.run narrow oneFace (some pats) doc).pages.any fun p =>
          p.lines.any fun l => l.segs.any fun s => match s with
            | .run _ _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '-')
            | .gap _ | .rule .. | .image .. => false
      t "a heading never hyphenates"
        (!hyphens (Elab.run "t" "\\section{incomprehensibility}").1)
      t "a frame title never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\begin{frame}{incomprehensibility}x\\end{frame}\\end{document}")).1)
      t "the title page never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\title{incomprehensibility}\\maketitle\\end{document}")).1)
      -- Display type sets ragged: justification without hyphenation would
      -- stretch a short display line across the whole measure (Butterick,
      -- "Justified text"; moloch's title templates are \raggedright).
      let (jhDoc, _) := Elab.run "t"
        "\\section{one two six ten oak elm fir ash}\n\nbody text"
      let headLines := (Layout.run narrow oneFace (some pats) jhDoc).pages.flatMap
        (·.lines) |>.filter (·.size == Layout.sectionSize narrow 1)
      t "a wrapped heading is ragged, not justified"
        (headLines.size ≥ 2 && headLines.all (·.setWidth < narrow.textWidth))
      t "layout hyphen avoids overfull" (!hyOut.diags.any (·.code == "W0005"))
      -- Scale must survive the dedup: W0005 is spanless, so the count is
      -- the only signal of how much of the document overflowed.
      let (ofDoc, _) := Elab.run "t"
        "aaaaaaaaaaaaaaaaaaaaaaaaaa\n\nbbbbbbbbbbbbbbbbbbbbbbbbbb"
      let ofOut := Layout.run narrow oneFace none ofDoc
      t "overfull warning carries the count"
        ((ofOut.diags.filter (·.code == "W0005")).size == 1 &&
         ofOut.diags.any (·.message == "2 overfull lines (no feasible break)"))

      let visualSrc := "\\section{Heading}\nBody text.\n\n" ++
        "\\begin{itemize}\\item A list item.\\end{itemize}"
      let (visualDoc, visualDs) := Elab.run "t" visualSrc
      t "layout visual source clean" visualDs.isEmpty
      let visualOut := Layout.run ({} : Layout.Geom) oneFace (some pats) visualDoc
      let hasSectionSize := visualOut.pages.any fun p =>
        p.lines.any (·.size == Layout.sectionSize ({} : Layout.Geom) 1)
      let hasListMarker := visualOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '•')
          | .gap _ | .rule .. | .image .. => false
      t "layout section size" hasSectionSize
      t "layout list marker" hasListMarker

      -- pdf: build a tiny document and re-verify the xref stream offsets
      let (doc, eds) := Elab.run "t" "hello world, a small pdf self check"
      t "pdf source clean" eds.isEmpty
      let geom : Layout.Geom := {}
      let out := Layout.run geom oneFace none doc
      t "pdf one page" (out.pages.size == 1)
      let pdf := Pdf.write geom oneFace out.pages
      t "pdf header" (String.fromUTF8! (pdf.extract 0 8) == "%PDF-2.0")
      t "pdf eof" (String.fromUTF8! (pdf.extract (pdf.size - 6) pdf.size) == "%%EOF\n")
      match checkXref pdf with
      | .ok n => t s!"pdf xref valid" (n > 0)
      | .error e => failures ref s!"pdf xref: {e}"

      pdfFaceChecks ref geom oneFace font
      webMetaChecks ref geom oneFace

      lineChecks ref geom oneFace
      listChecks ref oneFace font
      filChecks ref oneFace
      underlineChecks ref geom oneFace font
      linkSignalChecks ref geom oneFace
      inkGeometryChecks ref
      spacingChecks ref geom oneFace font
      slideChecks ref oneFace
      tableChecks ref oneFace
      recoveryChecks ref oneFace
      roleLayoutChecks ref geom oneFace
      vdistChecks ref geom oneFace
      headBandChecks ref oneFace
      cardChecks ref oneFace pats
      censusChecks ref oneFace pats
      bandChecks ref oneFace
      agreeChecks ref oneFace pats
      pictureLayoutChecks ref oneFace
      quoteChecks ref oneFace
      titleChecks ref
      outlineChecks ref
      columnsChecks ref oneFace
      overlayChecks ref oneFace
      overlayBlockChecks ref oneFace
      noteChecks ref oneFace
      themeFurnitureChecks ref oneFace
      themeReconcileChecks ref oneFace
      chromeDeclChecks ref
      footerBandChecks ref oneFace
      chromeFooterChecks ref oneFace
      numberingChecks ref oneFace
      frameFootChecks ref oneFace
      scannerChecks ref
      rhythmChecks ref oneFace
      measureChecks ref oneFace
      imageChecks ref oneFace

/-- M6's first slice, pinned end to end: the MATH constants read from the
shipped face, the box-is-box widths in sp (a math box's advance is the sum
of its atoms plus the spacing the table gives — recomputed here from the
font's own advances, sharing nothing with the layout walk), script sizes
and shifts from the constants, Bin degradation, script-style spacing
suppression, the italic/upright convention, and that nothing is silently
dropped: a glyph the math face lacks earns E0405 naming it, a document with
no math face earns one W0003 and its formulas set as source text, and every
out-of-scope construct earns a W0010 naming it while its source survives. -/
def mathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math: {name} unparsable: {e}")
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraMath-Regular.otf"
  -- The MATH table parses to the face's own constants (read independently
  -- with a struct-unpacking script against the OpenType spec offsets).
  t "text faces carry no MATH table" serif.math.isNone
  t "fira math constants" (fira.math == some {
    scales := { script := 72, scriptscript := 58 }
    axisHeight := 280
    subscriptShiftDown := 350
    superscriptShiftUp := 400
    superscriptShiftUpCramped := 270
    spaceAfterScript := 41
    displayOperatorMinHeight := 1500
    upperLimitGapMin := 150
    upperLimitBaselineRiseMin := 150
    lowerLimitGapMin := 150
    lowerLimitBaselineDropMin := 600
    fractionNumeratorShiftUp := 450
    fractionNumeratorDisplayStyleShiftUp := 580
    fractionDenominatorShiftDown := 480
    fractionDenominatorDisplayStyleShiftDown := 700
    fractionNumeratorGapMin := 80
    fractionNumDisplayStyleGapMin := 200
    fractionRuleThickness := 76
    fractionDenominatorGapMin := 80
    fractionDenomDisplayStyleGapMin := 200
    radicalVerticalGap := 96
    radicalDisplayStyleVerticalGap := 142
    radicalRuleThickness := 76
    radicalExtraAscender := 76
    radicalKernBeforeDegree := 276
    radicalKernAfterDegree := -400
    radicalDegreeBottomRaisePercent := 64 })
  -- MathVariants: the vertical size variants a delimiter grows through,
  -- checked against an independent struct-unpacking of the same face.
  t "fira grows ( through sixteen sizes"
    (((fira.gid '(').map fun g => fira.vertVariants g) ==
      some #[(9, 991), (1637, 1320), (1638, 1648), (1639, 1976), (1640, 2304),
             (1641, 2632), (1642, 2960), (1643, 3288), (1644, 3616), (1645, 3944),
             (1646, 4272), (1647, 4600), (1648, 4928), (1649, 5256), (1650, 5584),
             (1651, 5913)])
  t "fira grows the sum sign to display size"
    (((fira.gid '\u2211').map fun g => fira.vertVariants g) ==
      some #[(753, 863), (1584, 1528)])
  t "a text face grows nothing" (serif.mathVariants.isEmpty)
  -- Glyph vertical ink extents from the outline: the sum sign reaches well
  -- below the baseline and above the x-height; a period hugs the baseline.
  t "sum sign ink extent brackets the axis"
    (match (fira.gid '\u2211').bind fira.yExtent with
      | some (lo, hi) => lo < -100 && hi > 600
      | none => false)
  t "period ink sits on the baseline"
    (match (fira.gid '.').bind fira.yExtent with
      | some (lo, hi) => lo ≥ -30 && lo ≤ 0 && hi > 0 && hi < 300
      | none => false)
  let allSlots : Array ((Nat × Bool × Bool) × Nat) :=
    ((List.range 3).flatMap fun slot =>
      [((slot, false, false), 0), ((slot, true, false), 0),
       ((slot, false, true), 0), ((slot, true, true), 0)]).toArray
  let mfs : Font.FontSet := {
    fonts := #[serif, fira]
    index := allSlots
    math := some 1 }
  let geom : Layout.Geom := {}
  let base := geom.fontSize
  -- The engine sets the math face at the size that matches its x-height to
  -- the surrounding face's (`Math.mathSize`); every width below recomputes
  -- at that size from the font's own tables.
  let mbase : Dim.Sp := (Math.mathSize base.toNat serif.xHeightOptical
    serif.unitsPerEm fira.xHeightOptical fira.unitsPerEm : Nat)
  -- Optical agreement over the shipped pair, in sp: unscaled the two
  -- x-heights disagree (the mismatch the scaling exists to remove); at
  -- `mathSize` they agree to the division quantum — `mathSize_matches` and
  -- `body_xheight_le_mathSize_next`, witnessed on real faces.
  let bodyXh := (serif.xHeightOptical : Int) * base / serif.unitsPerEm
  let mathXhAt (sz : Dim.Sp) := (fira.xHeightOptical : Int) * sz / fira.unitsPerEm
  t "x-heights disagree before scaling" (mathXhAt base != bodyXh)
  t "x-heights agree after scaling, within one sp"
    (mathXhAt mbase ≤ bodyXh && bodyXh ≤ mathXhAt mbase + 1)
  let upem : Int := fira.unitsPerEm
  let adv (size : Dim.Sp) (c : Char) : Dim.Sp := (fira.advance c : Int) * size / upem
  let mu (size : Dim.Sp) (n : Int) : Dim.Sp := size * n / 18
  let konst (size : Dim.Sp) (v : Int) : Dim.Sp := v * size / upem
  let scriptSize := mbase * 72 / 100
  let ssSize := mbase * 58 / 100
  let lineOf (src : String) : Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    (((Layout.run geom mfs none d).pages.flatMap (·.lines))[0]?).getD default
  let widthOf (src : String) : Dim.Sp := (lineOf src).setWidth
  -- A box is a box: the advance equals the sum of what it contains plus
  -- the spacing the table gives, in sp, recomputed from the font alone.
  t "box is a box: a+b is two medium spaces"
    (widthOf "$a+b$" ==
      adv mbase '𝑎' + mu mbase 4 + adv mbase '+' + mu mbase 4 + adv mbase '𝑏')
  t "leading minus is a sign, not an operation"
    (widthOf "$-x$" == adv mbase '−' + adv mbase '𝑥')
  t "relation earns thick space"
    (widthOf "$a=b$" ==
      adv mbase '𝑎' + mu mbase 5 + adv mbase '=' + mu mbase 5 + adv mbase '𝑏')
  t "superscript: script size, spaceAfterScript, shifted by the constant"
    (widthOf "$x^2$" ==
      adv mbase '𝑥' + adv scriptSize '2' + konst mbase 41)
  let supRuns (src : String) : Array (Dim.Sp × Dim.Sp) :=
    (lineOf src).segs.filterMap fun s => match s with
      | .run _ _ _ _ glyphs sz _ raise =>
        if raise != 0 && !glyphs.isEmpty then some (sz, raise) else none
      | _ => none
  t "superscript raise is superscriptShiftUp at the base size"
    (supRuns "$x^2$" == #[(scriptSize, konst mbase 400)])
  t "subscript drop is subscriptShiftDown"
    (supRuns "$x_i$" == #[(scriptSize, -konst mbase 350)])
  -- Nested scripts: scriptscript size, shifts accumulating, the inner one
  -- scaled at its own base (the script size), cramped nowhere here.
  t "nested superscript reaches scriptscript and stacks its shifts"
    (supRuns "$x^{y^z}$" ==
      #[(scriptSize, konst mbase 400),
        (ssSize, konst mbase 400 + konst scriptSize 400)])
  -- Script styles suppress the conditional spacing: the + inside the
  -- superscript gets no medium space.
  t "no medium space inside a script"
    (widthOf "$x^{a+b}$" ==
      adv mbase '𝑥' + adv scriptSize '𝑎' + adv scriptSize '+' +
        adv scriptSize '𝑏' + konst mbase 41)
  -- Both scripts stack at one position: the atom advances by the wider.
  t "sup and sub stack, advancing by the wider"
    (widthOf "$x^a_b$" ==
      adv mbase '𝑥' + max (adv scriptSize '𝑎') (adv scriptSize '𝑏') + konst mbase 41)
  -- Variables italic, digits and function names upright (ISO 80000-2 §7,
  -- TeXbook ch. 18): x maps to U+1D465, sin and 2 stay ASCII.
  let glyphChars (src : String) : Array Char :=
    (lineOf src).segs.flatMap fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ => glyphs.map (·.2)
      | _ => #[]
  t "variables italic, functions and digits upright"
    (glyphChars "$\\sin 2x$" == #['s', 'i', 'n', '2', '𝑥'])
  t "sin binds with a thin space"
    (widthOf "$\\sin x$" ==
      adv mbase 's' + adv mbase 'i' + adv mbase 'n' + mu mbase 3 + adv mbase '𝑥')
  -- Nothing is silently dropped: a scalar the math face lacks warns,
  -- naming the face.
  let bDoc : Ir.Doc := { body := #[.para #[.formula false "₿"
    (.cons (.atom .ord (.sym '₿') .nil .nil false) .nil)]] }
  t "a glyph the math face lacks warns E0405 naming it"
    (((Layout.run geom mfs none bDoc).diags.filter (·.code == "E0405")).map (·.message)
      == #["'Fira Math' has no glyph for '₿' (U+20BF); dropped"])
  -- The chain, extended to math scalars: the census walk carries a
  -- formula's scalars to the driver's precompute, and a scalar the math
  -- face lacks that the precomputed chain covers sets from that face,
  -- named W0009 — never dropped.
  t "docScalars carries a formula's math scalars"
    ((Layout.docScalars (Elab.run "t" "$x$").1).contains '𝑥')
  let cfs : Font.FontSet := { mfs with fallback := #[('₿', 0)] }
  let cOut := Layout.run geom cfs none bDoc
  t "a math scalar the chain covers sets from the fallback face, named W0009"
    ((cOut.diags.filter (·.code == "E0405")).isEmpty &&
      (cOut.diags.filter (·.code == "W0009")).map (·.message) ==
        #["'Fira Math' has no glyph for '₿' (U+20BF); set from 'Source Serif Pro'"] &&
      ((cOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 0 _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '₿')
        | _ => false))
  -- No math face: one W0003 for the document, formulas set as their source.
  let bare : Font.FontSet := { fonts := #[serif], index := allSlots }
  let (nd, _) := Elab.run "t" "$x^2$ and $y$"
  let nOut := Layout.run geom bare none nd
  t "no math face warns W0003 once" ((nOut.diags.filter (·.code == "W0003")).size == 1)
  t "no math face sets the source text"
    ((nOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
      | .run 0 _ _ _ glyphs _ _ _ => glyphs.any (·.2 == '^')
      | _ => false)
  -- Elaboration shapes: display math is its own centred block; \(..\) is
  -- inline; equation* renders; align and \frac stay warned source.
  let (dd, dds) := Elab.run "t" "a \\[x\\] b"
  t "display math splits its paragraph into a centred block"
    (dds.isEmpty && dd.body ==
      #[.para #[.text "a"],
        .center #[.para #[.formula true "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil)]],
        .para #[.text "b"]])
  t "paren math is inline math"
    ((Elab.run "t" "\\(y\\)").1.body ==
      #[.para #[.formula false "y" (.cons (.atom .ord (.sym '𝑦') .nil .nil false) .nil)]])
  t "equation* is display math"
    ((Elab.run "t" "\\begin{equation*}x\\end{equation*}").1.body ==
      #[.center #[.para #[.formula true "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil)]]])
  -- What still is not modelled keeps its source and its name.
  t "an accent keeps its source and warns by name"
    (warnCodes "$\\hat{x}$" == ["W0012"] &&
      ((Elab.run "t" "$\\hat{x}$").1.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .math false _ => true
          | _ => false
        | _ => false))
  -- The alignment family renders as grids now; the numbered forms warn
  -- W0014 (numbers are owed, the mathematics is not), a ragged row is
  -- W0013 and still renders padded.
  t "align renders as a grid; its numbers warn W0015"
    (warnCodes "\\begin{align}a &= b\\end{align}" == ["W0015"] &&
      ((Elab.run "t" "\\begin{align}a &= b\\end{align}").1.body.any fun b => match b with
        | .center bs => bs.any fun b2 => match b2 with
          | .para xs => xs.any fun x => match x with
            | .formula true _ _ => true
            | _ => false
          | _ => false
        | _ => false))
  t "a ragged align row is W0014 and still renders"
    (warnCodes "\\begin{align*}a &= b \\\\ z\\end{align*}" == ["W0014"])
  -- Per-glyph positions: (char, gid, x, raise, advance) over every line.
  let glyphInfo (src : String) : Array (Char × Nat × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Char × Nat × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for page in (Layout.run geom mfs none d).pages do
      for l in page.lines do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .gap w => x := x + w
          | .rule w _ _ _ => x := x + w
          | .image _ w _ => x := x + w
          | .run _ _ _ w glyphs sz _ raise =>
            let mut gx := x
            for (g, c) in glyphs do
              let a := (fira.widths[g]?.getD 0 : Int) * sz / upem
              out := out.push (c, g, gx, raise, a)
              gx := gx + a
            x := x + w
    return out
  let rules (src : String) : Array (Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for page in (Layout.run geom mfs none d).pages do
      for l in page.lines do
        for s in l.segs do
          if let .rule w thickness raise _ := s then
            out := out.push (w, thickness, raise)
    return out
  -- Fractions: parts at their styles' sizes, numerator raised and
  -- denominator dropped, the bar fractionRuleThickness thick, and the
  -- advance the wider part plus \nulldelimiterspace each side.
  t "frac advance is the wider part plus null delimiters"
    (widthOf "$\\frac12$" ==
      2 * (mbase * 12 / 100) + max (adv scriptSize '1') (adv scriptSize '2'))
  t "frac raises its numerator and drops its denominator"
    (match (glyphInfo "$\\frac12$").toList with
      | [('1', _, _, up, _), ('2', _, _, down, _)] => up > 0 && down < 0
      | _ => false)
  t "the fraction bar is fractionRuleThickness thick, as wide as the parts"
    (rules "$\\frac12$" ==
      #[(max (adv scriptSize '1') (adv scriptSize '2'), konst mbase 76,
         konst mbase 280 - konst mbase 76 / 2)])
  -- The radical: the surd's ink top meets the overbar, radicand under it.
  t "sqrt draws surd and overbar over the radicand"
    ((glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '\u221A') &&
      (rules "$\\sqrt{x}$").size == 1 &&
      (glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '𝑥'))
  t "a root index sets small before the surd"
    ((glyphInfo "$\\sqrt[3]{x}$").any (fun g => g.1 == '3' && g.2.2.2.1 > 0))
  -- \left...\right grows through the variant ladder: around a tall display
  -- fraction the paren is no longer the base glyph (gid 9 in Fira Math).
  t "left paren grows over a display fraction"
    ((glyphInfo "\\[\\left(\\frac{a}{b}\\right)\\]").any fun g =>
      g.1 == '(' && g.2.1 != 9)
  t "an inline paren around a scalar stays the base glyph"
    ((glyphInfo "$\\left(a\\right)$").any fun g => g.1 == '(' && g.2.1 == 9)
  -- Big operators: display style takes the face's display-size variant
  -- (gid 1584) with limits above and below, centred; text style keeps the
  -- base glyph (753) and its scripts beside.
  t "display sum takes the display variant"
    ((glyphInfo "\\[\\sum_{i=1}^{n} i\\]").any fun g => g.1 == '\u2211' && g.2.1 == 1584)
  t "inline sum keeps the text-size glyph and scripts beside"
    ((glyphInfo "$\\sum_{i=1}^{n} i$").any fun g => g.1 == '\u2211' && g.2.1 == 753)
  t "display limits centre on the operator within a scaled point"
    (Id.run do
      let gs := glyphInfo "\\[\\sum_{j=2}^{m} j\\]"
      let some (_, _, sx, _, sa) := gs.find? (fun g => g.1 == '\u2211') | return false
      let some (_, _, mx, mraise, ma) := gs.find? (fun g => g.1 == '𝑚') | return false
      return mraise > 0 && ((2 * mx + ma) - (2 * sx + sa)).natAbs ≤ 2)
  t "the lower limit sits below the operator"
    ((glyphInfo "\\[\\sum_{j=2}^{m} j\\]").any fun g => g.1 == '2' && g.2.2.2.1 < 0)
  -- Alignment points align: the relation opening every even align cell
  -- sits at one x for every row, and the right-aligned column pushes a
  -- short cell right by exactly the width difference.
  t "align columns share their alignment point"
    (Id.run do
      let gs := glyphInfo "\\begin{align*}ab &= c \\\\ x &= yz\\end{align*}"
      let eqs := gs.filter (fun g => g.1 == '=')
      let some (_, _, x1, r1, _) := eqs[0]? | return false
      let some (_, _, x2, r2, _) := eqs[1]? | return false
      return x1 == x2 && r1 != r2)
  t "a right-aligned align cell pads by the width difference"
    (Id.run do
      let gs := glyphInfo "\\begin{align*}ab &= c \\\\ x &= yz\\end{align*}"
      let some (_, _, ax, _, _) := gs.find? (fun g => g.1 == '𝑎') | return false
      let some (_, _, xx, _, _) := gs.find? (fun g => g.1 == '𝑥') | return false
      return xx - ax == (adv mbase '𝑎' + adv mbase '𝑏') - adv mbase '𝑥')
  t "gather centres its rows on one axis"
    (Id.run do
      let gs := glyphInfo "\\begin{gather*}aaaa \\\\ b\\end{gather*}"
      let some (_, _, ax, _, _) := gs.find? (fun g => g.1 == '𝑎') | return false
      let some (_, _, bx, _, ba) := gs.find? (fun g => g.1 == '𝑏') | return false
      let w1 := 4 * adv mbase '𝑎'
      return ((2 * bx + ba) - (2 * ax + w1)).natAbs ≤ 2)
  -- Primes and \text.
  t "a prime is a raised superscript prime"
    ((glyphInfo "$x'$").any fun g => g.1 == '\u2032' && g.2.2.2.1 == konst mbase 400)
  t "text inside math keeps its letters and spaces upright"
    (glyphChars "$\\text{if }x$" == #['i', 'f', ' ', '𝑥'] ||
      glyphChars "$\\text{if }x$" == #['i', 'f', '𝑥'])
  t "operatorname binds like a named function"
    (widthOf "$\\operatorname{foo} x$" ==
      adv mbase 'f' + adv mbase 'o' + adv mbase 'o' + mu mbase 3 + adv mbase '𝑥')
  t "setmathfont fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\setmathfont{Fira Math}" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")
  t "fonts math key fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\fonts{ math = \"Fira Math\" }" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)
  let t := check ref

  utf8Checks ref
  argsChecks ref
  renderChecks ref
  lexChecks ref
  parseChecks ref
  elabDocChecks ref

  -- goldens
  runGoldens update (failures ref)

  -- dim
  t "sp pt string" ((Dim.pt 10).toPtString == "10" && (Dim.pt 3 / 2).toPtString == "1.5")
  dimChecks ref
  -- The two spellings of one length must agree: the engine's pt is the big
  -- point everywhere, so a default deck stage and \page{ width = 160mm }
  -- name the same number of sp.
  t "dim mm agrees with inch" (Dim.mm 254 == Dim.inch 10)

  kpChecks ref
  hyphenChecks ref
  walkChecks ref
  diagChecks ref
  pictureElabChecks ref
  diagVoiceChecks ref update
  allowChecks ref
  werrorChecks ref
  declChecks ref
  tokensChecks ref
  compatChecks ref
  unitChecks ref
  exprChecks ref
  wrapperChecks ref
  centeringChecks ref
  fontDiagChecks ref
  declaredFaceChecks ref
  fallbackChecks ref
  iconChecks ref
  smartChecks ref
  linkHtmlChecks ref
  paletteChecks ref
  mixChecks ref
  contrastChecks ref
  themeChecks ref
  designChecks ref
  roleChecks ref
  roleInvocationChecks ref
  roleShadowChecks ref
  fontsDeclChecks ref
  fontSuiteChecks ref
  mathChecks ref

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1
