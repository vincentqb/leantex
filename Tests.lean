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

def goldenNames : List String :=
  ["paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk", "deck", "themed", "latex-idioms", "wrapper",
   "centering", "columns", "overlays", "notes", "furniture"]

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
    | .W w => items := items.push (.box (Dim.pt w) 0 Ir.Color.black none #[] (Dim.pt 10) false)
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
    | .run _ _ _ _ glyphs size _ => some (glyphs.map (·.2), size)
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
    fr.body == #[.frame #[] false #[.center #[.para #[.text "Questions?"]]]])
  -- Inside inline content there is no block to centre; the warning stays.
  t "centering in an argument still warns"
    (warnCodes "\\textbf{\\centering x}" == ["W0108"])

/-- LaTeX idioms translate to native declarations. Own function, same reason. -/
def compatChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- LaTeX idioms translate to native declarations, each with a note that
  -- shows the shorter spelling. The document compiles as written.
  let notesOf (src : String) : List String :=
    ((elabStr src).2.filter (·.severity == .note)).toList.map (·.message)
  let pre (decls : String) : String :=
    "\\documentclass{article}\n" ++ decls ++ "\n\\begin{document}x\\end{document}"
  let (geoDoc, geoDs) := elabStr (pre "\\usepackage[letterpaper,vmargin=0.5in,hmargin=0.75in,headsep=1in]{geometry}")
  t "compat geometry becomes page" (geoDs.all (·.severity == .note) &&
    geoDoc.page.vmargin == Dim.inch 1 / 2 && geoDoc.page.hmargin == Dim.inch 3 / 4)
  t "compat geometry names what it dropped"
    ((notesOf (pre "\\usepackage[headsep=1in]{geometry}")).any (·.endsWith "headsep"))
  t "compat known package is a note, unknown a warning"
    ((elabStr (pre "\\usepackage{hyperref}")).2.all (·.severity == .note) &&
     warnCodes (pre "\\usepackage{tikz}") == ["W0103"])
  t "compat definecolor" ((elabStr (pre "\\definecolor{c}{HTML}{0F766E}")).1.palette.find? "c" ==
    some { r := 0x0F, g := 0x76, b := 0x6E })
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
    #[.para #[.styled .bold #[.text "x"]], .para #[.styled .bold #[.text "y"]]])
  t "a trailing forced break is dropped" ((elabStr "a\\\\ \n\nb").1.body ==
    #[.para #[.text "a"], .para #[.text "b"]])
  -- The document's definitions win over every built-in it may redefine;
  -- the ones it may not are refused with W0303, never shadowed silently.
  let (own, ownDs) := elabStr ("\\documentclass{article}" ++
    "\\define \\link(u: text, l: text) {\\href{\\u}{\\underline{\\l}}}" ++
    "\\begin{document}\\link{https://example.org}{here}\\end{document}")
  t "a defined link wins over the built-in"
    (ownDs.isEmpty && own.body ==
      #[.para #[.link "https://example.org" #[.underline #[.text "here"]]]])
  t "a parameter inside a URL is the caller's text"
    (own.body == #[.para #[.link "https://example.org" #[.underline #[.text "here"]]]])
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
    (ndc.body == #[.para #[.styled .bold #[.text "A"], .text " (B) ", .styled .bold #[.text "C"]]])
  let (nc, _) := elabStr ("\\documentclass{article}\\newcommand{\\two}[2]{#1+#2}" ++
    "\\begin{document}\\two{a}{b}\\end{document}")
  t "compat newcommand expands" (nc.body == #[.para #[.text "a+b"]])
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
  -- Unsupported configuration is skipped as a whole construct — command,
  -- options, arguments — with one warning naming it. It must never leak its
  -- arguments into elaboration as stray content (that was an E0313 per
  -- construct, an error cascade from a preamble the body never needed).
  -- \usetheme is no longer skipped: it rewrites to \theme (M5b).
  let beamerPre := pre ("\\usetheme{moloch}\\usefonttheme{professionalfonts}" ++
    "\\setbeamercovered{transparent}\\addtobeamertemplate{block begin}{}{\\smallskip}" ++
    "\\setbeameroption{hide notes}")
  t "compat beamer config skipped without errors" (errCodes beamerPre == [])
  t "compat beamer config warns once per construct"
    ((warnCodes beamerPre).length == 4 && (warnCodes beamerPre).all (· == "W0104"))
  t "compat usetheme selects the bundle instead of warning"
    ((elabStr beamerPre).1.palette.find? "frametitlebg" |>.isSome)
  t "compat beamer warnings name the native spelling"
    ((elabStr (pre "\\setbeamercolor{normal text}{fg=black}")).2.any fun d =>
      d.code == "W0104" && ((d.help.getD "").splitOn "\\palette").length == 2)
  t "compat tex conditional skipped whole, contents included"
    (warnCodes (pre "\\ifdefined\\x\\usepackage{pgfpages}\\setbeameroption{notes}\\fi") ==
      ["W0104"])
  t "compat def skipped through its body"
    (errCodes (pre "\\makeatletter\\def\\verbatim@font{\\footnotesize\\ttfamily}\\makeatother") == [])
  t "compat newenvironment defines; only its beamer-config body warns"
    (warnCodes (pre "\\newenvironment{wrap}[1]{\\logo{#1}}{\\logo{}}") == ["W0104"])
  -- Overlay specifications elaborate to steps; the content stays.
  t "uncover wraps its content in a step"
    ((elabStr "a \\uncover<2>{shown} b").1.body ==
      #[.para #[.text "a ", .step 2 #[.text "shown"], .text " b"]])
  t "pause between words steps the rest of the scope"
    ((elabStr "a \\pause b").1.body ==
      #[.para #[.text "a"], .step 2 #[.para #[.text "b"]]])
  t "unnumbered overlay specs warn once for the whole document"
    ((warnCodes "\\uncover<+->{a} \\uncover<.->{b}").length == 1)
  t "item overlay spec wraps the item"
    ((elabStr "\\begin{itemize}\\item<1-> one\\end{itemize}").1.body ==
      #[.list false #[#[.step 1 #[.para #[.text "one"]]]]])
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
        ("'Alpha Sans Light' declares \"Nope Sans\" as its bold face, " ++
         "which is not installed; using \"Alpha Sans Light\"")))
  -- No declaration: the substitution message names the face actually used.
  t "substitution names the face actually used"
    ((FontDb.resolveVariant faces "Alpha Sans Light" none { bold := true }).map (·.2) ==
      some (some "'Alpha Sans Light' has no bold face; using \"Alpha Sans Light\""))
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

/-- Per-glyph fallback: a scalar the styled face lacks is set from the face
the driver's map names, at the same size; the diagnostic is one line per
family+glyph, naming both families; a scalar no face covers is still an
honest W0004 naming the family; and a document whose faces cover their text
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
      | .run 1 _ _ _ glyphs _ _ => glyphs.any (·.2 == '∀')
      | _ => false)
  t "fallback reports once per family+glyph, naming both faces"
    ((out.diags.filter (·.code == "W0009")).map (·.message) ==
      #["'Open Sans' has no glyph for '∀' (U+2200); set from 'Source Code Pro'"])
  t "a covered scalar raises no W0004" (!out.diags.any (·.code == "W0004"))
  -- No face covers it: dropped once per family+glyph, family named.
  let (dropDoc, _) := Elab.run "t" "lost ⟨ here\n\nand ⟨ there"
  let dropOut := Layout.run geom mapped none dropDoc
  t "an uncovered scalar drops once, naming the family"
    ((dropOut.diags.filter (·.code == "W0004")).map (·.message) ==
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
  let picks ← FontDb.fallbackPicks shipped #['∀', '₿', '⟨']
  t "picks the first covering family in sorted order"
    (picks.contains ('∀', testFonts ++ "/SourceCodePro-Regular.otf"))
  t "picks the regular face of a family with variants"
    (picks.contains ('₿', testFonts ++ "/SourceSerifPro-Regular.otf"))
  t "a scalar no face covers is absent from the picks"
    (!picks.any (·.1 == '⟨'))
  -- Malformed and missing candidates stay total: no answer, never an abort.
  t "tableImage of a missing file is none"
    ((← FontDb.tableImage "/nonexistent/leantex-x.otf" (fun _ => true)).isNone)
  let corrupt := System.FilePath.mk "/tmp" / "leantex-test-corrupt-fallback.otf"
  IO.FS.writeBinFile corrupt ("OTTO".toUTF8 ++ ByteArray.mk (Array.replicate 40 0xff))
  t "a corrupt candidate yields no cmap image"
    ((← FontDb.tableImage corrupt.toString (· == "cmap")).isNone)
  IO.FS.removeFile corrupt

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
              | .run _ _ _ w _ _ _ => some w
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
  t "default over the shipped faces is the sans"
    (FontDb.defaultFamily faces == some "Open Sans")
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
    (((Html.render (Html.elem "p" #[Html.Node.script "x</SCRIPT>bad"]) 0).splitOn
      "</SCRIPT").length == 1)
  -- The terminator literal omits the closing `>`, which is what catches a
  -- spaced or self-closed end tag; pinned so the case fix cannot regress it.
  t "html script payload with a spaced terminator is removed"
    (((Html.render (Html.elem "p" #[Html.Node.script "x</script >bad"]) 0).splitOn
      "/* removed */").length == 2)

/-- The pre-commit gate's own predicates, exercised through the script's
`--selftest` mode: a gate that does not catch the shape it commemorates
grants false confidence. -/
def precommitChecks (ref : IO.Ref (List String)) : IO Unit := do
  let out ← IO.Process.output
    { cmd := "lean", args := #["--run", "scripts/precommit.lean", "--selftest"] }
  check ref s!"precommit selftest:\n{out.stderr}" (out.exitCode == 0)

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
  t "columns elaborate with widths, warning nothing" (ds.isEmpty &&
    doc.body == #[.frame #[] false #[.columns #[
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
      | #[.frame _ _ #[.columns cols]] => cols.map (·.1) == #[none, some 500]
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
    doc.body == #[.frame #[] false #[
      .list false #[
        #[.step 1 #[.para #[.text "first"]]],
        #[.step 2 #[.para #[.text "second"]]]],
      .para #[.step 2 #[.text "tail"]]]])
  -- \pause steps the rest of the scope.
  let (pDoc, pDs) := elabStr (deck "one\n\n\\pause\ntwo\n\n\\pause\nthree")
  t "pause steps the rest, cumulatively" (pDs.isEmpty &&
    pDoc.body == #[.frame #[] false #[
      .para #[.text "one"],
      .step 2 #[.para #[.text "two"], .step 3 #[.para #[.text "three"]]]]])
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
      | .run _ c _ _ _ _ _ => some c
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
    doc.body == #[.frame #[] false #[
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
      | #[.frame _ _ #[.para content, .note nbody]] =>
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
      | #[.frame _ _ #[_, .note nbody]] =>
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
  let fg : Ir.Color := ⟨0x23, 0x37, 0x3B⟩
  let bg : Ir.Color := ⟨0xFF, 0xFF, 0xFF⟩
  t "every step page of a standout frame stays inverted"
    (so.pages.all fun p => p.fills.any fun f =>
      f.x == 0 && f.y == 0 && f.w == geom.pageW && f.h == geom.pageH && f.color == fg)
  t "standout text keeps standoutfg on every step page"
    (so.pages.all fun p => p.lines.any fun l => l.segs.any fun s => match s with
      | .run _ c _ _ _ _ _ => c == bg
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
  let alert : Ir.Color := ⟨0xEB, 0x81, 0x1B⟩
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
  let bg : Ir.Color := ⟨0xFA, 0xFA, 0xFA⟩
  let fg : Ir.Color := ⟨0x23, 0x37, 0x3B⟩
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
        | .run _ c _ _ _ _ _ => c == bg
        | _ => false
     | none => false)
  t "body text takes fg"
    (match out.pages[0]? with
     | some p => p.lines.any fun l => l.segs.any fun s => match s with
        | .run _ c _ _ _ _ _ => c == fg
        | _ => false
     | none => false)
  let mp : Dim.Sp := geom.textWidth * 7875 / 10000
  let alert : Ir.Color := ⟨0xEB, 0x81, 0x1B⟩
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
    (fDoc.body == #[.frame #[.text "T"] false #[.para #[.text "body"]]])
  -- A group after a paragraph break is content, not a title: LaTeX's own
  -- argument scanning stops looking there too.
  t "frame title after a blank line is content"
    ((elabStr (deck "\\begin{frame}[plain]\n\n{scope group}\n\\end{frame}")).1.body ==
      #[.frame #[] false #[.para #[.text "scope group"]]])
  t "frametitle names the frame"
    ((elabStr (deck "\\begin{frame}\n\\frametitle{Named}\nbody\n\\end{frame}")).1.body ==
      #[.frame #[.text "Named"] false #[.para #[.text "body"]]])
  -- Two titles: the last wins, as in beamer, but never silently.
  let (dupDoc, dupDs) := elabStr
    (deck "\\begin{frame}\n\\frametitle{One}\n\\frametitle{Two}\nbody\n\\end{frame}")
  t "a second frametitle warns and wins"
    (dupDs.any (·.code == "W0311") &&
     match dupDoc.body with
     | #[.frame title _ _] => Ir.plainText title == "Two"
     | _ => false)
  -- \title and friends may sit in the body, as beamer documents do; an
  -- empty declaration (\date{}) is deliberately blank and sets nothing.
  let titled := deck ("\\title{A Deck}\\subtitle{Sub}\\author{Pat Placeholder}\\date{}\n" ++
    "\\maketitle\n\\begin{frame}{One}\nx\n\\end{frame}")
  let (tDoc, tDs) := elabStr titled
  t "maketitle source clean" tDs.isEmpty
  t "maketitle is a centered title frame with the empty date dropped"
    (match tDoc.body[0]? with
     | some (Ir.Block.frame title _ #[.center inner]) => title.isEmpty && inner.size == 3
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
    (out.pages.all fun p => p.lines.any (·.size == Dim.pt 14))
  let (html, _) := HtmlDoc.emit {} dDoc
  t "html gives each frame its own slide section"
    ((html.splitOn "<section class=\"slide\"").length == 4)
  -- Math environments carry their source whole — elaborating `&` and `\\`
  -- as text would shred the alignment; tables degrade to rows of cells and
  -- `&` never reaches inline elaboration as a reserved-character error.
  t "align* is one display-math block, source intact"
    (match (elabStr "\\begin{align*}1 &= 1 \\\\ 2 &= 4\\end{align*}").1.body with
     | #[.para #[.math true src]] => (src.splitOn "&").length == 3
     | _ => false)
  let tabSrc := "\\begin{tabular}{ll}a & b \\\\ c & d\\end{tabular}"
  t "tabular keeps cells as rows without errors"
    (errCodes tabSrc == [] &&
     match (elabStr tabSrc).1.body with
     | #[.para xs] => xs.contains (.linebreak {}) &&
         ["a", "b", "c", "d"].all fun w => ((Ir.plainText xs).splitOn w).length == 2
     | _ => false)
  -- The classic rules, not just booktabs: \hline and \cline are inert, and
  -- \multicolumn keeps its cell text without the span count or alignment
  -- spec leaking in beside it.
  let classicTab := "\\begin{tabular}{ll}\\hline\n" ++
    "\\multicolumn{2}{X}{Head} \\\\ \\cline{1-2}\na & b \\\\ \\hline\\end{tabular}"
  let (ctDoc, ctDs) := elabStr classicTab
  t "classic tabular rules are inert" (!ctDs.any (·.code == "W0301"))
  t "multicolumn keeps only its cell text"
    (match ctDoc.body with
     | #[.para xs] =>
       let s := Ir.plainText xs
       (s.splitOn "Head").length == 2 && !s.toList.contains '2' && !s.toList.contains 'X'
     | _ => false)
  -- [standout]: the one frame option that says what the frame IS. It
  -- inverts, centres, and sets Large bold in both backends; the other
  -- options stay burned.
  t "standout option marks the frame"
    (match (elabStr (deck "\\begin{frame}[fragile,standout]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ true _] => true
     | _ => false)
  t "other frame options do not mark it"
    (match (elabStr (deck "\\begin{frame}[plain]\nQ\n\\end{frame}")).1.body with
     | #[.frame _ false _] => true
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
           | .run _ c _ _ _ _ _ => c == Ir.Color.white
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
     | #[.verbatim s] => s.trimAscii.toString == "literal line one"
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
     ds.any fun d => d.code == "W0313" && d.message.startsWith "2 ")
  t "the block path warns about dropped begin-line groups too"
    ((elabStr "\\begin{wrap}{arg}\none\n\ntwo\n\\end{wrap}").2.any (·.code == "W0313"))
  t "no dropped-argument warning without begin-line groups"
    (!(elabStr "Take \\begin{banner}the text\\end{banner} along.").2.any (·.code == "W0313"))
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
    (secDs.isEmpty && match secDoc.body with
     | #[.section 1 false title, .para _] => Ir.plainText title == "Long Title"
     | _ => false)
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
     | #[.frame _ _ body] => body.any fun b => (blockText b).endsWith "Body survives."
     | _ => false)
  t "unclosed bracket in a frame warns" (fDs.any (·.code == "W0310"))
  -- a bracket opening the frame's content is content, not an option
  t "frame content starting with a bracket survives"
    (match (elabStr (deck "\\begin{frame}\n[1] Reference survives.\n\\end{frame}")).1.body with
     | #[.frame _ _ #[.para xs]] => Ir.plainText xs == "[1] Reference survives."
     | _ => false)
  -- options on the begin line are still arguments, bracket runs included
  t "frame options on the begin line are burned"
    (match (elabStr (deck "\\begin{frame}[plain][t]{T}\nbody\n\\end{frame}")).1.body with
     | #[.frame title _ #[.para xs]] =>
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
  t "args emit list" ((parse ["build", "--emit", "pdf,html", "a.tex"]).map (·.emit) ==
    .ok (some #[.pdf, .html]))
  t "args emit eq after command"
    ((parse ["build", "--emit=html", "a.tex"]).map (·.emit) == .ok (some #[.html]))
  t "args emit default is pdf"
    ((parse ["build", "a.tex"]).map (·.effectiveEmit #[]) == .ok #[.pdf])
  t "args emit bad" ((parse ["build", "--emit", "ps", "a.tex"]).isOk == false)
  t "args css after command"
    ((parse ["build", "--css", "bulma", "a.tex"]).map (·.css) == .ok (some .bulma))
  t "args css default is own"
    ((parse ["build", "a.tex"]).map (·.effectiveCss none) == .ok .own)
  t "args css bad" ((parse ["build", "--css", "tailwind", "a.tex"]).isOk == false)
  t "args math boundary"
    ((parse ["build", "--math-boundary", "katex", "a.tex"]).map (·.mathBoundary) ==
      .ok (some "katex"))
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
  t "args emit beats output name" ((parse ["a.tex", "--emit", "pdf,html", "-o", "out/"]).map
    (·.effectiveEmit #[]) == .ok #[.pdf, .html])
  t "args document formats apply" ((parse ["a.tex"]).map (·.effectiveEmit #["html"]) ==
    .ok #[.html])
  t "args flag beats document" ((parse ["a.tex", "--emit", "pdf"]).map
    (·.effectiveEmit #["html"]) == .ok #[.pdf])
  t "args document css applies" ((parse ["a.tex"]).map (·.effectiveCss (some "bulma")) ==
    .ok .bulma)
  t "args css flag beats document" ((parse ["a.tex", "--css", "none"]).map
    (·.effectiveCss (some "bulma")) == .ok CssChoice.none)
  t "args output dir keeps stem" (outPath (some "out/") false "doc.tex" .pdf == "out/doc.pdf")
  t "args output other backend beside source"
    (outPath (some "out.html") false "doc.tex" .pdf == "doc.pdf")
  t "args watch" ((parse ["a.tex", "--watch"]).map (·.watch) == .ok true)

def renderChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- render: porcelain is stable, escaped JSONL
  let d : Diag := {
    severity := .error
    code := "E0002"
    message := "bad \"quote\"\nline"
    span := some ⟨"a.tex", ⟨3, 7⟩⟩
    help := some "fix it"
  }
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
    #[.para #[.text "hello ", .math false "x", .text " world"]])
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
    #[.para #[.styled .bold #[.text "Ada"], .text " (Compute)"]])
  let (doc8, d8) := elabStr (defRole ++ "\\role{Ada}\n\\end{document}")
  t "elab define call optional omitted" (d8.isEmpty && doc8.body ==
    #[.para #[.styled .bold #[.text "Ada"]]])
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
  t "elab reserved command warns, never errors" (warnCodes ("\\documentclass{article}\\figure{x}" ++
    "\\begin{document}y\\end{document}") == ["W0307"])
  -- Unknown environments keep their body: the wrapper's decoration is
  -- unknowable, the content inside it is not. Arguments on the \begin line
  -- go with the wrapper; a group on a later line is content.
  t "elab unknown environment keeps its body"
    ((elabStr "\\begin{wrap}{arg}\nkept\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab unknown environment warns once per name"
    ((warnCodes "\\begin{w}a\\end{w}\\begin{w}b\\end{w}") == ["W0302"])
  t "elab unknown environment keeps a group on a later line"
    ((elabStr "\\begin{wrap}\n{kept}\n\\end{wrap}").1.body == #[.para #[.text "kept"]])
  t "elab reserved environment content is skipped with one warning"
    (warnCodes "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}" == ["W0307"] &&
     (elabStr "\\begin{tikzpicture}\\draw (0,0);\\end{tikzpicture}").1.body == #[])
  t "elab reserved char" (errCodes "a & b" == ["E0311"])
  t "elab redefine builtin warns and keeps the built-in"
    (warnCodes "\\define \\textbf() {x}\n\\begin{document}y\\end{document}" == ["W0303"])
  -- ...except a text symbol, whose name a document may want for itself.
  let (degDoc, degDs) := elabStr
    "\\define \\degree(a: text) {\\textbf{\\a}}\n\\begin{document}\\degree{PhD}\\end{document}"
  t "elab user definition shadows a symbol"
    (degDs.isEmpty && degDoc.body == #[.para #[.styled .bold #[.text "PhD"]]])
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
    ((elabStr verbSrc).1.body == #[.verbatim "\ndef f(n):\n    return n\n\nf(2)  # two spaces\n"] &&
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
      | .spaced _ _ => true
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
    (((Html.render (Html.elem "p" #[Html.Node.script "x</script>bad"]) 0).splitOn
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
  t "palette wrong type" (errCodes ("\\documentclass{article}\\palette{a = 3pt}" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "palette cannot shadow builtin" (errCodes
    ("\\documentclass{article}\\palette{textbf = #fff}" ++
     "\\begin{document}x\\end{document}") == ["E0303"])
  t "color value parsed" (Decl.parseValue "#7C3AED" == some (.color 0x7C 0x3A 0xED))
  t "color rejects bad hex" (Decl.parseValue "#12345" == none)
  t "color pdf components" ((Ir.Color.mk 255 0 128).pdfComponents == "1 0 0.502")
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
    ((List.range 256).all fun c => Contrast.channelLinear.getD c 0 == lin c)
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
  t "a declared fg is judged against the declared bg"
    ((warnCodes ("\\documentclass{article}" ++
      "\\palette{ fg = #999999, bg = #888888 }" ++
      "\\begin{document}x\\end{document}")).contains "W0315")
  t "the built-in themes raise no pairing warning"
    (!(warnCodes ("\\documentclass{slides}\\theme{moloch}\\begin{document}" ++
      "\\begin{frame}x\\end{frame}\\end{document}")).contains "W0315")

  -- The built-in theme bundles, held to the same contract. The theorems
  -- hold over the pre-resolved palettes; these pins close the chain: the
  -- constants equal the pure bundle resolution, the pure resolution equals
  -- what \theme actually installs, and the live check passes.
  t "molochResolved is bundlePalette moloch"
    (Contrast.bundlePalette Theme.moloch == Contrast.molochResolved)
  t "plainResolved is bundlePalette plain"
    (Contrast.bundlePalette Theme.plain == Contrast.plainResolved)
  for th in Theme.builtin do
    let (thDoc, _) := elabStr ("\\documentclass{slides}\\theme{" ++ th.name ++
      "}\\begin{document}\\begin{frame}x\\end{frame}\\end{document}")
    t s!"bundlePalette {th.name} matches the elaborator"
      (thDoc.palette == Contrast.bundlePalette th)
  t "every built-in bundle clears its thresholds"
    (Theme.builtin.all Contrast.Theme.contractHolds)
  -- The check fires on the illegible bundle it exists for: moloch's own
  -- alert (#EB811B, 2.61:1 as body text) fails the contract.
  t "the contract rejects moloch's original alert"
    (let badEntries := (Contrast.molochResolved.entries.filter (·.1 != "alert")).push
        ("alert", (⟨0xEB, 0x81, 0x1B⟩ : Ir.Color))
     !Contrast.paletteContract { entries := badEntries })
  -- Themed \alert is colour AND bold: colour alone would be the run's only
  -- signal (WCAG 2.2 SC 1.4.1); unthemed it stays the bold stand-in.
  let themedAlert := elabStr ("\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\begin{document}\\begin{frame}\\alert{hot}\\end{frame}\\end{document}")
  t "themed alert is colour and bold" (themedAlert.1.body.any fun b =>
    match b with
    | .frame _ _ body => body.any fun blk =>
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
  let pal : Ir.Palette := { entries := #[("base", ⟨0x40, 0x00, 0x80⟩)] }
  t "mix toward white" (pal.resolve "base!50" == some ⟨0xA0, 0x80, 0xC0⟩)
  t "mix with black" (pal.resolve "base!50!black" == some ⟨0x20, 0x00, 0x40⟩)
  t "mix chain folds left" (pal.resolve "base!50!black!30" ==
    some (((⟨0x40, 0x00, 0x80⟩ : Ir.Color).mix 50 Ir.Color.black).mix 30 Ir.Color.white))
  t "mix black!2 is near-white"
    (({} : Ir.Palette).resolve "black!2" == some ⟨250, 250, 250⟩)
  t "mix plain name still resolves" (pal.resolve "base" == some ⟨0x40, 0x00, 0x80⟩)
  t "mix pct over 100 rejected" (pal.resolve "base!101" == none)
  t "mix unknown atom rejected" (pal.resolve "nope!50" == none)
  -- Declaration site: a mix value reads the entries declared so far.
  let doc (body : String) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ fg = #000000, bg = #ffffff, dim = bg!50!fg, faint = black!2 }\n" ++
    "\\begin{document}" ++ body ++ "\\end{document}")
  let (pDoc, pDs) := doc "x"
  t "palette mix entry clean" pDs.isEmpty
  t "palette mix entry value" (pDoc.palette.find? "dim" == some ⟨0x80, 0x80, 0x80⟩)
  t "palette black!2 entry" (pDoc.palette.find? "faint" == some ⟨250, 250, 250⟩)
  -- Use site: \textcolor takes a mix, `fg`/`bg` naming the current semantic
  -- foreground and background. A computed colour carries no var name.
  let (uDoc, uDs) := doc "\\textcolor{fg!50!bg}{x}"
  t "textcolor mix resolves without W0304" (!uDs.any (·.code == "W0304"))
  t "textcolor mix colours the content" (uDoc.body == #[.para #[
    .colored ⟨0x80, 0x80, 0x80⟩ none #[.text "x"]]])
  t "textcolor mix with unknown base still warns"
    (warnCodes ("\\documentclass{article}\\begin{document}" ++
      "\\textcolor{quiet!50}{x}\\end{document}") == ["W0304"])
  -- Later declarations override earlier ones, theme defaults included.
  let (oDoc, _) := elabStr ("\\documentclass{article}\n" ++
    "\\palette{ a = #111111 }\\palette{ a = #222222 }\n" ++
    "\\tokens{ s = 4pt }\\tokens{ s = 8pt }\n" ++
    "\\begin{document}x\\end{document}")
  t "palette redeclare overrides" (oDoc.palette.find? "a" == some ⟨0x22, 0x22, 0x22⟩)
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
    (mDoc.palette.find? "bg" == some ⟨0xFA, 0xFA, 0xFA⟩ &&
     mDoc.palette.find? "frametitlebg" == some ⟨0x23, 0x37, 0x3B⟩ &&
     mDoc.palette.find? "progressbg" == some ⟨0xCB, 0xC0, 0xB6⟩)
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
    (oDoc.palette.find? "alert" == some ⟨0xC2, 0x18, 0x5B⟩ &&
     oDoc.palette.find? "frametitlebg" == some ⟨0x23, 0x37, 0x3B⟩)
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
    (uDs.any fun d => d.code == "W0314" &&
      ((d.help.getD "").splitOn "moloch").length == 2 &&
      ((d.help.getD "").splitOn "plain").length == 2)
  t "unknown theme leaves the palette empty" (uDoc.palette.entries.isEmpty)
  -- \alert through the compat layer: a colour when themed, bold when not.
  let (aDoc, _) := elabStr (deck "\\usetheme{moloch}"
    "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")
  t "themed alert is the alert colour"
    (match aDoc.body with
     | #[.frame _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .colored c (some "alert") _ => c == ⟨0xA5, 0x5A, 0x13⟩
          | _ => false
        | _ => false
     | _ => false)
  t "unthemed alert stays bold"
    (match (elabStr (deck "" "\\begin{frame}{T}\n\\alert{hot}\n\\end{frame}")).1.body with
     | #[.frame _ _ body] => body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .styled .bold _ => true
          | _ => false
        | _ => false
     | _ => false)

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
  t "fontdb finds the nine shipped faces" (faces.size == 9)
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
          | .run _ _ _ _ glyphs _ _ => glyphs.any (·.2 == '-')
          | .gap _ | .rule .. => false
      t "layout chosen hyphen renders" (hyOut.pages[0]!.lines.size > 1 && hyphenRendered)
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
        p.lines.any (·.size == Dim.pt 14)
      let hasListMarker := visualOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ => glyphs.any (·.2 == '–')
          | .gap _ | .rule .. => false
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

      lineChecks ref geom oneFace
      underlineChecks ref geom oneFace font
      inkGeometryChecks ref
      spacingChecks ref geom oneFace font
      slideChecks ref oneFace
      columnsChecks ref oneFace
      overlayChecks ref oneFace
      noteChecks ref oneFace
      themeFurnitureChecks ref oneFace
      themeReconcileChecks ref oneFace
      scannerChecks ref
      rhythmChecks ref oneFace
      measureChecks ref oneFace

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
  declChecks ref
  tokensChecks ref
  compatChecks ref
  wrapperChecks ref
  centeringChecks ref
  fontDiagChecks ref
  declaredFaceChecks ref
  fallbackChecks ref
  smartChecks ref
  linkHtmlChecks ref
  paletteChecks ref
  mixChecks ref
  contrastChecks ref
  themeChecks ref
  fontsDeclChecks ref
  fontSuiteChecks ref

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1
