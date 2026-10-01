/-
External math-alphabet differential. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/math-alphabet-diff.lean
  lake env lean --run scripts/math-alphabet-diff.lean --selftest

This is a report, never a hermetic gate. Work products stay below
`.lake/math-alphabet-diff`. Ghostscript's txtwrite TextFormat=0 reads the
complete extracted character sequence of each PDF, including every span.
UTF-16 pairs become one scalar; multi-scalar spans retain every character.
Malformed or absent observations are MISSING, never a first-glyph match.

PASS requires equal nonempty sequences of scalar, normalized font name,
point size and character bounding-box width. Face, size and width also have
separate verdict columns: a face match cannot hide a size or width DIFF.
Size is truncated to thousandths of a PDF point; width is the integer
character box at 720 dpi (0.1 pt per unit), not the PDF pen's advance. Its
quantization can depend on placement. Equality of these observations proves
neither font-program identity, glyph outlines nor full page-layout parity.

The generated preamble deliberately assigns the shipped OpenSans family to
all three text slots. That controls the inputs but does not test distinct
serif/sans/mono faces. Only the PDF's six-uppercase-letter subset tag, exact
Ghostscript CMap suffixes and documented aliases below are normalized.

The four-face matrix is bounded, not full unicode-math compatibility. It
includes nested alphabets, fallback and both source policies. It omits bm's
bold-math-version behavior and some legacy-command Greek cases. A reference
that fails to build, produces no text or cannot be read is not a match;
its reason stays on the row. Renderer differences are never exemptions.
-/

import LeanTex
import Lean.Data.Json.FromToJson

open LeanTex.Core

structure GlyphFact where
  scalar : String
  font : String
  width : Int
  sizeMilli : Int
  deriving Repr, BEq, Inhabited

structure FaceCase where
  label : String
  path : String
  deriving Repr, Inhabited

/-- One differential row: a math body set under a chosen source policy.
`sym` picks the `mathX=sym` override preamble; otherwise the body runs under
unicode-math's default (text-sourced legacy alphabets). There is
deliberately no scalar-only field: every row compares the full glyph fact. -/
structure Case where
  label : String
  body : String
  sym : Bool := true
  deriving Repr, Inhabited

/-- Single-scalar anchors plus sequences exercising the same reader and
comparator. The `sym` policy overrides legacy alphabet sources; explicit
`\sym…` commands remain symbol-sourced under either policy. -/
def cases : List Case :=
  -- sym-source single-letter anchors
  [ { label := "bb O", body := "\\mathbb{O}" },
    { label := "cal O", body := "\\mathcal{O}" },
    { label := "frak O", body := "\\mathfrak{O}" },
    { label := "bf O", body := "\\mathbf{O}" },
    { label := "it O", body := "\\mathit{O}" },
    { label := "sf O", body := "\\mathsf{O}" },
    { label := "tt O", body := "\\mathtt{O}" },
    { label := "rm O", body := "\\mathrm{O}" },
    -- per-range anchors: upper, lower, digit, Greek upper/lower, misc
    { label := "bf lower a", body := "\\mathbf{a}" },
    { label := "bf digit 5", body := "\\mathbf{5}" },
    { label := "bf Greek up", body := "\\mathbf{\\Gamma}" },
    { label := "bb digit 5", body := "\\mathbb{5}" },
    { label := "bb lower k", body := "\\mathbb{k}" },
    { label := "sf digit 5", body := "\\mathsf{5}" },
    { label := "tt digit 5", body := "\\mathtt{5}" },
    { label := "it lower x", body := "\\mathit{x}" },
    { label := "it Greek low", body := "\\mathit{\\gamma}" },
    { label := "it Greek up", body := "\\mathit{\\Gamma}" },
    { label := "up Greek up", body := "\\symup{\\Gamma}" },
    { label := "bfup Greek low", body := "\\symbfup{\\gamma}" },
    { label := "bfup nabla", body := "\\symbfup{\\nabla}" },
    -- Letterlike holes
    { label := "bb hole R", body := "\\mathbb{R}" },
    { label := "bb hole Z", body := "\\mathbb{Z}" },
    { label := "cal hole L", body := "\\mathcal{L}" },
    { label := "cal hole B", body := "\\mathcal{B}" },
    { label := "frak hole C", body := "\\mathfrak{C}" },
    { label := "frak hole H", body := "\\mathfrak{H}" },
    -- nested alphabet stacks: innermost that covers the range wins
    { label := "bf(cal A)", body := "\\mathbf{\\mathcal{A}}" },
    { label := "bb(cal A)", body := "\\mathbb{\\mathcal{A}}" },
    { label := "bf(cal 5)", body := "\\mathbf{\\mathcal{5}}" },
    { label := "bf(frak 5)", body := "\\mathbf{\\mathfrak{5}}" },
    { label := "bf(frak Z)", body := "\\mathbf{\\mathfrak{Z}}" },
    { label := "cal(bf A)", body := "\\mathcal{\\mathbf{A}}" },
    -- Nested fallback is observed even when the inner face lacks its glyph.
    { label := "bb(rm x) text", body := "\\mathbb{\\mathrm{x}}", sym := false },
    { label := "rm(bb x) text", body := "\\mathrm{\\mathbb{x}}", sym := false },
    { label := "bf(cal A) text", body := "\\mathbf{\\mathcal{A}}", sym := false },
    { label := "cal(bf A) text", body := "\\mathcal{\\mathbf{A}}", sym := false },
    { label := "bb(rm x) sym", body := "\\mathbb{\\mathrm{x}}" },
    { label := "rm(bb x) sym", body := "\\mathrm{\\mathbb{x}}" },
    -- \boldsymbol: bold, variables staying italic
    { label := "bsym O", body := "\\boldsymbol{O}" },
    { label := "bsym 5", body := "\\boldsymbol{5}" },
    { label := "bsym alpha", body := "\\boldsymbol{\\alpha}" },
    { label := "bsym Gamma", body := "\\boldsymbol{\\Gamma}" },
    { label := "bsym(cal A)", body := "\\boldsymbol{\\mathcal{A}}" },
    -- text (default) policy: the legacy alphabets now project to a real
    -- text family and the face is held to LuaLaTeX's, not just the scalar.
    { label := "text rm d", body := "\\mathrm{d}", sym := false },
    { label := "text bf x", body := "\\mathbf{x}", sym := false },
    { label := "text it y", body := "\\mathit{y}", sym := false },
    { label := "text sf R", body := "\\mathsf{R}", sym := false },
    { label := "text tt k", body := "\\mathtt{k}", sym := false },
    { label := "text bf a", body := "\\mathbf{a}", sym := false },
    { label := "text it X", body := "\\mathit{X}", sym := false },
    { label := "text it digit", body := "\\mathit{5}", sym := false },
    { label := "text bf(it digit)", body := "\\mathbf{\\mathit{5}}", sym := false },
    { label := "text it(bf digit)", body := "\\mathit{\\mathbf{5}}", sym := false },
    { label := "text rm sequence", body := "\\mathrm{x5R}", sym := false },
    { label := "mixed sequence", body := "\\mathit{x5}\\symbf{R}", sym := false },
    -- Explicit symbol alphabets under the default text-source policy.
    { label := "symrm d /text", body := "\\symrm{d}", sym := false },
    { label := "symit y /text", body := "\\symit{y}", sym := false },
    { label := "symit digit /text", body := "\\symit{5}", sym := false },
    { label := "symbf x /text", body := "\\symbf{x}", sym := false },
    { label := "symsf R /text", body := "\\symsf{R}", sym := false },
    { label := "symtt k /text", body := "\\symtt{k}", sym := false },
    { label := "symup G /text", body := "\\symup{\\Gamma}", sym := false },
    { label := "symbfup g /text", body := "\\symbfup{\\gamma}", sym := false },
    { label := "symbb N /text", body := "\\symbb{N}", sym := false },
    { label := "symcal O /text", body := "\\symcal{O}", sym := false },
    { label := "symfrak H /text", body := "\\symfrak{H}", sym := false },
    -- the same \sym… under the overridden (sym) policy — must agree with /text
    { label := "symbf x /sym", body := "\\symbf{x}" },
    { label := "symsf R /sym", body := "\\symsf{R}" },
    { label := "symtt k /sym", body := "\\symtt{k}" },
    { label := "symrm d /sym", body := "\\symrm{d}" },
    -- \symbfit: Latin, Greek, nabla
    { label := "symbfit x", body := "\\symbfit{x}" },
    { label := "symbfit gamma", body := "\\symbfit{\\gamma}" },
    { label := "symbfit nabla", body := "\\symbfit{\\nabla}" },
    { label := "symbfit X", body := "\\symbfit{X}" },
    { label := "symbfit Gamma", body := "\\symbfit{\\Gamma}" } ]

/-- Read one exactly named, quoted attribute in Ghostscript's line format.
Missing, duplicated or unterminated attributes are not observations. -/
def attrOf (line attr : String) : Option String := do
  let [_, after] := line.splitOn (" " ++ attr ++ "=\"") | none
  let value :: _ :: _ := after.splitOn "\"" | none
  some value

/-- Add an alias only with evidence that the two names refer to the same
input font file, documenting that file beside the entry. No aliases today;
family, weight, italic and slot differences must remain differences. -/
def fontAlias : List (String × String) := []

/-- ISO 32000 subset tags have six uppercase ASCII letters. The exact
-Identity-H/V suffix is Ghostscript's font/CMap spelling. This compares
resource names, not the bytes of embedded font programs. -/
def normFont (s0 : String) : String :=
  let s1 := match s0.splitOn "+" with
    | [tag, rest] =>
      if tag.length == 6 && tag.toList.all (fun c => 'A' ≤ c && c ≤ 'Z')
      then rest else s0
    | _ => s0
  let s2 :=
    if s1.endsWith "-Identity-H" then (s1.dropEnd "-Identity-H".length).toString
    else if s1.endsWith "-Identity-V" then (s1.dropEnd "-Identity-V".length).toString
    else s1
  (fontAlias.lookup s2).getD s2

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def hexNatGo (n : Nat) : List Char → Option Nat
  | [] => some n
  | c :: rest => do
    let d ← hexDigit c
    hexNatGo (n * 16 + d) rest

/-- Ghostscript emits one scalar or UTF-16 code unit in each char attribute.
Decode only that spelling, not the first character of arbitrary text. -/
def codeUnit (s : String) : Option Nat :=
  if s.startsWith "&#x" && s.endsWith ";" then
    let digits := ((s.drop 3).dropEnd 1).toString.toList
    if digits.isEmpty then none else hexNatGo 0 digits
  else if s.startsWith "&#" && s.endsWith ";" then
    let digits := ((s.drop 2).dropEnd 1).toString
    if digits.isEmpty || !digits.toList.all (fun c => '0' ≤ c && c ≤ '9')
    then none else digits.toNat?
  else match s with
    | "&amp;" => some '&'.toNat
    | "&lt;" => some '<'.toNat
    | "&gt;" => some '>'.toNat
    | "&quot;" => some '"'.toNat
    | "&apos;" => some '\''.toNat
    | _ => match s.toList with
      | [c] => if c == '&' || c == '<' || c == '"' then none else some c.toNat
      | _ => none

def scalarOfUnits (units : Array Nat) : Option Char :=
  match units.toList with
  | [hi, lo] =>
    if 0xD800 ≤ hi && hi ≤ 0xDBFF && 0xDC00 ≤ lo && lo ≤ 0xDFFF then
      some (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)))
    else none
  | [u] =>
    if u ≤ 0x10FFFF && !(0xD800 ≤ u && u ≤ 0xDFFF) then some (Char.ofNat u)
    else none
  | _ => none

def milli (s : String) : Option Int := do
  let (mantissa, scale) ← Decl.parseDecimal s
  pure (mantissa * 1000 / (scale : Int))

/-- Horizontal extent in Ghostscript's integer device coordinates. Require
the whole box even though this report compares only its width. -/
def bboxX (s : String) : Option (Int × Int) := do
  let [a, b, c, d] := (s.splitOn " ").filter (!·.isEmpty) | none
  let x0 ← a.toInt?
  let y0 ← b.toInt?
  let x1 ← c.toInt?
  let y1 ← d.toInt?
  if x0 ≤ x1 && y0 ≤ y1 then some (x0, x1) else none

/-- Read Ghostscript txtwrite TextFormat=0, not arbitrary XML. A bad span
invalidates the observation, including when a later span is well formed.
Every character survives; a UTF-16 pair gets the union of its two boxes
(Ghostscript normally puts the width on the high unit and zero on the low).
Span segmentation is not part of the comparison. -/
def parseGlyphs (xml : String) : Except String (Array GlyphFact) := do
  let mut out : Array GlyphFact := #[]
  let mut span : Option (String × Int × Nat) := none
  let mut high : Option (Nat × Int × Int) := none
  let mut inPage := false
  let mut pages := 0
  for (raw, index) in (xml.splitOn "\n").zipIdx do
    let line := raw.trimAscii.toString
    let loc := s!"line {index + 1}"
    if line.isEmpty then continue
    if line == "<page>" then
      if inPage || span.isSome then throw s!"{loc}: nested page"
      inPage := true
      pages := pages + 1
    else if line == "</page>" then
      if !inPage || span.isSome then throw s!"{loc}: unclosed span or unmatched page"
      inPage := false
    else if line.startsWith "<span " && line.endsWith ">" then
      if !inPage || span.isSome then throw s!"{loc}: span outside page or nested span"
      let some font := (attrOf line "font").map normFont
        | throw s!"{loc}: missing or malformed font"
      if font.trimAscii.toString.isEmpty then throw s!"{loc}: empty font"
      let some size := (attrOf line "size").bind milli
        | throw s!"{loc}: missing or malformed point size"
      if size ≤ 0 then throw s!"{loc}: nonpositive point size"
      let some _ := (attrOf line "bbox").bind bboxX
        | throw s!"{loc}: missing or malformed span box"
      span := some (font, size, out.size)
    else if line.startsWith "<char " && line.endsWith "/>" then
      let some (font, size, _) := span | throw s!"{loc}: char outside span"
      let some unit := (attrOf line "c").bind codeUnit
        | throw s!"{loc}: missing or malformed character"
      let some (x0, x1) := (attrOf line "bbox").bind bboxX
        | throw s!"{loc}: missing or malformed character box"
      if let some (hi, a, b) := high then
        let some c := scalarOfUnits #[hi, unit] | throw s!"{loc}: invalid UTF-16 pair"
        out := out.push
          { scalar := String.singleton c, font, width := max b x1 - min a x0, sizeMilli := size }
        high := none
      else if 0xD800 ≤ unit && unit ≤ 0xDBFF then
        high := some (unit, x0, x1)
      else
        let some c := scalarOfUnits #[unit] | throw s!"{loc}: invalid scalar"
        out := out.push
          { scalar := String.singleton c, font, width := x1 - x0, sizeMilli := size }
    else if line == "</span>" then
      let some (_, _, start) := span | throw s!"{loc}: unmatched span"
      if high.isSome then throw s!"{loc}: unpaired surrogate"
      if out.size == start then throw s!"{loc}: empty text span"
      span := none
    else throw s!"{loc}: unsupported txtwrite record"
  if inPage || span.isSome || pages == 0 then throw "truncated or absent page"
  return out

structure Comparison where
  face : Bool
  size : Bool
  width : Bool
  deriving Repr, BEq

/-- Each axis compares complete sequences. Face alone is blind to size and
width; the overall verdict is not. Empty observations never pass. -/
def compareGlyphs (r e : Array GlyphFact) : Comparison :=
  { face := !r.isEmpty && r.map (fun g => (g.scalar, g.font)) == e.map (fun g => (g.scalar, g.font))
    size := !r.isEmpty && r.map (·.sizeMilli) == e.map (·.sizeMilli)
    width := !r.isEmpty && r.map (·.width) == e.map (·.width) }

def Comparison.passes (c : Comparison) : Bool := c.face && c.size && c.width

def verdict (r e : Array GlyphFact) : Bool := (compareGlyphs r e).passes

def firstLine (s : String) : String :=
  ((s.splitOn "\n").headD "unknown").trimAscii.toString

def runTool (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO IO.Process.Output := do
  let out ← IO.Process.output { cmd, args, cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"{cmd} exited {out.exitCode}: {(out.stdout ++ out.stderr).trimAscii.toString}")
  return out

def version (cmd : String) (args : Array String)
    (cwd : System.FilePath) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args, cwd }
    if out.exitCode == 0 then return some (firstLine (out.stdout ++ out.stderr))
    return none
  catch _ => return none

def preambleFor (c : Case) : String :=
  if c.sym then
    "\\usepackage[mathrm=sym,mathit=sym,mathbf=sym,mathsf=sym,mathtt=sym]{unicode-math}\n"
  else "\\usepackage{unicode-math}\n"

/-- The same explicit input files in both engines. The text slots are
aliased deliberately; this matrix does not exercise distinct slot faces. -/
def texSource (bodyFontDir : String) (face : FaceCase) (c : Case) : String :=
  let p := System.FilePath.mk face.path
  let dir := (p.parent.getD ".").toString
  let file := p.fileName.getD face.path
  "\\documentclass{article}\n" ++
  "\\usepackage{fontspec}\n" ++
  preambleFor c ++
  s!"\\setmainfont\{OpenSans-Regular.ttf}[Path={bodyFontDir}/,BoldFont=OpenSans-Bold.ttf,ItalicFont=OpenSans-Italic.ttf,BoldItalicFont=OpenSans-BoldItalic.ttf]\n" ++
  s!"\\setsansfont\{OpenSans-Regular.ttf}[Path={bodyFontDir}/,BoldFont=OpenSans-Bold.ttf,ItalicFont=OpenSans-Italic.ttf,BoldItalicFont=OpenSans-BoldItalic.ttf]\n" ++
  s!"\\setmonofont\{OpenSans-Regular.ttf}[Path={bodyFontDir}/]\n" ++
  s!"\\setmathfont[Scale=MatchLowercase]\{{file}}[Path={dir}/]\n" ++
  "\\pagestyle{empty}\n\\begin{document}\n$" ++ c.body ++
  "$\n\\end{document}\n"

/-- A filesystem-safe stem: letters and digits kept, everything else a dash. -/
def slug (s : String) : String :=
  String.ofList (s.toList.map fun ch =>
    if ('a' ≤ ch && ch ≤ 'z') || ('A' ≤ ch && ch ≤ 'Z') || ('0' ≤ ch && ch ≤ '9')
    then ch else '-')

def extract (root work : System.FilePath) (tag : String)
    (pdf : System.FilePath) : IO (Except String (Array GlyphFact)) := do
  let xml := work / s!"{tag}.xml"
  let _ ← runTool "gs" #["-q", "-dNOPAUSE", "-dBATCH", "-r720",
    "-sDEVICE=txtwrite", "-dTextFormat=0", s!"-sOutputFile={xml}", pdf.toString] root
  return parseGlyphs (← IO.FS.readFile xml)

/-- Positive observations and adversarial neighbours. The first twelve
checks reproduce the review's fail-first witnesses on the old reader and
comparator; sequence checks now retain all spans rather than requiring a
single glyph. No external tool is needed for these guards. -/
def selftest : IO UInt32 := do
  let page (s : String) := "<page>\n" ++ s ++ "\n</page>\n"
  let sample := "<span bbox=\"1 2 9 12\" font=\"ABCDEF+FiraMath-Regular-Identity-H\" size=\"10.000\">\n" ++
    "<char bbox=\"1 2 9 12\" c=\"&#xd835;\"/>\n" ++
    "<char bbox=\"9 2 9 12\" c=\"&#xdc42;\"/>\n</span>"
  let bmp := "<span bbox=\"0 0 10 12\" font=\"XYZABC+OpenSans-Bold-Identity-H\" size=\"10.000\">\n" ++
    "<char bbox=\"0 0 10 12\" c=\"&#x0052;\"/>\n</span>"
  let last := "<span bbox=\"10 0 21 12\" font=\"XYZABC+OpenSans-Bold-Identity-H\" size=\"10.000\">\n" ++
    "<char bbox=\"10 0 21 12\" c=\"S\"/>\n</span>"
  let multi := (bmp.replace "bbox=\"0 0 10 12\" font=" "bbox=\"0 0 21 12\" font=").replace
    "</span>" "<char bbox=\"10 0 21 12\" c=\"S\"/>\n</span>"
  let noFace := bmp.replace "font=\"XYZABC+OpenSans-Bold-Identity-H\"" ""
  let o : GlyphFact := { scalar := "𝑂", font := "FiraMath-Regular", width := 8, sizeMilli := 10000 }
  let r : GlyphFact := { scalar := "R", font := "OpenSans-Bold", width := 10, sizeMilli := 10000 }
  let s : GlyphFact := { r with scalar := "S", width := 11 }
  let wide : GlyphFact := { r with width := 72 }
  let large : GlyphFact := { r with sizeMilli := 12000 }
  let checks : List (String × Bool) := [
    ("reject an extra painted glyph", !verdict #[o] #[o, r]),
    ("retain a multi-character span before a valid span", (parseGlyphs (page (multi ++ "\n" ++ sample))).toOption == some #[r, s, o]),
    ("reject missing font evidence", (parseGlyphs (page noFace)).toOption.isNone),
    ("only strip six-uppercase-letter subset prefixes", normFont "notatag+FiraMath-Regular" == "notatag+FiraMath-Regular"),
    ("reject unpaired surrogate", (scalarOfUnits #[0xd800]).isNone),
    ("reject out-of-range scalar", (scalarOfUnits #[0x110000]).isNone),
    ("reject malformed entity", (codeUnit "&unknown;").isNone),
    ("reject multiple literal chars", (codeUnit "AB").isNone),
    ("decode named XML entity", codeUnit "&lt;" == some 60),
    ("reject empty hex entity", (codeUnit "&#x;").isNone),
    ("full verdict detects width drift", !verdict #[r] #[wide]),
    ("full verdict detects size drift", !verdict #[r] #[large]),
    ("BMP observation", (parseGlyphs (page bmp)).toOption == some #[r]),
    ("surrogate observation", (parseGlyphs (page sample)).toOption == some #[o]),
    ("scalar entity agrees with surrogate pair", (parseGlyphs (page (bmp.replace "&#x0052;" "&#x1d442;"))).toOption == some #[{ r with scalar := "𝑂" }]),
    ("span splitting preserves per-character boxes", (parseGlyphs (page multi)).toOption == some #[r, s] && (parseGlyphs (page (bmp ++ "\n" ++ last))).toOption == some #[r, s]),
    ("true complete match", verdict #[r, s, o] #[r, s, o]),
    ("missing glyph", !verdict #[r, s] #[r]),
    ("different later scalar", !verdict #[r, s] #[r, { s with scalar := "T" }]),
    ("different later face", !verdict #[r, s] #[r, { s with font := "OpenSans-Regular" }]),
    ("different glyph order", !verdict #[r, s] #[s, r]),
    ("size axis stays separate", compareGlyphs #[r] #[large] == { face := true, size := false, width := true }),
    ("width axis stays separate", compareGlyphs #[r] #[wide] == { face := true, size := true, width := false }),
    ("face axis stays separate", compareGlyphs #[r] #[{ r with font := "OpenSans-Regular" }] == { face := false, size := true, width := true }),
    ("empty observations cannot pass", !verdict #[] #[]),
    ("empty page retains its empty observation", (parseGlyphs (page "")).toOption == some #[]),
    ("known subset/CMap spellings agree", normFont "ABCDEF+FiraMath-Regular-Identity-H" == normFont "UVWXYZ+FiraMath-Regular-Identity-V"),
    ("bare name survives", normFont "FiraMath-Regular" == "FiraMath-Regular"),
    ("unknown plus prefix survives", normFont "OpenSans+Bold" == "OpenSans+Bold"),
    ("case is significant", normFont "FiraMath-Regular" != normFont "firamath-regular"),
    ("weight is significant", normFont "OpenSans-Bold" != normFont "OpenSans-Regular"),
    ("italic is significant", normFont "OpenSans-Italic" != normFont "OpenSans-Regular"),
    ("family is significant", normFont "FiraSans-Regular" != normFont "OpenSans-Regular"),
    ("other CMap spellings survive", normFont "ABCDEF+FiraMath-Regular-Identity-H-extra" == "FiraMath-Regular-Identity-H-extra"),
    ("strict attribute name", (attrOf "<span notfont=\"Fira\">" "font").isNone),
    ("duplicate attribute", (attrOf "<span font=\"Fira\" font=\"Other\">" "font").isNone),
    ("unterminated attribute", (attrOf "<span font=\"Fira>" "font").isNone),
    ("decimal entity", codeUnit "&#82;" == some 82),
    ("literal scalar", codeUnit "𝑂" == some 0x1d442),
    ("pair bounds", scalarOfUnits #[0xd800, 0xdc00] == some (Char.ofNat 0x10000) && scalarOfUnits #[0xdbff, 0xdfff] == some (Char.ofNat 0x10ffff)),
    ("reversed pair", (scalarOfUnits #[0xdc42, 0xd835]).isNone),
    ("unpaired low surrogate", (scalarOfUnits #[0xdc42]).isNone),
    ("missing box cannot read as zero", (parseGlyphs (page (bmp.replace "bbox=\"0 0 10 12\"" ""))).toOption.isNone),
    ("missing size cannot read as zero", (parseGlyphs (page (bmp.replace "size=\"10.000\"" ""))).toOption.isNone),
    ("malformed box", (bboxX "0 0 10 nope").isNone),
    ("reversed box", (bboxX "10 0 0 12").isNone),
    ("numeric resolution", milli "9.9626" == some 9962),
    ("bad span never vanishes before a good one", (parseGlyphs (page (noFace ++ "\n" ++ sample))).toOption.isNone),
    ("bad character never vanishes before a good one", (parseGlyphs (page ((bmp.replace "&#x0052;" "&unknown;") ++ "\n" ++ sample))).toOption.isNone),
    ("unclosed span", (parseGlyphs (page (bmp.replace "</span>" ""))).toOption.isNone),
    ("unmatched span", (parseGlyphs (page "</span>")).toOption.isNone),
    ("nested span", (parseGlyphs (page (bmp.replace "</span>" (sample ++ "\n</span>")))).toOption.isNone),
    ("unpaired high in span", (parseGlyphs (page (bmp.replace "&#x0052;" "&#xd835;"))).toOption.isNone),
    ("out-of-range character in span", (parseGlyphs (page (bmp.replace "&#x0052;" "&#x110000;"))).toOption.isNone),
    ("empty text span", (parseGlyphs (page (bmp.replace "<char bbox=\"0 0 10 12\" c=\"&#x0052;\"/>\n" ""))).toOption.isNone),
    ("absent observation", (parseGlyphs "").toOption.isNone),
    ("truncated page", (parseGlyphs ((page bmp).replace "</page>" "")).toOption.isNone),
    ("unknown record", (parseGlyphs (page (bmp ++ "\n<unknown/>"))).toOption.isNone),
    ("all pages read", (parseGlyphs (page bmp ++ page sample)).toOption == some #[r, o]),
    ("distinct matrix output paths", (cases.map (fun c => slug c.label)).eraseDups.length == cases.length)]
  let failures := checks.filter fun row => !row.2
  for (name, _) in failures do IO.eprintln s!"FAIL {name}"
  IO.println s!"math-alphabet-diff --selftest: {checks.length} checks, {failures.length} failures"
  return if failures.isEmpty then 0 else 1

/-- JSON arrays keep all glyphs and escape separators in TSV cells. -/
def column [Lean.ToJson α] (xs : Array α) : String := (Lean.toJson xs).compress

def mark (ok : Bool) : String := if ok then "SAME" else "DIFF"

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  let root ← IO.currentDir
  let bin := root / ".lake" / "build" / "bin" / "leantex"
  unless ← bin.pathExists do
    IO.eprintln "math-alphabet-diff: build leantex first"
    return 2
  let some luaVersion ← version "lualatex" #["--version"] root
    | IO.eprintln "math-alphabet-diff: lualatex unavailable — untested"; return 2
  let some gsVersion ← version "gs" #["--version"] root
    | IO.eprintln "math-alphabet-diff: ghostscript unavailable — untested"; return 2
  let fira ← IO.FS.realPath (root / "tests" / "corpus" / "fonts" / "FiraMath-Regular.otf")
  let required : List (String × String) :=
    [("Latin Modern Math", "latinmodern-math.otf"),
     ("TeX Gyre Pagella Math", "texgyrepagella-math.otf"),
     ("STIX Two Math", "STIXTwoMath-Regular.otf")]
  let mut faces : Array FaceCase := #[{ label := "Fira Math", path := fira.toString }]
  for (label, file) in required do
    let found ← try
      let out ← IO.Process.output { cmd := "kpsewhich", args := #[file], cwd := root }
      if out.exitCode == 0 then pure out.stdout.trimAscii.toString else pure ""
    catch _ => pure ""
    if found.isEmpty then
      IO.eprintln s!"math-alphabet-diff: {file} unavailable — four-face matrix untested"
      return 2
    faces := faces.push { label, path := found }
  let work := root / ".lake" / "math-alphabet-diff"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let bodyFontDir := (root / "tests" / "corpus" / "fonts").toString
  IO.println "math-alphabet-diff: LuaLaTeX/leantex alphabet matrix"
  IO.println s!"  lualatex: {luaVersion}"
  IO.println s!"  ghostscript: {gsVersion}"
  IO.println "  widths: character bbox at 720 dpi; sizes: thousandths of a PDF point"
  IO.println "face\tcase\tsrc\tref-scalars\tengine-scalars\tref-fonts\tengine-fonts\tref-widths\tengine-widths\tref-sizes\tengine-sizes\tface-axis\tsize-axis\twidth-axis\tresult"
  let mut rows := 0
  let mut passed := 0
  let mut diffs := 0
  let mut missing := 0
  let mut errors := 0
  let mut faceDiffs := 0
  let mut sizeDiffs := 0
  let mut widthDiffs := 0
  for face in faces do
    for c in cases do
      rows := rows + 1
      let stem := slug face.label ++ "-" ++ slug c.label
      let src := work / s!"{stem}.tex"
      let srcTag := if c.sym then "sym" else "text"
      let rowPrefix := s!"{face.label}\t{c.label}\t{srcTag}"
      try
        IO.FS.writeFile src (texSource bodyFontDir face c)
        let _ ← runTool "lualatex"
          #["-halt-on-error", "-interaction=batchmode", s!"-output-directory={work}", src.toString] root
        let refPdf := work / s!"{stem}.pdf"
        let enginePdf := work / s!"{stem}-engine.pdf"
        let _ ← runTool bin.toString #[src.toString, "-o", enginePdf.toString, "-q"] root
        let refFact ← extract root work (stem ++ "-ref") refPdf
        let engineFact ← extract root work (stem ++ "-engine") enginePdf
        match refFact, engineFact with
        | .ok r, .ok e =>
          if r.isEmpty || e.isEmpty then
            missing := missing + 1
            IO.println s!"{rowPrefix}\t{column (r.map (·.scalar))}\t{column (e.map (·.scalar))}\t?\t?\t?\t?\t?\t?\t?\t?\t?\tMISSING(empty sequence)"
          else
            let cmp := compareGlyphs r e
            if cmp.passes then passed := passed + 1 else diffs := diffs + 1
            if !cmp.face then faceDiffs := faceDiffs + 1
            if !cmp.size then sizeDiffs := sizeDiffs + 1
            if !cmp.width then widthDiffs := widthDiffs + 1
            IO.println s!"{rowPrefix}\t{column (r.map (·.scalar))}\t{column (e.map (·.scalar))}\t{column (r.map (·.font))}\t{column (e.map (·.font))}\t{column (r.map (·.width))}\t{column (e.map (·.width))}\t{column (r.map (·.sizeMilli))}\t{column (e.map (·.sizeMilli))}\t{mark cmp.face}\t{mark cmp.size}\t{mark cmp.width}\t{if cmp.passes then "PASS" else "DIFF"}"
        | _, _ =>
          missing := missing + 1
          let why (side : String) (fact : Except String (Array GlyphFact)) := match fact with
            | .ok _ => s!"{side}: read"
            | .error msg => s!"{side}: {msg}"
          IO.println s!"{rowPrefix}\t?\t?\t?\t?\t?\t?\t?\t?\t?\t?\t?\tMISSING({why "reference" refFact}; {why "engine" engineFact})"
      catch e =>
        errors := errors + 1
        IO.FS.writeFile (work / s!"{stem}.error.log") e.toString
        IO.println s!"{rowPrefix}\t?\t?\t?\t?\t?\t?\t?\t?\t?\t?\t?\tERROR({firstLine e.toString})"
  IO.println s!"math-alphabet-diff: rows={rows} pass={passed} diff={diffs} missing={missing} errors={errors}"
  IO.println s!"  observed axis differences: face={faceDiffs} size={sizeDiffs} width={widthDiffs}"
  if diffs == 0 && missing == 0 && errors == 0 then
    IO.println "math-alphabet-diff: PASS"
    return 0
  IO.eprintln "math-alphabet-diff: DIFF (MISSING/ERROR rows are untested, not matches)"
  return 1
