/-
External math-alphabet differential. Run from the repository root:

  lake build leantex
  lake env lean --run scripts/math-alphabet-diff.lean
  lake env lean --run scripts/math-alphabet-diff.lean --selftest

This is a report, never a hermetic gate. It writes only below
`.lake/math-alphabet-diff` and compares LuaLaTeX with leantex over four math
faces and a wide alphabet matrix. Ghostscript reads each PDF's painted
scalar, font, advance, and point size — no IR dump, no emitted CSS, and no
source spelling is ever an observation; every verdict is from the artifact.

Every row is a FULL comparison on the face axis: the painted scalar AND the
selected font family/weight/italic/slot must agree (the normalized font name
IS that axis). Point size and advance are reported but NOT gated — a
text-sourced alphabet renders text-in-math at a size the engine derives from
the math face's `Scale=MatchLowercase` factor, so on a face whose factor
departs from 1 (Latin Modern scales ~1.24) the advance is visibly larger
than LuaLaTeX's, which sets text-in-math at the ambient size. That is a real
but SEPARATE sizing axis, orthogonal to which face/weight/italic was
selected; gating on it would conflate the two and bury the face finding, so
the advance columns expose it and leave it for a follow-up. There is no
scalar-only escape hatch: a text-policy alphabet (`\mathrm`/`\mathit`/
`\mathbf`/`\mathsf`/`\mathtt` under unicode-math's default) projects to a
real text family, and the report holds the engine's chosen face to
LuaLaTeX's. For that comparison to be fair the generated preamble gives
LuaLaTeX the SAME shipped OpenSans files the engine's font environment
carries: the full family (bold, italic, bold italic) as main, and the sans
and mono slots pointed at OpenSans too — the engine ships no distinct
sans/mono face, so its `.sf`/`.tt` slots fall to the body (`FontSet.lookup`),
and declaring the same here is what makes `\mathsf`/`\mathtt` name one
shipped file on both sides. Font names are compared after stripping the PDF
subset tag (`ABCDEF+`) and the CMap suffix (`-Identity-H`), with an explicit
alias table for the rare case where the two engines name the same shipped
file differently.

Scope notes carried on the rows: Greek under the text policy is NOT a
text-family projection (unicode-math keeps it a math-bold alphanumeric), and
`\bm` cannot be a row (LuaLaTeX's bm package falls to Computer Modern and
errors on `\bm{\alpha}`); both are harness limits, not engine signals. The
one engine FACE divergence the matrix surfaces is `bf(cal A)` under the text
policy on a face lacking the inner alphabet's glyph — see that row.
-/

import LeanTex

open LeanTex.Core

structure GlyphFact where
  scalar : String
  font : String
  advance : Int
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

/-- The widened matrix. The sym single-letter and per-range anchors stand
first; then Letterlike holes, nested alphabet stacks across both policies,
`\boldsymbol`, the text-policy legacy alphabets whose face the report now
checks, Greek under the text policy, every `\sym…` under both the default
and the overridden policy (they are symbol-sourced regardless, so the two
must agree), `\symbfit` over Latin/Greek/∇, and `\bm`. Every body is one
painted formula so `formulaGlyph` reads it. -/
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
    -- nesting across policies: a text-sourced inner wins its own range, and
    -- the policy decides whether `\mathrm`/`\mathbf` are text or sym. The
    -- `bf(cal A) text` row is the one surfaced engine divergence: when the
    -- inner `\mathcal` is uncovered (a face lacking script A, e.g. Fira) the
    -- engine falls the character through to the OUTER text `\mathbf` and
    -- projects it to a text family, while LuaLaTeX keeps it in the math face.
    -- On a face that carries script A (STIX/LM/Pagella) the inner wins on
    -- both sides and the row passes. Matching Fira exactly needs unicode-math
    -- uncovered-fallback semantics (LuaLaTeX paints a plain upright base, not
    -- the engine's bold or the source italic) — a dedicated follow-up; the
    -- row is kept so the oracle reports the divergence rather than hiding it.
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
    -- Greek is NOT text-projected under the text policy: unicode-math keeps
    -- it a math-bold alphanumeric (sym-sourced), so `\mathbf{\Gamma}` stays
    -- in the math face. The legacy-command Greek rows are therefore the sym
    -- Greek anchors above (`bf Greek up`, `it Greek low/up`, `symbfup`,
    -- `symbfit gamma/Gamma/nabla`); a bare `\mathbf{\Gamma}` is not added as
    -- a text-family row because there is no text projection to compare, and
    -- on a face lacking the math-bold-Greek glyph (Fira) LuaLaTeX paints
    -- nothing at all — a harness coverage gap, not an engine signal.
    -- every \sym… under the default (text) policy — symbol-sourced regardless
    { label := "symrm d /text", body := "\\symrm{d}", sym := false },
    { label := "symit y /text", body := "\\symit{y}", sym := false },
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
    -- `\bm`/`\boldsymbol`: `\boldsymbol` (the sym-sourced rows above) is the
    -- comparable differential and the engine's bold-symbol path. `\bm` is NOT
    -- a row here: with no bold math *version* declared, LuaLaTeX's bm package
    -- routes `\bm` through Computer Modern (`\bm{5}` → CMBX10) and errors
    -- outright on `\bm{\alpha}` (no CM bold Greek), so it shares no shipped
    -- file with the engine and cannot even build — a harness limitation, not
    -- an engine signal. The engine's `\bm`-vs-`\boldsymbol` split is held by
    -- the in-repo tests instead.

def attrOf (line attr : String) : Option String := do
  let after ← ((line.splitOn (attr ++ "=\"")).drop 1).head?
  (after.splitOn "\"").head?

/-- Same shipped file, different name across the two engines. Narrow by
design: an entry belongs here only when LuaLaTeX and leantex subset the
SAME font file under two spellings — never to paper over a genuine
family/weight/italic difference. Empty today; the four math faces and the
OpenSans text family subset-name identically on both sides. -/
def fontAlias : List (String × String) := []

/-- The shipped-file identity of a painted span: drop the PDF subset tag
(`ABCDEF+`), drop the CMap suffix (`-Identity-H`/`-Identity-V`), then apply
the alias table. What remains names the font file, which is what a
family/weight/italic comparison turns on. -/
def normFont (s0 : String) : String :=
  let s1 := match s0.splitOn "+" with
    | [_tag, rest] => rest
    | _ => s0
  let s2 :=
    if s1.endsWith "-Identity-H" then (s1.dropEnd "-Identity-H".length).toString
    else if s1.endsWith "-Identity-V" then (s1.dropEnd "-Identity-V".length).toString
    else s1
  (fontAlias.lookup s2).getD s2

def hexDigit : Char → Option Nat
  | c =>
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
    else none

def hexNatGo (n : Nat) : List Char → Option Nat
  | [] => some n
  | c :: rest => do
    let d ← hexDigit c
    hexNatGo (n * 16 + d) rest

def codeUnit (s : String) : Option Nat :=
  if s.startsWith "&#x" && s.endsWith ";" then
    hexNatGo 0 ((s.drop 3).dropEnd 1).toString.toList
  else s.toList.head?.map (·.toNat)

def scalarOfUnits (units : Array Nat) : Option Char :=
  match units.toList with
  | [hi, lo] =>
    if 0xD800 ≤ hi && hi ≤ 0xDBFF && 0xDC00 ≤ lo && lo ≤ 0xDFFF then
      some (Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)))
    else none
  | [u] => some (Char.ofNat u)
  | _ => none

def milli (s : String) : Option Int := do
  let (mantissa, scale) ← Decl.parseDecimal s
  pure (mantissa * 1000 / (scale : Int))

def bboxWidth (s : String) : Option Int := do
  let parts := s.splitOn " "
  let x0 ← parts[0]?.bind String.toInt?
  let x1 ← parts[2]?.bind String.toInt?
  pure (x1 - x0)

def parseGlyphs (xml : String) : Array GlyphFact := Id.run do
  let mut out : Array GlyphFact := #[]
  let mut font := ""
  let mut advance := 0
  let mut sizeMilli := 0
  let mut units : Array Nat := #[]
  for raw in xml.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.startsWith "<span " then
      font := normFont ((attrOf line "font").getD "")
      advance := (attrOf line "bbox").bind bboxWidth |>.getD 0
      sizeMilli := (attrOf line "size").bind milli |>.getD 0
      units := #[]
    else if line.startsWith "<char " then
      if let some u := (attrOf line "c").bind codeUnit then units := units.push u
    else if line == "</span>" then
      if let some c := scalarOfUnits units then
        out := out.push { scalar := String.ofList [c], font, advance, sizeMilli }
      units := #[]
  return out

def formulaGlyph (facts : Array GlyphFact) : Option GlyphFact :=
  facts[0]?

/-- The face verdict: the painted scalar AND the shipped font file must
agree. That pair IS the comparison this report exists for — the normalized
font name carries the family, the slot (serif/sans/mono), the weight, and
the italic axis, and the scalar carries which alphabet/character landed, so
`scalar == && font ==` is exactly "same face, weight, italic, slot, glyph".

Point size and advance are reported but NOT gated. A text-sourced alphabet
renders text-in-math at a size the engine derives from the math face's
`Scale=MatchLowercase` factor, so on a face whose factor departs from 1
(Latin Modern scales ~1.24) the advance is visibly larger than LuaLaTeX's,
which sets text-in-math at the ambient size — a real but SEPARATE sizing
axis, orthogonal to which face/weight/italic was selected, left for a
follow-up. Gating on advance here would conflate that sizing divergence with
face selection and bury the one face finding the matrix exists to surface.

The single owner of PASS/DIFF, shared by `main` and `--selftest`, so a
weakening cannot slip into one without the other. -/
def verdict (r e : GlyphFact) : Bool :=
  r.scalar == e.scalar && r.font == e.font

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

/-- The generated document. The text families LuaLaTeX reads are exactly the
shipped OpenSans files the engine's font environment carries — the full
family (bold/italic/bold-italic) as main, and the sans and mono slots on
OpenSans too, since the engine ships no distinct sans/mono face and falls
those slots to the body. That is what makes a text-policy alphabet name one
shipped file on both sides, so the comparison is of face, not of two
engines' unrelated defaults. -/
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
    (pdf : System.FilePath) : IO (Option GlyphFact) := do
  let xml := work / s!"{tag}.xml"
  let _ ← runTool "gs" #["-q", "-dNOPAUSE", "-dBATCH", "-r720",
    "-sDEVICE=txtwrite", "-dTextFormat=0", s!"-sOutputFile={xml}", pdf.toString] root
  return formulaGlyph (parseGlyphs (← IO.FS.readFile xml))

/-- The parser round-trips a surrogate-pair math scalar and a BMP text
scalar, and — the guard that keeps the oracle strong — `verdict` rejects a
font difference even when the scalar agrees, and a scalar difference even
when the font agrees. A regression that let a face difference pass (the old
`scalarOnly`/`PASS(text)` leniency, which compared scalars and waved the
font divergence through) fails here. -/
def selftest : IO UInt32 := do
  let sample := "<span bbox=\"1 2 9 12\" font=\"ABCDEF+FiraMath-Regular-Identity-H\" size=\"10.000\">\n" ++
    "<char bbox=\"1 2 9 12\" c=\"&#xd835;\"/>\n" ++
    "<char bbox=\"9 2 9 12\" c=\"&#xdc42;\"/>\n</span>"
  let want : Array GlyphFact :=
    #[{ scalar := "𝑂", font := "FiraMath-Regular", advance := 8, sizeMilli := 10000 }]
  let bmp := "<span bbox=\"0 0 10 12\" font=\"XYZABC+OpenSans-Bold-Identity-H\" size=\"10.000\">\n" ++
    "<char bbox=\"0 0 10 12\" c=\"&#x0052;\"/>\n</span>"
  let wantBmp : Array GlyphFact :=
    #[{ scalar := "R", font := "OpenSans-Bold", advance := 10, sizeMilli := 10000 }]
  let parseOk := parseGlyphs sample == want && parseGlyphs bmp == wantBmp
  -- The comparator rejects a face (font) difference and a scalar difference,
  -- and accepts a true match EVEN when the advance differs (the sizing axis
  -- is deliberately not gated). This is the property the text-policy rows
  -- rest on: same scalar is not enough, and a wrong weight (OpenSans-Regular
  -- vs OpenSans-Bold is a different shipped file) must fail.
  let base : GlyphFact := { scalar := "R", font := "OpenSans-Regular", advance := 50, sizeMilli := 10000 }
  let sameFaceFarAdvance : GlyphFact := { base with advance := 72 }
  let diffWeight : GlyphFact := { base with font := "OpenSans-Bold" }
  let diffScalar : GlyphFact := { base with scalar := "S" }
  let cmpOk :=
    verdict base base == true &&
    verdict base sameFaceFarAdvance == true &&
    verdict base diffWeight == false &&
    verdict base diffScalar == false
  if parseOk && cmpOk then
    IO.println "math-alphabet-diff --selftest: all passed"
    return 0
  IO.eprintln s!"math-alphabet-diff --selftest: FAIL parse={parseOk} cmp={cmpOk}"
  IO.eprintln s!"  {repr (parseGlyphs sample)} {repr (parseGlyphs bmp)}"
  return 1

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
  IO.println "face\tcase\tsrc\tref-scalar\tengine-scalar\tref-font\tengine-font\tref-adv\tengine-adv\tresult"
  let mut rows := 0
  let mut passed := 0
  let mut diffs := 0
  let mut missing := 0
  for face in faces do
    for c in cases do
      rows := rows + 1
      let stem := slug face.label ++ "-" ++ slug c.label
      let src := work / s!"{stem}.tex"
      IO.FS.writeFile src (texSource bodyFontDir face c)
      let _ ← runTool "lualatex"
        #["-halt-on-error", "-interaction=batchmode", s!"-output-directory={work}", src.toString] root
      let refPdf := work / s!"{stem}.pdf"
      let enginePdf := work / s!"{stem}-engine.pdf"
      let _ ← runTool bin.toString #[src.toString, "-o", enginePdf.toString, "-q"] root
      let refFact ← extract root work (stem ++ "-ref") refPdf
      let engineFact ← extract root work (stem ++ "-engine") enginePdf
      let srcTag := if c.sym then "sym" else "text"
      match refFact, engineFact with
      | some r, some e =>
        let ok := verdict r e
        if ok then passed := passed + 1 else diffs := diffs + 1
        let mark := if ok then "PASS" else "DIFF"
        IO.println s!"{face.label}\t{c.label}\t{srcTag}\t{r.scalar}\t{e.scalar}\t{r.font}\t{e.font}\t{r.advance}\t{e.advance}\t{mark}"
      | _, _ =>
        missing := missing + 1
        let rf := (refFact.map (·.font)).getD "?"
        let ef := (engineFact.map (·.font)).getD "?"
        IO.println s!"{face.label}\t{c.label}\t{srcTag}\t?\t?\t{rf}\t{ef}\t?\t?\tMISSING"
  IO.println s!"math-alphabet-diff: rows={rows} pass={passed} diff={diffs} missing={missing}"
  if diffs == 0 && missing == 0 then
    IO.println "math-alphabet-diff: PASS"
    return 0
  IO.eprintln "math-alphabet-diff: DIFF"
  return 1
