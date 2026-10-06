/-
The external corpus: a public test suite built by this engine and by
lualatex, measured, and every failure given a cause.

  lake env lean --run scripts/external.lean                   regenerate the `external` tier
  lake env lean --run scripts/external.lean --check           gate it (hermetic)
  lake env lean --run scripts/external.lean --selftest        the arithmetic and the tier's cases
  lake env lean --run scripts/external.lean --report <work> [<list>]
      build every document <list> names (default: the committed corpus,
      testdata/external/flashtex/documents.txt) with the engine — PDF, HTML,
      and PDF with the face pinned to Latin Modern — and with lualatex,
      into <work>, which must lie outside every leantex checkout; print the
      table, and write documents.tsv, census.tsv and worklist.tsv there.

*The report is not a gate.* It needs lualatex, the host's fonts and
poppler, so it can never be hermetic; its numbers are evidence, rerun when
wanted. *The tier is the part that needs neither*: each committed document
elaborated in-process through the same input splice the driver uses, which
reads only files beside the document — no face, no TeX tree. Its value per
document is how far elaboration alone gets:

  2  no error and no unknown construct (W0301/W0302)
  1  no error, at least one unknown construct
  0  an error diagnostic

*A list* is `<set><TAB><path>` lines, each path relative to the list's own
directory, `#` lines provenance. The committed corpus's list names only
documents lualatex builds under `-halt-on-error`, so every item is in the
denominator.

*Confinement.* The work directory is refused when it lies inside a leantex
checkout — every worktree and every clone — so builds, rasters and tables
never land in a tree, whatever list was read. Per-document build directories
are numbered, never named after the document.
-/
import LeanTex
import scripts.Board
import Lean.Data.Json

open LeanTex.Core LeanTex.Cli Scoreboard Lean

namespace External

def corpusDir : String := "testdata/external/flashtex"
def documentsPath : String := corpusDir ++ "/documents.txt"

/-- The unknown-construct codes: the engine met a name nothing answers. The
blocker ranking reads the same two. -/
def unknownCodes : List String := ["W0301", "W0302"]

/-- The codes whose loss is a face's: none found, one unusable, a glyph
missing, a variant or a math table absent. Keyed by constructor, so the
cause class is data and never a reading of a message. -/
def fontCodes : List DiagCode :=
  [.E0401, .E0402, .E0403, .E0404, .E0405, .W0003, .W0006, .W0009, .W0011, .N0018]

-- ## Lists

structure Doc where
  set : String
  path : String
deriving BEq, Inhabited

/-- A list's documents. A line that is not `<set><TAB><path>` is a fault,
not a skip: a skipped line is a document silently out of the denominator. -/
def parseList (text : String) : Except String (Array Doc) := Id.run do
  let mut out : Array Doc := #[]
  let mut n := 0
  for l in text.splitOn "\n" do
    n := n + 1
    if l.trimAscii.isEmpty || l.startsWith "#" then continue
    match l.splitOn "\t" with
    | [s, p] =>
      if s.isEmpty || p.isEmpty || p.startsWith "/" || (p.splitOn "..").length > 1 then
        return .error s!"line {n}: a set and a path inside the list's directory"
      out := out.push { set := s, path := p }
    | _ => return .error s!"line {n}: not `<set><TAB><path>`"
  return .ok out

-- ## Elaboration alone: the hermetic reading

/-- Elaborate a document as the driver's front end does before any face is
asked for: lex, parse, splice `\input` and local `.sty` files, resolve
`\data`, elaborate. Every read is a file beside the document. -/
def elaborate (file : String) : IO (Array Diag) := do
  let text ← IO.FS.readFile file
  let (toks, lexDs) := Lex.lex file text
  let (raws, parseDs) := Parse.parse file toks
  let (executed, inputDs, _) ← Input.expandInputs file raws
  let (raws, dataDs) ← Input.resolveData file executed.raws
  return (Elab.runExecuted file { executed with raws := raws }
    (lexDs ++ parseDs ++ inputDs ++ dataDs)).2

def standing (ds : Array Diag) : Int :=
  if ds.any (·.severity == .error) then 0
  else if ds.any (fun d => unknownCodes.contains d.code) then 1
  else 2

/-- The unknown constructs one elaboration names, by structured subject
(`ctrl:<name>`, `env:<name>`), deduplicated and sorted. -/
def unknownsIn (ds : Array Diag) : Array String := Id.run do
  let mut out : Array String := #[]
  for d in ds do
    if unknownCodes.contains d.code then
      if let some s := d.subject then
        unless s.any (fun c => Char.toNat c < 32) || out.contains s do out := out.push s
  return out.qsort (· < ·)

-- ## The tier

/-- The files this repository wrote beside the vendored ones. Every other
file below the corpus directory is upstream's, pinned in `SHA256SUMS`. -/
def ownFiles : List String := ["SHA256SUMS", "documents.txt", "PROVENANCE.txt"]

/-- Where the corpus directory `root` stops holding upstream's bytes, read in
both directions: a pinned file whose bytes are not its pin's, or that is
gone, and a file no pin names. The digest is `sha256Hex`, so the check is
hermetic: no tool answers for it. -/
def sumFaults (root : String) : IO (Array String) := do
  let sums := root ++ "/SHA256SUMS"
  let entries ← match parsePins sums (← readFileOr sums) with
    | .ok es => pure es
    | .error e => return #[e]
  let mut faults : Array String := #[]
  for e in entries do
    let p := root ++ "/" ++ e.path
    if e.path.startsWith "/" || (e.path.splitOn "..").length > 1 then
      faults := faults.push s!"{sums}: '{e.path}' leaves the corpus directory"
    else if !(← System.FilePath.pathExists p) then
      faults := faults.push s!"{p}: pinned in {sums}, and absent"
    else if sha256Hex (← IO.FS.readBinFile p) != e.pin then
      faults := faults.push s!"{p}: not the bytes its pin in {sums} names"
  for f in ← System.FilePath.walkDir root do
    unless ← f.isDir do
      let rel := (f.toString.drop (root.length + 1)).toString
      unless ownFiles.contains rel || entries.any (·.path == rel) do
        faults := faults.push s!"{f}: in the corpus directory, and pinned by no line of {sums}"
  return faults

def measureTier : IO (Array String × Array Row) := do
  let faults ← sumFaults corpusDir
  unless faults.isEmpty do
    throw (IO.userError s!"external: {faults.size} fault(s) in the vendored bytes:\n  \
{"\n  ".intercalate faults.toList}")
  let docs ← match parseList (← IO.FS.readFile documentsPath) with
    | .ok ds => pure ds
    | .error e => throw (IO.userError s!"{documentsPath}: {e}")
  let mut rows : Array Row := #[]
  let mut at2 := 0
  let mut at1 := 0
  for d in docs do
    let v := standing (← elaborate (corpusDir ++ "/" ++ d.path))
    if v == 2 then at2 := at2 + 1 else if v == 1 then at1 := at1 + 1
    rows := rows.push { item := d.path, value := v }
  return (#[s!"# corpus: {documentsPath}, {docs.size} documents, each built by lualatex \
under -halt-on-error when it was imported (testdata/external/flashtex/PROVENANCE.txt)",
    "# value: elaboration alone, through the driver's input splice — 2 no error and no \
unknown construct (W0301/W0302), 1 no error, 0 an error",
    s!"# counts: {at2} at 2, {at1} at 1, {docs.size - at2 - at1} at 0"], rows)

-- ## Measurements

/-- An 8-bit grey raster: `pdftoppm -gray`'s binary PGM. -/
structure Gray where
  w : Nat
  h : Nat
  px : ByteArray
deriving Inhabited

def isSpace (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

/-- `P5 <w> <h> <max>` and one whitespace byte, then `w*h` samples. Only
`max = 255` is read: that is what `pdftoppm -gray` writes. -/
def Gray.parse (b : ByteArray) : Option Gray := Id.run do
  if b.size < 3 || b[0]! != 80 || b[1]! != 53 then return none
  let mut i := 2
  let mut nums : Array Nat := #[]
  for _ in [0:b.size] do
    if nums.size == 3 || i ≥ b.size then break
    if b[i]! == 35 then
      while i < b.size && b[i]! != 10 do i := i + 1
    else if isSpace b[i]! then i := i + 1
    else if 48 ≤ b[i]! && b[i]! ≤ 57 then
      let mut n := 0
      while i < b.size && 48 ≤ b[i]! && b[i]! ≤ 57 do
        n := n * 10 + (b[i]! - 48).toNat
        i := i + 1
      nums := nums.push n
    else return none
  let #[w, h, mx] := nums | return none
  if mx != 255 || i ≥ b.size || !isSpace b[i]! then return none
  let start := i + 1
  if b.size < start + w * h then return none
  return some { w, h, px := b.extract start (start + w * h) }

/-- Root-mean-square grey difference in thousandths of full scale, both
rasters padded to the larger with white. -/
def rmsePermille (a b : Gray) : Nat := Id.run do
  let w := max a.w b.w
  let h := max a.h b.h
  if w * h == 0 then return 0
  let mut sum : UInt64 := 0
  for y in [0:h] do
    for x in [0:w] do
      let pa : UInt64 := if x < a.w && y < a.h then a.px[y * a.w + x]!.toUInt64 else 255
      let pb : UInt64 := if x < b.w && y < b.h then b.px[y * b.w + x]!.toUInt64 else 255
      let d := if pa ≥ pb then pa - pb else pb - pa
      sum := sum + d * d
  let r := Float.sqrt (sum.toFloat / (w * h).toFloat) / 255.0 * 1000.0
  return r.round.toUInt64.toNat

def ligatures : List (Char × String) :=
  [('ﬀ', "ff"), ('ﬁ', "fi"), ('ﬂ', "fl"), ('ﬃ', "ffi"), ('ﬄ', "ffl"), ('ﬅ', "st"),
   ('ﬆ', "st"), ('ℎ', "h")]

/-- A Mathematical Alphanumeric Symbol read as the letter or digit it
styles: the block runs A–Z a–z per style from U+1D400 (its holes are the
letters Letterlike Symbols already held) and 0–9 per style from U+1D7CE. -/
def mathPlain (c : Char) : Option Char :=
  let n := c.toNat
  if 0x1D400 ≤ n && n ≤ 0x1D6A3 then
    let k := (n - 0x1D400) % 52
    some (Char.ofNat (if k < 26 then 65 + k else 97 + k - 26))
  else if 0x1D7CE ≤ n && n ≤ 0x1D7FF then some (Char.ofNat (48 + (n - 0x1D7CE) % 10))
  else none

/-- A character a page is compared by: a letter or a digit, in any script.
Punctuation and symbols are not compared — lualatex's Type 1 faces carry no
`/ToUnicode`, so pdftotext reads their quotes, dashes and math by glyph name
or not at all, and a difference there is the reader's, not the page's. -/
def compared (c : Char) : Bool :=
  let n := c.toNat
  c.isAlphanum || (0xC0 ≤ n && n != 0xD7 && n != 0xF7 && !(0x2000 ≤ n && n ≤ 0x2BFF)
    && !(0xE000 ≤ n && n ≤ 0xF8FF) && n != 0xFFFD)

/-- pdftotext's output as the characters a page is compared by: a hyphen
closing a line goes with its break, ligatures and styled math letters spell
their plain letters, ASCII case is folded, and only letters and digits
count. Characters and not words, because the reference's Type 1 faces carry
no `/ToUnicode`: pdftotext drops a symbol it cannot map together with the
space beside it, and "a ⊞ b" reads as the one word "ab". -/
def letters (t : String) : Array Char := Id.run do
  let t := t.replace "-\n" ""
  let mut out : Array Char := #[]
  for c in t.toList do
    match ligatures.lookup c, mathPlain c with
    | some s, _ => for x in s.toList do out := out.push x
    | none, some p => out := out.push p.toLower
    | none, none => if compared c then out := out.push c.toLower
  return out

/-- Characters the two sides share, counted as multisets. -/
def common (a b : Array Char) : Nat := Id.run do
  let mut m : Std.HashMap Char Nat := {}
  for c in a do m := m.insert c (m.getD c 0 + 1)
  let mut n := 0
  for c in b do
    let k := m.getD c 0
    if k > 0 then
      m := m.insert c (k - 1)
      n := n + 1
  return n

/-- Thousandths of the longer side the two share; two empty sides agree. -/
def agreement (a b : Array Char) : Nat :=
  let top := max a.size b.size
  if top == 0 then 1000 else common a b * 1000 / top

/-- The diagnostics a porcelain run printed, as `(code, severity)` read off
the structured fields — never the message. -/
def porcelainDiags (out : String) : Array (String × String) := Id.run do
  let mut ds : Array (String × String) := #[]
  for l in out.splitOn "\n" do
    if l.trimAscii.isEmpty then continue
    if let .ok j := Json.parse l then
      if let .ok "diagnostic" := j.getObjValAs? String "event" then
        if let .ok c := j.getObjValAs? String "code" then
          ds := ds.push (c, (j.getObjValAs? String "severity").toOption.getD "")
  return ds

-- ## Causes

/-- Why a document falls short, one constructor per class the worklist
ranks. `outside` is not a failure of this engine: the reference did not
build, so the document leaves the denominator. -/
inductive Cause where
  | outside
  | crash (exit : UInt32)
  | refusal (code : String)
  | unknown (subject : String)
  | font (code : String)
  | html (exit : UInt32)
  | pages (engine reference : Nat)
  | text (permille : Nat)
  | raster (permille : Nat)
deriving BEq, Inhabited

/-- The worklist key: what one fix would answer, so two documents with the
same key are one item. -/
def Cause.key : Cause → String
  | .outside => "outside: lualatex does not build it"
  | .crash e => s!"crash: exit {e}"
  | .refusal c => s!"refusal: {c}"
  | .unknown s => s!"unknown: {s}"
  | .font c => s!"font: {c}"
  | .html e => s!"html: exit {e} where the PDF built"
  | .pages .. => "layout: page count"
  | .text _ => "layout: text"
  | .raster _ => "layout: raster"

def Cause.render : Cause → String
  | .pages e r => s!"pages {e}/{r}"
  | .text p => s!"text {p}‰"
  | .raster p => s!"raster {p}‰"
  | c => c.key

/-- The owner row a cause feeds, in the round's ownership table. An unknown
construct goes to the row of the package whose index names it
(`definer`, read off `indexOwners`); a layout cause of a picture set to the
picture row. -/
def Cause.owner (set : String) (definer : String → Option String) : Cause → String
  | .outside => "-"
  | .crash _ => "coordinator (a crash names no module; triage first)"
  | .refusal c =>
    if c.startsWith "E04" then "minimal-core (Font*)"
    else "warn-elab (refusal paths)"
  | .unknown s =>
    match definer s with
    | some "pkg:natbib" => "pkg-natbib"
    | some "pkg:amsmath" => "pkg-amsmath"
    | some "pkg:amssymb" | some "pkg:amsfonts" => "pkg-amssymb"
    | some "pkg:tikz" => "warn-pic"
    | some "primitive" => "warn-elab (a TeX primitive)"
    | some d => s!"coverage-honest ({d})"
    | none => "coverage-honest (unindexed: in no denominator)"
  | .font _ => "minimal-core (Font*, FontDb)"
  | .html _ => "rhythm-html / deck-reveal (HtmlDoc)"
  | .pages .. | .text _ | .raster _ =>
    if (set.splitOn "tikz").length > 1 then "warn-pic" else "rhythm-pdf2 (Layout)"

/-- Thresholds for a layout cause, each a declared value: below
`textFloor` thousandths of shared letters the text differs; above
`rasterCeiling` thousandths of mean RMSE the pages look different. -/
def textFloor : Nat := 950
def rasterCeiling : Nat := 150

structure Measure where
  doc : Doc
  ll : UInt32 := 0
  lt : UInt32 := 0
  html : UInt32 := 0
  ltlm : UInt32 := 0
  llPages : Nat := 0
  ltPages : Nat := 0
  lmPages : Nat := 0
  llChars : Nat := 0
  ltChars : Nat := 0
  text : Nat := 0
  lmText : Nat := 0
  rmse : Array Nat := #[]
  lmRmse : Array Nat := #[]
  census : Array (String × String) := #[]
  unknowns : Array String := #[]
  /-- The tier's reading of the same document: elaboration alone. -/
  alone : Int := 2
deriving Inhabited

def mean (xs : Array Nat) : Nat := if xs.isEmpty then 0 else xs.foldl (· + ·) 0 / xs.size

/-- Every cause one measurement shows, in the worklist's order. The
engine's own layout causes are read off the Latin Modern build where it
exists, so a face this engine defaults to differently from LaTeX is not
counted as every document's layout defect: that divergence is one
decision, reported once, not a thousand findings. -/
def causes (m : Measure) : Array Cause := Id.run do
  if m.ll != 0 then return #[.outside]
  let mut out : Array Cause := #[]
  if m.lt != 0 && m.lt != 1 then out := out.push (.crash m.lt)
  let mut seen : Array String := #[]
  for (c, sev) in m.census do
    if sev == "error" && !seen.contains c then
      seen := seen.push c
      out := out.push (match DiagCode.ofString? c with
        | some k => if fontCodes.contains k then .font c else .refusal c
        | none => .refusal c)
  for s in m.unknowns do out := out.push (.unknown s)
  for (c, sev) in m.census do
    if sev != "error" && !seen.contains c then
      if let some k := DiagCode.ofString? c then
        if fontCodes.contains k then
          seen := seen.push c
          out := out.push (.font c)
  if m.lt == 0 && m.html != 0 then out := out.push (.html m.html)
  if m.lt == 0 then
    let (pages, text, rmse) := if m.ltlm == 0 then (m.lmPages, m.lmText, m.lmRmse)
      else (m.ltPages, m.text, m.rmse)
    if pages != m.llPages then out := out.push (.pages pages m.llPages)
    if text < textFloor then out := out.push (.text text)
    if mean rmse > rasterCeiling then out := out.push (.raster (mean rmse))
  return out

-- ## Running the tools

structure Ran where
  exit : UInt32
  out : String

/-- One bounded tool run. A tool that could not start answers 127, as
`timeout` does for a command it cannot find. -/
def run (cmd : String) (args : Array String) (cwd : Option String := none)
    (secs : Nat := 180) : IO Ran := do
  try
    let o ← IO.Process.output
      { cmd := "timeout", args := #[toString secs, cmd] ++ args, cwd }
    return { exit := o.exitCode, out := o.stdout }
  catch _ => return { exit := 127, out := "" }

def pagesOf (pdf : String) : IO Nat := do
  let r ← run "pdfinfo" #[pdf]
  for l in r.out.splitOn "\n" do
    if l.startsWith "Pages:" then
      return ((l.drop 6).toString.trimAscii.toString.toNat?).getD 0
  return 0

def textOf (pdf out : String) : IO (Array Char) := do
  let r ← run "pdftotext" #["-enc", "UTF-8", pdf, out]
  if r.exit != 0 then return #[]
  return letters (← IO.FS.readFile out)

/-- Rasterize at 72 dpi, grey, into a directory of its own, and read the
pages back in page order. -/
def rastersOf (pdf dir : String) : IO (Array Gray) := do
  IO.FS.createDirAll dir
  let r ← run "pdftoppm" #["-r", "72", "-gray", pdf, dir ++ "/p"]
  if r.exit != 0 then return #[]
  let names := ((← System.FilePath.readDir dir).map (·.fileName)).filter (·.endsWith ".pgm")
  let num (n : String) : Nat := (((n.drop 2).toString.dropEnd 4).toString.toNat?).getD 0
  let mut out : Array Gray := #[]
  for n in names.qsort (fun a b => num a < num b) do
    if let some g := Gray.parse (← IO.FS.readBinFile (dir ++ "/" ++ n)) then out := out.push g
  return out

def rmses (a b : Array Gray) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:min a.size b.size] do out := out.push (rmsePermille a[i]! b[i]!)
  return out

/-- The document with its face pinned to Latin Modern, the family lualatex
sets a LaTeX class in: the declaration goes right after `\documentclass`. -/
def pinLatinModern (src : String) : String :=
  match src.splitOn "\\documentclass" with
  | pre :: rest@(first :: _) =>
    match first.splitOn "}" with
    | cls :: tail@(_ :: _) =>
      pre ++ "\\documentclass" ++ cls ++ "}\n\\fonts{ body = \"Latin Modern Roman\", \
math = \"Latin Modern Math\", mono = \"Latin Modern Mono\" }" ++ String.intercalate "}" tail
        ++ String.join (rest.drop 1 |>.map ("\\documentclass" ++ ·))
    | _ => src
  | _ => src

/-- Build and measure one document in `<work>/<n>`, a copy of its directory
there, so nothing is written beside the source. -/
def measureOne (bin root work : String) (n : Nat) (d : Doc) : IO Measure := do
  let dir := s!"{work}/{n}"
  let srcDir := (System.FilePath.mk (root ++ "/" ++ d.path)).parent.getD "."
  let base := (System.FilePath.mk d.path).fileName.getD "main.tex"
  let stem := (System.FilePath.mk base).fileStem.getD "main"
  IO.FS.createDirAll dir
  let _ ← run "rm" #["-r", dir ++ "/src"]
  let _ ← run "cp" #["-r", srcDir.toString, dir ++ "/src"]
  let file := s!"{dir}/src/{base}"
  let lt ← run bin #[file, "-o", s!"{dir}/lt.pdf", "--porcelain"]
  IO.FS.writeFile s!"{dir}/lt.porcelain" lt.out
  let html ← run bin #[file, "-o", s!"{dir}/lt.html", "--porcelain"]
  let lmFile := s!"{dir}/src/.lm-{base}"
  IO.FS.writeFile lmFile (pinLatinModern (← IO.FS.readFile file))
  let lm ← run bin #[lmFile, "-o", s!"{dir}/lm.pdf", "--porcelain"]
  IO.FS.createDirAll s!"{dir}/ll"
  let llArgs := #["-interaction=nonstopmode", "-halt-on-error", s!"-output-directory={dir}/ll",
    base]
  let first ← run "lualatex" llArgs (some s!"{dir}/src")
  let ll ← if first.exit == 0 then run "lualatex" llArgs (some s!"{dir}/src") else pure first
  let llPdf := s!"{dir}/ll/{stem}.pdf"
  let llw ← if ll.exit == 0 then textOf llPdf s!"{dir}/ll.txt" else pure #[]
  let ltw ← if lt.exit == 0 then textOf s!"{dir}/lt.pdf" s!"{dir}/lt.txt" else pure #[]
  let lmw ← if lm.exit == 0 then textOf s!"{dir}/lm.pdf" s!"{dir}/lm.txt" else pure #[]
  let llr ← if ll.exit == 0 then rastersOf llPdf s!"{dir}/r-ll" else pure #[]
  let ltr ← if lt.exit == 0 then rastersOf s!"{dir}/lt.pdf" s!"{dir}/r-lt" else pure #[]
  let lmr ← if lm.exit == 0 then rastersOf s!"{dir}/lm.pdf" s!"{dir}/r-lm" else pure #[]
  let llPages ← if ll.exit == 0 then pagesOf llPdf else pure 0
  let ltPages ← if lt.exit == 0 then pagesOf s!"{dir}/lt.pdf" else pure 0
  let lmPages ← if lm.exit == 0 then pagesOf s!"{dir}/lm.pdf" else pure 0
  let eds ← elaborate (root ++ "/" ++ d.path)
  return {
    doc := d, ll := ll.exit, lt := lt.exit, html := html.exit, ltlm := lm.exit
    llPages, ltPages, lmPages
    llChars := llw.size, ltChars := ltw.size
    text := agreement llw ltw, lmText := agreement llw lmw
    rmse := rmses ltr llr, lmRmse := rmses lmr llr
    census := porcelainDiags lt.out
    unknowns := unknownsIn eds, alone := standing eds }

-- ## Where output may land

/-- Does this `lakefile.toml` declare the package `leantex`? The rule
`scripts/blockers.lean` applies to its own outputs, restated because that
file is a program, not a library. -/
def namesLeantex (lakefile : String) : Bool :=
  (lakefile.splitOn "\n").any fun l =>
    let t := String.ofList (l.toList.filter (!·.isWhitespace))
    t == "name=\"leantex\"" || t == "name='leantex'"

/-- A work directory is refused when it, or any directory above it, is a
leantex checkout. It must exist, so it can be resolved. -/
def outsideCheckouts (dir : String) : IO (Except String String) := do
  let real ← try pure (some (← IO.FS.realPath dir).toString) catch _ => pure none
  let some real := real | return .error s!"{dir}: does not exist"
  let mut cur : System.FilePath := real
  for _ in [0:4096] do
    let lf := cur / "lakefile.toml"
    if ← lf.pathExists then
      let t ← try IO.FS.readFile lf catch _ => pure ""
      if namesLeantex t then
        return .error s!"{dir}: inside a leantex checkout; build outside every checkout"
    match cur.parent with
    | some p => if p == cur then break else cur := p
    | none => break
  return .ok real

-- ## The report

def tsvLine (xs : List String) : String := String.intercalate "\t" xs ++ "\n"

def pageList (xs : Array Nat) : String :=
  if xs.isEmpty then "-" else String.intercalate "," (xs.toList.map toString)

def documentsTsv (ms : Array Measure) : String := Id.run do
  let mut out := tsvLine ["set", "doc", "lualatex", "engine", "html", "engine+lm", "alone",
    "pages ll/engine/lm", "letters ll/engine", "text ‰ engine/lm", "rmse ‰ engine",
    "rmse ‰ lm", "causes"]
  for m in ms do
    out := out ++ tsvLine [m.doc.set, m.doc.path, toString m.ll, toString m.lt,
      toString m.html, toString m.ltlm, toString m.alone, s!"{m.llPages}/{m.ltPages}/{m.lmPages}",
      s!"{m.llChars}/{m.ltChars}", s!"{m.text}/{m.lmText}", pageList m.rmse,
      pageList m.lmRmse, String.intercalate "; " ((causes m).toList.map Cause.render)]
  return out

/-- The census over every document the reference builds: per code, its
declared loss, the documents it fired in and its records. -/
def censusTsv (ms : Array Measure) : String := Id.run do
  let mut docs : Std.HashMap (String × String) Nat := {}
  let mut recs : Std.HashMap (String × String) Nat := {}
  for m in ms do
    if m.ll != 0 then continue
    let mut here : Array (String × String) := #[]
    for k in m.census do
      recs := recs.insert k (recs.getD k 0 + 1)
      unless here.contains k do here := here.push k
    for k in here do docs := docs.insert k (docs.getD k 0 + 1)
  let rows := docs.toArray.qsort fun a b =>
    if a.2 != b.2 then a.2 > b.2 else a.1.1 ++ a.1.2 < b.1.1 ++ b.1.2
  let mut out := tsvLine ["code", "loss", "severity", "documents", "records"]
  for ((c, sev), n) in rows do
    let loss := ((DiagCode.ofString? c).map (·.loss.label)).getD "unregistered"
    out := out ++ tsvLine [c, loss, sev, toString n, toString (recs.getD (c, sev) 0)]
  return out

structure Item where
  key : String
  owner : String
  docs : Nat
  sole : Nat
deriving Inhabited

/-- Rank the causes: documents each holds back, then documents it alone
holds back (flashtex's `sole`). -/
def worklist (ms : Array Measure) (definer : String → Option String := fun _ => none) :
    Array Item := Id.run do
  let mut items : Array Item := #[]
  for m in ms do
    let distinct := (causes m).foldl
      (fun acc c => if acc.any (·.key == c.key) then acc else acc.push c) #[]
    let sole := if distinct.size == 1 then 1 else 0
    for c in distinct do
      match items.findIdx? (·.key == c.key) with
      | some i =>
        let it := items[i]!
        items := items.set! i { it with docs := it.docs + 1, sole := it.sole + sole }
      | none =>
        items := items.push { key := c.key, owner := c.owner m.doc.set definer, docs := 1,
                              sole }
  return items.qsort fun a b =>
    if a.docs != b.docs then a.docs > b.docs
    else if a.sole != b.sole then a.sole > b.sole else a.key < b.key

def worklistTsv (items : Array Item) : String :=
  items.foldl (fun acc it => acc ++ tsvLine [it.key, it.owner, toString it.docs,
    toString it.sole]) (tsvLine ["cause", "owner row", "documents", "sole"])

/-- Per set: documents, the reference's builds, and how many clear each rung
of the report's own reading. -/
def summary (ms : Array Measure) : String := Id.run do
  let mut sets : Array String := #[]
  for m in ms do unless sets.contains m.doc.set do sets := sets.push m.doc.set
  let mut out := tsvLine ["set", "docs", "ll builds", "engine pdf", "engine html",
    "pages agree (lm)", s!"text ≥ {textFloor}‰ (lm)", s!"rmse ≤ {rasterCeiling}‰ (lm)",
    "no cause"]
  for s in sets.qsort (· < ·) do
    let xs := ms.filter (·.doc.set == s)
    let inn := xs.filter (·.ll == 0)
    let pdf := inn.filter (·.lt == 0)
    let lmOk := inn.filter (·.ltlm == 0)
    out := out ++ tsvLine [s, toString xs.size, toString inn.size, toString pdf.size,
      toString (inn.filter (·.html == 0)).size,
      toString (lmOk.filter (fun m => m.lmPages == m.llPages)).size,
      toString (lmOk.filter (·.lmText ≥ textFloor)).size,
      toString (lmOk.filter (fun m => mean m.lmRmse ≤ rasterCeiling)).size,
      toString (inn.filter (fun m => (causes m).isEmpty)).size]
  return out

/-- The construct a compat-index row documents, read off its example: the
first control word that is not `\begin`/`\end`, else the first environment
it opens — so `\begin{tabular}{ll}\multirow{2}{*}{a}…` documents
`\multirow`, and `\begin{align*}x\end{align*}` documents `align*`. A
heuristic over the row's text, stated as one: the index has no field that
names the construct. -/
def rowConstruct (ex : String) : Option String :=
  let words := ((ex.splitOn "\\").drop 1).map fun w =>
    String.ofList (w.toList.takeWhile Char.isAlpha)
  match words.find? (fun w => !w.isEmpty && w != "begin" && w != "end") with
  | some w => some ("ctrl:" ++ w)
  | none => match ex.splitOn "\\begin{" with
    | _ :: env :: _ => some ("env:" ++ ((env.splitOn "}").headD ""))
    | _ => none

/-- Where the tree's own indexes place a construct: the kernel's documented
command list (`testdata/coverage/latex2e-index.txt`, with its manual chapter),
or the package whose compat index names it (`testdata/compat-index/<pkg>.txt`,
its example's first control word or `\begin{…}`). One source of truth for
what a construct is, read rather than restated; a construct neither names
is `unindexed`, which is a finding about the denominators as much as about
the engine — its absence costs coverage nothing. -/
def indexOwnersOf (kernel : String) (pkgs : Array (String × String)) :
    Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  for l in kernel.splitOn "\n" do
    if l.startsWith "#" then continue
    match l.splitOn "\t" with
    | name :: chapter :: _ => m := m.insert ("ctrl:" ++ name) s!"kernel ({chapter})"
    | _ => pure ()
  for p in Compat.texPrimitives do
    unless m.contains ("ctrl:" ++ p) do m := m.insert ("ctrl:" ++ p) "primitive"
  for (pkg, text) in pkgs do
    for l in text.splitOn "\n" do
      if l.startsWith "#" then continue
      if let some k := rowConstruct (String.intercalate " " ((l.splitOn " ").drop 2)) then
        unless m.contains k do m := m.insert k ("pkg:" ++ pkg)
  return m

def indexOwners : IO (Std.HashMap String String) := do
  let kernel ← try IO.FS.readFile "testdata/coverage/latex2e-index.txt" catch _ => pure ""
  let dir : System.FilePath := "testdata/compat-index"
  let mut names : Array String := #[]
  if ← dir.isDir then
    names := (← dir.readDir).map (·.fileName)
  let mut pkgs : Array (String × String) := #[]
  for f in names.qsort (· < ·) do
    if f.endsWith ".txt" then pkgs := pkgs.push ((f.dropEnd 4).toString, ← IO.FS.readFile (dir / f))
  return indexOwnersOf kernel pkgs

/-- The tier's premise, checked where both readings exist: elaboration alone
stands at 0 exactly when the shipped build refuses (exit 1). Documents the
reference builds only; a disagreement means the tier's 0 is not the
refusal the report measures, and the tier's docstring would be a claim. -/
def premiseMisses (ms : Array Measure) : Array String :=
  (ms.filter fun m => m.ll == 0 && (m.lt == 0 || m.lt == 1) && ((m.alone == 0) != (m.lt == 1))).map
    (·.doc.path)

def report (work : String) (listPath : Option String) : IO UInt32 := do
  let work ← match ← outsideCheckouts work with
    | .ok w => pure w
    | .error e => IO.eprintln s!"external: {e}"; return 3
  let listPath := listPath.getD documentsPath
  let root := ((System.FilePath.mk listPath).parent.getD ".").toString
  let docs ← match parseList (← IO.FS.readFile listPath) with
    | .ok ds => pure ds
    | .error e => IO.eprintln s!"external: {listPath}: {e}"; return 3
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex"] }
  if build.exitCode != 0 then
    IO.eprintln "external: `lake build leantex` failed; nothing to measure"
    return 3
  let bin := (← IO.FS.realPath ".lake/build/bin/leantex").toString
  let pool := 48
  IO.println s!"external: {docs.size} documents from {listPath}, {pool} at a time, into {work}"
  let mut ms : Array Measure := #[]
  let mut i := 0
  while i < docs.size do
    let stop := min docs.size (i + pool)
    let mut batch : Array (Task (Except IO.Error Measure)) := #[]
    for k in [i:stop] do
      batch := batch.push (← IO.asTask (measureOne bin root work k docs[k]!))
    for t in batch do
      match t.get with
      | .ok m => ms := ms.push m
      | .error e => IO.eprintln s!"external: a measurement raised: {e}"
    i := stop
  let owners ← indexOwners
  let items := worklist ms (owners.get? ·)
  IO.FS.writeFile s!"{work}/documents.tsv" (documentsTsv ms)
  IO.FS.writeFile s!"{work}/census.tsv" (censusTsv ms)
  IO.FS.writeFile s!"{work}/worklist.tsv" (worklistTsv items)
  IO.FS.writeFile s!"{work}/summary.tsv" (summary ms)
  IO.print (summary ms)
  IO.println ""
  IO.print (worklistTsv (items.extract 0 40))
  let misses := premiseMisses ms
  IO.println s!"external: elaboration alone and the shipped build disagree on {misses.size} \
of {(ms.filter (·.ll == 0)).size} documents the reference builds"
  for p in misses do IO.println s!"external:   {p}"
  IO.println s!"external: wrote documents.tsv, census.tsv, worklist.tsv, summary.tsv in {work}"
  return (if ms.size == docs.size then 0 else 1)

-- ## Selftest

def selftest : IO UInt32 := tierSelftest "external" fun expect => do
  -- Lists.
  expect "a list line is a set and a path" (parseList "# c\na\tb/c.tex\n" matches .ok #[_])
  expect "a line with no set is a fault" (parseList "b/c.tex\n" matches .error _)
  expect "an absolute path is a fault" (parseList "a\t/etc/x.tex\n" matches .error _)
  expect "a path leaving the list's directory is a fault"
    (parseList "a\t../x.tex\n" matches .error _)
  -- Standing, over structured diagnostics.
  let unk : Diag := { kind := .W0301, message := "", subject := some "ctrl:foo" }
  let err : Diag := { kind := .E0336, message := "" }
  let note : Diag := { kind := .N0100, message := "" }
  expect "no diagnostic stands at 2" (standing #[] == 2)
  expect "a note stands at 2" (standing #[note] == 2)
  expect "an unknown construct stands at 1" (standing #[note, unk] == 1)
  expect "an error stands at 0, whatever else fired" (standing #[unk, err] == 0)
  expect "unknowns are read off the subject, once each"
    (unknownsIn #[unk, unk, { kind := .W0302, message := "", subject := some "env:bar" }]
      == #["ctrl:foo", "env:bar"])
  expect "an unknown with no subject names nothing" (unknownsIn #[{ unk with subject := none }]
    == #[])
  -- Rasters.
  let pgm (w h : Nat) (v : UInt8) : ByteArray :=
    s!"P5\n{w} {h}\n255\n".toUTF8 ++ ByteArray.mk (Array.replicate (w * h) v)
  expect "a PGM reads back its size" ((Gray.parse (pgm 3 2 0)).map (fun g => (g.w, g.h))
    == some (3, 2))
  expect "a truncated PGM is refused" (Gray.parse ((pgm 3 2 0).extract 0 14) |>.isNone)
  expect "a PNG is refused" (Gray.parse "\x89PNG".toUTF8 |>.isNone)
  match Gray.parse (pgm 4 4 0), Gray.parse (pgm 4 4 255), Gray.parse (pgm 2 4 0) with
  | some black, some white, some half =>
    expect "identical pages differ by 0" (rmsePermille black black == 0)
    expect "black against white is full scale" (rmsePermille black white == 1000)
    expect "a narrower page is padded with white" (rmsePermille half white == 707)
    expect "padding is symmetric" (rmsePermille half black == rmsePermille black half)
  | _, _, _ => expect "the raster fixtures parse" false
  -- Letters.
  expect "a line-end hyphen goes with its break" (letters "hy-\nphen" == "hyphen".toList.toArray)
  expect "ligatures spell their letters" (letters "ﬁne ﬂow" == "fineflow".toList.toArray)
  expect "punctuation and space are not compared"
    (letters "don’t, ‘a’ — b." == "dontab".toList.toArray)
  expect "styled math letters read plain, case folded" (letters "𝑥 𝐀 𝟑 ℎ" == "xa3h".toList.toArray)
  expect "a letter of another script is compared" (letters "Æsop café" == "Æsopcafé".toList.toArray)
  expect "a symbol dropped with its spaces joins nothing" (letters "a ⊞ b" == letters "ab")
  expect "agreement counts multisets" (agreement #['a', 'a', 'b'] #['a', 'b', 'b'] == 666)
  expect "two empty sides agree" (agreement #[] #[] == 1000)
  expect "porcelain is read by field"
    (porcelainDiags "{\"event\":\"diagnostic\",\"severity\":\"error\",\"code\":\"E0336\",\
\"message\":\"code W0301\"}\n{\"event\":\"summary\"}\n" == #[("E0336", "error")])
  -- The face pin.
  expect "the face is pinned after the class"
    (pinLatinModern "\\documentclass[a]{article}\nx" == "\\documentclass[a]{article}\n\
\\fonts{ body = \"Latin Modern Roman\", math = \"Latin Modern Math\", mono = \"Latin Modern \
Mono\" }\nx")
  expect "a document with no class is left alone" (pinLatinModern "x" == "x")
  -- Causes.
  let clean : Measure := { doc := { set := "s", path := "p" }, llPages := 1, ltPages := 1
                           lmPages := 1, text := 1000, lmText := 1000 }
  expect "a clean measurement has no cause" (causes clean).isEmpty
  expect "a reference that fails puts the document outside"
    (causes { clean with ll := 1, census := #[("E0336", "error")] } == #[.outside])
  expect "an error is a refusal, keyed by its code"
    (causes { clean with lt := 1, census := #[("E0336", "error"), ("E0336", "error")] }
      == #[.refusal "E0336"])
  expect "a font code is a font cause, error or not"
    (causes { clean with census := #[("W0009", "warning")] } == #[.font "W0009"])
  expect "an exit other than 0 or 1 is a crash"
    ((causes { clean with lt := 4 }).contains (.crash 4))
  expect "layout reads the Latin Modern build"
    (causes { clean with ltPages := 2, rmse := #[900] } == #[])
  expect "and the shipped build when the pinned one failed"
    (causes { clean with ltlm := 1, ltPages := 2 } == #[.pages 2 1])
  expect "a failed HTML build beside a PDF is its own cause"
    (causes { clean with html := 1 } == #[.html 1])
  expect "the premise holds where elaboration and the build agree"
    (premiseMisses #[clean, { clean with lt := 1, alone := 0 }] == #[])
  expect "a refusal elaboration did not foresee is a miss, and so is the converse"
    (premiseMisses #[{ clean with lt := 1 }, { clean with alone := 0 }] == #["p", "p"])
  expect "a crash and a reference failure are outside the premise"
    (premiseMisses #[{ clean with lt := 4, alone := 0 }, { clean with ll := 1, lt := 1 }] == #[])
  let ms : Array Measure := #[{ clean with unknowns := #["ctrl:a"] },
    { clean with unknowns := #["ctrl:a", "env:b"] }, clean]
  let w := worklist ms
  expect "the worklist ranks by documents, then sole"
    (w.map (fun i => (i.key, i.docs, i.sole)) ==
      #[("unknown: ctrl:a", 2, 1), ("unknown: env:b", 1, 0)])
  -- Attribution, off the indexes' own row shapes.
  let owners := indexOwnersOf "# head\nbibitem\tEnvironments\tcall\n"
    #[("multirow", "body refuse:W0301 \\begin{tabular}{ll}\\multirow{2}{*}{a} & b\\end{tabular}\n"),
      ("natbib", "# src\nbody impl \\citep{k}\nbody refuse:W0301 \\citeauthor{k}\n"),
      ("amsmath", "body impl \\begin{align*}x\\end{align*}\n"),
      ("zz", "body impl \\citep{k}\n")]
  expect "a kernel row names its chapter"
    (owners.get? "ctrl:bibitem" == some "kernel (Environments)")
  expect "a TeX primitive the kernel index does not name is one"
    (owners.get? "ctrl:fontname" == some "primitive")
  expect "a row documents its first command, not the environment it stands in"
    (owners.get? "ctrl:multirow" == some "pkg:multirow" && owners.get? "env:tabular" == none)
  expect "a package row names its package, refused or not"
    (owners.get? "ctrl:citep" == some "pkg:natbib"
      && owners.get? "ctrl:citeauthor" == some "pkg:natbib")
  expect "a row with no command documents its environment"
    (owners.get? "env:align*" == some "pkg:amsmath")
  expect "the first index to name a construct keeps it" (owners.get? "ctrl:citep" != some "pkg:zz")
  expect "a construct no index names is unindexed" (owners.get? "env:description" == none)
  expect "an unindexed unknown feeds the programme, saying so"
    ((Cause.unknown "env:x").owner "s" (owners.get? ·)
      == "coverage-honest (unindexed: in no denominator)")
  expect "a natbib unknown feeds its package row"
    ((Cause.unknown "ctrl:citeauthor").owner "s" (owners.get? ·) == "pkg-natbib")
  -- Where output may land.
  expect "a lakefile naming leantex is a checkout"
    (namesLeantex "name = \"leantex\"\n" && !namesLeantex "name = \"other\"")
  expect "a work directory inside this checkout is refused"
    ((← outsideCheckouts "testdata") matches .error _)
  expect "one under /tmp is not" ((← outsideCheckouts "/tmp") matches .ok _)
  -- The vendored bytes, each fault once, through a real directory.
  IO.FS.withTempDir fun dir => do
    let root := dir.toString
    let put (rel body : String) : IO Unit := IO.FS.writeFile (root ++ "/" ++ rel) body
    IO.FS.createDirAll (root ++ "/sub")
    for f in ownFiles do put f ""
    put "a.tex" "alpha\n"
    put "sub/b.tex" "beta\n"
    let sums := pinnedEntry (sha256Hex "alpha\n".toUTF8) "a.tex" ++ "\n" ++
      pinnedEntry (sha256Hex "beta\n".toUTF8) "sub/b.tex" ++ "\n"
    put "SHA256SUMS" sums
    expect "the pinned bytes verify" (← sumFaults root).isEmpty
    put "sub/b.tex" "betb\n"
    expect "one changed byte is a fault" ((← sumFaults root).size == 1)
    put "sub/b.tex" "beta\n"
    put "sub/c.tex" "gamma\n"
    expect "a file no pin names is a fault" ((← sumFaults root).size == 1)
    IO.FS.removeFile (root ++ "/sub/c.tex")
    IO.FS.removeFile (root ++ "/a.tex")
    expect "a pinned file gone is a fault" ((← sumFaults root).size == 1)
    put "a.tex" "alpha\n"
    put "SHA256SUMS" (sums ++ pinnedEntry (sha256Hex "x".toUTF8) "../x.tex" ++ "\n")
    expect "a pin leaving the directory is a fault" ((← sumFaults root).size == 1)
    put "SHA256SUMS" (sums ++ "a.tex\n")
    expect "a line that is no pin is a fault" ((← sumFaults root).size == 1)

end External

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--report", work] => External.report work none
  | ["--report", work, list] => External.report work (some list)
  | _ => tierMain "external" .raw External.measureTier External.selftest args
