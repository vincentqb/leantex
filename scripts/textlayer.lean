/-
The textlayer tier: how many corpus artifacts' text this engine's readers read as the host's
tools do, from the committed text-layer matrix, its freshness key held to the readers' sources.
Usage: lake env lean --run scripts/textlayer.lean [--check | --selftest]
-/
import scripts.Board

open Scoreboard

def matrixPath : String := "testdata/oracles/text-layer-matrix.txt"

/-- The source files the readers' verdicts depend on, as `scripts/text-oracle.lean` keys them. -/
def readerSources : List String :=
  ["LeanTex/Core/HtmlRead.lean", "LeanTex/Core/HtmlEntity.lean", "LeanTex/Core/PdfTextRead.lean",
   "LeanTex/Core/PdfFont.lean", "LeanTex/Core/PdfContentLex.lean"]

/-- One section's counts for one tool: the rows with a verdict, and the passing ones. -/
structure Cells where
  section_ : String
  tool : String
  pass : Nat
  rows : Nat
deriving Inhabited, BEq

/-- Read the matrix: a `[name]` line opens a section, its first `#` line names the tool column,
and every other line is a fixture's row; `unbuilt` and `untested` cells are no verdict. -/
def readMatrix (text : String) : Array Cells := Id.run do
  let mut out : Array Cells := #[]
  let mut sec := ""
  let mut tool := ""
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "[" && l.endsWith "]" then
      sec := ((l.drop 1).toString.dropEnd 1).toString
      tool := ""
    else if l.startsWith "#" then
      if !sec.isEmpty && tool.isEmpty then
        tool := (((l.drop 1).toString.splitOn " ").filter (!·.isEmpty)).getLastD ""
        out := out.push { section_ := sec, tool, pass := 0, rows := 0 }
    else if !sec.isEmpty && !tool.isEmpty then
      let toks := (l.splitOn " ").filter (!·.isEmpty)
      if let some cell := toks[1]? then
        if cell != "unbuilt" && cell != "untested" then
          if let some k := out.findIdx? (fun c => c.section_ == sec && c.tool == tool) then
            if let some c := out[k]? then
              out := out.set! k { c with pass := c.pass + (if cell == "pass" then 1 else 0),
                                         rows := c.rows + 1 }
  return out

/-- A unique top-level `<name>:` value, or none when absent or repeated. -/
def matrixValue (text name : String) : Option String :=
  let values := (text.splitOn "\n").filterMap fun raw =>
    let line := raw.trimAscii.toString
    if line.startsWith (name ++ ":") then
      some ((line.drop (name.length + 1)).toString.trimAscii.toString)
    else none
  match values with
  | [value] => some value
  | _ => none

/-- The readers' freshness key over this tree's sources. -/
def readerKey : IO String := do
  let mut blobs : Array (String × ByteArray) := #[]
  for p in readerSources do
    blobs := blobs.push (p, ← IO.FS.readBinFile p)
  return contentKey blobs

def measureTier : IO (Array String × Array Row) := do
  if !(← System.FilePath.pathExists matrixPath) then
    IO.eprintln s!"scoreboard: {matrixPath} is missing; regenerate it with \
lake env lean --run scripts/text-oracle.lean"
    return (#[], #[])
  let text ← IO.FS.readFile matrixPath
  let some recorded := matrixValue text "reader-key"
    | IO.eprintln s!"scoreboard: {matrixPath} carries no unique `reader-key:` line, so nothing \
ties its verdicts to this tree's readers; regenerate it with lake env lean --run scripts/text-oracle.lean"
      return (#[], #[])
  let key ← readerKey
  if recorded != key then
    IO.eprintln s!"scoreboard: {matrixPath} judged other readers (reader-key {recorded}, this \
tree's are {key}); rerun the tools: lake env lean --run scripts/text-oracle.lean"
    return (#[], #[])
  let mut rows : Array Row := #[]
  for c in readMatrix text do
    rows := rows.push { item := s!"{c.section_}.{c.tool}.pass", value := Int.ofNat c.pass }
    rows := rows.push { item := s!"{c.section_}.{c.tool}.rows", value := Int.ofNat c.rows }
  return (#[s!"# source: {matrixPath}; {(matrixValue text "tools").getD "tools unrecorded"}",
    s!"# reader-key: {recorded} — the readers the tools judged, rebuilt and compared on every --check"],
    rows)

def selftest : IO UInt32 := tierSelftest "textlayer" fun no => do
  let text := "target: pdftotext chromium\nreader-key: abc\n\n[pdf]\n# fixture  pdftotext\n\
alpha  pass\nbeta   fail:text\ngamma  unbuilt\n\n[html]\n# fixture  chromium\nalpha  pass\n\
beta   untested\n"
  let cells := readMatrix text
  no "two sections read" (cells.size == 2)
  no "pdf: two verdicts, one pass" (cells[0]? == some ⟨"pdf", "pdftotext", 1, 2⟩)
  no "html: one verdict, one pass" (cells[1]? == some ⟨"html", "chromium", 1, 1⟩)
  no "reader-key: read off its line" (matrixValue text "reader-key" == some "abc")
  no "reader-key: absent when the matrix carries none" ((matrixValue "[pdf]\n" "reader-key").isNone)
  no "reader-key: a repeated line is no key"
    ((matrixValue "reader-key: a\nreader-key: b\n" "reader-key").isNone)
  let k ← readerKey
  no "reader-key: 16 hex digits over this tree's readers" (k.length == 16)

def main (args : List String) : IO UInt32 :=
  tierMain "textlayer" (.pairs "pass" "rows") measureTier selftest args
