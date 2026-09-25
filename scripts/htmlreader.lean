/-
What a real browser held, committed as a number. Run from the repository
root:

  lake env lean --run scripts/htmlreader.lean              regenerate the baseline
  lake env lean --run scripts/htmlreader.lean --check      gate against the committed one
  lake env lean --run scripts/htmlreader.lean --selftest   the cell reader

`scripts/html-oracle.lean` drives the browser and is
`tests/oracles/html-reader-matrix.txt`'s only writer; it demands `pass` in
every target column, so it answers "is anything failing". This tier answers
"how much passes, and is it more than last time" — which is the question a
ratchet can carry, and which survives a matrix that legitimately holds a
`fail:` cell with its reason beneath.

This tier never launches a browser: it reads the committed matrix, so
`--check` is hermetic. Only target readers are counted; a non-target column
(Firefox, which the cached build cannot start on this host) is recorded data
and gates nothing.
-/
import scripts.Board

open Scoreboard

def matrixPath : String := "tests/oracles/html-reader-matrix.txt"

structure Cells where
  section_ : String
  reader : String
  pass : Nat
  rows : Nat
deriving Inhabited

/-- Read the matrix: `target:` names the gated readers, a `[name]` line opens
a section, the first `#` line inside one names its columns, and every other
non-`#` line is a row whose cells follow its key. -/
def readMatrix (text : String) : Array String × Array Cells := Id.run do
  let mut target : Array String := #[]
  let mut out : Array Cells := #[]
  let mut sec := ""
  let mut columns : Array String := #[]
  let mut counts : Array Cells := #[]
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "target:" then
      target := (((l.drop "target:".length).toString).splitOn " ").filter (!·.isEmpty) |>.toArray
    else if l.startsWith "[" && l.endsWith "]" then
      out := out ++ counts
      counts := #[]
      sec := ((l.drop 1).toString.dropEnd 1).toString
      columns := #[]
    else if l.startsWith "#" then
      if !sec.isEmpty && columns.isEmpty then
        let toks := (((l.drop 1).toString).splitOn " ").filter (!·.isEmpty)
        columns := (toks.drop 1).toArray
        for c in columns do
          counts := counts.push { section_ := sec, reader := c, pass := 0, rows := 0 }
    else if !sec.isEmpty && !columns.isEmpty then
      let toks := ((l.splitOn " ").filter (!·.isEmpty)).toArray
      for i in [0:columns.size] do
        if let some cell := toks[i+1]? then
          if let some k := counts.findIdx? (fun c =>
              c.section_ == sec && c.reader == columns[i]!) then
            let c := counts[k]!
            counts := counts.set! k
              { c with pass := c.pass + (if cell == "pass" then 1 else 0)
                       rows := c.rows + 1 }
  out := out ++ counts
  return (target, out)

def measureTier : IO (Array String × Array Row) := do
  if !(← System.FilePath.pathExists matrixPath) then
    IO.eprintln s!"scoreboard: {matrixPath} is missing; regenerate it with \
lake env lean --run scripts/html-oracle.lean"
    return (#[], #[])
  let (target, cells) := readMatrix (← IO.FS.readFile matrixPath)
  let mut rows : Array Row := #[]
  let mut untested := 0
  for c in cells do
    if target.contains c.reader then
      rows := rows.push { item := s!"{c.section_}.{c.reader}.pass", value := Int.ofNat c.pass }
      rows := rows.push { item := s!"{c.section_}.{c.reader}.rows", value := Int.ofNat c.rows }
    else
      untested := untested + c.rows
  return (#[s!"# source: {matrixPath}; target readers: {String.intercalate " " target.toList}; \
{untested} cells in non-target columns are data and gate nothing"], rows)

def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let no (why : String) (ok : Bool) : IO Unit := do
    unless ok do fails.modify (why :: ·)
  let text := "target: chromium\n\
tools: invented\n\
\n\
[feature]\n\
# feature   chromium   firefox\n\
load        pass       untested\n\
images      fail:zz    untested\n\
#   chromium zz: the reason line, which is not a row\n\
fonts       pass       untested\n\
\n\
[fixture]\n\
# fixture   chromium   firefox\n\
alpha       pass       untested\n"
  let (target, cells) := readMatrix text
  no "target: chromium is the gated reader" (target == #["chromium"])
  let feat := cells.find? (fun c => c.section_ == "feature" && c.reader == "chromium")
  match feat with
  | none => no "feature/chromium has no cell count" false
  | some c =>
    no s!"feature rows: 3 expected, got {c.rows}" (c.rows == 3)
    no s!"feature passes: 2 expected, got {c.pass}" (c.pass == 2)
  let fix := cells.find? (fun c => c.section_ == "fixture" && c.reader == "chromium")
  no "fixture/chromium counted" ((fix.map (·.rows)).getD 0 == 1)
  no "both sections read" (cells.size == 4)
  let ff := cells.find? (fun c => c.reader == "firefox" && c.section_ == "feature")
  no "a non-target column is still read, so it can be reported as data"
    ((ff.map (·.rows)).getD 0 == 3)
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "htmlreader selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "htmlreader" (.pairs "pass" "rows") measureTier selftest args
