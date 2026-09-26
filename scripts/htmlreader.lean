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

This tier never launches a browser: it reads the committed matrix. What it
does do is rebuild the corpus to HTML in-process (`hermeticHtmlKey`: the
corpus and its shipped faces only — no TeX tree, no `PATH`, no font
variable) and compare a content key against the `src-key:` line the matrix
carries — the
freshness question the matrix cannot answer for itself. Without it the
engine can change what a page does and this tier keeps reporting the
browser's verdict on pages nobody emits any more. A differing key is a
fault, not a regression: the counts are not wrong, they are about something
else. Only target readers are counted; a non-target column (Firefox, which
the cached build cannot start on this host) is recorded data and gates
nothing.

Note what this tier does *not* claim. `scripts/html-oracle.lean --check`
demands `pass` in every target cell and fails on the committed matrix: 7
cells are `fail:` today, each with its reason beneath it, and no gate runs
that check. This tier's numbers are "how much passes", which is the
question a ratchet can carry; "is anything failing" stays html-oracle's,
and it is currently answered no.
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

/-- The `src-key:` line, or none where the matrix carries no key. -/
def matrixKey (text : String) : Option String :=
  ((text.splitOn "\n").find? (·.trimAscii.toString.startsWith "src-key:")).map fun l =>
    ((l.trimAscii.toString.drop "src-key:".length).toString).trimAscii.toString

def measureTier : IO (Array String × Array Row) := do
  if !(← System.FilePath.pathExists matrixPath) then
    IO.eprintln s!"scoreboard: {matrixPath} is missing; regenerate it with \
lake env lean --run scripts/html-oracle.lean"
    return (#[], #[])
  let text ← IO.FS.readFile matrixPath
  let (target, cells) := readMatrix text
  let mut rows : Array Row := #[]
  let mut untested := 0
  for c in cells do
    if target.contains c.reader then
      rows := rows.push { item := s!"{c.section_}.{c.reader}.pass", value := Int.ofNat c.pass }
      rows := rows.push { item := s!"{c.section_}.{c.reader}.rows", value := Int.ofNat c.rows }
    else
      untested := untested + c.rows
  -- Freshness. An empty row set is how this tier says "do not compare": the
  -- porcelain fault comes from tierMain's own malformed-measurement path.
  let fresh ← hermeticHtmlKey
  match matrixKey text, fresh with
  | none, _ =>
    IO.eprintln s!"scoreboard: {matrixPath} carries no `src-key:` line, so nothing \
ties its counts to the HTML this tree emits; regenerate it with \
lake env lean --run scripts/html-oracle.lean"
    return (#[], #[])
  | some k, .ok now =>
    if k != now then
      IO.eprintln s!"scoreboard: {matrixPath} was measured on different HTML \
(src-key {k}, this tree builds {now}), so its counts are about pages this tree \
no longer emits; rerun the browser: lake env lean --run scripts/html-oracle.lean"
      return (#[], #[])
  | some _, .error e =>
    IO.eprintln s!"scoreboard: cannot rebuild the corpus to compare against \
{matrixPath}'s src-key: {e}"
    return (#[], #[])
  return (#[s!"# source: {matrixPath}; target readers: {String.intercalate " " target.toList}; \
{untested} cells in non-target columns are data and gate nothing",
    s!"# src-key: {(matrixKey text).getD "absent"} — the HTML the browser saw, \
rebuilt and compared on every --check"], rows)

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
  -- The freshness key: read off the matrix, absent when there is none.
  no "src-key: read off the line" (matrixKey "target: chromium\nsrc-key: abc123\n" == some "abc123")
  no "src-key: absent when the matrix carries none" ((matrixKey text).isNone)
  -- The key itself: order and name are part of it, so a renamed or
  -- reordered page changes the answer.
  let a : Array (String × ByteArray) := #[("x", "1".toUTF8), ("y", "2".toUTF8)]
  no "key: stable over the same blobs" (contentKey a == contentKey a)
  no "key: a changed byte changes it"
    (contentKey a != contentKey #[("x", "1".toUTF8), ("y", "3".toUTF8)])
  no "key: a renamed page changes it"
    (contentKey a != contentKey #[("x", "1".toUTF8), ("z", "2".toUTF8)])
  no "key: reordering changes it"
    (contentKey a != contentKey #[("y", "2".toUTF8), ("x", "1".toUTF8)])
  no "key: 16 hex digits" ((contentKey a).length == 16)
  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "htmlreader selftest: all passed"
    return 0
  for f in failed do IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 :=
  tierMain "htmlreader" (.pairs "pass" "rows") measureTier selftest args
