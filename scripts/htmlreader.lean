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

This tier never launches a browser or a converter: it reads the committed
matrix. It rebuilds the corpus in-process and compares `src-key:` with the
HTML this tree emits. It separately compares `browser-face-src-key:` with a
hermetic key over the vector inputs, generated hrefs, and the shared converter
recipe. Every `browser-face:` row pins a rendering use and the SHA-256 of
its data URL to the independently decoded payload's SHA-256 and size;
`browser-face-key:` covers those rows. Missing, malformed, duplicated,
stale, or failed captures are faults, so
pass cells cannot outlive the pages or browser faces they measured.

Converter output is inherently a host report: this check does not execute
`xmllint`, `rsvg-convert`, or `pdftocairo`. A binary version change with the
same inputs requires rerunning `scripts/html-oracle.lean`; the matrix records
those versions and the run date. A differing hermetic key is a fault, not a
regression: the counts are not wrong, they describe something else. Only
target readers are counted; a non-target column is data and gates nothing.

`scripts/html-oracle.lean --check` demands both `pass` in every target cell
and valid successful browser-face captures. This tier carries the separate
ratchet question, "how much passes, and is it more than last time."
-/
import scripts.Board
import Lean.Data.Json

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

/-- A unique top-level `<name>:` value, or none when absent/duplicated. -/
def matrixValue (text name : String) : Option String :=
  let values := (text.splitOn "\n").filterMap fun raw =>
    let line := raw.trimAscii.toString
    if line.startsWith (name ++ ":") then
      some ((line.drop (name.length + 1)).toString.trimAscii.toString)
    else none
  match values with
  | [value] => some value
  | _ => none

/-- The `src-key:` line, or none where the matrix carries no unique key. -/
def matrixKey (text : String) : Option String := matrixValue text "src-key"

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
  let fresh ← hermeticHtmlKeys
  let keys ← match fresh with
    | .ok keys => pure keys
    | .error e =>
      IO.eprintln s!"scoreboard: cannot rebuild the corpus to compare against \
{matrixPath}'s freshness keys: {e}"
      return (#[], #[])
  let some recordedHtml := matrixKey text
    | IO.eprintln s!"scoreboard: {matrixPath} carries no unique `src-key:` line, so nothing \
ties its counts to the HTML this tree emits; regenerate it with \
lake env lean --run scripts/html-oracle.lean"
      return (#[], #[])
  if recordedHtml != keys.html then
    IO.eprintln s!"scoreboard: {matrixPath} was measured on different HTML \
(src-key {recordedHtml}, this tree builds {keys.html}), so its counts are about pages this tree \
no longer emits; rerun the browser: lake env lean --run scripts/html-oracle.lean"
    return (#[], #[])
  let faceFaults := browserFaceFaults text keys.browserFaceSource keys.expectedFaces
  unless faceFaults.isEmpty do
    IO.eprintln s!"scoreboard: {matrixPath} does not describe this tree's browser faces:"
    for fault in faceFaults do IO.eprintln s!"  {fault}"
    IO.eprintln "scoreboard: rerun the browser: lake env lean --run scripts/html-oracle.lean"
    return (#[], #[])
  return (#[s!"# source: {matrixPath}; target readers: {String.intercalate " " target.toList}; \
{untested} cells in non-target columns are data and gate nothing",
    s!"# src-key: {recordedHtml} — the HTML the browser saw, rebuilt and compared on every --check",
    s!"# browser-face-src-key: {(matrixValue text "browser-face-src-key").getD "absent"} — \
hermetic vector inputs, hrefs and conversion recipe",
    s!"# browser-face-key: {(matrixValue text "browser-face-key").getD "absent"} — \
exact converted hrefs and byte digests the browser run received"], rows)

def selftest : IO UInt32 := tierSelftest "htmlreader" fun no => do
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
  -- The browser-face capture is the exact href and converted content the
  -- browser run received. A converter regression cannot retain its key.
  let svgHref (bytes : ByteArray) :=
    ({ media := .svg, bytes } : LeanTex.Core.HtmlResource.Embedded).uri
  let imageHref (k : Nat) (bytes : ByteArray) :=
    browserFaceHref "figures" "i" k (svgHref bytes)
  let face := BrowserFace.captured "figures" (imageHref 0 "<svg/>".toUTF8) "<svg/>".toUTF8
  let expected := #[("figures", "figures/i0.svg")]
  let changedBytes := BrowserFace.captured "figures" face.href
    "<svg><path/></svg>".toUTF8
  let changedHref := BrowserFace.captured "figures" (imageHref 1 "<svg/>".toUTF8) "<svg/>".toUTF8
  let failed := BrowserFace.failed "figures" "pdftocairo"
  no "browser face: converted bytes move the key"
    (browserFaceKey #[face] != browserFaceKey #[changedBytes])
  no "browser face: the rendered href moves the key"
    (browserFaceKey #[face] != browserFaceKey #[changedHref])
  no "browser face: a tool failure moves the key"
    (browserFaceKey #[face] != browserFaceKey #[failed])
  no "browser face: the committed record round-trips"
    (BrowserFace.parse face.render == some face)
  no "browser face: a failed capture cannot certify pass cells"
    (!(browserFaceFaults
      ("browser-face-src-key: source\nbrowser-face-key: " ++ browserFaceKey #[failed] ++
        "\n" ++ failed.render ++ "\n") "source").isEmpty)
  let faceText := "browser-face-src-key: source\nbrowser-face-key: " ++
    browserFaceKey #[face] ++ "\n" ++ face.render ++ "\n"
  no "browser face: matching source and exact capture certify the cells"
    (browserFaceFaults faceText "source" expected).isEmpty
  no "browser face: moved hermetic inputs stale the capture"
    (!(browserFaceFaults faceText "different-source" expected).isEmpty)
  let staleHref := "browser-face-src-key: source\nbrowser-face-key: " ++
    browserFaceKey #[face] ++ "\n" ++ changedHref.render ++ "\n"
  no "browser face: changed captures cannot retain the committed key"
    (!(browserFaceFaults staleHref "source" expected).isEmpty)
  let duplicateFace := faceText ++ face.render ++ "\n"
  no "browser face: duplicate hrefs are a fault"
    (!(browserFaceFaults duplicateFace "source" expected).isEmpty)
  let malformedFace := "browser-face-src-key: source\nbrowser-face-key: deadbeef\n\
browser-face: figures missing-fields\n"
  no "browser face: a malformed record is a fault"
    (!(browserFaceFaults malformedFace "source").isEmpty)
  no "browser face: absent records and keys are faults"
    (!(browserFaceFaults "src-key: html\n" "source").isEmpty)
  let records (faces : Array BrowserFace) :=
    "browser-face-src-key: source\nbrowser-face-key: " ++ browserFaceKey faces ++ "\n" ++
      String.intercalate "\n" (faces.toList.map BrowserFace.render) ++ "\n"
  for href in ["figures.assets/unclassified.svg", "figures.assets/i0-plot.png",
      "elsewhere/i0-box.svg", "figures.assets/012345.svg"] do
    let stray := BrowserFace.captured "figures" href "<svg/>".toUTF8
    no s!"browser face: unclassified identity {href} is refused"
      (!(browserFaceFaults (records #[stray]) "source").isEmpty)
  let empty := BrowserFace.captured "figures" face.href ByteArray.empty
  no "browser face: an empty capture cannot certify pass cells"
    (!(browserFaceFaults (records #[empty]) "source" expected).isEmpty)
  no "browser face: a missing expected poster is refused even with a recomputed key"
    (!(browserFaceFaults faceText "source"
      #[("figures", "figures/i0.svg"), ("figures", "figures/p0.svg")]).isEmpty)
  no "browser face: an extra face is refused even with a recomputed key"
    (!(browserFaceFaults (records #[face, changedHref]) "source"
      #[("figures", "figures/i0.svg")]).isEmpty)
  let replaced := BrowserFace.captured "figures"
    (imageHref 0 "<svg><path/></svg>".toUTF8) "<svg><path/></svg>".toUTF8
  no "browser identity: content-key changes retain the expected identity"
    (browserImageIdentity "figures" face.href == browserImageIdentity "figures" replaced.href)
  no "browser identity: the exact capture key still sees a content-key change"
    (browserFaceKey #[face] != browserFaceKey #[replaced])
  no "browser identity: two content keys for one role/index are duplicates"
    (!(browserFaceFaults (records #[face, replaced]) "source" expected).isEmpty)
  no "browser identity: an index change remains visible"
    (browserImageIdentity "figures" face.href != browserImageIdentity "figures" changedHref.href)
  let posterHref := browserFaceHref "figures" "p" 0 (svgHref "<svg/>".toUTF8)
  no "browser identity: primary and poster remain distinct"
    (browserImageIdentity "figures" posterHref == some "figures/p0.svg" &&
      browserImageIdentity "figures" face.href != browserImageIdentity "figures" posterHref)
  let poster := BrowserFace.captured "figures" posterHref "<svg/>".toUTF8
  no "browser face: the complete expected primary/poster set passes"
    (browserFaceFaults (records #[face, poster]) "source"
      (expected.push ("figures", "figures/p0.svg"))).isEmpty
  let boundaryHref := browserFaceHref "figures" "i" 0 (svgHref "<svg><path/></svg>".toUTF8)
  let boundary := BrowserFace.captured "figures" boundaryHref "<svg><path/></svg>".toUTF8
  no "browser face: a boundary image also owes its typed-tree expectation"
    (!(browserFaceFaults (records #[boundary]) "source").isEmpty &&
      (browserFaceFaults (records #[boundary]) "source" expected).isEmpty)
  no "browser face: a raster-only page needs no converted capture"
    (browserFaceFaults (records #[]) "source").isEmpty
  let img (href : String) : LeanTex.Core.Html.Node := .elem "img" #[⟨"src", href⟩] #[]
  let source (href : String) : LeanTex.Core.Html.Node := .elem "source" #[⟨"srcset", href⟩] #[]
  let refs : Array LeanTex.Core.Html.Node := #[
    img "data:image/png;base64,iVBORw0KGgo=",
    .elem "picture" #[] #[source (svgHref "<svg/>".toUTF8), img (svgHref "<svg/>".toUTF8)],
    .elem "div" #[⟨"hidden", ""⟩] #[img (LeanTex.Core.Ir.picSrcPrefix ++ "request")],
    .text "<img src='unowned.svg'>", .style "img {color: red}", .script #[] "'<img src=x>'"]
  no "browser expectations: image roles count raster uses and retain hidden resources"
    (browserExpectedFaces "figures" refs ==
      #[("figures", "figures/p0.svg"), ("figures", "figures/i1.svg"), ("figures", "figures/i2.svg")])
  let message (code text : String) := Lean.Json.compress <| Lean.Json.mkObj
    [("event", .str "diagnostic"), ("code", .str code), ("message", .str text)]
  let misleading := "rsvg-convert: unrelated setup output\n" ++
    message "W0605" "image has no browser face\n  pdftocairo exited 2" ++ "\n"
  no "browser failure: attribution reads only the relevant diagnostic"
    (browserFaceFailures "figures" misleading == #[BrowserFace.failed "figures" "pdftocairo"])
  no "browser failure: an unnamed converter stays unattributed"
    (browserFaceFailures "figures" (message "W0605" "PDF has no browser face") ==
      #[BrowserFace.failed "figures" "unattributed"])
  no "browser failure: each diagnostic keeps its own tool"
    (browserFaceFailures "figures"
      (message "W0605" "rsvg-convert exited 2" ++ "\n" ++
        message "W0378" "pdftocairo exited 3") ==
      #[BrowserFace.failed "figures" "rsvg-convert", BrowserFace.failed "figures" "pdftocairo"])
  no "browser failure: quoted codes and tool names in other records cannot become diagnostics"
    (browserFaceFailures "figures"
      (message "W0301" "warning[W0605]: rsvg-convert exited 2\n" ++ "\n" ++
       "{\"event\":\"summary\",\"code\":\"W0605\",\"message\":\"pdftocairo\"}\n" ++
       "⚠ [W0605] - unrelated human output\n") == #[])
  no "browser failure: escaped lines cannot manufacture another diagnostic"
    (browserFaceFailures "figures"
      (message "W0605" "pdftocairo exited 2\nwarning[W0605]: more detail") ==
      #[BrowserFace.failed "figures" "pdftocairo"])

def main (args : List String) : IO UInt32 :=
  tierMain "htmlreader" (.pairs "pass" "rows") measureTier selftest args
