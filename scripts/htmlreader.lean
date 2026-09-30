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
recipe. Every `browser-face:` row then pins one href to the SHA-256 and size of
the exact bytes the oracle gave the browser; `browser-face-key:` covers those
rows. Missing, malformed, duplicated, stale, or failed captures are faults, so
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

open Scoreboard
open LeanTex.Core

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
  let face := BrowserFace.captured "figures" "figures.assets/i0-box.svg" "<svg/>".toUTF8
  let changedBytes := BrowserFace.captured "figures" "figures.assets/i0-box.svg"
    "<svg><path/></svg>".toUTF8
  let changedHref := BrowserFace.captured "figures" "figures.assets/i1-box.svg" "<svg/>".toUTF8
  let failed := BrowserFace.failed "figures" "figures.assets/i0-box.svg" "pdftocairo"
  no "browser face: converted bytes move the key"
    (browserFaceKey #[face] != browserFaceKey #[changedBytes])
  no "browser face: the rendered href moves the key"
    (browserFaceKey #[face] != browserFaceKey #[changedHref])
  no "browser face: a tool failure moves the key"
    (browserFaceKey #[face] != browserFaceKey #[failed])
  no "browser face: the committed record round-trips"
    (BrowserFace.parse face.render == some face)
  -- The expected converted-image identities the typed store projects. The
  -- committed records must match this set exactly.
  let exp : Array (String × String) := #[("figures", "figures.assets/i0-box.svg")]
  let faces (fs : Array BrowserFace) : String :=
    "browser-face-src-key: source\nbrowser-face-key: " ++ browserFaceKey fs ++ "\n" ++
      String.intercalate "\n" (fs.map (·.render)).toList ++ "\n"
  -- Matching set: one expected face, one exact capture, keys agree.
  no "browser face: matching source and exact capture certify the cells"
    (browserFaceFaults (faces #[face]) "source" exp).isEmpty
  -- Fail-first: delete the one expected capture (no records at all).
  no "browser face: a deleted expected capture is a fault (missing)"
    (!(browserFaceFaults
      ("browser-face-src-key: source\nbrowser-face-key: " ++ browserFaceKey #[] ++ "\n")
      "source" exp).isEmpty)
  -- Fail-first: add one extra converted image face not in the expected set.
  let extra := BrowserFace.captured "figures" "figures.assets/i9-extra.svg" "<svg/>".toUTF8
  no "browser face: an extra converted image face is a fault"
    (!(browserFaceFaults (faces #[face, extra]) "source" exp).isEmpty)
  -- Fail-first: rename the one capture — the expected identity is now
  -- missing and the renamed one is an extra.
  no "browser face: a renamed capture is a fault (missing + extra)"
    (!(browserFaceFaults (faces #[changedHref]) "source" exp).isEmpty)
  -- Fail-first: fail the one conversion — a failed record still names the
  -- expected href (so it is not missing) but a failed conversion faults.
  no "browser face: a failed conversion of an expected face is a fault"
    (!(browserFaceFaults (faces #[failed]) "source" exp).isEmpty)
  no "browser face: a failed record names the expected href, so it is not also missing"
    ((browserFaceFaults (faces #[failed]) "source" exp).all fun f =>
      !f.startsWith "expected converted image face")
  -- Fail-first: duplicate the one capture.
  no "browser face: duplicate hrefs are a fault"
    (!(browserFaceFaults (faces #[face, face]) "source" exp).isEmpty)
  -- Moved hermetic inputs stale the capture even when records match.
  no "browser face: moved hermetic inputs stale the capture"
    (!(browserFaceFaults (faces #[face]) "different-source" exp).isEmpty)
  -- A boundary picture's hex-named SVG is classified positively (its stem is
  -- the shape `Ir.picHash` produces): captured beside the image face, it is
  -- neither missing nor an extra image face.
  let boundary := BrowserFace.captured "figures"
    "figures.assets/0123456789abcdef0123456789abcdef.svg" "<svg/>".toUTF8
  no "browser face: a boundary picture SVG is neither missing nor extra"
    (browserFaceFaults (faces #[face, boundary]) "source" exp).isEmpty
  no "browser face: the boundary SVG name is classified as a boundary face, not an image face"
    (HtmlDoc.isBoundaryFaceName (HtmlDoc.basename boundary.href) &&
      !HtmlDoc.isImageFaceName (HtmlDoc.basename boundary.href))
  -- Fail-closed: a captured SVG matching neither classifier is unclassified
  -- and faults, rather than being silently admitted as a boundary face.
  let garbage := BrowserFace.captured "figures" "figures.assets/garbage.svg" "<svg/>".toUTF8
  no "browser face: an unclassified SVG name is a fault"
    (!(browserFaceFaults (faces #[face, garbage]) "source" exp).isEmpty)
  let shortHex := BrowserFace.captured "figures" "figures.assets/0123abcd.svg" "<svg/>".toUTF8
  no "browser face: a wrong-length hex stem is not a boundary face and faults"
    (!HtmlDoc.isBoundaryFaceName (HtmlDoc.basename shortHex.href) &&
      !(browserFaceFaults (faces #[face, shortHex]) "source" exp).isEmpty)
  -- Deleting a boundary capture moves the content key, so a committed key can
  -- never outlive the boundary faces it measured.
  no "browser face: deleting a boundary capture moves the key"
    (browserFaceKey #[face, boundary] != browserFaceKey #[face])
  no "browser face: an image face name is classified as one"
    (HtmlDoc.isImageFaceName (HtmlDoc.basename face.href) &&
      HtmlDoc.isImageFaceName (HtmlDoc.basename
        (BrowserFace.captured "f" "f.assets/p0-box.svg" "".toUTF8).href))
  -- Real generated names run through the classifier: converted i…/p… .svg
  -- faces are image faces; a picHash boundary name is a boundary face; a
  -- raster's own-extension name and a non-.svg i-name are neither image faces.
  no "browser face: real converted image-face names classify as image faces"
    (HtmlDoc.isImageFaceName (HtmlDoc.imageAssetName 0 "box.svg") &&
      HtmlDoc.isImageFaceName (HtmlDoc.imagePosterName 3 { src := "box.pdf" }))
  no "browser face: a non-.svg i-name (a raster asset) is rejected as an image face"
    (!HtmlDoc.isImageFaceName (HtmlDoc.imageAssetName 0 "photo.png") &&
      !HtmlDoc.isImageFaceName "i0-box.pdf")
  no "browser face: a picHash boundary name is a boundary face, not an image face"
    (HtmlDoc.isBoundaryFaceName (Ir.picHash "\\draw (0,0) -- (1,1);" ++ ".svg") &&
      !HtmlDoc.isImageFaceName (Ir.picHash "\\draw (0,0) -- (1,1);" ++ ".svg") &&
      !HtmlDoc.isImageFaceName (Ir.picHash "\\node {x};" ++ ".svg"))
  no "browser face: a raster source name is neither an image nor a boundary face"
    (!HtmlDoc.isImageFaceName "box.pdf" && !HtmlDoc.isBoundaryFaceName "box.pdf")
  -- The tool a face failure names is read from the diagnostic's own text, not
  -- from another line of the log; missing output with no diagnostic is
  -- unattributed, never a guessed converter.
  no "face failure tool: named in the diagnostic's reason"
    (faceFailureTool "warning[W0605]: image has no browser face\n  rsvg-convert exited 19"
      == "rsvg-convert" &&
     faceFailureTool "warning[W0605]: no browser face\n  pdftocairo exited 1" == "pdftocairo")
  no "face failure tool: a diagnostic naming no converter is unattributed"
    (faceFailureTool "warning[W0605]: PDF page no browser decodes" == "unattributed")
  no "face failure tool: a build log mentioning a tool elsewhere does not attribute it"
    (faceFailureTool
      (String.intercalate "\n" (w0605Blocks
        "note: rsvg-convert is installed\nwarning[W0605]: no browser face\n  no reason given\n\
info: pdftocairo present").toList) == "unattributed")
  no "w0605 blocks: only W0605 diagnostics and their indented reasons are read"
    (let bs := w0605Blocks "warning[W0605]: a\n  reason a\nwarning[W0301]: b\n  reason b"
     bs.size == 1 &&
       ((bs.getD 0 "").splitOn "reason a").length == 2 &&
       ((bs.getD 0 "").splitOn "reason b").length == 1)
  let malformedFace := "browser-face-src-key: source\nbrowser-face-key: deadbeef\n\
browser-face: figures missing-fields\n"
  no "browser face: a malformed record is a fault"
    (!(browserFaceFaults malformedFace "source" exp).isEmpty)
  no "browser face: absent records and keys are faults"
    (!(browserFaceFaults "src-key: html\n" "source" exp).isEmpty)
  -- The behavioural source key: the shared plan's decision and its
  -- deterministic stand-in output are hashed, and no whole driver source
  -- file is, so each meaningful mutation moves the key while a
  -- behaviour-preserving edit to Main.lean leaves it unmoved.
  let p1 : HtmlDoc.FacePlan := .convertedPrimary (.pdfPage .first)
  let p2 : HtmlDoc.FacePlan := .convertedPrimary (.pdfPage (.number 2))
  let p3 : HtmlDoc.FacePlan := .animatedWithCompanion (.pdfPage .first)
  let p4 : HtmlDoc.FacePlan := .movingSvgWithPoster .svgPoster
  no "src key: the requested page moves the plan key" (p1.key != p2.key)
  no "src key: the animation shape moves the plan key" (p1.key != p3.key)
  no "src key: an SVG source's plan differs from a PDF's" (p1.key != p4.key)
  no "src key: a resolved physical page moves the conversion key"
    (HtmlDoc.FaceConv.key (.pdfPage (.number 1)) != HtmlDoc.FaceConv.key (.pdfPage (.number 2)))
  let enA : Image.Loaded := { src := "a.pdf" }
  let enB : Image.Loaded := { src := "b.pdf" }
  no "src key: the resolved source moves the stand-in output"
    (HtmlDoc.faceStandIn enA p1 (.pdfPage .first)
      != HtmlDoc.faceStandIn enB p1 (.pdfPage .first))
  no "src key: the plan decision moves the stand-in output"
    (HtmlDoc.faceStandIn enA p1 (.pdfPage .first)
      != HtmlDoc.faceStandIn enA p4 .svgPoster)
  no "src key: the conversion contract is nonempty and hashed"
    (!LeanTex.Cli.ImageAssets.browserFaceContract.isEmpty)
  -- The src/poster hrefs and physical page ride in the per-request
  -- descriptor blob; contentKey is byte-sensitive (proven above), so a
  -- changed href, poster, or physical page moves the source key.
  no "src key: a changed descriptor field (href/poster/physical page) moves it"
    (contentKey #[("r", "href=x".toUTF8)] != contentKey #[("r", "href=y".toUTF8)])

def main (args : List String) : IO UInt32 :=
  tierMain "htmlreader" (.pairs "pass" "rows") measureTier selftest args
