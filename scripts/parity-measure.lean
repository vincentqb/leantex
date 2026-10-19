/-
Report measuring the parity ladder's premises over the committed pairings: `/ToUnicode`
coverage, advances under a shared font, and line breaks.
Usage: lake build ScriptsModules && lake env lean --run scripts/parity-measure.lean
-/
import LeanTex.Cli.FontDiscovery
import scripts.ParityCore

open LeanTex.Core LeanTex.Cli Parity

/-- One line of a page as the file paints it: a baseline and the scalars on it. -/
structure ArtLine where
  y : Dim.Length
  text : String
  width : Dim.Length
  deriving Repr, Inhabited

/-- A page's lines with their baseline and extent, in painting order, for the report's
advance and measure numbers. -/
def lineBoxesOf (p : ArtPage) : Array ArtLine := Id.run do
  let mut ys : Array Dim.Length := #[]
  let mut texts : Array String := #[]
  let mut x0 : Array Dim.Length := #[]
  let mut x1 : Array Dim.Length := #[]
  for r in p.runs do
    match ys.findIdx? (· == r.y) with
    | some i =>
      texts := texts.set! i (texts[i]! ++ r.text)
      x0 := x0.set! i (min x0[i]! r.x)
      x1 := x1.set! i (max x1[i]! r.x1)
    | none =>
      ys := ys.push r.y
      texts := texts.push r.text
      x0 := x0.push r.x
      x1 := x1.push r.x1
  let mut out : Array ArtLine := #[]
  for i in [0:ys.size] do
    let t := String.ofList (inked texts[i]!)
    unless t.isEmpty do
      out := out.push { y := ys[i]!, text := t, width := x1[i]! - x0[i]! }
  return out

/-- How many scalars a reading could not name: the glyphs with no `/ToUnicode` entry. -/
def unmappedCount (pages : Array ArtPage) : Nat := Id.run do
  let bad := artUnmapped.toList.headD (Char.ofNat 0xFFFD)
  let mut n := 0
  for p in pages do
    for r in p.runs do
      for c in r.text.toList do
        if c == bad then n := n + 1
  return n

/-- Every scalar a reading inks, so a denominator stands beside the count
of unnamed ones. -/
def scalarCount (pages : Array ArtPage) : Nat :=
  pages.foldl (fun a p => a + (p.runs.foldl (fun b r => b + (inked r.text).length) 0)) 0

/-- The widest run both sides paint with identical text, and each side's painted advance
for it, horizontal scale included. -/
def sharedRunDelta (e r : Array ArtPage) : Option (String × Dim.Length × Dim.Length) := Id.run do
  let mut best : Option (String × Dim.Length × Dim.Length) := none
  for pi in [0:min e.size r.size] do
    for a in e[pi]!.runs do
      let key := String.ofList (inked a.text)
      if key.length < 4 then continue
      for b in r[pi]!.runs do
        if String.ofList (inked b.text) == key then
          match best with
          | some (t, _, _) => if t.length < key.length then best := some (key, a.w, b.w)
          | none => best := some (key, a.w, b.w)
  return best

/-- The line readings side by side: agreeing lines out of the shorter reading, and the
first index where they part. -/
def lineReport (stem : String) (e r : Array ArtPage) : IO Unit := do
  let mut agree := 0
  let mut total := 0
  let mut firstDiff : Option String := none
  for pi in [0:min e.size r.size] do
    let el := lineBoxesOf e[pi]!
    let rl := lineBoxesOf r[pi]!
    total := total + max el.size rl.size
    for li in [0:min el.size rl.size] do
      if el[li]!.text == rl[li]!.text then agree := agree + 1
      else if firstDiff.isNone then
        firstDiff := some s!"p{pi + 1} line {li + 1}: engine {repr el[li]!.text}, reference {repr rl[li]!.text}"
    unless el.size == rl.size do
      if firstDiff.isNone then
        firstDiff := some s!"p{pi + 1}: engine {el.size} lines, reference {rl.size}"
  IO.println s!"  lines: {agree}/{total} identical"
  match firstDiff with
  | some d => IO.println s!"    first difference — {d}"
  | none => IO.println s!"    every line of {stem} breaks at the same word on both sides"

/-- Every Type0 font a file carries, with its descendant's `/W` read as the artifact
reader reads it and with the indirect reference followed. -/
def widthMapSizes (pdf : ByteArray) : Except String (Array (Nat × Nat × Int)) := do
  let es ← PdfRead.objects pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let mut out : Array (Nat × Nat × Int) := #[]
  for e in esv do
    let o := e.val
    if (o.get? "Subtype") != some (PdfRead.Obj.name "Type0") then continue
    let cid := match deref ((o.get? "DescendantFonts").getD .null) with
      | .arr xs => deref (xs[0]?.getD .null)
      | d => d
    let raw := (cid.get? "W").getD .null
    let asRead := (artWidthMap raw).size
    let followed := (artWidthMap (deref raw)).size
    let dw := ((cid.get? "DW").bind PdfRead.Obj.int?).getD 1000
    out := out.push (asRead, followed, dw)
  return out

/-- The shape of the reference's `/W` entry: an array in place or a reference to one, and
its top-level item count. -/
def widthEntryShape (pdf : ByteArray) : Except String (Array String) := do
  let es ← PdfRead.objects pdf
  let esv := es.val
  let deref := PdfCensus.deref esv
  let mut out : Array String := #[]
  for e in esv do
    let o := e.val
    if (o.get? "Subtype") != some (PdfRead.Obj.name "Type0") then continue
    let cid := match deref ((o.get? "DescendantFonts").getD .null) with
      | .arr xs => deref (xs[0]?.getD .null)
      | d => d
    let raw := (cid.get? "W").getD .null
    let shape (x : PdfRead.Obj) : String :=
      match x with
      | .arr xs => s!"an array of {xs.size} item(s)"
      | .ref n g => s!"a reference to {n} {g}"
      | .null => "absent"
      | _ => "something else"
    out := out.push s!"/W in place is {shape raw}; followed it is {shape (deref raw)}"
  return out

/-- The placement distribution per page: same-character glyphs matched one to one, |Δx|
and |Δy| as p50 / p95 / max, raw and with the page's first-baseline offset removed. -/
def placeReport (e r : Array ArtPage) : IO Unit := do
  for pi in [0:min e.size r.size] do
    let (pairs, unmatched) := placePairs e[pi]! r[pi]!
    if pairs.isEmpty then
      IO.println s!"  place p{pi + 1}: nothing paired"
      continue
    -- The page's own baseline offset: the median Δy, constant under an origin offset.
    let dys := pairs.map fun (a, b) => a.2 - b.2
    let shift := atPercentile dys 50
    let dxs := pairs.map fun (a, b) => (a.1 - b.1).abs
    let raw := pairs.map fun (a, b) => (a.2 - b.2).abs
    let corrected := pairs.map fun (a, b) => (a.2 - b.2 - shift).abs
    let dist (label : String) (ys : Array Dim.Length) : String :=
      s!"{label} p50 {Dim.Length.toBpString (atPercentile ys 50)}, \
p95 {Dim.Length.toBpString (atPercentile ys 95)}, \
max {Dim.Length.toBpString (atPercentile ys 100)}"
    IO.println s!"  place p{pi + 1}: {pairs.size} glyph(s) paired, {unmatched} skipped"
    IO.println s!"    {dist "|dx|" dxs}"
    IO.println s!"    {dist "|dy| raw" raw}"
    IO.println s!"    {dist s!"|dy| less the page shift {Dim.Length.toBpString shift}" corrected}"

def main : IO UInt32 := do
  let pats := Hyphen.english.get
  let some fontData ← findFont | throw (IO.userError "parity-measure: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "parity-measure: corpus font unparsable")
  let oneFace := oneFaceOf font
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDiscovery.scanRoots [testFonts]
  IO.println "parity-measure: the ladder's three premises, on the committed pairings"
  for stem in ← parityNames do
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    unless ← sidecarPath.pathExists do continue
    let .ok side := Sidecar.parse (← IO.FS.readFile sidecarPath) | continue
    unless side.compiles do continue
    let refBytes ← IO.FS.readBinFile (System.FilePath.mk parityDir / (stem ++ ".ref.pdf"))
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let (doc, _) ← elabFixture stem src
    let geom := Layout.Geom.ofPage doc.page
    let fs ← fixtureFontSet oneFace mathSet shipped doc
    let out := layoutOf fs doc geom (some pats) {}
    let .ok ePages := readArtifact (driverPdf fs geom doc out {})
      | do IO.eprintln s!"{stem}: the engine's own bytes are unreadable"; return 1
    let .ok rPages := readArtifact refBytes
      | do IO.eprintln s!"{stem}: the committed reference is unreadable"; return 1
    IO.println s!"\n{stem}: engine {ePages.size} page(s), reference {rPages.size}"
    let (eu, ru) := (unmappedCount ePages, unmappedCount rPages)
    IO.println s!"  ToUnicode: reference {ru} unnamed of {scalarCount rPages} scalars, \
engine {eu} of {scalarCount ePages}"
    match sharedRunDelta ePages rPages with
    | some (t, ew, rw) =>
      IO.println s!"  advances (painted, horizontal scale included): {repr t} ({t.length} scalars) — \
engine {Dim.Length.toBpString ew}, reference {Dim.Length.toBpString rw}, delta {Dim.Length.toBpString (ew - rw)}"
    | none => IO.println "  advances: the two sides share no run of four scalars or more"
    for (label, bytes) in [("engine", driverPdf fs geom doc out {}), ("reference", refBytes)] do
      match widthMapSizes bytes with
      | .error e => IO.println s!"  widths ({label}): unreadable: {e}"
      | .ok fs' =>
        for (asRead, followed, dw) in fs' do
          IO.println s!"  widths ({label}): /W as the reader reads it {asRead} glyph(s), \
with the reference followed {followed}, /DW {dw}"
      match widthEntryShape bytes with
      | .error _ => pure ()
      | .ok shapes => for s in shapes do IO.println s!"  widths ({label}): {s}"
    lineReport stem ePages rPages
    placeReport ePages rPages
  return 0
