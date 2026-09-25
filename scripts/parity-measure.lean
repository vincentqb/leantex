/-
The parity ladder's three premises, measured rather than assumed. Run from
the repository root:

  lake build ParityLib
  lake env lean --run scripts/parity-measure.lean

This is a report, never a gate: it prints what two engines actually agree
on for the committed pairings, so a tolerance is set around a number
somebody read. It reads committed references only and invokes nothing, so
it runs with the reference engine absent.

The three premises, from the ladder's design:

  1. `/ToUnicode` is real on the reference side, so no glyph-name
     reconstruction is needed. Falsified by any unmapped scalar in the
     reference's reading — the reader substitutes U+FFFD for a glyph it
     cannot name, so the count of those *is* the measurement.
  2. fontspec pointed at the fixture's own font gives identical advances.
     Measured as the width of the longest shared run on each side.
  3. lualatex's line breaks agree with the engine's Knuth-Plass in
     practice. Measured by grouping each side's runs into lines by
     baseline and comparing the line texts — the reading the page-level
     order rung is blind to.
-/
import scripts.ParityCore

open LeanTex.Core Parity

/-- One line of a page, as the file paints it: a baseline and the scalars
on it. Runs are grouped by their `y`, which both writers set per line. -/
structure ArtLine where
  y : Dim.Sp
  text : String
  width : Dim.Sp
  deriving Repr, Inhabited

/-- A page's lines, in painting order, grouped by baseline. Both engines
emit runs down the page, so first appearance order is reading order; the
grouping is by exact `y` because both writers position each line once. -/
def linesOf (p : ArtPage) : Array ArtLine := Id.run do
  let mut ys : Array Dim.Sp := #[]
  let mut texts : Array String := #[]
  let mut x0 : Array Dim.Sp := #[]
  let mut x1 : Array Dim.Sp := #[]
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

/-- How many scalars a reading could not name. `artUnmapped` is what the
reader substitutes for a glyph with no `/ToUnicode` entry, so this counts
exactly the glyphs that would need name reconstruction. -/
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

/-- The widest run both sides paint with identical text, and each side's
advance for it. The comparison is per identical string so the two numbers
are advances over the same glyphs: a difference is the `hmtx` read
differently, which is premise 2 falsified. -/
def sharedRunDelta (e r : Array ArtPage) : Option (String × Dim.Sp × Dim.Sp) := Id.run do
  let mut best : Option (String × Dim.Sp × Dim.Sp) := none
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

/-- The line readings side by side, and where they part. Reported as a
count of agreeing lines out of the shorter reading: a line-break
disagreement shows as the first index whose texts differ. -/
def lineReport (stem : String) (e r : Array ArtPage) : IO Unit := do
  let mut agree := 0
  let mut total := 0
  let mut firstDiff : Option String := none
  for pi in [0:min e.size r.size] do
    let el := linesOf e[pi]!
    let rl := linesOf r[pi]!
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

/-- Every Type0 font a file carries, with its descendant's `/W` read two
ways: as the artifact reader reads it, and with the indirect reference
followed. A writer may put `/W` behind a reference, and the two numbers
part exactly when it does — which is premise 2's real subject, since a
width map that came back empty leaves every glyph on `/DW`. -/
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

/-- What shape the reference's `/W` entry has, so a routed fix names the
right thing: whether it is an array in place or a reference to one, and
how many top-level items that array carries. -/
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

def main : IO UInt32 := do
  let pats := Hyphen.english.get
  let some fontData ← findFont | throw (IO.userError "parity-measure: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "parity-measure: corpus font unparsable")
  let oneFace := oneFaceOf font
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
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
      IO.println s!"  advances: {repr t} ({t.length} scalars) — engine {Dim.Sp.toPtString ew}, \
reference {Dim.Sp.toPtString rw}, delta {Dim.Sp.toPtString (ew - rw)}"
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
  return 0
