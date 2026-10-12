module

public import Tests.Support
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.SlotLoss

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly FontScan

/-! **An undeclared typewriter slot sets in a monospaced face wherever the
font environment holds one, and a font collection's faces are part of that
environment.**

A document that declared no typewriter family set its code in the
proportional text face, and W0390 named it, whenever its text family had
no designed companion the scan served: on macOS, where the system's own
monospace faces ship as font collections the scan skipped, that was every
such document. The invariants: the platform list is read in order, the
first family the scan serves whole fills the slot, and W0390 names only a
scan that serves none — two builds apart, on either surface — while both
artifacts set the code in the chosen face: its runs on `Layout.Out`, and
the HTML's typewriter stack and the face it ships. A collection's faces are
found by the scan, read face by face, and shipped as the standalone font
files a reader of one face expects; truncated and mutated collections are
refused or read within their bytes. The suite's own font files stand in
for the platform faces under the scan records' names, packed into a
collection by an encoder of the check's own. Every word here is invented. -/

namespace Tests.MonoDefault

/-- Open Sans's four files as a text family no project pairs with a
typewriter face, so only the platform list can serve its slot. -/
def unpaired : Array FontDb.Face :=
  #[face "Open Sans" false (path := testFonts ++ "/OpenSans-Regular.ttf"),
    face "Open Sans" false (bold := true) (path := testFonts ++ "/OpenSans-Bold.ttf"),
    face "Open Sans" false (italic := true) (path := testFonts ++ "/OpenSans-Italic.ttf"),
    face "Open Sans" false (bold := true) (italic := true)
      (path := testFonts ++ "/OpenSans-BoldItalic.ttf")]

private def be16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v / 256 % 256).toUInt8).push (v % 256).toUInt8

private def be32 (b : ByteArray) (v : Nat) : ByteArray :=
  be16 (be16 b (v / 65536 % 65536)) (v % 65536)

/-- A standalone font's tables as its directory names them: tag, checksum
and bytes, in directory order. -/
def tablesOf (f : ByteArray) : Array (Nat × Nat × ByteArray) :=
  (Array.range (Ink.u16 f 4)).map fun k =>
    let e := 12 + 16 * k
    let off := Ink.u32 f (e + 8)
    (Ink.u32 f e, Ink.u32 f (e + 4), f.extract off (off + Ink.u32 f (e + 12)))

/-- A font collection of standalone font files, packed as the OpenType
spec lays one out: the `ttcf` header and one offset per face, every face's
directory with its offsets made absolute, then every table at its
four-byte boundary — an encoder of this check's own, so the engine's
reader is not judged by its own writer. -/
def packCollection (fonts : Array ByteArray) : ByteArray := Id.run do
  let faces := fonts.map tablesOf
  let mut pos := 12 + 4 * fonts.size
  let mut dirAt : Array Nat := #[]
  for ts in faces do
    dirAt := dirAt.push pos
    pos := pos + 12 + 16 * ts.size
  let mut tableAt : Array (Array Nat) := #[]
  for ts in faces do
    let mut row : Array Nat := #[]
    for (_, _, b) in ts do
      row := row.push pos
      pos := (pos + b.size + 3) / 4 * 4
    tableAt := tableAt.push row
  let mut out := be32 (be32 (be32 ByteArray.empty 0x74746366) 0x00010000) fonts.size
  for d in dirAt do
    out := be32 out d
  for (f, ts, row) in fonts.zip (faces.zip tableAt) do
    out := out ++ f.extract 0 12
    for ((tag, sum, b), place) in ts.zip row do
      out := be32 (be32 (be32 (be32 out tag) sum) place) b.size
  for ts in faces do
    for (_, _, b) in ts do
      out := out ++ b
      for _ in [0:(b.size + 3) / 4 * 4 - b.size] do
        out := out.push 0
  return out

/-- Does every table a standalone font's directory names lie inside it? -/
def directoryFits (b : ByteArray) : Bool :=
  let n := Ink.u16 b 4
  12 + 16 * n ≤ b.size && (List.range n).all fun k =>
    let e := 12 + 16 * k
    Ink.u32 b (e + 8) + Ink.u32 b (e + 12) ≤ b.size

/-- The `src` the HTML's `@font-face` for the typewriter slot's regular
face names. -/
def monoSrc (html : String) : Option String :=
  match html.splitOn "@font-face { font-family: \"ltx-mono\"; font-weight: 400; \
font-style: normal; src: url(\"" with
  | _ :: rest :: _ => (rest.splitOn "\")").head?
  | _ => none

/-- The generic family the HTML's typewriter stack over the faces it
ships closes on. -/
def monoGeneric (html : String) : Option String :=
  match html.splitOn "--font-mono: \"ltx-mono\"" with
  | _ :: rest :: _ => (rest.splitOn ";").head?.bind fun stack => (stack.splitOn ", ").getLast?
  | _ => none

/-- A markdown and a tex document, each with inline and displayed code. -/
def codeDocs : List (String × Ir.Doc) :=
  [("markdown", (elabMd "Words with `inline code` beside them.\n\n```\nfenced code\n```\n").1),
   ("tex", (elabStr (dvDoc "" ("Words with \\texttt{inline code} beside them.\n\n" ++
      "\\begin{verbatim}\nfenced code\n\\end{verbatim}"))).1)]

/-- The scan the assembly reads: these faces, nothing else. -/
def scanOf (faces : Array FontDb.Face) : FaceScan :=
  { faces, docDirs := [], dirs := #[], diags := #[] }

/-- **The platform monospace, read in order, and its premise two builds
apart.** Over scan records: the list's order, a listed family passed over
for a missing corner or a proportional face, a fixed-pitch family off the
list never taken, and the companion before the list. Through the driver's
assembly, on either surface: with a platform monospace in the scan the
slot is that face, fixed-pitch, and no loss is named; without it, or with
it short of a corner, the slot is the text face and W0390 names it — the
default moves ink, it never silences a loss. Both artifacts carry the
decision: the code's runs on the shipped page, and the HTML's typewriter
stack and the face its `@font-face` ships. -/
def monoDefaultChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let menlo := family4 "Menlo" "m.ttc#0" true
  t "the platform list prefers SF Mono to Menlo"
    (FontDb.monoDefault (menlo ++ family4 "SF Mono" "s.otf" true) == some "SF Mono")
  t "the platform list prefers Menlo to DejaVu Sans Mono"
    (FontDb.monoDefault (family4 "DejaVu Sans Mono" "d.ttf" true ++ menlo) == some "Menlo")
  t "the platform list prefers DejaVu Sans Mono to Liberation Mono"
    (FontDb.monoDefault (family4 "Liberation Mono" "l.ttf" true ++
      family4 "DejaVu Sans Mono" "d.ttf" true) == some "DejaVu Sans Mono")
  t "a listed family missing a corner is passed over for the next"
    (FontDb.monoDefault (#[face "SF Mono" true] ++ menlo) == some "Menlo")
  t "a listed family whose faces are proportional is passed over for the next"
    (FontDb.monoDefault (family4 "Menlo" "m.ttc#0" false ++ family4 "Liberation Mono" "l.ttf" true)
      == some "Liberation Mono")
  t "a fixed-pitch family off the list is never taken by guess"
    (FontDb.monoDefault (family4 "Aardvark Mono" "a.ttf" true) == none)
  t "the text family's designed companion answers before the platform list"
    (FontDb.monoFor (#[face "DejaVu Sans" false] ++ family4 "DejaVu Sans Mono" "d.ttf" true ++ menlo)
      (some "DejaVu Sans") == some "DejaVu Sans Mono")
  t "a default text family with no companion takes the platform list"
    (FontDb.monoFor (#[face "Helvetica Neue" false] ++ menlo) (some "Helvetica Neue") == some "Menlo")
  let cache ← FontEnv.Cache.mk'
  let code := testFonts ++ "/SourceCodePro-Regular.otf"
  let withList := scanOf (unpaired ++ family4 "Menlo" code true)
  let short := scanOf (unpaired ++ #[face "Menlo" true (path := code)])
  for (surface, doc) in codeDocs do
    match ← buildFontSet doc withList cache .settled, ← buildFontSet doc (scanOf unpaired) cache .settled,
        ← buildFontSet doc short cache .settled with
    | .ok (fsA, docA, diagsA, pathsA), .ok (fsB, docB, _, _), .ok (fsC, docC, diagsC, _) =>
      let loss (fs : Font.FontSet) (d : Ir.Doc) :=
        SlotLoss.diags d.fonts fs d (SlotLoss.carries #[.pdf, .html] d.fontPolicy)
      let monoA := fsA.lookup 2 400 false
      let textB := fsB.lookup 0 400 false
      t s!"{surface}: a platform monospace fills the undeclared slot whole, and no loss is named"
        (fsA.slotIsFixedPitch 2 && !fsA.slotCollapsed 2 && (loss fsA docA).isEmpty
          && pathsA.contains code && !diagsA.any (·.kind == .W0006))
      t s!"{surface}: a scan with no platform monospace leaves the slot to the text face, and W0390 names it"
        (fsB.slotCollapsed 2 && (loss fsB docB).any (·.kind == .W0390))
      t s!"{surface}: a listed family short of a corner is no default, and W0390 names the slot"
        (fsC.slotCollapsed 2 && (loss fsC docC).any (·.kind == .W0390)
          && !diagsC.any (·.kind == .W0006))
      t s!"{surface} page: the code ships in the platform monospace, and without it in the text face"
        (runFace (layoutOf fsA docA) "fenced" == some monoA && (fsA.get monoA).isFixedPitch
          && runFace (layoutOf fsB docB) "fenced" == some textB && !(fsB.get textB).isFixedPitch)
      let (htmlA, _) := HtmlDoc.emit { fonts := some fsA } docA
      let (htmlB, _) := HtmlDoc.emit { fonts := some fsB } docB
      t s!"{surface} html: the typewriter stack closes on monospace, and without the default on the text face's generic"
        (monoGeneric htmlA == some "monospace" && monoGeneric htmlB == some "sans-serif")
      t s!"{surface} html: the typewriter face the page ships is the platform monospace, and without it the text face"
        (monoSrc htmlA == some (HtmlDoc.fontResource (fsA.get monoA)).uri && (fsA.get monoA).isFixedPitch
          && monoSrc htmlB == some (HtmlDoc.fontResource (fsB.get textB)).uri
          && !(fsB.get textB).isFixedPitch)
    | _, _, _ => t s!"{surface}: the three assemblies succeed" false
  -- A document that sets no typewriter run loads no typewriter face: no
  -- page ships faces it never sets, and there is no loss to name.
  for (surface, doc) in
      [("markdown", (elabMd "Words and nothing set in code.\n").1),
       ("tex", (elabStr (dvDoc "" "Words and nothing set in code.")).1)] do
    match ← buildFontSet doc withList cache .settled with
    | .ok (fs, resolved, _, paths) =>
      t s!"{surface}: a document setting no typewriter run loads no typewriter face"
        (!paths.contains code && fs.slotCollapsed 2
          && (SlotLoss.diags resolved.fonts fs resolved
            (SlotLoss.carries #[.pdf, .html] resolved.fontPolicy)).isEmpty)
    | .error d => t s!"{surface}: the assembly succeeds ({d.message})" false

/-- **A font collection's faces are fonts the engine can use.** Each face
read out of a packed collection is the file it was packed from, table for
table, and parses as it; an index past the count and a standalone file are
refused; every truncation and every mutant of the header and directories
is refused or read within its bytes. On disk, the scan finds each face
under its member path, a cached scan replays them, a truncated collection
contributes none, and a collection's face fills a slot through the
driver's assembly: the page's code runs set in it and the HTML ships it as
a standalone font file, never the collection. -/
def fontCollectionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let read (f : String) : IO ByteArray := IO.FS.readBinFile (testFonts ++ "/" ++ f)
  let regular ← read "OpenSans-Regular.ttf"
  let bold ← read "OpenSans-Bold.ttf"
  let code ← read "SourceCodePro-Regular.otf"
  let ttc := packCollection #[regular, bold]
  t "a packed collection counts its faces" (Font.collectionCount ttc == some 2)
  t "a standalone font is no collection" (Font.collectionCount regular == none)
  let same (a b : Font.Font) : Bool :=
    a.family == b.family && a.weight == b.weight && a.isBold == b.isBold
      && a.unitsPerEm == b.unitsPerEm && a.numGlyphs == b.numGlyphs
      && "Quartz glyphs 0123".toList.all fun c => a.advance c == b.advance c
  for (i, orig) in [(0, regular), (1, bold)] do
    match Font.collectionMember ttc i, Font.parse orig with
    | .ok m, .ok of =>
      t s!"collection face {i}: every table is its file's, byte for byte"
        ((tablesOf m).map (fun (tag, _, b) => (tag, b.toList)) ==
          (tablesOf orig).map (fun (tag, _, b) => (tag, b.toList)))
      t s!"collection face {i}: a standalone font, parsed as its file is"
        (Font.collectionCount m == none && directoryFits m &&
          match Font.parse m with
          | .ok f => same f of
          | .error _ => false)
    | _, _ => t s!"collection face {i} reads" false
  t "an index past the collection's count is refused"
    (Font.collectionMember ttc 2 matches .error _)
  t "a standalone font is refused as a collection"
    (Font.collectionMember regular 0 matches .error _)
  let mut cases := 0
  let mut outside := 0
  for k in [0:97] do
    for i in [0:2] do
      cases := cases + 1
      if let .ok m := Font.collectionMember (ttc.extract 0 (ttc.size * k / 97)) i then
        unless directoryFits m do outside := outside + 1
  let dirEnd := 12 + 8 + (12 + 16 * Ink.u16 regular 4) + (12 + 16 * Ink.u16 bold 4)
  for pos in [0:dirEnd] do
    for v in ([0x00, 0x01, 0x7F, 0xFF] : List UInt8) do
      for i in [0:2] do
        cases := cases + 1
        if let .ok m := Font.collectionMember (ttc.set! pos v) i then
          unless directoryFits m do outside := outside + 1
  t s!"truncated and mutated collections are refused or read within their bytes \
({outside} of {cases} outside)"
    (outside == 0 && cases > 2000)
  let cache ← FontEnv.Cache.mk'
  IO.FS.withTempDir fun dir => do
    let file := (dir / "Example.ttc").toString
    let mono := (dir / "Mono.otc").toString
    IO.FS.writeBinFile file ttc
    IO.FS.writeBinFile mono (packCollection #[code])
    let faces ← FontDiscovery.scanRootsIn none [dir.toString]
    t "the scan finds each face a collection holds, under its member path"
      (faces.map (·.path) == #[FontDb.memberPath file 0, FontDb.memberPath file 1,
          FontDb.memberPath mono 0]
        && faces.map (·.family) == #["Open Sans", "Open Sans", "Source Code Pro"]
        && faces.map (·.weight) == #[400, 700, 400]
        && faces.map (·.fixedPitch) == #[false, false, true])
    let expected := #[FontDb.memberPath file 0, FontDb.memberPath file 1, FontDb.memberPath mono 0]
    IO.FS.withTempDir fun cacheDir => do
      let cold ← FontDiscovery.scanRootsIn (some cacheDir) [dir.toString]
      let warm ← FontDiscovery.scanRootsIn (some cacheDir) [dir.toString]
      t "a cached scan replays a collection's faces"
        (cold.map (·.path) == expected && warm.map (·.path) == expected
          && warm.map (·.family) == faces.map (·.family))
    let damaged := (dir / "Damaged.ttc").toString
    IO.FS.writeBinFile damaged (ttc.extract 0 200)
    let after ← FontDiscovery.scanRootsIn none [dir.toString]
    t "a truncated collection on disk contributes no face, and the others still stand"
      (after.map (·.path) == expected)
    let member := FontDb.memberPath mono 0
    let doc := (elabMd "Words with `inline code` beside them.\n\n```\nfenced code\n```\n").1
    match ← buildFontSet doc (scanOf (unpaired ++ family4 "Menlo" member true)) cache .settled,
        Font.collectionMember (packCollection #[code]) 0 with
    | .ok (fs, resolved, diags, paths), .ok standalone =>
      let slot := fs.lookup 2 400 false
      let face := fs.get slot
      t "a collection's face fills the typewriter slot through the assembly"
        (paths.contains member && face.isFixedPitch && !fs.slotCollapsed 2
          && !diags.any (·.kind == .E0404))
      t "the page's code runs set in the collection's face"
        (runFace (layoutOf fs resolved) "fenced" == some slot && face.isFixedPitch)
      let (html, _) := HtmlDoc.emit { fonts := some fs } resolved
      t "the HTML ships the collection's face as a standalone font file, never the collection"
        (monoSrc html == some (HtmlDoc.fontResource face).uri
          && (HtmlDoc.fontResource face).bytes == standalone
          && Font.collectionCount (HtmlDoc.fontResource face).bytes == none)
    | _, _ => t "a collection's face assembles and reads" false

end Tests.MonoDefault
