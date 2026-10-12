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
  -- A document that ships its fonts is answered from its own faces alone:
  -- a platform monospace the host holds never displaces one it ships, and
  -- one it does not ship leaves its slot to the text face on every host.
  IO.FS.withTempDir fun host => do
    let hostCode := (host / "Code.otf").toString
    IO.FS.writeBinFile hostCode (← IO.FS.readBinFile code)
    let shipped (own : Array FontDb.Face) (hostFaces : Array FontDb.Face) : FaceScan :=
      { faces := own ++ hostFaces, docDirs := [testFonts], dirs := #[], diags := #[] }
    let ownText := unpaired
    let ownMono := family4 "DejaVu Sans Mono" code true
    let hostMenlo := family4 "Menlo" hostCode true
    let doc := (codeDocs.lookup "tex").getD {}
    match ← buildFontSet doc (shipped (ownText ++ ownMono) hostMenlo) cache .settled,
        ← buildFontSet doc (shipped (ownText ++ ownMono) #[]) cache .settled,
        ← buildFontSet doc (shipped ownText hostMenlo) cache .settled,
        ← buildFontSet doc (shipped ownText #[]) cache .settled with
    | .ok (fsA, _, _, pathsA), .ok (fsB, _, _, pathsB), .ok (fsC, docC, _, pathsC),
        .ok (fsD, docD, _, _) =>
      let loss (fs : Font.FontSet) (d : Ir.Doc) :=
        SlotLoss.diags d.fonts fs d (SlotLoss.carries #[.pdf, .html] d.fontPolicy)
      t "a document shipping its fonts sets the typewriter face it ships, whatever the host holds"
        (pathsA.contains code && !pathsA.contains hostCode && pathsB.contains code
          && fsA.slotIsFixedPitch 2 && fsB.slotIsFixedPitch 2)
      t "a document shipping no typewriter face sets its code in its text face on every host"
        (!pathsC.contains hostCode && fsC.slotCollapsed 2 && fsD.slotCollapsed 2
          && (loss fsC docC).any (·.kind == .W0390) && (loss fsD docD).any (·.kind == .W0390))
    | _, _, _, _ => t "the shipped-fonts assemblies succeed" false
  -- The census reaches every typewriter run a document sets, among them a
  -- picture's label and a formula's typewriter alphabet: each alone moves
  -- the slot to the platform monospace, and without the run nothing loads.
  for (what, body) in
      [("a picture's label", "\\begin{tikzpicture}\\node at (0,0) {\\texttt{label code}};\\end{tikzpicture}"),
       ("a formula's typewriter alphabet", "A formula $\\mathtt{abc}$ in words.")] do
    let (doc, _) := elabStr (dvDoc "\\usepackage{tikz}\n" body)
    let (bare, _) := elabStr (dvDoc "\\usepackage{tikz}\n" "Plain words only.")
    match ← buildFontSet doc withList cache .settled, ← buildFontSet bare withList cache .settled with
    | .ok (_, _, _, paths), .ok (_, _, _, barePaths) =>
      t s!"{what} alone loads the platform monospace"
        (paths.contains code && !barePaths.contains code)
    | _, _ => t s!"{what}: the assemblies succeed" false
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
        ((fontTables m).map (fun (tag, _, b) => (tag, b.toList)) ==
          (fontTables orig).map (fun (tag, _, b) => (tag, b.toList)))
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
  -- A face the reader answers holds no more table bytes than its file: its
  -- directory and padding beside them, nothing copied out twice.
  let bounded (input m : ByteArray) : Bool :=
    directoryFits m && m.size ≤ input.size + 12 + 19 * Ink.u16 m 4
  let mut cases := 0
  let mut outside := 0
  for k in [0:97] do
    for i in [0:2] do
      cases := cases + 1
      let cut := ttc.extract 0 (ttc.size * k / 97)
      if let .ok m := Font.collectionMember cut i then
        unless bounded cut m do outside := outside + 1
  let dirEnd := 12 + 8 + (12 + 16 * Ink.u16 regular 4) + (12 + 16 * Ink.u16 bold 4)
  for pos in [0:dirEnd] do
    for v in ([0x00, 0x01, 0x7F, 0xFF] : List UInt8) do
      for i in [0:2] do
        cases := cases + 1
        let mutant := ttc.set! pos v
        if let .ok m := Font.collectionMember mutant i then
          unless bounded mutant m do outside := outside + 1
  t s!"truncated and mutated collections are refused or read within their bytes \
({outside} of {cases} outside)"
    (outside == 0 && cases > 2000)
  -- One region of the file named by every record of a face's directory:
  -- refused, where copying each record out made the face hundreds of times
  -- its file.
  let repeated := Id.run do
    let records := 400
    let region := 4096
    let dir := 16
    let tables := dir + 12 + 16 * records
    let mut b := pushBe32 (pushBe32 (pushBe32 (pushBe32 ByteArray.empty 0x74746366) 0x00010000) 1) dir
    b := pushBe16 (pushBe16 (pushBe16 (pushBe16 (pushBe32 b 0x00010000) records) 256) 8) (records * 16 - 256 * 16)
    for k in [0:records] do
      b := pushBe32 (pushBe32 (pushBe32 (pushBe32 b (0x61610000 + k)) 0) tables) region
    for _ in [0:region] do
      b := b.push 0x41
    return b
  t "a directory naming one region again and again is refused"
    (Font.collectionCount repeated == some 1 &&
      Font.collectionMember repeated 0 matches .error _)
  -- An Apple `true` face reads as the TrueType outlines it names.
  let appleTagged := packCollection #[regular]
  let trueMember := pushBe32 (appleTagged.extract 0 (Ink.u32 appleTagged 12)) 0x74727565 ++
    appleTagged.extract (Ink.u32 appleTagged 12 + 4) appleTagged.size
  t "a face tagged true reads as its TrueType outlines"
    (match Font.collectionMember trueMember 0 with
      | .ok m => Ink.u32 m 0 == 0x00010000 && (Font.parse m).toOption.isSome
      | .error _ => false)
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
