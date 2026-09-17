import LeanTex

open LeanTex.Core LeanTex.Cli

structure Ui where
  cfg : Config
  color : Bool
  errStream : IO.FS.Stream
  outStream : IO.FS.Stream

def Ui.mk' (cfg : Config) : IO Ui := do
  let errStream ← IO.getStderr
  let color ← match cfg.color with
    | .always => pure true
    | .never => pure false
    | .auto => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      let tty ← errStream.isTty
      pure (!noColor && tty)
  return ⟨cfg, color, errStream, ← IO.getStdout⟩

def Ui.diag (ui : Ui) (d : Diag) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDiag d)
  else if d.severity != .note || ui.cfg.verbosity ≥ 1 then
    ui.errStream.putStrLn (Render.human ui.color d)

/-- One phase's diagnostics resolved against the document's acceptance
(`\allow` and `--best-effort`) and printed. Returns the codes that fired,
the codes whose errors were accepted, and the error count after
acceptance. -/
def Ui.resolve (ui : Ui) (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) : IO (Array String × Array String × Nat) := do
  let mut fired : Array String := #[]
  let mut accepted : Array String := #[]
  let mut errors := 0
  for d0 in ds do
    let (d, acc) := Diag.accept allowed allowAll d0
    fired := fired.push d.code
    if acc then accepted := accepted.push d.code
    if d.severity == .error then errors := errors + 1
    ui.diag d
  return (fired, accepted, errors)

/-- Codes with their multiplicities, first appearance first. -/
def tally (xs : Array String) : List (String × Nat) := Id.run do
  let mut out : Array (String × Nat) := #[]
  for x in xs do
    match out.findIdx? (·.1 == x) with
    | some i => out := out.set! i (x, out[i]!.2 + 1)
    | none => out := out.push (x, 1)
  return out.toList

/-- Acceptance is visible, never ambient: whenever any loss was accepted,
the line prints — under `-q` too, because an accepted error is exactly the
thing quiet mode must not hide. -/
def Ui.accepted (ui : Ui) (accepted : Array String) : IO Unit := do
  if accepted.isEmpty then return
  let counts := tally accepted
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainAccepted counts)
  else
    ui.errStream.putStrLn (Render.humanAccepted ui.color counts)

def Ui.phase (ui : Ui) (name detail : String) (ms : Nat) : IO Unit := do
  if ui.cfg.verbosity ≥ 1 then
    if ui.cfg.porcelain then
      ui.outStream.putStrLn (Render.porcelainPhase name detail ms)
    else
      ui.errStream.putStrLn s!"{name}: {detail} ({ms} ms)"

def Ui.summary (ui : Ui) (file : String) (errors ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainSummary file (errors == 0) errors ms)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanSummary ui.color file errors ms)

def Ui.done (ui : Ui) (file output : String) (pages ms : Nat) (notes : Nat := 0) :
    IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDone file output pages ms)
  else if !ui.cfg.quiet then
    let shown := if ui.cfg.verbosity ≥ 1 then 0 else notes
    ui.errStream.putStrLn (Render.humanDone ui.color file output pages ms shown)

/-- Every slot and variant mapped to one face: the shape of a single-font set. -/
def singleFaceIndex : Array ((Nat × Bool × Bool) × Nat) :=
  ((List.range 3).flatMap fun slot =>
    [((slot, false, false), 0), ((slot, true, false), 0),
     ((slot, false, true), 0), ((slot, true, true), 0)]).toArray

/-- `LEANTEX_FONT` (a path) overrides the default face for a document that
declares no `\fonts`: one face serves every slot and variant, no scan. -/
def loadOverride (path : String) : IO (Except Diag (Font.Font × String)) := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    match Font.parse data with
    | .ok f => return .ok (f, path)
    | .error e => return .error (DriverDiag.envFontUnusable path e)
  else
    return .error (DriverDiag.envFontMissing path)

/-- TeX Live's font roots, asked of kpsewhich when it is installed, so
`--font-dir` is almost never needed. `--show-path` returns the expanded list.
Two process spawns cost ~120 ms -- measured, not the ~10 ms first assumed --
so the answer is remembered beside the font cache, keyed by the kpsewhich
binary's own mtime: a TeX Live upgrade replaces it and the roots are asked
again. -/
def texFontDirs : IO (List String) := do
  let query (ext : String) : IO (List String) := do
    try
      let out ← IO.Process.output { cmd := "kpsewhich", args := #["--show-path=" ++ ext] }
      if out.exitCode != 0 then return []
      return (out.stdout.trimAscii.toString.splitOn ":").filterMap fun p =>
        let p := if p.startsWith "!!" then (p.drop 2).toString else p
        let p := String.ofList (p.toList.reverse.dropWhile (· == '/')).reverse
        if p.startsWith "/" then some p else none
    catch _ => return []
  let cache ← FontDb.cacheDir
  let stamp ← do
    let which ← try IO.Process.output { cmd := "sh", args := #["-c", "command -v kpsewhich"] }
      catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
    if which.exitCode != 0 then return []
    let bin := which.stdout.trimAscii.toString
    match ← (System.FilePath.mk bin).metadata.toBaseIO with
    | .ok md => pure s!"{bin} {md.modified.sec}"
    | .error _ => pure bin
  let memo := cache.map (· / "texroots.txt")
  if let some m := memo then
    if let .ok text ← IO.FS.readFile m |>.toBaseIO then
      match text.splitOn "\n" with
      | first :: roots => if first == stamp then return roots.filter (!·.isEmpty)
      | _ => pure ()
  let roots := ((← query ".otf") ++ (← query ".ttf")).eraseDups
  if let some m := memo then
    try
      if let some parent := m.parent then IO.FS.createDirAll parent
      IO.FS.writeFile m (String.intercalate "\n" (stamp :: roots) ++ "\n")
    catch _ => pure ()
  return roots

/-- The scan produced nothing usable at all. -/
def noFontDiag : Diag := DriverDiag.noFont

/-- Every face a document can reach: the three family slots crossed with the
four bold/italic variants, loaded once and deduplicated by path. Faces the
document never uses are still loaded but not embedded — `usedGlyphs` decides
what reaches the file. A document with no `\fonts` is served by the same
mechanism: `FontDb.defaultFamily` picks a family from the scan and it fills
the body slot, so the default exists wherever any font does, by construction.
A `\fonts{ dir = ... }` is searched first, resolved against the document's own
directory like `\input`: a document that ships its fonts renders the same on
every host, whatever else is installed.

Per-glyph fallback is precomputed here, against the document's own scalars
(`Layout.docScalars`): a scalar some declared face covers maps to the first
covering face in declaration order, and one no declared face covers goes to
`FontDb.fallbackPicks`, whose face is loaded at the end of the set. Layout
consults the map only on a missing glyph. The `LEANTEX_FONT` override is a
single face with no scan behind it, so it gets no fallback. -/
def buildFontSet (ui : Ui) (file : String) (doc : Ir.Doc) :
    IO (Except Diag (Font.FontSet × Array Diag × String)) := do
  let spec := doc.fonts
  let bare := spec.body.isNone && spec.sans.isNone && spec.mono.isNone
    && spec.math.isNone
  if bare then
    if let some path ← IO.getEnv "LEANTEX_FONT" then
      match ← loadOverride path with
      | .error d => return .error d
      | .ok (f, path) =>
        return .ok ({ fonts := #[f], index := singleFaceIndex }, #[], path)
  let mut diags : Array Diag := #[]
  let mut docDirs : List String := []
  for d in spec.dirs do
    let d := if d.endsWith "/" && d.length > 1 then (d.dropEnd 1).toString else d
    let p := System.FilePath.mk d
    let p := if p.isAbsolute then p else ((System.FilePath.mk file).parent.getD ".") / p
    if ← p.isDir then
      docDirs := docDirs ++ [p.toString]
    else
      diags := diags.push (DriverDiag.fontsDirMissing d p.toString)
  let t ← IO.monoMsNow
  let faces ← FontDb.scanRoots
    (docDirs ++ (← FontDb.systemRoots (ui.cfg.fontDirs.toList ++ (← texFontDirs))))
  ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  let spec ← if bare then
      match FontDb.defaultFamily faces with
      | some fam => pure { spec with body := some fam }
      | none => return .error noFontDiag
    else pure spec
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Bool × Bool) × Nat) := #[]
  let mut missing : Array String := #[]
  let slots : List (Nat × Option String) :=
    [(0, spec.body), (1, spec.sans), (2, spec.mono)]
  -- A slot the document did not name falls back to the body family, and the
  -- body's declared per-variant faces come with it.
  let resolveName (slot : Nat) : Option String :=
    match slot with
    | 0 => spec.body
    | 1 => spec.sans.orElse fun _ => spec.body
    | _ => spec.mono.orElse fun _ => spec.body
  let declaredFace (slot : Nat) (bold italic : Bool) : Option String :=
    let effective := match slot with
      | 1 => if spec.sans.isSome then 1 else 0
      | 2 => if spec.mono.isSome then 2 else 0
      | _ => 0
    spec.faceFor effective bold italic
  for (slot, _) in slots do
    let some family := resolveName slot | continue
    for (bold, italic) in [(false, false), (true, false), (false, true), (true, true)] do
      match FontDb.resolveVariant faces family (declaredFace slot bold italic)
          { bold := bold, italic := italic } with
      | none =>
        unless missing.contains family do
          missing := missing.push family
          -- A host with TeX Live installed has a thousand families; listing
          -- them all is not help. Name the ones that look like what was asked
          -- for, and how to see the rest.
          let all := FontDb.families faces
          diags := diags.push (DriverDiag.familyMissing family
            (FontDb.nearest all family).toList all.size)
      | some (face, warning) =>
        if let some msg := warning then
          -- Slots share families, so the same substitution surfaces repeatedly.
          unless diags.any (·.message == msg) do
            diags := diags.push (Diag.of .W0006 msg)
        match paths.findIdx? (· == face.path) with
        | some i => index := index.push ((slot, bold, italic), i)
        | none =>
          let data ← IO.FS.readBinFile face.path
          match Font.parse data with
          | .error e =>
            diags := diags.push (DriverDiag.fontFileUnusable face.path e)
          | .ok f =>
            index := index.push ((slot, bold, italic), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  -- The math face: resolved like any named family, and installed only when
  -- it carries an OpenType MATH table — constants are never invented, so a
  -- face without the table earns a diagnostic naming it and math is set as
  -- source text (PLAN, M6 design decision 1).
  let mut mathIdx : Option Nat := none
  if let some family := spec.math then
    match FontDb.resolveVariant faces family none {} with
    | none =>
      unless missing.contains family do
        missing := missing.push family
        let all := FontDb.families faces
        diags := diags.push (DriverDiag.familyMissing family
          (FontDb.nearest all family).toList all.size)
    | some (face, _) =>
      let loaded ← match paths.findIdx? (· == face.path) with
        | some i => pure (some i)
        | none =>
          let data ← IO.FS.readBinFile face.path
          match Font.parse data with
          | .error e =>
            diags := diags.push (DriverDiag.fontFileUnusable face.path e)
            pure none
          | .ok f =>
            fonts := fonts.push f
            paths := paths.push face.path
            pure (some (fonts.size - 1))
      if let some i := loaded then
        if (fonts[i]!).math.isSome then
          mathIdx := some i
        else
          diags := diags.push (DriverDiag.mathFaceNoTable (fonts[i]!).family face.path)
  if fonts.isEmpty then
    -- Every named family failed and `diags` carries the errors; the caller
    -- stops on them, but nothing downstream may ever see an empty set.
    match FontDb.defaultFamily faces |>.bind (FontDb.resolve faces · {}) with
    | none => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
    | some (face, _) =>
      let data ← IO.FS.readBinFile face.path
      match Font.parse data with
      | .error _ => return .error ((diags.find? (·.severity == .error)).getD noFontDiag)
      | .ok f =>
        return .ok ({ fonts := #[f], index := singleFaceIndex }, diags, face.path)
  -- Per-glyph fallback: map every scalar the document uses to the first
  -- declared face covering it; scalars none covers go to the scan.
  let mut fallback : Array (Char × Nat) := #[]
  let mut uncovered : Array Char := #[]
  for c in Layout.docScalars doc do
    match (Array.range fonts.size).find? (fun i => ((fonts[i]!).gid c).isSome) with
    | some i => fallback := fallback.push (c, i)
    | none => uncovered := uncovered.push c
  unless uncovered.isEmpty do
    for (c, path) in ← FontDb.fallbackPicks faces uncovered do
      match paths.findIdx? (· == path) with
      | some i => fallback := fallback.push (c, i)
      | none =>
        let data ← IO.FS.readBinFile path
        match Font.parse data with
        | .error _ => pure ()  -- undecodable candidate; the scalar stays dropped
        | .ok f =>
          fallback := fallback.push (c, fonts.size)
          fonts := fonts.push f
          paths := paths.push path
  let set : Font.FontSet := {
    fonts := fonts
    index := index
    fallback := fallback
    math := mathIdx }
  return .ok (set, diags, String.intercalate ", " paths.toList)

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

/-- The image request an elaborated document states (`Ir.imageRefs`),
fulfilled: each path resolves against the document's own directory, like
`\input`, and decodes in the pure core. A file that is missing or refuses
to decode keeps its entry with no payload — layout places a placeholder box
of the requested size, so the document still compiles and the diagnostic
here says why the figure is a box. -/
def loadImages (file : String) (doc : Ir.Doc) : IO (Image.Store × Array Diag) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut entries : Array Image.Loaded := #[]
  let mut diags : Array Diag := #[]
  for src in Ir.imageRefs doc do
    -- The name as written, then graphicx's extension resolution: a deck
    -- says `figures/plot` and means the `figures/plot.png` beside it.
    let mut hit : Option (String × System.FilePath) := none
    for cand in Image.sourceCandidates src do
      let p := if (System.FilePath.mk cand).isAbsolute then System.FilePath.mk cand
        else dir / cand
      if ← p.pathExists then
        hit := some (cand, p)
        break
    let bytes? ← do
      match hit with
      | some (_, p) =>
        try pure (some (← IO.FS.readBinFile p))
        catch e =>
          diags := diags.push (DriverDiag.imageUnreadable src (toString e))
          pure none
      | none =>
        let p := if (System.FilePath.mk src).isAbsolute then System.FilePath.mk src
          else dir / src
        diags := diags.push (DriverDiag.imageMissing src p.toString)
        pure none
    let href := match hit with
      | some (cand, _) => if cand == src then "" else cand
      | none => ""
    match bytes? with
    | none => entries := entries.push { src, href }
    | some bytes =>
      match Image.decode bytes with
      | .ok info => entries := entries.push { src, href, info := some info }
      | .error e =>
        entries := entries.push { src, href }
        diags := diags.push (DriverDiag.imageUndecodable src (toString e))
  return ({ entries := entries }, diags)

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

/-! `\input{name}` splices a file into the parsed tree. Reading a file is an
effect, so it happens here in the driver rather than in the core; the core
sees one tree, as if the document had been written in one file. One pass
splices each `\input` without descending into what it read; nested inputs
resolve on the next pass, and eight passes bound the depth the way TeX's input
stack does. Every pass is a structural walk, so nothing here is partial. -/

def readInput (dir : System.FilePath) (name : String) (pos : Pos) :
    IO (Array Parse.Raw × Array Diag) := do
  let name := if name.endsWith ".tex" then name else name ++ ".tex"
  let path := dir / name
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    let (toks, lexDs) := Lex.lex path.toString text
    let (sub, parseDs) := Parse.parse path.toString toks
    -- Wrapped, not spliced flat: a diagnostic inside the file must name the
    -- file, and the wrapper is what carries that name to the elaborator.
    return (#[.env (Parse.inputEnv path.toString) sub pos], lexDs ++ parseDs)
  else
    let d := DriverDiag.inputMissing name (some ⟨dir.toString, pos⟩)
    return (#[], #[d])

mutual

/-- One splicing pass. `out` accumulates so the walk is linear: prepending to
the recursive result would copy it at every element. -/
def spliceList (dir : System.FilePath) (out : Array Parse.Raw) (ds : Array Diag) (hit : Bool) :
    List Parse.Raw → IO (Array Parse.Raw × Array Diag × Bool)
  | [] => pure (out, ds, hit)
  | .ctrl "input" pos :: .group nameRaws _ :: rest
  | .ctrl "include" pos :: .group nameRaws _ :: rest => do
    let (sub, ds') ← readInput dir (Parse.rawSrc nameRaws) pos
    spliceList dir (out ++ sub) (ds ++ ds') true rest
  | r :: rest => do
    let (r', ds', hit') ← spliceOne dir r
    spliceList dir (out.push r') (ds ++ ds') (hit || hit') rest

def spliceOne (dir : System.FilePath) : Parse.Raw → IO (Parse.Raw × Array Diag × Bool)
  | .env n body p => do
    let (body', ds, hit) ← spliceList dir #[] #[] false body.toList
    return (.env n body' p, ds, hit)
  | .group body p => do
    let (body', ds, hit) ← spliceList dir #[] #[] false body.toList
    return (.group body' p, ds, hit)
  | r => pure (r, #[], false)

end

def expandInputs (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut raws := raws
  let mut diags : Array Diag := #[]
  for _ in [0:8] do
    let (raws', ds, hit) ← spliceList dir #[] #[] false raws.toList
    raws := raws'
    diags := diags ++ ds
    unless hit do return (raws, diags)
  let (_, _, still) ← spliceList dir #[] #[] false raws.toList
  if still then
    diags := diags.push DriverDiag.inputTooDeep
  return (raws, diags)

/-- Read and decode the file, then run the front end, reporting phases.
Returns the document, all diagnostics, and whether reading itself failed. -/
def frontend (ui : Ui) (file : String) : IO (Option (Ir.Doc × Array Diag)) := do
  let t0 ← IO.monoMsNow
  let bytes ← try
    pure (some (← IO.FS.readBinFile file))
  catch e =>
    ui.diag (DriverDiag.unreadableInput file (toString e))
    pure none
  let some bytes := bytes | return none
  ui.phase "read" s!"{bytes.size} bytes" (← since t0)
  let t ← IO.monoMsNow
  match LeanTex.Core.Utf8.validate bytes with
  | some err =>
    ui.diag (err.toDiag file)
    return none
  | none =>
    ui.phase "utf8" "valid" (← since t)
    let input := String.fromUTF8! bytes
    let t ← IO.monoMsNow
    let (toks, lexDiags) := Lex.lex file input
    ui.phase "lex" s!"{toks.size} tokens" (← since t)
    let t ← IO.monoMsNow
    let (raws, parseDiags) := Parse.parse file toks
    ui.phase "parse" s!"{raws.size} top-level nodes" (← since t)
    let t ← IO.monoMsNow
    let (raws, inputDiags) ← expandInputs file raws
    let (doc, elabDiags) := Elab.runRaws file raws (lexDiags ++ parseDiags ++ inputDiags)
    ui.phase "elab" s!"{doc.body.size} blocks" (← since t)
    return some (doc, elabDiags)

def build (ui : Ui) (file : String) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  match ← frontend ui file with
  | none =>
    ui.summary file 1 (← since t0)
    return 1
  | some (doc, diags) =>
    let allowAll := ui.cfg.bestEffort
    let mut fired : Array String := #[]
    let mut accepted : Array String := #[]
    let (f0, a0, errors) ← ui.resolve doc.allow allowAll diags
    fired := fired ++ f0
    accepted := accepted ++ a0
    if errors > 0 then
      ui.accepted accepted
      ui.summary file errors (← since t0)
      return 1
    let t ← IO.monoMsNow
    match ← buildFontSet ui file doc with
    | .error d =>
      -- No usable font set exists at all: nothing downstream can run, so
      -- this stays fatal whatever the document accepts.
      ui.diag d
      ui.summary file 1 (← since t0)
      return 1
    | .ok (fs, fontDiags, paths) =>
      let (f1, a1, fontErrors) ← ui.resolve doc.allow allowAll fontDiags
      fired := fired ++ f1
      accepted := accepted ++ a1
      if fontErrors > 0 then
        ui.accepted accepted
        ui.summary file fontErrors (← since t0)
        return 1
      let names := ", ".intercalate (fs.fonts.toList.map (·.psName))
      ui.phase "font" s!"{names} ({paths})" (← since t)
      let t ← IO.monoMsNow
      let (imgs, imgDiags) ← loadImages file doc
      let (f2, a2, imgErrors) ← ui.resolve doc.allow allowAll imgDiags
      fired := fired ++ f2
      accepted := accepted ++ a2
      unless imgs.entries.isEmpty do
        ui.phase "images" s!"{imgs.entries.size} files" (← since t)
      let t ← IO.monoMsNow
      let pats := Hyphen.load
      ui.phase "hyphen" s!"{pats.map.size} patterns" (← since t)
      let t ← IO.monoMsNow
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs (some pats) doc imgs
      let (f3, a3, layoutErrors) ← ui.resolve doc.allow allowAll out.diags
      fired := fired ++ f3
      accepted := accepted ++ a3
      ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      -- An unaccepted error anywhere before the writers means no output: a
      -- failing document must not produce one (the assertion contract, held
      -- for every dropped loss).
      if imgErrors + layoutErrors > 0 then
        ui.accepted accepted
        ui.summary file (imgErrors + layoutErrors) (← since t0)
        return 1
      -- Assertions judge what shipped, so they run after layout and before
      -- the file is written: a failing document must not produce output.
      -- The page walk is skipped when nothing asserts: measuring ink on
      -- every build would tax the common path for the rare check.
      let shipped := if doc.asserts.isEmpty then
          { pages := out.pages.size, fontsEmbedded := true : Check.Shipped }
        else Check.Shipped.ofOut geom fs out (fontsEmbedded := true)
      let failures := Check.all shipped doc.asserts
      unless doc.asserts.isEmpty do
        ui.phase "assert"
          s!"{doc.asserts.size - failures.size}/{doc.asserts.size} held" (← since t)
      if !failures.isEmpty then
        for d in failures do
          ui.diag d
        ui.accepted accepted
        ui.summary file failures.size (← since t0)
        return 2
      let mut written : Array String := #[]
      let emit := ui.cfg.effectiveEmit doc.output.formats
      let css := ui.cfg.effectiveCss doc.output.css
      let outIsDir ← match ui.cfg.output with
        | some o => (System.FilePath.mk o).isDir
        | none => pure false
      if let some o := ui.cfg.output then
        if o.endsWith "/" && !outIsDir then
          IO.FS.createDirAll o
      if emit.contains .html then
        let t ← IO.monoMsNow
        let cssMode := match css with
          | .own => HtmlDoc.CssMode.own
          | .bulma => HtmlDoc.CssMode.bulma
          | .none => HtmlDoc.CssMode.none
        let hcfg : HtmlDoc.Config := {
          css := cssMode
          mathBoundary := ui.cfg.mathBoundary
          imgs := imgs
          -- The markdown twin, when one is being written beside the page,
          -- is linked from the head as the alternate representation.
          mdHref := if emit.contains .md then
              (System.FilePath.mk (outPath ui.cfg.output outIsDir file .md)).fileName
            else none
        }
        let (html, hdiags) := HtmlDoc.emit hcfg doc
        let (f4, a4, _) ← ui.resolve doc.allow allowAll hdiags
        fired := fired ++ f4
        accepted := accepted ++ a4
        let htmlPath := outPath ui.cfg.output outIsDir file .html
        IO.FS.writeFile htmlPath html
        written := written.push htmlPath
        ui.phase "html" s!"{html.utf8ByteSize} bytes" (← since t)
      if emit.contains .md then
        let t ← IO.monoMsNow
        let md := MarkdownDoc.emit doc
        let mdPath := outPath ui.cfg.output outIsDir file .md
        IO.FS.writeFile mdPath md
        written := written.push mdPath
        ui.phase "markdown" s!"{md.utf8ByteSize} bytes" (← since t)
      if emit.contains .pdf then
        let t ← IO.monoMsNow
        let pdf := Pdf.write geom fs out.pages doc.info imgs
        let pdfPath := outPath ui.cfg.output outIsDir file .pdf
        IO.FS.writeBinFile pdfPath pdf
        written := written.push pdfPath
        ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
      -- The hatch's other teeth: an `\allow` that never fired is stale
      -- acceptance and warns; what was accepted always prints.
      for c in Diag.unfired doc.allow fired do
        ui.diag (DriverDiag.allowUnfired c)
      ui.accepted accepted
      let notes := diags.foldl (fun n d => if d.severity == .note then n + 1 else n) 0
      ui.done file (String.intercalate ", " written.toList) out.pages.size (← since t0) notes
      return 0

def dump (ui : Ui) (file : String) : IO UInt32 := do
  match ← frontend ui file with
  | none => return 1
  | some (doc, diags) =>
    IO.print (Ir.dump doc diags)
    return (if countErrors diags > 0 then 1 else 0)

/-- Insert `-` at each hyphenation point: the `hyphenate` command's output
format, and what the lualatex differential harness compares. -/
def showHyphens (pats : Hyphen.Patterns) (word : String) : String := Id.run do
  let breaks := Hyphen.hyphenate pats word
  let mut out := ""
  for (c, i) in word.toList.zipIdx do
    if i > 0 && breaks.contains i then
      out := out.push '-'
    out := out.push c
  return out

def hyphenate (ui : Ui) (words : List String) (file : Option String) : IO UInt32 := do
  let mut all := words
  if let some path := file then
    let contents ← try
      pure (some (← IO.FS.readFile path))
    catch e =>
      ui.diag (Diag.of .E0001 s!"cannot read '{path}': {e}")
      pure none
    let some contents := contents | return 1
    all := all ++ (contents.splitOn "\n").filterMap fun line =>
      let w := line.trimAscii.toString
      if w.isEmpty then none else some w
  let pats := Hyphen.load
  for w in all do
    IO.println (showHyphens pats w)
  return 0

/-- Rebuild whenever the source changes, by polling its mtime every 200 ms —
no inotify dependency. Each rebuild prints the usual summary line. -/
def watch (cfg : Config) (file : String) : IO UInt32 := do
  let mtime : IO (Option IO.FS.SystemTime) := do
    try
      pure (some (← (System.FilePath.mk file).metadata).modified)
    catch _ =>
      pure none
  let mut last ← mtime
  discard <| build (← Ui.mk' cfg) file
  repeat
    IO.sleep 200
    let m ← mtime
    if m != last && m.isSome then
      last := m
      discard <| build (← Ui.mk' cfg) file
  return 0

def main (argv : List String) : IO UInt32 := do
  match parse argv with
  | .error msg =>
    let stderr ← IO.getStderr
    stderr.putStrLn s!"leantex: {msg}"
    stderr.putStrLn "try 'leantex --help'"
    return 3
  | .ok cfg =>
    match cfg.cmd with
    | .help =>
      IO.println helpText
      return 0
    | .version =>
      IO.println s!"leantex {LeanTex.version}"
      return 0
    | .build file =>
      if file.endsWith ".md" then
        let stderr ← IO.getStderr
        stderr.putStrLn
          "leantex: markdown input is not implemented yet; write the document as .tex"
        return 3
      if let some o := cfg.output then
        unless o.endsWith "/" || (← (System.FilePath.mk o).isDir) ||
            (emitOfPath o).isSome do
          let stderr ← IO.getStderr
          stderr.putStrLn
            s!"leantex: cannot tell the output format of '{o}'; name it *.pdf or *.html, or pass a directory"
          return 3
      if cfg.watch then
        watch cfg file
      else
        build (← Ui.mk' cfg) file
    | .dump file =>
      dump (← Ui.mk' cfg) file
    | .hyphenate words file =>
      hyphenate (← Ui.mk' cfg) words file
    | .fonts =>
      -- The answer to "what may \\fonts name here": one family per line on
      -- stdout, so it pipes into grep.
      let faces ← FontDb.scan (cfg.fontDirs.toList ++ (← texFontDirs))
      for f in FontDb.families faces do
        IO.println f
      return 0
    | .themes =>
      -- The answer to "what may \\theme name here": one bundle per line.
      for th in Theme.builtin do
        IO.println th.name
      return 0
