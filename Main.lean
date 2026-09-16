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

def fontCandidates : List String :=
  ["/usr/share/fonts/dejavu/DejaVuSans.ttf",
   "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
   "/usr/share/fonts/TTF/DejaVuSans.ttf"]

/-- Load the default face: `LEANTEX_FONT` override, then known paths. Used
when the document declares no `\fonts`. -/
def loadFont : IO (Except Diag (String × Font.Font)) := do
  let tryPath (path : String) : IO (Option (String × Font.Font)) := do
    if ← System.FilePath.pathExists path then
      let data ← IO.FS.readBinFile path
      match Font.parse data with
      | .ok f => return some (path, f)
      | .error _ => return none
    else
      return none
  match ← IO.getEnv "LEANTEX_FONT" with
  | some path =>
    if ← System.FilePath.pathExists path then
      let data ← IO.FS.readBinFile path
      match Font.parse data with
      | .ok f => return .ok (path, f)
      | .error e => return .error {
          severity := .error
          code := "E0402"
          message := s!"cannot use LEANTEX_FONT '{path}': {e}"
        }
    else
      return .error {
        severity := .error
        code := "E0402"
        message := s!"LEANTEX_FONT '{path}' does not exist"
      }
  | none =>
    for p in fontCandidates do
      if let some r ← tryPath p then
        return .ok r
    return .error {
      severity := .error
      code := "E0401"
      message := "no usable font found"
      help := some s!"searched: {String.intercalate ", " fontCandidates}; set LEANTEX_FONT"
    }

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

/-- Every face a document can reach: the three family slots crossed with the
four bold/italic variants, loaded once and deduplicated by path. Faces the
document never uses are still loaded but not embedded — `usedGlyphs` decides
what reaches the file. -/
def buildFontSet (ui : Ui) (spec : Ir.FontSpec) :
    IO (Except Diag (Font.FontSet × Array Diag × String)) := do
  if spec.body.isNone && spec.sans.isNone && spec.mono.isNone then
    -- No \fonts: one default face, no directory scan.
    match ← loadFont with
    | .error d => return .error d
    | .ok (path, f) =>
      let index := (List.range 3).flatMap fun slot =>
        [((slot, false, false), 0), ((slot, true, false), 0),
         ((slot, false, true), 0), ((slot, true, true), 0)]
      return .ok ({ fonts := #[f], index := index.toArray }, #[], path)
  let t ← IO.monoMsNow
  let faces ← FontDb.scan (ui.cfg.fontDirs.toList ++ (← texFontDirs))
  ui.phase "fontdb" s!"{faces.size} faces" ((← IO.monoMsNow) - t)
  let mut diags : Array Diag := #[]
  let mut fonts : Array Font.Font := #[]
  let mut paths : Array String := #[]
  let mut index : Array ((Nat × Bool × Bool) × Nat) := #[]
  let mut missing : Array String := #[]
  let slots : List (Nat × Option String) :=
    [(0, spec.body), (1, spec.sans), (2, spec.mono)]
  -- A slot the document did not name falls back to the body family.
  let resolveName (slot : Nat) : Option String :=
    match slot with
    | 0 => spec.body
    | 1 => spec.sans.orElse fun _ => spec.body
    | _ => spec.mono.orElse fun _ => spec.body
  for (slot, _) in slots do
    let some family := resolveName slot | continue
    for (bold, italic) in [(false, false), (true, false), (false, true), (true, true)] do
      match FontDb.resolve faces family { bold := bold, italic := italic } with
      | none =>
        unless missing.contains family do
          missing := missing.push family
          diags := diags.push {
            severity := .error
            code := "E0403"
            message := s!"no installed font family named '{family}'"
            help := some s!"installed: {String.intercalate ", " (FontDb.families faces).toList}"
          }
      | some (face, satisfied) =>
        unless satisfied do
          let want :=
            if bold && italic then "bold italic" else if bold then "bold" else "italic"
          let msg := s!"'{family}' has no {want} face; using {face.subfamily.quote}"
          -- Slots share families, so the same substitution surfaces repeatedly.
          unless diags.any (·.message == msg) do
            diags := diags.push {
              severity := .warning
              code := "W0006"
              message := msg
            }
        match paths.findIdx? (· == face.path) with
        | some i => index := index.push ((slot, bold, italic), i)
        | none =>
          let data ← IO.FS.readBinFile face.path
          match Font.parse data with
          | .error e =>
            diags := diags.push {
              severity := .error
              code := "E0404"
              message := s!"cannot use '{face.path}': {e}"
            }
          | .ok f =>
            index := index.push ((slot, bold, italic), fonts.size)
            fonts := fonts.push f
            paths := paths.push face.path
  if fonts.isEmpty then
    match ← loadFont with
    | .error d => return .error d
    | .ok (path, f) =>
      let idx := (List.range 3).flatMap fun slot =>
        [((slot, false, false), 0), ((slot, true, false), 0),
         ((slot, false, true), 0), ((slot, true, true), 0)]
      return .ok ({ fonts := #[f], index := idx.toArray }, diags, path)
  return .ok ({ fonts := fonts, index := index }, diags,
    String.intercalate ", " paths.toList)

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

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
    return (sub, lexDs ++ parseDs)
  else
    let d : Diag := {
      severity := .warning
      code := "W0501"
      message := s!"\\input file not found: '{name}'; skipped"
      span := some ⟨dir.toString, pos⟩ }
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
    diags := diags.push {
      severity := .error
      code := "E0501"
      message := "\\input nesting deeper than 8 files; is a file including itself?" }
  return (raws, diags)

/-- Read and decode the file, then run the front end, reporting phases.
Returns the document, all diagnostics, and whether reading itself failed. -/
def frontend (ui : Ui) (file : String) : IO (Option (Ir.Doc × Array Diag)) := do
  let t0 ← IO.monoMsNow
  let bytes ← try
    pure (some (← IO.FS.readBinFile file))
  catch e =>
    ui.diag { severity := .error, code := "E0001", message := s!"cannot read '{file}': {e}" }
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
    for d in diags do
      ui.diag d
    let errors := countErrors diags
    if errors > 0 then
      ui.summary file errors (← since t0)
      return 1
    let t ← IO.monoMsNow
    match ← buildFontSet ui doc.fonts with
    | .error d =>
      ui.diag d
      ui.summary file 1 (← since t0)
      return 1
    | .ok (fs, fontDiags, paths) =>
      for d in fontDiags do
        ui.diag d
      if fontDiags.any (·.severity == .error) then
        ui.summary file (countErrors fontDiags) (← since t0)
        return 1
      let names := ", ".intercalate (fs.fonts.toList.map (·.psName))
      ui.phase "font" s!"{names} ({paths})" (← since t)
      let t ← IO.monoMsNow
      let pats := Hyphen.load
      ui.phase "hyphen" s!"{pats.map.size} patterns" (← since t)
      let t ← IO.monoMsNow
      let geom := Layout.Geom.ofPage doc.page
      let out := Layout.run geom fs (some pats) doc
      for d in out.diags do
        ui.diag d
      ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      -- Assertions judge what shipped, so they run after layout and before
      -- the file is written: a failing document must not produce output.
      let shipped := Check.Shipped.ofOut out (fontsEmbedded := true)
      let failures := Check.all shipped doc.asserts
      unless doc.asserts.isEmpty do
        ui.phase "assert"
          s!"{doc.asserts.size - failures.size}/{doc.asserts.size} held" (← since t)
      if !failures.isEmpty then
        for d in failures do
          ui.diag d
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
        }
        let (html, hdiags) := HtmlDoc.emit hcfg doc
        for d in hdiags do
          ui.diag d
        let htmlPath := outPath ui.cfg.output outIsDir file .html
        IO.FS.writeFile htmlPath html
        written := written.push htmlPath
        ui.phase "html" s!"{html.utf8ByteSize} bytes" (← since t)
      if emit.contains .pdf then
        let t ← IO.monoMsNow
        let pdf := Pdf.write geom fs out.pages doc.info
        let pdfPath := outPath ui.cfg.output outIsDir file .pdf
        IO.FS.writeBinFile pdfPath pdf
        written := written.push pdfPath
        ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
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
      ui.diag { severity := .error, code := "E0001", message := s!"cannot read '{path}': {e}" }
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
          "leantex: markdown input is reserved for the second surface; not implemented yet (PLAN.md)"
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
