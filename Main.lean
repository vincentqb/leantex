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
  else
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

def Ui.done (ui : Ui) (file output : String) (pages ms : Nat) : IO Unit := do
  if ui.cfg.porcelain then
    ui.outStream.putStrLn (Render.porcelainDone file output pages ms)
  else if !ui.cfg.quiet then
    ui.errStream.putStrLn (Render.humanDone ui.color file output pages ms)

def fontCandidates : List String :=
  ["/usr/share/fonts/dejavu/DejaVuSans.ttf",
   "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
   "/usr/share/fonts/TTF/DejaVuSans.ttf"]

/-- Resolve the default font: `LEANTEX_FONT` override, then known paths.
Font *selection* in the document arrives with M3 `\fonts`. -/
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

def since (t0 : Nat) : IO Nat := do
  return (← IO.monoMsNow) - t0

def countErrors (diags : Array Diag) : Nat :=
  diags.foldl (fun n d => if d.severity == .error then n + 1 else n) 0

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
    let (doc, elabDiags) := ((Elab.elabDoc file raws).run {})
    ui.phase "elab" s!"{doc.body.size} blocks" (← since t)
    return some (doc, lexDiags ++ parseDiags ++ elabDiags.diags)

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
    match ← loadFont with
    | .error d =>
      ui.diag d
      ui.summary file 1 (← since t0)
      return 1
    | .ok (path, font) =>
      ui.phase "font" s!"{font.psName} ({path})" (← since t)
      let t ← IO.monoMsNow
      let pats := Hyphen.load
      ui.phase "hyphen" s!"{pats.map.size} patterns" (← since t)
      let t ← IO.monoMsNow
      let geom : Layout.Geom := {}
      let out := Layout.run geom font (some pats) doc
      for d in out.diags do
        ui.diag d
      ui.phase "layout" s!"{out.pages.size} pages" (← since t)
      let t ← IO.monoMsNow
      let pdf := Pdf.write geom font out.pages
      let outPath := (System.FilePath.mk file).withExtension "pdf" |>.toString
      IO.FS.writeBinFile outPath pdf
      ui.phase "pdf" s!"{pdf.size} bytes" (← since t)
      ui.done file outPath out.pages.size (← since t0)
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
      build (← Ui.mk' cfg) file
    | .dump file =>
      dump (← Ui.mk' cfg) file
    | .hyphenate words file =>
      hyphenate (← Ui.mk' cfg) words file
