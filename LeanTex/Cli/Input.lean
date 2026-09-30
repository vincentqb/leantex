import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Compat
import LeanTex.Core.MdDesugar
import LeanTex.Core.Utf8
import LeanTex.Core.Bib
import LeanTex.Core.BibStyle
import LeanTex.Core.Data
import LeanTex.Cli.DriverDiag

/-! The driver's file-splicing frontend: `\input`/`\include`, `\markdownInput`
and the local `.sty` read (`\usepackage{p}` with `p.sty` beside the document)
are one splice — each wraps a file's parsed text as its own input fragment — and
run to one fixpoint here. Reading a file is an effect, so it happens in
the driver rather than in the core; the core sees one tree, as if the
document had been written in one file. Lives beside the other Cli modules
rather than in Main so the fixpoint is testable: the three `\input`-parity
cases (a `\usepackage` inside an `\input`'ed preamble file, a
`\RequirePackage` inside a spliced `.sty`, an `\input` inside a `.sty`)
exist only across passes of this loop.

Every other file the *document* names is read here for the same reason:
the document's own bytes (`readSource`), the `.bib` its `\bibliography`
requests (`resolveBibliography`), the `.bib` its `\data` requests
(`resolveData`). Each is one decision — the file is there, or its absence
is a named loss — and each **returns** its diagnostics rather than
printing them, which is what lets a test run the decision instead of
restating it. A decision reachable only from the entry path in Main.lean
is a decision no test can witness: its code's witness then has to be a
hand-built value, and a value cannot tell you the driver stopped emitting
it. -/

namespace LeanTex.Cli.Input

open LeanTex.Core

/-- The first line of an `IO.Error`'s rendering. `IO.Error`'s own
`toString` appends a second `  file: <path>` line, and the path it repeats
is the one the message already names — so the second line says nothing new
and costs a newline inside a `Diag.message`, where one line per diagnostic
is what every reader, `Render.human`, and the registry golden's block
parse all assume. -/
private def reasonLine (s : String) : String :=
  (s.splitOn "\n").headD s

/-- The document's own bytes, or the diagnostic naming why they could not
be read (E0001). The read is the driver's first effect and its refusal is
the driver's first decision, so it is returned rather than printed. -/
def readSource (file : String) : IO (Except Diag ByteArray) := do
  match ← (IO.FS.readBinFile file).toBaseIO with
  | .ok bytes => return .ok bytes
  | .error e => return .error (DriverDiag.unreadableInput file (reasonLine (toString e)))

/-- Every included surface uses the document reader's UTF-8 and IO error
contract. The surface reader returns a fragment of the same AST; its bytes
are never converted to TeX source and parsed again. Filename normalization
precedes the surface's extension policy: LaTeX's file-name sanitizer removes
paired quotes and trims both ends when the name contains a dot, only the
start otherwise (expl3-code.tex; quotedInputFilenameChecks). -/
private def readFragment (dir : System.FilePath) (file name : String) (pos : Pos)
    (prefer : String → String) (command : String)
    (reader : String → String → Array Parse.Raw × Array Diag) :
    IO (Array Parse.Raw × Array Diag) := do
  -- Do not turn an unmatched quote into an accepted, unquoted filename.
  let name := if name.toList.count '"' % 2 == 0 then
      let unquoted := name.replace "\"" ""
      if unquoted.contains '.' then unquoted.trimAscii.toString
      else unquoted.trimAsciiStart.toString
    else name
  let preferred := prefer name
  let candidate := dir / preferred
  let path ← if ← candidate.pathExists then pure candidate else pure (dir / name)
  if ← path.pathExists then
    match ← readSource path.toString with
    | .error d => return (#[], #[d])
    | .ok bytes =>
      if let some err := Utf8.validate bytes then
        return (#[], #[err.toDiag path.toString])
      let (sub, ds) := reader path.toString (String.fromUTF8! bytes)
      -- The wrapper carries the source filename to the elaborator.
      return (#[.env (Parse.inputEnv path.toString) sub pos], ds)
  else
    -- The span names `file`, the file the `\input` sits in — the reader
    -- goes to that line to fix it, and a directory has no line 5.
    let d := DriverDiag.inputMissing preferred (some ⟨file, pos⟩) command
    return (#[], #[d])

def readInput (dir : System.FilePath) (file name : String) (pos : Pos) :
    IO (Array Parse.Raw × Array Diag) :=
  -- TeX's input scanner tries the default `.tex` suffix before the literal
  -- spelling, unless that spelling already ends in `.tex` (inputFileChecks).
  readFragment dir file name pos (fun name =>
    if name.endsWith ".tex" then name else name ++ ".tex")
    "input" fun path text =>
      let (toks, lexDs) := Lex.lex path text
      let (raws, parseDs) := Parse.parse path toks
      (raws, lexDs ++ parseDs)

/-- Consuming a command's optional argument leaves a suffix of its input.
This bound lets the ordinary structural splice walk read command signatures
without introducing a second depth limit. -/
private theorem drop_size_le (rs : List Parse.Raw) (n : Nat) :
    sizeOf (rs.drop n) ≤ sizeOf rs := by
  induction rs generalizing n with
  | nil => simp
  | cons r rs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.drop_succ_cons]
      have := ih n
      simp only [List.cons.sizeOf_spec]
      omega

mutual

/-- One splicing pass. `out` accumulates so the walk is linear: prepending to
the recursive result would copy it at every element. `file` is the file the
raws under scrutiny were parsed from — the top-level document, or the
spliced file whose `inputEnv` wrapper we descended into — so a missing
`\input` is reported at the file and line that wrote it. -/
def spliceList (dir : System.FilePath) (file : String)
    (out : Array Parse.Raw) (ds : Array Diag) (hit : Bool) :
    List Parse.Raw → IO (Array Parse.Raw × Array Diag × Bool)
  | [] => pure (out, ds, hit)
  | .ctrl "input" pos :: .group nameRaws _ :: rest
  | .ctrl "include" pos :: .group nameRaws _ :: rest => do
    let (sub, ds') ← readInput dir file (Parse.rawSrc nameRaws) pos
    spliceList dir file (out ++ sub) (ds ++ ds') true rest
  | .ctrl "markdownInput" pos :: rest => do
    let raws := rest.toArray
    let (opt, k) := Compat.takeOpt raws 0
    let j := Parse.skipSpaces raws k
    match raws[j]? with
    | some (.group nameRaws _) =>
      -- markdown.sty defines one optional setup argument and one filename.
      -- Native Markdown has one dialect; legacy setup keys remain a named
      -- loss, never literal option text in the output.
      let name := Parse.rawSrc nameRaws
      -- markdown.sty's file lookup honours an explicit extension; without
      -- one it tries `.tex`, then the literal spelling (inputFileChecks).
      let prefer := fun name : String => if (System.FilePath.mk name).extension.isSome then name
        else name ++ ".tex"
      let (sub, ds') ← readFragment dir file name pos prefer
        "markdownInput" Md.read
      let opts := (opt.getD "").trimAscii.toString
      let ds' := if opts.isEmpty then ds' else ds'.push <|
        Diag.of .W0110 s!"'\\markdownInput' options '{opts}' are not applied; \
the file uses the Markdown document dialect" (some ⟨file, pos⟩)
          (subject := some "markdownInput:options")
      spliceList dir file (out ++ sub) (ds ++ ds') true (rest.drop (j + 1))
    | _ =>
      spliceList dir file (out.push (.ctrl "markdownInput" pos)) ds hit rest
  | r :: rest => do
    let (r', ds', hit') ← spliceOne dir file r
    spliceList dir file (out.push r') (ds ++ ds') (hit || hit') rest
termination_by rs => sizeOf rs
decreasing_by
  all_goals simp_wf
  all_goals try omega
  have := drop_size_le rest (Parse.skipSpaces rest.toArray k + 1)
  omega

def spliceOne (dir : System.FilePath) (file : String) :
    Parse.Raw → IO (Parse.Raw × Array Diag × Bool)
  | .env n body p => do
    let (body', ds, hit) ← spliceList dir ((Parse.inputEnvFile? n).getD file)
      #[] #[] false body.toList
    return (.env n body' p, ds, hit)
  | .group body p => do
    let (body', ds, hit) ← spliceList dir file #[] #[] false body.toList
    return (.group body' p, ds, hit)
  | r => pure (r, #[], false)
termination_by r => sizeOf r
decreasing_by
  all_goals simp_wf
  all_goals (have hb : sizeOf body = 1 + sizeOf body.toList := rfl; omega)

end

/-- `\usepackage{p}` where `p.sty` exists beside the document is LaTeX's
own rule (ltfiles.dtx `\@onefilewithoptions`: find `p.sty` on the input
path and read it as TeX). Reading the file is this driver's effect, the
same door `\input` uses; the splice and the option machinery are the pure
core's (`Compat.applyLocalSty`), which wraps the file's text as its own
input fragment so every diagnostic names the `.sty` and its line. Where
no such file exists, the CTAN dispatch (W0103) applies unchanged. The
style file's own lexer and parser diagnostics are dropped: the file is
not the engine's to lint, and the splice carries its own positions. -/
def expandLocalSty (dir : System.FilePath) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array (String × Option String × Pos)) := do
  let candidates := Compat.localStyCandidates raws
  if candidates.isEmpty then return (raws, #[])
  let mut stys : Array (String × Array Parse.Raw) := #[]
  for name in candidates do
    let path := dir / (name ++ ".sty")
    if ← path.pathExists then
      let text ← IO.FS.readFile path
      let (toks, _) := Lex.lex (name ++ ".sty") text
      let (sraws, _) := Parse.parse (name ++ ".sty") toks
      stys := stys.push (name, sraws)
  if stys.isEmpty then return (raws, #[])
  return Compat.applyLocalSty raws stys

/-- `\input{name}` — and the local `.sty`, which is `\input` at its
`\usepackage` position — splices a file into the parsed tree. One pass
splices each site without descending into what it read; nested inputs, a
`\usepackage` inside an `\input`'ed file, a `\RequirePackage` inside a
spliced `.sty`, and an `\input` inside a `.sty` all resolve on the next
pass, and eight passes bound the depth the way TeX's input stack does — a
`.sty` that `\RequirePackage`s itself hits E0501, never loops. Every pass
is a structural walk, total by construction. Returns the tree, the
splice diagnostics, and the `.sty` records `Main` names as N0020 once the
elaborated counts exist. -/
def expandInputs (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag × Array (String × Option String × Pos)) := do
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut raws := raws
  let mut diags : Array Diag := #[]
  let mut spliced : Array (String × Option String × Pos) := #[]
  for _ in [0:8] do
    let (raws', ds, hitInput) ← spliceList dir file #[] #[] false raws.toList
    let (raws'', sp) ← expandLocalSty dir raws'
    raws := raws''
    diags := diags ++ ds
    spliced := spliced ++ sp
    unless hitInput || !sp.isEmpty do
      return (raws, diags, spliced)
  let (_, _, stillInput) ← spliceList dir file #[] #[] false raws.toList
  let (_, stillSty) ← expandLocalSty dir raws
  if stillInput || !stillSty.isEmpty then
    diags := diags.push DriverDiag.inputTooDeep
  return (raws, diags, spliced)

/-- The bibliography request an elaborated document states (`Ir.bibRefs`),
fulfilled: each named `.bib` resolves beside the document, like `\input`,
and its text goes to the pure core (`Bib.apply`) — parsing, ordering,
formatting, and the citation rewrite all happen there, on every document
(`Bib.apply_no_cite`: no `.cite` node reaches a backend). A missing file is
E0503 naming the path; the marker stays empty and the citations' `?`
marks say so on the page. -/
def resolveBibliography (file : String) (doc : Ir.Doc)
    (bibSpans : Array (String × Span) := #[]) :
    IO (Ir.Doc × Array Diag) := do
  let requested := Ir.bibRefs doc
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for src in requested do
    let name := Bib.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      sources := sources.push (src, ← IO.FS.readFile path)
    else
      diags := diags.push (DriverDiag.bibMissing src path.toString
        ((bibSpans.find? (·.1 == src)).map (·.2)))
  let (doc, applyDiags) := Bib.apply sources doc
  return (doc, diags ++ applyDiags)

/-- The data request a parsed document states (`Data.fileRefs`), fulfilled
before elaboration — the expansion needs the records where
`\begin{foreach}` stands, so this is the `resolveBibliography` shape moved
ahead of `Elab.runRaws`. Each named `.bib` resolves beside the document,
like `\input`; a missing file is E0365 naming the path, and the reads that
wanted its records say what stayed unresolved. -/
def resolveData (file : String) (raws : Array Parse.Raw) :
    IO (Array Parse.Raw × Array Diag) := do
  unless Data.hasData raws do return (raws, #[])
  let requested := Data.fileRefs raws
  let dir := (System.FilePath.mk file).parent.getD "."
  let mut sources : Array (String × String) := #[]
  let mut diags : Array Diag := #[]
  for (src, pos) in requested do
    let name := Data.sourceName src
    let path := if (System.FilePath.mk name).isAbsolute then System.FilePath.mk name
      else dir / name
    if ← path.pathExists then
      sources := sources.push (src, ← IO.FS.readFile path)
    else
      diags := diags.push (DriverDiag.dataMissing src path.toString (some ⟨file, pos⟩))
  let (raws, expandDiags) := Data.expandData file sources raws
  return (raws, diags ++ expandDiags)

end LeanTex.Cli.Input
