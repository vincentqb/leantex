import LeanTex.Core.Lex
import LeanTex.Core.Parse
import LeanTex.Core.Compat
import LeanTex.Cli.DriverDiag

/-! The driver's file-splicing frontend: `\input`/`\include` and the local
`.sty` read (`\usepackage{p}` with `p.sty` beside the document) are one
splice — both wrap a file's parsed text as its own input fragment — and
run to one fixpoint here. Reading a file is an effect, so it happens in
the driver rather than in the core; the core sees one tree, as if the
document had been written in one file. Lives beside the other Cli modules
rather than in Main so the fixpoint is testable: the three `\input`-parity
cases (a `\usepackage` inside an `\input`'ed preamble file, a
`\RequirePackage` inside a spliced `.sty`, an `\input` inside a `.sty`)
exist only across passes of this loop. -/

namespace LeanTex.Cli.Input

open LeanTex.Core

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
    let (raws', ds, hitInput) ← spliceList dir #[] #[] false raws.toList
    let (raws'', sp) ← expandLocalSty dir raws'
    raws := raws''
    diags := diags ++ ds
    spliced := spliced ++ sp
    unless hitInput || !sp.isEmpty do
      return (raws, diags, spliced)
  let (_, _, stillInput) ← spliceList dir #[] #[] false raws.toList
  let (_, stillSty) ← expandLocalSty dir raws
  if stillInput || !stillSty.isEmpty then
    diags := diags.push DriverDiag.inputTooDeep
  return (raws, diags, spliced)

end LeanTex.Cli.Input
