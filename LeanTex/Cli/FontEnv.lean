import LeanTex.Core.Font
import LeanTex.Cli.DriverDiag

/-! The font environment, as the driver's own decisions: the `LEANTEX_FONT`
override's face (`loadOverride`), the document's declared font directories
(`resolveDocDirs`), and the math face (`resolveMath`). All open files, so
they are effects and belong here rather than in the core; all **return**
what they decided instead of printing it, so a test can run the decision
rather than restate it.

None of the three performs the scan. `loadOverride` reads a path the
environment names, `resolveDocDirs` asks whether a path the *document*
names is a directory, and `resolveMath` is handed the faces a scan already
found — so each answers the same way on every host given the same inputs,
and a test may hand the last one a directory the suite ships. What is
genuinely the host's answer stays with the caller: which directories to
scan, and whether the scan found anything at all. -/

namespace LeanTex.Cli.FontEnv

open LeanTex.Core

/-- `LEANTEX_FONT` (a path) overrides the default face for a document that
declares no `\fonts`: one face serves every slot and variant, no scan.
Either the parsed face and the path it came from, or the diagnostic naming
why that path yielded none (E0402, for a path that is not there and for one
that is not a font). -/
def loadOverride (path : String) : IO (Except Diag (Font.Font × String)) := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    match Font.parse data with
    | .ok f => return .ok (f, path)
    | .error e => return .error (DriverDiag.envFontUnusable path e)
  else
    return .error (DriverDiag.envFontMissing path)

/-- The directories a document's `\fonts{ dir = ... }` names, resolved
against the document's own directory like `\input`, and kept only where one
really is a directory: a document that ships its fonts renders the same on
every host, and a declaration naming nothing is W0008 — config, not a
loss, because the scan simply looks elsewhere. A trailing slash is the same
directory as none. -/
def resolveDocDirs (file : String) (dirs : Array String) :
    IO (List String × Array Diag) := do
  let mut docDirs : List String := []
  let mut diags : Array Diag := #[]
  for d in dirs do
    let d := if d.endsWith "/" && d.length > 1 then (d.dropEnd 1).toString else d
    let p := System.FilePath.mk d
    let p := if p.isAbsolute then p else ((System.FilePath.mk file).parent.getD ".") / p
    if ← p.isDir then
      docDirs := docDirs ++ [p.toString]
    else
      diags := diags.push (DriverDiag.fontsDirMissing d p.toString)
  return (docDirs, diags)

/-- What the math-face decision leaves behind: the loaded faces and their
paths, extended where a file had to be read; `index` the set's math slot;
`missing` the families already named, so no second E0403 repeats one; and
`diags` what the decision decided. -/
structure MathFace where
  fonts : Array Font.Font
  paths : Array String
  index : Option Nat
  missing : Array String
  diags : Array Diag

/-- The math face, decided against a scan it is handed rather than one it
performs. Which faces exist is the host's answer and stays the caller's to
fetch; what the engine does with them is this decision, and it is the same
on every host holding the same faces — which is what lets a test run it
over a directory the suite ships.

A declared face is resolved like any named family and installed only when
it carries an OpenType MATH table: constants are never invented, so a face
without the table earns W0011 naming it and math is set as source text
(PLAN, M6 design decision 1). With no declaration and formulas on the
page, the body family's designed companion answers when the scan holds it,
else the first scanned MATH-table face — either way N0016 names it, so a
face the document did not choose is never silent. -/
def resolveMath (faces : Array FontDb.Face) (declared : Option String)
    (body : Option String) (wantsMath : Bool)
    (fonts : Array Font.Font) (paths : Array String)
    (missing : Array String) : IO MathFace := do
  let mut fonts := fonts
  let mut paths := paths
  let mut missing := missing
  let mut diags : Array Diag := #[]
  let mut mathIdx : Option Nat := none
  -- The face comes back with its slot, never an index to look up again: a
  -- `]!` here would abort a whole run over an invariant no reader can see.
  let loadFace (fonts : Array Font.Font) (paths : Array String) (path : String) :
      IO (Option (Nat × Font.Font) × Array Font.Font × Array String × Option Diag) := do
    match paths.findIdx? (· == path) with
    | some i =>
      match fonts[i]? with
      | some f => return (some (i, f), fonts, paths, none)
      | none => return (none, fonts, paths, none)
    | none =>
      let data ← IO.FS.readBinFile path
      match Font.parse data with
      | .error e =>
        return (none, fonts, paths, some (DriverDiag.fontFileUnusable path e))
      | .ok f =>
        return (some (fonts.size, f), fonts.push f, paths.push path, none)
  if let some family := declared then
    match FontDb.resolveVariant faces family none {} with
    | none =>
      unless missing.contains family do
        missing := missing.push family
        let all := FontDb.families faces
        diags := diags.push (DriverDiag.familyMissing family
          (FontDb.nearest all family).toList all.size)
    | some (face, _) =>
      let (loaded, fonts', paths', diag?) ← loadFace fonts paths face.path
      fonts := fonts'
      paths := paths'
      if let some d := diag? then
        diags := diags.push d
      if let some (i, f) := loaded then
        if f.math.isSome then
          mathIdx := some i
        else
          diags := diags.push (DriverDiag.mathFaceNoTable f.family face.path)
  else if wantsMath then
    let bodyFam := body.getD ""
    let choice : Option (FontDb.Face × Option String) ←
      (← FontDb.pickMathFace faces bodyFam).mapM fun (face, row?) =>
        pure (face, row?.map fun _ => bodyFam)
    if let some (face, companionOf) := choice then
      let (loaded, fonts', paths', diag?) ← loadFace fonts paths face.path
      fonts := fonts'
      paths := paths'
      if let some d := diag? then
        diags := diags.push d
      if let some (i, f) := loaded then
        if f.math.isSome then
          mathIdx := some i
          diags := diags.push (match companionOf with
            | some named => DriverDiag.mathFaceCompanion f.family named
            | none => DriverDiag.mathFaceFirst f.family)
  return { fonts, paths, index := mathIdx, missing, diags }

end LeanTex.Cli.FontEnv
