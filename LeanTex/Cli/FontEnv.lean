module

public import LeanTex.Core.Font
public import LeanTex.Core.FontDb
public import LeanTex.Core.Diag
import LeanTex.Cli.FontDiscovery
import LeanTex.Cli.DriverDiag

/-! The driver's font-environment decisions: the `LEANTEX_FONT` override, the document's
font directories and the math face, each returned rather than printed. -/

namespace LeanTex.Cli.FontEnv

open LeanTex.Core

/-- Face files parsed once per path per run; a set is never cached, since its order is its
index. -/
public structure Cache where
  private mk ::
  private ref : IO.Ref (Array (String × Font.Font))
  /-- Face resolution answers, keyed by the question. -/
  private weights : IO.Ref (Array ((String × Option String × Nat × Bool) ×
    Option (FontDb.Face × Option FontDb.Substituted)))
  /-- Every path `parse` read, whatever the parse made of it. -/
  private read : IO.Ref (Array String)

public def Cache.mk' : IO Cache := do
  return ⟨← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[]⟩

/-- Resolve a family's face for one weight and slant, through the memo. -/
public def Cache.resolveWeight (c : Cache) (faces : Array FontDb.Face) (family : String)
    (declared : Option String) (weight : Nat) (italic : Bool) :
    IO (Option (FontDb.Face × Option FontDb.Substituted)) := do
  let key := (family, declared, weight, italic)
  if let some e := (← c.weights.get).find? (·.1 == key) then
    return e.2
  let answer := FontDb.resolveWeight faces family declared weight italic
  c.weights.modify (·.push (key, answer))
  return answer

/-- The face files this cache read, parsed or refused, by the paths they were read at. -/
public def Cache.readPaths (c : Cache) : IO (Array String) := c.read.get

/-- Parse a face, or return the parse already made for that path. -/
public def Cache.parse (c : Cache) (path : String) : IO (Except String Font.Font) := do
  if let some f := (← c.ref.get).find? (·.1 == path) then
    return .ok f.2
  let file := FontDb.faceFile path
  unless (← c.read.get).contains file do c.read.modify (·.push file)
  match (← FontDiscovery.faceBytes path) >>= Font.parse with
  | .error e => return .error e
  | .ok f =>
    c.ref.modify (·.push (path, f))
    return .ok f

/-- Parse through the cache when the caller holds one; the answer is the same without it.
-/
private def parseFace (cache : Option Cache) (path : String) :
    IO (Except String Font.Font) := do
  match cache with
  | some c => c.parse path
  | none => return (← FontDiscovery.faceBytes path) >>= Font.parse

/-- `LEANTEX_FONT`'s face for a document declaring no `\fonts`, with its path, or the
E0402 naming why the path yields none. -/
public def loadOverride (path : String) : IO (Except Diag (Font.Font × String)) := do
  if ← System.FilePath.pathExists path then
    let data ← IO.FS.readBinFile path
    match Font.parse data with
    | .ok f => return .ok (f, path)
    | .error e => return .error (DriverDiag.envFontUnusable path e)
  else
    return .error (DriverDiag.envFontMissing path)

/-- The directories a document's `\fonts{ dir = ... }` names, resolved against the
document's directory and kept where one is a directory; a name that is none is W0008. -/
public def resolveDocDirs (file : String) (dirs : Array String) :
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

/-- What the math-face decision leaves: the faces and paths it loaded, the set's math
slot, the families already named, and its diagnostics. -/
public structure MathFace where
  fonts : Array Font.Font
  paths : Array String
  index : Option Nat
  missing : Array String
  diags : Array Diag

/-- The math face, decided over the scanned faces it is handed: a declared face installs
only with an OpenType MATH table (else W0011), and a face the document did not declare is
named by N0016. -/
public def resolveMath (faces : Array FontDb.Face) (declared : Option String)
    (body : Option String) (wantsMath : Bool)
    (fonts : Array Font.Font) (paths : Array String)
    (missing : Array String) (cache : Option Cache := none)
    (source : Option Span := none) : IO MathFace := do
  let mut fonts := fonts
  let mut paths := paths
  let mut missing := missing
  let mut diags : Array Diag := #[]
  let mut mathIdx : Option Nat := none
  let loadFace (fonts : Array Font.Font) (paths : Array String) (path : String) :
      IO (Option (Nat × Font.Font) × Array Font.Font × Array String × Option Diag) := do
    match paths.findIdx? (· == path) with
    | some i =>
      match fonts[i]? with
      | some f => return (some (i, f), fonts, paths, none)
      | none => return (none, fonts, paths, none)
    | none =>
      match ← parseFace cache path with
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
      (← FontDiscovery.pickMathFace faces bodyFam).mapM fun (face, row?) =>
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
          let note := match companionOf with
            | some named => DriverDiag.mathFaceCompanion f.family named
            | none => DriverDiag.mathFaceFirst f.family
          let written := (source.bind (·.pos.command)).bind Diag.Spelling.ofWritten?
          diags := diags.push { note with span := source, trigger := written }
  return { fonts, paths, index := mathIdx, missing, diags }

end LeanTex.Cli.FontEnv
