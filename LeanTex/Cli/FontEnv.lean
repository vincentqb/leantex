import LeanTex.Core.Font
import LeanTex.Cli.DriverDiag

/-! The font environment, as the driver's own decisions: the `LEANTEX_FONT`
override's face (`loadOverride`) and the document's declared font
directories (`resolveDocDirs`). Both open files, so they are effects and
belong here rather than in the core; both **return** what they decided
instead of printing it, so a test can run the decision rather than restate
it.

The rest of the font environment — which installed family answers a name,
which face carries a MATH table — is decided against what this host has
scanned, and a test asserting one of those fires would be asserting a fact
about the machine. These two are not: one reads a path the environment
names, the other asks whether a path the *document* names is a directory,
and both answer the same way on every host. -/

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

end LeanTex.Cli.FontEnv
