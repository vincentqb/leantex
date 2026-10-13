module

public import Lean

namespace ProofSources

public section

/-- Whether a path is a maintained source: no hidden component, and outside testdata. -/
def sourcePath (parts : List String) : Bool :=
  parts.all (!·.startsWith ".") && parts.head? != some "testdata"

/-- The maintained Lean sources, sorted and relative to the canonical source root, links
excluded. -/
def sources (root : System.FilePath) : IO (Array System.FilePath) := do
  let root ← IO.FS.realPath root
  let relative := fun (path : System.FilePath) =>
    path.normalize.components.drop root.normalize.components.length
  let paths ← root.walkDir fun path => do
    return (← path.symlinkMetadata).type == .dir && sourcePath (relative path)
  let mut found := #[]
  for path in paths do
    let parts := relative path
    if sourcePath parts && path.extension == some "lean" &&
        parts != ["lakefile.lean"] then
      unless (← path.symlinkMetadata).type == .file do
        throw <| IO.userError s!"proof audit: source is not a regular file: {path}"
      found := found.push ⟨String.intercalate "/" parts⟩
  return found.qsort (fun a b => a.toString < b.toString)

def moduleName (file : System.FilePath) : String :=
  (file.withExtension "").toString.replace "/" "."

def importName (name : String) : String :=
  String.intercalate "." ((name.splitOn ".").map fun part => "«" ++ part ++ "»")

/-- The sources grouped for separate compiler environments, since executable roots may
each declare `main`; every source is in one group. -/
def groups (files : Array System.FilePath) : Array (Array String) := Id.run do
  let mut library := #[]
  let mut isolated := #[]
  for file in files do
    let name := moduleName file
    if name.startsWith "LeanTex." || name.startsWith "Tests." || name == "LeanTex" then
      library := library.push name
    else
      isolated := isolated.push #[name]
  return (if library.isEmpty then #[] else #[library]) ++ isolated

end
end ProofSources
