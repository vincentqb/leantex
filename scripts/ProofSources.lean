module

public import Lean

namespace ProofSources

public section

/-- Hidden build metadata and fixture bytes are not maintained Lean modules.
Every other source directory is discovered, including newly added libraries. -/
def sourcePath (parts : List String) : Bool :=
  parts.all (!·.startsWith ".") &&
    parts.head? != some "tests" && parts.head? != some "testdata"

/-- Sorted paths relative to the canonical source root, independent of umbrella
imports and Lake target registration. Links are not maintained source files;
compiled import closure must be checked separately against this inventory. -/
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

/-- Executable roots can declare the same global `main`; inspect them in
separate compiler environments. Every discovered source occurs in one group,
including libraries outside the current production and test namespaces. -/
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
