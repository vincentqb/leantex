module

public import Tests.Support
import Lean.Elab.ParseImportsFast

public section

/-! The build graph as Lake reads it. A module's private part — its
private declarations, unexposed bodies, proofs and comments — reaches a
dependent's build only through `import all`, or through a file outside the
module system, which reads every transitive import whole (Lake's
`ModuleImportInfo.addImport`). So a private edit to a module rebuilds
exactly the files that read its private part. A large module on that list
re-elaborates for nothing: an appended comment line once cost six and a
half minutes of `lake build leantex Tests`, Layout and HtmlDoc each
reading all of Ir and 172 test files reading everything. -/

namespace Tests.BuildGraph

/-- One `import` of a header: the module named and whether it reads the
private part (`import all`). -/
structure Import where
  mod : String
  all : Bool
  deriving BEq, Repr

/-- A source file's header: its module name, whether it is a `module`, and
its imports. -/
structure Header where
  name : String
  isModule : Bool
  imports : Array Import
  deriving Repr

/-- A source file's header as Lake reads it — `Lean.parseImports'`, the
reader Lake builds its import graph from, so a comment or a modifier
anywhere in a header is read as the build reads it — or the error Lake
raises on a header it refuses. -/
def parseHeader (name text : String) : IO (Except String Header) := do
  try
    let h ← Lean.parseImports' text name
    return .ok {
      name, isModule := h.isModule
      imports := h.imports.map fun i =>
        { mod := i.module.toString (escape := false), all := i.importAll } }
  catch e => return .error e.toString

/-- The modules whose private part `h`'s build reads, among those in
`graph`. A file outside the module system reads every transitive import
whole; a module reads each module it imports `all`, and whatever that one
imports `all` in turn. The closure takes at most one round per module. -/
def privateReads (graph : Std.HashMap String Header) (h : Header) : Array String := Id.run do
  let follow (i : Import) : Bool := !h.isModule || i.all
  let mut seen : Array String :=
    (h.imports.filter fun i => follow i && graph.contains i.mod).map (·.mod)
  for _ in [0:graph.size] do
    let mut next := seen
    for m in seen do
      for i in (graph.get? m).map (·.imports) |>.getD #[] do
        if follow i && graph.contains i.mod && !next.contains i.mod then
          next := next.push i.mod
    if next.size == seen.size then break
    seen := next
  return seen.qsort (· < ·)

/-- The files outside the module system, each small and imported by no
module: the suite's root, which gathers every check; `Tests.DiagAudit`,
which defines the `thm%`/`check%` pin syntax, and `Tests.Reports`, which
uses it; `Tests.PdfReadRepresentability`, whose proofs decide over the
UTF-8 bytes of string literals, a body core does not expose to modules; and
`Tests.SvgBrowser`, outside the suite, which reads the scoreboard library. -/
def legacyFiles : List String :=
  ["Tests", "Tests.DiagAudit", "Tests.PdfReadRepresentability", "Tests.Reports",
   "Tests.SvgBrowser"]

/-- A file at least this long takes tens of seconds to elaborate (Layout,
about 21,000 lines: 130 s; Picture, about 6,000: 27 s), so what its build
reads is declared below. -/
def largeLines : Nat := 5000

/-- What each large file's build reads of other modules' private parts —
every large file has a row, and the row is exactly what its imports read.
Layout's diagnostic proofs compare code spellings, which the registry
(`DiagCode.spec`) keeps private. -/
def largeReads : List (String × List String) :=
  [("LeanTex.Core.Compat", []),
   ("LeanTex.Core.Elab", []),
   ("LeanTex.Core.HtmlDoc", []),
   ("LeanTex.Core.Ir", []),
   ("LeanTex.Core.Layout", ["LeanTex.Core.Diag"]),
   ("LeanTex.Core.Picture", []),
   ("Tests.Layout", []),
   ("Tests.Surface", [])]

/-- The maintained Lean sources: the library, the suite and the two roots
beside them. Tools under `scripts/` build on their own. -/
def sources : IO (Array (String × String)) := do
  let mut out := #[]
  for dir in ["LeanTex", "Tests"] do
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" then
        out := out.push f.toString
  out := out ++ #["LeanTex.lean", "Main.lean", "Tests.lean"]
  let mut named := #[]
  for path in out.qsort (· < ·) do
    let name := ".".intercalate ((path.dropEnd ".lean".length).toString.splitOn "/")
    named := named.push (name, ← IO.FS.readFile path)
  return named

/-- The verdicts over one tree, as named facts. -/
def judge (files : Array (String × String)) : IO (List (String × Bool)) := do
  let mut headers : Array Header := #[]
  let mut refused : Array String := #[]
  for (n, t) in files do
    match ← parseHeader n t with
    | .ok h => headers := headers.push h
    | .error e => refused := refused.push e
  let graph : Std.HashMap String Header :=
    headers.foldl (fun g h => g.insert h.name h) {}
  let legacy := (headers.filter (!·.isModule)).map (·.name)
  let mut facts : List (String × Bool) :=
    [(s!"every header reads as Lake reads it (refused: {refused.toList})", refused.isEmpty),
     (s!"the files outside the module system are exactly {legacyFiles} (found {legacy.toList})",
      legacy.toList.mergeSort (· ≤ ·) == legacyFiles.mergeSort (· ≤ ·)),
     ("every declared large file exists",
      largeReads.all fun (n, _) => graph.contains n)]
  for (name, text) in files do
    let size := (text.splitOn "\n").length
    let large := size ≥ largeLines
    let row := largeReads.lookup name
    if large || row.isSome then
      let reads := ((graph.get? name).map (privateReads graph) |>.getD #[]).toList
      facts := facts ++ [match row with
        | some r =>
          if large then (s!"{name} ({size} lines) reads exactly the private parts {r} \
(found {reads})", r == reads)
          else (s!"{name} keeps a largeReads row at {size} lines, under {largeLines}", false)
        | none => (s!"{name} ({size} lines) declares what it reads in largeReads \
(found {reads})", false)]
  return facts

/-- The model on an invented graph, both ways: a legacy file reads its whole
closure, a module reads only through `import all`, and `import all` is
transitive only through further `import all`; the header as Lake reads it —
a comment anywhere in it, a nested one, one ending an import line, one
before `module` — and a header Lake refuses is a failing fact, never a
skipped file; and the table both ways: a large file needs a row, and a row
needs a large file. -/
def selfTest : IO (List (String × Bool)) := do
  let g : List (String × String) :=
    [("A", "module\n\nimport all B\nimport C\n\nnamespace A\n\nimport all G"),
     ("B", "module\n\npublic import all D\nimport E\n"),
     ("C", "module\n\nimport all F\n"),
     ("D", "module\n"), ("E", "module\n"), ("F", "module\n"), ("G", "module\n"),
     ("L", "-- a legacy file\nimport C\n\ndef x := 1"),
     ("K1", "module\n\n/- generated; do not edit -/\nimport all G\n"),
     ("K2", "module\n\nimport C -- a trailing comment\nimport all G\n"),
     ("K3", "module\n/- outer /- inner -/ outer again -/\nimport all G\n"),
     ("K4", "/- a header comment before the keyword -/\nmodule\nimport all G\n")]
  let mut graph : Std.HashMap String Header := {}
  for (n, t) in g do
    if let .ok h ← parseHeader n t then graph := graph.insert n h
  let reads (n : String) := (graph.get? n).map (privateReads graph) |>.getD #[]
  let big := "module\n" ++ "\n".intercalate (List.replicate largeLines "-- line")
  let unrowed ← judge #[("Synthetic.Big", big)]
  let smallRow ← judge #[("LeanTex.Core.Compat", "module\n")]
  let refused ← judge #[("Synthetic.Bad", "import all G\n")]
  return [("an import all reads through further import all, never through a plain import",
     reads "A" == #["B", "D"]),
   ("a plain import reads no private part", reads "D" == #[]),
   ("a legacy file reads its whole closure", reads "L" == #["C", "F"]),
   ("an import after the first command is not the header's",
     (graph.get? "A").map (·.imports.any (·.mod == "G")) == some false),
   ("an import all after a block comment is read", reads "K1" == #["G"]),
   ("an import all after a commented import line is read", reads "K2" == #["G"]),
   ("an import all after a nested block comment is read", reads "K3" == #["G"]),
   ("a comment before `module` leaves the file a module",
     (graph.get? "K4").map (·.isModule) == some true && reads "K4" == #["G"]),
   ("a header Lake refuses fails, naming its file",
     refused.any fun (n, ok) => !ok && hasStr n "as Lake reads it" && hasStr n "Synthetic.Bad"),
   ("a large file without a declared row fails",
     unrowed.any fun (n, ok) => !ok && hasStr n "Synthetic.Big"),
   ("a declared row on a small file fails",
     smallRow.any fun (n, ok) => !ok && hasStr n "keeps a largeReads row")]

end Tests.BuildGraph

/-- The build graph's private reads over the maintained tree. -/
def buildGraphChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, ok) in ← Tests.BuildGraph.selfTest do
    check ref s!"build graph model: {name}" ok
  for (name, ok) in ← Tests.BuildGraph.judge (← Tests.BuildGraph.sources) do
    check ref s!"build graph: {name}" ok
