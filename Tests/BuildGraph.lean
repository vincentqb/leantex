module

public import Tests.Support
public import scripts.Layers
import Lean.Elab.ParseImportsFast

public section

/-! The build graph as Lake reads it: a module's private part reaches a dependent's build only
through `import all` or a file outside the module system. -/

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

/-- A source file's header as Lake reads it, by `Lean.parseImports'`, or the error Lake raises on a
header it refuses. -/
def parseHeader (name text : String) : IO (Except String Header) := do
  try
    let h ← Lean.parseImports' text name
    return .ok {
      name, isModule := h.isModule
      imports := h.imports.map fun i =>
        { mod := i.module.toString (escape := false), all := i.importAll } }
  catch e => return .error e.toString

/-- Every module `root`'s build reaches through the imports `follow` admits, each with the first chain
reaching it; a module `stop` names, or one outside `graph`, is reached and not read on. -/
def reach (graph : Std.HashMap String Header) (root : String) (follow : Import → Bool)
    (stop : String → Bool := fun _ => false) : Array (List String) := Id.run do
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert root
  let mut frontier : Array (List String) := #[[root]]
  let mut found : Array (List String) := #[]
  for _ in [0:graph.size + 1] do
    let mut next : Array (List String) := #[]
    for path in frontier do
      let some m := path.head? | continue
      for i in (graph.get? m).map (·.imports) |>.getD #[] do
        unless !follow i || seen.contains i.mod do
          seen := seen.insert i.mod
          found := found.push (i.mod :: path).reverse
          unless stop i.mod do next := next.push (i.mod :: path)
    if next.isEmpty then break
    frontier := next
  return found

/-- The modules whose private part `h`'s build reads among `graph`: everything for a file outside
the module system, else the transitive `import all` closure. -/
def privateReads (graph : Std.HashMap String Header) (h : Header) : Array String :=
  (((reach graph h.name fun i => !h.isModule || i.all).filterMap (·.getLast?)).filter
    graph.contains).qsort (· < ·)

/-- Each surface module `root`'s build reaches through a chain of imports of any kind, with the first
chain reaching it, a surface's own imports and those of a module `stop` names unread. -/
def surfaceReach (graph : Std.HashMap String Header) (root : String)
    (stop : String → Bool := fun _ => false) : Array (List String) :=
  (reach graph root (fun _ => true) fun m => surfaceModules.contains m || stop m).filter fun chain =>
    chain.getLast?.any surfaceModules.contains

/-- The files outside the module system, each small and imported by no module. -/
def legacyFiles : List String :=
  ["Tests", "Tests.DiagAudit", "Tests.PdfReadRepresentability", "Tests.Premises",
   "Tests.Reports", "Tests.SvgBrowser"]

/-- A file at least this long takes tens of seconds to elaborate, so what its build reads is
declared below. -/
def largeLines : Nat := 5000

/-- What each large file's build reads of other modules' private parts: exactly its imports' reads. -/
def largeReads : List (String × List String) :=
  [("LeanTex.Core.Compat", []),
   ("LeanTex.Core.Elab", []),
   ("LeanTex.Core.HtmlDoc", []),
   ("LeanTex.Core.Ir", []),
   ("LeanTex.Core.Layout", ["LeanTex.Core.Diag"]),
   ("LeanTex.Core.Picture", []),
   ("Tests.Layout", []),
   ("Tests.Surface", [])]

/-- Whose builds read each large file's private part: exactly its readers, so a new reader is a
decision written here. -/
def largeReaders : List (String × List String) :=
  [("LeanTex.Core.Compat", ["LeanTex.Core.ControlContract", "LeanTex.Core.InputContract"]),
   ("LeanTex.Core.Elab", ["LeanTex.Core.ControlContract", "LeanTex.Core.ElabRegistryContract",
     "LeanTex.Core.GroupContract", "LeanTex.Core.InputContract", "LeanTex.Core.PictureContract",
     "LeanTex.Core.TitleContract"]),
   ("LeanTex.Core.HtmlDoc", ["LeanTex.Core.PdfAgreement"]),
   ("LeanTex.Core.Ir", ["LeanTex.Core.BibContract", "LeanTex.Core.ColorContract",
     "LeanTex.Core.ContrastContract", "LeanTex.Core.ControlContract",
     "LeanTex.Core.ElabRegistryContract", "LeanTex.Core.FloatNumberProof", "LeanTex.Core.Pending",
     "LeanTex.Core.PictureCensus",
     "LeanTex.Core.Theme", "LeanTex.Core.ThemeContract"]),
   ("LeanTex.Core.Layout", ["LeanTex.Core.Layout.FramePartition",
     "LeanTex.Core.Layout.InkContract", "LeanTex.Core.Layout.InkOutput",
     "LeanTex.Core.Layout.MathRhythm", "LeanTex.Core.Layout.SpacingContract"]),
   ("LeanTex.Core.Picture", ["LeanTex.Core.ElabRegistryContract"]),
   ("Tests.Layout", []),
   ("Tests.Surface", [])]

/-- The maintained tools' sources, which a module may import too. -/
def scriptSources : IO (Array (String × String)) := do
  let mut named := #[]
  for f in ← System.FilePath.walkDir "scripts" do
    if f.extension == some "lean" then
      let name := ".".intercalate ((f.toString.dropEnd ".lean".length).toString.splitOn "/")
      named := named.push (name, ← IO.FS.readFile f)
  return named

/-- The maintained Lean sources: the library, the suite and the two roots beside them. -/
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

/-- The verdicts over one tree, as named facts; `tools` join the graph its import closures read. -/
def judge (files : Array (String × String)) (tools : Array (String × String) := #[]) :
    IO (List (String × Bool)) := do
  let mut headers : Array Header := #[]
  let mut toolHeaders : Array Header := #[]
  let mut refused : Array String := #[]
  for (n, t) in files do
    match ← parseHeader n t with
    | .ok h => headers := headers.push h
    | .error e => refused := refused.push e
  for (n, t) in tools do
    match ← parseHeader n t with
    | .ok h => toolHeaders := toolHeaders.push h
    | .error e => refused := refused.push e
  let graph : Std.HashMap String Header :=
    (headers ++ toolHeaders).foldl (fun g h => g.insert h.name h) {}
  let chains (cs : Array (List String)) : List String := cs.toList.map (" → ".intercalate ·)
  let reaches (root target : String) : Bool :=
    (reach graph root (fun _ => true)).any (·.getLast? == some target)
  -- Every module of the core whose build reads a backend lies on the backends' side of the surface.
  let aboveBackends := headers.filter fun h => h.name.startsWith "LeanTex.Core." &&
    (backendModules.contains h.name || backendModules.any (reaches h.name ·))
  let crossing := aboveBackends.filterMap fun h =>
    let found := surfaceReach graph h.name backendModules.contains
    if found.isEmpty || backendModules.contains h.name then none else some (chains found)
  let door := "LeanTex.Core.Surface"
  let backendSide (m : String) : Bool := backendModules.any fun b => b == m || reaches b m
  let doorReads := (((graph.get? door).map (·.imports)).getD #[]).filterMap fun i =>
    if i.mod.startsWith "LeanTex." && !backendSide i.mod then some i.mod else none
  let layers := surfaceModules ++ backendModules ++ importFloors.flatMap fun (a, b) => [a, b]
  let legacy := (headers.filter (!·.isModule)).map (·.name)
  let mut facts : List (String × Bool) :=
    [(s!"every header reads as Lake reads it (refused: {refused.toList})", refused.isEmpty),
     (s!"the files outside the module system are exactly {legacyFiles} (found {legacy.toList})",
      legacy.toList.mergeSort (· ≤ ·) == legacyFiles.mergeSort (· ≤ ·)),
     ("every declared large file exists",
      (largeReads ++ largeReaders).all fun (n, _) => graph.contains n),
     (s!"every surface module, backend and floor's end is in the tree (missing: \
{layers.filter (!graph.contains ·)})", layers.all graph.contains),
     (s!"every module of the library the surfaces' door reads and no backend reads is a surface \
module (found {doorReads})", graph.contains door && doorReads.all surfaceModules.contains),
     (s!"no module of the core whose build reads a backend reaches a surface module but through one \
(found {crossing})", crossing.isEmpty)] ++
    (backendModules.map fun b =>
      (s!"the backend {b} reaches no surface module through any import (found \
{chains (surfaceReach graph b)})", (surfaceReach graph b).isEmpty)) ++
    importFloors.map fun (root, banned) =>
      let found := (reach graph root (fun _ => true)).filter (·.getLast? == some banned)
      (s!"{root} stays below {banned}, which none of its imports reaches (found {chains found})",
        found.isEmpty)
  let moduleReads := (headers.filter (·.isModule)).map fun h => (h.name, privateReads graph h)
  for (name, text) in files do
    let size := (text.splitOn "\n").length
    let large := size ≥ largeLines
    let reads := ((graph.get? name).map (privateReads graph) |>.getD #[]).toList
    let readers := (((moduleReads.filter (·.2.contains name)).map (·.1)).qsort (· < ·)).toList
    for (table, rows, what, found) in
        [("largeReads", largeReads, "the private parts it reads", reads),
         ("largeReaders", largeReaders, "the modules reading it whole", readers)] do
      let row := rows.lookup name
      if large || row.isSome then
        facts := facts ++ [match row with
          | some r =>
            if large then (s!"{name} ({size} lines): {what} are exactly its {table} row {r} \
(found {found})", r == found)
            else (s!"{name} keeps a {table} row at {size} lines, under {largeLines}", false)
          | none => (s!"{name} ({size} lines) declares {what} in {table} (found {found})", false)]
  return facts

/-- The model on an invented graph, both ways: closures, headers as Lake reads them, and the tables. -/
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
  let chained ← judge #[("LeanTex.Core.Picture", big),
    ("Synthetic.Mid", "module\nimport all LeanTex.Core.Picture\n"),
    ("Synthetic.Contract", "module\nimport all Synthetic.Mid\n")]
  let throughMid ← judge #[("LeanTex.Core.HtmlDoc", "module\nimport Synthetic.Leaf\nimport Synthetic.Mid\n"),
    ("Synthetic.Leaf", "module\n"), ("Synthetic.Mid", "module\npublic import all LeanTex.Core.Parse\n"),
    ("LeanTex.Core.Parse", "module\nimport LeanTex.Core.Lex\n"), ("LeanTex.Core.Lex", "module\n")]
  let spelled ← judge #[("LeanTex.Core.MarkdownDoc", "module\npublic meta import LeanTex.Core.MdDesugar\n"),
    ("LeanTex.Core.MdDesugar", "module\n")]
  let clean ← judge #[("LeanTex.Core.Html", "module\nimport Synthetic.Leaf\n"),
    ("Synthetic.Leaf", "module\n")]
  let backendFact (facts : List (String × Bool)) (b : String) : Option (String × Bool) :=
    facts.find? fun (n, _) => hasStr n s!"the backend {b} "
  let viaTool ← judge #[("LeanTex.Core.Html", "module\nimport scripts.Mid\n")]
    #[("scripts.Mid", "module\nimport LeanTex.Core.Parse\n")]
  let above ← judge #[("LeanTex.Core.Html", "module\n"),
    ("Synthetic.Above", "module\nimport LeanTex.Core.Html\nimport LeanTex.Core.Lex\n")]
  let aboveCore ← judge #[("LeanTex.Core.Html", "module\n"),
    ("LeanTex.Core.Above", "module\nimport LeanTex.Core.Html\nimport LeanTex.Core.Lex\n")]
  let floorKept ← judge #[("LeanTex.Core.Oklab", "module\npublic import LeanTex.Core.Color\n"),
    ("LeanTex.Core.Color", "module\n")]
  let floorBroken ← judge #[("LeanTex.Core.Oklab", "module\nimport LeanTex.Core.Ir\n")]
  let floorThrough ← judge #[("LeanTex.Core.Contrast", "module\npublic import LeanTex.Core.Theme\n"),
    ("LeanTex.Core.Theme", "module\npublic import all LeanTex.Core.Layout\n")]
  let floorFact (facts : List (String × Bool)) (root : String) : Option (String × Bool) :=
    facts.find? fun (n, _) => hasStr n s!"{root} stays below"
  let throughBackend ← judge #[("LeanTex.Core.Html", "module\nimport LeanTex.Core.Lex\n"),
    ("LeanTex.Core.Lex", "module\n"), ("LeanTex.Core.Above", "module\nimport LeanTex.Core.Html\n")]
  let sharedDoor ← judge #[("LeanTex.Core.Surface", "module\nimport LeanTex.Core.Ir\n"),
    ("LeanTex.Core.Html", "module\nimport LeanTex.Core.Ir\n"), ("LeanTex.Core.Ir", "module\n")]
  let unlistedDoor ← judge #[("LeanTex.Core.Surface", "module\nimport LeanTex.Core.Helper\n"),
    ("LeanTex.Core.Helper", "module\n")]
  let doorFact (facts : List (String × Bool)) : Option (String × Bool) :=
    facts.find? fun (n, _) => hasStr n "the surfaces' door reads"
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
     smallRow.any fun (n, ok) => !ok && hasStr n "keeps a largeReads row"),
   ("a large file read whole through a chain of import all fails, naming the reader",
     chained.any fun (n, ok) => !ok && hasStr n "largeReaders" && hasStr n "Synthetic.Contract"),
   ("a backend reaching a surface through a module it imports fails, naming the first chain",
     (backendFact throughMid "LeanTex.Core.HtmlDoc").any fun (n, ok) => !ok &&
       hasStr n "[LeanTex.Core.HtmlDoc → Synthetic.Mid → LeanTex.Core.Parse]"),
   ("a backend importing a surface meta and publicly fails",
     (backendFact spelled "LeanTex.Core.MarkdownDoc").any fun (n, ok) => !ok &&
       hasStr n "LeanTex.Core.MarkdownDoc → LeanTex.Core.MdDesugar"),
   ("a backend whose imports reach no surface passes",
     (backendFact clean "LeanTex.Core.Html").any (·.2)),
   ("a backend absent from the tree fails, named missing",
     clean.any fun (n, ok) => !ok && hasStr n "missing:" && hasStr n "LeanTex.Core.Pdf"),
   ("a floor's end absent from the tree fails, named missing",
     clean.any fun (n, ok) => !ok && hasStr n "missing:" && hasStr n "LeanTex.Core.DesignRole"),
   ("a core module reaching a surface only through a backend is named once, by the backend",
     (backendFact throughBackend "LeanTex.Core.Html").any (!·.2) &&
       throughBackend.any fun (n, ok) => ok && hasStr n "whose build reads a backend"),
   ("the door may read a module a backend reads, and not an unlisted one no backend reads",
     (doorFact sharedDoor).any (·.2) &&
       (doorFact unlistedDoor).any fun (n, ok) => !ok && hasStr n "LeanTex.Core.Helper"),
   ("a backend reaching a surface through a tool's module fails",
     (backendFact viaTool "LeanTex.Core.Html").any fun (n, ok) => !ok &&
       hasStr n "LeanTex.Core.Html → scripts.Mid → LeanTex.Core.Parse"),
   ("a core module above a backend reaching a surface fails, and one outside the core does not",
     aboveCore.any (fun (n, ok) => !ok && hasStr n "LeanTex.Core.Above → LeanTex.Core.Lex") &&
       !above.any fun (n, ok) => !ok && hasStr n "Synthetic.Above"),
   ("a floor its imports keep passes",
     (floorFact floorKept "LeanTex.Core.Oklab").any (·.2)),
   ("a floor broken by a direct import fails, naming the chain",
     (floorFact floorBroken "LeanTex.Core.Oklab").any fun (n, ok) => !ok &&
       hasStr n "LeanTex.Core.Oklab → LeanTex.Core.Ir"),
   ("a floor broken through a dependency's import all fails",
     (floorFact floorThrough "LeanTex.Core.Contrast").any fun (n, ok) => !ok &&
       hasStr n "LeanTex.Core.Contrast → LeanTex.Core.Theme → LeanTex.Core.Layout")]

end Tests.BuildGraph

/-- Every library and test file is a `module` but the declared shims, and the shims, each large
file's private reads and its private readers match the declared lists; no backend, nor a core module
above one, reaches a surface, and every import floor holds. -/
def buildGraphChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, ok) in ← Tests.BuildGraph.selfTest do
    check ref s!"build graph model: {name}" ok
  for (name, ok) in ← Tests.BuildGraph.judge (← Tests.BuildGraph.sources)
      (← Tests.BuildGraph.scriptSources) do
    check ref s!"build graph: {name}" ok
