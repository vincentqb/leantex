/-
The blocker ranking: which missing construct holds back the most documents?

  lake env lean --run scripts/blockers.lean --screen <dir> <out>   lualatex-buildable list
  lake env lean --run scripts/blockers.lean --rank <list>          rank, write the table
  lake env lean --run scripts/blockers.lean --selftest             the ranking arithmetic

A report, never a gate. `--screen` needs lualatex and a corpus on the host;
`--rank` needs the corpus files it names. Neither runs in `lake test`, and
no corpus document is ever committed — only the aggregated table
(`tests/coverage/blockers.tsv`), which carries no document text.

*The denominator is what lualatex builds.* A document lualatex cannot
compile with `-halt-on-error` says nothing about this engine, so `--screen`
drops it before anything is counted, and the surviving count is published
beside the ranking.

*What a blocker is.* The constructs the engine does not know: the subjects
of W0301 (unknown command) and W0302 (unknown environment), read from the
structured `Diag.subject` rather than from message text. Losses the engine
*names* are deliberately not blockers here — a refusal with a code is a
decision on the record, and the ranking is for the names nothing answers.

*How they are ranked* (flashtex's two numbers, for the same reason):

  * `sole` — documents this construct alone blocks. Implementing it makes
    those documents clean. This is the number that buys something today.
  * `share` — Σ 1/|blockers| over the documents it blocks, in thousandths.
    It spreads a shared document's weight, so a construct that appears in
    many crowded documents still ranks, and one that appears in a single
    document with forty other gaps does not dominate.

*Attribution.* A construct is grouped by what defines it, so the ranking
reads as work items rather than as names: the precedence is primitive →
the document's own macro → a class the document loads → the LaTeX kernel →
a package the document loads → unattributed. Ordering matters: a document
that defines a name locally is not a package gap, and a name in both a
class and a package belongs to the class, which the document cannot drop.
-/
import LeanTex

open LeanTex.Core

def blockersPath : String := "tests/coverage/blockers.tsv"

/-- The unknown-construct codes: the engine met a name nothing answers. -/
def blockerCodes : List String := ["W0301", "W0302"]

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

-- ## Screening: only what lualatex builds

/-- Run lualatex on one file in a scratch directory and report whether it
built. Nothing is read back but the exit code, so a document's text never
enters this process. -/
def buildsWithLualatex (path : String) : IO Bool := do
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  if dir.isEmpty then return false
  try
    let _ ← IO.Process.output { cmd := "cp", args := #[path, dir ++ "/doc.tex"] }
    let r ← IO.Process.output
      { cmd := "timeout", cwd := some dir,
        args := #["60", "lualatex", "-halt-on-error", "-interaction=nonstopmode", "doc.tex"] }
    return r.exitCode == 0
  catch _ => return false
  finally
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir] }

/-- Screen a directory of `.tex` files, in parallel: the host has cores and
each lualatex run is independent. The list is written, so ranking can be
rerun without paying for the screen again. -/
def screen (dir out : String) : IO UInt32 := do
  let files := (← System.FilePath.walkDir dir).filter (·.toString.endsWith ".tex")
  let sorted := files.map (·.toString) |>.qsort (· < ·)
  IO.println s!"blockers: screening {sorted.size} candidate(s) with lualatex"
  let mut tasks : Array (String × Task (Except IO.Error Bool)) := #[]
  for f in sorted do
    tasks := tasks.push (f, ← IO.asTask (buildsWithLualatex f))
  let mut ok : Array String := #[]
  for (f, t) in tasks do
    match t.get with
    | .ok true => ok := ok.push f
    | _ => pure ()
  IO.FS.writeFile out (ok.foldl (fun acc f => acc ++ f ++ "\n") "")
  IO.println s!"blockers: {ok.size} of {sorted.size} build with lualatex -halt-on-error"
  return 0

-- ## The blockers of one document

/-- Strip the namespace from a subject key: an unknown command's key is
`ctrl:\name`, an environment's `env:{name}`. The bare construct is what a
reader wants; the prefix is kept as the kind. -/
def constructOf (subject : String) : Option (String × String) :=
  match subject.splitOn ":" with
  | kind :: rest =>
    let name := String.intercalate ":" rest
    -- A subject carrying a control character is a line break or a
    -- mis-spelled key, not a construct a reader could implement; drop it
    -- rather than publish a row nobody can act on.
    if name.isEmpty || name.any (fun c => Char.toNat c < 32) then none else some (kind, name)
  | [] => none

/-- Every construct one document is blocked on, deduplicated. -/
def blockersOf (path : String) : IO (Array String) := do
  let text ← IO.FS.readFile path
  let ds := (Elab.run path text).2
  let mut out : Array String := #[]
  for d in ds do
    unless blockerCodes.contains d.code do continue
    match d.subject with
    | none => pure ()
    | some s =>
      match constructOf s with
      | none => pure ()
      | some (_, name) => if !out.contains name then out := out.push name
  return out.qsort (· < ·)

-- ## Attribution

/-- The package and class names a document loads. -/
def loadsOf (text : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for marker in ["\\usepackage", "\\RequirePackage", "\\documentclass"] do
    let parts := text.splitOn marker
    for p in parts.drop 1 do
      -- Skip an optional argument, then read the brace group.
      let afterOpt :=
        if (p.trimAscii.toString).startsWith "[" then
          ((p.splitOn "]").drop 1 |> String.intercalate "]")
        else p
      match (afterOpt.splitOn "{").drop 1 |>.head? with
      | none => pure ()
      | some g =>
        for name in ((g.splitOn "}").headD "").splitOn "," do
          let n := name.trimAscii.toString
          if !n.isEmpty && !out.contains n then out := out.push n
  return out

/-- Does this source define the command? The three definer spellings a
`.sty` actually uses; a name defined by `\let` or by expansion is missed,
and such a construct falls through to the next layer or to
`unattributed` — visible as a gap in the table rather than as a guess. -/
def defines (src name : String) : Bool :=
  let n := "\\" ++ name
  [ "\\newcommand{" ++ n ++ "}", "\\newcommand*{" ++ n ++ "}",
    "\\newcommand " ++ n, "\\renewcommand{" ++ n ++ "}",
    "\\DeclareRobustCommand{" ++ n ++ "}", "\\DeclareRobustCommand*{" ++ n ++ "}",
    "\\def" ++ n ++ "{", "\\def" ++ n ++ "#", "\\def" ++ n ++ " ",
    "\\let" ++ n ++ "=", "\\newenvironment{" ++ name ++ "}",
    "\\newenvironment*{" ++ name ++ "}", "\\NewDocumentCommand{" ++ n ++ "}",
    "\\NewDocumentEnvironment{" ++ name ++ "}"
  ].any (fun pat => (src.splitOn pat).length > 1)

/-- Resolve a file through kpsewhich and read it, once. -/
def sourceOf (cache : IO.Ref (Array (String × String))) (file : String) : IO String := do
  match (← cache.get).find? (fun p => p.1 == file) with
  | some (_, src) => return src
  | none =>
    let mut src := ""
    try
      let r ← IO.Process.output { cmd := "kpsewhich", args := #[file] }
      let path := r.stdout.trimAscii.toString
      unless path.isEmpty do src ← IO.FS.readFile path
    catch _ => pure ()
    cache.modify (·.push (file, src))
    return src

/-- Where a construct comes from, by the declared precedence. -/
def ownerOf (cache : IO.Ref (Array (String × String))) (docText name : String) :
    IO String := do
  if Compat.texPrimitives.contains name then return "primitive"
  if defines docText name then return "document"
  let loads := loadsOf docText
  for cls in loads do
    if defines (← sourceOf cache (cls ++ ".cls")) name then return "class:" ++ cls
  if defines (← sourceOf cache "latex.ltx") name then return "kernel"
  for pkg in loads do
    if defines (← sourceOf cache (pkg ++ ".sty")) name then return "pkg:" ++ pkg
  return "unattributed"

-- ## The ranking

structure Rank where
  construct : String
  owner : String
  sole : Nat
  /-- Σ 1/|blockers|, in thousandths. -/
  share : Nat
  docs : Nat
deriving Inhabited, BEq

/-- Accumulate `sole`, `share` and the document count from one document's
blocker set. A document with one blocker gives that construct a whole
`sole` and a whole 1000 thousandths; a document with n blockers gives each
1000/n and no `sole`. -/
def tally (acc : Array Rank) (blockers : Array String) (owners : Array (String × String)) :
    Array Rank := Id.run do
  let n := blockers.size
  if n == 0 then return acc
  let piece := 1000 / n
  let mut out := acc
  for b in blockers do
    let owner := (owners.find? (fun p => p.1 == b)).map (·.2) |>.getD "unattributed"
    let add : Rank :=
      { construct := b, owner, sole := if n == 1 then 1 else 0, share := piece, docs := 1 }
    match out.findIdx? (fun r => r.construct == b) with
    | some i =>
      let r := out[i]!
      let bumped : Rank :=
        { construct := r.construct, owner := r.owner, sole := r.sole + add.sole,
          share := r.share + add.share, docs := r.docs + 1 }
      out := out.set! i bumped
    | none => out := out.push add
  return out

def rank (listPath : String) : IO UInt32 := do
  unless (← System.FilePath.pathExists listPath) do
    return (← die 3 s!"blockers: {listPath} is missing — run --screen first")
  let list : List String := ((← IO.FS.readFile listPath).splitOn "\n").filterMap fun l =>
    let l := l.trimAscii.toString
    if l.isEmpty then none else some l
  let cache ← IO.mkRef (#[] : Array (String × String))
  let mut acc : Array Rank := #[]
  let mut seen := 0
  let mut blocked := 0
  for path in list do
    let fp : System.FilePath := path
    unless (← fp.pathExists) do continue
    seen := seen + 1
    let bs ← blockersOf path
    if bs.isEmpty then continue
    blocked := blocked + 1
    let docText ← IO.FS.readFile fp
    let mut owners : Array (String × String) := #[]
    for b in bs do
      owners := owners.push (b, ← ownerOf cache docText b)
    acc := tally acc bs owners
  let sorted := acc.qsort fun a b =>
    if a.sole != b.sole then a.sole > b.sole
    else if a.share != b.share then a.share > b.share
    else a.construct < b.construct
  let date := (← IO.Process.output { cmd := "date", args := #["-u", "+%Y-%m-%d"] }).stdout
  let lua := (← IO.Process.output { cmd := "lualatex", args := #["--version"] }).stdout
  let head :=
    "# The blocker ranking: constructs nothing in this engine answers, over a\n\
     # public corpus, ranked by the documents they hold back. A report, never a\n\
     # gate. sole: documents this construct alone blocks. share: thousandths of\n\
     # a document summed over the documents it blocks, splitting each document\n\
     # between its blockers. docs: documents it appears in. owner: what defines\n\
     # it (primitive | document | class:<c> | kernel | pkg:<p> | unattributed).\n\
     # No corpus document is committed; this table carries no document text.\n" ++
    s!"# corpus: {seen} lualatex-buildable document(s), {blocked} with at least one blocker\n" ++
    s!"# screened-by: {((lua.splitOn "\n").headD "").trimAscii.toString}\n" ++
    s!"# date: {date.trimAscii.toString}\n" ++
    "construct\towner\tsole\tshare\tdocs\n"
  let body := sorted.foldl
    (fun acc r => acc ++ r.construct ++ "\t" ++ r.owner ++ "\t" ++ toString r.sole ++ "\t"
      ++ toString r.share ++ "\t" ++ toString r.docs ++ "\n") head
  IO.FS.createDirAll "tests/coverage"
  IO.FS.writeFile blockersPath body
  IO.println s!"blockers: wrote {blockersPath} — {sorted.size} construct(s) over \
{seen} document(s), {blocked} blocked"
  for r in sorted.toList.take 20 do
    IO.println s!"  {r.sole}\t{r.share}\t{r.docs}\t{r.construct}\t{r.owner}"
  return 0

-- ## Selftest

def selftest : IO UInt32 := do
  let ref ← IO.mkRef (#[] : Array String)
  let expect (name : String) (ok : Bool) : IO Unit := do
    unless ok do ref.modify (·.push name)
  expect "a subject's namespace is stripped"
    (constructOf "ctrl:\\foo" == some ("ctrl", "\\foo"))
  expect "an empty name is no construct" (constructOf "ctrl:" == none)
  expect "a control character is no construct" (constructOf "ctrl:\\\n" == none)
  -- One document, one blocker: a whole sole and a whole share.
  let one := tally #[] #["a"] #[("a", "kernel")]
  expect "a sole blocker takes the whole document"
    (one == #[{ construct := "a", owner := "kernel", sole := 1, share := 1000, docs := 1 }])
  -- One document, four blockers: no sole, a quarter each.
  let four := tally #[] #["a", "b", "c", "d"] #[]
  expect "four blockers split the document" (four.all fun r => r.sole == 0 && r.share == 250)
  expect "every blocker is recorded" (four.size == 4)
  -- Two documents: the same construct accumulates.
  let twice := tally one #["a"] #[("a", "kernel")]
  expect "a construct blocking twice doubles"
    (twice == #[{ construct := "a", owner := "kernel", sole := 2, share := 2000, docs := 2 }])
  expect "an empty blocker set changes nothing" (tally one #[] #[] == one)
  -- The definer scan.
  expect "newcommand defines" (defines "\\newcommand{\\foo}[1]{x}" "foo")
  expect "def defines" (defines "\\def\\foo#1{x}" "foo")
  expect "an environment definer defines" (defines "\\newenvironment{bar}{}{}" "bar")
  expect "a mention is not a definition" (defines "we use \\foo here" "foo" == false)
  -- The load scan.
  expect "usepackage lists are read"
    (loadsOf "\\usepackage{amsmath,graphicx}" == #["amsmath", "graphicx"])
  expect "an option group is skipped"
    (loadsOf "\\usepackage[margin=1in]{geometry}" == #["geometry"])
  expect "a class is a load" (loadsOf "\\documentclass{article}" == #["article"])
  let bad ← ref.get
  if bad.isEmpty then
    IO.println "blockers: selftest ok"
    return 0
  else
    for b in bad do IO.eprintln ("blockers: selftest failed: " ++ b)
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--screen", dir, out] => screen dir out
  | ["--rank", list] => rank list
  | ["--selftest"] => selftest
  | _ => die 3 "usage: blockers [--screen <dir> <out> | --rank <list> | --selftest]"
