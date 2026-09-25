/-
The blocker ranking: which missing construct holds back the most documents?

  lake env lean --run scripts/blockers.lean --screen <dir> <out>   lualatex-buildable list
  lake env lean --run scripts/blockers.lean --rank <list>          rank, write the table
  lake env lean --run scripts/blockers.lean --selftest             the ranking arithmetic
                                                                  and the confinement rule

A report, never a gate. `--screen` needs lualatex and a corpus on the host;
`--rank` needs the corpus files it names. Neither runs in `lake test`.

*Confinement is structural, not stated.* A construct name is published only
when something public defines it: a TeX primitive, the LaTeX kernel, or a
class or package file `kpsewhich` resolved out of the TeX installation.
Everything else — a macro the document defined, and every name the definer
scan could not attribute — is folded into one aggregate row per owner,
carrying counts and no names. So pointing `--rank` at the private reference
corpus cannot write a private document's macro names into the tree: not
because a docstring asks it not to, but because `publish` has no branch that
would. `--selftest` breaks it once against a synthetic corpus whose document
defines its own distinctive name.

*The denominator is what lualatex builds.* A document lualatex cannot
compile with `-halt-on-error` says nothing about this engine, so `--screen`
drops it before anything is counted, and the surviving count is published
beside the ranking.

*A kill is not a verdict.* `--screen` bounds its own pool and records a run
the timeout killed in a third list, neither buildable nor unbuildable. An
unbounded pool over a real corpus means contention, and contention under a
per-file timeout silently shrinks the denominator — the tree's rule for
cached tool answers, applied to a screen: an attempt the tool never finished
is a fact about the machine, not about the document.

*What a blocker is, and how that differs from T0.* The constructs the engine
does not know: the subjects of W0301 (unknown command) and W0302 (unknown
environment), read from the structured `Diag.subject` rather than from
message text, and kept with the kind that namespaces them — `verse` the
environment and `em` the command are two constructs, not one. Losses the
engine *names* are deliberately not blockers here: a refusal with a code is a
decision on the record, and the ranking is for the names nothing answers.

So "blocked" is narrower than T0. A document that elaborates with errors and
no unknown name is unblocked here and still fails T0, and implementing a
construct with `sole` weight *n* makes *n* documents free of unknown names,
not *n* documents T0-clean. The gap is published as a number beside the
ranking rather than left as a caveat.

*How they are ranked* (flashtex's two numbers, for the same reason):

  * `sole` — documents this construct alone blocks. Implementing it makes
    those documents clean of unknown names. This is the number that buys
    something today.
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

/-- What one screening run learned. A kill is its own answer: `timeout`
exits 124 when it kills the child, and that says nothing about the
document. -/
inductive Screened where
  | builds
  | fails
  | killed
deriving Inhabited, BEq

/-- Run lualatex on one file in a scratch directory and report what
happened. Nothing is read back but the exit code, so a document's text never
enters this process. -/
def buildsWithLualatex (path : String) : IO Screened := do
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  if dir.isEmpty then return .killed
  try
    let _ ← IO.Process.output { cmd := "cp", args := #[path, dir ++ "/doc.tex"] }
    let r ← IO.Process.output
      { cmd := "timeout", cwd := some dir,
        args := #["60", "lualatex", "-halt-on-error", "-interaction=nonstopmode", "doc.tex"] }
    if r.exitCode == 0 then return .builds
    -- 124 is `timeout`'s own "I killed it"; 137 is a SIGKILL after that.
    else if r.exitCode == 124 || r.exitCode == 137 then return .killed
    else return .fails
  catch _ => return .killed
  finally
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir] }

/-- How many lualatex runs stand at once. The host has cores, but a screen
that starts one process per candidate turns a large corpus into contention,
and contention under a per-file timeout is indistinguishable from a document
that does not build. Bounded, so a kill means the document really took a
minute. -/
def poolSize : Nat := 16

/-- Screen a directory of `.tex` files through a bounded pool. Two lists are
written: the buildable ones at `out`, and the killed ones at `out.killed` —
never merged into either verdict, so a busy minute cannot condemn a document
that compiles. -/
def screen (dir out : String) : IO UInt32 := do
  let files := (← System.FilePath.walkDir dir).filter (·.toString.endsWith ".tex")
  let sorted := files.map (·.toString) |>.qsort (· < ·)
  IO.println s!"blockers: screening {sorted.size} candidate(s) with lualatex, \
{poolSize} at a time"
  let mut ok : Array String := #[]
  let mut killed : Array String := #[]
  let mut failed := 0
  let mut i := 0
  while i < sorted.size do
    let stop := min sorted.size (i + poolSize)
    let mut batch : Array (String × Task (Except IO.Error Screened)) := #[]
    for k in [i:stop] do
      batch := batch.push (sorted[k]!, ← IO.asTask (buildsWithLualatex sorted[k]!))
    for (f, t) in batch do
      match t.get with
      | .ok .builds => ok := ok.push f
      | .ok .fails => failed := failed + 1
      | .ok .killed => killed := killed.push f
      | .error _ => killed := killed.push f
    i := stop
  IO.FS.writeFile out (ok.foldl (fun acc f => acc ++ f ++ "\n") "")
  IO.FS.writeFile (out ++ ".killed") (killed.foldl (fun acc f => acc ++ f ++ "\n") "")
  IO.println s!"blockers: {ok.size} build, {failed} do not, {killed.size} were killed \
(in {out}.killed, counted as neither)"
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

/-- Every construct one document is blocked on, deduplicated, each kept with
the kind that namespaces it: `ctrl` and `env` are two namespaces, so `verse`
the environment and `em` the command are two work items. -/
def blockersOf (path : String) : IO (Array (String × String)) := do
  let text ← IO.FS.readFile path
  let ds := (Elab.run path text).2
  let mut out : Array (String × String) := #[]
  for d in ds do
    unless blockerCodes.contains d.code do continue
    match d.subject with
    | none => pure ()
    | some s =>
      match constructOf s with
      | none => pure ()
      | some (kind, name) => if !out.contains (kind, name) then out := out.push (kind, name)
  return out.qsort (fun a b => a.1 ++ a.2 < b.1 ++ b.2)

/-- Documents that elaborate with an error and no unknown name: unblocked by
this table's rule and still short of T0. The number that says how far
"blocked" is from "fails the parity ladder's first level". -/
def erroredNotBlocked (path : String) : IO Bool := do
  let text ← IO.FS.readFile path
  let ds := (Elab.run path text).2
  let unknowns := ds.filter (fun d => blockerCodes.contains d.code)
  return unknowns.isEmpty && ds.any (fun d => d.severity == .error)

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

/-- Does this source define the command? The definer spellings a `.cls` or
`.sty` actually uses, in both the braced and the bare form — `\newcommand`
and `\DeclareRobustCommand` are written both ways, `\let` takes no `=`, and
expl3 declares through `\cs_new:Npn`. The first version matched only the
braced forms with an `=` on `\let`, which is why `\hspace`, `\em`,
`\markboth`, `\markright`, `\enlargethispage` and `\tt` came out
unattributed: every one of them is declared in `latex.ltx` in a form the
scan did not read.

A name defined by expansion is still missed, and such a construct falls
through to the next layer or to `unattributed` — visible as a gap in the
table rather than as a guess. -/
def defines (src name : String) : Bool :=
  let n := "\\" ++ name
  let braced := ["newcommand", "newcommand*", "renewcommand", "renewcommand*",
    "providecommand", "providecommand*", "DeclareRobustCommand", "DeclareRobustCommand*",
    "NewDocumentCommand", "DeclareDocumentCommand", "newrobustcmd", "newrobustcmd*"]
  -- A bare definer is followed by the control sequence directly, so the
  -- pattern must not also match a longer name: `\newcommand\emph` does not
  -- define `\em`. The character after the name decides.
  let bareHeads := braced ++ ["def", "let", "cs_new:Npn", "cs_new_protected:Npn",
    "cs_set:Npn", "cs_set_protected:Npn", "cs_new_nopar:Npn", "cs_gset:Npn"]
  let envForms := ["\\newenvironment{" ++ name ++ "}", "\\newenvironment*{" ++ name ++ "}",
    "\\renewenvironment{" ++ name ++ "}", "\\NewDocumentEnvironment{" ++ name ++ "}"]
  let bracedForms := braced.map (fun h => "\\" ++ h ++ "{" ++ n ++ "}")
  if (bracedForms ++ envForms).any (fun pat => (src.splitOn pat).length > 1) then true
  else
    -- `\def\name{`, `\def\name#1`, `\let\name\other`, `\cs_new:Npn \name`:
    -- the definer, then the control sequence, then a character that cannot
    -- continue the name.
    bareHeads.any fun h =>
      let pats := ["\\" ++ h ++ n, "\\" ++ h ++ " " ++ n]
      pats.any fun p =>
        (src.splitOn p).drop 1 |>.any fun after =>
          match after.toList with
          | [] => true
          | c :: _ => !c.isAlpha

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
  kind : String
  construct : String
  owner : String
  sole : Nat
  /-- Σ 1/|blockers|, in thousandths. -/
  share : Nat
  docs : Nat
deriving Inhabited, BEq

/-- **The confinement rule, as a function of the owner alone.** A construct
name may be published only when something public defines it: a TeX
primitive, the LaTeX kernel, or a class or package file `kpsewhich` resolved
out of the TeX installation. `--rank` runs with the repository as its working
directory, so a `.cls` sitting beside a private document is not on
`kpsewhich`'s path and cannot become a `class:` attribution.

Everything else is a name the corpus itself chose. There is no branch that
writes one, so the rule holds for a corpus this code has never seen. -/
def publishable (owner : String) : Bool :=
  owner == "primitive" || owner == "kernel"
    || owner.startsWith "class:" || owner.startsWith "pkg:"

/-- The rows as written: publishable ones by name, the rest folded into one
aggregate row per owner, carrying counts and no names. The number of names
folded away is reported in the header, so the table says how much of itself
it is not showing. -/
def publish (rows : Array Rank) : Array Rank × Nat := Id.run do
  let mut out : Array Rank := #[]
  let mut folded := 0
  for r in rows do
    if publishable r.owner then out := out.push r
    else
      folded := folded + 1
      let key := "(" ++ r.owner ++ ")"
      match out.findIdx? (fun q => q.construct == key) with
      | some i =>
        let q := out[i]!
        let bumped : Rank :=
          { kind := q.kind, construct := q.construct, owner := q.owner,
            sole := q.sole + r.sole, share := q.share + r.share, docs := q.docs + r.docs }
        out := out.set! i bumped
      | none =>
        let fresh : Rank :=
          { kind := "aggregate", construct := key, owner := r.owner,
            sole := r.sole, share := r.share, docs := r.docs }
        out := out.push fresh
  return (out, folded)

/-- Accumulate `sole`, `share` and the document count from one document's
blocker set. A document with one blocker gives that construct a whole
`sole` and a whole 1000 thousandths; a document with n blockers gives each
1000/n and no `sole`. -/
def tally (acc : Array Rank) (blockers : Array (String × String))
    (owners : Array (String × String)) : Array Rank := Id.run do
  let n := blockers.size
  if n == 0 then return acc
  let piece := 1000 / n
  let mut out := acc
  for (kind, b) in blockers do
    let owner := (owners.find? (fun p => p.1 == b)).map (·.2) |>.getD "unattributed"
    let add : Rank :=
      { kind, construct := b, owner, sole := if n == 1 then 1 else 0,
        share := piece, docs := 1 }
    match out.findIdx? (fun r => r.construct == b && r.kind == kind) with
    | some i =>
      let r := out[i]!
      let bumped : Rank :=
        { kind := r.kind, construct := r.construct, owner := r.owner,
          sole := r.sole + add.sole, share := r.share + add.share, docs := r.docs + 1 }
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
  let mut erroredClean := 0
  for path in list do
    let fp : System.FilePath := path
    unless (← fp.pathExists) do continue
    seen := seen + 1
    let bs ← blockersOf path
    if bs.isEmpty then
      if ← erroredNotBlocked path then erroredClean := erroredClean + 1
      continue
    blocked := blocked + 1
    let docText ← IO.FS.readFile fp
    let mut owners : Array (String × String) := #[]
    for (_, b) in bs do
      owners := owners.push (b, ← ownerOf cache docText b)
    acc := tally acc bs owners
  let (published, folded) := publish acc
  let sorted := published.qsort fun a b =>
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
     # between its blockers. docs: documents it appears in. kind: the subject\n\
     # namespace (ctrl | env | aggregate). owner: what defines it (primitive |\n\
     # kernel | class:<c> | pkg:<p>, or an aggregate row for the rest).\n\
     # A construct is named only when something public defines it; a name the\n\
     # document itself chose, or one the definer scan could not attribute, is\n\
     # folded into an aggregate row carrying counts and no name. No corpus\n\
     # document is committed and this table carries no document text.\n\
     # \"Blocked\" means \"has at least one unknown construct\", which is narrower\n\
     # than the parity ladder's T0: a document that elaborates with errors and\n\
     # no unknown name is unblocked here and still fails T0.\n" ++
    s!"# corpus: {seen} lualatex-buildable document(s), {blocked} with at least one blocker\n" ++
    s!"# errored but unblocked: {erroredClean} document(s) — the T0 gap this table \
does not rank\n" ++
    s!"# names folded into aggregate rows: {folded}\n" ++
    s!"# screened-by: {((lua.splitOn "\n").headD "").trimAscii.toString}\n" ++
    s!"# date: {date.trimAscii.toString}\n" ++
    "kind\tconstruct\towner\tsole\tshare\tdocs\n"
  let body := sorted.foldl
    (fun acc r => acc ++ r.kind ++ "\t" ++ r.construct ++ "\t" ++ r.owner ++ "\t"
      ++ toString r.sole ++ "\t" ++ toString r.share ++ "\t" ++ toString r.docs ++ "\n") head
  IO.FS.createDirAll "tests/coverage"
  IO.FS.writeFile blockersPath body
  IO.println s!"blockers: wrote {blockersPath} — {sorted.size} row(s) over \
{seen} document(s), {blocked} blocked, {folded} name(s) folded away"
  for r in sorted.toList.take 20 do
    IO.println s!"  {r.sole}\t{r.share}\t{r.docs}\t{r.kind}:{r.construct}\t{r.owner}"
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
  let one := tally #[] #[("ctrl", "a")] #[("a", "kernel")]
  expect "a sole blocker takes the whole document"
    (one == #[{ kind := "ctrl", construct := "a", owner := "kernel", sole := 1,
                share := 1000, docs := 1 }])
  -- One document, four blockers: no sole, a quarter each.
  let four := tally #[] (#["a", "b", "c", "d"].map (("ctrl", ·))) #[]
  expect "four blockers split the document" (four.all fun r => r.sole == 0 && r.share == 250)
  expect "every blocker is recorded" (four.size == 4)
  -- Two documents: the same construct accumulates.
  let twice := tally one #[("ctrl", "a")] #[("a", "kernel")]
  expect "a construct blocking twice doubles"
    (twice == #[{ kind := "ctrl", construct := "a", owner := "kernel", sole := 2,
                  share := 2000, docs := 2 }])
  expect "an empty blocker set changes nothing" (tally one #[] #[] == one)
  -- The kind namespaces the construct: a command and an environment of the
  -- same name are two work items, which the first version merged into one.
  let bothKinds := tally #[] #[("ctrl", "em"), ("env", "em")] #[]
  expect "a command and an environment of one name are two rows" (bothKinds.size == 2)
  -- The confinement rule, broken in both directions.
  expect "a public owner may be named"
    (publishable "kernel" && publishable "primitive" && publishable "class:article"
      && publishable "pkg:amsmath")
  expect "a corpus-chosen name may not be"
    (!publishable "document" && !publishable "unattributed" && !publishable "")
  let mixed : Array Rank :=
    #[{ kind := "ctrl", construct := "hspace", owner := "kernel", sole := 3,
        share := 3000, docs := 3 },
      { kind := "ctrl", construct := "zzPrivateMacro", owner := "document", sole := 1,
        share := 1000, docs := 1 },
      { kind := "ctrl", construct := "zzOtherPrivate", owner := "document", sole := 0,
        share := 500, docs := 1 },
      { kind := "env", construct := "zzUnknownThing", owner := "unattributed", sole := 2,
        share := 700, docs := 2 }]
  let (pub, folded) := publish mixed
  expect "folding reports how many names it removed" (folded == 3)
  expect "a private name cannot reach the table"
    (!pub.any fun r => r.construct == "zzPrivateMacro" || r.construct == "zzOtherPrivate"
      || r.construct == "zzUnknownThing")
  expect "a public name survives folding" (pub.any fun r => r.construct == "hspace")
  expect "an aggregate row keeps the counts"
    ((pub.find? (·.construct == "(document)")).map (fun r => (r.sole, r.share, r.docs))
      == some (1, 1500, 2))
  expect "each non-public owner gets its own aggregate row"
    ((pub.filter (·.kind == "aggregate")).size == 2)
  -- The definer scan, in the spellings latex.ltx really uses.
  expect "a braced newcommand defines" (defines "\\newcommand{\\foo}[1]{x}" "foo")
  expect "a bare newcommand defines" (defines "\\newcommand\\foo{x}" "foo")
  expect "def defines" (defines "\\def\\foo#1{x}" "foo")
  expect "let defines without an equals sign" (defines "\\let\\foo\\bar" "foo")
  expect "DeclareRobustCommand defines bare" (defines "\\DeclareRobustCommand\\foo{x}" "foo")
  expect "expl3 defines" (defines "\\cs_new:Npn \\foo #1 {x}" "foo")
  expect "an environment definer defines" (defines "\\newenvironment{bar}{}{}" "bar")
  expect "a mention is not a definition" (defines "we use \\foo here" "foo" == false)
  expect "a longer name is not this one" (defines "\\newcommand\\foobar{x}" "foo" == false)
  -- The load scan.
  expect "usepackage lists are read"
    (loadsOf "\\usepackage{amsmath,graphicx}" == #["amsmath", "graphicx"])
  expect "an option group is skipped"
    (loadsOf "\\usepackage[margin=1in]{geometry}" == #["geometry"])
  expect "a class is a load" (loadsOf "\\documentclass{article}" == #["article"])
  -- A kill is not a verdict.
  expect "the three screening answers are distinct"
    (Screened.builds != Screened.fails && Screened.fails != Screened.killed
      && Screened.builds != Screened.killed)
  -- The confinement rule, end to end, against a synthetic corpus whose
  -- document defines a name of its own: the ranking must be writable and the
  -- name must not appear in what it writes.
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  unless dir.isEmpty do
    let doc := dir ++ "/synthetic.tex"
    IO.FS.writeFile doc
      "\\documentclass{article}\n\
       \\let\\zzsyntheticprivatemacro\\relax\n\
       \\begin{document}\n\
       \\zzsyntheticprivatemacro\\ and \\zzsyntheticunattributed\\ and \\hspace{1em} here.\n\
       \\end{document}\n"
    let listFile := dir ++ "/list.txt"
    IO.FS.writeFile listFile (doc ++ "\n")
    let cache ← IO.mkRef (#[] : Array (String × String))
    let bs ← blockersOf doc
    let docText ← IO.FS.readFile doc
    let mut owners : Array (String × String) := #[]
    for (_, b) in bs do
      owners := owners.push (b, ← ownerOf cache docText b)
    let (pub, _) := publish (tally #[] bs owners)
    let rendered := pub.foldl (fun acc r => acc ++ r.kind ++ r.construct ++ r.owner) ""
    expect "the synthetic document's own names are blockers"
      (bs.any (·.2 == "zzsyntheticprivatemacro") && bs.any (·.2 == "zzsyntheticunattributed"))
    expect "the definer scan attributes one of them to the document"
      ((owners.find? (·.1 == "zzsyntheticprivatemacro")).map (·.2) == some "document")
    expect "and neither can reach the written table"
      ((rendered.splitOn "zzsynthetic").length == 1)
    let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir] }
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
