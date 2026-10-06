/-
Documented-command coverage: how much of LaTeX does this engine answer?

  lake env lean --run scripts/coverage.lean                  regenerate the scoreboard (Scoreboard.tierMain)
  lake env lean --run scripts/coverage.lean --check          measure and hold it to the committed baseline
  lake env lean --run scripts/coverage.lean --selftest       the rung rule, the guards, and the corpus control
  lake env lean --run scripts/coverage.lean --report         the per-item detail and the drift audit
  lake env lean --run scripts/coverage.lean --denominator <latex2e.texi>
                                                             rebuild tests/coverage/latex2e-index.txt

Each mode imports compiled script modules, which `scoreboard` builds before
fan-out; run standalone, build them first (`lake build ScriptsModules`).

The number is a measurement, never a list. Every rung comes from running
the engine's own dispatch over a probe of the command (`Elab.run`), so the
published figure cannot drift from what the engine does: a command the
dispatch stops recognising falls to `unknown` on the next run.

**The rung is read from the diagnostics whose subject names the construct.**
That qualification is the whole of the rule, and getting it wrong is how
the first version of this script charged its own malformed probes to the
commands it was probing: `\begin` read `unknown` because the probe's
environment `x` was unknown, and `\documentclass` read refused because the
probe put it in the body. W0301/W0302/W0012 carry `ctrl:<name>`,
`env:<name>` and `math:\<name>` subjects; the probe's own argument errors
(E0304 "missing argument", E0312 "block-level command used inline",
E0205) carry none. So a subjectless warning or error is the probe's
mistake, never the command's, and a name whose every shape produced only
those is `unprobed` — reported, not counted as a gap we owe.

**A construct is probed in the places LaTeX defines it in.** Many commands
exist only relative to a context and the engine models them only there:
the math parser answers `\frac` and `\sum`, the tabular answers `\hline`,
the float answers `\caption`, the list answers `\item`, a label answers
`\ref`, a declared title answers `\maketitle`. Probing every name
as a text-mode command in an article body is not a measurement of the
engine; it is a measurement of one dispatch table. The place family below
is uniform — no per-command table — and monotone: a place can only move a
name toward recognised, so it cannot inflate the count. The control is
`\zzfakecommandzz`, which stays `unknown` in every place, asserted in
`--selftest`.

The positive control is the repo's own golden corpus, read in both
directions. A name the probe calls `unknown` that a fixture uses where
elaboration never reports it unknown is a contradiction; so is a name the
probe puts on any other rung below the cut that a fixture uses where no
diagnostic names it at all. Every contradiction is explained or the
selftest fails, and every explanation is falsifiable: it says which side of
the contradiction the construct is on and carries a natural usage, which
must read the way that side says. The context-blind place list fails the
control; the shipped one passes it.

The denominator has two halves, and neither is chosen here.

*Kernel.* `tests/coverage/latex2e-index.txt`: the command names indexed by
the LaTeX2e unofficial reference manual (`@findex`, `@ftable` items, and
`@node` headings that name a command), each confirmed by lualatex to be a
control sequence LaTeX actually defines, and each classified by the meaning
lualatex gives it. `--denominator` rebuilds it from the manual alone: it
writes its own Lua probe and wrappers into a scratch directory and runs
lualatex over them, so the only input outside the tree is the manual, whose
sha256 the file records. The file carries its own row count and a body
stamp, which catch an accidental edit; what stops a deliberate prune is the
scoreboard, whose `<item>.rows` values may not fall without a human-written
`# lowered:` line.

*Packages.* `tests/compat-index/<pkg>.txt`, unchanged: each file is already
one package's documented command list sourced to a manual section, one row
per command with its verdict. Every row is in the denominator, including a
`divergence:<code>` row; only `impl` and `inert:` enter the numerator. The
rule is shared with the `compat` scoreboard tier. That tier ratchets both
numbers per package (`<p>.rows`, `<p>.impl`), while this tier ratchets their
aggregate as `packages.rows` and `packages.counted`, so the combined
headline cannot stale as provenance.

Exclusions, all stated and all derived:

  * math-mode symbol commands — the names lualatex reports as `math_given`
    (`\mathchardef`-style: `\alpha`, `\Gamma`, `\leq`). They are a font
    table, not a dispatch surface; counting them would inflate both halves
    of the fraction with the same work. The classification runs under a
    *bare* `article` and a bare `book`, no packages: under amsmath, seven
    of them (`\sum \int \prod \coprod \oint \bigcup \bigcap`) are macros
    instead, so a package-loaded confirmation makes the exclusion depend on
    what the confirmation happened to load.
  * the names `latex.ltx` defines only as an error — `\def\mho{\not@base\mho}`
    and ten like it, whose one expansion is "Command not provided in base
    LaTeX2e". lualatex reports them as macros, so the confirmation reads
    each macro's body and classifies these `not_base`. They are commands a
    package provides, and a package-provided command is counted in that
    package's half or not at all.
  * names the manual indexes that lualatex does not define under a bare
    `article` or `book` — index entries for environments, file extensions,
    counters, the `letter` class's commands, tabbing-local spellings, box
    parameters, and commands a package provides.
  * environments. The manual indexes them as `@findex <name> environment`;
    this extraction keeps `\name` tokens only, so `itemize` never enters the
    command denominator. An environment surface is the compat-index's job.

The scoreboard is `tests/scoreboard/coverage.tsv`, written and checked by
`Scoreboard.tierMain` like every other tier, under the `pairs counted/rows`
encoding: per kernel item (a manual chapter, or the register file),
`<item>.counted` is the count of names at `rewritten` or above and
`<item>.rows` the count of names in its denominator; `packages.counted` and
`packages.rows` hold the package aggregate. Both are higher-better under
the one ratchet, so a construct falling below the cut and a denominator row
deleted are both regressions, and the queue ranks each item by the names it
still owes.
-/
import LeanTex
import scripts.Board
import scripts.Rung

open LeanTex.Core

def denomPath : String := "tests/coverage/latex2e-index.txt"
def corpusDir : System.FilePath := "tests/corpus"

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

-- ## The kernel denominator, as committed data

/-- One kernel row: the command, the manual chapter that documents it, and
the meaning lualatex gives it (the class the exclusion and the register
grouping read). -/
structure KRow where
  name : String
  chapter : String
  cls : String
deriving Inhabited, BEq

/-- Commands whose lualatex meaning is a math symbol — excluded, by the
engine's own report rather than by a list kept here. -/
def mathClass : String := "math_given"

/-- Commands `latex.ltx` defines only as `\not@base\<name>` — an error
saying the command is not provided in base LaTeX2e. The confirmation's Lua
reads each macro's body and gives these their own class, so the exclusion
is lualatex's reading too and not a list kept here. -/
def notBaseClass : String := "not_base"

/-- The TeX register classes: a name that is a length, a glue or a counter
register, not a command with a dispatch. They are counted, because a
document that writes `\parindent` is owed an answer, but they are grouped
into their own scoreboard item rather than scattered through the chapters
that happen to document them: the work that answers one answers most. -/
def registerClasses : List String := ["assign_dimen", "assign_glue", "assign_int"]

def KRow.counted (r : KRow) : Bool := r.cls != mathClass && r.cls != notBaseClass

def KRow.isRegister (r : KRow) : Bool := registerClasses.contains r.cls

/-- The scoreboard item a row belongs to. -/
def KRow.item (r : KRow) : String :=
  if r.isRegister then "kernel/registers" else "kernel/" ++ r.chapter

/-- Split on the first tab, keeping the rest whole. -/
def tabs (line : String) : Array String :=
  (line.splitOn "\t").toArray.map (·.trimAscii.toString)

/-- A provenance line, as distinct from a data row: a `#` with no tab after
it. `\#` is a documented command and its row begins with `#`, so "starts
with `#`" alone silently dropped it — the row count check below is what
caught that, and it is why the count is checked at all. -/
def isComment (line : String) : Bool :=
  line.startsWith "#" && !(line.any (· == '\t'))

/-- The value of a `# key: value` provenance line. -/
def provValue (lines : Array String) (key : String) : Option String :=
  (lines.find? (·.startsWith ("# " ++ key ++ ": "))).map fun l =>
    (l.drop ("# " ++ key ++ ": ").length).toString.trimAscii.toString

structure Denom where
  provenance : Array String
  rows : Array KRow
deriving Inhabited

def parseDenom (text : String) : Except String Denom := do
  let mut provenance : Array String := #[]
  let mut rows : Array KRow := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    if isComment line then
      provenance := provenance.push line
      continue
    let f := tabs line
    if f.size != 3 then
      throw s!"denominator: want three tab-separated fields, got {f.size}: {line}"
    rows := rows.push { name := f[0]!, chapter := f[1]!, cls := f[2]! }
  if rows.isEmpty then throw "denominator: no rows"
  return { provenance, rows }

/-- The body a digest is taken over: the data rows, as written. -/
def denomBody (rows : Array KRow) : String :=
  rows.foldl (fun acc r => acc ++ r.name ++ "\t" ++ r.chapter ++ "\t" ++ r.cls ++ "\n") ""

/-- The committed body's fingerprint: rows, bytes and Adler-32, recorded in
the file's own header and re-derived by `--check`.

A change detector for an *accidental* edit, and no more: the file stamps
itself, so pruning rows and rewriting the two header lines passes it — a
review did exactly that and reached 555/1249. What makes a deliberate prune
a human act is the scoreboard: every item's `.rows` value is ratcheted, so
a smaller denominator is a fall that regeneration refuses to write without
a `# lowered:` line. Nothing this check prints hands a caller the value to
paste. -/
def bodyStamp (body : String) : String :=
  let b := body.toUTF8
  s!"{b.size} bytes, adler32 {Flate.hex16 (Flate.adler32 b).toUInt64}"

-- ## The rung: what this engine does with one construct

/-- The coverage cut: `rewritten` and above. A named refusal is better than
silence and is still not support — the same judgement `ink_covered_or_named`
makes one level up. -/
def Rung.counted (r : Rung) : Bool := r.level ≥ Rung.rewritten.level

def Rung.best (a b : Rung) : Rung := if a.level ≥ b.level then a else b

def Rung.worse (a b : Rung) : Rung := if a.level ≤ b.level then a else b

/-- The unknown-construct codes: the engine met a name nothing answers, in
text, where any command may stand. -/
def textUnknownCodes : List String := ["W0301", "W0302"]

/-- The math parser's decline. It reports a name it does not know with
W0012 (`math:\<name>`) rather than with W0301, and W0012's declared loss is
`degraded` — so reading it by its loss would move every name in the
`unknown` list into `degraded` (all 434, measured). The coverage number
would not budge, because
`degraded` is below the cut; what would be destroyed is the `unknown` list,
which is the queue the autonomy loop takes its next item from.

It is read as *no information* rather than as `unknown`, because a math
place is additive: it exists to rescue the constructs that live in math, and
its negative answer says only that this name is not one of them. Reading it
as `unknown` put `\documentclass` in the gap queue — every probe document
uses `\documentclass`, and what the math place had found was that it is not
a math construct. -/
def mathDeclinedCodes : List String := ["W0012"]

/-- The tokens the probe injects as arguments. A diagnostic whose subject
names one of them is a complaint about the probe's *own* operand — which is
evidence that the construct read its argument, and so that the dispatch
answered it.

Both halves matter. Charging a `\zzprobe` argument's own W0301 to the
construct discarded every definer shape, which is where `\setlength`,
`\newenvironment` and `\newcommand` are answered; and reading an operand
complaint as nothing at all left `\ref` in the gap queue, whose W0349 names
the key it could not resolve — a key the probe invented. -/
def probeOperands : List String := ["zzprobe", "x", "y", "o", "1", "1-2", "empty", "section", "3"]

/-- The bare name inside a namespaced subject key: `ctrl:zzprobe` and
`\zzprobe` both name `zzprobe`. -/
def bareSubject (s : String) : String :=
  let afterNs := match s.splitOn ":" with
    | _ :: rest => if rest.isEmpty then s else String.intercalate ":" rest
    | [] => s
  if afterNs.startsWith "\\" then (afterNs.drop 1).toString else afterNs

def isOperandDiag (d : Diag) : Bool :=
  match d.subject with
  | some s => probeOperands.contains (bareSubject s)
  | none => false

/-- The subject keys a diagnostic uses to name this construct. Measured,
not read off a docstring: `ctrl:` and `env:` carry the bare name and
`math:` carries the name with its backslash. -/
def aboutKeys (name : String) : List String :=
  ["ctrl:" ++ name, "env:" ++ name, "math:\\" ++ name]

def isAbout (name : String) (d : Diag) : Bool :=
  match d.subject with
  | some s => (aboutKeys name).contains s
  | none => false

/-- The rung one `Loss` puts a construct on, when a diagnostic carrying that
loss names the construct. The one place the ladder reads `Loss`. -/
def rungOfLoss : Loss → Rung
  | .dropped => .fails
  | .pending => .degraded
  | .degraded => .degraded
  | .standard => .native
  | .config => .skipped
  | .info => .rewritten

/-- One probe's rung, read from that probe's diagnostics.

The order of the readings is the rule, and each arm was put there by a
defect it answers.

1. A code whose subject names the construct decides through its `Loss`,
   except that a text-mode unknown is `unknown` and the math parser's
   decline is no information at all.
2. The engine's own note that it rewrote the construct to nothing
   (`ctrl:nothing:<name>`) is `skipped`: recognised and consumed, nothing
   modelled. Read as a rewrite, it counted `\noindent`, `\frenchspacing`
   and the ten `\Class…`/`\Package…` log commands as translated.
3. A subjectless warning or error is the probe's own shape, misplaced or
   malformed, and nothing downstream of it counts: `\documentclass{\zzprobe}`
   in a body draws E0312 for the misplacement *and* a W0301 for the argument
   that then leaked into text, and the second is not evidence of dispatch.
   It is read before a rewrite, so a rewrite whose document also errors
   without a subject does not count — a bare `\vspace` draws N0100 and
   E0320. Reading the rewrite first changed no verdict, which is why the
   order could be fixed before it mattered.
4. So is a complaint the place draws around any fragment — its own,
   measured once per place against a name nothing knows (`Place.own`):
   the dimension-operand place's W0314 for a width it cannot read. With it
   the probe perturbed its context, and a rewrite beside it says nothing.
   Reading it as nothing counted `\newenvironment` and `\renewenvironment`,
   whose only counting witness was that place.
5. Otherwise a rewrite note is positive whatever subject-carrying complaint
   stands beside it. The complaint names an operand the probe invented or
   the construct the rewrite produced — `\setlength{\zzprobe}{y}` draws a
   W0301 for the placeholder, `\linespread{x}` in a body a W0340 about the
   `\page` it became — and requiring a complaint-free rewrite dropped five
   more names (`\fontseries`, `\linespread`, `\parbox`, `\setlength`,
   `\vspace`) that a natural usage shows the engine implements.
6. A document with no complaint is clean.
7. Otherwise a complaint about one of the probe's own operands says the
   construct read its argument, so it decides through its `Loss`.
8. Anything else: some other part of the document objected, so the probe
   perturbed its own context and learned nothing. The `length-argument`
   place reports `W0314 {env:minipage-width}` for a width it cannot read,
   which is how `\zzfakecommandzz` came to read as recognised there — the
   control is what caught it.

`native` means "nothing went wrong" — that a usage differs from a decoy's is
a separate question, asked in `probeIn`, because answering it costs a
second elaboration.

A subjectless diagnostic is assumed to be the probe's, and only censused
codes promise a subject, so a construct the engine answers only with a
subjectless code reads `unprobed` — a probe owed, never a gap. -/
def rungOfProbe (name : String) (own : Array String) (ds : Array Diag) : Rung :=
  let worstOf (xs : Array Diag) : Rung :=
    xs.foldl (fun acc d => Rung.worse acc (rungOfLoss d.kind.loss)) .verified
  let about := ds.filter (isAbout name)
  let complaints := ds.filter (·.severity != .note)
  if about.any (fun d => textUnknownCodes.contains d.code) then .unknown
  else if about.any (fun d => mathDeclinedCodes.contains d.code) then .unprobed
  else if !about.isEmpty then worstOf about
  else if ds.any (·.subject == some ("ctrl:nothing:" ++ name)) then .skipped
  else if complaints.any (·.subject.isNone) then .unprobed
  else if complaints.any (fun d => d.subject.any own.contains) then .unprobed
  else if ds.any (fun d => d.kind.loss == .info) then .rewritten
  else if complaints.isEmpty then .native
  else
    let operands := complaints.filter isOperandDiag
    if operands.isEmpty then .unprobed else worstOf operands

/-- The argument shapes every command is tried in. The denominator carries
names and not signatures, so the family is uniform and monotone: a shape
can only move a name toward recognised.

Read it as a fixed set of *opaque argument tokens* rather than as
signatures — a text group (`x`, `y`), a control sequence (`\zzprobe`), a
composable base in both TeX spellings (`o`), a span (`1-2`), a keyword
(`empty`), a counter name (`section`) — plus the definer shapes whose first
argument is a control sequence rather than text. No token is chosen for a
command; each is tried against every name, and `\zzfakecommandzz` stays
`unknown` through all of them, which is what stops a token that happens to
fit from inflating the count. -/
def shapes (name : String) : Array String :=
  #["\\" ++ name,
    "\\" ++ name ++ "{x}",
    "\\" ++ name ++ "{x}{y}",
    "\\" ++ name ++ "[o]{x}",
    "\\" ++ name ++ "{\\zzprobe}",
    "\\" ++ name ++ "{\\zzprobe}{y}",
    "\\" ++ name ++ "{\\zzprobe}[1]{y}",
    "\\" ++ name ++ "{o}",
    "\\" ++ name ++ " o",
    "\\" ++ name ++ "{1-2}",
    "\\" ++ name ++ "{empty}",
    "\\" ++ name ++ "{section}",
    "\\" ++ name ++ "{section}{3}"]

/-- A place is a document context a construct can stand in, as a function
from the spelled fragment to a whole document. The wrapper alone draws no
diagnostic, which is what lets `rungOfProbe` attribute a subjectless note
to the fragment. -/
structure Place where
  label : String
  doc : String → String

def wrap (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

def wrapPre (pre : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nx\n\\end{document}"

/-- The places the original script probed: an article body and its
preamble. Kept, because `--selftest` runs the corpus control against them
as its negative control — a context-blind place list must fail a check that
the shipped list passes, or the check witnesses nothing. -/
def contextBlindPlaces : Array Place :=
  #[{ label := "body", doc := wrap }, { label := "preamble", doc := wrapPre }]

/-- Every place, uniform across all names. Each context here is one the
engine models a family of commands *only* inside. -/
def places : Array Place :=
  contextBlindPlaces ++ #[
    { label := "inline-math", doc := fun s => wrap ("$" ++ s ++ "$") },
    { label := "display-math", doc := fun s => wrap ("\\[" ++ s ++ "\\]") },
    { label := "math-operand", doc := fun s => wrap ("$" ++ s ++ " x$") },
    { label := "tabular-cell",
      doc := fun s => wrap ("\\begin{tabular}{ll}\na " ++ s ++ " & b \\\\\n\\end{tabular}") },
    { label := "tabular-rule",
      doc := fun s => wrap ("\\begin{tabular}{ll}\n" ++ s ++ "\na & b \\\\\n\\end{tabular}") },
    { label := "float", doc := fun s => wrap ("\\begin{figure}\nx\n" ++ s ++ "\n\\end{figure}") },
    { label := "list-item",
      doc := fun s => wrap ("\\begin{itemize}\n\\item x " ++ s ++ "\n\\end{itemize}") },
    -- A dimension operand. The registers (`\textwidth`, `\linewidth`) are
    -- answered here and nowhere else, which the golden corpus shows: it
    -- writes them inside `p{0.29\linewidth}` and `{0.55\textwidth}`. Not
    -- through `\setlength`, which accepts invented names too and would flip
    -- every name including the control (a routed engine defect).
    { label := "length-argument",
      doc := fun s => wrap ("\\begin{minipage}{0.5" ++ s ++ "}\nx\n\\end{minipage}") },
    -- After a label: a reference is defined relative to one, and `\ref{x}`
    -- with no `\label{x}` is a degraded reference, not a gap.
    { label := "after-label", doc := fun s => wrap ("\\section{s}\\label{x}\n" ++ s) },
    -- A titled document: `\maketitle` is defined relative to a declared
    -- title, and with none it draws W0309 for the title it has nothing to set.
    { label := "titled",
      doc := fun s => "\\documentclass{article}\n\\title{t}\n\\author{a}\n\\begin{document}\n"
        ++ s ++ "\n\\end{document}" }]

/-- The name a construct is swapped for when the effect question is asked:
one nothing can know. -/
def decoy (name : String) : String := "zqzqzq" ++ name

/-- An alphabetic name can be swapped for one nothing knows, which is how
the effect question is asked. A control symbol cannot: `\$` has no letters
to replace, and `\zqzq$` is a different parse rather than the same document
under an unknown name. So the effect check runs for control words only, and
a control symbol takes `native` on the absence of a diagnostic alone. -/
def isControlWord (n : String) : Bool := !n.isEmpty && n.all Char.isAlpha

/-- Does this usage differ from *the same shape in the same place* with the
command replaced by a name nothing knows? The compat index's
`compatRowEffect` question, asked of the kernel half.

What it shows is narrower than it looks: the decoy keeps its arguments as
text, so any construct that consumes its arguments differs from it. So
`native` means consumed without complaint, not that something came of it;
five names (`\setcounter`, `\addtocounter`, `\textwidth`, `\linewidth`,
`\columnwidth`) have no witness that differs from deleting the fragment,
and all five are implemented — their effect needs a later construct to
show, which is the parity ladder's to witness, not this check's.

The comparison is made by re-spelling the shape, not by rewriting the
finished document: a document holds the wrapper's own `\documentclass`,
`\begin` and `\end`, and replacing the name everywhere destroyed the
wrapper whenever the construct under test was one of those three. That is
how `\documentclass` came to read `unknown` while every probe document used
it. -/
def changesDoc (a b : String) : Bool := (Elab.run "effect" a).1 != (Elab.run "effect" b).1

/-- A place's own complaints: the subjects its document draws, in every
shape, around a name nothing knows — other than that name's own key and the
probe's operands. What the place says around any fragment is the place's to
answer for, and `rungOfProbe` reads it as a probe that perturbed its context.
Measured, not listed: today it is W0314's `env:minipage-width` in the
dimension-operand place and nothing anywhere else. -/
def Place.own (p : Place) : Array String := Id.run do
  let n := decoy "place"
  let mut out : Array String := #[]
  for s in shapes n do
    for d in (Elab.run "place" (p.doc s)).2 do
      if d.severity == .note || isAbout n d || isOperandDiag d then continue
      if let some sub := d.subject then
        unless out.contains sub do out := out.push sub
  return out

/-- Places with their own complaints, measured once for a run. -/
abbrev Measured := Array (Place × Array String)

def measurePlaces (ps : Array Place) : Measured := ps.map fun p => (p, p.own)

/-- Probe one name through the engine's real dispatch, in every shape and
every place, and keep the best rung. A shape that draws no diagnostic has
its effect checked on the spot; with no effect the name is recognised and
consumed and nothing came of it, which is `skipped`. -/
def probeIn (ps : Measured) (name : String) : Rung := Id.run do
  let mut best : Rung := .unprobed
  let real := shapes name
  let fake := shapes (decoy name)
  for i in [0:real.size] do
    for (p, own) in ps do
      let doc := p.doc real[i]!
      let r := rungOfProbe name own (Elab.run "coverage" doc).2
      if r == .native then
        if !isControlWord name || changesDoc doc (p.doc fake[i]!) then return .native
        else best := Rung.best best .skipped
      else best := Rung.best best r
  return best

/-- One name, on its own. A run measures the places once and calls `probeIn`. -/
def probe (name : String) : Rung := probeIn (measurePlaces places) name

-- ## The package half, from the compat index

/-- One package's documented rows and its implemented subset. -/
structure PRow where
  pkg : String
  documented : Nat
  impl : Nat
deriving Inhabited, BEq

def packageRow (pkg : String) (rows : Array IndexRow) : PRow :=
  { pkg, documented := rows.size, impl := (rows.filter (·.implemented)).size }

def readPackages : IO (Array PRow) := do
  return (← readCompatIndex).map fun (pkg, rows) => packageRow pkg rows

-- ## The scoreboard file

/-- How many probe tasks stand at once. Each probe is pure, so the only
contention is the allocator's: one task per name put 690 threads on a
shared host and spent twice its user time in the kernel. -/
def probeTasks : Nat := 24

/-- `f` over `xs`, in `probeTasks` contiguous chunks, each its own task; the
result is in input order whatever the schedule. -/
def parMap (xs : Array α) (f : α → β) : Array β := Id.run do
  let per := (xs.size + probeTasks - 1) / probeTasks
  let mut tasks : Array (Task (Array β)) := #[]
  let mut i := 0
  while i < xs.size do
    let chunk := xs.extract i (i + per)
    tasks := tasks.push (Task.spawn fun _ => chunk.map f)
    i := i + max per 1
  let mut out : Array β := #[]
  for t in tasks do
    for y in t.get do out := out.push y
  return out

/-- The rung of every counted kernel row, measured once, in parallel.
Every mode reads this array: probing 679 names in 13 places is the
expensive part of a run, and the first version of this script paid for it
three times in `--check` alone. -/
def measureKernel (rows : Array KRow) : Array (KRow × Rung) :=
  let ps := measurePlaces places
  parMap (rows.filter (·.counted)) fun r => (r, probeIn ps r.name)

/-- The rows a run computes, under the `pairs counted/rows` encoding: per
kernel item, `<item>.rows` names in its denominator and `<item>.counted`
names at `rewritten` or above. Every item appears in both, so an item whose
count falls to zero is a regression and not a retirement. -/
def computeRows (kernel : Array (KRow × Rung)) : Array Scoreboard.Row := Id.run do
  let mut items : Array (String × Nat × Nat) := #[]
  for (r, rung) in kernel do
    let key := r.item
    let add := if rung.counted then 1 else 0
    match items.findIdx? (fun p => p.1 == key) with
    | some i => items := items.set! i (key, items[i]!.2.1 + add, items[i]!.2.2 + 1)
    | none => items := items.push (key, add, 1)
  let mut out : Array Scoreboard.Row := #[]
  for (key, c, n) in items do
    out := out.push { item := key ++ ".counted", value := Int.ofNat c }
    out := out.push { item := key ++ ".rows", value := Int.ofNat n }
  return out.qsort (fun a b => a.item < b.item)

/-- The complete coverage measurement. Kernel items stay per chapter; the
package half is one aggregate pair, while `compat` holds every package's
pair independently. Keeping this aggregate in rows makes the combined
headline part of `--check`, not ungated provenance. -/
def computeCoverageRows (kernel : Array (KRow × Rung)) (pkgs : Array PRow) :
    Array Scoreboard.Row :=
  let pImpl := pkgs.foldl (fun n p => n + p.impl) 0
  let pDoc := pkgs.foldl (fun n p => n + p.documented) 0
  let packageRows : Array Scoreboard.Row :=
    #[{ item := "packages.counted", value := Int.ofNat pImpl },
      { item := "packages.rows", value := Int.ofNat pDoc }]
  (computeRows kernel ++ packageRows).qsort (fun a b => a.item < b.item)

structure Totals where
  buckets : Array (Rung × Nat)
  kExcluded : Nat
  pImpl : Nat
  pDoc : Nat
deriving Inhabited

def Totals.bucket (t : Totals) (r : Rung) : Nat :=
  (t.buckets.find? (fun p => p.1 == r)).map (·.2) |>.getD 0

def Totals.kCounted (t : Totals) : Nat :=
  t.buckets.foldl (fun acc (r, n) => if r.counted then acc + n else acc) 0

def Totals.kRows (t : Totals) : Nat := t.buckets.foldl (fun acc p => acc + p.2) 0

def Totals.num (t : Totals) : Nat := t.kCounted + t.pImpl
def Totals.den (t : Totals) : Nat := t.kRows + t.pDoc

/-- Percent with one decimal, as an integer count of tenths. -/
def tenths (num den : Nat) : Nat := if den == 0 then 0 else (num * 1000 + den / 2) / den

def pct (num den : Nat) : String :=
  let t := tenths num den
  toString (t / 10) ++ "." ++ toString (t % 10) ++ "%"

def totalsOf (kernel : Array (KRow × Rung)) (rows : Array KRow) (pkgs : Array PRow) :
    Totals := Id.run do
  let mut buckets : Array (Rung × Nat) := Rung.all.toArray.map (·, 0)
  for (_, rung) in kernel do
    match buckets.findIdx? (fun p => p.1 == rung) with
    | some i => buckets := buckets.set! i (rung, buckets[i]!.2 + 1)
    | none => buckets := buckets.push (rung, 1)
  let mut t : Totals :=
    { buckets, kExcluded := (rows.filter (!·.counted)).size, pImpl := 0, pDoc := 0 }
  for p in pkgs do
    t := { t with pImpl := t.pImpl + p.impl, pDoc := t.pDoc + p.documented }
  return t

-- ## The corpus control

/-- Control words a source uses, with `%` comments stripped. A name in
verbatim or in a user definition is still collected, which is why the
contradictions this finds are read against a declared exemption table
rather than treated as a count. -/
def controlWordsOf (text : String) : Array String := Id.run do
  let noComments := String.intercalate "\n" ((text.splitOn "\n").map fun l =>
    match l.splitOn "%" with
    | first :: _ => if first.endsWith "\\" then l else first
    | [] => l)
  let cs := noComments.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '\\' && i + 1 < cs.size && cs[i + 1]!.isAlpha then
      let mut j := i + 1
      while j < cs.size && cs[j]!.isAlpha do j := j + 1
      let name := String.ofList ((cs.toList.drop (i + 1)).take (j - i - 1))
      if !out.contains name then out := out.push name
      i := j
    else i := i + 1
  return out

/-- A subject that names the construct, under its own key, a longer one
(`ctrl:fontseries:b`), or the engine's rewrite-to-nothing key
(`ctrl:nothing:noindent`). The corpus control reads it wide: a fixture whose
elaboration names the construct anywhere is not a clean use of it. -/
def namesConstruct (name : String) (d : Diag) : Bool :=
  match d.subject with
  | some s =>
    (aboutKeys name).contains s || (aboutKeys name).any (fun k => s.startsWith (k ++ ":"))
      || s == "ctrl:nothing:" ++ name
  | none => false

def reportsUnknown (name : String) (d : Diag) : Bool :=
  textUnknownCodes.contains d.code && isAbout name d

/-- One disagreement between the probe and the golden corpus. -/
structure Contradiction where
  name : String
  file : String
  rung : Rung
deriving Inhabited

/-- The corpus control, in both directions. A fixture uses a name the probe
puts below the cut, and the fixture's own elaboration says otherwise: for
`unknown`, the file never reports the name unknown; for every other rung
below the cut, no diagnostic in the file names it at all. Checking `unknown`
alone let eight names the corpus uses cleanly read `degraded`, `skipped` or
`unprobed` unremarked.

Only names the corpus actually uses are probed, one task each, which is
what makes this runnable inside `--selftest`. -/
def corpusContradictions (ps : Array Place) (denom : Array KRow) :
    IO (Array Contradiction) := do
  let files := (← System.FilePath.walkDir corpusDir).filter (·.toString.endsWith ".tex")
  let mut notUnknown : Array (String × String) := #[]
  let mut clean : Array (String × String) := #[]
  for f in files.qsort (·.toString < ·.toString) do
    let text ← IO.FS.readFile f
    let ds := (Elab.run f.toString text).2
    let file := f.fileName.getD ""
    for name in controlWordsOf text do
      unless denom.any (fun r => r.name == name && r.counted) do continue
      if !notUnknown.any (·.1 == name) && !ds.any (reportsUnknown name) then
        notUnknown := notUnknown.push (name, file)
      if !clean.any (·.1 == name) && !ds.any (namesConstruct name) then
        clean := clean.push (name, file)
  let names := notUnknown.map (·.1) ++
    (clean.map (·.1)).filter (fun n => !notUnknown.any (·.1 == n))
  let measured := measurePlaces ps
  let rungs := parMap names (probeIn measured)
  let mut hits : Array Contradiction := #[]
  for i in [0:names.size] do
    let name := names[i]!
    let rung := rungs[i]!
    if rung == .unknown then
      if let some (_, file) := notUnknown.find? (·.1 == name) then
        hits := hits.push { name, file, rung }
    else if !rung.counted then
      if let some (_, file) := clean.find? (·.1 == name) then
        hits := hits.push { name, file, rung }
  return hits.qsort (·.name < ·.name)

/-- Which side of a contradiction an explanation puts the construct on. -/
inductive Side where
  /-- The fixture's use is not evidence — a region elaboration never reaches,
  or the same spelling meaning something else — and the construct really is
  where the probe put it. -/
  | corpus
  /-- The engine answers the construct and no fragment the probe writes can
  spell it: a known false reading below the cut, printed by `--report`. -/
  | probe
deriving BEq, Inhabited

def Side.word : Side → String
  | .corpus => "corpus"
  | .probe => "probe"

/-- The fragment a document would write for the construct, in the body or
in the preamble: the falsifier an explanation carries. -/
structure Usage where
  preamble : Bool
  fragment : String

def Usage.doc (u : Usage) : String := if u.preamble then wrapPre u.fragment else wrap u.fragment

/-- Does the engine answer the construct in this usage, at the level a
contradiction on `rung` asks about? For `unknown`, nothing reports it
unknown; for any other rung, nothing names it at all. -/
def answeredIn (name : String) (rung : Rung) (u : Usage) : Bool :=
  let ds := (Elab.run "usage" u.doc).2
  if rung == .unknown then !ds.any (reportsUnknown name) else !ds.any (namesConstruct name)

structure Explanation where
  name : String
  side : Side
  usage : Usage
  why : String

/-- The contradictions the probe is not wrong about, and the ones it is,
each with its side and a natural usage that must read the way that side
says: a `corpus` row's usage must *not* be answered — the construct really
is a gap — and a `probe` row's usage must be. The first draft of this table
had no falsifier, and it filed `\fill` and `\parskip` under `corpus` while
`\vspace{\fill}` and `\setlength{\parskip}{7pt}` both rewrite cleanly.

A row must also still be a contradiction: if the corpus stops using the
name, or the probe starts answering it, the row is stale and `--selftest`
fails. Failing in every direction is what keeps this from becoming a
baseline that blesses whatever the script says today. -/
def witnessExplained : Array Explanation := #[
  { name := "accent", side := .corpus, usage := ⟨false, "\\accent127 a"⟩,
    why := "a palette role named in a theme block, not the kernel's \\accent" },
  { name := "begin", side := .probe, usage := ⟨false, "\\begin{center}x\\end{center}"⟩,
    why := "half of a delimiter pair: no fragment can spell it alone" },
  { name := "bf", side := .corpus, usage := ⟨false, "{\\bf x}"⟩,
    why := "inside a \\renewcommand{\\@maketitle} body elaboration never reaches" },
  { name := "documentclass", side := .probe, usage := ⟨false, "x"⟩,
    why := "a document's identity: every probe document already declares one" },
  { name := "end", side := .probe, usage := ⟨false, "\\begin{center}x\\end{center}"⟩,
    why := "half of a delimiter pair: no fragment can spell it alone" },
  { name := "fill", side := .probe, usage := ⟨false, "\\vspace{\\fill}"⟩,
    why := "answered as glue, \\vspace{\\fill}; the fixture's is TikZ's path command, and no \
probe token is a glue value" },
  { name := "hsize", side := .corpus, usage := ⟨false, "\\hsize=10pt x"⟩,
    why := "inside a \\renewcommand{\\@maketitle} body elaboration never reaches" },
  { name := "hspace", side := .probe, usage := ⟨false, "a\\hspace{1pt}b"⟩,
    why := "a native dimensioned command whose probe operand is not a readable length" },
  { name := "left", side := .probe, usage := ⟨false, "$\\left( x \\right)$"⟩,
    why := "a delimiter operand: no probe token is a delimiter" },
  { name := "multicolumn", side := .probe,
    usage := ⟨false, "\\begin{tabular}{ll}\n\\multicolumn{2}{c}{x} \\\\\n\\end{tabular}"⟩,
    why := "set as a span only at the start of a tabular cell, where no probe shape reaches" },
  { name := "newenvironment", side := .probe, usage := ⟨true, "\\newenvironment{zzbox}{[}{]}"⟩,
    why := "a preamble definer of three arguments; no probe shape has three, and its one \
counting witness was the dimension-operand place, whose own complaint it stood beside" },
  { name := "parskip", side := .probe, usage := ⟨true, "\\setlength{\\parskip}{7pt}"⟩,
    why := "answered through \\setlength with a length; the fixture's sits in a \
\\newcommand{\\@toptitlebar} body, and no probe token is a length" },
  { name := "renewenvironment", side := .probe,
    usage := ⟨true, "\\newenvironment{zzbox}{[}{]}\n\\renewenvironment{zzbox}{(}{)}"⟩,
    why := "a preamble definer of three arguments; no probe shape has three, and its one \
counting witness was the dimension-operand place, whose own complaint it stood beside" },
  { name := "right", side := .probe, usage := ⟨false, "$\\left( x \\right)$"⟩,
    why := "a delimiter operand: no probe token is a delimiter" },
  { name := "rule", side := .probe, usage := ⟨false, "\\rule{1pt}{1pt}"⟩,
    why := "a native two-dimension command whose probe operands are not readable lengths" },
  { name := "usepackage", side := .probe, usage := ⟨true, "\\usepackage{amsmath}"⟩,
    why := "a package name: no probe token names a package the engine reads" },
  { name := "vbox", side := .corpus, usage := ⟨false, "\\vbox{x}"⟩,
    why := "inside a \\renewcommand{\\@maketitle} body elaboration never reaches" }]

/-- Known false readings the corpus cannot witness, because no fixture uses
the construct: found by spot checks in natural usage. Each row fails in both
directions like the table above — the usage must stay answered and the probe
must still read the name below the cut. -/
def falseQueue : Array Explanation := #[]

def explained (name : String) : Option Explanation :=
  witnessExplained.find? (·.name == name)

-- ## Modes

def loadKernel : IO Denom := do
  unless (← System.FilePath.pathExists denomPath) do
    throw (IO.userError s!"coverage: {denomPath} is missing — run --denominator")
  match parseDenom (← IO.FS.readFile denomPath) with
  | .error e => throw (IO.userError ("coverage: " ++ e))
  | .ok d => return d

/-- The denominator's own header, checked before the file is trusted: the
row count against the figure it states, and the body against its stamp.
This catches an accidental edit and nothing more — the file stamps itself —
so no message here prints the value a caller could paste back: a
regeneration from the manual is the only way to a new stamp, and a smaller
denominator is the ratchet's to refuse, through every item's `.rows`. -/
def checkDenom (d : Denom) : Array String := Id.run do
  let mut bad : Array String := #[]
  match provValue d.provenance "rows" with
  | none => bad := bad.push "the header states no row count"
  | some want =>
    match want.toNat? with
    | none => bad := bad.push "the header's row count is not a number"
    | some n =>
      if n != d.rows.size then
        bad := bad.push s!"the header states {n} rows and the file holds {d.rows.size}"
  match provValue d.provenance "body" with
  | none => bad := bad.push "the header states no body stamp"
  | some want =>
    if want != bodyStamp (denomBody d.rows) then
      bad := bad.push "the body is not the one the header stamps"
  return bad.map (fun m => s!"{denomPath}: {m} — never hand-edit it; rebuild it from the \
manual with --denominator <latex2e.texi>")

/-- The tier's provenance. The package aggregate is also a scoreboard pair,
so these readable totals cannot stale independently of `--check`. -/
def provenanceLines (d : Denom) (t : Totals) : Array String :=
  let bucketLine := String.intercalate ", " (Rung.all.map fun r =>
    let n := t.bucket r
    if n == 0 && r == .verified then "0 verified (the parity ladder's to award)"
    else s!"{n} {r.word}")
  let mathN := (d.rows.filter (·.cls == mathClass)).size
  let notBaseN := (d.rows.filter (·.cls == notBaseClass)).size
  #[s!"# documented-command coverage, kernel half: per manual chapter (and the register \
file), <item>.counted names at the `rewritten` rung or above (rewritten | native | \
verified) of <item>.rows names in {denomPath}.",
    s!"# kernel: {bucketLine}.",
    s!"# kernel excluded: {mathN} math-mode symbol commands (math_given), {notBaseN} \
commands latex.ltx defines only as an error (not_base).",
    s!"# package half, gated here as packages.counted/packages.rows and per package by \
the compat tier: {t.pImpl} implemented of {t.pDoc} documented (tests/compat-index; `impl` \
or `inert:`).",
    s!"# total: {t.num}/{t.den} = {pct t.num t.den}"]

/-- One measurement for the tier: the denominator's header checked, every
counted kernel name probed. A header that fails its own check measures
nothing, which the shared `tierMain` reports as a fault after the reasons
printed here. -/
def measureTier : IO (Array String × Array Scoreboard.Row) := do
  let d ← loadKernel
  let bad := checkDenom d
  unless bad.isEmpty do
    for b in bad do IO.eprintln ("coverage: " ++ b)
    return (#[], #[])
  let pkgs ← readPackages
  let kernel := measureKernel d.rows
  let t := totalsOf kernel d.rows pkgs
  return (provenanceLines d t, computeCoverageRows kernel pkgs)

/-- The per-item detail, and the audit the number cannot show: where the
measured rung and the compat-index's reviewed verdict disagree. -/
def report : IO UInt32 := do
  let d ← loadKernel
  let pkgs ← readPackages
  let kernel := measureKernel d.rows
  let pr := probeIn (measurePlaces places)
  let t := totalsOf kernel d.rows pkgs
  IO.println s!"kernel  {t.kCounted} counted of {t.kRows} ({t.kExcluded} excluded)"
  for r in Rung.all do
    IO.println s!"  {t.bucket r}\t{r.word}"
  IO.println s!"package {t.pImpl} implemented / {t.pDoc} documented"
  IO.println s!"total   {t.num}/{t.den} = {pct t.num t.den}"
  IO.println ""
  IO.println "-- items, most unknown first (unknown, unprobed, below-cut, counted)"
  let mut items : Array (String × Nat × Nat × Nat × Nat) := #[]
  for (r, rung) in kernel do
    let key := r.item
    let (u, p, b, c) := match items.findIdx? (fun i => i.1 == key) with
      | some j => (items[j]!.2.1, items[j]!.2.2.1, items[j]!.2.2.2.1, items[j]!.2.2.2.2)
      | none => (0, 0, 0, 0)
    let bumped :=
      if rung == .unknown then (key, u + 1, p, b, c)
      else if rung == .unprobed then (key, u, p + 1, b, c)
      else if rung.counted then (key, u, p, b, c + 1)
      else (key, u, p, b + 1, c)
    match items.findIdx? (fun i => i.1 == key) with
    | some j => items := items.set! j bumped
    | none => items := items.push bumped
  for c in items.qsort (fun a b => a.2.1 > b.2.1) do
    IO.println s!"  {c.2.1}\t{c.2.2.1}\t{c.2.2.2.1}\t{c.2.2.2.2}\t{c.1}"
  IO.println ""
  IO.println "-- unknown kernel commands, by item"
  for c in items.qsort (fun a b => a.1 < b.1) do
    let names := kernel.filterMap fun (r, rung) =>
      if r.item == c.1 && rung == .unknown then some r.name else none
    unless names.isEmpty do
      IO.println s!"  {c.1}: {String.intercalate " " names.toList}"
  IO.println ""
  IO.println "-- unprobed (the probe's own arguments, not the engine's answer)"
  let unprobed := kernel.filterMap fun (r, rung) =>
    if rung == .unprobed then some r.name else none
  IO.println s!"  {String.intercalate " " unprobed.toList}"
  IO.println ""
  IO.println "-- the corpus control, both directions"
  let hits ← corpusContradictions places d.rows
  IO.println s!"  {hits.size} contradiction(s) on the shipped places"
  for c in hits do
    match explained c.name with
    | some e => IO.println s!"    {c.name}\t{c.rung.word}\t{c.file}\t{e.side.word}: {e.why}"
    | none => IO.println s!"    {c.name}\t{c.rung.word}\t{c.file}\tNOT EXPLAINED"
  let known := (witnessExplained ++ falseQueue).filter (·.side == .probe)
  IO.println s!"  known false readings below the cut (the engine recognises them; no probe \
fragment spells them): {known.size}"
  for e in known do
    IO.println s!"    {e.name}\t{(pr e.name).word}\t{e.why}"
  let blind ← corpusContradictions contextBlindPlaces d.rows
  IO.println s!"  {blind.size} contradiction(s) on the context-blind places"
  IO.println ""
  IO.println "-- compat-index audit: recognition disagreements, then counting differences"
  let mut disagree := 0
  let mut comparable := 0
  let mut counting : Array String := #[]
  for (pkg, idx) in ← readCompatIndex do
    for r in idx do
        let ann := r.verdict
        let call := r.call
        -- Only a row that *is* one control word is comparable. A row naming
        -- a whole environment, several commands, a starred form or a
        -- delimited call has no single name to probe — and admitting
        -- `\lstinline|x|` and `\ProcessKeyvalOptions*` as names is what
        -- produced four of the seven "disagreements" this audit first
        -- reported.
        if call.startsWith "\\" && isControlWord (call.drop 1).toString then
          let name := (call.drop 1).toString
          comparable := comparable + 1
          let rung := pr name
          -- The vocabularies are lined up before a difference means
          -- anything. `refuse:W0301` *is* unknown (W0301 is the
          -- unknown-command code). Every other annotation — `impl`,
          -- `inert:`, and a refusal naming any other code — asserts that the
          -- dispatch recognised the command, which is the one question both
          -- vocabularies can answer. Skipping this alignment made 37 rows
          -- read as disagreements and every one was this script's own
          -- vocabulary.
          let wantUnknown :=
            match r.refusalCode? with
            | some code => textUnknownCodes.contains code
            | none => false
          let gotUnknown := rung == .unknown
          if rung == .unprobed then
            disagree := disagree + 1
            IO.println s!"  {pkg}\t{call}\tindex:{ann}\tmeasured:unprobed — the probe \
cannot spell it"
          else if wantUnknown != gotUnknown then
            disagree := disagree + 1
            IO.println s!"  {pkg}\t{call}\tindex:{ann}\tmeasured:{rung.word}"
          else if r.implemented && !rung.counted then
            -- Recognition agrees; the two halves count it differently. An
            -- `inert:` row and the `skipped` rung are the same judgement —
            -- recognised, no ink — made by a reviewer and by the engine, and
            -- the package half counts it while the kernel half does not.
            counting := counting.push s!"  {pkg}\t{call}\tindex:{ann}\tmeasured:{rung.word}"
  IO.println s!"-- {disagree} recognition disagreement(s) over {comparable} comparable \
row(s), one control word each, of {t.pDoc} documented"
  for c in counting do IO.println c
  IO.println s!"-- {counting.size} row(s) the package half counts and the kernel rule \
would not"
  return 0

-- ## Rebuilding the denominator

/-- Texinfo writes `@`, `{` and `}` as `@@`, `@{` and `@}`, so a manual line
documenting `\@`, `\{` or `\}` reads `\@@`, `\@{` or `\@}`. Reading the
escape as the character it stands for is how those three enter the
denominator at all; without it `\@` — the second-ranked blocker over the
public corpus — was never harvested. -/
def texinfoChar? (c : Char) : Option Char :=
  if c == '@' || c == '{' || c == '}' then some c else none

/-- The command names one manual line indexes: every `\name` token, a
control word or a single-character control symbol, with texinfo's own
escapes read. -/
def namesOnLine (line : String) : Array String := Id.run do
  let arr := line.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < arr.size do
    if arr[i]! == '\\' && i + 1 < arr.size then
      let c := arr[i + 1]!
      if c.isAlpha then
        let mut j := i + 1
        while j < arr.size && arr[j]!.isAlpha do j := j + 1
        out := out.push (String.ofList (arr.toList.drop (i + 1) |>.take (j - i - 1)))
        i := j
      else if c == '@' && i + 2 < arr.size then
        -- `\@@`, `\@{`, `\@}`: texinfo's escape for the character itself.
        match texinfoChar? arr[i + 2]! with
        | some ch => out := out.push (String.singleton ch); i := i + 3
        | none => out := out.push "@"; i := i + 2
      else if !c.isWhitespace && c != '{' && c != '}' then
        out := out.push (String.singleton c)
        i := i + 2
      else i := i + 2
    else i := i + 1
  return out

/-- A chapter title with texinfo's markup read as the text it stands for:
`Overview of @LaTeX{}` is the chapter "Overview of LaTeX", and a scoreboard
item is a name a reader reads. -/
def plainTitle (s : String) : String := Id.run do
  let arr := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < arr.size do
    if arr[i]! == '@' && i + 1 < arr.size then
      if arr[i + 1]!.isAlpha then
        let mut j := i + 1
        while j < arr.size && arr[j]!.isAlpha do j := j + 1
        let cmd := String.ofList (arr.toList.drop (i + 1) |>.take (j - i - 1))
        -- `@LaTeX{}`, `@TeX{}`: the command's own name is the text.
        out := out ++ cmd
        i := j
        if i + 1 < arr.size && arr[i]! == '{' && arr[i + 1]! == '}' then i := i + 2
      else
        out := out.push arr[i + 1]!
        i := i + 2
    else
      out := out.push arr[i]!
      i := i + 1
  return out.trimAscii.toString

/-- The Lua the confirmation runs: lualatex's own answer to "is this name
defined, and what is it?", asked through `token.is_defined` and
`token.create(n).cmdname`, and for a macro whose body begins `\not@base` —
`latex.ltx`'s "not provided in base LaTeX2e" error — the class
`notBaseClass` names, read from `token.get_macro`. Written by this mode
rather than kept beside the tree, so the only input a regeneration needs is
the manual. -/
def probeLua (outFile : String) : String :=
  String.intercalate "\n" [
    "local out = io.open(\"" ++ outFile ++ "\", \"w\")",
    "for line in io.lines(\"cands.txt\") do",
    "  if line ~= \"\" then",
    "    local def = token.is_defined(line)",
    "    local cn = \"undefined\"",
    "    if def then cn = token.create(line).cmdname or \"?\" end",
    "    if cn == \"call\" or cn == \"long_call\" or cn == \"protected_call\" then",
    "      local ok, body = pcall(token.get_macro, line)",
    "      if ok and type(body) == \"string\" and body:sub(1, 9) == \"\\\\not@base\" then",
    "        cn = \"" ++ notBaseClass ++ "\"",
    "      end",
    "    end",
    "    out:write(line, \"\\t\", tostring(def), \"\\t\", cn, \"\\n\")",
    "  end",
    "end",
    "out:close()",
    ""]

/-- The wrapper: a *bare* class, no packages. Under amsmath seven math
symbols are macros rather than symbol-table entries, so a package-loaded
confirmation makes the one stated exclusion depend on what it loaded. -/
def probeTex (cls luaFile : String) : String :=
  "\\documentclass{" ++ cls ++ "}\n\\begin{document}\n\\directlua{dofile(\"" ++ luaFile ++
  "\")}\nx\n\\end{document}\n"

/-- Run one bare class's confirmation and read back lualatex's answers. -/
def confirmUnder (dir cls : String) (cands : Array String) :
    IO (Array (String × String)) := do
  let stem := "probe-" ++ cls
  IO.FS.writeFile (dir ++ "/cands.txt")
    (cands.foldl (fun acc n => acc ++ n ++ "\n") "")
  IO.FS.writeFile (dir ++ "/" ++ stem ++ ".lua") (probeLua (stem ++ ".out"))
  IO.FS.writeFile (dir ++ "/" ++ stem ++ ".tex") (probeTex cls (stem ++ ".lua"))
  let r ← IO.Process.output
    { cmd := "lualatex", cwd := some dir,
      args := #["-interaction=nonstopmode", "--shell-escape", stem ++ ".tex"] }
  unless r.exitCode == 0 do
    IO.eprintln s!"coverage: lualatex exited {r.exitCode} for {cls}; reading what it wrote"
  let outPath := dir ++ "/" ++ stem ++ ".out"
  unless (← System.FilePath.pathExists outPath) do
    throw (IO.userError s!"coverage: lualatex wrote no probe output for {cls}")
  let mut out : Array (String × String) := #[]
  for line in (← IO.FS.readFile outPath).splitOn "\n" do
    let f := tabs line
    if f.size < 3 then continue
    if f[1]! == "true" then out := out.push (f[0]!, f[2]!)
  return out

/-- Rebuild the kernel denominator from the reference manual. The manual is
the one input outside the tree; the probe inputs are written here and run
here, so "never hand-edit" is enforceable and the file is reproducible from
a sha256. Never part of a gate: `--check` reads the committed file only. -/
def denominator (texi : String) : IO UInt32 := do
  let src ← IO.FS.readFile texi
  let mut chapter := "About this document"
  let mut found : Array (String × String) := #[]
  let mut inFtable := false
  for line in src.splitOn "\n" do
    if line.startsWith "@chapter " then chapter := plainTitle ((line.drop 9).toString)
    else if line.startsWith "@appendix " then chapter := plainTitle ((line.drop 10).toString)
    if line.startsWith "@ftable" then inFtable := true
    else if line.startsWith "@end ftable" then inFtable := false
    let harvest := line.startsWith "@findex" || line.startsWith "@node"
      || (inFtable && line.startsWith "@item")
    unless harvest do continue
    for name in namesOnLine line do
      found := found.push (name, chapter)
  let cands := found.foldl (fun (acc : Array String) (p : String × String) =>
    if acc.contains p.1 then acc else acc.push p.1) #[]
  let tmp ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let dir := tmp.stdout.trimAscii.toString
  if dir.isEmpty then return (← die 3 "coverage: no scratch directory")
  let article ← confirmUnder dir "article" cands
  let book ← confirmUnder dir "book" cands
  let mut rows : Array KRow := #[]
  for (name, ch) in found do
    if rows.any (fun r => r.name == name) then continue
    match article.find? (fun m => m.1 == name) with
    | some (_, cls) => rows := rows.push { name, chapter := ch, cls }
    | none =>
      match book.find? (fun m => m.1 == name) with
      | some (_, cls) => rows := rows.push { name, chapter := ch, cls }
      | none => continue
  let sorted := rows.qsort (fun a b => a.name < b.name)
  let body := denomBody sorted
  let sha := (← IO.Process.output { cmd := "sha256sum", args := #[texi] }).stdout
  let shaField := ((sha.splitOn " ").headD "").trimAscii.toString
  let id := (src.splitOn "\n").find? (·.startsWith "@c $Id:")
  let luaVer := (← IO.Process.output { cmd := "lualatex", args := #["--version"] }).stdout
  let head :=
    "# The kernel command denominator: every command name the LaTeX2e unofficial\n\
     # reference manual indexes (@findex, @ftable items, @node headings), confirmed\n\
     # by lualatex to be a control sequence LaTeX defines, and classified by the\n\
     # meaning lualatex reports. Fields: name, manual chapter, lualatex meaning.\n\
     # A `math_given` row is a math-mode symbol command and a `not_base` row a\n\
     # command latex.ltx defines only as its \"not provided in base LaTeX2e\"\n\
     # error; both are excluded from the count and kept here so the exclusion\n\
     # is visible and countable. The\n\
     # confirmation runs under bare classes with no packages loaded, because under\n\
     # amsmath seven of those symbols are macros and the exclusion would then\n\
     # depend on what the confirmation happened to load.\n\
     # The manual is © its authors and permits verbatim and modified copies under\n\
     # its own notice; what is kept here is command names, chapter titles and\n\
     # lualatex meaning classes, and no prose.\n\
     # Regenerate with scripts/coverage.lean --denominator <latex2e.texi>; never\n\
     # hand-edit. The row count and body stamp below are checked by --check.\n" ++
    s!"# manual: latex2e-help-texinfo latex2e.texi, sha256 {shaField}\n" ++
    s!"# manual-source: https://mirrors.ctan.org/info/latex2e-help-texinfo/latex2e.texi\n" ++
    s!"# manual-id: {(id.getD "unknown").trimAscii.toString}\n" ++
    s!"# confirmed-by: {((luaVer.splitOn "\n").headD "").trimAscii.toString}\n" ++
    s!"# confirmed-under: bare \\documentclass\{article} and \{book}, no packages\n" ++
    s!"# candidates: {cands.size}\n" ++
    s!"# rows: {sorted.size}\n" ++
    s!"# body: {bodyStamp body}\n"
  IO.FS.createDirAll "tests/coverage"
  IO.FS.writeFile denomPath (head ++ body)
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir] }
  IO.println s!"coverage: wrote {denomPath} with {sorted.size} confirmed names \
of {cands.size} indexed"
  return 0

-- ## Selftest

def selftest : IO UInt32 := Scoreboard.tierSelftest "coverage" fun expect => do
  -- The rung rule, on diagnostics the engine really produces.
  let measured := measurePlaces places
  let pr := probeIn measured
  expect "a known command is native" (pr "textbf" == .native)
  expect "an invented name is unknown" (pr "zzfakecommandzz" == .unknown)
  expect "the control stays unknown in every place"
    ((measured.all fun (p, own) =>
      shapes "zzfakecommandzz" |>.all fun s =>
        rungOfProbe "zzfakecommandzz" own (Elab.run "c" (p.doc s)).2 != .native))
  expect "every place's wrapper draws no diagnostic"
    (places.all fun p => (Elab.run "w" (p.doc "")).2.isEmpty)
  -- The context each of these lives in is the point of the place family.
  expect "a tabular rule is answered" ((pr "hline").counted)
  expect "a float's caption is answered" ((pr "caption").counted)
  expect "a list item is answered" ((pr "item").counted)
  expect "a math construct is answered" ((pr "frac").counted)
  expect "a reference is answered after its label" ((pr "ref").counted)
  expect "a title is answered where one is declared" ((pr "maketitle").counted)
  -- Every probe document uses these three, and the first version of this
  -- script read `\begin` as unknown and `\documentclass`/`\end` as refused
  -- because of it. None of the three can be spelled as a fragment — a class
  -- name is a document's identity, `\begin`/`\end` are halves of a delimiter
  -- pair — so `unprobed` is the honest reading, and the point is that none
  -- of them is a gap charged to the engine.
  expect s!"documentclass is unprobed, not a gap (got {(pr "documentclass").word})"
    (pr "documentclass" == .unprobed)
  expect s!"end is unprobed, not a gap (got {(pr "end").word})" (pr "end" == .unprobed)
  expect s!"begin is unprobed, not a gap (got {(pr "begin").word})"
    (pr "begin" == .unprobed)
  expect "a page style is answered through its keyword" ((pr "thispagestyle").counted)
  expect "the registers a length argument answers are counted"
    ((pr "textwidth").counted && (pr "linewidth").counted)
  expect "a definer shape survives its own placeholder's warning" ((pr "setlength").counted)
  -- A place's own complaint is the place's: a rewrite beside it says nothing.
  match measured.find? (·.1.label == "length-argument") with
  | none => expect "the dimension-operand place exists" false
  | some (p, own) =>
    expect "the dimension-operand place owns its width complaint"
      (own.contains "env:minipage-width")
    let ds := (Elab.run "p" (p.doc "\\newenvironment{x}{y}")).2
    expect "a rewrite beside the place's own complaint does not count"
      (rungOfProbe "newenvironment" own ds == .unprobed
        && rungOfProbe "newenvironment" #[] ds == .rewritten)
  expect "no other place owns a complaint"
    (measured.all fun (p, own) => p.label == "length-argument" || own.isEmpty)
  expect "an operand complaint is evidence of dispatch"
    (rungOfProbe "ref" #[] (Elab.run "p" (wrap "\\ref{x}")).2 == .degraded)
  expect "a counter name is answered where a text group is not"
    ((pr "setcounter").counted && (pr "stepcounter").counted
      && (pr "addtocounter").counted && (pr "refstepcounter").counted)
  expect "a rewrite onto nothing is skipped, not translated"
    (rungOfProbe "noindent" #[] (Elab.run "p" (wrap "\\noindent")).2 == .skipped
      && pr "noindent" == .skipped && pr "PackageWarning" == .skipped)
  -- The silence guard's W0387 once carried no subject, so its two log
  -- commands read as the probe's own mistake; with `ctrl:<name>` they are a
  -- `config` answer about the construct.
  expect "a construct the silence guard names reads skipped"
    (pr "ClassError" == .skipped && pr "PackageError" == .skipped)
  expect "a rewrite whose document also errors without a subject does not count"
    (rungOfProbe "vspace" #[] (Elab.run "p" (wrap "\\vspace")).2 == .unprobed)
  expect "the bare wrapper draws no diagnostic" ((Elab.run "w" (wrap "")).2.isEmpty)
  expect "a subjectless error is the probe's, not the construct's"
    (rungOfProbe "textbf" #[] (Elab.run "p" (wrap "\\textbf")).2 == .unprobed)
  expect "another subject's warning is the probe's, not the construct's"
    (rungOfProbe "zzfakecommandzz" #[]
      (Elab.run "p" (wrap "\\begin{minipage}{0.5\\zzfakecommandzz}\nx\n\\end{minipage}")).2
      == .unprobed)
  -- The ladder's arithmetic.
  expect "best keeps the higher rung" (Rung.best .unknown .native == .native)
  expect "worse keeps the lower rung" (Rung.worse .native .skipped == .skipped)
  expect "a measurement beats no measurement" (Rung.best .unprobed .unknown == .unknown)
  expect "the cut is rewritten and above"
    (Rung.rewritten.counted && Rung.native.counted && Rung.verified.counted
      && !Rung.degraded.counted && !Rung.skipped.counted && !Rung.fails.counted
      && !Rung.unknown.counted && !Rung.unprobed.counted)
  expect "every loss has a rung"
    ([Loss.dropped, .pending, .degraded, .standard, .config, .info].map rungOfLoss
      == [.fails, .degraded, .degraded, .native, .skipped, .rewritten])
  expect "rung words are distinct"
    ((Rung.all.map Rung.word).eraseDups.length == Rung.all.length)
  -- The exclusions and the register grouping are read from the class.
  expect "a math symbol row is excluded"
    (!(KRow.counted { name := "alpha", chapter := "Math formulas", cls := mathClass }))
  expect "a row latex.ltx defines only as an error is excluded"
    (!(KRow.counted { name := "mho", chapter := "Math formulas", cls := notBaseClass }))
  expect "a macro row is counted"
    (KRow.counted { name := "textbf", chapter := "Fonts", cls := "call" })
  expect "a register takes its own item"
    (KRow.item { name := "parindent", chapter := "Lengths", cls := "assign_dimen" }
      == "kernel/registers")
  expect "a command takes its chapter"
    (KRow.item { name := "textbf", chapter := "Fonts", cls := "call" } == "kernel/Fonts")
  -- The tier's rows: one counted/rows pair per item, in the shared format.
  let tiny : Array (KRow × Rung) :=
    #[({ name := "textbf", chapter := "Fonts", cls := "call" }, .native),
      ({ name := "zz", chapter := "Fonts", cls := "call" }, .unknown),
      ({ name := "parindent", chapter := "Lengths", cls := "assign_dimen" }, .skipped)]
  let rows := computeCoverageRows tiny #[]
  expect "every item carries its counted and its rows"
    (rows.map (fun r => (r.item, r.value)) ==
      #[("kernel/Fonts.counted", 1), ("kernel/Fonts.rows", 2),
        ("kernel/registers.counted", 0), ("kernel/registers.rows", 1),
        ("packages.counted", 0), ("packages.rows", 0)])
  let pkg : PRow := { pkg := "zz", documented := 2, impl := 1 }
  let combined := computeCoverageRows tiny #[pkg]
  expect "the package half is a scoreboard pair, not provenance only"
    (combined.any (fun r => r.item == "packages.counted" && r.value == 1) &&
      combined.any (fun r => r.item == "packages.rows" && r.value == 2))
  let changed := computeCoverageRows tiny #[{ pkg with documented := 3 }]
  expect "a stale combined package total changes a scoreboard row"
    (!(Scoreboard.ratchet
      { provenance := #[], rows := combined, retired := #[], lowered := #[],
        encoding := some (.pairs "counted" "rows") }
      { provenance := #[], rows := changed, retired := #[], lowered := #[],
        encoding := some (.pairs "counted" "rows") }).changes.isEmpty)
  let asTsv (rs : Array Scoreboard.Row) : Scoreboard.Tsv :=
    { provenance := #[], rows := rs, retired := #[], lowered := #[],
      encoding := some (.pairs "counted" "rows") }
  expect "the rows are a valid baseline" ((Scoreboard.validate (asTsv rows)).isEmpty)
  -- A pruned denominator is a fall under the one ratchet — a human act, not
  -- a rewrite of the header.
  let pruned := computeCoverageRows (tiny.filter (·.1.name != "zz")) #[]
  let d := Scoreboard.ratchet (asTsv rows) (asTsv pruned)
  expect "a smaller denominator is a fall the ratchet reports"
    (d.losses.any fun c => c.item == "kernel/Fonts.rows")
  -- The denominator parser, and the row `\#` whose line starts with one.
  expect "the denominator parser wants three fields"
    ((parseDenom "a\tb\n").toOption.isNone)
  expect "a provenance line has no tab"
    (isComment "# rows: 3" && !isComment "#\tSpecial insertions\tchar_given")
  expect "the hash command is a row, not a comment"
    (match parseDenom "# h\n#\tSpecial insertions\tchar_given\n" with
     | .ok d => d.rows.size == 1 && d.rows[0]!.name == "#"
     | .error _ => false)
  -- The header check, broken in both directions, and never a hint.
  let goodRows : Array KRow :=
    #[{ name := "a", chapter := "Fonts", cls := "call" },
      { name := "b", chapter := "Fonts", cls := "call" }]
  let stamped : Denom :=
    { provenance := #["# rows: 2", "# body: " ++ bodyStamp (denomBody goodRows)],
      rows := goodRows }
  expect "a stamped denominator passes" ((checkDenom stamped).isEmpty)
  let prunedMsgs := checkDenom { stamped with rows := goodRows.pop }
  expect "a pruned denominator fails" (!prunedMsgs.isEmpty)
  expect "and its message names no stamp to paste back"
    (prunedMsgs.all fun m => !containsSub m "adler32"
      && !containsSub m (bodyStamp (denomBody goodRows.pop)))
  expect "an edited row fails"
    (!(checkDenom { stamped with
        rows := #[{ name := "a", chapter := "Fonts", cls := "call" },
                  { name := "c", chapter := "Fonts", cls := "call" }] }).isEmpty)
  expect "a denominator with no stamp fails"
    (!(checkDenom { provenance := #["# rows: 2"], rows := goodRows }).isEmpty)
  -- One rule for "implemented", shared with the compat tier.
  expect "impl and inert count, a refusal does not"
    ((IndexRow.mk "body" "impl" "\\zz").implemented
      && (IndexRow.mk "body" "inert:no ink by design" "\\zz").implemented
      && !(IndexRow.mk "body" "refuse:N0102" "\\zz").implemented
      && !(IndexRow.mk "body" "refuse:W0301" "\\zz").implemented)
  let refusal := packageRow "zz" #[IndexRow.mk "body" "refuse:W0301" "\\zz"]
  expect "a refusal remains in the documented denominator"
    (refusal.documented == 1 && refusal.impl == 0)
  let refusalTotals := totalsOf #[] #[] #[refusal]
  expect "the combined total includes every refusal"
    (refusalTotals.pDoc == 1 && refusalTotals.den == 1)
  -- The texinfo escapes, and a chapter title a reader reads.
  expect "a texinfo escape is harvested"
    (namesOnLine "@findex \\@@" == #["@"] && namesOnLine "@findex \\@{" == #["{"]
      && namesOnLine "@findex \\@}" == #["}"])
  expect "a control word is harvested" (namesOnLine "@findex \\hspace" == #["hspace"])
  expect "markup leaves a chapter title"
    (plainTitle "Overview of @LaTeX{}" == "Overview of LaTeX")
  expect "a plain title is unchanged" (plainTitle "Math formulas" == "Math formulas")
  expect "tenths rounds" (tenths 1 3 == 333 && tenths 2 3 == 667 && tenths 1 2 == 500)
  expect "pct renders" (pct 605 1314 == "46.0%")
  -- The positive control, both directions: the corpus is evidence from the
  -- artifact side, and a context-blind place list must fail it.
  match (← IO.FS.readFile denomPath |>.toBaseIO) with
  | .error _ => expect "the denominator is readable for the corpus control" false
  | .ok text =>
    match parseDenom text with
    | .error _ => expect "the denominator parses for the corpus control" false
    | .ok d =>
      expect "the committed denominator reads \\mho as defined only as an error"
        (d.rows.any fun r => r.name == "mho" && r.cls == notBaseClass)
      let hits ← corpusContradictions places d.rows
      for c in hits do
        if (explained c.name).isNone then
          expect s!"the corpus uses \\{c.name} in {c.file} and the probe reads \
{c.rung.word}" false
      -- Every explanation still explains something, and says true of its side.
      for e in witnessExplained do
        match hits.find? (·.name == e.name) with
        | none => expect s!"the explanation for \\{e.name} is stale — drop it" false
        | some c =>
          let answered := answeredIn e.name c.rung e.usage
          if e.side == .probe && !answered then
            expect s!"\\{e.name} is filed as the probe's miss, and its natural \
usage is not answered either" false
          if e.side == .corpus && answered then
            expect s!"\\{e.name} is filed as a real gap, and its natural usage \
is answered" false
      for e in falseQueue do
        let rung := pr e.name
        if rung.counted then
          expect s!"\\{e.name} is answered by the probe now — drop its row" false
        else if !answeredIn e.name rung e.usage then
          expect s!"\\{e.name}'s natural usage is not answered — it is a real \
gap, not the probe's miss" false
      let blind ← corpusContradictions contextBlindPlaces d.rows
      let blindUnexplained := blind.filter fun c => (explained c.name).isNone
      expect "the corpus control fails on context-blind places"
        (!blindUnexplained.isEmpty)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--report"] => report
  | ["--denominator", texi] => denominator texi
  | _ => Scoreboard.tierMain "coverage" (.pairs "counted" "rows") measureTier selftest args
