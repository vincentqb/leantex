/-
The coverage tier: per manual chapter and for the package indexes in aggregate, the documented
commands (`.rows`) and those whose probed rung reaches `rewritten` (`.counted`).
Usage: lake build ScriptsModules && lake env lean --run scripts/coverage.lean [--check | --selftest | --report | --denominator <latex2e.texi>]
-/
import LeanTex
import scripts.Board
import scripts.Rung

open LeanTex.Core

def denomPath : String := "testdata/coverage/latex2e-index.txt"
def corpusDir : System.FilePath := "testdata/corpus"

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- One kernel row: the command, the manual chapter documenting it, and the meaning
lualatex gives it. -/
structure KRow where
  name : String
  chapter : String
  cls : String
deriving Inhabited, BEq

/-- Commands whose lualatex meaning is a math symbol, excluded by the engine's own
report. -/
def mathClass : String := "math_given"

/-- Commands `latex.ltx` defines only as the `\not@base` error, excluded by lualatex's
reading too. -/
def notBaseClass : String := "not_base"

/-- The TeX register classes: lengths, glues and counters, counted in an item of their
own. -/
def registerClasses : List String := ["assign_dimen", "assign_glue", "assign_int"]

def KRow.counted (r : KRow) : Bool := r.cls != mathClass && r.cls != notBaseClass

def KRow.isRegister (r : KRow) : Bool := registerClasses.contains r.cls

/-- The scoreboard item a row belongs to. -/
def KRow.item (r : KRow) : String :=
  if r.isRegister then "kernel/registers" else "kernel/" ++ r.chapter

/-- Split on the first tab, keeping the rest whole. -/
def tabs (line : String) : Array String :=
  (line.splitOn "\t").toArray.map (·.trimAscii.toString)

/-- A provenance line, as distinct from a data row: a `#` with no tab after it, since `\#`
is a documented command. -/
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

/-- The committed body's fingerprint (rows, bytes, Adler-32), which catches an accidental
edit; a deliberate prune is a ratcheted fall. -/
def bodyStamp (body : String) : String :=
  let b := body.toUTF8
  s!"{b.size} bytes, adler32 {Flate.hex16 (Flate.adler32 b).toUInt64}"

/-- The coverage cut: `rewritten` and above. -/
def Rung.counted (r : Rung) : Bool := r.level ≥ Rung.rewritten.level

def Rung.best (a b : Rung) : Rung := if a.level ≥ b.level then a else b

def Rung.worse (a b : Rung) : Rung := if a.level ≤ b.level then a else b

/-- The unknown-construct codes in text, where any command may stand. -/
def textUnknownCodes : List String := ["W0301", "W0302"]

/-- The math parser's decline (W0012), read as no information, since a math place only
rescues the constructs living in math. -/
def mathDeclinedCodes : List String := ["W0012"]

/-- The tokens the probe injects as arguments; a diagnostic naming one is a complaint
about the probe's own operand, so the construct read its argument. -/
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

/-- The subject keys a diagnostic names this construct by: `ctrl:` and `env:` with the
bare name, `math:` with its backslash. -/
def aboutKeys (name : String) : List String :=
  ["ctrl:" ++ name, "env:" ++ name, "math:\\" ++ name]

def isAbout (name : String) (d : Diag) : Bool :=
  match d.subject with
  | some s => (aboutKeys name).contains s
  | none => false

/-- The rung one `Loss` puts a construct on when a diagnostic carrying that loss names the
construct, the one place the ladder reads `Loss`. -/
def rungOfLoss : Loss → Rung
  | .dropped => .fails
  | .pending => .degraded
  | .degraded => .degraded
  | .standard => .native
  | .config => .skipped
  | .info => .rewritten

/-- One probe's rung from its diagnostics, the first rule that applies deciding: those
naming the construct, a rewrite to nothing, a subjectless or place-own complaint, a
rewrite note, a clean document, then operand complaints. -/
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

/-- The argument shapes every command is tried in: a fixed set of opaque argument tokens
and definer shapes, uniform and monotone, which `\zzfakecommandzz` stays `unknown`
through. -/
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

/-- A document context a construct can stand in, as a function from the spelled fragment
to a whole document whose wrapper draws no diagnostic. -/
structure Place where
  label : String
  doc : String → String

def wrap (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

def wrapPre (pre : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nx\n\\end{document}"

/-- An article body and its preamble, the context-blind places the corpus control must
fail with. -/
def contextBlindPlaces : Array Place :=
  #[{ label := "body", doc := wrap }, { label := "preamble", doc := wrapPre }]

/-- Every place, uniform across all names, each a context the engine models a family of
commands only inside. -/
def places : Array Place :=
  contextBlindPlaces ++ #[
    { label := "inline-math", doc := fun s => wrap ("$ " ++ s ++ " $") },
    { label := "display-math", doc := fun s => wrap ("\\[" ++ s ++ "\\]") },
    { label := "math-operand", doc := fun s => wrap ("$" ++ s ++ " x$") },
    { label := "tabular-cell",
      doc := fun s => wrap ("\\begin{tabular}{ll}\na " ++ s ++ " & b \\\\\n\\end{tabular}") },
    { label := "tabular-rule",
      doc := fun s => wrap ("\\begin{tabular}{ll}\n" ++ s ++ "\na & b \\\\\n\\end{tabular}") },
    { label := "float", doc := fun s => wrap ("\\begin{figure}\nx\n" ++ s ++ "\n\\end{figure}") },
    { label := "list-item",
      doc := fun s => wrap ("\\begin{itemize}\n\\item x " ++ s ++ "\n\\end{itemize}") },
    -- A dimension operand, where the registers (`\textwidth`, `\linewidth`) are answered.
    { label := "length-argument",
      doc := fun s => wrap ("\\begin{minipage}{0.5" ++ s ++ "}\nx\n\\end{minipage}") },
    -- After a label: `\ref{x}` with no `\label{x}` is a degraded reference, not a gap.
    { label := "after-label", doc := fun s => wrap ("\\section{s}\\label{x}\n" ++ s) },
    -- A titled document, which `\maketitle` is defined relative to.
    { label := "titled",
      doc := fun s => "\\documentclass{article}\n\\title{t}\n\\author{a}\n\\begin{document}\n"
        ++ s ++ "\n\\end{document}" }]

/-- The name a construct is swapped for when the effect question is asked:
one nothing can know. -/
def decoy (name : String) : String := "zqzqzq" ++ name

/-- Whether a name can be swapped for a decoy: control words only, so a control symbol
takes `native` on the absence of a diagnostic alone. -/
def isControlWord (n : String) : Bool := !n.isEmpty && n.all Char.isAlpha

/-- Whether a usage differs from the same shape in the same place with the command swapped
for a decoy, which shows the construct consumed its arguments. -/
def changesDoc (a b : String) : Bool := (Elab.run "effect" a).1 != (Elab.run "effect" b).1

/-- A place's own complaints around a name nothing knows, measured per place;
`rungOfProbe` reads them as a probe that perturbed its context. -/
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

/-- Probe one name through the engine's real dispatch in every shape and place and keep
the best rung; a clean shape with no effect is `skipped`. -/
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

/-- One name, on its own; a run measures the places once and calls `probeIn`. -/
def probe (name : String) : Rung := probeIn (measurePlaces places) name

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

/-- How many probe tasks stand at once; one task per name contends on the allocator. -/
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

/-- The rung of every counted kernel row, measured once, in parallel. -/
def measureKernel (rows : Array KRow) : Array (KRow × Rung) :=
  let ps := measurePlaces places
  parMap (rows.filter (·.counted)) fun r => (r, probeIn ps r.name)

/-- The rows a run computes: per kernel item, `<item>.rows` and `<item>.counted`, every
item in both so a count falling to zero is a regression. -/
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

/-- The complete coverage measurement: kernel items per chapter and the package half as
one aggregate pair. -/
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

/-- Control words a source uses, `%` comments stripped; names in verbatim or user
definitions are still collected, so contradictions are read against an exemption table. -/
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

/-- A subject naming the construct under its own key, a longer one, or the
rewrite-to-nothing key. -/
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

/-- The corpus control, both ways: a fixture uses a name the probe puts below the cut, and
the fixture's own elaboration never reports it unknown, or names it not at all. -/
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
  /-- The fixture's use is not evidence, and the construct really is where the probe put
  it. -/
  | corpus
  /-- The engine answers the construct and no fragment the probe writes can spell it: a
  known false reading below the cut. -/
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

/-- Whether the engine answers the construct in this usage at the level a contradiction on
`rung` asks about. -/
def answeredIn (name : String) (rung : Rung) (u : Usage) : Bool :=
  let ds := (Elab.run "usage" u.doc).2
  if rung == .unknown then !ds.any (reportsUnknown name) else !ds.any (namesConstruct name)

structure Explanation where
  name : String
  side : Side
  usage : Usage
  why : String

/-- The corpus contradictions explained, each with its side and a natural usage that must
read the way that side says; a stale row fails `--selftest`. -/
def witnessExplained : Array Explanation := #[
  { name := "accent", side := .corpus, usage := ⟨false, "\\accent127 a"⟩,
    why := "a palette role named in a theme block, not the kernel's \\accent" },
  { name := "begin", side := .probe, usage := ⟨false, "\\begin{center}x\\end{center}"⟩,
    why := "half of a delimiter pair: no fragment can spell it alone" },
  { name := "documentclass", side := .probe, usage := ⟨false, "x"⟩,
    why := "a document's identity: every probe document already declares one" },
  { name := "end", side := .probe, usage := ⟨false, "\\begin{center}x\\end{center}"⟩,
    why := "half of a delimiter pair: no fragment can spell it alone" },
  { name := "fill", side := .probe, usage := ⟨false, "\\vspace{\\fill}"⟩,
    why := "answered as glue, \\vspace{\\fill}; the fixture's is TikZ's path command, and no \
probe token is a glue value" },
  { name := "hsize", side := .probe, usage := ⟨false, "\\hsize=10pt x"⟩,
    why := "answered as a TeX parameter's assignment; the fixture's sits in a \
\\renewcommand{\\@maketitle} body elaboration never reaches" },
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
  { name := "raisebox", side := .probe, usage := ⟨false, "a\\raisebox{1pt}{x}b"⟩,
    why := "a native box whose lift is a length, which no probe token is" },
  { name := "right", side := .probe, usage := ⟨false, "$\\left( x \\right)$"⟩,
    why := "a delimiter operand: no probe token is a delimiter" },
  { name := "rule", side := .probe, usage := ⟨false, "\\rule{1pt}{1pt}"⟩,
    why := "a native two-dimension command whose probe operands are not readable lengths" },
  { name := "usepackage", side := .probe, usage := ⟨true, "\\usepackage{amsmath}"⟩,
    why := "a package name: no probe token names a package the engine reads" },
  { name := "vbox", side := .corpus, usage := ⟨false, "\\vbox{x}"⟩,
    why := "inside a \\renewcommand{\\@maketitle} body elaboration never reaches" }]

/-- Known false readings no fixture witnesses, held both ways like `witnessExplained`. -/
def falseQueue : Array Explanation := #[]

def explained (name : String) : Option Explanation :=
  witnessExplained.find? (·.name == name)

def loadKernel : IO Denom := do
  unless (← System.FilePath.pathExists denomPath) do
    throw (IO.userError s!"coverage: {denomPath} is missing — run --denominator")
  match parseDenom (← IO.FS.readFile denomPath) with
  | .error e => throw (IO.userError ("coverage: " ++ e))
  | .ok d => return d

/-- The denominator's header checked before the file is trusted: its row count and body
stamp, with no message printing a value to paste back. -/
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

/-- The tier's provenance; the package aggregate is also a scoreboard pair, so these
totals cannot go stale apart from `--check`. -/
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
the compat tier: {t.pImpl} implemented of {t.pDoc} documented (testdata/compat-index; `impl` \
or `inert:`).",
    s!"# total: {t.num}/{t.den} = {pct t.num t.den}"]

/-- One measurement for the tier: the denominator's header checked and every counted
kernel name probed. -/
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
        -- Only a row that is one control word is comparable.
        if call.startsWith "\\" && isControlWord (call.drop 1).toString then
          let name := (call.drop 1).toString
          comparable := comparable + 1
          let rung := pr name
          -- `refuse:W0301` is unknown; every other annotation asserts recognition.
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
            -- Recognition agrees; `inert:` and `skipped` are one judgement, counted differently.
            counting := counting.push s!"  {pkg}\t{call}\tindex:{ann}\tmeasured:{rung.word}"
  IO.println s!"-- {disagree} recognition disagreement(s) over {comparable} comparable \
row(s), one control word each, of {t.pDoc} documented"
  for c in counting do IO.println c
  IO.println s!"-- {counting.size} row(s) the package half counts and the kernel rule \
would not"
  return 0

/-- Texinfo's `@@`, `@{` and `@}` read as the character they stand for, so `\@`, `\{` and
`\}` enter the denominator. -/
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

/-- The Lua the confirmation runs: lualatex's own `token.is_defined` and `cmdname` per
name, and `notBaseClass` for a macro whose body begins `\not@base`. -/
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

/-- The confirmation wrapper: a bare class with no packages, since amsmath turns seven
math symbols into macros. -/
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

/-- Rebuild the kernel denominator from the reference manual alone, its probe inputs
written and run here; never part of a gate. -/
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
  IO.FS.createDirAll "testdata/coverage"
  IO.FS.writeFile denomPath (head ++ body)
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", dir] }
  IO.println s!"coverage: wrote {denomPath} with {sorted.size} confirmed names \
of {cands.size} indexed"
  return 0

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
  -- `\begin`, `\end` and `\documentclass` cannot be fragments, so `unprobed`, not a gap.
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
    let ds := (Elab.run "p" (p.doc "\\enquote{x}")).2
    expect "a rewrite beside the place's own complaint does not count"
      (rungOfProbe "enquote" own ds == .unprobed
        && rungOfProbe "enquote" #[] ds == .rewritten)
  expect "no other place owns a complaint"
    (measured.all fun (p, own) => p.label == "length-argument" || own.isEmpty)
  expect "an operand complaint is evidence of dispatch"
    (rungOfProbe "ref" #[] (Elab.run "p" (wrap "\\ref{x}")).2 == .degraded)
  expect "a counter name is answered where a text group is not"
    ((pr "setcounter").counted && (pr "stepcounter").counted
      && (pr "addtocounter").counted && (pr "refstepcounter").counted)
  expect "a rewrite onto nothing is skipped, not translated"
    (rungOfProbe "nonfrenchspacing" #[] (Elab.run "p" (wrap "\\nonfrenchspacing")).2 == .skipped
      && pr "nonfrenchspacing" == .skipped && pr "PackageWarning" == .skipped)
  -- The silence guard's W0387 carries `ctrl:<name>`, so its two log commands read `skipped`.
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
  -- A pruned denominator is a fall under the one ratchet.
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
  -- The positive control, both ways: a context-blind place list must fail it.
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
