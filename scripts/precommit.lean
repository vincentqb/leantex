/-
Pre-commit gate: compile+lint via lake build --wfail, plus convention checks
over the staged diff. Silent on success. Git executes the FILE
scripts/hooks/pre-commit, a 3-line sh trampoline that runs this after a cheap
staged-file filter; install with: git config core.hooksPath scripts/hooks
-/

import scripts.Gate

def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  if out.exitCode != 0 then
    IO.eprintln s!"pre-commit: git {String.intercalate " " args.toList} failed:\n{out.stderr}"
    IO.Process.exit 1
  return out.stdout

def relevant (f : String) : Bool :=
  f.endsWith ".lean" || f == "lakefile.toml" || f == "lakefile.lean"
    || f == "lean-toolchain" || f.startsWith "tests/golden/" || f == "PLAN.md"

/-- The owed-theorem staging area (see scripts/owed.lean): the one path
where a stated obligation may hold its proof open. -/
def obligationsFile (f : String) : Bool :=
  f == "Obligations.lean" || f.startsWith "Obligations/"

/-- The banned words, composed so this file's own staged diff never contains
them as word-delimited tokens — the gate scans every .lean file, itself
included. -/
def kwPartial : String := "par" ++ "tial"
def kwUnsafe : String := "uns" ++ "afe"

/-- Composed for the same reason: prepending to a recursive call's result
copies that result at every element. -/
def patAppend : String := "+" ++ "+"

/-- Composed like the banned keywords: the selftest must hold lines that
ARE markers, and this file's own staged diff may not carry one. (The rule
below fires only at line start, so an indented literal could not trip it
anyway — the composition keeps that true under any reformat.) -/
def mkOurs : String := "<<<" ++ "<<<<"
def mkTheirs : String := ">>>" ++ ">>>>"
def mkBase : String := "|||" ++ "||||"

/-- A merge-conflict marker line: exactly seven `<`, `>`, or `|` opening
the line, then end-of-line or whitespace — the shape git writes
(`<<<<<<< HEAD`, `||||||| base`, `>>>>>>> theirs`). Two deliberate
non-matches, each avoiding a false positive: `=======` alone is a markdown
setext rule and a Lean comment banner, and a wrongly resolved merge always
carries a `<<<<<<<`/`>>>>>>>` sibling this rule does catch; an eighth
marker char (`<<<<<<<<`, a decorative banner) also passes, since git
writes exactly seven. -/
def conflictMarker (l : String) : Bool :=
  [mkOurs, mkTheirs, mkBase].any fun m =>
    l.startsWith m &&
      match ((l.drop 7).toString).toList.head? with
      | none => true
      | some c => c.isWhitespace

/-- Added lines carrying a conflict marker, with file, new-file line
number, and the line itself, from a unified=0 cached diff over every
staged file — staged content, which is what the commit will contain, not
the working tree. Binary files produce no `+` content lines and are
skipped by construction. -/
def conflictMarkers (diff : String) : Array (String × Nat × String) := Id.run do
  let mut out : Array (String × Nat × String) := #[]
  let mut file := ""
  let mut line := 0
  for l in diff.splitOn "\n" do
    if l.startsWith "+++ " then
      file := if l.startsWith "+++ b/" then (l.drop "+++ b/".length).toString else ""
    else if l.startsWith "@@" then
      -- @@ -a,b +c,d @@ — the next added line is new-file line c
      let plus := ((l.splitOn "+").getD 1 "").takeWhile Char.isDigit
      line := (plus.toString.toNat?).getD 0
    else if l.startsWith "+" then
      if !file.isEmpty && conflictMarker ((l.drop 1).toString) then
        out := out.push (file, line, (l.drop 1).toString)
      line := line + 1
  return out

def tokens (s : String) : List String :=
  (s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty)

/-- One applied name, dotted qualification included (`Ir.dumpInlineList`). -/
def isAtom (w : String) : Bool :=
  !w.isEmpty && w.toList.all (fun c => isWordChar c || c == '.')

/-- Is the append writing back onto the very name it extends
(`s := s ++ one x`)? That appends in place under unique ownership — the
blessed `mut` accumulator pattern — it does not copy a recursive result. -/
def selfAppend (lhs : String) : Bool :=
  match (lhs.splitOn ":=").reverse with
  | after :: before :: _ =>
    match tokens after, (tokens before).reverse with
    | [n], target :: _ => n == target
    | _, _ => false
  | _ => false

/-- Does the text after the line's last append read as a plain application
of two or more names ending in a bare variable (`… ++ walk cfg rest`)? That
is the spelling of every quadratic walk this tree has produced — with or
without a `#[` literal, qualified head (`Mod.f rest`) included: prepending
to the recursive call's result copies it at every element. Still legal: a
bare name after the append (the one-off prepend escape — bind the call to a
name first), a parenthesised append (`walk cfg (acc ++ node x) rest` extends
an accumulator), an RHS with non-name structure (literals, brackets), a
self-append (`s := s ++ one x`), and an RHS ending in a projection
(`out.extract i out.size` splices, it does not walk a tail). Line-local: an
application split across lines is not seen. -/
def quadraticPrepend (l : String) : Bool :=
  match (l.splitOn patAppend).reverse with
  | rhs :: lhs :: _ =>
    let ws := tokens rhs
    ws.length ≥ 2 && ws.all isAtom
      && (ws.getLastD "").toList.all isWordChar
      && !selfAppend lhs
  | _ => false

/-- The text of the innermost paren group still open at the end of `pre`,
with closed inner groups dropped: for `(f : (A → B) ` that is `f : `. -/
def lastOpenGroup (pre : String) : Option String :=
  let step : List String → Char → List String := fun st c =>
    match c, st with
    | '(', _ => "" :: st
    | ')', _ :: rest => rest
    | c, cur :: rest => (cur.push c) :: rest
    | _, [] => []
  (pre.toList.foldl step []).head?

/-- Does the group read `name :` — a binder with a type ascription, the only
opening a constructor field default can live in? A named argument `(n := 3)`
has no ascription colon and stays legal. -/
def binderish (g : String) : Bool :=
  let g := g.trimAscii.toString
  let name := (g.takeWhile isWordChar).toString
  !name.isEmpty && ((g.drop name.length).toString.trimAscii.toString).startsWith ":"

/-- Is some `:=` on the line inside a paren group that opens `(name :`? -/
def hasBinderDefault (t : String) : Bool := Id.run do
  let mut pre := ""
  for p in (t.splitOn ":=").dropLast do
    pre := pre ++ p
    if (lastOpenGroup pre).any binderish then return true
    pre := pre ++ ":="
  return false

/-- An inductive constructor field with a default value: patterns then
under-specify silently (`.run a b c` once matched only the default — PLAN
2026-09-15). Structure fields keep their defaults; their lines do not start
with `|`. The default lives in a binder, `(name : … := …)`, so the `:=`
must sit inside a paren group that opens like one: a `:=` elsewhere on a
`|` line — a Markdown table row in a docstring, a named argument — is not a
field default, and requiring the binder (rather than the absence of `=>`)
keeps a lambda default like `(f : α → β := fun _ => c)` caught. Takes the
raw diff line, `+` prefix included. -/
def ctorDefault (l : String) : Bool :=
  let t := (l.drop 1).toString.trimAscii.toString
  t.startsWith "|" && hasBinderDefault t

/-- Added lines of one unified diff, attributed to their file. -/
def addedByFile (diff : String) : Array (String × Array String) := Id.run do
  let mut out : Array (String × Array String) := #[]
  let mut cur : Option String := none
  let mut lines : Array String := #[]
  for l in diff.splitOn "\n" do
    if l.startsWith "+++ b/" then
      if let some f := cur then out := out.push (f, lines)
      cur := some (l.drop "+++ b/".length).toString
      lines := #[]
    else if l.startsWith "+" && !l.startsWith "+++" then
      lines := lines.push (l.drop 1).toString
  if let some f := cur then out := out.push (f, lines)
  return out

/-- Modules that consume the IR and must never reach back into the surface:
re-parsing is how md→PDF and tex→HTML would decay into N×M special cases. -/
def backendFiles : List String :=
  ["LeanTex/Core/Layout.lean", "LeanTex/Core/Pdf.lean",
   "LeanTex/Core/Html.lean", "LeanTex/Core/HtmlDoc.lean"]

/-- `IO` named outside a comment. A string literal naming IO still matches,
and a block comment's continuation line naming IO still matches — both
stated blind spots of the line scanner, not claims the gate makes. -/
def ioInCore (l : String) : Bool :=
  hasWord (stripLineComment l) "IO"

def surfaceMods : List String := ["Lex", "Parse", "Elab", "Compat"]

/-- Composed like the banned keywords: the gate scans this file's own staged
diff, and the pattern must not read as a violation where it is defined. -/
def kwSeverityAssign : String := "sever" ++ "ity :="

/-- A literal severity assignment: severity derives from a `DiagCode`'s
declared `Loss` through `Diag.of`, never chosen at a call site, so the field
may be written in Diag.lean alone. String and comment content aside. -/
def severityAssign (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) kwSeverityAssign

def surfaceImports : List String := surfaceMods.map ("import LeanTex.Core." ++ ·)

/-- A qualified use `Mod.…` with nothing word-like before the name: catches
`Parse.scanOpt` and `LeanTex.Core.Parse.scanOpt`, not `myParse.foo`. -/
def usesQualified (l mod : String) : Bool :=
  (l.splitOn (mod ++ ".")).dropLast.any fun p =>
    match p.toList.getLast? with
    | none => true
    | some c => !isWordChar c

/-- A bare dimension literal (`pt 14`, `mm 5`, `inch 1`, `mm100 140`): a
design value spelled at a use site with no same-line `--` comment to carry
its source. The comment is taken as the source whatever it says — the gate
checks that a why was written, not that it is right — and same-line is a
stated limit of the diff scanner: it cannot see a comment on the line
above. -/
def dimLiteral (l : String) : Bool :=
  if containsSub l "--" then false
  else
    ["pt", "mm", "mm100", "inch"].any fun u =>
      let parts := l.splitOn (u ++ " ")
      (parts.zip parts.tail).any fun (before, after) =>
        (match before.toList.getLast? with
         | none => true
         | some c => !isWordChar c)
        && (after.toList.head?.map Char.isDigit).getD false


def isVarToken (w : String) : Bool :=
  !w.isEmpty && w.toList.all isWordChar
    && (w.toList.head?.map Char.isLower).getD false

/-- The pattern and RHS of a line-leading match arm, when the line is one
(`| pat => rhs` with exactly one `=>`). An arm split across lines, or an
arm not opening the line, is not seen — a stated line-scanner blind spot. -/
def armParts (l : String) : Option (List String × List String) :=
  let t := (stripLineComment l).trimAscii.toString
  if !t.startsWith "|" then none
  else match (t.drop 1).toString.splitOn "=>" with
    | [pat, rhs] => some (tokens pat, tokens rhs)
    | _ => none

/-- The identity catch-all of a rewrite walk: a match arm whose pattern is
one bare variable and whose RHS is that same variable (`| other => other`).
It is how a new IR constructor ships through a walk untouched — the walks
in Ir.lean and Layout.lean spell every constructor now, and the compiler
turns the next constructor into a build error at each. -/
def identityArm (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) => p == r && isVarToken p
  | _ => false

/-- A catch-all arm answering a bare numeral (`| _ => 1`): the measure-walk
default that once kept a step inside a section title off the handout.
Checked only in Ir.lean, where every walk over the IR lives. -/
def wildcardNumeral (l : String) : Bool :=
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || isVarToken p) && !r.isEmpty && r.toList.all Char.isDigit
  | _ => false

/-- The registered conservation-shape suffixes: a public IR-to-IR walk's
census statement is the walk's name plus one of these — census equality
(`dimBlocks_text`), leaf coverage (`keepFor_covers`), or conditional
identity (`substPage_id`). AGENTS.md § Conventions carries the
reviewer-facing suffix registry; this list is its mechanical half. -/
def conservesSuffixes : List String := ["_text", "_covers", "_id"]

/-- A public IR-to-IR walk entry: a non-private `def`, signature on one
line, taking and returning `Array Block` or `Array Inline` — the shape
whose census fact the obligation table's walk row owes. Returns the def's
name. A signature split across lines is not seen — the same line-scanner
limitation as `ioInCore`, stated, not claimed away. -/
def walkEntry (l : String) : Option String := Id.run do
  let t := stripLineComment l
  unless t.startsWith "def " do return none
  let name := String.ofList (((t.drop 4).toString).toList.takeWhile isWordChar)
  if name.isEmpty then return none
  let parts := t.splitOn ") : "
  if parts.length < 2 then return none
  let ret0 := ((parts.getLast?.getD "").splitOn ":=").headD ""
  let ret := (ret0.trimAscii).toString
  unless ret == "Array Block" || ret == "Array Inline" do return none
  -- an IR-to-IR walk consumes what it returns: a parameter carries the type
  let params := String.intercalate ") : " parts.dropLast
  unless containsSub params s!": {ret}" do return none
  return some name

/-- The escape a walk that genuinely conserves nothing writes beside its
def: a comment line carrying `conserves: none` and the reason. -/
def conservesNone (l : String) : Bool :=
  containsSub l "conserves: none"

/-- A backend reaching into the surface: an import, an `open`, or a
qualified use of a surface module, comments aside. An alias
(`abbrev P := LeanTex.Core.Parse` elsewhere) would not be seen — the same
line-scanner limitation as `ioInCore`, stated, not claimed away. -/
def surfaceReach (l : String) : Bool :=
  let l := stripLineComment l
  let t := l.trimAscii.toString
  surfaceImports.any (t == ·)
    || (t.startsWith "open " && surfaceMods.any (hasWord t ·))
    || surfaceMods.any (usesQualified l ·)

/-- HTML built by concatenating tag strings: the exact shape AGENTS.md bans
(`"<" ++ …`) everywhere but the typed tree's own renderer (Html.lean, which
the caller exempts by file). A multi-character tag literal (`"<div>" ++`)
is a stated blind spot — Pdf.lean's CMap and XMP writers legitimately build
non-HTML angle-bracket text that way. -/
def tagStringEmit (l : String) : Bool :=
  ((stripLineComment l).splitOn "\"<\"").drop 1 |>.any fun rest =>
    rest.trimAscii.toString.startsWith patAppend

/-- `pat` with no identifier character following — so `FontDb.scan` does not
match `FontDb.scanRoots`. `hasWord` cannot carry a dotted name: the dot is
a word delimiter. -/
def hasCall (line pat : String) : Bool :=
  ((line.splitOn pat).drop 1).any fun rest =>
    match rest.toList with
    | [] => true
    | c :: _ => !isWordChar c

/-- A host font scan in a test: `FontDb.scan` where only the shipped-corpus
`FontDb.scanRoots [testFonts]` is hermetic (AGENTS.md, Conventions). -/
def fontScanInTest (l : String) : Bool :=
  hasCall (stripLineComment (stripStrings l)) "FontDb.scan"

/-- The marker stating why an `Ir.dump` read in a test is not a page claim;
its presence on the line is the escape the gate honours. -/
def irTierMark : String := "-- ir tier:"

/-- An IR dump in a test without its stated tier. `Ir.dump` and its walk
companions all match: each reads the IR, and a page claim judged there is
the six-visual-defects shape (AGENTS.md, Conventions). -/
def irDumpUnmarked (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) "Ir.dump" && !containsSub l irTierMark

/-- Handed by impl-proofs: a heartbeat raise is a proof smell, not a budget
knob — the tree holds zero. Composed self-diff-safe, like the keywords. -/
def kwMaxHeartbeats : String := "maxHeart" ++ "beats"

def heartbeatRaise (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) kwMaxHeartbeats

/-- Handed by impl-shapes: a catch-all arm that ships its scrutinee or an
accumulator through unchanged (`| _ => out`, `| other => other`) — in an IR
walk that is the next constructor silently falling through. A `none`/`nil`
pattern is a constructor match, not a catch-all; an answer (`false`,
`none`) or a control keyword (`break`) as RHS is a decision, not a
pass-through. -/
def wildcardThrough (l : String) : Bool :=
  let answers := ["false", "true", "none", "nil", "break", "continue", "return"]
  match armParts l with
  | some ([p], [r]) =>
    (p == "_" || (isVarToken p && p != "none" && p != "nil")) &&
      isVarToken r && !answers.contains r
  | _ => false

/-- `]!` sites in a file, strings and comments aside — the panic-on-miss
index COMMON bans adding to reach green. -/
def bangCount (ls : Array String) : Nat := Id.run do
  let mut n := 0
  for l in ls do
    n := n + ((stripLineComment (stripStrings l)).splitOn "]!").length - 1
  return n

/-- The frozen `]!` counts per file (whole LeanTex/ tree, 2026-09-18). A
commit may lower a file's count — and then lowers its row — never raise
it. Regenerate after removing sites: `bangCount` over the file. -/
def bangBaseline : List (String × Nat) := [
  ("LeanTex/Cli/Render.lean", 2),
  ("LeanTex/Core/Compat.lean", 2),
  ("LeanTex/Core/Elab.lean", 3),
  ("LeanTex/Core/Flate.lean", 2),
  ("LeanTex/Core/Font.lean", 3),
  ("LeanTex/Core/FontDb.lean", 11),
  ("LeanTex/Core/HtmlDoc.lean", 4),
  ("LeanTex/Core/Hyphen.lean", 4),
  ("LeanTex/Core/Ir.lean", 2),
  ("LeanTex/Core/Layout.lean", 41),
  ("LeanTex/Core/Lex.lean", 2),
  ("LeanTex/Core/MathParse.lean", 1),
  ("LeanTex/Core/Pdf.lean", 10),
  ("LeanTex/Core/Utf8.lean", 4)]

/-- The line's string-literal contents, concatenated — `stripStrings`'
complement, with its stated line-scanner limitations. What the engine says
to a user lives in string literals; this is the text the self-containment
gate reads. -/
def stringsOnly (l : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut esc := false
  for c in l.toList do
    if inStr then
      if esc then
        esc := false
        out := out.push c
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
      else out := out.push c
    else if c == '"' then
      inStr := true
      out := out.push ' '
  return out

/-- A milestone token (`M6`, `M8`, …): an internal name that means nothing
outside this repository. -/
def milestoneTok (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  for i in [0:cs.size] do
    if cs[i]! == 'M' && ((cs[i+1]?.map Char.isDigit).getD false)
        && !(i > 0 && (isWordChar (cs[i-1]!)))
        && !((cs[i+2]?.map isWordChar).getD false) then
      return true
  return false

/-- A repo-internal reference inside a string literal: `PLAN.md`,
`AGENTS.md`, a `LeanTex/` path, or a milestone token. A diagnostic must be
actionable by someone holding only their own document — `see PLAN.md`
points at a file the user does not have (the diag-voice defect). Lines that
are themselves comments stay legal: prose for developers may name the plan. -/
def repoRefInString (l : String) : Bool :=
  let s := stringsOnly (stripLineComment l)
  containsSub s "PLAN.md" || containsSub s "AGENTS.md" ||
    containsSub s "LeanTex/" || milestoneTok s

/-- The Config fields the driver may read: the command, the diagnostic
channel, the where/when of a run, the run's acceptance policy, the font
environment — and `mathBoundary`, the one recorded artifact-shaping
remainder (see `artifact_flag_free` in Args.lean). `effectiveEmit` is the
planning function the theorem covers. A new entry lands here only after
the question "can it change a byte of the artifact?" is answered no — a
field that does shape the artifact is the theorem's counterexample, not a
new list entry. -/
def driverConfigReads : List String :=
  ["cmd", "verbosity", "quiet", "porcelain", "color", "output", "watch",
   "bestEffort", "werror", "fontDirs", "mathBoundary", "effectiveEmit"]

/-- A `cfg.<name>` read whose name is not on `driverConfigReads`, comments
and strings aside. This is how a new flag would reach a backend from the
driver — the thread starts as exactly this token in `Main.build` — so the
common leak is caught where it starts. Stated misses, line-scanner shaped:
a read that never spells the dot (destructuring, a helper handed the whole
`Config`), an alias (`let c := ui.cfg` then `c.newFlag`), and an
allowlisted field newly routed into a backend call. -/
def undeclaredConfigRead (l : String) : Bool := Id.run do
  let t := stripLineComment (stripStrings l)
  let parts := t.splitOn "cfg."
  let mut pre := parts.headD ""
  for p in parts.tail do
    let boundary := match pre.toList.getLast? with
      | none => true
      | some c => !isWordChar c
    if boundary then
      let field := (p.takeWhile isWordChar).toString
      if !field.isEmpty && !driverConfigReads.contains field then
        return true
    pre := pre ++ "cfg." ++ p
  return false

/-- No allowance remains: the last one (Elab.elabBlocks) came off on
2026-09-19 — `elaboration_total` names the fact — and the list is empty
and stays empty. -/
def partialAllowed (_l : String) : Bool := false

/-- The string-comparison spelling that compiles against the `DocClass`
inductive and bypasses exhaustiveness: `docClass.name == "…"` re-creates
the stringly class checks the inductive replaced, one flag at a time. The
plain `docClass == "article"` does not build, so the compiler owns that
spelling; this is the variant it cannot see. -/
def classNameCompare (l : String) : Bool :=
  containsSub (stripLineComment (stripStrings l)) "docClass.name =="

/-- The quoted names of the `nativePackages` list block in a Compat
source: from its `def nativePackages` line to the block's closing
bracket. Package names never contain a quote or a bracket, so the scan is
a line walk. -/
def nativePackagesOf (src : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut inside := false
  for l in src.splitOn "\n" do
    if (stripLineComment l).startsWith "def nativePackages" then
      inside := true
    else if inside then
      let mut parts := (l.splitOn "\"")
      let mut quoted := false
      for p in parts do
        if quoted then out := out.push p
        quoted := !quoted
      if containsSub (stripLineComment (stripStrings l)) "]" then
        inside := false
  return out

/-- One staged-diff check: which files it reads, the line predicate, the
headline naming the file, and the fix paragraph. The stanzas `main` used
to spell one by one differed only in these four fields. -/
structure Gate where
  applies : String → Bool
  flag : String → Bool
  what : String → String
  help : String

def gates : List Gate := [
  { applies := (·.startsWith "LeanTex/")
    flag := classNameCompare
    what := fun f => s!"a class judged by its name string (`docClass.name ==`) in {f}"
    help := "  The DocClass inductive exists so a class check is a match the compiler
  keeps exhaustive; comparing the name string re-creates the stringly
  checks it replaced, invisible to the next constructor.
  Fix: match on the constructor; a genuinely name-shaped need (a
  diagnostic quoting the class) reads .name without comparing it." },
  { applies := fun _ => true
    flag := fun l => bannedWord kwPartial l && !partialAllowed l
    what := fun f => s!"new '{kwPartial}' in staged changes to {f}"
    help := s!"  The tree holds no '{kwPartial}': every recursion terminates by a
  proved measure (elaboration_total names the elaborator's; AGENTS.md,
  Conventions, holds the technique).
  Fix: make the recursion structural (see AGENTS.md, Conventions)." },
  { applies := (!obligationsFile ·)
    flag := bannedWord kwSorry
    what := fun f => s!"'{kwSorry}' in staged changes outside Obligations/, in {f}"
    help := "  Fix: finish the proof -- a broken theorem is a broken build -- or, for a
  statement the engine does not yet earn, stage it as a recorded obligation
  under Obligations/ (see scripts/owed.lean; the ratchet applies)." },
  { applies := fun _ => true
    flag := bannedWord kwUnsafe
    what := fun f => s!"'{kwUnsafe}' in staged changes to {f}"
    help := s!"  Fix: stay in the safe fragment; {kwUnsafe} code voids the certification story." },
  { applies := fun _ => true
    flag := quadraticPrepend
    what := fun f => s!"'{patAppend} walk rest' (prepend to a recursive call's result) in {f}"
    help := "  Prepending to a recursive call's result copies it at every element -- it
  turned a 4 ms pass into 1157 ms, three times in one day (PLAN 2026-09-16).
  Fix: thread an Array accumulator through the walk (see Compat.rewriteList);
  a one-off prepend outside a recursion can bind the call to a name first." },
  { applies := fun _ => true
    flag := ctorDefault
    what := fun f => s!"inductive constructor field with a default value, in {f}"
    help := "  Defaults on constructor fields let patterns under-specify silently: `.run
  a b c` once matched only the default, with the whole suite green (PLAN
  2026-09-15).
  Fix: spell the field at every constructor site; defaults belong on structures." },
  { applies := (!obligationsFile ·)
    flag := importsObligations
    what := fun f => s!"import of Obligations outside the staging area, in {f}"
    help := "  Obligations is the owed-theorem staging area: statements with open proofs.
  The gated library must never depend on it (scripts/owed.lean also checks
  the whole tree).
  Fix: prove the statement and move it into its owner module first." },
  { applies := fun f => f.endsWith ".lean" && f != "LeanTex/Core/Diag.lean"
    flag := severityAssign
    what := fun f => s!"a severity written outside Diag.lean, in {f}"
    help := "  Severity is a function of the code's declared Loss — a free severity is how
  \"content silently gone\" shipped as a warning fourteen times (PLAN, the
  severity policy).
  Fix: emit through Diag.of with a DiagCode; if the code's loss category is
  wrong, change it in DiagCode.spec." },
  { applies := fun f => f.startsWith "LeanTex/" || f == "Main.lean"
    flag := repoRefInString
    what := fun f => s!"a repo-internal reference in a string the user can see, in {f}"
    help := "  A diagnostic is read by someone holding only their own document: PLAN.md,
  AGENTS.md, a LeanTex/ path, and milestone names (M6, M8) mean nothing
  there — 'see PLAN.md' shipped in real output (the diag-voice defect).
  Fix: say what happens and what to write instead; the voice lint in
  Tests.lean judges the registered text." },
  { applies := (· == "Main.lean")
    flag := undeclaredConfigRead
    what := fun f => s!"a Config read in {f} not on the driver's declared list"
    help := "  The artifact is a function of the document and the font environment;
  flags are not arguments to it (AGENTS.md, Conventions). A new Config
  field the driver reads is one question away from shaping the artifact,
  so it lands on driverConfigReads (scripts/precommit.lean) only after
  that question is answered no — and a flag that does shape the artifact
  breaks the theorem artifact_flag_free instead of growing the list.
  Fix: make it a document declaration (\\output) rather than a flag; a
  flag about where/when/how-loudly goes on the list, deliberately." },
  { applies := fun f => f.startsWith "LeanTex/Core/" && f != "LeanTex/Core/FontDb.lean"
    flag := ioInCore
    what := fun f => s!"IO in {f}"
    help := "  Modules under LeanTex/Core/ do no IO (FontDb is the one exception): files
  and fonts surface as request values the CLI driver fulfills.
  Fix: return a request value and fulfill it in Main.lean." },
  { applies := (·.startsWith "LeanTex/Core/")
    flag := identityArm
    what := fun f => s!"identity catch-all arm (`| x => x`) in {f}"
    help := "  A rewrite walk with a wildcard ships a new IR constructor through
  untouched -- the shape of the covered-content defect (PLAN 2026-09-17).
  Fix: spell every constructor; the compiler then makes the next
  constructor a build error at every walk (AGENTS.md, obligation table)." },
  { applies := (· == "LeanTex/Core/Ir.lean")
    flag := wildcardNumeral
    what := fun f => s!"wildcard arm answering a numeral (`| _ => 1`) in {f}"
    help := "  A measure walk with a numeric default silently miscounts a new IR
  constructor -- a step inside a section title got no handout page this
  way (PLAN 2026-09-17).
  Fix: spell every constructor and say what each one measures." },
  { applies := (backendFiles.contains ·)
    flag := surfaceReach
    what := fun f => s!"a backend reaches into the surface, in {f}"
    help := "  Backends consume the IR and nothing else; a backend that re-parses is how
  md→PDF and tex→HTML decay into N×M special cases (AGENTS.md, Conventions).
  Fix: put what the backend needs on the IR." },
  { applies := (backendFiles.contains ·)
    flag := dimLiteral
    what := fun f => s!"bare dimension literal in {f}"
    help := "  A design value in a backend is a token, or carries its source where it
  stands (AGENTS.md, obligation table): a loose `pt 14` is how a heading
  scale drifts from the type scale, invisibly.
  Fix: read a token/style/palette entry, or put the source in a `--`
  comment on the same line (the diff scanner cannot see the line above)." },
  { applies := fun f => backendFiles.contains f && f != "LeanTex/Core/Html.lean"
    flag := tagStringEmit
    what := fun f => s!"HTML built from tag strings, in {f}"
    help := "  HTML is a typed tree with a certified escaper; a concatenated tag skips
  the escaper by construction (AGENTS.md, Conventions). Html.lean's own
  renderer is the one sanctioned site.
  Fix: build the node with the typed constructors; the renderer emits it." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := fontScanInTest
    what := fun f => s!"FontDb.scan in {f}"
    help := "  Tests scan only the shipped corpus fonts — FontDb.scanRoots [testFonts]
  (AGENTS.md, Conventions); a host scan makes the suite depend on what
  this machine has installed.
  Fix: ship the font in tests/corpus/fonts/ and scan through testFonts." },
  { applies := fun f => f == "Tests.lean" || f.startsWith "Tests/"
    flag := irDumpUnmarked
    what := fun f => s!"Ir.dump in {f} without its stated tier"
    help := s!"  A claim about what a page shows never comes from an IR dump — six visual
  defects once passed a fully green suite that way (AGENTS.md, Conventions).
  Fix: assert over Layout.Out or the typed HTML tree; an IR-tier fact that
  is not a page claim says so on the line: `{irTierMark} <why>`." },
  { applies := fun f => f.startsWith "LeanTex/" && f.endsWith ".lean"
    flag := heartbeatRaise
    what := fun f => s!"a {kwMaxHeartbeats} raise in {f}"
    help := s!"  The tree holds zero heartbeat raises; a proof that needs one is telling
  you the definition's shape is wrong (the MarkdownDoc emit_body_title_first
  case), not that the budget is small.
  Fix: reshape the proof or the definition; if neither closes, state it in
  Obligations and report the blocker." }]

/-- Every case a gate predicate must catch and every legal spelling it must
pass, run by `lean --run scripts/precommit.lean --selftest` from `lake test`.
Positive cases are the shapes whose escape prompted a gate change; negative
cases are lines of this tree. A gate that does not catch the shape it
commemorates grants false confidence, so a gate change lands with both. -/
def selftest : IO UInt32 := do
  let fails ← IO.mkRef ([] : List String)
  let expect (name : String) (p : String → Bool) (cases : List (String × Bool)) : IO Unit := do
    for (line, want) in cases do
      if p line != want then
        fails.modify (s!"{name} {if want then "missed" else "fired on"}: {line}" :: ·)

  expect "quadraticPrepend" quadraticPrepend [
    -- the walks this tree has produced, all of which must fire
    ("  | x :: rest => inlineNode cfg x ++ inlineNodes cfg rest", true),
    ("  | x :: rest => plainTextOne x ++ plainTextList rest", true),
    ("  | x :: rest => dumpInline ind x ++ dumpInlineList ind rest", true),
    ("  | b :: rest => dumpBlock ind b ++ dumpBlockList ind rest", true),
    ("    s!\"{ind}item\\n\" ++ dumpBlocks (ind ++ \"  \") item ++ dumpItems ind rest", true),
    ("    | c :: rest => escapeCharText c ++ go rest", true),
    ("    | c :: rest => escapeCharAttr c ++ go rest", true),
    ("  | k :: rest, indent => render k indent ++ renderList rest indent", true),
    ("  | k :: rest => inlineRender k ++ inlineRenderList rest", true),
    ("  | r :: rest => rawSrcOne r ++ rawSrcList rest", true),
    ("  | b :: rest => #[blockNode cfg b] ++ blockNodes cfg rest", true),
    ("  | x :: rest => #[x] ++ Compat.rewriteList rest", true),
    -- legal spellings from this tree that must stay legal
    ("  | x :: rest => inlineNodes cfg (acc ++ inlineNode cfg x) rest", false),
    ("  | b :: rest => blockNodes cfg (acc.push (blockNode cfg b)) rest", false),
    ("  base ++ plus ++ minus", false),
    ("      | other => s := s ++ rawSrcOne other", false),
    ("        | some i => out.extract 0 i ++ running ++ out.extract i out.size", false),
    ("    s!\"{ind}styled {st.label}\\n\" ++ dumpInlines (ind ++ \"  \") body", false),
    ("        chosen := chosen ++ [b]", false),
    ("  | x :: rest => #[x] ++ rest", false)]

  expect "classNameCompare" classNameCompare [
    -- the spelling that compiles past the inductive, wherever it stands
    ("  if doc.docClass.name == \"article\" then", true),
    ("    (d.docClass.name == cls)", true),
    -- legal spellings: a match, a diagnostic quoting the name, prose
    ("  match doc.docClass with", false),
    ("    say s!\"class {doc.docClass.name} has no chapter pages\"", false),
    ("  -- a comment naming docClass.name == article does not count", false),
    ("    (\"docClass.name == inside a string\", true),", false)]

  expect "nativePackages parse" (fun s => (nativePackagesOf s).toList
      == ["geometry", "natbib"]) [
    -- the list block yields exactly its quoted names, quotes elsewhere
    -- ignored, the scan closed at the bracket
    ("def other : List String := [\"nope\"]\n" ++
     "def nativePackages : List String :=\n  [\"geometry\",\n   \"natbib\"]\n" ++
     "def after : String := \"also-not-a-package\"", true)]

  expect "conflictMarker" conflictMarker [
    -- the shapes git writes, all of which must fire
    (mkOurs ++ " HEAD", true),
    (mkTheirs ++ " theirs", true),
    (mkBase ++ " merged common ancestors", true),
    (mkOurs, true),
    (mkBase, true),
    -- near-misses that must pass: the setext rule / comment banner,
    -- an eight-run decorative banner, a six-run, mid-line, indented
    ("=======", false),
    (mkOurs ++ "<", false),
    ("<<<" ++ "<<<", false),
    ("a " ++ mkTheirs, false),
    ("  " ++ mkOurs ++ " HEAD", false),
    (mkOurs ++ "quoted", false)]

  -- the diff walker: staged content only, file and line attributed
  let d := "+++ b/PLAN.md\n@@ -3,0 +4,3 @@\n+prose\n+" ++ mkOurs ++ " HEAD\n+more"
  if conflictMarkers d != #[("PLAN.md", 5, mkOurs ++ " HEAD")] then
    fails.modify ("conflictMarkers missed or misattributed the PLAN.md case" :: ·)

  expect "bannedWord" (bannedWord kwPartial) [
    -- a declaration must still fire, wherever it stands on the line
    ("+" ++ kwPartial ++ " def foo : Nat := 0", true),
    ("+  " ++ kwPartial ++ " def go (l : List Nat) : Nat := go l", true),
    -- the escape that prompted the stripper: a command-name table entry
    ("+   (\"" ++ kwPartial ++ "\", .ord, '𝜕'),", false),
    ("+    say s!\"a message naming " ++ kwPartial ++ " in prose\"", false),
    -- comments are data too: the shared stripper ended the divergence where
    -- the hook fired on a comment the owed ratchet ignored
    ("+  -- a comment naming " ++ kwPartial ++ " does not count", false),
    -- word-delimiting still holds
    ("+  let " ++ kwPartial ++ "Sums := 3", false)]

  expect "ctorDefault" ctorDefault [
    -- a field default, with and without the lambda that evaded the old check
    ("+  | run (label : String := \"unnamed\") : Cmd", true),
    ("+  | mk (a : Nat) (f : Nat → Nat := fun _ => 0) : T", true),
    -- `|` lines that carry a `:=` without being a field default
    ("+  | `.run a b c` := what the pattern matched | the whole suite green |", false),
    ("+  | x => go (n := 3) rest", false),
    ("+  | x => { s with field := v }", false),
    ("+  | .text s => s", false)]

  -- `addedByFile` hands these two checks their lines with the `+` already
  -- stripped, unlike the whole-diff checks above.
  expect "ioInCore" ioInCore [
    ("def scan (roots : List String) : IO (Array Face) := do", true),
    ("    let bytes ← IO.FS.readBinFile path", true),
    -- a stated blind spot, pinned so a change to it is a deliberate one:
    -- a block comment's continuation line still looks like code
    ("continuation line of a block comment naming IO", true),
    -- the fix: `--` comments no longer trip the check
    ("  -- files and fonts surface as request values, never IO here", false),
    ("/-- Effects as data: the IO happens in Main.lean. -/", false),
    ("  let priority := ioPriority.toNat", false)]

  expect "surfaceReach" surfaceReach [
    ("import LeanTex.Core.Parse", true),
    ("open LeanTex.Core.Parse in", true),
    ("open Elab", true),
    ("  let opt := Parse.scanOpt args i", true),
    ("    LeanTex.Core.Compat.rewrite doc", true),
    ("import LeanTex.Core.Ir", false),
    ("  -- a backend never calls Parse.scanOpt; the IR carries it", false),
    ("  let reparse := myParse.run s", false),
    ("  openTag := elem tag attrs kids", false)]

  expect "tagStringEmit" tagStringEmit [
    -- the renderer's own shape: outside Html.lean it must fire, spaced or not
    ("    let open' := \"<\" " ++ patAppend ++ " tag " ++ patAppend ++ " attrString attrs", true),
    ("  out := out " ++ patAppend ++ " \"<\"" ++ patAppend ++ "tag", true),
    -- angle-bracket text that is not the banned shape stays legal:
    -- a multi-char literal (stated blind spot), an escaper arm, a CMap
    -- interpolation, and the shape quoted in a comment
    ("  \"<!DOCTYPE html>\\n\" " ++ patAppend, false),
    ("  if c == '<' then out := out " ++ patAppend ++ " \"&lt;\"", false),
    ("  s := s " ++ patAppend ++ " s!\"<{hex4 g}> <{utf16Hex c}>\\n\"", false),
    ("  -- writing \"<\" " ++ patAppend ++ " tag is banned here", false)]

  expect "fontScanInTest" fontScanInTest [
    -- the driver's spelling, which in a test is the hermeticity break
    ("  let faces ← FontDb.scan (cfg.fontDirs.toList ++ (← texFontDirs))", true),
    ("  let faces ← FontDb.scan", true),
    -- the hermetic spelling, a comment, and a string naming the call
    ("  let shipped ← FontDb.scanRoots [testFonts]", false),
    ("  -- FontDb.scan here would break hermeticity", false),
    ("  t \"a message naming FontDb.scan stays data\" true", false)]

  expect "irDumpUnmarked" irDumpUnmarked [
    -- dump and its walk companions, unmarked: all must fire
    ("    let out := Ir.dump doc diags", true),
    ("        ((Ir.dumpBlocks \"\" nbody).splitOn \"never shown\").length == 2", true),
    -- the stated-tier escape, a comment, and a string naming the call
    ("    let out := Ir.dump doc diags " ++ irTierMark ++ " goldens witness elaboration", false),
    ("  -- Ir.dump is rejected in tests without a tier", false),
    ("  t \"a message naming Ir.dump stays data\" true", false)]

  expect "heartbeatRaise" heartbeatRaise [
    -- the raise shapes, standalone and scoped
    ("set_option " ++ kwMaxHeartbeats ++ " 400000", true),
    ("  set_option " ++ kwMaxHeartbeats ++ " 1000000 in", true),
    -- a comment, a string, and the other budget option stay legal
    ("-- " ++ kwMaxHeartbeats ++ ": zero sites in the tree", false),
    ("  say s!\"raise " ++ kwMaxHeartbeats ++ "\"", false),
    ("set_option maxRecDepth 8192", false)]

  expect "wildcardThrough" wildcardThrough [
    -- the frozen pass-through shapes, all of which must fire
    ("  | _ => out", true),
    ("  | other => other", true),
    ("  | x => x", true),
    -- constructor matches, predicate answers, and multi-token arms stay legal
    ("  | none => acc", false),
    ("  | nil => simp [textLeavesTableCells]", false),
    ("  | _ => false", false),
    ("  | _ => none", false),
    ("  | _ => break", false),
    ("  | .text s => s", false),
    ("  | other => cur := cur.push other", false),
    ("  | _ => 1", false)]

  -- bangCount: strings and comments are data, code is counted
  if bangCount #["let x := xs[i]!", "-- xs[i]! in a comment",
      "say \"xs[i]! quoted\"", "ys[j]! + zs[k]!"] != 3 then
    fails.modify ("bangCount miscounted the mixed sample" :: ·)

  expect "identityArm" identityArm [
    -- the wildcard drops the walk audit found, all of which must fire
    ("  | other => other", true),
    ("  | x => x", true),
    -- explicit arms and non-arm lines that must stay legal
    ("  | .text s => .text s", false),
    ("  | .verbatim s => .verbatim s", false),
    ("  | .box .. | .pen .. => it", false),
    ("  | some x => x", false),
    ("  | [] => []", false),
    ("  | x :: rest => fillOne content x :: fillList content rest", false),
    ("| a docstring table row | with cells |", false),
    ("  -- | other => other, quoted in a comment", false)]

  expect "wildcardNumeral" wildcardNumeral [
    ("  | _ => 1", true),
    ("  | other => 1", true),
    -- a wildcard answering a non-numeral stays legal (a Nat scrutinee
    -- cannot spell every case), as does an explicit arm answering one
    ("  | _ => \"mono\"", false),
    ("  | _ => geom.fontSize", false),
    ("  | .verbatim _ => 1", false),
    ("  | [] => 1", false)]

  expect "dimLiteral" dimLiteral [
    -- the unsourced design values this tree has carried
    ("  | 1 => pt 14", true),
    ("        fun g => (a.resolve g).width).getD (pt 1)", true),
    ("  vmargin := Dim.mm 9", true),
    ("  if w > inch 1 then", true),
    ("  let floor := Dim.mm100 140", true),
    -- sourced or token-borne spellings that must stay legal
    ("  pageW : Sp := pt 612 -- US letter, the class default", false),
    ("  let w := scaledAt size font (font.advance c)", false),
    ("  let s := v.toPtString", false),
    ("  let g := (a.resolve tok).width", false),
    ("  let mmNames := [\"mm\", \"cm\"]", false)]

  expect "obligationsFile" obligationsFile [
    -- the staging area, root module and any future submodule
    ("Obligations.lean", true),
    ("Obligations/Conservation.lean", true),
    -- everything else keeps the flat ban
    ("LeanTex/Core/Ir.lean", false),
    ("Tests.lean", false),
    ("scripts/owed.lean", false),
    ("ObligationsExtra.lean", false)]

  expect "importsObligations" importsObligations [
    ("import Obligations", true),
    ("import Obligations.Conservation", true),
    ("-- import Obligations would be rejected", false),
    ("import LeanTex.Core.Ir", false)]

  expect "walkEntry" (fun l => (walkEntry l).isSome) [
    -- the shapes the tree carries today: entries in, companions and
    -- non-walks out
    ("def dimBlocks (cover : Cover) (k : Nat) (xs : Array Block) : Array Block :=", true),
    ("def unwrapItemSteps (xs : Array Block) : Array Block :=", true),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", true),
    ("def substPage (n total : Nat) (xs : Array Inline) : Array Inline :=", true),
    ("def fillTemplate (template content : Array Inline) : Array Inline :=", true),
    -- a body on the definition line does not evade the scan
    ("def sneakyWalk (xs : Array Block) : Array Block := xs", true),
    -- a List companion is scaffolding, not the public entry
    ("def unwrapItemStepList (out : Array Block) : List Block → Array Block", false),
    -- a rendering makes its output from another type: not IR-to-IR
    ("def bandInlines (b : Array BandSlot) : Array Inline :=", false),
    -- a census returns a summary, not the IR
    ("def blocksText (xs : Array Block) : String := blockTextList \"\" xs.toList", false),
    ("private def raggedItems (items : Array Item) : Array Item :=", false),
    ("  -- def fake (xs : Array Block) : Array Block, quoted in a comment", false)]

  expect "conservesNone" conservesNone [
    ("-- conserves: none — fills a hole; the output census is a mix", true),
    ("  -- conserves: none — the walk edits only image alt text", true),
    ("-- conserves everything", false),
    ("def keepFor (t : String) (xs : Array Block) : Array Block :=", false)]

  expect "repoRefInString" repoRefInString [
    -- the shapes that shipped in real output (the diag-voice defects)
    ("      (help := \"the rest of M6; see PLAN.md\")", true),
    ("      (help := \"there is no Lua here; see PLAN.md for the native declarations\")", true),
    ("            (help := s!\"planned for {milestone}; see PLAN.md\" ++", true),
    ("  say .W0104 \"planned for M8\" pos", true),
    ("  let msg := \"stated in AGENTS.md\"", true),
    ("  fail s!\"see LeanTex/Core/Diag.lean\"", true),
    -- legal spellings: code tokens, comments, docstrings, honest text
    ("  -- planned for M8, tracked in PLAN.md", false),
    ("/-- the registry row's why lives in PLAN.md -/", false),
    ("  let milestone := reservedCtrl.lookup name", false),
    ("      (help := \"\\\\allow{E0333} accepts the loss\")", false),
    ("    \"'{tikzpicture}' is not implemented yet; its content is not rendered\"", false),
    ("  say .W0104 \"a 10mm margin\" pos", false),
    ("  let m8 := M8.compute x", false)]

  expect "severityAssign" severityAssign [
    -- the free-severity spellings the DiagCode gate closed over
    ("    severity := .error", true),
    ("  { d with severity := .warning }", true),
    ("  let d : Diag := { severity := sev, code := code, message := msg }", true),
    -- mentions in comments and strings, and reads of the field, stay legal
    ("  -- severity := comes only from Diag.of, never a call site", false),
    ("  say s!\"a string naming severity := x\"", false),
    ("  let sev := d.severity", false),
    ("    severity := c.loss.severity", true)]

  expect "undeclaredConfigRead" undeclaredConfigRead [
    -- the leak shape: a new Config field threaded from the driver toward a
    -- backend starts as exactly this token
    ("          mathRenderer := ui.cfg.mathRenderer", true),
    ("        let hcfg := { css := ui.cfg.cssMode, imgs }", true),
    ("  if cfg.newFlag then", true),
    -- the declared reads of today's driver
    ("      let emit := ui.cfg.effectiveEmit doc.output.formats", false),
    ("          mathBoundary := ui.cfg.mathBoundary", false),
    ("  if ui.cfg.porcelain then", false),
    ("    let allowAll := ui.cfg.bestEffort", false),
    ("  let faces ← FontDb.scan (cfg.fontDirs.toList ++ (← texFontDirs))", false),
    -- comments, strings, and non-Config names stay legal
    ("  -- ui.cfg.frobnicate would be rejected here", false),
    ("  say s!\"a message naming cfg.frobnicate\"", false),
    ("  let x := hcfg.mathBoundary", false),
    ("  cfg : Config", false)]

  let failed := (← fails.get).reverse
  if failed.isEmpty then
    IO.println "precommit selftest: all passed"
    return 0
  for f in failed do
    IO.eprintln s!"FAIL {f}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then
    return (← selftest)
  let staged := ((← git #["diff", "--cached", "--name-only"]).splitOn "\n").filter (!·.isEmpty)
  if staged.isEmpty then
    return 0

  let failed ← IO.mkRef false
  let say (msg : String) : IO Unit := do
    IO.eprintln msg
    failed.set true

  -- Checked in every staged file whatever its extension — the two markers
  -- that once landed were in PLAN.md prose — and before the relevance
  -- gate, which would otherwise skip a prose-only commit.
  let fullDiff ← git #["diff", "--cached", "--no-color", "--unified=0"]
  let bad := conflictMarkers fullDiff
  if !bad.isEmpty then
    let hits := String.intercalate "\n" (bad.toList.map fun (f, n, l) => s!"  {f}:{n}: {l}")
    say s!"pre-commit: merge-conflict marker in staged content:
{hits}
  Fix: resolve the conflict -- keep the side you mean, delete the marker
  lines -- then re-stage the file."

  if !staged.any relevant then
    return (if ← failed.get then 1 else 0)

  if staged.contains "lean-toolchain" && staged.any (· != "lean-toolchain") then
    say "pre-commit: lean-toolchain changed together with other files.
  Toolchain bumps are deliberate and go in their own commit (AGENTS.md, Don't touch).
  Fix: git restore --staged lean-toolchain, commit the rest, then commit the bump alone."

  if staged.any (·.startsWith "tests/golden/") then
    -- A golden may not be hand-edited, which is why it must travel with the
    -- change that moved it. On a branch that already carries such a change,
    -- a later regeneration is legitimate on its own: two slices landing in
    -- the same fixture only agree after the second one rebases, and the
    -- harness output is what lands either way. So the source change is
    -- looked for across the branch, not only in this commit.
    let branchTouched ← do
      let base := ((← git #["merge-base", "HEAD", "main"]).splitOn "\n").head?
      match base with
      | some b =>
        let b := b.trimAscii.toString
        if b.isEmpty then pure #[] else
          pure (((← git #["diff", "--name-only", b ++ "..HEAD"]).splitOn "\n").filter
            (!·.isEmpty)).toArray
      | none => pure #[]
    let isSource (f : String) : Bool :=
      f.endsWith ".lean" || (f.startsWith "tests/corpus/" && f.endsWith ".tex")
    if !staged.any isSource && !branchTouched.any isSource then
      say "pre-commit: tests/golden/** changed without a .lean or tests/corpus/*.tex change.
  Goldens are regenerated through the harness, never hand-edited (AGENTS.md, Don't touch).
  Fix: revert the golden files, or regenerate with: lake exe Tests --update"

  let diff ← git #["diff", "--cached", "--no-color", "--unified=0", "--", "*.lean"]
  for (file, lns) in addedByFile diff do
    for g in gates do
      if g.applies file then
        let bad := lns.filter g.flag
        if !bad.isEmpty then
          say s!"pre-commit: {g.what file}:
{String.intercalate "\n" bad.toList}
{g.help}"


  -- Warn-once keys are namespaced: a flat key space let an environment and a
  -- command of one name silence each other once (W0301/W0302), and a growing
  -- catch-all table re-creates the collision quietly. The check is
  -- structural about the call site, not about one literal spelling: every
  -- warn-once call in core code must spell its namespace where it stands —
  -- a string literal containing ':', alone or opening a concatenation. A
  -- key the line cannot prove namespaced (`sayOnce name`, a variable, an
  -- interpolation, a call split across lines) is rejected outright.
  let addedInCore : List String := Id.run do
    let mut file := ""
    let mut out : List String := []
    for l in diff.splitOn "\n" do
      if l.startsWith "+++ b/" then
        file := (l.drop "+++ b/".length).toString
      else if l.startsWith "+" && !l.startsWith "+++" && file.startsWith "LeanTex/" then
        out := (l.drop 1).toString :: out
    return out.reverse
  let patSay := "say" ++ "Once "
  let patWarn := "warn" ++ "Once "
  let keyNamespaced (rest : String) : Bool :=
    let r := rest.trimAscii.toString
    let r := if r.startsWith "(" then ((r.drop 1).toString.trimAscii.toString) else r
    r.startsWith "\"" && containsSub ((((r.drop 1).toString.splitOn "\"").headD "")) ":"
  let onceCallFlat (l : String) : Bool := Id.run do
    if containsSub l ("def say" ++ "Once") || containsSub l ("def warn" ++ "Once") then
      return false
    for pat in [patSay, patWarn] do
      for rest in (l.splitOn pat).drop 1 do
        -- warnOnce takes the context first; the key follows it
        let rest := if pat == patWarn then
            match rest.splitOn " " with
            | _ :: rs => String.intercalate " " rs
            | [] => rest
          else rest
        if !keyNamespaced rest then
          return true
    return false
  let bad := addedInCore.filter onceCallFlat
  if !bad.isEmpty then
    say s!"pre-commit: warn-once call whose key is not visibly namespaced at the call site:
{String.intercalate "\n" bad}
  Keys share one flat store per module; spell the namespace where the call is —
  a literal (\"ctrl:x\") or a concatenation opening with one ((\"env:\" ++ name)) —
  so two constructs of one name cannot silence each other, and this check can see it."

  -- The claim and its evidence arrive together: a nativePackages entry
  -- without its tests/compat-index file used to surface an hour later at
  -- lake test (the paper-bib escape); the hook refuses it at commit time.
  -- Whole tree, like the conservation gate: the entry and the file may
  -- land in different hunks.
  if (← System.FilePath.pathExists "LeanTex/Core/Compat.lean") then
    let compatSrc ← IO.FS.readFile "LeanTex/Core/Compat.lean"
    for pkg in nativePackagesOf compatSrc do
      unless (← System.FilePath.pathExists s!"tests/compat-index/{pkg}.txt") do
        say s!"pre-commit: '{pkg}' is in nativePackages with no tests/compat-index/{pkg}.txt.
  A nativePackages entry arrives with its index file: the package's
  documented command list, one row per command, the manual section named
  in its header (AGENTS.md, obligation table); lake test probes every row.
  Fix: write tests/compat-index/{pkg}.txt before adding the entry."

  -- The conservation gate — the obligation table's walk row, mechanical:
  -- every public IR-to-IR walk in core (a def taking and returning
  -- Array Block / Array Inline) ships its census statement, named by a
  -- registered shape suffix (`_text` / `_covers` / `_id`, the Conserves
  -- instances and census equalities), or writes
  -- `-- conserves: none — <why>` beside the def. Whole tree, not the
  -- diff: the walk and its theorem may land in different hunks, and the
  -- next walk must not ship without one.
  let mut coreFiles : Array String := #[]
  for f in (← System.FilePath.walkDir "LeanTex") do
    if f.toString.endsWith ".lean" then coreFiles := coreFiles.push f.toString
  let mut allCore := ""
  let mut coreTexts : Array (String × Array String) := #[]
  let mut walkSites : Array (String × Nat × String × Array String) := #[]
  for f in coreFiles do
    let txt ← IO.FS.readFile f
    allCore := allCore ++ txt
    let lines := (txt.splitOn "\n").toArray
    coreTexts := coreTexts.push (f, lines)
    for i in [0:lines.size] do
      if let some name := walkEntry lines[i]! then
        walkSites := walkSites.push (f, i, name, lines)
  for (f, i, name, lines) in walkSites do
    let hasThm := conservesSuffixes.any fun suf =>
      containsSub allCore s!"theorem {name}{suf}"
    let escaped := (List.range 13).any fun d =>
      i ≥ d && conservesNone (lines[i - d]?.getD "")
    unless hasThm || escaped do
      say s!"pre-commit: the IR walk `{name}` ({f}:{i + 1}) has no conservation statement.
  A public Block/Inline walk owes its census fact (AGENTS.md, obligation
  table): a theorem named `{name}_text` (census equality — state it as a
  `Conserves` instance), `{name}_covers`, or `{name}_id` — or, when the
  walk genuinely conserves nothing, the one-line refusal
  `-- conserves: none — <why>` beside the def."

  -- The arm gate (handed by impl-shapes), whole tree over LeanTex/Core:
  -- a pass-through catch-all in a def whose one-line signature takes IR is
  -- the next constructor silently falling through. The frozen holes are
  -- allowlisted by def name; shrink the list as they close.
  let armAllow : List String :=
    ["imageSrcsInline", "setAltInline", "setAltBlock", "flattenLeadStep"]
  for (f, lines) in coreTexts do
    if f.startsWith "LeanTex/Core/" then
      let mut cur := ""
      let mut curWalk := false
      for i in [0:lines.size] do
        let l := lines[i]!
        let t := stripLineComment l
        if t.startsWith "def " || t.startsWith "private def " then
          let rest := (if t.startsWith "private def " then t.drop 12 else t.drop 4).toString
          cur := (rest.takeWhile (fun c => isWordChar c || c == '.')).toString
          curWalk := hasWord t "Inline" || hasWord t "Block"
        if curWalk && wildcardThrough l && !armAllow.contains cur then
          say s!"pre-commit: wildcard arm in the IR walk `{cur}` ({f}:{i + 1}):
  {l.trimAscii}
  Spell every constructor, or the next Ir constructor silently falls
  through (AGENTS.md, obligation table: an Ir constructor owes an explicit
  arm in every walk); the allowlisted frozen sites live in precommit.lean."

  -- The ]! ratchet (handed by impl-shapes), whole tree: per-file counts
  -- against the frozen baseline — a commit may lower a count, never raise
  -- it. ]! aborts the process; COMMON bans adding it to reach green.
  for (f, lines) in coreTexts do
    let n := bangCount lines
    let base := ((bangBaseline.find? (·.1 == f)).map (·.2)).getD 0
    if n > base then
      say s!"pre-commit: new ]! index in {f}: {n} sites, baseline {base}.
  ]! aborts the whole run on a miss — one font in a TeX Live tree once took
  the run down with it.
  Fix: use `for h :` bounds, getD, or a proof-carrying index; the per-file
  count may only fall (lower its bangBaseline row in scripts/precommit.lean
  when you remove sites)."

  -- The owed-theorem ratchet: a commit that touches the staging area or
  -- PLAN.md must leave the debt recorded — one hole per owed record, every
  -- record registered in PLAN, no import of Obligations from the gated
  -- library. The check reads the whole tree, not the diff, so the count
  -- cannot drift through an edit the diff scanner does not see.
  let mut env : Array (String × Option String) := #[]
  let clang := "/home/linuxbrew/.linuxbrew/bin/clang"
  if (← IO.getEnv "LEAN_CC").isNone && (← System.FilePath.pathExists clang) then
    let prefixOut ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
    let pre := prefixOut.stdout.trimAscii.toString
    env := #[("LEAN_CC", some clang), ("LIBRARY_PATH", some s!"{pre}/lib:{pre}/lib/lean")]

  if staged.any (fun f => obligationsFile f || f == "PLAN.md") then
    let owedBuild ← IO.Process.output
      { cmd := "lake", args := #["build", "owed", "-q"], env }
    let owed ← if owedBuild.exitCode == 0 then
        IO.Process.output { cmd := ".lake/build/bin/owed", args := #["--check"] }
      else pure owedBuild
    if owed.exitCode != 0 then
      say s!"pre-commit: the owed-theorem ratchet failed:
{owed.stderr}  Fix: register the obligation in PLAN.md ('Owed obligations'), or finish
  its proof and move it to its owner module (see scripts/owed.lean)."

  if ← failed.get then
    return 1

  let build ← IO.Process.output
    { cmd := "lake", args := #["build", "--wfail", "-q", "leantex", "precommit", "owed"], env }
  if build.exitCode != 0 then
    IO.eprintln "pre-commit: lake build --wfail failed (linter warnings fail too):"
    IO.eprint build.stdout
    IO.eprint build.stderr
    return 1

  -- Staged obligations must still type-check: the staging target builds
  -- without --wfail, so its expected open-proof warnings pass while a
  -- statement that does not compile still fails the commit. A statement
  -- that does not compile is worse than no statement.
  if staged.any obligationsFile then
    let ob ← IO.Process.output { cmd := "lake", args := #["build", "Obligations", "-q"], env }
    if ob.exitCode != 0 then
      IO.eprintln "pre-commit: lake build Obligations failed (staged statements must type-check):"
      IO.eprint ob.stdout
      IO.eprint ob.stderr
      return 1

  return 0
