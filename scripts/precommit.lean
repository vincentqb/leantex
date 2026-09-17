/-
Pre-commit gate: compile+lint via lake build --wfail, plus convention checks
over the staged diff. Silent on success. Git executes the FILE
scripts/hooks/pre-commit, a 3-line sh trampoline that runs this after a cheap
staged-file filter; install with: git config core.hooksPath scripts/hooks
-/

def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  if out.exitCode != 0 then
    IO.eprintln s!"pre-commit: git {String.intercalate " " args.toList} failed:\n{out.stderr}"
    IO.Process.exit 1
  return out.stdout

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Does `line` contain `word` delimited by non-word characters — the
`(^|[^[:alnum:]_])word([^[:alnum:]_]|$)` grep the shell hook used. -/
def hasWord (line word : String) : Bool :=
  (line.split (fun c => !isWordChar c)).any (·.toString == word)

def containsSub (line pat : String) : Bool :=
  (line.splitOn pat).length > 1

/-- The line with its string-literal content removed: a banned keyword is a
code token, and a string mentioning one — the math tables' command-name
entry for TeX's derivative symbol was the escape — is data, not a
declaration. Escapes are honoured. Two stated line-scanner limitations,
like `ioInCore`'s: a literal left open by a multi-line string strips to the
line's end, and a char literal holding a double quote reads as opening one. -/
def stripStrings (l : String) : String := Id.run do
  let mut out := ""
  let mut inStr := false
  let mut esc := false
  for c in l.toList do
    if inStr then
      if esc then esc := false
      else if c == '\\' then esc := true
      else if c == '"' then inStr := false
    else if c == '"' then
      inStr := true
    else
      out := out.push c
  return out

/-- A banned keyword as a code token: word-delimited, string content aside. -/
def bannedWord (kw l : String) : Bool :=
  hasWord (stripStrings l) kw

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
def kwSorry : String := "sor" ++ "ry"
def kwUnsafe : String := "uns" ++ "afe"

/-- Composed for the same reason: prepending to a recursive call's result
copies that result at every element. -/
def patAppend : String := "+" ++ "+"

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

/-- The line with any `--` comment stripped: a line comment, or a doc/block
comment's opening line. Blind spots, accepted rather than parsed around
(a line scanner has no comment state): a continuation line inside a block
comment still looks like code, and a string literal containing `--`
truncates the code after it. -/
def stripLineComment (l : String) : String :=
  (l.splitOn "--").headD l

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

/-- An import of the owed-theorem staging area: legal only inside it. The
gated library must never depend on a statement whose proof is open. -/
def importsObligations (l : String) : Bool :=
  ((stripLineComment l).trimAscii.toString).startsWith "import Obligations"

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

  expect "bannedWord" (bannedWord kwPartial) [
    -- a declaration must still fire, wherever it stands on the line
    ("+" ++ kwPartial ++ " def foo : Nat := 0", true),
    ("+  " ++ kwPartial ++ " def go (l : List Nat) : Nat := go l", true),
    -- the escape that prompted the stripper: a command-name table entry
    ("+   (\"" ++ kwPartial ++ "\", .ord, '𝜕'),", false),
    ("+    say s!\"a message naming " ++ kwPartial ++ " in prose\"", false),
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
  if !staged.any relevant then
    return 0

  let failed ← IO.mkRef false
  let say (msg : String) : IO Unit := do
    IO.eprintln msg
    failed.set true

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
  let added := (diff.splitOn "\n").filter fun l =>
    l.startsWith "+" && !l.startsWith "+++"

  let partialAllowed (l : String) : Bool :=
    containsSub l s!"{kwPartial} def takeArgs" || containsSub l s!"{kwPartial} def elabInlines"
      || containsSub l s!"{kwPartial} def elabBlocks"
  let bad := added.filter fun l => bannedWord kwPartial l && !partialAllowed l
  if !bad.isEmpty then
    say s!"pre-commit: new '{kwPartial}' in staged .lean changes:
{String.intercalate "\n" bad}
  Only Elab.takeArgs/elabInlines/elabBlocks may be {kwPartial} (tracked in PLAN.md).
  Fix: make the recursion structural (see AGENTS.md, Conventions)."

  let bad := ((addedByFile diff).filter (fun p => !obligationsFile p.1)).flatMap (·.2)
    |>.filter (bannedWord kwSorry)
  if !bad.isEmpty then
    say s!"pre-commit: '{kwSorry}' in staged .lean changes outside Obligations/:
{String.intercalate "\n" bad.toList}
  Fix: finish the proof -- a broken theorem is a broken build -- or, for a
  statement the engine does not yet earn, stage it as a recorded obligation
  under Obligations/ (see scripts/owed.lean; the ratchet applies)."

  let bad := added.filter (bannedWord kwUnsafe)
  if !bad.isEmpty then
    say s!"pre-commit: '{kwUnsafe}' in staged .lean changes:
{String.intercalate "\n" bad}
  Fix: stay in the safe fragment; {kwUnsafe} code voids the certification story."

  let bad := added.filter quadraticPrepend
  if !bad.isEmpty then
    say s!"pre-commit: '{patAppend} walk rest' (prepend to a recursive call's result) in staged .lean changes:
{String.intercalate "\n" bad}
  Prepending to a recursive call's result copies it at every element -- it
  turned a 4 ms pass into 1157 ms, three times in one day (PLAN 2026-09-16).
  Fix: thread an Array accumulator through the walk (see Compat.rewriteList);
  a one-off prepend outside a recursion can bind the call to a name first."

  let bad := added.filter ctorDefault
  if !bad.isEmpty then
    say s!"pre-commit: inductive constructor field with a default value:
{String.intercalate "\n" bad}
  Defaults on constructor fields let patterns under-specify silently: `.run
  a b c` once matched only the default, with the whole suite green (PLAN
  2026-09-15).
  Fix: spell the field at every constructor site; defaults belong on structures."

  for (file, lines) in addedByFile diff do
    if !obligationsFile file then
      let bad := lines.filter importsObligations
      if !bad.isEmpty then
        say s!"pre-commit: import of Obligations outside the staging area, in {file}:
{String.intercalate "\n" bad.toList}
  Obligations is the owed-theorem staging area: statements with open proofs.
  The gated library must never depend on it (scripts/owed.lean also checks
  the whole tree).
  Fix: prove the statement and move it into its owner module first."
    if file.endsWith ".lean" && file != "LeanTex/Core/Diag.lean" then
      let bad := lines.filter severityAssign
      if !bad.isEmpty then
        say s!"pre-commit: a severity written outside Diag.lean, in {file}:
{String.intercalate "\n" bad.toList}
  Severity is a function of the code's declared Loss — a free severity is how
  \"content silently gone\" shipped as a warning fourteen times (PLAN, the
  severity policy).
  Fix: emit through Diag.of with a DiagCode; if the code's loss category is
  wrong, change it in DiagCode.spec."
    if file.startsWith "LeanTex/" || file == "Main.lean" then
      let bad := lines.filter repoRefInString
      if !bad.isEmpty then
        say s!"pre-commit: a repo-internal reference in a string the user can see, in {file}:
{String.intercalate "\n" bad.toList}
  A diagnostic is read by someone holding only their own document: PLAN.md,
  AGENTS.md, a LeanTex/ path, and milestone names (M6, M8) mean nothing
  there — 'see PLAN.md' shipped in real output (the diag-voice defect).
  Fix: say what happens and what to write instead; the voice lint in
  Tests.lean judges the registered text."
    if file.startsWith "LeanTex/Core/" && file != "LeanTex/Core/FontDb.lean" then
      let bad := lines.filter ioInCore
      if !bad.isEmpty then
        say s!"pre-commit: IO in {file}:
{String.intercalate "\n" bad.toList}
  Modules under LeanTex/Core/ do no IO (FontDb is the one exception): files
  and fonts surface as request values the CLI driver fulfills.
  Fix: return a request value and fulfill it in Main.lean."
    if file.startsWith "LeanTex/Core/" then
      let bad := lines.filter identityArm
      if !bad.isEmpty then
        say s!"pre-commit: identity catch-all arm (`| x => x`) in {file}:
{String.intercalate "\n" bad.toList}
  A rewrite walk with a wildcard ships a new IR constructor through
  untouched -- the shape of the covered-content defect (PLAN 2026-09-17).
  Fix: spell every constructor; the compiler then makes the next
  constructor a build error at every walk (AGENTS.md, obligation table)."
    if file == "LeanTex/Core/Ir.lean" then
      let bad := lines.filter wildcardNumeral
      if !bad.isEmpty then
        say s!"pre-commit: wildcard arm answering a numeral (`| _ => 1`) in {file}:
{String.intercalate "\n" bad.toList}
  A measure walk with a numeric default silently miscounts a new IR
  constructor -- a step inside a section title got no handout page this
  way (PLAN 2026-09-17).
  Fix: spell every constructor and say what each one measures."
    if backendFiles.contains file then
      let bad := lines.filter surfaceReach
      if !bad.isEmpty then
        say s!"pre-commit: a backend reaches into the surface, in {file}:
{String.intercalate "\n" bad.toList}
  Backends consume the IR and nothing else; a backend that re-parses is how
  md→PDF and tex→HTML decay into N×M special cases (AGENTS.md, Conventions).
  Fix: put what the backend needs on the IR."
      let bad := lines.filter dimLiteral
      if !bad.isEmpty then
        say s!"pre-commit: bare dimension literal in {file}:
{String.intercalate "\n" bad.toList}
  A design value in a backend is a token, or carries its source where it
  stands (AGENTS.md, obligation table): a loose `pt 14` is how a heading
  scale drifts from the type scale, invisibly.
  Fix: read a token/style/palette entry, or put the source in a `--`
  comment on the same line (the diff scanner cannot see the line above)."

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

  -- The owed-theorem ratchet: a commit that touches the staging area or
  -- PLAN.md must leave the debt recorded — one hole per owed record, every
  -- record registered in PLAN, no import of Obligations from the gated
  -- library. The check reads the whole tree, not the diff, so the count
  -- cannot drift through an edit the diff scanner does not see.
  if staged.any (fun f => obligationsFile f || f == "PLAN.md") then
    let owed ← IO.Process.output
      { cmd := "lean", args := #["--run", "scripts/owed.lean", "--check"] }
    if owed.exitCode != 0 then
      say s!"pre-commit: the owed-theorem ratchet failed:
{owed.stderr}  Fix: register the obligation in PLAN.md ('Owed obligations'), or finish
  its proof and move it to its owner module (see scripts/owed.lean)."

  if ← failed.get then
    return 1

  let mut env : Array (String × Option String) := #[]
  let clang := "/home/linuxbrew/.linuxbrew/bin/clang"
  if (← IO.getEnv "LEAN_CC").isNone && (← System.FilePath.pathExists clang) then
    let prefixOut ← IO.Process.output { cmd := "lean", args := #["--print-prefix"] }
    let pre := prefixOut.stdout.trimAscii.toString
    env := #[("LEAN_CC", some clang), ("LIBRARY_PATH", some s!"{pre}/lib:{pre}/lib/lean")]

  let build ← IO.Process.output { cmd := "lake", args := #["build", "--wfail", "-q"], env }
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
