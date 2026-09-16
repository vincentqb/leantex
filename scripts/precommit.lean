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

def relevant (f : String) : Bool :=
  f.endsWith ".lean" || f == "lakefile.toml" || f == "lakefile.lean"
    || f == "lean-toolchain" || f.startsWith "tests/golden/"

/-- The banned words, composed so this file's own staged diff never contains
them as word-delimited tokens — the gate scans every .lean file, itself
included. -/
def kwPartial : String := "par" ++ "tial"
def kwSorry : String := "sor" ++ "ry"
def kwUnsafe : String := "uns" ++ "afe"

def main : IO UInt32 := do
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
    if !staged.any (fun f => f.endsWith ".lean"
        || (f.startsWith "tests/corpus/" && f.endsWith ".tex")) then
      say "pre-commit: tests/golden/** changed without a .lean or tests/corpus/*.tex change.
  Goldens are regenerated through the harness, never hand-edited (AGENTS.md, Don't touch).
  Fix: revert the golden files, or regenerate with: lake exe Tests --update"

  let diff ← git #["diff", "--cached", "--no-color", "--unified=0", "--", "*.lean"]
  let added := (diff.splitOn "\n").filter fun l =>
    l.startsWith "+" && !l.startsWith "+++"

  let partialAllowed (l : String) : Bool :=
    containsSub l s!"{kwPartial} def takeArgs" || containsSub l s!"{kwPartial} def elabInlines"
      || containsSub l s!"{kwPartial} def elabBlocks"
  let bad := added.filter fun l => hasWord l kwPartial && !partialAllowed l
  if !bad.isEmpty then
    say s!"pre-commit: new '{kwPartial}' in staged .lean changes:
{String.intercalate "\n" bad}
  Only Elab.takeArgs/elabInlines/elabBlocks may be {kwPartial} (tracked in PLAN.md).
  Fix: make the recursion structural (see AGENTS.md, Conventions)."

  let bad := added.filter (hasWord · kwSorry)
  if !bad.isEmpty then
    say s!"pre-commit: '{kwSorry}' in staged .lean changes:
{String.intercalate "\n" bad}
  Fix: finish the proof; a broken theorem is a broken build."

  let bad := added.filter (hasWord · kwUnsafe)
  if !bad.isEmpty then
    say s!"pre-commit: '{kwUnsafe}' in staged .lean changes:
{String.intercalate "\n" bad}
  Fix: stay in the safe fragment; {kwUnsafe} code voids the certification story."

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

  return 0
