module

public import LeanTex.Cli.World
public import LeanTex.Core.CodeDoc

/-! Where a Lean file stands in its repository, for the links a page gives its declarations' names,
git asked only for the parts a link's template names. -/

namespace LeanTex.Cli.LeanLinks

open LeanTex.Core LeanTex.Cli.World

/-- How long git may take over one question, and how long it has to stop. -/
public def gitBudgetMs : Nat := 10000
public def gitGraceMs : Nat := 2000

/-- The environment variables that point git at a repository other than the one its working
directory holds, which a question about a file's repository unsets. -/
public def gitRepoVars : Array String := #[
  "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_CONFIG", "GIT_CONFIG_PARAMETERS",
  "GIT_CONFIG_COUNT", "GIT_OBJECT_DIRECTORY", "GIT_DIR", "GIT_WORK_TREE",
  "GIT_IMPLICIT_WORK_TREE", "GIT_GRAFT_FILE", "GIT_INDEX_FILE", "GIT_NO_REPLACE_OBJECTS",
  "GIT_REPLACE_REF_BASE", "GIT_PREFIX", "GIT_SHALLOW_FILE", "GIT_COMMON_DIR", "GIT_NAMESPACE"]

/-- The run that asks git one question about a file's repository, from the file's directory, with
no repository the caller's environment names. -/
public def gitAt (dir : String) (args : Array String) (exe : String) : ToolCall :=
  { tool := exe, args, budgetMs := gitBudgetMs, graceMs := gitGraceMs, captureLimit := 65536
    cwd := some dir, env := gitRepoVars.map (·, none) }

/-- Where a file stands in its repository, git asked only for the parts a link's template names:
the commit `HEAD` names, whether that commit holds the file, the file's path there, and whether
the file differs from it, none of these where git could not say. -/
public def placeOf (file template : String) : Prog Code.LinkPlace := do
  let names (part : String) : Bool := (template.splitOn part).length > 1
  let joined := match ← ask .cwd with
    | .ok d => if file.startsWith "/" then file else ToolPath.join d file
    | .error _ => file
  let parts := joined.splitOn "/"
  let dir := "/".intercalate parts.dropLast
  let base := parts.getLastD file
  let said (args : Array String) : Prog (Option String) := do
    match ← ToolPath.probe "git" (gitAt (if dir.isEmpty then "/" else dir) args) with
    | some (_, e) => pure (if e.ran == .exited 0 then some e.out else none)
    | none => pure none
  unless names "{commit}" || names "{path}" do return {}
  let held ← said #["ls-tree", "-z", "--full-name", "--name-only", "HEAD", "--", base]
  let path := (held.map fun o => (o.splitOn "\x00").headD "").filter (!·.isEmpty)
  let commit ← if names "{commit}" then
      (·.map (·.trimAscii.toString)) <$> said #["rev-parse", "--verify", "HEAD"] else pure none
  let dirty ← if names "{commit}" then
      (·.map fun o => !o.trimAscii.toString.isEmpty) <$> said #["status", "--porcelain", "--", base]
    else pure none
  return { commit, path := if names "{path}" then path else none, dirty, tracked := path.isSome }

end LeanTex.Cli.LeanLinks
