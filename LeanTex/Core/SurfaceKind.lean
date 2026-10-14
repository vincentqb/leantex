module

/-! The surfaces a document can be written in, and the input names that select them. -/

namespace LeanTex.Core.Ir

/-- A programming language whose source files read as documents. -/
public inductive CodeLang where
  | lean
  | python
  | bash
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The surface a document or an included file is written in. -/
public inductive Surface where
  | tex
  | markdown
  | code (lang : CodeLang)
  deriving Repr, BEq, DecidableEq, Inhabited

public def CodeLang.all : List CodeLang := [.lean, .python, .bash]

/-- The file extension a language's sources carry. -/
public def CodeLang.extension : CodeLang → String
  | .lean => "lean"
  | .python => "py"
  | .bash => "sh"

/-- The listing language a code file's code sets in. -/
public def CodeLang.listing : CodeLang → String
  | .lean => "lean4"
  | .python => "python"
  | .bash => "bash"

/-- The surface an input name's extension selects, `none` where no surface reads it. -/
public def Surface.ofInput? (file : String) : Option Surface :=
  if file.endsWith ".tex" then some .tex
  else if file.endsWith ".md" then some .markdown
  else (CodeLang.all.find? fun l => file.endsWith ("." ++ l.extension)).map .code

/-- The extensions an input name may end in, as a refusal lists them. -/
public def Surface.inputExtensions : List String :=
  ["tex", "md"] ++ CodeLang.all.map (·.extension)

/-- `.md` reads as markdown, a code language's extension as that code, everything else as tex. -/
public def Surface.ofPath (file : String) : Surface :=
  match Surface.ofInput? file with
  | some .markdown => .markdown
  | some (.code l) => .code l
  | some .tex | none => .tex

public theorem Surface.ofInput_extension_exact (s : Surface) (file : String)
    (h : Surface.ofInput? file = some s) : Surface.ofPath file = s := by
  unfold Surface.ofPath
  rw [h]
  cases s <;> rfl

end LeanTex.Core.Ir
