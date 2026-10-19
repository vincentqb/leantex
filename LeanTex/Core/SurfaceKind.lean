module

/-! The surfaces a document can be written in, the code languages whose sources read as documents,
and the input names that select them. -/

namespace LeanTex.Core.Ir

/-- A programming language whose source files read as documents. -/
public inductive CodeLang where
  | lean
  | python
  | bash
  | c
  | cpp
  | rust
  | java
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Inhabited

/-- How a documentation comment's text is marked up. -/
public inductive DocMarkup where
  /-- CommonMark, as doc-gen4 reads it. -/
  | markdown
  /-- rustdoc's: CommonMark, a code block Rust unless it names a language, its `#` lines hidden, an
  item's path a link. -/
  | rustdoc
  /-- A Python docstring: markdown, its doctests set as code. -/
  | docstring
  /-- Javadoc: HTML with inline `{@…}` tags and `@…` block tags. -/
  | javadoc
  /-- Javadoc's markdown comments: CommonMark with its inline and block tags. -/
  | javadocMarkdown
  /-- Doxygen: markdown with its `\…` and `@…` special commands. -/
  | doxygen
  deriving Repr, BEq, DecidableEq, Inhabited

/-- What a documentation comment documents. -/
public inductive DocScope where
  /-- The declaration after it. -/
  | next
  /-- What holds it, the file where it stands at the file's head. -/
  | holder
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A documentation comment's spelling. -/
public inductive DocForm where
  /-- Lines each opening with `marker`, a run of them one comment. -/
  | lines (marker : String) (scope : DocScope) (markup : DocMarkup)
  /-- A block from `opener` to the first `closer` after it. -/
  | block (opener closer : String) (scope : DocScope) (markup : DocMarkup)
  deriving Repr, BEq, Inhabited

/-- What opens a form's comment. -/
public def DocForm.opener : DocForm → String
  | .lines m _ _ => m
  | .block o _ _ _ => o

/-- How a form's text is marked up. -/
public def DocForm.markup : DocForm → DocMarkup
  | .lines _ _ m => m
  | .block _ _ _ m => m

/-- Where a language's documentation comments are found. -/
public inductive DocSource where
  /-- Lean's `/-- -/` and `/-! -/`, by Lean's own comment grammar. -/
  | lean
  /-- Python's docstrings, by Python's grammar. -/
  | python
  /-- The file's leading block of comments opening with `marker`, after its `#!` line. -/
  | leading (marker : String)
  /-- The comments the language's lexer reads that open with one of `forms`, each the first thing
  on its line. -/
  | comments (forms : List DocForm)
  deriving Repr, BEq, Inhabited

/-- What a language's source files read by: the extensions selecting it, the listing language its
code sets in, the line comment its directive is written in, where its documentation stands, and the
files marking its project's root, whose `docs/references.bib` its documentation cites into. -/
public structure LangRow where
  extensions : List String
  listing : String
  lineComment : String
  docs : DocSource
  project : List String
  deriving Repr, Inhabited

/-- Rustdoc's outer and inner comments, line and block. -/
private def rustDocs : List DocForm :=
  [.lines "///" .next .rustdoc, .lines "//!" .holder .rustdoc,
   .block "/**" "*/" .next .rustdoc, .block "/*!" "*/" .holder .rustdoc]

/-- Doxygen's JavaDoc, Qt and C++ comment styles. -/
private def doxygenDocs : List DocForm :=
  [.lines "///" .next .doxygen, .lines "//!" .next .doxygen,
   .block "/**" "*/" .next .doxygen, .block "/*!" "*/" .next .doxygen]

/-- The files marking a C or C++ project's root, by its build system. -/
private def cProject : List String := ["CMakeLists.txt", "meson.build", "configure.ac", "Makefile"]

/-- Each language's row. -/
public def CodeLang.row : CodeLang → LangRow
  | .lean => ⟨["lean"], "lean4", "--", .lean, ["lakefile.lean", "lakefile.toml"]⟩
  | .python => ⟨["py"], "python", "#", .python, ["pyproject.toml", "setup.py", "setup.cfg"]⟩
  | .bash => ⟨["sh"], "bash", "#", .leading "#", []⟩
  | .c => ⟨["c", "h"], "c", "//", .comments doxygenDocs, cProject⟩
  | .cpp => ⟨["cpp", "cc", "cxx", "c++", "hpp", "hh", "hxx", "h++"], "cpp", "//",
      .comments doxygenDocs, cProject⟩
  | .rust => ⟨["rs"], "rust", "//", .comments rustDocs, ["Cargo.toml"]⟩
  | .java => ⟨["java"], "java", "//", .comments [.block "/**" "*/" .next .javadoc,
      .lines "///" .next .javadocMarkdown], ["pom.xml", "build.gradle", "build.gradle.kts"]⟩

public def CodeLang.all : List CodeLang := [.lean, .python, .bash, .c, .cpp, .rust, .java]

/-- Every language is listed, so its extensions select it. -/
public theorem CodeLang.all_complete (l : CodeLang) : l ∈ CodeLang.all := by
  cases l <;> simp [CodeLang.all]

/-- The file extension a language's sources carry first. -/
public def CodeLang.extension (l : CodeLang) : String := l.row.extensions.headD ""

/-- The listing language a code file's code sets in. -/
public def CodeLang.listing (l : CodeLang) : String := l.row.listing

/-- The surface a document or an included file is written in. -/
public inductive Surface where
  | tex
  | markdown
  | code (lang : CodeLang)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The surface an input name's extension selects, `none` where no surface reads it. -/
public def Surface.ofInput? (file : String) : Option Surface :=
  if file.endsWith ".tex" then some .tex
  else if file.endsWith ".md" then some .markdown
  else (CodeLang.all.find? fun l => l.row.extensions.any fun e => file.endsWith ("." ++ e)).map .code

/-- The extensions an input name may end in, as a refusal lists them. -/
public def Surface.inputExtensions : List String :=
  ["tex", "md"] ++ CodeLang.all.flatMap (·.row.extensions)

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
