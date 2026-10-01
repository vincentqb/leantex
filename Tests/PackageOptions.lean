import Tests.Support

open LeanTex.Core

namespace Tests

/-- Synthetic local styles measured against LuaLaTeX's ltclass option
machinery. The expected text is committed independently of the resolver.
Bodies register literal begin-document ink so order and multiplicity are
observable on both shipped surfaces, without a TeX expansion runtime. -/
structure PackageOptionCase where
  name : String
  passed : String
  style : String
  expected : String
  body : String := "Tail"

def packageOptionDeclare (name ink : String) : String :=
  "\\DeclareOption{" ++ name ++ "}{\\AtBeginDocument{" ++ ink ++ "}}\n"

def packageOptionDefault (ink : String) : String :=
  "\\DeclareOption*{\\AtBeginDocument{" ++ ink ++ "}}\n"

/-- Declaration order, caller order and default order are three different
orders. In particular, a starred process repeats a repeated caller option;
an unstarred process runs each declared name once, using its latest body at
its first declaration's position. Executing defaults does not consume them;
processing does. Unknown defaults do not call the catch-all. -/
def packageOptionCases : Array PackageOptionCase := Id.run do
  let ab := packageOptionDeclare "a" "A" ++ packageOptionDeclare "b" "B"
  let fallback := packageOptionDefault "U"
  let plain := "\\ProcessOptions\\relax"
  let starred := "\\ProcessOptions*\\relax"
  return #[
    ⟨"declared-order", "b,a", ab ++ plain, "ABTail", "Tail"⟩,
    ⟨"passed-order", "b,a", ab ++ starred, "BATail", "Tail"⟩,
    ⟨"defaults-order", "b", ab ++ "\\ExecuteOptions{b,a}" ++ plain, "BABTail", "Tail"⟩,
    ⟨"defaults-before-star", "a,b", ab ++ "\\ExecuteOptions{b,a}" ++ starred,
      "BAABTail", "Tail"⟩,
    ⟨"catch-all", "u", fallback ++ plain, "UTail", "Tail"⟩,
    ⟨"mixed-declared", "u,b,v,a", ab ++ fallback ++ plain, "ABUUTail", "Tail"⟩,
    ⟨"mixed-passed", "u,b,v,a", ab ++ fallback ++ starred, "UBUATail", "Tail"⟩,
    ⟨"redeclared-name", "b,a",
      packageOptionDeclare "a" "Old" ++ packageOptionDeclare "b" "B" ++
        packageOptionDeclare "a" "New" ++ plain, "NewBTail", "Tail"⟩,
    ⟨"redeclared-default", "u", packageOptionDefault "Old" ++
      packageOptionDefault "New" ++ plain, "NewTail", "Tail"⟩,
    ⟨"unknown-defaults", "", ab ++ fallback ++
      "\\ExecuteOptions{u,b,v,a}" ++ plain, "BATail", "Tail"⟩,
    ⟨"duplicate-star", "a,b,a", ab ++ starred, "ABATail", "Tail"⟩,
    ⟨"duplicate-unstar", "a,b,a", ab ++ plain, "ABTail", "Tail"⟩,
    ⟨"duplicate-execute", "", ab ++ "\\ExecuteOptions{a,a,b}" ++ plain, "AABTail", "Tail"⟩,
    ⟨"duplicate-unknown", "u,u", fallback ++ starred, "UUTail", "Tail"⟩,
    ⟨"empty-options", "", ab ++ fallback ++ "\\ExecuteOptions{}" ++ starred, "Tail", "Tail"⟩,
    ⟨"unused-default", "a", ab ++ fallback ++ starred, "ATail", "Tail"⟩,
    ⟨"catch-all-without-process", "", fallback ++ "\\AtBeginDocument{S}", "STail", "Tail"⟩,
    ⟨"empty-catch-all", "u", "\\DeclareOption*{}" ++ starred ++
      "\\AtBeginDocument{S}", "STail", "Tail"⟩,
    ⟨"spaced-stars", "u", "\\DeclareOption *{\\AtBeginDocument{U}}\n" ++
      "\\ProcessOptions * \\relax", "UTail", "Tail"⟩,
    ⟨"process-without-relax", "b,a", ab ++ "\\ProcessOptions*\\AtBeginDocument{S}",
      "BASTail", "Tail"⟩,
    ⟨"execute-spaces", "", packageOptionDeclare "alpha" "A" ++
      "\\ExecuteOptions{ a l p h a }" ++ plain, "ATail", "Tail"⟩,
    ⟨"passed-spaces", " a l p h a ", packageOptionDeclare "alpha" "A" ++ starred,
      "ATail", "Tail"⟩,
    ⟨"key-value", "key = value", packageOptionDeclare "key=value" "V" ++ starred,
      "VTail", "Tail"⟩,
    ⟨"empty-passed-items", ",a,,b,", ab ++ fallback ++ starred, "ABTail", "Tail"⟩,
    ⟨"empty-default-items", "", ab ++ fallback ++ "\\ExecuteOptions{,a,,b,}" ++ plain,
      "ABTail", "Tail"⟩,
    ⟨"empty-declaration-process", ",a,", packageOptionDeclare "" "E" ++ ab ++
      fallback ++ starred, "ATail", "Tail"⟩,
    ⟨"empty-declaration-execute", "", packageOptionDeclare "" "E" ++ ab ++
      "\\ExecuteOptions{,a,}" ++ plain, "EAETail", "Tail"⟩,
    ⟨"execute-before-declaration", "a", "\\ExecuteOptions{a}" ++ ab ++ plain, "ATail", "Tail"⟩,
    ⟨"execute-after-process", "a", ab ++ plain ++ "\\ExecuteOptions{a,b}", "ATail", "Tail"⟩,
    ⟨"repeat-unstar", "a", ab ++ fallback ++ plain ++ plain, "ATail", "Tail"⟩,
    ⟨"repeat-star", "a", ab ++ fallback ++ starred ++ starred, "AUTail", "Tail"⟩,
    ⟨"redeclare-after-process", "b,a", ab ++ plain ++ packageOptionDeclare "a" "C" ++
      plain, "ABCTail", "Tail"⟩,
    ⟨"flag-declared-order", "b,a",
      "\\newif\\ifoptionprobe\\optionprobefalse\n" ++
      "\\DeclareOption{a}{\\optionprobefalse}\n" ++
      "\\DeclareOption{b}{\\optionprobetrue}\n" ++ plain,
      "ChosenTail", "\\ifoptionprobe Chosen\\else Other\\fi Tail"⟩,
    ⟨"flag-passed-order", "b,a",
      "\\newif\\ifoptionprobe\\optionprobefalse\n" ++
      "\\DeclareOption{a}{\\optionprobefalse}\n" ++
      "\\DeclareOption{b}{\\optionprobetrue}\n" ++ starred,
      "OtherTail", "\\ifoptionprobe Chosen\\else Other\\fi Tail"⟩]

def packageOptionStyle (style : String) : String :=
  "\\NeedsTeXFormat{LaTeX2e}\n\\ProvidesPackage{pkgoptionsprobe}[2026/10/01 Synthetic]\n" ++
    style ++ "\n"

def packageOptionSource (passed body : String) : String :=
  "\\documentclass{article}\n\\usepackage[" ++ passed ++ "]{pkgoptionsprobe}\n" ++
    "\\pagestyle{empty}\n\\begin{document}" ++ body ++ "\\end{document}\n"

/-- The option resolver must preserve the actual local-style splice's
execution order, multiplicity and body boundaries on Layout.Out and the
typed HTML tree. An unselected body stays inert; a selected unsupported
body keeps its existing explicit refusal. No assertion reads an IR dump.
Run by scripts/package-options.lean until the parent wires this block into
the suite; the test-module-only edit keeps that integration independent. -/
def packageOptionChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let samePage (name style passed body expected : String) : IO (Array Diag) := do
      IO.FS.writeFile (dir / "pkgoptionsprobe.sty") (packageOptionStyle style)
      let (doc, ds) ← elabInputSrc file (packageOptionSource passed body)
      let (control, controlDs) := elabStr
        ("\\documentclass{article}\\pagestyle{empty}\\begin{document}" ++
          expected ++ "\\end{document}")
      let (head, tree, _) := HtmlDoc.emitTree {} doc
      let (controlHead, controlTree, _) := HtmlDoc.emitTree {} control
      let out := layoutOf fonts doc
      let controlOut := layoutOf fonts control
      t s!"package options {name}: control is recognised"
        (controlDs.all (·.severity == .note))
      t s!"package options {name}: typed HTML has exactly the selected ink"
        (Html.document "en" head tree == Html.document "en" controlHead controlTree)
      t s!"package options {name}: Layout.Out has exactly the selected ink"
        (reprStr out.pages == reprStr controlOut.pages)
      t s!"package options {name}: HTML witness reaches the reader"
        (hasStr (shownTextList "" tree.toList) expected)
      t s!"package options {name}: layout witness reaches the reader"
        ((bodyLines out).any fun line => hasStr (lineText line) expected)
      return ds
    for c in packageOptionCases do
      let ds ← samePage c.name c.style c.passed c.body c.expected
      t s!"package options {c.name}: no error or unsupported command"
        (ds.all fun d => d.severity == .note && d.refused.isNone)

    -- Selection schedules a body, never interprets a TeX program inside
    -- it. The unsupported operation is still named at its style-file site.
    for (name, body, code) in [
        ("expanding-definition", "\\edef\\optionprobe{Unused}", "W0357"),
        ("package-error", "\\PackageError{pkgoptionsprobe}{Unused}{Unused}", "W0387"),
        ("lua", "\\directlua{error('unused')}", "W0104")] do
      let decl := "\\DeclareOption*{" ++ body ++ "}\\ProcessOptions*\\relax"
      let ds ← samePage name decl "u" "Tail" "Tail"
      t s!"package options {name}: selected refusal keeps its code and source"
        (ds.any fun d => d.code == code && d.span.any (·.file.endsWith "pkgoptionsprobe.sty"))
      t s!"package options {name}: refusal is not an error"
        (ds.all (·.severity != .error))
      let unused := "\\DeclareOption{unused}{" ++ body ++ "}\\ProcessOptions\\relax"
      let ds ← samePage (name ++ "-unselected") unused "" "Tail" "Tail"
      t s!"package options {name}: unselected refusal stays inert"
        (ds.all fun d => d.severity == .note && d.code != code)

end Tests
