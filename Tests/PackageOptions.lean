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

/-- Unknown caller options are losses, including options left unprocessed
at the end of a package. The expected diagnostics name the package, option
and source line; line 1 names an unprocessed load, other lines its process
site. LuaLaTeX must independently reject every case with a live loss.
An absent catch-all differs from an explicitly declared empty one. -/
structure PackageOptionDiagCase where
  name : String
  passed : String := "u"
  style : String := "\\ProcessOptions*\\relax\n"
  expected : String := "Tail"
  unhandled : Array (String × String × Nat) := #[]
  beforeLoad : String := ""
  afterLoad : String := ""

def packageOptionDiagCases : Array PackageOptionDiagCase := Id.run do
  let a := packageOptionDeclare "a" "A"
  let plain := "\\ProcessOptions\\relax\n"
  let star := "\\ProcessOptions*\\relax\n"
  let issue (option : String) (line : Nat) := #[( "pkgoptionsprobe", option, line)]
  return #[
    { name := "unknown-plain", style := plain, unhandled := issue "u" 3 },
    { name := "unknown-star", unhandled := issue "u" 3 },
    { name := "mixed-unhandled", passed := "u,a,v", style := a ++ plain,
      expected := "ATail",
      unhandled := #[("pkgoptionsprobe", "u", 4), ("pkgoptionsprobe", "v", 4)] },
    { name := "normalised-unhandled", passed := " key = value ",
      unhandled := issue "key=value" 3 },
    { name := "duplicate-unhandled", passed := "u,u",
      unhandled := issue "u" 3 ++ issue "u" 3 },
    { name := "empty-items-unhandled", passed := ",u,,",
      unhandled := issue "u" 3 },
    { name := "no-options", passed := ",," },
    { name := "unknown-default-is-inert", passed := "",
      style := "\\ExecuteOptions{u}\n" ++ plain },
    { name := "unused-handler-is-inert", style :=
        "\\DeclareOption{unused}{\\directlua{error('unused')}}\n" ++ star,
      unhandled := issue "u" 4 },
    { name := "catch-all-handles", style := packageOptionDefault "U" ++ star,
      expected := "UTail" },
    { name := "empty-catch-all-handles", style := "\\DeclareOption*{}\n" ++ star },
    { name := "catch-all-is-not-retroactive", style := star ++ packageOptionDefault "U",
      unhandled := issue "u" 3 },
    { name := "declaration-is-not-retroactive", style := star ++ packageOptionDeclare "u" "U",
      unhandled := issue "u" 3 },
    { name := "spent-star-is-unhandled", passed := "a", style := a ++ star ++ star,
      expected := "ATail", unhandled := issue "a" 5 },
    { name := "spent-plain-stays-empty", passed := "a", style := a ++ plain ++ plain,
      expected := "ATail" },
    { name := "spent-default-is-inert", passed := "a",
      style := a ++ star ++ "\\ExecuteOptions{a,u}", expected := "ATail" },
    { name := "redeclared-handler-is-live", passed := "a",
      style := a ++ star ++ packageOptionDeclare "a" "B" ++ star, expected := "ABTail" },
    { name := "no-process", style := "", unhandled := issue "u" 1 },
    { name := "declared-but-unprocessed", passed := "a", style := a,
      unhandled := issue "a" 1 },
    { name := "catch-all-but-unprocessed", style := packageOptionDefault "U",
      unhandled := issue "u" 1 },
    { name := "false-load", beforeLoad := "\\iffalse\n", afterLoad := "\\fi\n" },
    { name := "true-load", beforeLoad := "\\iftrue\n", afterLoad := "\\fi\n",
      unhandled := issue "u" 3 },
    { name := "false-process", style := "\\iffalse\n" ++ star ++ "\\fi\n",
      unhandled := issue "u" 1 },
    { name := "true-process", style := "\\iftrue\n" ++ star ++ "\\fi\n",
      unhandled := issue "u" 4 },
    { name := "endinput-before-process", style := "\\endinput\n" ++ star,
      unhandled := issue "u" 1 },
    { name := "endinput-after-process", passed := "a",
      style := a ++ star ++ "\\endinput\n" ++ star, expected := "ATail" },
    { name := "nested-load", passed := "",
      style := "\\RequirePackage[u]{pkgoptionschild}\n" ++ star,
      unhandled := #[("pkgoptionschild", "u", 2)] },
    { name := "nested-process-does-not-discharge-parent",
      style := "\\RequirePackage{pkgoptionschild}\n", unhandled := issue "u" 1 },
    { name := "nested-false-load", passed := "",
      style := "\\iffalse\n\\RequirePackage[u]{pkgoptionschild}\n\\fi\n" ++ star },
    { name := "unselected-nested-load", passed := "", style :=
      "\\DeclareOption{unused}{\\RequirePackage[u]{pkgoptionschild}}\n" ++ star }]

def packageOptionDiagSource (c : PackageOptionDiagCase) : String :=
  "\\documentclass{article}\n" ++ c.beforeLoad ++
    "\\usepackage[" ++ c.passed ++ "]{pkgoptionsprobe}\n" ++ c.afterLoad ++
    "\\pagestyle{empty}\n\\begin{document}Tail\\end{document}\n"

def packageOptionChildStyle : String :=
  "\\ProvidesPackage{pkgoptionschild}\n\\ProcessOptions*\\relax\n"

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
    let sameSourcePage (name style source expected : String) : IO (Array Diag) := do
      IO.FS.writeFile (dir / "pkgoptionsprobe.sty") (packageOptionStyle style)
      let (doc, ds) ← elabInputSrc file source
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
    let samePage (name style passed body expected : String) :=
      sameSourcePage name style (packageOptionSource passed body) expected
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

    IO.FS.writeFile (dir / "pkgoptionschild.sty") packageOptionChildStyle
    for c in packageOptionDiagCases do
      let ds ← sameSourcePage c.name c.style (packageOptionDiagSource c) c.expected
      let losses := ds.filter (·.code == "W0110")
      let actual := losses.map fun d =>
        (d.subject.getD "", d.span.map (·.file), d.span.map (·.pos))
      let expected := c.unhandled.map fun (pkg, option, line) =>
        ("package-option:" ++ pkg ++ ":" ++ option, some (pkg ++ ".sty"),
          some ({ line, col := 1 } : Pos))
      t s!"package options {c.name}: exactly the live losses, keyed and source-located"
        (actual == expected)
      t s!"package options {c.name}: only W0110 names ignored options"
        (ds.all fun d => d.severity == .note || d.code == "W0110")
      t s!"package options {c.name}: loss is degraded, never an error"
        (losses.all fun d => d.kind.loss == .degraded && d.severity != .error)
      t s!"package options {c.name}: one warning per option, every site counted"
        (losses.foldl (fun n d => n + d.sites) 0 == c.unhandled.size &&
          (losses.filter (·.severity != .note)).size ==
            (c.unhandled.toList.map fun (pkg, option, _) => (pkg, option)).eraseDups.length)
      t s!"package options {c.name}: diagnostic names the package and the option"
        ((losses.zip c.unhandled).all fun (d, pkg, option, _) =>
          hasStr d.message pkg && hasStr d.message option)

/-- Standalone engine entry used by the synthetic comparison script.
The parent suite can supply its shared fonts to `packageOptionChecks`;
this entry needs only the shipped fixture face. -/
def packageOptionFailures : IO (List String) := do
  let some bytes ← findFont | throw <| IO.userError "shipped fixture font is missing"
  let .ok font := Font.parse bytes | throw <| IO.userError "shipped fixture font is invalid"
  let ref ← IO.mkRef ([] : List String)
  packageOptionChecks ref (oneFaceOf font)
  ref.get

end Tests
