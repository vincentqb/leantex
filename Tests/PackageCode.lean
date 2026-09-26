import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # Package code sets no text

A style file is programming: its tests, definitions and hooks address the
engine, never the page. The defect these blocks pin shipped a package name as
the first word of a paper, because a style file's `\AtBeginDocument` hook
tested whether another package was loaded, the test was an unknown command,
and the unknown-command recovery set its arguments as body text. Fixtures in
tests/corpus/sty-parity, synthetic and invented. -/

/-- The body text a `sty-parity` fixture ships, read off the laid-out pages,
with its diagnostics. -/
def styPageText (fonts : Font.FontSet) (name : String) : IO (String × Array Diag) := do
  let (doc, ds, _) ← runStyParity name
  return (String.join ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·)), ds)

/-- **The package-loaded test family is answered from the document's own
loads, and only the branch it picks reaches the page.** latex.ltx's
`\@ifl@aded` holds from the `\usepackage` line on and never before; a test
inside a group — a hook's body, a definition — runs after the preamble, so it
is read against every load the preamble writes; the option forms read the
list the package itself was passed, never the class's global options. Each
row was the whole argument list set as text before the family was read. -/
def loadedTestChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (pre body : String) : String := pageTextOf fonts (dvDoc pre body)
  let (guard, guardDs) ← styPageText fonts "guardhook"
  -- was: "wideframe Body words stay." — the tested name as the first word.
  t "a style file's hook test sets none of its arguments as text"
    (guard.startsWith "Body words stay" && !hasStr guard "wideframe")
  t "the hook's choice is named once, at the style file"
    ((guardDs.filter fun d => d.code == "N0114" &&
        (d.subject.getD "").startsWith "ifloaded:" &&
        d.span.any (·.file == "venueguard.sty")).size == 1)
  let (timing, _) ← styPageText fonts "timinghook"
  t "a hook's test runs after the preamble, so a later load counts"
    (hasStr timing "Framed opening" && !hasStr timing "Plain opening")
  t "a test in the style's own flow runs where it stands, before a later load"
    (hasStr timing "Mark late" && !hasStr timing "early")
  t "a loaded package takes the first branch"
    (let s := page "\\usepackage{booktabs}\n" "\\IfPackageLoadedTF{booktabs}{yes}{no}"
     hasStr s "yes" && !hasStr s "no" && !hasStr s "booktabs")
  t "an absent package takes the second branch"
    (let s := page "" "\\IfPackageLoadedTF{booktabs}{yes}{no}"
     hasStr s "no" && !hasStr s "yes" && !hasStr s "booktabs")
  t "the T form keeps nothing for an absent package, the F form its branch"
    (page "" "one \\IfPackageLoadedT{booktabs}{yes} \\IfPackageLoadedF{booktabs}{no} two" ==
      "one no two")
  t "the class test reads the document class"
    (let s := page "" "\\@ifclassloaded{article}{paged}{other} \\IfClassLoadedTF{beamer}{deck}{flat}"
     hasStr s "paged flat" && !hasStr s "other" && !hasStr s "deck")
  t "an option the package was passed holds"
    (page "\\usepackage[letterpaper]{geometry}\n"
      "\\@ifpackagewith{geometry}{letterpaper}{with}{without}" == "with")
  t "a class option is not an option the package was passed"
    (pageTextOf fonts ("\\documentclass[letterpaper]{article}\n\\usepackage{geometry}\n" ++
      "\\begin{document}\n\\@ifpackagewith{geometry}{letterpaper}{with}{without}\n" ++
      "\\end{document}") == "without")
  t "an option passed ahead of the load holds"
    (page "\\PassOptionsToPackage{draft}{booktabs}\n\\usepackage{booktabs}\n"
      "\\IfPackageLoadedWithOptionsTF{booktabs}{draft}{with}{without}" == "with")
  t "a preamble test before the load reads not loaded"
    (page ("\\@ifpackageloaded{booktabs}{\\newcommand{\\probe}{early}}" ++
      "{\\newcommand{\\probe}{late}}\n\\usepackage{booktabs}\n") "\\probe" == "late")
  t "a preamble test after the load reads loaded"
    (page ("\\usepackage{booktabs}\n\\@ifpackageloaded{booktabs}" ++
      "{\\newcommand{\\probe}{early}}{\\newcommand{\\probe}{late}}\n") "\\probe" == "early")
  t "a definition's test is read against the whole preamble"
    (page "\\newcommand{\\probe}{\\@ifpackageloaded{booktabs}{yes}{no}}\n\\usepackage{booktabs}\n"
      "\\probe" == "yes")
  t "a test inside a kept branch is answered too"
    (page "\\usepackage{booktabs}\n"
      "\\@ifpackageloaded{booktabs}{\\@ifclassloaded{article}{both}{one}}{none}" == "both")
  t "a test missing a branch is left to the unknown-command refusal"
    ((dvE (dvDoc "" "\\@ifpackageloaded{booktabs}{yes}")).any (·.code == "W0301"))


/-- **An unknown command in package code sets none of its arguments, and one
diagnostic per site says so.** The same construct registered by the
document's own hook is document content and keeps today's recovery — that
pair is the two builds the premise beside the rule reads: they differ only
in which file registers the hook, and only the style's drops. Both
artifacts are read: the laid-out pages and the typed HTML tree. -/
def packageCodeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds, _) ← runStyParity "codehook"
  let text := String.join ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·))
  let (_, body, _) := HtmlDoc.emitTree {} doc
  -- was: "hidden words more hidden secret Opening line. kept words".
  t "a style's hook sets none of an unknown command's arguments on the page"
    (!hasStr text "hidden" && !hasStr text "secret" && !hasStr text "wide" &&
     hasStr text "Opening line.")
  t "nor in the web page"
    (treeShownOccurs body "hidden" == 0 && treeShownOccurs body "secret" == 0 &&
     treeShownOccurs body "Opening line." == 1)
  t "the document's own use of the same command keeps its arguments"
    (hasStr text "kept words" && treeShownOccurs body "kept words" == 1)
  let pkg := ds.filter fun d => d.code == "W0391" && d.span.any (·.file == "venuecode.sty")
  t "each package-code site is named once, under the construct's own key"
    (pkg.size == 2 &&
     pkg.any (·.subject == some "pkgcode:venueprobe") &&
     pkg.any (·.subject == some "pkgcode:@venuehelper"))
  t "a TeX internal there is a note, counted as the style file's refusal"
    (pkg.any (fun d => d.subject == some "pkgcode:@venuehelper" && d.severity == .note) &&
     pkg.any (fun d => d.subject == some "pkgcode:venueprobe" && d.severity == .warning) &&
     Compat.styCounts "venuecode.sty" ds == (1, 1, 1))
  t "the document's site keeps its own refusal, with the kept text as salvage"
    ((ds.filter fun d => d.code == "W0301" && d.subject == some "ctrl:venueprobe").size == 1 &&
     doc.salvage.all (fun s => !hasStr s.text "hidden" && !hasStr s.text "secret") &&
     doc.salvage.any (fun s => hasStr s.text "kept words"))
  -- The other build: the same hook written by the document itself.
  let own := pageTextOf fonts
    ("\\documentclass{article}\n\\AtBeginDocument{\\venueprobe[wide]{hidden words}}\n" ++
     "\\begin{document}\nOpening line.\n\\end{document}")
  t "the same hook registered by the document keeps the arguments as text"
    (hasStr own "hidden words" && hasStr own "Opening line.")
  -- The loaded-test fixture, on the web page too.
  let (gDoc, _, _) ← runStyParity "guardhook"
  let (_, gBody, _) := HtmlDoc.emitTree {} gDoc
  t "a style's hook test sets no text in the web page either"
    (treeShownOccurs gBody "wideframe" == 0 && treeShownOccurs gBody "Body words stay." == 1)
