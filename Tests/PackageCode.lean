module

public import Tests.Support
import Tests.VenueStyle

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! Package code sets no text from a LaTeX internal. -/

/-- The body text and diagnostics of a `sty-parity` fixture, read off its laid-out pages. -/
def styPageText (fonts : Font.FontSet) (name : String) : IO (String × Array Diag) := do
  let (doc, ds, _) ← runStyParity name
  return (String.join ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·)), ds)

/-- The package-loaded test family is answered from the document's own loads, and only the branch it
picks reaches the page. -/
def loadedTestChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let page (pre body : String) : String := pageTextOf fonts (dvDoc pre body)
  let (guard, guardDs) ← styPageText fonts "guardhook"
  t "a style file's hook test sets none of its arguments as text"
    (guard.startsWith "Body words stay" && !hasStr guard "wideframe")
  t "the hook's choice is named once, at the style file"
    ((guardDs.filter fun d => d.code == "N0114" &&
        (d.subject.getD "").startsWith "ifloaded:" &&
        d.span.any (·.file == "venueguard.sty")).size == 1)
  let (timing, _) ← styPageText fonts "timinghook"
  t "a hook's test runs after the preamble, so a later load counts"
    (hasStr timing "Framed opening" && !hasStr timing "Plain opening")
  t "a test in the style's flow runs where it stands, before later loads"
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
  t "a definition used after the preamble sees its completed loads"
    (page "\\newcommand{\\probe}{\\@ifpackageloaded{booktabs}{yes}{no}}\n\\usepackage{booktabs}\n"
      "\\probe" == "yes")
  t "a test inside a kept branch is answered too"
    (page "\\usepackage{booktabs}\n"
      "\\@ifpackageloaded{booktabs}{\\@ifclassloaded{article}{both}{one}}{none}" == "both")
  t "a test missing a branch is left to the unknown-command refusal"
    ((dvE (dvDoc "" "\\@ifpackageloaded{booktabs}{yes}")).any (·.code == "W0301"))


/-- A LaTeX internal in package code sets none of its arguments and is named once per site; every
other unknown command there keeps them. -/
def packageCodeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds, _) ← runStyParity "codehook"
  -- Lines joined with a space: a phrase that wraps still reads as one.
  let text := " ".intercalate ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·))
  let (_, body, _) := HtmlDoc.emitTree {} doc
  t "a style hook sets none of an internal's arguments on the page"
    (!hasStr text "secret" && !hasStr text "mode" && hasStr text "Opening line.")
  t "nor in the web page"
    (treeShownOccurs body "secret" == 0 && treeShownOccurs body "mode" == 0 &&
     treeShownOccurs body "Opening line." == 1)
  t "a venue macro in a style hook keeps its arguments, drops its option run"
    (hasStr text "style words" && !hasStr text "wide" &&
     treeShownOccurs body "style words" == 1)
  t "a TeX primitive in a style hook keeps its group"
    (hasStr text "boxed words" && treeShownOccurs body "boxed words" == 1)
  t "the document's own use of the venue macro keeps its arguments"
    (hasStr text "kept words" && treeShownOccurs body "kept words" == 1)
  let pkg := ds.filter fun d => d.code == "W0391" && d.span.any (·.file == "venuecode.sty")
  t "the internal is named once under its own key, the style's refusal"
    (pkg.size == 1 &&
     pkg.all (fun d => d.subject == some "pkgcode:@venuehelper" && d.severity == .note) &&
     Compat.styCounts "venuecode.sty" ds == (1, 1, 2))
  t "other commands keep the document's refusal, the kept text salvaged"
    ((ds.filter fun d => d.code == "W0301" && d.subject == some "ctrl:venueprobe").size == 2 &&
     (ds.filter fun d => d.code == "W0301" && d.subject == some "ctrl:hbox").size == 1 &&
     doc.salvage.all (fun s => !hasStr s.text "secret") &&
     doc.salvage.any (fun s => hasStr s.text "style words") &&
     doc.salvage.any (fun s => hasStr s.text "kept words"))
  let own := pageTextOf fonts
    ("\\documentclass{article}\n\\AtBeginDocument{\\@venuehelper[mode]{own words}}\n" ++
     "\\begin{document}\nOpening line.\n\\end{document}")
  t "the internal in a document-registered hook keeps its arguments"
    (hasStr own "own words" && !hasStr own "mode" && hasStr own "Opening line.")
  let (sDoc, sDs, _) ← runStyParity "sizehook"
  let sText := " ".intercalate ((bodyLines (layoutOf fonts sDoc)).toList.map (lineText ·))
  t "a style's kernel-internal size redefinition sets none as text"
    (hasStr sText "Small words." && !hasStr sText "11")
  t "the trial reads the body as its use will: the refused size is a step"
    ((sDs.filter fun d => d.code == "N0100" && d.span.any (·.file == "venuesize.sty")).size == 2 &&
     sDs.all (·.code != "W0391"))
  let (gDoc, _, _) ← runStyParity "guardhook"
  let (_, gBody, _) := HtmlDoc.emitTree {} gDoc
  t "a style's hook test sets no text in the web page either"
    (treeShownOccurs gBody "wideframe" == 0 && treeShownOccurs gBody "Body words stay." == 1)
  venueStyleChecks ref fonts
