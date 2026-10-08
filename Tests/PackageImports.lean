module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private def importSource (pre : String) (body : String := "Tail") : String :=
  "\\documentclass{article}\n" ++ pre ++
    "\n\\pagestyle{empty}\\begin{document}" ++ body ++ "\\end{document}"

private def importRun (file src : String) :
    IO (Ir.Doc × Array Diag × Array String) := do
  let (toks, ld) := Lex.lex file src
  let (raws, pd) := Parse.parse file toks
  let (executed, ds, records) ← LeanTex.Cli.Input.expandInputs file raws
  let (doc, ds) := Elab.runExecuted file executed (ld ++ pd ++ ds)
  return (doc, ds, records.map (·.1))

/-- Importing a package again must not register its hooks again, restore
its defaults over intervening declarations, or recurse through its file
again. The comparison reads both artifacts; the trace counts actual style
splices, not package names merely mentioned in the source.

The option expectations are LaTeX's `\@onefilewithoptions`: a later
subset is compatible, new options clash, and the first execution stands.
Conflicting `\def` assignments deliberately keep TeX's source-order
last-write rule. Only disjoint declarations are expected to commute. -/
def packageImportChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let samePage (name : String) (actual expected : Ir.Doc) : IO Unit := do
    let (head, tree, _) := HtmlDoc.emitTree {} actual
    let (wantHead, wantTree, _) := HtmlDoc.emitTree {} expected
    t s!"package imports {name}: typed HTML agrees"
      (Html.document (actual.info.language.getD "en") head tree ==
        Html.document (expected.info.language.getD "en") wantHead wantTree)
    t s!"package imports {name}: Layout.Out agrees"
      (reprStr (layoutOf fonts actual).pages == reprStr (layoutOf fonts expected).pages)
  IO.FS.withTempDir fun dir => do
    let file := (dir / "host.tex").toString
    let style (name body : String) : IO Unit :=
      IO.FS.writeFile (dir / (name ++ ".sty"))
        ("\\ProvidesPackage{" ++ name ++ "}\n" ++ body ++ "\n")
    let hasOnlyNotes (ds : Array Diag) := ds.all (·.severity == .note)
    let plainCase (name pre expected : String) (splices : Array String) : IO Unit := do
      let (doc, ds, actual) ← importRun file (importSource pre)
      let (control, cd) := elabStr (importSource "" expected)
      samePage name doc control
      let (_, tree, _) := HtmlDoc.emitTree {} doc
      t s!"package imports {name}: expected ink reaches HTML"
        (hasStr (shownTextList "" tree.toList) expected)
      t s!"package imports {name}: expected ink reaches Layout.Out"
        ((bodyLines (layoutOf fonts doc)).any fun line => hasStr (lineText line) expected)
      t s!"package imports {name}: actual style splices occur once"
        (actual == splices.map (· ++ ".sty"))
      t s!"package imports {name}: no loss or nesting error"
        (hasOnlyNotes ds && hasOnlyNotes cd)

    IO.FS.writeFile (dir / "part.tex") "\\AtBeginDocument{Again}"
    plainCase "ordinary-input-still-repeats" "\\input{part}\\input{part}"
      "AgainAgainTail" #[]
    style "onceprobe" "\\AtBeginDocument{Loaded}"
    plainCase "local-single" "\\usepackage{onceprobe}" "LoadedTail" #["onceprobe"]
    plainCase "local-repeat" "\\usepackage{onceprobe}\\usepackage{onceprobe}"
      "LoadedTail" #["onceprobe"]
    plainCase "local-duplicate-list" "\\usepackage{onceprobe,onceprobe}"
      "LoadedTail" #["onceprobe"]
    plainCase "local-require-repeat" "\\RequirePackage{onceprobe}\\usepackage{onceprobe}"
      "LoadedTail" #["onceprobe"]
    plainCase "unselected-load" "\\iffalse\\usepackage{onceprobe}\\fi\\usepackage{onceprobe}"
      "LoadedTail" #["onceprobe"]
    plainCase "nullary-macro-load"
      "\\def\\loadprobe{\\usepackage{onceprobe}}\\loadprobe\\loadprobe"
      "LoadedTail" #["onceprobe"]
    plainCase "unused-macro-load"
      "\\def\\loadprobe{\\usepackage{onceprobe}}\\usepackage{onceprobe}"
      "LoadedTail" #["onceprobe"]
    style "onceprobe" "\\RequirePackage{onceprobe}\\AtBeginDocument{Loaded}"
    plainCase "self-cycle" "\\usepackage{onceprobe}" "LoadedTail" #["onceprobe"]
    style "leftprobe" "\\RequirePackage{rightprobe}\\AtBeginDocument{Left}"
    style "rightprobe" "\\RequirePackage{leftprobe}\\AtBeginDocument{Right}"
    plainCase "mutual-cycle" "\\usepackage{leftprobe}" "RightLeftTail"
      #["leftprobe", "rightprobe"]
    style "sharedprobe" "\\AtBeginDocument{Shared}"
    style "leftprobe" "\\RequirePackage{sharedprobe}\\AtBeginDocument{Left}"
    style "rightprobe" "\\RequirePackage{sharedprobe}\\AtBeginDocument{Right}"
    plainCase "diamond" "\\usepackage{leftprobe,rightprobe}" "SharedLeftRightTail"
      #["leftprobe", "sharedprobe", "rightprobe"]
    plainCase "nested-then-sibling" "\\usepackage{leftprobe,sharedprobe}"
      "SharedLeftTail" #["leftprobe", "sharedprobe"]
    style "beamerthemeImportprobe" "\\AtBeginDocument{Theme}"
    plainCase "theme-and-package-share-identity"
      "\\usetheme{Importprobe}\\usepackage{beamerthemeImportprobe}\\usetheme{Importprobe}"
      "ThemeTail" #["beamerthemeImportprobe"]

    style "optionprobe"
      ("\\DeclareOption{a}{\\AtBeginDocument{A}}" ++
       "\\DeclareOption{b}{\\AtBeginDocument{B}}\\ProcessOptions*\\relax")
    plainCase "compatible-options"
      "\\usepackage[a,b]{optionprobe}\\usepackage[b,a,a]{optionprobe}"
      "ABTail" #["optionprobe"]
    plainCase "empty-repeat-options"
      "\\usepackage[a]{optionprobe}\\usepackage{optionprobe}"
      "ATail" #["optionprobe"]
    plainCase "early-option-pass"
      "\\PassOptionsToPackage{a}{optionprobe}\\usepackage{optionprobe}\\usepackage[a]{optionprobe}"
      "ATail" #["optionprobe"]
    plainCase "late-option-pass"
      "\\usepackage[a]{optionprobe}\\PassOptionsToPackage{b}{optionprobe}\\usepackage[b]{optionprobe}"
      "ATail" #["optionprobe"]
    let (clash, ds, records) ← importRun file (importSource
      "\\usepackage[a]{optionprobe}\n\\usepackage[b]{optionprobe}")
    let (control, _) := elabStr (importSource "" "ATail")
    samePage "option-clash-keeps-first" clash control
    t "package imports option clash: no second file execution" (records == #["optionprobe.sty"])
    t "package imports option clash: new option is named at the later load"
      (ds.any fun d => d.code == "W0110" &&
        d.subject == some "package-option-clash:optionprobe:b" &&
        d.span.any (fun s => s.file == file && s.pos.line == 3))
    -- Nested values are one comparison item, not extra compatible options.
    style "optionprobe" "\\DeclareOption*{}\\ProcessOptions*\\relax\\AtBeginDocument{Loaded}"
    let (nested, nestedDs, nestedRecords) ← importRun file (importSource
      "\\usepackage[key={left,a,right}]{optionprobe}\\usepackage[a]{optionprobe}")
    let (nestedControl, _) := elabStr (importSource "" "LoadedTail")
    samePage "nested-value-is-not-an-option-pass" nested nestedControl
    t "package imports nested value: inner item clashes without replay"
      (nestedRecords == #["optionprobe.sty"] && nestedDs.any fun d =>
        d.code == "W0110" && d.subject == some "package-option-clash:optionprobe:a")

    let theoremPre := "\\usepackage{amsthm}\\theoremstyle{definition}"
    let theoremPost := "\\newtheorem{claim}{Claim}"
    let body := "\\begin{claim}Uprightword.\\end{claim}"
    let (once, onceDs, _) ← importRun file (importSource (theoremPre ++ theoremPost) body)
    let (repeated, repeatedDs, _) ← importRun file
      (importSource (theoremPre ++ "\\usepackage{amsthm}" ++ theoremPost) body)
    samePage "native-repeat-preserves-theoremstyle" repeated once
    t "package imports native repeat: both builds recognised"
      (hasOnlyNotes onceDs && hasOnlyNotes repeatedDs)
    let (_, onceTree, _) := HtmlDoc.emitTree {} once
    t "package imports native repeat: control contains the theorem"
      (hasStr (shownTextList "" onceTree.toList) "Uprightword.")
    let (macroDoc, macroDs, _) ← importRun file (importSource
      ("\\def\\loadprobe{\\usepackage{amsthm}}\\loadprobe\\theoremstyle{definition}" ++
       "\\loadprobe" ++ theoremPost) body)
    samePage "native-nullary-macro-load" macroDoc once
    t "package imports native macro: recognised" (hasOnlyNotes macroDs)
    let (unused, unusedDs, _) ← importRun file (importSource
      ("\\def\\loadprobe{\\usepackage{amsthm}}" ++ theoremPre ++ theoremPost) body)
    samePage "unused-native-load-does-not-reserve" unused once
    t "package imports unused native definition: recognised" (hasOnlyNotes unusedDs)

    style "uprightprobe" "\\theoremstyle{definition}"
    let (nativeFirst, nfd, _) ← importRun file (importSource
      ("\\usepackage{amsthm,uprightprobe}" ++ theoremPost) body)
    samePage "mixed-native-then-local" nativeFirst once
    let (plain, _, _) ← importRun file
      (importSource ("\\usepackage{amsthm}" ++ theoremPost) body)
    let (localFirst, lfd, _) ← importRun file (importSource
      ("\\usepackage{uprightprobe,amsthm}" ++ theoremPost) body)
    samePage "mixed-local-then-native" localFirst plain
    t "package imports mixed order: both builds recognised"
      (hasOnlyNotes nfd && hasOnlyNotes lfd)
    t "package imports mixed order: conflicting declarations remain observable"
      (reprStr (layoutOf fonts nativeFirst).pages != reprStr (layoutOf fonts localFirst).pages)

    let languageBody := "\\begin{abstract}Languageword.\\end{abstract}"
    let (english, englishDs, _) ← importRun file
      (importSource "\\usepackage[english]{babel}" languageBody)
    let (late, lateDs, _) ← importRun file (importSource
      "\\usepackage[english]{babel}\\PassOptionsToPackage{french}{babel}\\usepackage[french]{babel}"
      languageBody)
    samePage "native-late-pass-does-not-replay" late english
    t "package imports native late pass: compatible" (hasOnlyNotes lateDs)
    let (french, frenchDs, _) ← importRun file
      (importSource "\\usepackage[french]{babel}" languageBody)
    let (_, englishTree, _) := HtmlDoc.emitTree {} english
    let (_, frenchTree, _) := HtmlDoc.emitTree {} french
    t "package imports language controls: recognised with distinct HTML ink"
      (hasOnlyNotes englishDs && hasOnlyNotes frenchDs &&
        hasStr (shownTextList "" englishTree.toList) "Abstract" &&
        hasStr (shownTextList "" frenchTree.toList) "Résumé")
    t "package imports language controls: distinct Layout.Out ink"
      ((bodyLines (layoutOf fonts english)).any (fun line => hasStr (lineText line) "Abstract") &&
        (bodyLines (layoutOf fonts french)).any (fun line => hasStr (lineText line) "Résumé"))
    let (early, earlyDs, _) ← importRun file (importSource
      "\\PassOptionsToPackage{french}{babel}\\usepackage{babel}\\usepackage[french]{babel}"
      languageBody)
    samePage "native-early-pass" early french
    t "package imports native early pass: compatible" (hasOnlyNotes earlyDs)
    let (nativeClash, ncd, _) ← importRun file (importSource
      "\\usepackage[english]{babel}\\usepackage[french]{babel}" languageBody)
    samePage "native-option-clash-keeps-first" nativeClash english
    t "package imports native option clash: language option named"
      (ncd.any fun d => d.code == "W0110" &&
        d.subject == some "package-option-clash:babel:french")
    let (missing, missingDs, missingRecords) ← importRun file (importSource
      "\\usepackage{missingimportprobe}\\usepackage[a]{missingimportprobe}")
    let (missingControl, _) := elabStr (importSource "")
    samePage "missing-file-is-not-reserved" missing missingControl
    t "package imports missing file: both requests retain their refusal"
      (missingRecords.isEmpty && (missingDs.filter (·.code == "W0103")).size == 2 &&
        !(missingDs.any fun d => d.subject ==
          some "package-option-clash:missingimportprobe:a"))

    style "leftprobe" "\\def\\leftword{Left}"
    style "rightprobe" "\\def\\rightword{Right}"
    let body := "\\leftword\\rightword"
    let (lr, lrd, _) ← importRun file
      (importSource "\\usepackage{leftprobe,rightprobe}" body)
    let (rl, rld, _) ← importRun file
      (importSource "\\usepackage{rightprobe,leftprobe}" body)
    let (control, _) := elabStr (importSource "" "LeftRight")
    samePage "independent-declarations-forward" lr control
    samePage "independent-declarations-reverse" rl control
    t "package imports independent declarations: both orders recognised"
      (hasOnlyNotes lrd && hasOnlyNotes rld)

    style "leftprobe" "\\def\\chosenword{Left}"
    style "rightprobe" "\\def\\chosenword{Right}"
    for (name, pre, expected) in [
        ("conflict-forward", "\\usepackage{leftprobe,rightprobe}", "Right"),
        ("conflict-reverse", "\\usepackage{rightprobe,leftprobe}", "Left"),
        ("conflict-repeat", "\\usepackage{leftprobe,rightprobe}\\usepackage{leftprobe}",
          "Right")] do
      let (doc, ds, _) ← importRun file (importSource pre "\\chosenword")
      let (control, _) := elabStr (importSource "" expected)
      samePage name doc control
      t s!"package imports {name}: explicit TeX def replacement is recognised" (hasOnlyNotes ds)

/-- Standalone entry for the focused gate, using only the shipped font. -/
def packageImportFailures : IO (List String) := do
  let some bytes ← findFont | throw <| IO.userError "shipped fixture font is missing"
  let .ok font := Font.parse bytes | throw <| IO.userError "shipped fixture font is invalid"
  let ref ← IO.mkRef ([] : List String)
  packageImportChecks ref (oneFaceOf font)
  ref.get

end Tests
