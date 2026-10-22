module

public import LeanTex.Cli.FontDiscovery
public import LeanTex.Cli.FontAssembly
public import Tests.FontMath

public section

namespace Tests

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly

private def fontDefaultSource (slides : Bool) (spec : Ir.FontSpec) : String :=
  let declarations := [
    ("setmainfont", spec.body), ("setsansfont", spec.sans),
    ("setmonofont", spec.mono), ("setmathfont", spec.math)]
  String.intercalate "\n" (
    ["\\documentclass{" ++ (if slides then "beamer" else "article") ++ "}",
     "\\usepackage{fontspec}"] ++
    declarations.filterMap (fun (command, family) =>
      family.map fun f => "\\" ++ command ++ "{" ++ f ++ "}") ++
    ["\\begin{document}",
     if slides then "\\begin{frame}{Heading}" else "\\section*{Heading}",
     "Plain\\par", "\\textbf{Bold}\\par", "\\textit{Slant}\\par",
     "\\textbf{\\textit{Both}}\\par", "\\texttt{Code}\\par", "$x$",
     if slides then "\\end{frame}" else "", "\\end{document}"])

/-- A mono or math declaration cannot choose the text family: through the driver's assembly, the
layout's glyphs and the HTML head consume the resolved text face. -/
def fontDefaultsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let scanned ← FontDiscovery.scanRootsIn none [testFonts]
  -- Fix the default candidate order without depending on host fonts.
  let faces := scanned.filter (·.family == "Open Sans") ++
    scanned.filter (·.family != "Open Sans")
  let some defaultFamily := FontDb.defaultFamily faces |
    throw <| IO.userError "font defaults: the vendored scan has no default"
  let scan : FaceScan := { faces, docDirs := [], dirs := #[], diags := #[] }
  let cache ← FontEnv.Cache.mk'
  let corners := [(400, false), (700, false), (400, true), (700, true)]
  for slides in [false, true] do
    for body in [none, some "Source Serif Pro"] do
      for sans in [none, some "Fira Sans"] do
        for mono in [none, some "Source Code Pro"] do
          for math in [none, some "Fira Math"] do
            if body.isNone && sans.isNone && mono.isNone && math.isNone then continue
            let spec : Ir.FontSpec := { body, sans, mono, math }
            let (doc, _) := elabStr (fontDefaultSource slides spec)
            let label := s!"font defaults {slides}/{body}/{sans}/{mono}/{math}"
            let t := fun why ok => check ref (label ++ ": " ++ why) ok
            t "surface declarations reach the driver"
              (doc.fonts.body == body && doc.fonts.sans == sans &&
               doc.fonts.mono == mono && doc.fonts.math == math)
            let textFamily := (if slides then sans.orElse (fun _ => body)
              else body.orElse (fun _ => sans)).getD defaultFamily
            let expected ← corners.toArray.mapM fun (weight, italic) => do
              let some (face, _) := FontDb.resolveWeight faces textFamily none weight italic |
                throw <| IO.userError s!"font defaults: missing fixture family {textFamily}"
              let .ok f ← cache.parse face.path |
                throw <| IO.userError "font defaults: a fixture face did not parse"
              return f
            for purpose in [Purpose.provisional false, .provisional true, .settled] do
              let .ok (fs, resolved, diags, _) ← buildFontSet doc scan cache purpose |
                t s!"{repr purpose} assembly succeeds" false
                continue
              t s!"{repr purpose} keeps explicit text mappings for all four variants"
                (corners.toArray.zip expected |>.all fun ((weight, italic), f) =>
                  fs.index.any (·.1 == (0, weight, italic)) &&
                  (fs.get (fs.lookup 0 weight italic)).psName == f.psName)
              t s!"{repr purpose} starts with the text regular face"
                (fs.body.psName == expected[0]!.psName)
              t s!"{repr purpose} resolves every installed declaration"
                (!diags.any (·.kind == .W0390))
              t s!"{repr purpose} supplies math when declared or needed"
                (fs.mathFont?.isSome ==
                  (math.isSome || purpose != .provisional false))
              if let some _ := math then
                t s!"{repr purpose} retains the independent math face"
                  (fs.mathFont?.any fun (_, f, _) => f.family == "Fira Math")
              unless purpose == .settled do continue
              if let some _ := mono then
                t "retains the independent mono face"
                  ((fs.get (fs.lookup 2 400 false)).family == "Source Code Pro")
              let out := layoutOf fs resolved
              t "Layout keeps formulas in a math face"
                (!out.diags.any (·.kind == .W0003))
              for (word, f) in #[("Plain", expected[0]!), ("Bold", expected[1]!),
                  ("Slant", expected[2]!), ("Both", expected[3]!)] do
                let lines := out.pages.flatMap (·.lines) |>.filter fun line =>
                  hasStr (lineText line) word
                t s!"Layout paints {word} with the text variant"
                  (!lines.isEmpty && lines.all fun line => line.segs.all fun
                    | .run i _ _ _ glyphs _ _ _ _ _ _ =>
                      glyphs.isEmpty || (fs.get i).psName == f.psName
                    | _ => true)
              let titles := out.pages.flatMap (·.lines) |>.filter fun line =>
                hasStr (lineText line) "Heading"
              t "Layout paints a title in the text family"
                (!titles.isEmpty && titles.all fun line => line.segs.all fun
                  | .run i _ _ _ glyphs _ _ _ _ _ _ =>
                    glyphs.isEmpty || (fs.get i).family == textFamily
                  | _ => true)
              let (head, tree, htmlDiags) := HtmlDoc.emitTree { fonts := some fs } resolved
              let css := String.join (head.toList.filterMap fun
                | .style rules => some rules
                | _ => none)
              t "typed HTML ships its text and title"
                (treeOccurs tree "Plain" > 0 && treeOccurs tree "Heading" > 0)
              t "typed HTML resolves the body stack to the selected text program"
                (htmlSlotSource css "body" == some (HtmlDoc.fontResource expected[0]!).uri)
              t "typed HTML embeds the resolved math program"
                (htmlSlotSource css "math" ==
                  fs.mathFont?.map (fun (_, f, _) => (HtmlDoc.fontResource f).uri) &&
                 !htmlDiags.any (·.kind == .W0003))
  -- A declared family no face answers is named once, its slot set as the undeclared document's.
  let (plainDoc, _) := elabStr (fontDefaultSource false {})
  let .ok (plain, _, _, _) ← buildFontSet plainDoc scan cache .settled |
    check ref "font defaults: the undeclared document assembles" false
  let corner (fs : Font.FontSet) (slot w : Nat) (i : Bool) : String :=
    (fs.get (fs.lookup slot w i)).psName
  let asPlain (fs : Font.FontSet) : Bool := (List.range 3).all fun k =>
    FontDb.corners.all fun (w, i) => corner fs k w i == corner plain k w i
  for slot in [0:4] do
    let missing := "MissingFixtureFamily"
    let spec : Ir.FontSpec :=
      match slot with
      | 0 => { body := some missing }
      | 1 => { sans := some missing }
      | 2 => { mono := some missing }
      | _ => { math := some missing }
    let doc := (elabStr (fontDefaultSource false spec)).1
    let .ok (fs, _, diags, _) ← buildFontSet doc scan cache .settled |
      check ref s!"font defaults: missing slot {slot} still ships its document" false
      continue
    check ref s!"font defaults: missing slot {slot} is named once, as a degraded loss"
      ((diags.filter (·.kind == .W0390)).size == 1 &&
       diags.any (fun d => d.kind == .W0390 && hasStr d.message missing) &&
       diags.all (·.severity != .error))
    check ref s!"font defaults: missing slot {slot} sets as the undeclared document does"
      (asPlain fs && (fs.mathFont?.map (·.2.1.psName)) == (plain.mathFont?.map (·.2.1.psName)))
    let empty ← buildFontSet doc { scan with faces := #[] } cache .settled
    check ref s!"font defaults: an empty scan stops on no usable font, missing slot {slot}"
      (match empty with
       | .error d => d.kind == .E0401
       | .ok _ => false)
  -- A label its face files serve is no missing family; a missing one's face reads as undeclared.
  let .ok bold ← cache.parse (testFonts ++ "/SourceSerifPro-Bold.otf") |
    check ref "font defaults: the bold fixture parses" false
  let labelFaces : Array ((Nat × Nat × Bool) × String) :=
    #[((0, 400, false), "SourceSerifPro-Regular.otf"),
      ((0, 700, false), "SourceSerifPro-Bold.otf"),
      ((0, 400, true), "SourceSerifPro-RegularIt.otf"),
      ((0, 700, true), "SourceSerifPro-BoldIt.otf")]
  for (what, family, faces, served) in
      [("a label its four face files serve", "FixtureLabel", labelFaces, true),
       ("a missing family beside one face file", "MissingFixtureFamily",
         #[((0, 700, false), "SourceSerifPro-Bold.otf")], false)] do
    let doc := { plainDoc with fonts := { plainDoc.fonts with body := some family, faces } }
    match ← buildFontSet doc scan cache .settled with
    | .ok (fs, _, diags, _) =>
      check ref s!"font defaults: {what} is named missing {if served then "never" else "once"}"
        ((diags.filter (·.kind == .W0390)).size == (if served then 0 else 1))
      check ref s!"font defaults: {what} sets {if served then "its faces" else "as undeclared"}"
        (if served then corner fs 0 700 false == bold.psName else asPlain fs)
    | .error _ => check ref s!"font defaults: {what} ships its document" false

/-- Two weights a family lacks, served by one nearest face, are two records in one wording that the
log folds to one line counting both. -/
def weightSubstitutionRecordChecks (ref : IO.Ref (List String)) : IO Unit := do
  let faces ← FontDiscovery.scanRootsIn none [testFonts]
  let scan : FaceScan := { faces, docDirs := [], dirs := #[], diags := #[] }
  let doc := (elabStr (String.intercalate "\n" [
    "\\documentclass{article}", "\\usepackage{fontspec}",
    "\\setmainfont{Open Sans}", "\\setsansfont{Open Sans}", "\\begin{document}",
    "{\\fontseries{el}\\selectfont Extra light.} {\\fontseries{l}\\selectfont Light.}",
    "\\textsf{\\fontseries{l}\\selectfont Light again.}", "\\end{document}"])).1
  let t := fun why ok => check ref ("weight substitution records: " ++ why) ok
  let .ok (_, _, diags, _) ← buildFontSet doc scan (← FontEnv.Cache.mk') .settled |
    t "the assembly succeeds" false
  let subs := diags.filter (·.kind == .W0006)
  t s!"one record per substituted weight: {subs.map (·.detail)}"
    (subs.map (·.detail) == #[some "weight 200 asked, weight 400 the nearest",
      some "weight 300 asked, weight 400 the nearest"])
  let folded := Diag.foldRepeats subs
  t "the log prints them as one line counting both"
    ((folded.filter (·.severity.isWarning)).map (·.sites) == #[2] &&
     (folded.filter (·.demoted)).size == 1)

/-- The single-face override applies only with no declared family; with mono or math alone even an
invalid override is ignored, the pitch read from the embedded program. -/
def fontDefaultsOverrideChecks (ref : IO.Ref (List String))
    (executable : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let binary ← IO.FS.realPath executable
  let corpus ← IO.FS.realPath testFonts
  IO.FS.withTempDir fun dir => do
    let fonts := dir / "fonts"
    IO.FS.createDirAll fonts
    for file in ["SourceCodePro-Regular.otf", "FiraMath-Regular.otf",
        "OpenSans-Regular.ttf"] do
      IO.FS.writeBinFile (fonts / file) (← IO.FS.readBinFile (corpus / file))
    for (name, decl, valid, accepted) in [
        ("bare-valid", "", true, true), ("bare-invalid", "", false, false),
        ("mono-valid", "\\setmonofont{Source Code Pro}", true, true),
        ("mono-invalid", "\\setmonofont{Source Code Pro}", false, true),
        ("math-valid", "\\setmathfont{Fira Math}", true, true),
        ("math-invalid", "\\setmathfont{Fira Math}", false, true)] do
      let source := dir / (name ++ ".tex")
      let output := dir / name
      IO.FS.writeFile source (String.intercalate "\n" [
        "\\documentclass{article}", "\\usepackage{fontspec}", "\\fonts{dir=\"fonts\"}", decl,
        "\\output{formats=pdf,html, fonts=embedded}",
        "\\begin{document}", if decl.isEmpty then "Plain" else "Plain $x$",
        "\\end{document}"])
      let result ← IO.Process.output {
        cmd := binary.toString
        args := #[source.toString, "-o", output.toString ++ "/", "--porcelain"]
        cwd := some dir
        env := #[("LEANTEX_FONT", some ((fonts /
            (if valid then "SourceCodePro-Regular.otf" else "missing.ttf")).toString)),
          ("LEANTEX_FONT_PATH", none), ("HOME", some (dir / "home").toString),
          ("XDG_CACHE_HOME", some (dir / "cache").toString),
          ("PATH", some (dir / "no-tools").toString)] }
      let t := fun why ok => check ref s!"font override {name}: {why}" ok
      t s!"exit follows declaration boundary ({result.exitCode}): {result.stdout}{result.stderr}"
        ((result.exitCode == 0) == accepted)
      unless accepted && result.exitCode == 0 do continue
      let html ← IO.FS.readFile (output / (name ++ ".html"))
      let some resource := htmlSlotSource html "body" |
        t "HTML has a body program" false
        continue
      let (_, program) ← htmlDataDecode resource
      t "HTML body uses the override only for an undeclared document"
        (postIsFixedPitch program == some decl.isEmpty)
      unless decl.isEmpty do
        t "formulas retain a math face in both outputs"
          (!hasStr result.stdout "W0003" && !hasStr result.stderr "W0003")
        let some mathResource := htmlSlotSource html "math" |
          t "HTML embeds a math face" false
          continue
        let (_, mathProgram) ← htmlDataDecode mathResource
        t "HTML math face carries an OpenType MATH table"
          (match Font.parse mathProgram with
           | .ok f => f.math.isSome
           | .error _ => false)
      let pdf ← IO.FS.readBinFile (output / (name ++ ".pdf"))
      let .ok runs := pdfFaceRuns pdf |
        t "PDF font programs are readable" false
        continue
      t "PDF body uses the override only for an undeclared document"
        ((faceSetting runs "Plain").bind (fun (_, _, pitch) => pitch) == some decl.isEmpty)

end Tests
