module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! algorithm2e and algorithmic read as their packages read them, judged on the shipped page and the
HTML tree: a document's keyword over the package's, and an opening option past a line end. -/

/-- A source's shipped lines, each trimmed; its HTML algorithm lists, each whether it is numbered
and its items' shown text; and its diagnostics. -/
def algArtifacts (fonts : Font.FontSet) (src : String) :
    Array String × Array (Bool × Array String) × Array Diag :=
  let (doc, ds) := elabStr src
  let lines := (censusOf (coveredColorsOf doc) (layoutOf fonts doc)).flatMap fun p =>
    p.lines.map (·.text.trimAscii.toString)
  let items (kids : Array Html.Node) : Array String :=
    (elemNodesList (· == "li") #[] kids.toList).filterMap fun
      | .elem _ _ k => some (shownTextList "" k.toList).trimAscii.toString
      | _ => none
  let lists := (elemNodesList (· == "ol") #[] (docNodesOf doc).toList).filterMap fun
    | .elem _ attrs kids =>
      let cls := ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " "
      if cls.contains "algorithm" then some (cls.contains "numbered", items kids) else none
    | _ => none
  (lines, lists, ds)

def algorithmReadChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let a2e (pre body : String) : String := dvDoc ("\\usepackage[ruled]{algorithm2e}\n" ++ pre) body
  let shipsLines (src : String) (want : Array (Array String)) : Bool :=
    let (lines, lists, _) := algArtifacts fonts src
    want.all (·.all lines.contains) && lists.map (·.2) == want
  t "algorithm2e: the preamble's keywords replace the package's, each io line its own and unended"
    (shipsLines (a2e ("\\SetKwInput{KwIn}{Data}\n\\SetKwInput{KwOut}{Yield}\n" ++
        "\\SetKw{KwRet}{give}\n\\SetKwInOut{Input}{Given}\n")
      ("\\begin{algorithm}\n\\KwIn{alpha words}\n\\KwOut{bravo words}\n\\Input{charlie words}\n" ++
        "delta words\\;\n\\KwRet{echo words}\\;\n\\end{algorithm}"))
      #[#["Data: alpha words", "Yield: bravo words", "Given: charlie words", "delta words;",
        "give echo words;"]])
  t "algorithm2e: an algorithm's own keywords replace the package's there and nowhere after"
    (shipsLines (a2e ""
      ("\\begin{algorithm}\n\\SetKwInput{KwData}{Facts}\n\\SetKw{Return}{hand back}\n" ++
        "\\KwData{foxtrot words}\n\\Return{golf words}\\;\n\\end{algorithm}\n" ++
        "\\begin{algorithm}\n\\KwData{hotel words}\n\\Return{india words}\\;\n\\end{algorithm}"))
      #[#["Facts: foxtrot words", "hand back golf words;"],
        #["Data: hotel words", "return india words;"]])
  let acx (opening : String) : String := dvDoc "\\usepackage{algpseudocode}\n"
    ("\\begin{algorithmic}" ++ opening ++
      "\n\\State alpha words\n\\State bravo words\n\\end{algorithmic}")
  let numbered (opening : String) : Bool :=
    let (lines, lists, _) := algArtifacts fonts (acx opening)
    lines.contains "1 alpha words;" && lines.contains "2 bravo words;" &&
      !lines.any (hasStr · "[") && lists == #[(true, #["alpha words;", "bravo words;"])]
  let unnumbered (opening : String) : Bool :=
    let (lines, lists, _) := algArtifacts fonts (acx opening)
    lines.contains "alpha words;" && !lines.any (hasStr · "1 alpha") &&
      lists.all (!·.1)
  let raises (opening code : String) : Bool :=
    let (_, _, ds) := algArtifacts fonts (acx opening)
    ds.any (·.code == code)
  t "algorithmic: an option past a line end or a comment line numbers, one past a blank line is text"
    (numbered "\n[1]" && numbered "\n% an invented remark\n[1]" &&
      unnumbered "\n\n[1]" && (algArtifacts fonts (acx "\n\n[1]")).1.any (hasStr · "[1]"))
  t "algorithmic: a braced step reads as its value, and step 0 numbers no line"
    (numbered "[{1}]" && !raises "[{1}]" "N0102" && unnumbered "[0]" && unnumbered "[{0}]" &&
      !raises "[0]" "N0102" && !raises "[{0}]" "N0102")
  t "algorithmic: a bracket past a line end that holds no step is still the option, numbering none"
    (unnumbered "\n[an invented note]" &&
      !(algArtifacts fonts (acx "\n[an invented note]")).1.any (hasStr · "invented note"))
  t "algorithmic: a step the engine does not model is named, its spelling the detail"
    ((algArtifacts fonts (acx "[{2}]")).2.2.any fun d =>
      d.code == "N0102" && d.detail == some "[{2}]" && !hasStr d.message "[{2}]")
  t "algorithmic: a step is the count only as written, braces around the whole of it aside"
    (numbered "[1]" && numbered "[{1}]" && unnumbered "[ {1} ]" && unnumbered "[1 ]" &&
      unnumbered "[ 1]" && unnumbered "[01]" && unnumbered "[{ 1}]")
  t "algorithm2e: a placement past a line end is the float's option, never a line"
    (shipsLines (a2e "" ("Before words.\n\\begin{algorithm}\n[H]\n\\caption{An invented caption}\n" ++
        "alpha words\\;\n\\end{algorithm}\nAfter words."))
      #[#["alpha words;"]])
  let bracketLine := a2e "" "\\begin{algorithm}\n[alpha, bravo] words\\;\n\\end{algorithm}"
  t "algorithm2e: a bracket past a line end that names no placement is the first line's text"
    (shipsLines bracketLine #[#["[alpha, bravo] words;"]] &&
      !(algArtifacts fonts bracketLine).2.2.any (·.code == "N0102"))
  let fnGlobal := a2e ""
    ("\\begin{algorithm}\n\\SetKwFunction{FnProbe}{Zulu}\n\\FnProbe{echo}\\;\n\\end{algorithm}\n" ++
      "\\begin{algorithm}\n\\FnProbe{foxtrot}\\;\n\\end{algorithm}")
  t "algorithm2e: a function keyword holds past its algorithm, as the package's \\gdef does"
    (let (lines, lists, ds) := algArtifacts fonts fnGlobal
     lists.map (·.2) == #[#["Zulu(echo);"], #["Zulu(foxtrot);"]] &&
       lines.any (hasStr · "(foxtrot);") && !ds.any (·.code == "W0301"))
  let labelled := a2e "\\SetKwInput{KwIn}{∀ alpha}\n" "\\begin{algorithm}\n\\KwIn{bravo words}\n\\end{algorithm}"
  t "algorithm2e: a declared io word's characters reach the font census"
    ((Layout.docScalars (elabStr labelled).1).contains '∀')
  let floatLines (src : String) : Array String := (algArtifacts fonts src).1
  let floatNotes (src : String) : Bool :=
    (algArtifacts fonts src).2.2.any fun d => d.code == "N0102" && hasStr d.message "[placement]"
  let figure := dvDoc "" ("\\begin{figure}\n[ht]\nalpha words\n\\caption{An invented caption}\n" ++
    "\\end{figure}\n\\begin{table}\n% an invented remark\n[!b]\nbravo words\n" ++
    "\\caption{Another invented caption}\n\\end{table}")
  t "floats: a placement past a line end or a comment line is the float's option, never text"
    (!(floatLines figure).any (fun l => hasStr l "[ht]" || hasStr l "[!b]") &&
      (floatLines figure).any (hasStr · "alpha words") && floatNotes figure)
  let twice := dvDoc "" "\\begin{figure}[h][t]\ncharlie words\n\\caption{An invented caption}\n\\end{figure}"
  t "floats: a float takes one placement, a second bracket its text"
    ((floatLines twice).any (hasStr · "[t] charlie words"))
  let centred := dvDoc "" ("\\begin{figure}\n\\begin{center}\n[ht] alpha words\n\\end{center}\n" ++
    "\\caption{An invented caption}\n\\end{figure}\n\\begin{figure}\\begin{center}[b] bravo words\n" ++
    "\\end{center}\n\\caption{Another invented caption}\n\\end{figure}\n\\begin{table}\n" ++
    "\\begin{center}\n[] charlie words\n\\end{center}\n\\caption{A third invented caption}\n" ++
    "\\end{table}")
  t "floats: a bracket opening a spliced centre is the centre's text, never the float's placement"
    (let ls := floatLines centred
     let html := shownTextList "" (docNodesOf (elabStr centred).1).toList
     (["[ht] alpha words", "[b] bravo words", "[] charlie words"].all fun w =>
       ls.any (hasStr · w) && hasStr html w) && !floatNotes centred)
  let spaced := dvDoc "" "\\begin{figure}\n[h t]\necho words\n\\caption{An invented caption}\n\\end{figure}"
  t "floats: a placement's letters may stand apart, as LaTeX reads them"
    (!(floatLines spaced).any (hasStr · "[h t]") && (floatLines spaced).any (hasStr · "echo words"))
  let bare := a2e "\\SetKwInOut{Input}{Given}\n"
    "\\begin{algorithm}\n\\Input G\n\\KwIn H\nalpha words\\;\n\\end{algorithm}"
  t "algorithm2e: an io keyword without braces reads one token as TeX reads its argument"
    (let (ls, lists, ds) := algArtifacts fonts bare
     ls.contains "Given: G" && ls.contains "Input: H" &&
       lists.map (·.2) == #[#["Given: G", "Input: H", "alpha words;"]] && ds.all (·.code != "E0304"))
  let deck := "\\documentclass{beamer}\n\\begin{document}\n" ++
    ("\\begin{frame}\n[t]\n\\frametitle{An invented title}\nAlpha words.\n" ++
    "\\end{frame}\n\\begin{frame}\n\\begin{columns}\n[T]\n\\column{0.5\\textwidth} Bravo words.\n" ++
    "\\column{0.5\\textwidth} Charlie words.\n\\end{columns}\n\\begin{minipage}\n[t]{0.4\\textwidth}\n" ++
    "Delta words.\n\\end{minipage}\n\\end{frame}") ++ "\n\\end{document}"
  t "frames, columns and boxes: an option past a line end is theirs, never ink"
    (let (ls, _, ds) := algArtifacts fonts deck
     !ls.any (fun l => hasStr l "[t]" || hasStr l "[T]") && ls.any (hasStr · "Delta words") &&
       ds.all (·.code != "E0304"))
  let empty := a2e "" "\\begin{algorithm}\n[]\ndelta words\\;\n\\end{algorithm}"
  t "floats: an empty placement past a line end is the float's option"
    (shipsLines empty #[#["delta words;"]])
  let thm := dvDoc "\\newtheorem{theorem}{Theorem}\n"
    ("\\begin{theorem}\n[An invented note]\nAlpha words.\n\\end{theorem}\n" ++
      "\\begin{theorem}\n% an invented remark\n[Another note]\nBravo words.\n\\end{theorem}\n" ++
      "\\begin{theorem}\n\n[Kept text] Charlie words.\n\\end{theorem}")
  t "theorems: a note past a line end or a comment line is the note, one past a blank line text"
    (let ls := floatLines thm
     ls.any (hasStr · "(An invented note)") && ls.any (hasStr · "(Another note)") &&
       !ls.any (hasStr · "[An invented note]") && ls.any (hasStr · "[Kept text] Charlie words"))
  let listed := dvDoc "\\usepackage{enumitem}\n"
    "\\begin{itemize}\n[label=--]\n\\item Delta words.\n\\end{itemize}"
  t "lists: options past a line end are the list's, never content before its first item"
    (let (ls, _, ds) := algArtifacts fonts listed
     ls.any (hasStr · "Delta words") && !ls.any (hasStr · "label") && !ds.any (·.code == "E0310"))

/-- A declared io word the slots' faces lack sets from the face the document ships for it, in both
artifacts, through the driver's own fallback assembly. -/
def algLabelFaceChecks (ref : IO.Ref (List String))
    (binary : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath binary
  let corpus ← IO.FS.realPath testFonts
  let sans ← match Font.parse (← IO.FS.readBinFile (corpus / "OpenSans-Regular.ttf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"label faces: Open Sans unparsable: {e}")
  let code ← match Font.parse (← IO.FS.readBinFile (corpus / "SourceCodePro-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"label faces: Source Code Pro unparsable: {e}")
  t "label faces: coverage premise, only the code face has U+2200"
    ((sans.gid '∀').isNone && (code.gid '∀').isSome)
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "fonts")
    for f in ["OpenSans-Regular.ttf", "OpenSans-Bold.ttf", "OpenSans-Italic.ttf",
        "OpenSans-BoldItalic.ttf", "SourceCodePro-Regular.otf"] do
      IO.FS.writeBinFile (dir / "fonts" / f) (← IO.FS.readBinFile (corpus / f))
    IO.FS.writeFile (dir / "doc.tex") ("\\documentclass{article}\n" ++
      "\\fonts{ dir = \"fonts\", body = \"Open Sans\", sans = \"Open Sans\", mono = \"Open Sans\" }\n" ++
      "\\usepackage[ruled]{algorithm2e}\n\\SetKwInput{KwIn}{∀ alpha}\n\\begin{document}\n" ++
      "\\begin{algorithm}\n\\KwIn{bravo words}\ncharlie words\\;\n\\end{algorithm}\n\\end{document}\n")
    for ext in ["pdf", "html"] do
      let out := dir / s!"doc.{ext}"
      let r ← IO.Process.output {
        cmd := binary.toString
        args := #["build", (dir / "doc.tex").toString, "-o", out.toString, "--porcelain"]
        env := sealedRunEnv dir }
      let shipped ← out.pathExists
      t s!"label faces: the {ext} ships, the label's glyph set from the face holding it ({r.exitCode})"
        (r.exitCode == 0 && shipped && !hasStr r.stdout "E0405")
      if ext == "pdf" then
        t "label faces: the label's replaced glyph is reported at its use"
          ((r.stdout.splitOn "\n").any fun l =>
            hasStr l "\"code\":\"W0009\"" && hasStr l "U+2200" && hasStr l "\"line\":7")
      if ext == "html" && shipped then
        let page ← IO.FS.readFile out
        t "label faces: the page sets the declared word and ships a fallback face in the body's stack"
          (let stack := ((page.splitOn "--font-body: \"ltx-body\"").getD 1 "").takeWhile (· != ';')
           hasStr page "∀ alpha:" && hasStr page "font-family: \"ltx-fb" &&
             hasStr stack.toString "ltx-fb")
