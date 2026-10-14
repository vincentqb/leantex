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
  t "algorithmic: a step the engine does not model is named as written"
    ((algArtifacts fonts (acx "[{2}]")).2.2.any fun d =>
      d.code == "N0102" && hasStr d.message "'[{2}]'")
  t "algorithm2e: a placement past a line end is the float's option, never a line"
    (shipsLines (a2e "" ("Before words.\n\\begin{algorithm}\n[H]\n\\caption{An invented caption}\n" ++
        "alpha words\\;\n\\end{algorithm}\nAfter words."))
      #[#["alpha words;"]])
  let bracketLine := a2e "" "\\begin{algorithm}\n[alpha, bravo] words\\;\n\\end{algorithm}"
  t "algorithm2e: a bracket past a line end that names no placement is the first line's text"
    (shipsLines bracketLine #[#["[alpha, bravo] words;"]] &&
      !(algArtifacts fonts bracketLine).2.2.any (·.code == "N0102"))
