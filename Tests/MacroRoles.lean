module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

private structure MacroRoleHtml where
  glyphs : Array (Char × List String) := #[]
  roles : Array (String × List String × String) := #[]
  paragraphs : Array String := #[]
  deriving BEq, Repr

mutual

private def macroRoleHtmlOne (watched parents : List String) (acc : MacroRoleHtml) :
    Html.Node → MacroRoleHtml
  | .text s =>
    { acc with glyphs := s.toList.foldl (fun xs c =>
        if c.isWhitespace then xs else xs.push (c, parents)) acc.glyphs }
  | .style _ | .script _ _ => acc
  | .elem tag attrs kids =>
    let names := attrs.toList.flatMap fun (key, value) =>
      if key == "class" then
        (value.splitOn " ").filterMap fun cls =>
          watched.find? fun name => cls == HtmlDoc.roleClass name
      else []
    let text := shownTextList "" kids.toList
    let acc := { acc with
      roles := names.foldl (fun xs name => xs.push (name, parents, text)) acc.roles
      paragraphs := if tag == "p" then acc.paragraphs.push text else acc.paragraphs }
    if attrs.any (fun (key, _) => key == "hidden") then acc
    else macroRoleHtmlList watched (parents ++ names) acc kids.toList

private def macroRoleHtmlList (watched parents : List String) (acc : MacroRoleHtml) :
    List Html.Node → MacroRoleHtml
  | [] => acc
  | node :: rest =>
    macroRoleHtmlList watched parents (macroRoleHtmlOne watched parents acc node) rest

end

private structure MacroRoleCase where
  label : String
  pre : String
  body : String
  control : String
  owned : Array (String × List String)
  /-- One occurrence can straddle a declaration and need two emitted
  wrappers. Simple nested/adjacent calls have exact, equal bounds. -/
  counts : Array (String × Nat × Nat)

/-- Executing a parameterized macro preserves its semantic name: the typed
HTML still exposes its class, and its declared rhythm reaches the shipped
lines exactly as for a native definition. That annotation is not a TeX
group or an argument boundary; the last primitive in replacement text may
still read the following source. All sources are invented. -/
def macroRoleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let classes (source : String) : Array String :=
    let (_, tree, _) := HtmlDoc.emitTree {} (elabStr source).1
    tree.flatMap (attrValuesOf (fun _ => true) "class")
  let lines (source : String) : Array (String × Dim.Sp) :=
    (bodyLines (layoutOf fonts (elabStr source).1)).map fun line => (lineText line, line.y)
  for (label, definition, call) in #[
      ("newcommand", "\\newcommand\\entryprobe[1]{#1\\par}", "\\entryprobe{follow}"),
      ("providecommand", "\\providecommand\\entryprobe[1]{#1\\par}", "\\entryprobe{follow}"),
      ("def", "\\def\\entryprobe#1{#1\\par}", "\\entryprobe{follow}"),
      ("optional", "\\newcommand\\entryprobe[1][follow]{#1\\par}", "\\entryprobe")] do
    let source := dvDoc (definition ++ "\\style{entryprobe}{before = 24pt}")
      ("lead\n\n" ++ call)
    let native := dvDoc
      "\\define \\entryprobe(a: content){\\a\\par}\\style{entryprobe}{before = 24pt}"
      "lead\n\n\\entryprobe{follow}"
    let bare := dvDoc definition ("lead\n\n" ++ call)
    t s!"macro roles {label}: style accepted" ((elabStr source).2.all (·.severity == .note))
    t s!"macro roles {label}: typed HTML keeps the name"
      ((classes source).any fun cls => (cls.splitOn " ").contains "u-entryprobe")
    t s!"macro roles {label}: shipped rhythm matches native definition" (lines source == lines native)
    t s!"macro roles {label}: declared rhythm changes the page" (lines source != lines bare)
  for (label, definition, call) in #[
      ("inline", "\\newcommand\\markprobe[1]{#1}", "\\markprobe{Marked} Tail"),
      ("conditional", "\\newif\\ifroleprobe\\newcommand\\markprobe[1]{\\roleprobetrue#1}",
        "\\markprobe{Marked}\\ifroleprobe{} Tail\\else Wrong\\fi")] do
    let source := dvDoc definition call
    t s!"macro roles {label}: typed HTML keeps the name"
      ((classes source).any fun cls => (cls.splitOn " ").contains "u-markprobe")
    sourceTextChecks ref fonts s!"macro roles {label}" source (dvDoc "" "Marked Tail")
  for (label, definition, body, control) in #[
      ("following argument", "\\newcommand\\bridgeprobe[1]{\\textbf}",
        "\\bridgeprobe{}{After}", "\\textbf{After}"),
      ("following declaration", "\\def\\bridgeprobe#1{\\bfseries}",
        "\\bridgeprobe{}After", "\\bfseries After"),
      ("word remainder", "\\def\\bridgeprobe#1{#1}",
        "\\bridgeprobe AB Tail", "AB Tail")] do
    let source := dvDoc definition body
    let expected := dvDoc "" control
    sourceTextChecks ref fonts s!"macro roles {label}" source expected
    t s!"macro roles {label}: shipped glyphs keep their faces"
      (shippedBodyGlyphs (layoutOf fonts (elabStr source).1) ==
        shippedBodyGlyphs (layoutOf fonts (elabStr expected).1))

  let some fs ← serifFacesSet
    | t "macro roles: shipped serif faces load" false
      return
  let word := "\\newcommand\\wordrole[1]{#1}"
  let cases : Array MacroRoleCase := #[
    { label := "block primitive consumes outside group"
      pre := "\\newcommand\\blockprobe[1]{#1\\par\\textbf}"
      body := "\\blockprobe{A}{B} Tail", control := "A\\par\\textbf{B} Tail"
      owned := #[("AB", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "mixed paragraph crosses block origin"
      pre := "\\newcommand\\blockprobe[1]{#1\\par Z}"
      body := "Lead\\blockprobe{A}Tail", control := "LeadA\\par ZTail"
      owned := #[("Lead", []), ("AZ", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "palette marker cannot spend a mixed paragraph skip"
      pre := "\\newcommand\\blockprobe[1]{#1\\pagecolor{white}\\par Z}"
      body := "Lead\\blockprobe{A}Tail", control := "LeadA\\pagecolor{white}\\par ZTail"
      owned := #[("Lead", []), ("AZ", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "block tail shares ordinary paragraph"
      pre := "\\newcommand\\blockprobe[1]{#1\\par Z}"
      body := "\\blockprobe{A}Tail", control := "A\\par ZTail"
      owned := #[("AZ", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "block pause continuation keeps outside Tail unowned"
      pre := "\\newcommand\\blockprobe[1]{#1\\par\\pause X}"
      body := "\\blockprobe{A} Tail", control := "A\\par\\pause X Tail"
      owned := #[("AX", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "block open overlay continuation keeps outside Tail unowned"
      pre := "\\newcommand\\blockprobe[1]{#1\\par\\onslide<2-> X}"
      body := "\\blockprobe{A} Tail", control := "A\\par\\onslide<2-> X Tail"
      owned := #[("AX", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 2, 2)] },
    { label := "adjacent block calls share one mixed paragraph"
      pre := "\\newcommand\\blockprobe[1]{#1\\par X}"
      body := "\\blockprobe{A}\\blockprobe{B}Tail", control := "A\\par XB\\par XTail"
      owned := #[("AXBX", ["blockprobe"]), ("Tail", [])]
      counts := #[("blockprobe", 4, 4)] },
    { label := "nested block tails retain both owners"
      pre := "\\newcommand\\innerrole[1]{#1\\par I}" ++
        "\\newcommand\\outerrole[1]{O\\par\\innerrole{#1}E}"
      body := "\\outerrole{X}Tail", control := "O\\par X\\par IETail"
      owned := #[("O", ["outerrole"]), ("XI", ["outerrole", "innerrole"]),
        ("E", ["outerrole"]), ("Tail", [])]
      counts := #[("outerrole", 2, 2), ("innerrole", 2, 2)] },
    { label := "empty pending group cannot skip a following heading owner"
      pre := "\\newcommand\\headrole[1]{\\section*{#1}}"
      body := "Lead\\par {}\\headrole{Head}Tail", control := "Lead\\par {}\\section*{Head}Tail"
      owned := #[("Lead", []), ("Head", ["headrole"]), ("Tail", [])]
      counts := #[("headrole", 1, 1)] },
    { label := "consumer and argument have different origins"
      pre := "\\newcommand\\makerole[1]{\\textbf}" ++
        "\\newcommand\\argrole[1]{{\\textit{#1}}}"
      body := "\\makerole{}\\argrole{X}Tail", control := "\\textbf{\\textit{X}}Tail"
      owned := #[("X", ["makerole", "argrole"]), ("Tail", [])]
      counts := #[("makerole", 1, 1), ("argrole", 1, 1)] },
    { label := "font consumes tagged bare word"
      pre := word
      body := "\\textbf\\wordrole{X} Tail", control := "\\textbf{X} Tail"
      owned := #[("X", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 1, 1)] },
    { label := "underline consumes tagged bare word"
      pre := word
      body := "\\underline\\wordrole{X} Tail", control := "\\underline{X} Tail"
      owned := #[("X", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 1, 1)] },
    { label := "native parameter consumes tagged bare word"
      pre := word ++ "\\define \\readprobe(a: content){\\a}"
      body := "\\readprobe\\wordrole{X} Tail", control := "\\readprobe{X} Tail"
      owned := #[("X", ["readprobe", "wordrole"]), ("Tail", [])]
      counts := #[("readprobe", 1, 1), ("wordrole", 1, 1)] },
    { label := "native text parameter consumes tagged group"
      pre := "\\newcommand\\wordrole[1]{{#1}}\\define \\readtext(a: text){\\a}"
      body := "\\readtext\\wordrole{X} Tail", control := "\\readtext{X} Tail"
      owned := #[("X", ["readtext", "wordrole"]), ("Tail", [])]
      counts := #[("readtext", 1, 1), ("wordrole", 1, 1)] },
    { label := "native text parameter consumes tagged bare word"
      pre := word ++ "\\define \\readtext(a: text){\\a}"
      body := "\\readtext\\wordrole{X} Tail", control := "\\readtext{X} Tail"
      owned := #[("X", ["readtext", "wordrole"]), ("Tail", [])]
      counts := #[("readtext", 1, 1), ("wordrole", 1, 1)] },
    { label := "native text parameter consumes tagged text inside source group"
      pre := word ++ "\\define \\readtext(a: text){\\a}"
      body := "\\readtext{\\wordrole{X}} Tail", control := "\\readtext{X} Tail"
      owned := #[("X", ["readtext", "wordrole"]), ("Tail", [])]
      counts := #[("readtext", 1, 1), ("wordrole", 1, 1)] },
    { label := "group spaces still trim at paragraph edges"
      pre := "\\newcommand\\padrole[1]{{ #1 }}"
      body := "\\padrole{X}", control := "{ X }"
      owned := #[("X", ["padrole"])]
      counts := #[("padrole", 1, 1)] },
    { label := "smart punctuation inside macro"
      pre := word
      body := "\\wordrole{a---b} Tail", control := "a---b Tail"
      owned := #[("a—b", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 1, 1)] },
    { label := "literal font retains macro punctuation"
      pre := word
      body := "\\texttt{\\wordrole{a---b}} Tail", control := "\\texttt{a---b} Tail"
      owned := #[("a---b", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 1, 1)] },
    { label := "primitive legitimately owns following argument"
      pre := "\\newcommand\\bridgeprobe[1]{L\\textbf}"
      body := "\\bridgeprobe{}{X} Tail", control := "L\\textbf{X} Tail"
      owned := #[("LX", ["bridgeprobe"]), ("Tail", [])]
      counts := #[("bridgeprobe", 1, 1)] },
    { label := "nested occurrences of the same spelling"
      pre := "\\newcommand\\nestprobe[1]{(#1)}"
      body := "\\nestprobe{\\nestprobe{X}}Tail", control := "((X))Tail"
      owned := #[("(", ["nestprobe"]), ("(X)", ["nestprobe", "nestprobe"]),
        (")", ["nestprobe"]), ("Tail", [])]
      counts := #[("nestprobe", 2, 2)] },
    { label := "terminal call through a later binding"
      pre := "\\newcommand\\outerrole[1]{O\\innerrole{#1}E}" ++
        "\\newcommand\\innerrole[1]{(#1)}"
      body := "\\outerrole{X}Tail", control := "O(X)ETail"
      owned := #[("O", ["outerrole"]), ("(X)", ["outerrole", "innerrole"]),
        ("E", ["outerrole"]), ("Tail", [])]
      counts := #[("outerrole", 1, 1), ("innerrole", 1, 1)] },
    { label := "terminal copied call through older text"
      pre := "\\newcommand\\outerrole[1]{O\\innerrole{#1}E}" ++
        "\\newcommand\\laterrole[1]{(#1)}\\let\\innerrole\\laterrole"
      body := "\\outerrole{X}Tail", control := "O(X)ETail"
      owned := #[("O", ["outerrole"]), ("(X)", ["outerrole", "innerrole"]),
        ("E", ["outerrole"]), ("Tail", [])]
      counts := #[("outerrole", 1, 1), ("innerrole", 1, 1)] },
    { label := "terminal discarded argument does not execute"
      pre := "\\def\\flagrole{F}" ++
        "\\newcommand\\outerrole[1]{O\\innerrole{\\gdef\\flagrole{T}#1}E}" ++
        "\\newcommand\\innerrole[1]{K}"
      body := "\\outerrole{X}\\flagrole{} Tail", control := "OKEF Tail"
      owned := #[("O", ["outerrole"]), ("K", ["outerrole", "innerrole"]),
        ("E", ["outerrole"]), ("FTail", [])]
      counts := #[("outerrole", 1, 1), ("innerrole", 1, 1)] },
    { label := "adjacent occurrences stay distinct"
      pre := word
      body := "\\wordrole{A}\\wordrole{B}Tail", control := "ABTail"
      owned := #[("AB", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 2, 2)] },
    { label := "spaces between adjacent occurrences"
      pre := word
      body := "Lead \\wordrole{A} \\wordrole{B} Tail", control := "Lead A B Tail"
      owned := #[("Lead", []), ("AB", ["wordrole"]), ("Tail", [])]
      counts := #[("wordrole", 2, 2)] },
    { label := "nested and adjacent different spellings"
      pre := "\\newcommand\\innerrole[1]{#1}" ++
        "\\newcommand\\outerrole[1]{O\\innerrole{#1}E}"
      body := "\\outerrole{X}\\innerrole{Y}Tail", control := "OXEYTail"
      owned := #[("O", ["outerrole"]), ("X", ["outerrole", "innerrole"]),
        ("E", ["outerrole"]), ("Y", ["innerrole"]), ("Tail", [])]
      counts := #[("outerrole", 1, 1), ("innerrole", 2, 2)] },
    { label := "unconsumed word remainder has no role"
      pre := "\\def\\wordrole#1{#1}"
      body := "\\wordrole AB Tail", control := "AB Tail"
      owned := #[("A", ["wordrole"]), ("BTail", [])]
      counts := #[("wordrole", 1, 1)] },
    { label := "empty expansion adds no role or separator"
      pre := "\\newcommand\\emptyrole[1]{}"
      body := "A\\emptyrole{}B Tail", control := "AB Tail"
      owned := #[("ABTail", [])]
      counts := #[("emptyrole", 0, 0)] },
    { label := "space-only expansion keeps its space without a token"
      pre := "\\newcommand\\spacerole[1]{ }"
      body := "A\\spacerole{}B Tail", control := "A B Tail"
      owned := #[("ABTail", [])]
      counts := #[("spacerole", 0, 0)] },
    { label := "dropped leading space does not attach a role to Tail"
      pre := "\\newcommand\\spacerole[1]{ }"
      body := "\\spacerole{}Tail", control := "Tail"
      owned := #[("Tail", [])]
      counts := #[("spacerole", 0, 0)] }]
  let declarations : Array MacroRoleCase :=
    #["\\bfseries", "\\color{blue}", "\\large"].flatMap fun decl =>
      #[{ label := s!"declaration continuation {decl}"
          pre := "\\newcommand\\bridgeprobe[1]{L" ++ decl ++ " X}"
          body := "\\bridgeprobe{} Tail", control := "L" ++ decl ++ " X Tail"
          owned := #[("LX", ["bridgeprobe"]), ("Tail", [])]
          counts := #[("bridgeprobe", 1, 2)] },
        { label := s!"declaration group boundary {decl}"
          pre := "\\newcommand\\bridgeprobe[1]{L" ++ decl ++ " X}"
          body := "{\\bridgeprobe{} Tail} After"
          control := "{L" ++ decl ++ " X Tail} After"
          owned := #[("LX", ["bridgeprobe"]), ("TailAfter", [])]
          counts := #[("bridgeprobe", 1, 2)] },
        { label := s!"declaration followed by another origin {decl}"
          pre := "\\newcommand\\bridgeprobe[1]{L" ++ decl ++ " X}" ++ word
          body := "\\bridgeprobe{} \\wordrole{Y} Tail"
          control := "L" ++ decl ++ " X Y Tail"
          owned := #[("LX", ["bridgeprobe"]), ("Y", ["wordrole"]), ("Tail", [])]
          counts := #[("bridgeprobe", 1, 2), ("wordrole", 1, 1)] },
        { label := s!"block declaration continuation {decl}"
          pre := "\\newcommand\\blockprobe[1]{#1\\par" ++ decl ++ " X}"
          body := "\\blockprobe{A} Tail", control := "A\\par" ++ decl ++ " X Tail"
          owned := #[("AX", ["blockprobe"]), ("Tail", [])]
          counts := #[("blockprobe", 2, 2)] }]
  let allCases := cases ++ declarations
  for c in allCases do
    let source := dvDoc c.pre c.body
    let control := dvDoc c.pre c.control
    let (doc, ds) := elabStr source
    let (expectedDoc, expectedDs) := elabStr control
    let out := layoutOf fs doc
    let expectedOut := layoutOf fs expectedDoc
    let (_, tree, hds) := HtmlDoc.emitTree {} doc
    let (_, expectedTree, expectedHds) := HtmlDoc.emitTree {} expectedDoc
    let watched := c.counts.toList.map (·.1)
    let html := macroRoleHtmlList watched [] {} tree.toList
    let expectedHtml := macroRoleHtmlList watched [] {} expectedTree.toList
    let label := "macro roles " ++ c.label
    t (label ++ ": literal control has no loss")
      ((expectedDs ++ expectedOut.diags ++ expectedHds).all (·.severity == .note))
    t (label ++ ": no loss") ((ds ++ out.diags ++ hds).all (·.severity == .note))
    t (label ++ ": visible HTML including every space")
      (shownTextList "" tree.toList == shownTextList "" expectedTree.toList)
    t (label ++ ": paragraph boundaries and spaces") (html.paragraphs == expectedHtml.paragraphs)
    for key in #["data-step", "data-step-last", "data-steps"] do
      t (label ++ s!": typed HTML keeps {key}")
        (tree.flatMap (attrValuesOf (fun _ => true) key) ==
          expectedTree.flatMap (attrValuesOf (fun _ => true) key))
    t (label ++ ": shipped page count") (out.pages.size == expectedOut.pages.size)
    t (label ++ ": shipped lines including spaces")
      (out.pages.map (fun p => (p.lines.filter (!·.furniture)).map lineInk) ==
        expectedOut.pages.map (fun p => (p.lines.filter (!·.furniture)).map lineInk))
    t (label ++ ": exact glyph positions and paint")
      (shippedBodyGlyphs out == shippedBodyGlyphs expectedOut)
    -- Space has no provenance. Its exact presence is checked above; the
    -- positioned characters must have exactly these owners, in this order.
    let owned := c.owned.flatMap fun (text, parents) =>
      (text.toList.filter (!·.isWhitespace)).toArray.map (·, parents)
    t (label ++ ": exact typed HTML role ancestry") (html.glyphs == owned)
    for (name, lo, hi) in c.counts do
      let count := (html.roles.filter (·.1 == name)).size
      t (label ++ s!": {name} wrapper count in [{lo}, {hi}]") (lo ≤ count && count ≤ hi)

  -- A terminal substitution needs no recursive expansion. A later binding
  -- that still needs conditional execution remains outside the serial
  -- bound: its genuinely lost state change must still be named.
  let effectful := dvDoc
    ("\\newif\\ifroleprobe\\newcommand\\outerrole[1]{O\\innerrole{#1}E}" ++
      "\\newcommand\\innerrole[1]{\\roleprobetrue#1}")
    "\\outerrole{X}\\ifroleprobe T\\else F\\fi"
  let (effectDoc, effectDs) := elabStr effectful
  let (effectControl, _) := elabStr (dvDoc "" "OXET")
  let (_, effectTree, _) := HtmlDoc.emitTree {} effectDoc
  let (_, effectControlTree, _) := HtmlDoc.emitTree {} effectControl
  t "macro roles nonterminal later binding: lost execution remains W0104"
    (effectDs.any fun d =>
      d.code == "W0104" && d.subject == some "cond:unexpanded:innerrole")
  t "macro roles nonterminal later binding: the control ships the set flag"
    (shownTextList "" effectControlTree.toList == "OXET")
  t "macro roles nonterminal later binding: the warning names a real artifact difference"
    (shownTextList "" effectTree.toList == "OXEF" &&
      shippedBodyGlyphs (layoutOf fs effectDoc) !=
        shippedBodyGlyphs (layoutOf fs effectControl))

  -- Metadata is transparent to a text parameter's predicate, but paint
  -- nested under that metadata still violates the text-only contract.
  for (styleName, styled) in #[
      ("font", "\\textbf{#1}"), ("color", "\\textcolor{blue}{#1}"),
      ("size", "{\\large #1}")] do
    let pre := "\\newcommand\\wordrole[1]{{" ++ styled ++ "}}" ++
      "\\define \\readtext(a: text){\\a}"
    let source := dvDoc pre "\\readtext\\wordrole{X} Tail"
    let control := dvDoc pre ("\\readtext{" ++ styled.replace "#1" "X" ++ "} Tail")
    let (doc, _) := elabStr source
    let (controlDoc, _) := elabStr control
    let out := layoutOf fs doc
    let controlOut := layoutOf fs controlDoc
    let (_, tree, _) := HtmlDoc.emitTree {} doc
    let (_, controlTree, _) := HtmlDoc.emitTree {} controlDoc
    let html := macroRoleHtmlList ["readtext", "wordrole"] [] {} tree.toList
    let label := s!"macro roles native text parameter rejects tagged {styleName}"
    t (label ++ ": literal control remains E0305") (errCodes control == ["E0305"])
    t (label ++ ": tagged style remains E0305") (errCodes source == ["E0305"])
    t (label ++ ": visible HTML including every space")
      (shownTextList "" tree.toList == shownTextList "" controlTree.toList)
    t (label ++ ": exact glyph positions and paint")
      (shippedBodyGlyphs out == shippedBodyGlyphs controlOut)
    t (label ++ ": exact typed HTML role ancestry")
      (html.glyphs == (#['X'].map (·, ["readtext", "wordrole"]) ++
        "Tail".toList.toArray.map (·, [])))
    t (label ++ ": exactly one consumer and argument owner")
      (html.roles.map (·.1) == #["readtext", "wordrole"])

  -- A deferred paragraph skip is spent when that paragraph is flushed,
  -- even if its raws elaborate to nothing and blocks.size never grows.
  for (prefixName, prefixText) in #[
      ("discarded whitespace", " \n  "), ("empty group", "{}"), ("space group", "{ }")] do
    for (startName, start) in #[("text first", ""), ("paragraph end first", "\\par")] do
      let source := dvDoc
        ("\\newcommand\\entryprobe[1]{" ++ start ++ "#1\\par}" ++
          "\\style{entryprobe}{before = 24pt}")
        ("Lead\\par " ++ prefixText ++ "\\entryprobe{Follow}")
      let control := dvDoc
        ("\\define \\entryprobe(a: content){" ++ start ++ "\\a\\par}" ++
          "\\style{entryprobe}{before = 24pt}")
        ("Lead\\par " ++ prefixText ++ "\\entryprobe{Follow}")
      let (doc, ds) := elabStr source
      let (controlDoc, controlDs) := elabStr control
      let out := layoutOf fs doc
      let controlOut := layoutOf fs controlDoc
      let (_, tree, hds) := HtmlDoc.emitTree {} doc
      let (_, controlTree, controlHds) := HtmlDoc.emitTree {} controlDoc
      let html := macroRoleHtmlList ["entryprobe"] [] {} tree.toList
      let label := s!"macro roles leading {prefixName}, {startName}"
      t (label ++ ": no loss")
        ((ds ++ out.diags ++ hds ++ controlDs ++ controlOut.diags ++ controlHds).all
          (·.severity == .note))
      t (label ++ ": visible HTML including every space")
        (shownTextList "" tree.toList == shownTextList "" controlTree.toList)
      t (label ++ ": exactly one owner")
        (html.roles.map (·.1) == #["entryprobe"])
      t (label ++ ": exact typed HTML role ancestry")
        (html.glyphs == ("Lead".toList.toArray.map (·, []) ++
          "Follow".toList.toArray.map (·, ["entryprobe"])))
      t (label ++ ": whole-block rhythm and exact glyph positions")
        (shippedBodyGlyphs out == shippedBodyGlyphs controlOut)

end Tests
