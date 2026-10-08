module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

def styleAttr (attrs : Array (String × String)) (key : String) : String :=
  ((attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- Read the emitted selector attributes, not the elaborator's selector parser.
The same numbered-state vocabulary is exercised by OverlaySets. -/
private def styleActive (attrs : Array (String × String)) (step : Nat) : Bool :=
  if attrs.any (·.1 == "data-steps") then
    (styleAttr attrs "data-steps").splitOn " " |>.contains (toString step)
  else
    let lo := (styleAttr attrs "data-step").toNat?.getD 1
    let hi := (styleAttr attrs "data-step-last").toNat?
    lo ≤ step && (hi.map fun n => decide (step ≤ n)).getD true

/-- Only the alternation carrier is erased after selecting its branch. Any
unrelated class, style, accessibility attribute, or link remains observable. -/
private def styleCarrierAttrs (attrs : Array (String × String)) :
    Array (String × String) :=
  attrs.filterMap fun (key, value) =>
    if key == "class" then
      let kept := (value.splitOn " ").filter fun c =>
        !["alt", "alt-set", "alt-crisp", "alt-pending"].contains c
      if kept.isEmpty then none else some (key, String.intercalate " " kept)
    else if ["data-step", "data-step-last", "data-steps", "hidden"].contains key then none
    else some (key, value)

mutual

/-- Project the actual typed HTML at one numbered snap. Unlike a text-only
census, this preserves the selected branch's tags and their attributes. -/
private def styleAtOne (step : Nat) (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .text s => acc.push (.text s)
  | .style css => acc.push (.style css)
  | .script attrs js => acc.push (.script attrs js)
  | .elem tag attrs kids =>
    let classes := (styleAttr attrs "class").splitOn " "
    let isAlt := classes.contains "alt-set" || classes.contains "alt-crisp" ||
      classes.contains "alt-pending"
    if isAlt then
      let shown := if classes.contains "alt-pending" then !styleActive attrs step
        else styleActive attrs step
      if !shown then acc else
        let kids := styleAtList step #[] kids.toList
        let attrs := styleCarrierAttrs attrs
        if attrs.isEmpty then acc ++ kids else acc.push (.elem tag attrs kids)
    else acc.push (.elem tag attrs (styleAtList step #[] kids.toList))

private def styleAtList (step : Nat) (acc : Array Html.Node) :
    List Html.Node → Array Html.Node
  | [] => acc
  | n :: ns => styleAtList step (styleAtOne step acc n) ns

end

private def styleAt (step : Nat) (tree : Array Html.Node) : Array Html.Node :=
  styleAtList step #[] tree.toList

private def styleTreeKey (tree : Array Html.Node) : String :=
  Html.document "en" #[] tree

private def styleIds (tree : Array Html.Node) : Array String :=
  (elemAttrsList (fun _ => true) #[] tree.toList).flatMap fun (_, attrs) =>
    attrs.filterMap fun (key, value) => if key == "id" then some value else none

private def styleUniqueIds (tree : Array Html.Node) : Bool :=
  let ids := styleIds tree
  ids.all fun id => !id.isEmpty && (ids.filter (· == id)).size == 1

mutual

/-- The only location normalization: remove an explicitly marked, empty
hoisted anchor and its allowed ID from the original element. Original empty
label spans remain, as do every other tag and attribute. Nested hoists can
leave an empty marker with its ID relocated again; those markers also vanish.
The separate ID census in styleAnchorKey retains missing/duplicate targets. -/
private def styleAnchorOne (allowed : Array String) (acc : Array Html.Node) :
    Html.Node → Array Html.Node
  | .text s => acc.push (.text s)
  | .style css => acc.push (.style css)
  | .script attrs js => acc.push (.script attrs js)
  | .elem tag attrs kids =>
    let id := styleAttr attrs "id"
    let marker := attrs == #[("data-alt-anchor", "")] ||
      (allowed.contains id && attrs == #[("id", id), ("data-alt-anchor", "")])
    if tag == "span" && kids.isEmpty && marker then acc else
      acc.push (.elem tag
        (attrs.filter fun (key, value) => !(key == "id" && allowed.contains value))
        (styleAnchorList allowed #[] kids.toList))

private def styleAnchorList (allowed : Array String) (acc : Array Html.Node) :
    List Html.Node → Array Html.Node
  | [] => acc
  | n :: ns => styleAnchorList allowed (styleAnchorOne allowed acc n) ns

end

private def styleAnchorKey (allowed : Array String) (tree : Array Html.Node) :
    Array Nat × String :=
  let ids := styleIds tree
  (allowed.map (fun id => (ids.filter (· == id)).size),
    styleTreeKey (styleAnchorList allowed #[] tree.toList))

/-- Only IDs carried by the actual artifact's explicit relocation marker
may move. An ID moved onto another ordinary element remains an exact-tree
mismatch, even if its multiplicity is unchanged. -/
private def styleAnchorsAgree (allowed : Array String)
    (ordinary actual : Array Html.Node) : Bool :=
  let relocated := (elemAttrsList (· == "span") #[] actual.toList).filterMap fun (_, attrs) =>
    let id := styleAttr attrs "id"
    if allowed.contains id && attrs == #[("id", id), ("data-alt-anchor", "")]
      then some id else none
  styleAnchorKey relocated ordinary == styleAnchorKey relocated actual

private def styleAnchorSelfChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let attrs := #[("href", "#fn1"), ("id", "fnref1"), ("role", "doc-noteref")]
  let node (a : Array (String × String)) := Html.elem "sup" #[Html.elem "a" #[.text "1"] a]
  let stripped := attrs.filter (·.1 != "id")
  let anchor := Html.elem "span" #[] #[("id", "fnref1"), ("data-alt-anchor", "")]
  let original := #[node attrs]
  let moved := #[anchor, node stripped]
  let key := styleAnchorKey #["fnref1"]
  t "overlay anchor projection allows only declared location change"
    (key original == key moved && styleAnchorsAgree #["fnref1"] original moved &&
      styleTreeKey original != styleTreeKey moved)
  t "overlay anchor projection detects a missing target"
    (key original != key #[node stripped] &&
      key original != key #[Html.elem "span" #[] #[("data-alt-anchor", "")], node stripped])
  t "overlay anchor projection detects a duplicate target"
    (key original != key #[anchor, anchor, node stripped] &&
      key original != key #[anchor, node attrs])
  t "overlay anchor projection keeps href and accessibility roles"
    (key original != key #[anchor, node (stripped.map fun (k, v) =>
      (k, if k == "href" then "#missing" else v))] &&
      key original != key #[anchor, node (stripped.filter (·.1 != "role"))])
  t "overlay anchor projection keeps unmarked spans and other anchor markup"
    (key original != key #[Html.elem "span" #[] #[("id", "fnref1")], node stripped] &&
      key original != key #[Html.elem "span" #[.text "EXTRA"]
        #[("id", "fnref1"), ("data-alt-anchor", "")], node stripped] &&
      key original != key #[Html.elem "span" #[]
        #[("id", "fnref1"), ("data-alt-anchor", ""), ("class", "extra")], node stripped])
  let unmarkedOriginal := #[node attrs, Html.elem "span" #[.text "TEXT"]]
  let unmarkedMove := #[node stripped, Html.elem "span" #[.text "TEXT"] #[("id", "fnref1")]]
  t "overlay anchor comparison refuses relocation without an explicit marker"
    (key unmarkedOriginal == key unmarkedMove &&
      !styleAnchorsAgree #["fnref1"] unmarkedOriginal unmarkedMove)
  t "overlay anchor comparison refuses missing and duplicate marked targets"
    (!styleAnchorsAgree #["fnref1"] original #[node stripped] &&
      !styleAnchorsAgree #["fnref1"] original #[anchor, anchor, node stripped])
  let label := Html.elem "span" #[] #[("id", "effect-label")]
  let labelAnchor := Html.elem "span" #[] #[("id", "effect-label"), ("data-alt-anchor", "")]
  let labelKey := styleAnchorKey #["effect-label"]
  t "overlay label projection retains the original empty label element"
    (labelKey #[label] == labelKey #[labelAnchor, Html.elem "span" #[]] &&
      labelKey #[label] != labelKey #[labelAnchor] &&
      labelKey #[label] != labelKey #[labelAnchor, labelAnchor, Html.elem "span" #[]])
  t "overlay ID uniqueness sees hidden alternatives"
    (styleUniqueIds original && !styleUniqueIds
      #[node attrs, Html.elem "span" original #[("hidden", "hidden")]])

private def styleTagCount (tree : Array Html.Node) (tag : String)
    (className : String := "") : Nat :=
  ((elemAttrsList (· == tag) #[] tree.toList).filter fun (_, attrs) =>
    className.isEmpty || ((styleAttr attrs "class").splitOn " ").contains className).size

def styleBuild (fonts : Font.FontSet) (source : String) :
    Layout.Out × Array Html.Node × Array Diag :=
  let (doc, ds) := elabStr source
  let out := layoutOf fonts doc
  let (_, tree, htmlDs) := HtmlDoc.emitTree {} doc
  (out, tree, ds ++ out.diags ++ htmlDs)

def stylePage (out : Layout.Out) (i : Nat) : Layout.Out :=
  { out with pages := match out.pages[i]? with | some p => #[p] | none => #[] }

def styleText (out : Layout.Out) : String :=
  String.ofList ((shippedBodyGlyphs out).toList.map (·.scalar))

def styleCopies (text needle : String) : Nat :=
  (text.splitOn needle).length - 1

/-- The marker has already been held to one copy by styleWitness. Reading its
shipped glyphs lets a positive assertion distinguish a real style from two
identically unstyled (or blank) artifacts. Markers contain no spaces. -/
def styleGlyphs (out : Layout.Out) (marker : String) : Array ShippedGlyph :=
  let glyphs := shippedBodyGlyphs out
  match (List.range glyphs.size).find? (fun i =>
      (glyphs.extract i (i + marker.length)).toList.map (·.scalar) == marker.toList) with
  | some i => glyphs.extract i (i + marker.length)
  | none => #[]

/-- Compare shipped pages, including the geometry of decoration rider lines,
and selected typed HTML. The artificial clock exposes steps after a closed
range; callers can omit it to test the style command's own frame extent. -/
private def styleWitness (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label native canonical : String) (steps : Nat) (markers : List String)
    (warning : Bool := false) (clock : Bool := true) :
    IO (Array (Layout.Out × Array Html.Node)) := do
  let t := check ref
  let source (body : String) := deck169Frame (body ++
    if clock then "\n\n\\uncover<" ++ toString steps ++ ">{ClockMarker}" else "")
  let (out, tree, ds) := styleBuild fonts (source native)
  let (want, wantTree, wantDs) := styleBuild fonts (source canonical)
  let expectedCodes := if warning then #["W0105"] else #[]
  t (label ++ ": native diagnostics")
    ((ds.filter (·.severity != .note)).map (·.code) == expectedCodes)
  t (label ++ ": canonical diagnostics")
    ((wantDs.filter (·.severity != .note)).map (·.code) == expectedCodes)
  t (label ++ ": shipped page extent") (out.pages.size == steps && want.pages.size == steps)
  let snaps (nodes : Array Html.Node) :=
    ((elemAttrsList (fun _ => true) #[] nodes.toList).filter fun (_, attrs) =>
      attrs.any (·.1 == "data-snap")).size
  t (label ++ ": reachable HTML snaps") (snaps tree == steps && snaps wantTree == steps)
  for marker in markers do
    t (label ++ ": HTML handout keeps " ++ marker) (treeShownOccurs tree marker == 1)
  let mut result := #[]
  for i in [:steps] do
    let page := stylePage out i
    let control := stylePage want i
    let html := styleAt (i + 1) tree
    let controlHtml := styleAt (i + 1) wantTree
    let here := label ++ s!": step {i + 1}"
    t (here ++ " glyph placement and paint")
      (shippedBodyGlyphs page == shippedBodyGlyphs control)
    t (here ++ " line geometry")
      ((bodyLines page).map (fun l => (l.x, l.y, l.setWidth, l.expand)) ==
        (bodyLines control).map (fun l => (l.x, l.y, l.setWidth, l.expand)))
    t (here ++ " decoration geometry")
      (metricDecorationSegs page == metricDecorationSegs control)
    t (here ++ " typed HTML") (styleTreeKey html == styleTreeKey controlHtml)
    for marker in markers do
      t (here ++ " one shipped " ++ marker) (styleCopies (styleText page) marker == 1)
      t (here ++ " one HTML " ++ marker) (treeShownOccurs html marker == 1)
      let glyphs := styleGlyphs page marker
      t (here ++ " positive glyph ink for " ++ marker)
        (!glyphs.isEmpty && glyphs.all fun g => g.glyph > 0 && g.advance > 0 && g.size > 0)
    t (here ++ " selector is syntax")
      (!(styleText page).contains '<' && !(styleText page).contains '>' &&
        !(shownTextList "" html.toList).contains '<' &&
        !(shownTextList "" html.toList).contains '>')
    result := result.push (page, html)
  return result

private def styleAlt (spec styled body : String) : String :=
  "\\alt<" ++ spec ++ ">{" ++ styled ++ "}{" ++ body ++ "}"

private def styleCall (cmd body : String) (spec : String := "") : String :=
  "\\" ++ cmd ++ (if spec.isEmpty then "" else "<" ++ spec ++ ">") ++ "{" ++ body ++ "}"

/-- The serif quartet distinguishes weight and slant; two regular faces
add genuinely different sans and mono slots. Tests requesting weight or
slant use the serif slot. No host font discovery is involved. -/
private def overlayStyleFonts : IO (Option Font.FontSet) := do
  let some base ← serifFacesSet | return none
  let mut loaded := base.fonts
  for name in ["FiraSans-Regular.otf", "SourceCodePro-Regular.otf"] do
    let path := testFonts ++ "/" ++ name
    unless ← System.FilePath.pathExists path do return none
    match Font.parse (← IO.FS.readBinFile path) with
    | .ok font => loaded := loaded.push font
    | .error _ => return none
  return some { base with fonts := loaded, index := base.index.map fun (key, face) =>
    (key, if key.1 == 1 then base.fonts.size
      else if key.1 == 2 then base.fonts.size + 1 else face) }

private structure StyleFontCase where
  command : String
  ambient : String := ""
  onFace : Nat
  offFace : Nat := 0
  tag : String := "span"
  className : String := ""

/-- Every entry is selected through Elab.argStyles below; this table supplies
independent artifact expectations, including inherited styles for resets. -/
private def styleFontCases : List StyleFontCase :=
  [{ command := "textrm", ambient := "textsf", onFace := 0, offFace := 5, className := "rm" },
   { command := "textsf", onFace := 5, className := "sans" },
   { command := "texttt", onFace := 6, tag := "code" },
   { command := "textmd", ambient := "textbf", onFace := 0, offFace := 1, className := "md" },
   { command := "textbf", onFace := 1, tag := "strong" },
   { command := "textup", ambient := "textit", onFace := 0, offFace := 2, className := "up" },
   { command := "textit", onFace := 2, tag := "em" },
   { command := "textsl", onFace := 2, tag := "em" },
   { command := "textsc", onFace := 0, className := "sc" },
   { command := "textnormal", ambient := "textbf", onFace := 0, offFace := 1, tag := "" },
   { command := "emph", ambient := "textit", onFace := 2, offFace := 2, tag := "em" }]

/-- Compare to ordinary documents so the reference cannot duplicate source
side effects through authored alt branches. The only permitted HTML difference
is the explicitly marked anchor relocation, held to its ID multiplicity. -/
private def styleEffectWitness (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label native : String) (ordinary : List String) : IO Unit := do
  let t := check ref
  let source (body : String) := deck169Frame
    (styleCall "textrm" body ++ "\n\n\\uncover<3>{ClockMarker}")
  let (out, tree, ds) := styleBuild fonts (source native)
  t (label ++ ": complete artifact without a loss")
    (ordinary.length == 3 && out.pages.size == 3 && ds.all (·.severity == .note))
  t (label ++ ": full tree has unique IDs, including hidden branches") (styleUniqueIds tree)
  for id in ["fn1", "fn2", "fnref1", "fnref2", "effect-label"] do
    t (label ++ ": full tree has one target " ++ id) (((styleIds tree).filter (· == id)).size == 1)
  let allowed := #["fnref1", "effect-label"]
  for (body, i) in ordinary.zipIdx do
    let (want, wantTree, wantDs) := styleBuild fonts (source body)
    let here := label ++ s!": step {i + 1}"
    t (here ++ " ordinary reference is complete")
      (want.pages.size == 3 && wantDs.all (·.severity == .note) && styleUniqueIds wantTree)
    let page := stylePage out i
    let control := stylePage want i
    let html := styleAt (i + 1) tree
    let controlHtml := styleAt (i + 1) wantTree
    t (here ++ " matches the ordinary reference's shipped glyphs")
      (shippedBodyGlyphs page == shippedBodyGlyphs control)
    t (here ++ " matches the ordinary reference's decoration geometry")
      (metricDecorationSegs page == metricDecorationSegs control)
    t (here ++ " matches the ordinary reference's HTML with explicit anchor relocation")
      (styleAnchorsAgree allowed controlHtml html)
    let flow : Layout.Out := { page with pages := page.pages.map fun p =>
      { p with lines := p.lines.filter (!·.note) } }
    let notes : Layout.Out := { page with pages := page.pages.map fun p =>
      { p with lines := p.lines.filter (·.note) } }
    t (here ++ " first mark remains 1 and following mark remains 2")
      (styleCopies (styleText flow) "FirstProbe1" == 1 &&
        styleCopies (styleText flow) "SecondProbe2" == 1)
    for marker in ["FirstNote", "SecondNote"] do
      let glyphs := styleGlyphs notes marker
      t (here ++ " one positive shipped and HTML note body " ++ marker)
        (styleCopies (styleText notes) marker == 1 && !glyphs.isEmpty &&
          glyphs.all (fun g => g.glyph > 0 && g.advance > 0) && treeShownOccurs html marker == 1)
    let links := elemAttrsList (· == "a") #[] html.toList
    let refs := links.filter fun (_, attrs) => styleAttr attrs "role" == "doc-noteref"
    let backs := links.filter fun (_, attrs) => styleAttr attrs "role" == "doc-backlink"
    t (here ++ " exactly two stable HTML note references")
      (refs.map (fun (_, attrs) => styleAttr attrs "href") == #["#fn1", "#fn2"])
    t (here ++ " exactly two stable HTML backlinks")
      (backs.map (fun (_, attrs) => styleAttr attrs "href") == #["#fnref1", "#fnref2"])
    let noteIds := ((elemAttrsList (· == "li") #[] html.toList).map fun (_, attrs) =>
      styleAttr attrs "id").filter (·.startsWith "fn")
    t (here ++ " exactly two stable HTML note targets") (noteIds == #["fn1", "fn2"])
    for id in ["fn1", "fn2", "fnref1", "fnref2", "effect-label"] do
      t (here ++ " one reachable target " ++ id) (((styleIds html).filter (· == id)).size == 1)
    t (here ++ " the label link reaches its single anchor")
      ((links.filter fun (_, attrs) => styleAttr attrs "href" == "#effect-label").size == 1 &&
        treeShownOccurs html "LabelLink" == 1 && styleCopies (styleText flow) "LabelLink" == 1)

private def styleEffectChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let first := "FirstProbe\\footnote{FirstNote}\\label{effect-label}"
  let after := " SecondProbe\\footnote{SecondNote} \\hyperlink{effect-label}{LabelLink}"
  for cmd in ["textbf", "textit", "texttt", "sout", "uline", "underline", "textcolor"] do
    let apply (spec body : String) := if cmd == "textcolor" then
        "\\textcolor" ++ (if spec.isEmpty then "" else "<" ++ spec ++ ">") ++
          "[RGB]{17,34,51}{" ++ body ++ "}"
      else styleCall cmd body spec
    for (spec, active) in [("2", [false, true, false]), ("1,3", [true, false, true])] do
      styleEffectWitness ref fonts ("overlay effects " ++ cmd ++ " <" ++ spec ++ ">")
        (apply spec first ++ after)
        (active.map fun selected => (if selected then apply "" first else first) ++ after)
  styleEffectWitness ref fonts "overlay effects nested font and decoration selectors"
    (styleCall "textbf" (styleCall "uline" first "1,3") "2-3" ++ after)
    [styleCall "uline" first ++ after, styleCall "textbf" first ++ after,
      styleCall "textbf" (styleCall "uline" first) ++ after]
  let colored := "\\textcolor[RGB]{17,34,51}{" ++ first ++ "}"
  styleEffectWitness ref fonts "overlay effects nested mono and colour selectors"
    (styleCall "texttt" ("\\textcolor<1,3>[RGB]{17,34,51}{" ++ first ++ "}") "2" ++ after)
    [colored ++ after, styleCall "texttt" first ++ after, colored ++ after]

/-- Explicitly repeated notes in one authored arm must survive multiset
union across alternatives. Reusing an explicit mark here intentionally repeats
IDs; the unique-ID contract above applies to a single authored occurrence. -/
private def styleRepeatedNotes (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let arm (n : Nat) := String.intercalate " "
    (List.replicate n "RepeatProbe\\footnote[7]{RepeatNote}")
  for (first, other) in [(2, 1), (1, 2), (2, 2)] do
    let label := s!"overlay same-arm repeated notes {first}/{other}"
    let (out, tree, ds) := styleBuild fonts (deck169Frame (styleAlt "2" (arm first) (arm other)))
    t (label ++ ": two shipped steps") (out.pages.size == 2 && ds.all (·.severity != .error))
    let maximum := max first other
    t (label ++ ": HTML retains max multiplicity across exclusive branches")
      (treeShownOccurs tree "RepeatNote" == maximum &&
        ((elemAttrsList (· == "li") #[] tree.toList).filter fun (_, attrs) =>
          styleAttr attrs "id" == "fn7").size == maximum)
    for (count, i) in [other, first].zipIdx do
      let page := stylePage out i
      let notes : Layout.Out := { page with pages := page.pages.map fun p =>
        { p with lines := p.lines.filter (·.note) } }
      let glyphs := styleGlyphs notes "RepeatNote"
      t (label ++ s!": step {i + 1} preserves repeated note bodies and marks")
        (styleCopies (styleText notes) "RepeatNote" == count &&
          styleCopies (styleText page) "RepeatProbe7" == count && !glyphs.isEmpty &&
          glyphs.all (fun g => g.glyph > 0 && g.advance > 0))

/-- Conditional mono punctuation is checked against ordinary documents,
including text below another font/decor wrapper. No alt supplies the oracle. -/
private def stylePunctuationChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let body := "``PUNCT''--A---B... \\uline{``INNER''--C}"
  -- Keep the frame name independent of the first reveal: the body is the oracle.
  let source (s : String) := deck169Frame
    ("\\frametitle{Punctuation}\n" ++
      styleCall "textrm" ("StartGuard " ++ s ++ " EndGuard") ++ "\n\n\\uncover<3>{ClockMarker}")
  let (out, tree, ds) := styleBuild fonts (source (styleCall "texttt" body "2"))
  t "overlay mono punctuation: three complete steps" (out.pages.size == 3 && ds.all (·.severity == .note))
  for (selected, i) in [false, true, false].zipIdx do
    let (want, wantTree, wantDs) := styleBuild fonts
      (source (if selected then styleCall "texttt" body else body))
    let page := stylePage out i
    let control := stylePage want i
    let html := styleAt (i + 1) tree
    let here := s!"overlay mono punctuation step {i + 1}"
    t (here ++ ": matches an ordinary reference without markup normalization")
      (want.pages.size == 3 && wantDs.all (·.severity == .note) &&
        shippedBodyGlyphs page == shippedBodyGlyphs control &&
        metricDecorationSegs page == metricDecorationSegs control &&
        styleTreeKey html == styleTreeKey (styleAt (i + 1) wantTree))
    let expected := if selected then "``PUNCT''--A---B..." else "“PUNCT”–A—B…"
    let inner := if selected then "``INNER''--C" else "“INNER”–C"
    t (here ++ ": independent literal or smart punctuation and positive glyphs")
      (styleCopies (styleText page) expected == 1 && treeShownOccurs html expected == 1 &&
        styleCopies (styleText page) inner == 1 && treeShownOccurs html inner == 1 &&
        !(styleGlyphs page "PUNCT").isEmpty &&
        (styleGlyphs page "PUNCT").all (·.face == if selected then 6 else 0) &&
        styleTagCount html "code" == if selected then 1 else 0)

/-- Native overlay styles retain one body on every step and only select the
style. All visual claims read Layout.Out or the typed HTML artifact; the
reference is an explicit alternation through the existing native command. -/
def overlayStyleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  styleAnchorSelfChecks ref
  -- Hold the projection's declared blind spot in both directions: only
  -- inactive alternatives and their carrier attributes disappear.
  let selected := Html.elem "strong" #[.text "PROBE"]
  let carrier := Html.elem "span" #[selected]
    #[("class", "alt alt-set"), ("data-steps", "2 4"), ("hidden", "hidden")]
  t "overlay style projection selects a hidden union branch"
    (styleTreeKey (styleAt 2 #[carrier]) == styleTreeKey #[selected] &&
      styleTreeKey #[carrier] != styleTreeKey #[selected] &&
      (styleAt 3 #[carrier]).isEmpty)
  let marked := Html.elem "span" #[selected]
    #[("class", "alt alt-set author"), ("data-steps", "2"), ("aria-hidden", "true")]
  t "overlay style projection keeps unrelated class and accessibility attributes"
    (styleTreeKey (styleAt 2 #[marked]) == styleTreeKey #[Html.elem "span" #[selected]
      #[("class", "author"), ("aria-hidden", "true")]] &&
      styleTreeKey (styleAt 2 #[marked]) != styleTreeKey #[selected])
  let hidden := Html.elem "span" #[.text "PROBE"] #[("hidden", "hidden")]
  t "overlay style projection does not reveal ordinary hidden content"
    (styleTreeKey (styleAt 2 #[hidden]) == styleTreeKey #[hidden] &&
      treeShownOccurs (styleAt 2 #[hidden]) "PROBE" == 0)

  let specs : List (String × List Bool) :=
    [("2", [false, true, false]), ("-2", [true, true, false]),
     ("2-", [false, true, true, true]), ("2-3", [false, true, true, false]),
     ("1,3-4", [true, false, true, true, false]),
     ("4,1,4", [true, false, false, true, false]),
     ("1-2,2,4", [true, true, false, true, false]),
     ("2,4-", [false, true, false, true, true])]
  let guard (body : String) := "StartGuard " ++ body ++ " EndGuard"
  let markers := ["StartGuard", "STYLEPROBE", "EndGuard"]
  let decorationCheck (label cmd marker : String) (selected : Bool)
      (page : Layout.Out) (html : Array Html.Node) : IO Unit := do
    let strike := cmd == "sout"
    let kind : Ir.Decoration := if strike then .lineThrough else .underline
    let marks := metricDecorationSegs page
    t (label ++ ": selected decoration ships ink") (!marks.isEmpty == selected)
    t (label ++ ": positive decoration on the correct side of the baseline")
      (marks.all fun (k, w, thickness, raise, _) =>
        k == kind && w > 0 && thickness > 0 && (if strike then raise > 0 else raise < 0))
    t (label ++ ": selected semantic tag")
      (styleTagCount html (if strike then "s" else "u") == if selected then 1 else 0)
    t (label ++ ": decoration belongs to body glyphs")
      ((styleGlyphs page marker).all fun g =>
        if strike then g.decorations.lineThrough.isSome == selected && !g.decorations.underline
        else g.decorations.underline == selected && g.decorations.lineThrough.isNone)
    t (label ++ ": following text stays undecorated")
      ((styleGlyphs page "EndGuard").all fun g =>
        !g.decorations.underline && g.decorations.lineThrough.isNone)
  for cmd in ["sout", "uline", "underline"] do
    for (spec, active) in specs do
      let label := "overlay style " ++ cmd ++ " <" ++ spec ++ ">"
      let pages ← styleWitness ref fonts label (guard (styleCall cmd "STYLEPROBE" spec))
        (guard (styleAlt spec (styleCall cmd "STYLEPROBE") "STYLEPROBE")) active.length markers
      for (selected, i) in active.zipIdx do
        let some (page, html) := pages[i]? |
          t (label ++ s!": missing step {i + 1}") false
          continue
        decorationCheck (label ++ s!" step {i + 1}") cmd "STYLEPROBE" selected page html
    -- The operand is a single character adjacent to the selector. A whole
    -- Raw.word's TeX character-token semantics is a separate compatibility issue.
    let pages ← styleWitness ref fonts ("overlay style adjacent " ++ cmd)
      (guard ("\\" ++ cmd ++ "<2>Q{TAIL}"))
      (guard (styleAlt "2" (styleCall cmd "Q") "Q" ++ "{TAIL}")) 2
      ["StartGuard", "QTAIL", "EndGuard"] (clock := false)
    for (page, html, i) in pages.mapIdx (fun i (page, html) => (page, html, i)) do
      decorationCheck (s!"overlay style adjacent {cmd} step {i + 1}") cmd "Q" (i == 1) page html
      t (s!"overlay style adjacent {cmd}: operand boundary {i + 1}")
        ((styleGlyphs page "TAIL").all fun g =>
          !g.decorations.underline && g.decorations.lineThrough.isNone)

  let some faceSet ← overlayStyleFonts | t "overlay style fixture faces load" false
  styleEffectChecks ref faceSet
  styleRepeatedNotes ref faceSet
  stylePunctuationChecks ref faceSet
  t "overlay style font oracle covers exactly the native argument family"
    (Elab.argStyles.all (fun (name, _) => styleFontCases.any (·.command == name)) &&
      styleFontCases.all (fun c => Elab.argStyles.any (·.1 == c.command)) &&
      styleFontCases.length == Elab.argStyles.length)
  for (cmd, _) in Elab.argStyles do
    let some row := styleFontCases.find? (·.command == cmd) | continue
    let scope (body : String) := styleCall "textrm" (guard
      (if row.ambient.isEmpty then body else styleCall row.ambient body))
    for (spec, active, clock) in
        [("2", [false, true], false), ("1,3-4", [true, false, true, true, false], true)] do
      let label := "overlay font " ++ cmd ++ " <" ++ spec ++ ">"
      let pages ← styleWitness ref faceSet label (scope (styleCall cmd "STYLEPROBE" spec))
        (scope (styleAlt spec (styleCall cmd "STYLEPROBE") "STYLEPROBE")) active.length markers
        (clock := clock)
      for (selected, i) in active.zipIdx do
        let some (page, html) := pages[i]? |
          t (label ++ s!": missing step {i + 1}") false
          continue
        let probe := styleGlyphs page "STYLEPROBE"
        t (label ++ s!": step {i + 1} independently selected face")
          (probe.all (·.face == if selected then row.onFace else row.offFace))
        t (label ++ s!": step {i + 1} surrounding face restored")
          ((styleGlyphs page "StartGuard").all (·.face == 0) &&
            (styleGlyphs page "EndGuard").all (·.face == 0))
        unless row.tag.isEmpty do
          let ambientCount := if row.className == "rm" ||
              (row.tag == "em" && row.ambient == "textit") then 1 else 0
          t (label ++ s!": step {i + 1} selected HTML font tag")
            (styleTagCount html row.tag row.className == ambientCount + if selected then 1 else 0)
        if cmd == "textsc" then
          let normalSize := ((styleGlyphs page "StartGuard")[0]?).map (·.size)
          let changed := probe.any fun g =>
            (faceSet.get g.face).gid g.scalar != some g.glyph || normalSize.any (g.size < ·)
          t (label ++ s!": step {i + 1} small-cap glyph or size change") (changed == selected)
    let _ ← styleWitness ref faceSet ("overlay font adjacent " ++ cmd)
      (scope ("\\" ++ cmd ++ "<2>Q{TAIL}"))
      (scope (styleAlt "2" (styleCall cmd "Q") "Q" ++ "{TAIL}")) 2
      ["StartGuard", "QTAIL", "EndGuard"] (clock := false)

  -- beamerbaseoverlay.sty declares emph with a trailing overlay and
  -- presentation emphasis forces italic even inside italic text.
  for ambient in ["", "textit"] do
    let scope (body : String) := styleCall "textrm" (guard
      (if ambient.isEmpty then body else styleCall ambient body))
    let pages ← styleWitness ref faceSet ("overlay emph trailing " ++ ambient)
      (scope "\\emph{STYLEPROBE}<2>")
      (scope (styleAlt "2" (styleCall "emph" "STYLEPROBE") "STYLEPROBE")) 3 markers
    for (page, html, i) in pages.mapIdx (fun i (page, html) => (page, html, i)) do
      t (s!"overlay emph trailing {ambient} step {i + 1}: native italic and tags")
        ((styleGlyphs page "STYLEPROBE").all
          (·.face == if i == 1 || ambient == "textit" then 2 else 0) &&
          styleTagCount html "em" == (if ambient == "textit" then 1 else 0) +
            (if i == 1 then 1 else 0))
  -- Beamer's emph is a plain italic wrapper: unlike textit, it does not
  -- insert font-command corrections. LuaLaTeX box/glyph probes confirm the
  -- declaration spelling below on either side of adjacent upright text.
  for ambient in ["", "textit"] do
    let scope (body : String) := styleCall "textrm" (guard
      (if ambient.isEmpty then body else styleCall ambient body))
    for (native, canonical) in
        [("\\emph<2>{x}A", styleAlt "2" "{\\itshape x}" "x" ++ "A"),
         ("A\\emph{x}<2>", "A" ++ styleAlt "2" "{\\itshape x}" "x")] do
      let _ ← styleWitness ref faceSet ("overlay emph correction " ++ ambient ++ native)
        (scope native) (scope canonical) 2 ["StartGuard", "x", "EndGuard"]
  let (article, articleTree, articleDs) := styleBuild faceSet
    (dvDoc "" "\\textrm{\\textit{StartGuard \\emph{STYLEPROBE} EndGuard}}")
  t "ordinary article emphasis still toggles an inherited italic face"
    (article.pages.size == 1 && articleDs.all (·.severity == .note) &&
      styleCopies (styleText article) "STYLEPROBE" == 1 && treeShownOccurs articleTree "STYLEPROBE" == 1 &&
      !(styleGlyphs article "STYLEPROBE").isEmpty &&
      (styleGlyphs article "STYLEPROBE").all (·.face == 0) &&
      (styleGlyphs article "StartGuard").all (·.face == 2) &&
      (styleGlyphs article "EndGuard").all (·.face == 2))

  for (args, color) in [("{blue}", Ir.Color.ofHtml 0 0 255),
      ("[RGB]{17,34,51}", Ir.Color.ofHtml 17 34 51)] do
    for (spec, active) in [("2", [false, true, false]),
        ("1,3-4", [true, false, true, true, false])] do
      let plain := "\\textcolor" ++ args ++ "{STYLEPROBE}"
      let label := "overlay textcolor " ++ args ++ " <" ++ spec ++ ">"
      let pages ← styleWitness ref fonts label
        (guard ("\\textcolor<" ++ spec ++ ">" ++ args ++ "{STYLEPROBE}"))
        (guard (styleAlt spec plain "STYLEPROBE")) active.length markers
      for (selected, i) in active.zipIdx do
        let some (page, html) := pages[i]? |
          t (label ++ s!": missing step {i + 1}") false
          continue
        let ordinary := ((styleGlyphs page "StartGuard")[0]?).map (·.color)
        t (label ++ s!": step {i + 1} independent glyph colour")
          ((styleGlyphs page "STYLEPROBE").all fun g =>
            if selected then g.color == color else some g.color == ordinary)
        t (label ++ s!": step {i + 1} one selected HTML colour")
          (((elemAttrsList (· == "span") #[] html.toList).filter fun (_, attrs) =>
            (styleAttr attrs "style").startsWith "color:").size == if selected then 1 else 0)

  -- Each nested selector affects its own style, even when the other style
  -- is inactive. The linked body and the always-on font survive both arms.
  let inner := "\\href{https://example.org/overlay}{\\textbf{STYLEPROBE}}"
  let innerAlt := styleAlt "1,3" (styleCall "uline" inner) inner
  let nested ← styleWitness ref faceSet "overlay nested link font and selectors"
    (styleCall "textrm" (guard ("\\sout<2-3>{\\uline<1,3>{" ++ inner ++ "}}")))
    (styleCall "textrm" (guard (styleAlt "2-3" (styleCall "sout" innerAlt) innerAlt))) 4 markers
  for (page, html, i) in nested.mapIdx (fun i (page, html) => (page, html, i)) do
    let strike := i == 1 || i == 2
    let under := i == 0 || i == 2
    let glyphs := styleGlyphs page "STYLEPROBE"
    t (s!"overlay nested step {i + 1}: link and bold face survive")
      (glyphs.all fun g => g.face == 1 && g.link == some "https://example.org/overlay")
    t (s!"overlay nested step {i + 1}: separate style membership")
      (styleTagCount html "s" == (if strike then 1 else 0) &&
        styleTagCount html "u" == (if under then 1 else 0) && styleTagCount html "strong" == 1 &&
        ((elemAttrsList (· == "a") #[] html.toList).filter fun (_, attrs) =>
          styleAttr attrs "href" == "https://example.org/overlay").size == 1 &&
        glyphs.all (fun g => g.decorations.lineThrough.isSome == strike))
    let strikes := (metricDecorationSegs page).filter (fun (kind, _, _, _, _) => kind == .lineThrough)
    t (s!"overlay nested step {i + 1}: painted strike membership")
      (strikes.isEmpty == !strike && strikes.all (fun (_, w, h, raise, _) => w > 0 && h > 0 && raise > 0))

  let nestedFont := styleAlt "1,3" (styleCall "textit" "STYLEPROBE") "STYLEPROBE"
  let fontPages ← styleWitness ref faceSet "overlay nested font selectors"
    (styleCall "textrm" (guard "\\textbf<2-3>{\\textit<1,3>{STYLEPROBE}}"))
    (styleCall "textrm" (guard (styleAlt "2-3" (styleCall "textbf" nestedFont) nestedFont))) 4 markers
  for (page, html, i) in fontPages.mapIdx (fun i (page, html) => (page, html, i)) do
    let face := (#[2, 1, 3, 0] : Array Nat)[i]!
    t (s!"overlay nested fonts step {i + 1}: independent face")
      ((styleGlyphs page "STYLEPROBE").all (·.face == face))
    t (s!"overlay nested fonts step {i + 1}: independent tags")
      (styleTagCount html "strong" == (if i == 1 || i == 2 then 1 else 0) &&
        styleTagCount html "em" == (if i == 0 || i == 2 then 1 else 0))

  -- Refusing a selector is accounted for once and retains the native
  -- command's body, as an unsupported explicit alt retains its first arm.
  for spec in ["+-", "2,x"] do
    for cmd in ["sout", "uline", "underline"] ++ Elab.argStyles.map (·.1) do
      let _ ← styleWitness ref faceSet ("overlay refused " ++ cmd ++ " <" ++ spec ++ ">")
        (guard (styleCall cmd "STYLEPROBE" spec))
        (guard (styleAlt spec (styleCall cmd "STYLEPROBE") "STYLEPROBE")) 3 markers (warning := true)
    for args in ["{blue}", "[RGB]{17,34,51}"] do
      let _ ← styleWitness ref fonts ("overlay refused textcolor " ++ args ++ " <" ++ spec ++ ">")
        (guard ("\\textcolor<" ++ spec ++ ">" ++ args ++ "{STYLEPROBE}"))
        (guard (styleAlt spec ("\\textcolor" ++ args ++ "{STYLEPROBE}") "STYLEPROBE"))
        3 markers (warning := true)

  for (label, body, literal) in [
      ("prose", "BEFORE<2>AFTER", "BEFORE<2>AFTER"),
      ("after argument", "\\textbf{BEFORE}<2>AFTER", "BEFORE<2>AFTER"),
      ("after link", "\\href{https://example.org}{BEFORE}<1,3-4>AFTER", "BEFORE<1,3-4>AFTER"),
      ("inline verbatim", "\\verb|\\sout<2>{LITERAL}|", "\\sout<2>{LITERAL}"),
      ("block verbatim", "\\begin{verbatim}\n\\textbf<1,3-4>{LITERAL}\n\\end{verbatim}",
        "\\textbf<1,3-4>{LITERAL}")] do
    let source := deck169Body ("\\begin{frame}[fragile]\n" ++ body ++ "\n\\end{frame}")
    let (out, tree, ds) := styleBuild fonts source
    t ("overlay literal " ++ label ++ ": no selector diagnostic or extra page")
      (out.pages.size == 1 && ds.all (·.severity == .note))
    t ("overlay literal " ++ label ++ ": shipped verbatim") (styleCopies (styleText out) literal == 1)
    t ("overlay literal " ++ label ++ ": typed HTML verbatim") (treeShownOccurs tree literal == 1)
    if label == "inline verbatim" || label == "block verbatim" then
      t ("overlay literal " ++ label ++ ": no interpreted style")
        ((metricDecorationSegs out).isEmpty && styleTagCount tree "s" == 0 &&
          styleTagCount tree "strong" == 0 && styleTagCount tree "code" > 0)

end Tests
