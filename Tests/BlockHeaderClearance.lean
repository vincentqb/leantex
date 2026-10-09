module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.BlockHeaderClearance

private def bodyColor : Ir.Color := { r := 230, g := 241, b := 216 }
private def titleColor : Ir.Color := { r := 35, g := 57, b := 91 }
private def innerColor : Ir.Color := { r := 199, g := 218, b := 242 }
private def headerColor : Ir.Color := { r := 67, g := 85, b := 104 }

/-- Invented frame boundary probes. Ordinary fit, spill, and empty paint
are separate witnesses; the ordinary matrix does not claim zero flex. -/
private def source (alignment body : String) (size : Nat := 12) (height : Nat := 240) : String :=
  "\\documentclass{beamer}\n" ++
  s!"\\page\{width=320pt,height={height}pt,hmargin=16pt,vmargin=14pt,fontsize={size}pt}\n" ++
  "\\palette{fg=#101010,bg=#FFFFFF,frametitlebg=#435568,frametitlefg=#FFFFFF," ++
    "blockbodybg=#E6F1D8," ++
    "blocktitlebg=#23395B,examplebodybg=#C7DAF2,exampletitlebg=#23395B}\n" ++
  "\\begin{document}\n\\begin{frame}[" ++ alignment ++ "]{FRAME}\n" ++
  body ++ "\n\\end{frame}\n\\end{document}\n"

private def bodies : Array (String × String) := #[
  ("paragraph", "BODY"),
  ("titleless", "\\begin{block}{}BODY\\end{block}"),
  ("titled", "\\begin{block}{CAPTION}BODY\\end{block}"),
  ("nested", "\\begin{block}{}\\begin{exampleblock}{CAPTION}BODY" ++
    "\\end{exampleblock}\\end{block}")]

private def isSurface (fill : Layout.Fill) : Bool :=
  #[bodyColor, titleColor, innerColor].contains fill.color

private def hasClass (node : Html.Node) (name : String) : Bool :=
  match node with
  | .elem _ attrs _ =>
    ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " " |>.contains name
  | .text _ | .style _ | .script .. => false

/-- The minimum painted body coordinate of the shipped page. Header ink
is identified by its fixture text; header lines are not `furniture`.
Filled surfaces count even when their first glyph stands lower. -/
private def paintedTop (fonts : Font.FontSet) (page : Layout.PageOut) : Option Dim.Sp :=
  let ys := (page.fills.filter isSurface).map (·.y) ++
    (page.lines.filter fun line =>
      !line.furniture && lineText line != "FRAME" && !(lineText line).isEmpty).map
      (fun line => line.y - (Layout.segsInk fonts line.segs).1)
  ys.foldl (fun acc y => some (acc.map (min y) |>.getD y)) none

/-- Read the actual repeated header paint independently of its census
metadata: a missing `PageOut.band` must not hide a continuation page. -/
private def headerBottom (page : Layout.PageOut) : Option Dim.Sp :=
  (page.fills.filter (·.color == headerColor)).foldl
    (fun edge fill => some (edge.map (max (fill.y + fill.h)) |>.getD (fill.y + fill.h))) none

private def property (decls key : String) : Option String :=
  (decls.splitOn ";").foldl (fun acc decl =>
    match decl.splitOn ":" with
    | [name, value] =>
      if name.trimAscii.toString == key then some value.trimAscii.toString else acc
    | _ => acc) none

private def styleOf : Html.Node → String
  | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "style").getD ""
  | .text _ | .style _ | .script .. => ""

private def participates : Html.Node → Bool
  | .elem "header" _ _ => false
  | node@(.elem _ attrs _) =>
    !(attrs.any (·.1 == "hidden")) && !hasClass node "fill" &&
      !hasClass node "slide-foot" && !hasClass node "slide-logo"
  | .text _ | .style _ | .script .. => false

private def selectorParts (selector : String) : List String := Id.run do
  let mut out := []
  let mut part := ""
  let mut depth := 0
  for c in selector.toList do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if c == ',' && depth == 0 then
      out := part.trimAscii.toString :: out
      part := ""
    else part := part.push c
  return (part.trimAscii.toString :: out).reverse

private def compoundMatches (selector : String) (node : Html.Node) : Bool :=
  match node, selector.splitOn "." with
  | .elem tag _ _, kind :: classes =>
    (kind.isEmpty || kind == "*" || kind == tag) &&
      classes.all (hasClass node)
  | _, _ => false

/-- A bounded cascade reader for these direct stage children: type/class
compounds, direct-child and adjacent-sibling selectors, and `:where()`.
The emitted rules are read in order; inline declarations win. This is not
a general CSS engine or a rendered-browser distance measurement. -/
private def selectorMatches (selector : String) (stage node : Html.Node)
    (previous : Option Html.Node) : Bool :=
  let selector := selector.trimAscii.toString
  let selector := if selector.startsWith ":where(" && selector.endsWith ")" then
      (selector.drop 7 |>.dropEnd 1).toString
    else selector
  (selectorParts selector).any fun part =>
    match part.splitOn " > " with
    | [parent, child] => compoundMatches parent stage && compoundMatches child node
    | [one] => match one.splitOn " + " with
      | [left, right] => previous.any (compoundMatches left) && compoundMatches right node
      | [one] => compoundMatches one node
      | _ => false
    | _ => false

private def specificity (selector : String) : Nat × Nat :=
  if selector.startsWith ":where(" then (0, 0)
  else
    ((selector.toList.filter (· == '.')).length,
      ((selector.splitOn " ").filter fun part =>
        part.toList.head?.any Char.isAlpha).length)

private def marginTop (decls : String) : Option String :=
  (decls.splitOn ";").foldl (fun acc decl =>
    match decl.splitOn ":" with
    | [key, value] =>
      let value := value.trimAscii.toString
      if key.trimAscii.toString == "margin-top" then some value
      else if key.trimAscii.toString == "margin" then
        (value.splitOn " ").head?
      else acc
    | _ => acc) none

private def winningMargin (css : String) (stage node : Html.Node)
    (previous : Option Html.Node) : Option String := Id.run do
  let mut winner : Option String := none
  let mut rank := (0, 0)
  for (selector, decls) in artCssBlocks css do
    if selectorMatches selector stage node previous then
      if let some margin := marginTop decls then
        let next := specificity selector
        if next.1 > rank.1 || (next.1 == rank.1 && next.2 ≥ rank.2) then
          winner := some margin
          rank := next
  return (marginTop (styleOf node)).or winner

private def openingMargin :=
  "calc(var(--frame-body-skip) + var(--frame-body-before, 0pt) + var(--frame-body-open, 0pt))"

/-- Read the first participating box and its winning margin, including
resets, class specificity and inline precedence. Authored leading space
must remain a separate addend. The stage conversion permits only its one
printed milli-percent of coordinate rounding. -/
private def htmlOpeningClearance (css : String) (stage : Html.Node)
    (skip height : Dim.Sp) (before : String := "0pt") : Bool :=
  match stage with
  | .elem "section" attrs kids =>
    let body := kids.filter participates
    let elements := kids.filter fun node => node.tag?.isSome
    let first := elements.findIdx? participates
    (first.bind fun i => do
      let node ← elements[i]?
      let previous := if i == 0 then none else elements[i - 1]?
      let margin := winningMargin css stage node previous
      return hasClass node "frame-body-start" &&
        (margin == some openingMargin ||
          (before == "0pt" && margin == some "var(--frame-body-skip)")) &&
        (property (styleOf node) "--frame-body-before").getD "0pt" == before).getD false &&
      (kids.filter (hasClass · "frame-body-start")).size == 1 &&
      !body.isEmpty &&
      cssStageLength ((HtmlDoc.attrOf? attrs "style").getD "")
        "--frame-body-skip" skip height
  | .elem _ _ _ | .text _ | .style _ | .script .. => false

/-- Mutations of the read-side judge: the right class and property must
not hide a stronger class, inline margin, later reset, or hidden owner. -/
private def cascadeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let header := Html.elem "header" #[]
  let node := Html.elem "div" #[] #[("class", "spaced frame-body-start")]
  let stage := Html.elem "section" #[header, node]
    #[("class", "slide"), ("style", "--frame-body-skip: 1vh")]
  let css := s!":where(section.slide > .frame-body-start) \{ margin-top: {openingMargin}; }"
  let accepts (css : String) (node : Html.Node) :=
    winningMargin css stage node (some header) == some openingMargin
  check ref "block clearance judge: accepts the winning boundary" (accepts css node)
  check ref "block clearance judge: later reset defeats the boundary"
    (!accepts (css ++ ":where(div) { margin: 0; }") node)
  check ref "block clearance judge: earlier class defeats the boundary"
    (!accepts (".spaced { margin-top: 0; }" ++ css) node)
  let inline := Html.elem "div" #[] #[("class", "spaced frame-body-start"),
    ("style", "margin-top: 0")]
  check ref "block clearance judge: inline margin defeats the boundary" (!accepts css inline)
  let hidden := Html.elem "aside" #[] #[("hidden", ""), ("class", "frame-body-start")]
  check ref "block clearance judge: hidden owner cannot pay for visible body"
    (!htmlOpeningClearance css
      (Html.elem "section" #[header, hidden, Html.elem "div" #[]]
        #[("class", "slide"), ("style", "--frame-body-skip: 1vh")]) 1 100)

/-- Exercise the sourced-glue boundary directly: a theme may supply a
resolved fallback without declaring its token in the document. Root and
epoch declarations, and that fallback, must all remain CSS lengths when
the opening rule adds them. The positive cases preserve token references;
the zero cases catch unitless numbers inside the emitted `calc`. -/
private def tokenClearanceChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) :
    IO Unit := do
  let (base, ds) := Elab.run "frame-clearance.tex"
    (source "t" "\\begin{block}{}BODY\\end{block}")
  check ref "block clearance tokens: source has no loss" (ds.all (·.severity == .note))
  for points in #[0, 7] do
    for scope in #["root", "fallback", "epoch"] do
      let gap : Dim.SymGlue := { width := Dim.Length.ofSp (Dim.pt points) }
      let initial : Dim.SymGlue := { width := Dim.Length.ofSp (Dim.pt 9) }
      let tokens := if scope == "fallback" then base.tokens else
        base.tokens.declare "clearancegap" (if scope == "epoch" then initial else gap)
      let doc := { base with tokens, body := base.body.map fun
        | .frame title standout valign breakable body =>
          .frame title standout valign breakable
            ((if scope == "epoch" then
                #[.setTokens (tokens.declare "clearancegap" gap)] else #[]) ++
              #[.spaced { value := gap, token := some "clearancegap" } body])
        | other => other }
      let (head, nodes, htmlDs) := HtmlDoc.emitTree { fonts := some fonts } doc
      let css := treeCssList "" head.toList
      let rootValue := (artCssBlocks css).foldl (fun value (selector, decls) =>
        if selector.trimAscii.toString == ":root" then
          (property decls "--clearancegap").or value else value) none
      let stages := (elemNodesList (· == "section") #[] nodes.toList).filter
        (hasClass · "slide")
      let length := s!"{points}pt"
      let expectedRoot := if scope == "fallback" then none else
        some (if scope == "epoch" then "9pt" else length)
      let name := s!"block clearance tokens/{scope}/{points}"
      check ref (name ++ ": root declaration remains a length")
        (rootValue == expectedRoot)
      check ref (name ++ ": sourced fallback composes with the fixed opening")
        (stages.size == 1 && stages.all
          (htmlOpeningClearance css · (doc.page.fontSize / 4 + Dim.mm 2)
            doc.page.height s!"var(--clearancegap, {length})"))
      if scope == "epoch" then
        check ref (name ++ ": epoch declaration remains a length on the opening box")
          ((elemNodesList (fun _ => true) #[] nodes.toList).any fun node =>
            hasClass node "frame-body-start" &&
              property (styleOf node) "--clearancegap" == some length)
      let out := layoutOf fonts doc
      check ref (name ++ ": native paint includes the sourced gap")
        ((out.pages[0]?).any fun page => (paintedTop fonts page).any fun y =>
          page.band.any fun band =>
            band + doc.page.fontSize / 4 + Dim.mm 2 + Dim.pt points ≤ y)
      check ref (name ++ ": both artifacts retain body text without loss")
        ((htmlDs ++ out.diags).all (·.severity == .note) &&
          (out.pages.flatMap (·.lines)).any (fun line => lineText line == "BODY") &&
          (nodeTextList "" nodes.toList).contains "BODY")

/-- Artifact guard for the opening boundary, independently specified from
beamer's quarter-em title skip and 2 mm top-alignment skip. The PDF guard
reads final paint; HTML reads the first emitted body element and CSS. -/
def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  cascadeChecks ref
  tokenClearanceChecks ref fonts
  for alignment in #["t", "c", "b"] do
    for (kind, body, before) in
        (bodies.map fun (kind, body) => (kind, body, "0pt")) ++ #[
          ("zero-before", "\\block[before=0pt]{\\begin{block}{}BODY\\end{block}}", "0pt"),
          ("positive-before", "\\block[before=7pt]{\\begin{block}{}BODY\\end{block}}", "7pt"),
          ("leading-vspace", "\\vspace{7pt}\\begin{block}{}BODY\\end{block}", "0pt"),
          ("leading-note", "\\note{SPEAKER}\\begin{block}{}BODY\\end{block}", "0pt"),
          ("note-before", "\\note{SPEAKER}\\block[before=7pt]{\\begin{block}{}BODY\\end{block}}",
            "7pt")] do
      let name := s!"block header clearance/{alignment}/{kind}"
      let (doc, diags) := Elab.run "frame-clearance.tex" (source alignment body)
      let out := layoutOf fonts doc
      let (head, nodes, htmlDiags) := HtmlDoc.emitTree { fonts := some fonts } doc
      let skip := doc.page.fontSize / 4 + if alignment == "t" then Dim.mm 2 else 0
      let pages := out.pages.filter (·.band.isSome)
      let stages := (elemNodesList (· == "section") #[] nodes.toList).filter
        (hasClass · "slide")
      let css := treeCssList "" head.toList
      check ref (name ++ ": source and both backends have no loss")
        ((diags ++ out.diags ++ htmlDiags).all (·.severity == .note))
      check ref (name ++ ": painted body clears the header by the declared skip")
        (!pages.isEmpty && pages.all fun page =>
          (paintedTop fonts page).any fun y => page.band.any fun band => band + skip ≤ y)
      check ref (name ++ ": first visible HTML box wins fixed plus authored opening")
        (stages.size == 1 &&
          stages.all (htmlOpeningClearance css · skip doc.page.height before))
      check ref (name ++ ": body survives in both artifacts")
        ((out.pages.flatMap (·.lines)).any (fun line => lineText line == "BODY") &&
          (nodeTextList "" nodes.toList).contains "BODY")
      -- A document skip opening the frame is a box of its own: it takes the
      -- opening, and the authored space is its height, a separate addend.
      if kind == "leading-vspace" then
        check ref (name ++ ": a leading skip takes the opening as a box as tall as the skip")
          (!stages.isEmpty && stages.all fun stage => match stage with
            | .elem _ _ kids => ((kids.filter participates)[0]?).any fun node =>
                hasClass node HtmlDoc.skipClass && hasClass node "frame-body-start" &&
                ((property (styleOf node) "--skip").bind remMilliOf ==
                  some (HtmlDoc.screenMilli doc.page.fontSize (Dim.pt 7) : Int))
            | .text _ | .style _ | .script .. => false)
      if kind == "leading-note" || kind == "note-before" then
        check ref (name ++ ": note remains hidden and cannot own the opening")
          ((elemNodesList (· == "aside") #[] nodes.toList).any fun node =>
            hasClass node "note" && !participates node && !hasClass node "frame-body-start")
  for alignment in #["t", "c", "b"] do
    for (kind, body, height) in #[
        ("empty-surface", "\\begin{block}{}\\end{block}", 240),
        ("dense-spill", "\\begin{block}{}" ++
          String.intercalate "\n\n" (List.replicate 18 "BODY") ++ "\\end{block}", 90)] do
      let name := s!"block header clearance/{alignment}/{kind}"
      let (doc, diags) := Elab.run "frame-clearance.tex" (source alignment body 12 height)
      let out := layoutOf fonts doc
      let (head, nodes, htmlDiags) := HtmlDoc.emitTree { fonts := some fonts } doc
      let skip := doc.page.fontSize / 4 + if alignment == "t" then Dim.mm 2 else 0
      let stages := (elemNodesList (· == "section") #[] nodes.toList).filter
        (hasClass · "slide")
      check ref (name ++ ": source and HTML have no loss")
        ((diags ++ htmlDiags).all (·.severity == .note))
      check ref (name ++ ": fixed opening remains on the visible HTML box")
        (stages.size == 1 &&
          stages.all (htmlOpeningClearance (treeCssList "" head.toList) · skip doc.page.height))
      check ref (name ++ ": first native surface clears its header")
        ((out.pages[0]?).any fun page =>
          (paintedTop fonts page).any fun y => page.band.any fun band => band + skip ≤ y)
      if kind == "dense-spill" then
        check ref (name ++ ": exceeds one native frame and reports the spill")
          (out.pages.size > 1 && out.diags.any (·.code == "W0384"))
        check ref (name ++ ": every continuation surface clears its repeated header")
          (out.pages.all fun page =>
            (headerBottom page).any fun band =>
              (paintedTop fonts page).any (band + skip ≤ ·))
        check ref (name ++ ": repeated header census agrees with its actual paint")
          (out.pages.all fun page => page.band == headerBottom page)
        check ref (name ++ ": all dense body paragraphs ship")
          (((out.pages.flatMap (·.lines)).filter (fun line => lineText line == "BODY")).size == 18)
      else
        check ref (name ++ ": empty body still ships a positive filled surface")
          (out.pages.any fun page => page.fills.any fun fill =>
            isSurface fill && 0 < fill.w && 0 < fill.h)
  let topY (body : String) : Option Dim.Sp :=
    let (doc, _) := Elab.run "frame-clearance.tex" (source "t" body)
    ((layoutOf fonts doc).pages[0]?).bind (paintedTop fonts)
  let unspaced := topY "\\begin{block}{}BODY\\end{block}"
  for (kind, body) in #[
      ("wrapper", "\\block[before=7pt]{\\begin{block}{}BODY\\end{block}}"),
      ("vspace", "\\vspace{7pt}\\begin{block}{}BODY\\end{block}")] do
    check ref ("block header clearance: native authored " ++ kind ++ " adds exactly once")
      ((unspaced.bind fun y => (topY body).map (· == y + Dim.pt 7)).getD false)

end Tests.BlockHeaderClearance
