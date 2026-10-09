import Tests.Support
import Tests.DriverAssets

open LeanTex.Core

namespace PictureMathLabels

/-- Invented labels exercise empty nuclei as well as ordinary mathematical
structure. The expected leaves are painted characters, not a linear reading
of the formula: a superscript contributes no parentheses or caret. -/
def mathLabelCases : Array (String × String × String) := #[
  ("Maple$'$", "Maple′", "msup"),
  ("Birch$''$", "Birch′′", "msup"),
  ("Cedar$_r$", "Cedar𝑟", "msub"),
  ("Elm$^{2}$", "Elm2", "msup"),
  ("Ash$\\frac{3}{7}$", "Ash37", "mfrac"),
  ("Pine$\\sqrt{z}$", "Pine𝑧", "msqrt")]

end PictureMathLabels

/-- **Parsed picture mathematics keeps its structure on the shipped page.**
The native page must retain and raise an orphan script after text. The
typed HTML must paint the same letters and a native script, fraction or
radical, without introducing the punctuation of a plaintext serialization.
The label retains the shared measured baseline, every horizontal anchor,
and visible overflow. This guard fails on the structural-text SVG fallback.
It reads `Layout.Out` and the emitted HTML tree, never an IR dump.
Invented content throughout. -/
def pictureMathLabelChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let attr := fun (node : Html.Node) (key : String) =>
    match node with
    | .elem _ attrs _ => HtmlDoc.attrOf? attrs key
    | _ => none
  let fs ← mathSetOf oneFace
  t "picture mathematics: the bundled math face loads" fs.math.isSome
  for (label, leaves, schema) in PictureMathLabels.mathLabelCases do
    let (base, ds) := elabMeasured fs (mathLabelSource label "")
    let pics := docPictures base
    t s!"picture mathematics: {label} parses one picture without loss"
      (pics.size == 1 &&
        !ds.any fun d => ["W0012", "W0334", "E0333", "W0335"].contains d.code)
    let some original := pics[0]? | continue
    for (side, align) in #[("center", Ir.Pic.LabelAlign.center), ("west", .west),
        ("east", .east), ("north", .north), ("south", .south)] do
      for scale in (#[700, 1000, 1600] : Array Nat) do
        let pic := { original with shapes := original.shapes.map fun shape =>
          match shape with
          | .label x y content color _ _ => .label x y content color scale align
          | _ => shape }
        let doc := { base with
          body := #[.picture pic], tokens := base.tokens.declare "topskip" {} }
        let geom := Layout.Geom.ofPage doc.page
        let out := layoutOf fs doc
        let cfg : HtmlDoc.Config := {
          fonts := some fs, page := doc.page, labelMetric := Layout.labelMetric geom fs }
        let svgs := #[HtmlDoc.pictureSvg cfg pic]
        let name := s!"picture mathematics: {label}/{side}/{scale}"
        t (name ++ " ships one native label") ((bodyLines out).size == 1)
        for svg in svgs do
          t (name ++ " publishes as self-contained typed HTML")
            ((HtmlResource.close #[] #[] HtmlDoc.deckScript "en" #[] #[svg]).isOk)
          t (name ++ " paints exactly the mathematical leaves")
            (String.ofList (MathMl.nodeChars #[] svg).toList == leaves)
          t (name ++ " preserves its native mathematical schema")
            (!(elemNodesOne (· == schema) #[] svg).isEmpty)
          t (name ++ " never clips the label")
            (attr svg "overflow" == some "visible")
          -- Both formatting contexts need a zero-size font strut. A
          -- nonzero outer math font can move its baseline below the
          -- declared y even when mpadded itself has zero height/depth.
          let carriers := elemNodesOne (· == "foreignObject") #[] svg
          t (name ++ " separates the zero-size carrier from the label font")
            (!carriers.isEmpty && carriers.all fun carrier =>
              match carrier with
              | .elem _ _ #[.elem "div" _ #[.elem "math" outer
                  #[.elem "mpadded" padded #[.elem "mrow" inner _]]]] =>
                HtmlDoc.attrOf? outer "style" ==
                  some "font-size: 0; font-family: inherit" &&
                HtmlDoc.attrOf? padded "height" == some "0px" &&
                HtmlDoc.attrOf? padded "depth" == some "0px" &&
                HtmlDoc.attrOf? inner "style" ==
                  some s!"font-size: {(Ir.baseFontSize * (scale : Int) / 1000).toPtString}px"
              | _ => false)
        -- Layout's first run must keep the leading letter. For scripts,
        -- measure the emitted glyphs, not a source spelling or a box guess.
        let glyphs := shippedBodyGlyphs out
        t (name ++ " keeps its first native letter")
          ((glyphs[0]?.map (·.scalar)) == leaves.toList.head?)
        if schema == "msup" then
          let primes := glyphs.filter fun g => g.scalar == '′' || g.scalar == '2'
          let first := glyphs[0]?
          t (name ++ " ships an elevated native superscript")
            (!primes.isEmpty && primes.all fun g =>
              first.any fun f => g.y < f.y && g.size < f.size)
        for shape in pic.shapes do
          match shape with
          | .label x y content color size align =>
            let metric := Layout.labelMetric geom fs
            let emitted := HtmlDoc.pictureKids pic (pic.box metric).1.1
              (pic.box metric).2.2 metric
            let baselines := emitted.filterMap fun n =>
              attr n "y"
            let baseline := (pic.box metric).2.2 -
              Ir.Pic.labelBaseline y align (metric content size)
            t (name ++ " retains the shared alphabetic baseline")
              (baselines.contains baseline.toPtString &&
                (bodyLines out)[0]?.any fun l => l.y - geom.vmargin == baseline)
            -- Give the label a box narrower than its ink: both artifacts
            -- must still retain the whole leading word.
            let small : Ir.Pic.Picture := {
              shapes := #[.label x y content color size align]
              declared := some ((0, 0), (Dim.pt 1, Dim.pt 1)) }
            let narrow := HtmlDoc.pictureSvg cfg small
            t (name ++ " retains ink outside a declared box")
              (attr narrow "overflow" == some "visible" &&
                String.ofList (MathMl.nodeChars #[] narrow).toList == leaves)
          | _ => pure ()
  -- Styling may surround both text and math. The script still owns its
  -- mathematical structure under face resets, nested emphasis and colour.
  for label in #["\\textbf{Maple$'$}", "\\textit{\\emph{Maple}$'$}",
      "\\textbf{\\textnormal{Maple}$'$}", "\\textcolor{red}{Maple$'$}"] do
    let (doc, _) := elabMeasured fs (mathLabelSource label "")
    let cfg : HtmlDoc.Config := {
      fonts := some fs, labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs }
    let svgs := elemNodesList (· == "svg") #[] (HtmlDoc.emitTree cfg doc).2.1.toList
    t s!"picture mathematics: styled label {label} preserves text and the script"
      (svgs.size == 1 && svgs.all fun svg =>
        String.ofList (MathMl.nodeChars #[] svg).toList == "Maple′" &&
          !(elemNodesOne (· == "msup") #[] svg).isEmpty)
  -- The generated carrier is transparent to dependency checking, never a
  -- way to admit opaque HTML or to reset the SVG raw-text context.
  let carrier := fun (attrs : Array (String × String)) (kids : Array Html.Node) =>
    Html.elem "svg" #[Html.elem "foreignObject"
      #[Html.elem "div" kids #[("xmlns", "http://www.w3.org/1999/xhtml")]] attrs]
  let admits := fun (node : Html.Node) =>
    (HtmlResource.close #[] #[] HtmlDoc.deckScript "en" #[] #[node]).isOk
  t "picture mathematics: the checked carrier accepts escaped passive text"
    (admits (carrier #[] #[.text "<Maple & Birch>"]))
  for (name, child) in #[
      ("image URL", Html.elem "img" #[] #[("src", "https://example.invalid/pixel.png")]),
      ("raw style", Html.Node.style "mtext { color: red }"),
      ("raw script", Html.Node.script #[] HtmlDoc.deckScript),
      ("active element", Html.elem "iframe" #[]),
      ("event attribute", Html.elem "span" #[] #[("onclick", "alert(1)")])] do
    t ("picture mathematics: the carrier still refuses " ++ name)
      (!(admits (carrier #[] #[child])))
  t "picture mathematics: the carrier's own attributes are checked"
    (!(admits (carrier #[("onload", "alert(1)")] #[])))

namespace PictureMathLabels

/-- Invented contents a picture label and a paragraph both set: a math
alphabet from each family the resolver distinguishes — text-sourced
upright, bold, sans, italic and mono, symbol-sourced double-struck and
script — and an alphabet under a colour and inside a text style. -/
def alphabetLabelCases : Array String := #[
  "$\\mathrm{Fir}$", "$\\mathbf{v}$", "$\\mathsf{Q}$", "$\\mathit{ab}$", "$\\mathtt{k}$",
  "$\\mathbb{R}$", "$\\mathcal{A}$", "\\textcolor{red}{$\\mathrm{Fir}$}",
  "\\textbf{Elm $\\mathrm{Fir}$}"]

/-- The same content as a paragraph. -/
def paragraphSource (content : String) : String :=
  "\\documentclass{article}\\begin{document}\n" ++ content ++ "\n\\end{document}"

/-- On the shipped page of a document drawing one outlined node: the gaps
from the outline the layout strokes to the label line it sets, left and
right. The outline was placed at elaboration; the line is the label as the
page paints it. -/
def outlineGaps (out : Layout.Out) : Option (Dim.Sp × Dim.Sp) := do
  let page ← out.pages[0]?
  let (x, w) ← page.paths.findSome? fun q => match q.path with
    | .rect x _ w _ => some (x, w)
    | _ => none
  let line ← (page.lines.filter (!·.furniture))[0]?
  return (line.x - x, x + w - (line.x + line.setWidth))

end PictureMathLabels

/-- **A label's formula paints what the same formula paints in a
paragraph**, on both artifacts. A math alphabet resolves in a picture label
exactly as it resolves in prose: the typed HTML tree carries the paragraph's
MathML glyph text and no `merror`, the native page ships the paragraph's
scalars, and every shipped `math` element is its tree's only root. Before
alphabet resolution reached picture labels, a label's alphabet shipped as an
unresolved node — an `merror` around the source glyphs in HTML, which a
browser frames in red on yellow, and the source italic on the page — and the
label's carrier nested each formula's own `math` root. A drawn outline,
placed at elaboration, stands a text node's inner sep clear of the label
line the page sets (the measure behind it is `Layout.labelMetric_resolve_id`).
Reads `Layout.Out` and the emitted HTML tree, never an IR dump. Invented
content. -/
def pictureAlphabetLabelChecks (ref : IO.Ref (List String))
    (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let fs ← mathSetOf oneFace
  let cfgOf := fun (doc : Ir.Doc) => ({
    fonts := some fs, page := doc.page
    labelMetric := Layout.labelMetric (Layout.Geom.ofPage doc.page) fs } : HtmlDoc.Config)
  let scalars := fun (out : Layout.Out) => String.ofList (shippedBodyGlyphs out |>.map (·.scalar)).toList
  for content in PictureMathLabels.alphabetLabelCases do
    let name := s!"picture alphabet: {content}"
    let (prose, _) := elabMeasured fs (PictureMathLabels.paragraphSource content)
    let (label, _) := elabMeasured fs (mathLabelSource content "")
    t (name ++ " elaborates one picture")
      ((docPictures label).size == 1)
    let (_, proseBody, _) := HtmlDoc.emitTree (cfgOf prose) prose
    let (_, labelBody, _) := HtmlDoc.emitTree (cfgOf label) label
    let proseFormulas := formulaElems proseBody
    let labelFormulas := formulaElems labelBody
    t (name ++ " paints the paragraph's MathML glyphs in its label")
      (!proseFormulas.isEmpty && proseFormulas.size == labelFormulas.size &&
        MathMl.nodeListChars #[] labelFormulas.toList ==
          MathMl.nodeListChars #[] proseFormulas.toList)
    t (name ++ s!" ships no merror \
({(elemNodesList (· == "merror") #[] labelBody.toList).size})")
      (MathMl.tagFreeList (· == "merror") labelBody.toList)
    t (name ++ s!" ships one math root, unnested \
({(elemNodesList (· == "math") #[] labelBody.toList).size} math elements)")
      (MathMl.unnestedList labelBody.toList &&
        (elemNodesList (· == "math") #[] labelBody.toList).size == 1)
    let proseOut := layoutOf fs prose
    let labelOut := layoutOf fs label
    t (name ++ s!" sets the paragraph's scalars on the page \
({scalars labelOut} against {scalars proseOut})")
      (!(scalars proseOut).isEmpty && scalars labelOut == scalars proseOut)
  -- **A drawn outline stands its inner sep clear of the label the page
  -- sets.** The outline is placed at elaboration; the line is the label the
  -- page paints, its alphabet resolved. Against a plain-text node, each gap
  -- is the same, to the rounding of a halved width.
  let gapsOf := fun (content : String) =>
    let (doc, _) := elabMeasured fs (drawnNodeSource content)
    PictureMathLabels.outlineGaps (layoutOf fs doc)
  let plain := gapsOf "W"
  t s!"picture alphabet: a text node ships its outline and label line ({plain})" plain.isSome
  for content in #["$\\mathbf{W}$", "$\\mathrm{Fir}$", "$\\mathsf{Q}$", "$\\mathtt{k}$"] do
    let alphabet := gapsOf content
    t s!"picture alphabet: a drawn node around {content} stands a text node's inner sep \
clear of its shipped label ({alphabet} against {plain})"
      (match plain, alphabet with
       | some (l, r), some (l', r') => (l - l').natAbs ≤ 2 && (r - r').natAbs ≤ 2
       | _, _ => false)
  -- A display formula set in a carrier keeps its display style on the row:
  -- the display root's children, `displaystyle` where the root declares
  -- `display="block"`, and nothing for an inline row.
  let (displayDoc, _) := elabStr (PictureMathLabels.paragraphSource "\\[\\frac{1}{2}\\]")
  let displayBody := firstFormula displayDoc
  t "picture alphabet: a display formula parses for the row probe" displayBody.isSome
  if let some body := displayBody then
    let render := fun (kids : Array Html.Node) => String.join (kids.toList.map (Html.render · 0))
    t "picture alphabet: a display row carries the display root's children and style"
      (match MathMl.formula true #[] body, MathMl.formulaRow true #[] body,
          MathMl.formulaRow false #[] body with
       | .elem "math" rootAttrs rootKids, .elem "mrow" rowAttrs rowKids,
           .elem "mrow" inlineAttrs _ =>
         HtmlDoc.attrOf? rootAttrs "display" == some "block" &&
           HtmlDoc.attrOf? rowAttrs "displaystyle" == some "true" &&
           (HtmlDoc.attrOf? inlineAttrs "displaystyle").isNone &&
           render rowKids == render rootKids
       | _, _, _ => false)

/-- **The driver settles on the labels elaboration measured.** A document
elaborated against a provisional face stands only where the settled face
measures every label elaboration measured as the provisional face did. Font
assembly returns the document resolved against the settled face's coverage,
whose labels are not those calls: where the settled face lacks an alphabet
the provisional face carries, the resolved label sets the source glyphs,
which both faces measure alike, while the label elaboration measured — the
alphabet — measures differently, so the drawn outline around it would stand
sized for glyphs the page never sets. Invented content. -/
def labelSettleChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let carried ← mathSetOf oneFace
  let lacking : Font.FontSet := { carried with mathAlphabets := {} }
  -- A symbol-sourced alphabet: the math face's own coverage decides it.
  let src := drawnNodeSource "$\\mathbb{R}$"
  let (elaborated, _) := elabMeasured carried src
  let geom := Layout.Geom.ofPage elaborated.page
  let pre := Layout.labelMetric geom carried
  let resolvedBy := fun (fs : Font.FontSet) =>
    (Ir.resolveMathAlphas fs.mathAlphabets "math face" elaborated).1
  t "label settle: the provisional face, settled on, holds"
    (← Tests.DriverAssets.settles elaborated (some pre) carried (resolvedBy carried))
  t "label settle: a settled face lacking the label's alphabet supersedes it"
    !(← Tests.DriverAssets.settles elaborated (some pre) lacking (resolvedBy lacking))
  t "label settle: the resolved labels would hide that, measuring alike under both"
    (LeanTex.Cli.FontFix.agree pre (Layout.labelMetric geom lacking)
      (LeanTex.Cli.FontFix.probes (resolvedBy lacking).body))
  t "label settle: with no provisional face, a drawn picture is elaborated again"
    !(← Tests.DriverAssets.settles elaborated none carried (resolvedBy carried))
