module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.BlockGeometry

/-!
# A beamer block is the default inner theme's two colour boxes

beamerinnerthemedefault.sty sets every block as `\par\vskip\medskipamount`,
a title `beamercolorbox` and a body `beamercolorbox`, both `colsep*=.75ex`,
then `\vskip\smallskipamount`. A painted box stands `.75ex` above and below
its lines and its paint reaches `.75ex` beyond the text measure on both
sides, the text itself on the measure; a painted title meets a painted body
through `\nointerlineskip\vskip-0.5pt`; the body opens on a `\vbox{}`, so
its first baseline is one `\baselineskip` below the body box's top; the
boxes reset `\parskip` (`\@arrayparboxrestore`); an untitled block keeps
its empty title box; and TeX's interline glue spaces each box from the
band above (`\lineskip` where the boxes would collide).

Every distance below was measured under lualatex on this very source
(moloch, OpenSans Regular as the only face, 10pt): the table is the PDF's
own coordinates in big points converted to TeX points, the unit this
engine's `pt` stands for numerically. The checks read the shipped pages
(`Layout.Out`) and the typed HTML tree, never the IR.
-/

/-- Word spaces ship as gaps, not glyphs: a line is found by its letters. -/
private def letters (text : String) : String := text.replace " " ""

private def titleColor : Ir.Color := { r := 0xC9, g := 0xD6, b := 0xE8 }
private def bodyColor : Ir.Color := { r := 0xE8, g := 0xEE, b := 0xF6 }

/-- The invented probe: one frame per paint combination, `[t]` with room
to spare so every glue keeps its natural size. -/
def source : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n\\definecolor{probeTitle}{HTML}{C9D6E8}\n" ++
  "\\definecolor{probeSurface}{HTML}{E8EEF6}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setlength{\\parskip}{0.5em}\n\\begin{document}\n" ++
  "\\setbeamercolor{block title}{fg=probeInk,bg=probeTitle}\n" ++
  "\\setbeamercolor{block body}{fg=probeInk,bg=probeSurface}\n" ++
  "\\begin{frame}[t]{Painted}\nLead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\nBody words here.\n\nSecond body paragraph.\n\\end{block}\n" ++
  "\\begin{block}{Beta title words}\nThird body words.\n\\end{block}\n" ++
  "\\begin{block}{}\nUntitled body words.\n\\end{block}\nTrailing paragraph below.\n\\end{frame}\n" ++
  "\\setbeamercolor{block title}{bg=}\n\\setbeamercolor{block body}{bg=}\n" ++
  "\\begin{frame}[t]{Transparent}\nLead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\nBody words here.\n\\end{block}\n" ++
  "\\begin{block}{Beta title words}\nThird body words.\n\\end{block}\n" ++
  "\\begin{block}{}\nUntitled body words.\n\\end{block}\nTrailing paragraph below.\n\\end{frame}\n" ++
  "\\setbeamercolor{block title}{bg=probeTitle}\n\\setbeamercolor{block body}{bg=}\n" ++
  "\\begin{frame}[t]{Title Only}\nLead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\nBody words here.\n\\end{block}\n" ++
  "\\begin{block}{}\nUntitled body words.\n\\end{block}\nTrailing paragraph below.\n\\end{frame}\n" ++
  "\\setbeamercolor{block title}{bg=}\n\\setbeamercolor{block body}{bg=probeSurface}\n" ++
  "\\begin{frame}[t]{Body Only}\nLead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}\nBody words here.\n\\end{block}\n" ++
  "\\begin{block}{}\nUntitled body words.\n\\end{block}\nTrailing paragraph below.\n\\end{frame}\n" ++
  "\\setbeamercolor{block title}{bg=probeTitle}\n\\setbeamercolor{block body}{bg=probeSurface}\n" ++
  "\\begin{frame}[t]{Long Title}\n\\begin{block}{A very long block title that certainly " ++
  "wraps onto a second line of text because it keeps going and going}\nBody words here.\n" ++
  "\\end{block}\n\\end{frame}\n\\end{document}\n"

/-- lualatex's distances on `source`, in thousandths of a TeX point (the
PDF's big points times 72.27/72): what the shipped page must reproduce.
Each row names two marks on one page; a mark is a line's baseline, or a
fill's top or bottom edge. -/
private inductive Mark where
  | base (text : String)
  | top (color : Ir.Color) (n : Nat)
  | bottom (color : Ir.Color) (n : Nat)

private def measured : Array (Nat × Mark × Mark × Int) := #[
  -- Painted title and body: medskip and `\lineskip` above the title box,
  -- `.75ex` inside it, the body overlapping it by half a point and opening
  -- one `\baselineskip` below its top, no `\parskip` between its paragraphs.
  (0, .base "Lead paragraph above.", .top titleColor 0, 9402),
  (0, .top titleColor 0, .base "Alpha title words", 11611),
  (0, .base "Alpha title words", .bottom titleColor 0, 6416),
  (0, .bottom titleColor 0, .top bodyColor 0, -500),
  (0, .top bodyColor 0, .base "Body words here.", 12000),
  (0, .base "Body words here.", .base "Second body paragraph.", 12000),
  (0, .base "Second body paragraph.", .bottom bodyColor 0, 6416),
  -- Consecutive blocks stand smallskip, medskip and `\lineskip` apart.
  (0, .bottom bodyColor 0, .top titleColor 1, 10001),
  (0, .top titleColor 1, .base "Beta title words", 11611),
  (0, .base "Beta title words", .bottom titleColor 1, 4111),
  (0, .top bodyColor 1, .base "Third body words.", 12000),
  (0, .base "Third body words.", .bottom bodyColor 1, 6416),
  -- The untitled block keeps its empty title box, `1.5ex` tall, spaced
  -- by `\baselineskip` because it is shorter than one.
  (0, .bottom bodyColor 1, .top titleColor 2, 12974),
  (0, .top titleColor 2, .bottom titleColor 2, 8027),
  (0, .top bodyColor 2, .base "Untitled body words.", 12000),
  (0, .bottom bodyColor 2, .base "Trailing paragraph below.", 20000),
  -- Transparent boxes: the title spaced as text, the body box opening
  -- `.25ex` above its own top edge, an untitled block's empty title line.
  (1, .base "Lead paragraph above.", .base "Alpha title words", 18000),
  (1, .base "Alpha title words", .base "Body words here.", 14065),
  (1, .base "Body words here.", .base "Beta title words", 21000),
  (1, .base "Beta title words", .base "Third body words.", 12000),
  (1, .base "Third body words.", .base "Untitled body words.", 33000),
  (1, .base "Untitled body words.", .base "Trailing paragraph below.", 20000),
  -- A painted title above an unpainted body.
  (2, .base "Lead paragraph above.", .top titleColor 0, 9402),
  (2, .bottom titleColor 0, .base "Body words here.", 12000),
  (2, .base "Body words here.", .top titleColor 1, 12974),
  (2, .top titleColor 1, .bottom titleColor 1, 8027),
  (2, .bottom titleColor 1, .base "Untitled body words.", 12000),
  (2, .base "Untitled body words.", .base "Trailing paragraph below.", 20000),
  -- An unpainted title above a painted body: `\lineskip` between them.
  (3, .base "Lead paragraph above.", .base "Alpha title words", 18000),
  (3, .base "Alpha title words", .top bodyColor 0, 3403),
  (3, .top bodyColor 0, .base "Body words here.", 12000),
  (3, .base "Body words here.", .bottom bodyColor 0, 6416),
  (3, .bottom bodyColor 0, .top bodyColor 1, 22000),
  (3, .top bodyColor 1, .base "Untitled body words.", 12000),
  (3, .bottom bodyColor 1, .base "Trailing paragraph below.", 20000)]

/-- The `n`th box of a colour down the page: paint order is not reading order. -/
private def boxOf (page : Layout.PageOut) (c : Ir.Color) (n : Nat) : Option Layout.Fill :=
  ((page.fills.filter (·.color == c)).qsort (·.y < ·.y))[n]?

private def markY (page : Layout.PageOut) : Mark → Option Dim.Sp
  | .base text => (page.lines.find? fun l => !l.furniture && lineText l false == letters text).map (·.y)
  | .top c n => (boxOf page c n).map (·.y)
  | .bottom c n => (boxOf page c n).map fun f => f.y + f.h

private def milliOf (d : Dim.Sp) : Int := (d * 1000 + 32768) / 65536

/-- 0.02 pt: the reference's three-decimal big points, the TeX/big-point
conversion and TeX's sp rounding together stay under 0.005 pt; the rest is
margin for the font program's glyph bounds read by two decoders. -/
private def tolerance : Int := 20

private def layout (fonts : Font.FontSet) (src : String) : Layout.Out × Array Diag :=
  let (doc, diags) := Elab.run "block-geometry.tex" src
  (Layout.run (Layout.Geom.ofPage doc.page) fonts none doc, diags)

/-- Geometry the reference table cannot spell as a distance: the paint's
reach beyond the measure, the wrapped title's full cover, and the frame
opening a block spends. -/
private def shapeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (out : Layout.Out) : IO Unit := do
  let (doc, _) := Elab.run "block-geometry.tex" source
  let geom := Layout.Geom.ofPage doc.page
  let xh := fonts.body.xHeight * geom.fontSize / fonts.body.unitsPerEm
  let colsep := 3 * xh / 4
  let painted := out.pages.flatMap (·.fills) |>.filter fun f =>
    f.color == titleColor || f.color == bodyColor
  check ref "block geometry: some painted box ships" (painted.size ≥ 10)
  check ref "block geometry: paint reaches .75ex beyond the measure on both sides"
    (painted.all fun f => f.x == geom.hmargin - colsep &&
      f.w == geom.pageW - 2 * geom.hmargin + 2 * colsep)
  check ref "block geometry: block text stands on the measure"
    (out.pages.all fun page => page.lines.all fun l =>
      l.furniture || lineText l false != letters "Body words here." || l.x == geom.hmargin)
  -- The wrapped title: one box covers both lines, `.75ex` beyond their
  -- TeX boxes, the lines one `\baselineskip` apart.
  match out.pages[4]? with
  | some page =>
    let titles := page.lines.filter fun l =>
      !l.furniture && (lineText l false).startsWith "Avery" ||
        (!l.furniture && (lineText l false).endsWith "going")
    let bars := page.fills.filter (·.color == titleColor)
    check ref "block geometry: a wrapped title is two lines under one bar"
      (titles.size == 2 && bars.size == 1)
    match titles[0]?, titles[1]?, bars[0]? with
    | some first, some last, some bar =>
      let (h1, _) := Layout.segsInk fonts first.segs
      let (_, d2) := Layout.segsInk fonts last.segs
      check ref "block geometry: the bar covers the wrapped title's first line"
        (bar.y == first.y - h1 - colsep)
      check ref "block geometry: the bar covers the wrapped title's last line"
        (bar.y + bar.h == last.y + d2 + colsep)
      check ref "block geometry: wrapped title lines stand one baselineskip apart"
        (last.y - first.y == Dim.pt 12)
      -- The frame opens `\vskip-\parskip\vbox{}`; the block's medskip and
      -- `\lineskip` follow it (lualatex: 2 pt below the opening skip).
      let header := (page.fills.filter (·.color == { r := 0x23, g := 0x37, b := 0x3B : Ir.Color })).foldl
        (fun e f => max e (f.y + f.h)) 0
      check ref "block geometry: a frame's first block spends medskip less parskip"
        (bar.y == header + Layout.frameBodySkip true .top geom.fontSize + Dim.pt 2)
    | _, _, _ => check ref "block geometry: the wrapped title and its bar ship" false
  | none => check ref "block geometry: the wrapped-title frame ships" false

mutual
  private def nodeStyles (acc : Array String × String) : Html.Node → Array String × String
    | .elem _ attrs kids =>
      let acc := match attrs.find? (·.1 == "style") with
        | some (_, s) => (acc.1.push s, acc.2)
        | none => acc
      listStyles acc kids.toList
    | .style css => (acc.1, acc.2 ++ css)
    | .text _ | .script .. => acc
  private def listStyles (acc : Array String × String) : List Html.Node → Array String × String
    | [] => acc
    | node :: rest => listStyles (nodeStyles acc node) rest
end

/-- The browser twin: the same insets and skips as CSS on the typed tree. -/
private def htmlChecks (ref : IO.Ref (List String)) : IO Unit := do
  let (doc, _) := Elab.run "block-geometry.tex" source
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let (inline, sheet) := listStyles (#[], "") (head.toList ++ body.toList)
  check ref "block geometry HTML: the boxes' insets are .75ex, reaching beyond the measure"
    (HtmlDoc.titledBoxPaint == "padding: 0.75ex; margin-inline: -0.75ex;" &&
      HtmlDoc.titledBodyBoxPaint == "padding: 0 0.75ex 0.75ex; margin-inline: -0.75ex;")
  check ref "block geometry HTML: a painted title is padded all round"
    (inline.any fun s => hasStr s "background: #c9d6e8" && hasStr s HtmlDoc.titledBoxPaint)
  check ref "block geometry HTML: a painted body opens flush on its top"
    (inline.any fun s => hasStr s "background: #e8eef6" && hasStr s HtmlDoc.titledBodyBoxPaint)
  check ref "block geometry HTML: an untitled painted block keeps its band"
    (inline.any (· == s!"background: #c9d6e8; {HtmlDoc.titledBoxPaint}"))
  check ref "block geometry HTML: an untitled transparent block keeps its empty line"
    (inline.any (· == "min-height: 1lh;"))
  check ref "block geometry HTML: consecutive blocks stand apart"
    (hasStr sheet ":where(section.block + section.block) { margin-top:")
  check ref "block geometry HTML: a block's paragraphs spend no parskip"
    (hasStr sheet ":where(section.block > *) { --parskip: 0rem; }")

/-- The shipped block paint and title ink of a three-kind frame, in page
order: what the colour checks compare between spellings. -/
private def blockPaint (fonts : Font.FontSet) (src : String) :
    Array Ir.Color × Array (Option Ir.Color) × Array Diag :=
  let (out, diags) := layout fonts src
  let page := out.pages[0]?.getD {}
  let paint := ((page.fills.filter fun f => f.x != 0).qsort (·.y < ·.y)).map (·.color)
  let ink := #["Plain", "Loud", "Shown"].map fun title =>
    (page.lines.find? (lineText · false == title)).bind fun l => l.segs.findSome? fun
      | .run _ c _ _ _ _ _ _ _ _ _ => some c
      | _ => none
  (paint, ink, diags ++ out.diags)

/-- Block colours resolve as beamer resolves them: moloch's `block=fill`
option, in either spelling, is moloch's own declarations; an empty value
clears a channel; the alerted and example bodies inherit the block body
(moloch) and the titles inherit `structure` and the text roles (beamer's
default colour theme). Read on the shipped page, against lualatex's fills
on the same frame: a title bar of `#CFD3D4`, bodies of `#E4E6E7`. -/
private def colorChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let pre := "\\documentclass{beamer}\n"
  let frame := "\\begin{document}\\begin{frame}[t]{F}\\begin{block}{Plain}P\\end{block}" ++
    "\\begin{alertblock}{Loud}A\\end{alertblock}" ++
    "\\begin{exampleblock}{Shown}E\\end{exampleblock}\\end{frame}\\end{document}\n"
  let spelled := pre ++ "\\usetheme{moloch}\n" ++
    "\\setbeamercolor{block title}{use=normal text,fg=normal text.fg,bg=normal text.bg!80!fg}\n" ++
    "\\setbeamercolor{block body}{use=block title,bg=block title.bg!50!normal text.bg}\n" ++
    "\\setbeamercolor{block title alerted}{use={block title,alerted text},bg=block title.bg}\n" ++
    "\\setbeamercolor{block title example}{use={block title,example text},bg=block title.bg}\n" ++
    "\\setbeamercolor{block body alerted}{use=block body,parent=block body}\n" ++
    "\\setbeamercolor{block body example}{use=block body,parent=block body}\n" ++ frame
  let (paint, ink, _) := blockPaint fonts spelled
  let title : Ir.Color := { r := 0xCF, g := 0xD3, b := 0xD4 }
  let body : Ir.Color := { r := 0xE4, g := 0xE6, b := 0xE7 }
  let near (a b : Ir.Color) : Bool :=
    (a.r.toNat - b.r.toNat) + (b.r.toNat - a.r.toNat) ≤ 1 &&
      (a.g.toNat - b.g.toNat) + (b.g.toNat - a.g.toNat) ≤ 1 &&
      (a.b.toNat - b.b.toNat) + (b.b.toNat - a.b.toNat) ≤ 1
  check ref "block colours: moloch's fill paints six boxes, titles and bodies alternating"
    (paint.size == 6 && (paint.toList.zipIdx.all fun (c, i) =>
      if i % 2 == 0 then c == title else near c body))
  let fg := ((Theme.find? "moloch").map (·.palette)).bind (·.find? "fg")
  check ref "block colours: titles take structure's and the text roles' ink"
    (ink[0]? == some fg && fg.isSome && ink.all Option.isSome &&
      ink[1]? != ink[0]? && ink[2]? != ink[0]? && ink[1]? != ink[2]?)
  for (name, src) in #[("usetheme option", pre ++ "\\usetheme[block=fill]{moloch}\n" ++ frame),
      ("molochset", pre ++ "\\usetheme{moloch}\n\\molochset{block=fill}\n" ++ frame),
      ("metropolisset", pre ++ "\\usetheme{metropolis}\n\\metropolisset{block=fill}\n" ++ frame)] do
    let (p, i, ds) := blockPaint fonts src
    check ref s!"block colours: the {name} spelling is moloch's own declarations"
      (p == paint && i == ink)
    check ref s!"block colours: the {name} spelling raises nothing about the option"
      (ds.all fun d => d.code != "W0104" && d.code != "W0301")
  let (cleared, _, ds) := blockPaint fonts
    (pre ++ "\\usetheme[block=fill]{moloch}\n\\molochset{block=transparent}\n" ++ frame)
  check ref "block colours: moloch's transparent option clears every box"
    (cleared.isEmpty && ds.all (·.code != "W0104"))
  let (inherited, _, _) := blockPaint fonts
    (pre ++ "\\usetheme{moloch}\n" ++
      "\\setbeamercolor{block body}{use=normal text,bg=normal text.bg!90!fg}\n" ++ frame)
  check ref "block colours: the alerted and example bodies inherit the block body"
    (inherited.size == 3 && inherited.all (· == inherited[0]!))

/-- beamer's transparent covering mixes every colour a covered step uses
with the page (`\opaqueness`, beamerbaseoverlay.sty), a block's colour
boxes and heading ink included: on the step that does not show it, a block
after `\pause` ships its bars and heading at their cover, the cover the
engine gives every covered colour (`Ir.Design.cover`), within the ink bound
of xcolor's mix; on the step that shows it, its own colours. -/
private def coveredChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let src := "\\documentclass{beamer}\n\\setbeamercovered{transparent}\n" ++
    "\\definecolor{probeInk}{HTML}{1F2A44}\n\\definecolor{probeSurface}{HTML}{E8EEF6}\n" ++
    "\\setbeamercolor{block title}{fg=white,bg=probeInk}\n" ++
    "\\setbeamercolor{block body}{fg=probeInk,bg=probeSurface}\n\\begin{document}\n" ++
    "\\begin{frame}[t]{Steps}\n\\begin{block}{Plain}Early words.\\end{block}\n\\pause\n" ++
    "\\begin{block}{Later}Late words.\\end{block}\n\\end{frame}\n\\end{document}\n"
  let (doc, _) := Elab.run "block-covered.tex" src
  let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
  let cover := (Ir.Design.ofDoc doc).cover
  let page := (doc.palette.find? "bg").getD Ir.Color.white
  let ink : Ir.Color := { r := 0x1F, g := 0x2A, b := 0x44 }
  let surface : Ir.Color := { r := 0xE8, g := 0xEE, b := 0xF6 }
  let paint (p : Nat) : Array Ir.Color :=
    let pg := out.pages[p]?.getD {}
    ((pg.fills.filter fun f => f.x != 0).qsort (·.y < ·.y)).map (·.color)
  let headingInk (p : Nat) : Option Ir.Color :=
    ((out.pages[p]?.getD {}).lines.find? (lineText · false == "Later")).bind fun l =>
      l.segs.findSome? fun
        | .run _ c _ _ _ _ _ _ _ _ _ => some c
        | _ => none
  check ref "block covering: one page per step" (out.pages.size == 2)
  check ref "block covering: the shown block keeps its own boxes on the first step"
    ((paint 0)[0]? == some ink && (paint 0)[1]? == some surface)
  check ref "block covering: a covered block's boxes ship at their cover"
    ((paint 0)[2]? == some (cover.of ink) && (paint 0)[3]? == some (cover.of surface))
  check ref "block covering: a covered block's heading ink ships at its cover"
    (headingInk 0 == some (cover.of Ir.Color.white))
  check ref "block covering: the covered boxes lie within the ink bound of xcolor's mix"
    (Contrast.deltaEOkSq (ink.mix 15 page) (cover.of ink) ≤ Contrast.inkBoundSq &&
      Contrast.deltaEOkSq (surface.mix 15 page) (cover.of surface) ≤ Contrast.inkBoundSq)
  check ref "block covering: the step that shows the block ships its own colours"
    (paint 1 == #[ink, surface, ink, surface] && headingInk 1 == some Ir.Color.white)

def blockGeometryChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (out, diags) := layout fonts source
  check ref "block geometry: the probe elaborates without loss"
    (diags.all (·.severity == .note) && out.diags.all (·.severity == .note))
  check ref "block geometry: one page per frame" (out.pages.size == 5)
  for (page, a, b, want) in measured do
    match out.pages[page]?.bind (fun p => (markY p a).bind fun ya => (markY p b).map (· - ya)) with
    | some d =>
      check ref s!"block geometry: page {page + 1} distance {want} (lualatex) got {milliOf d}"
        ((milliOf d - want).natAbs ≤ tolerance.toNat)
    | none => check ref s!"block geometry: page {page + 1} marks for {want} ship" false
  shapeChecks ref fonts out
  htmlChecks ref
  colorChecks ref fonts
  coveredChecks ref fonts
  let transparent := out.pages[1]?.getD {}
  check ref "block geometry: empty colour values clear the transparent frame's boxes"
    (transparent.fills.all fun f => f.color != titleColor && f.color != bodyColor)

end Tests.BlockGeometry
