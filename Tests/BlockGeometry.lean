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

/-- The `margin-top` of the gap sheet's first rule whose selector holds
every fragment. -/
private def ruleValue (sheet : String) (frags : List String) : Option String :=
  (sheet.splitOn "\n").findSome? fun l =>
    if l.startsWith ":where(" && frags.all (hasStr l ·) then
      match l.splitOn "{ margin-top: " with
      | [_, v] => some ((v.splitOn ";").headD "")
      | _ => none
    else none

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
    ((ruleValue sheet ["section.block:last-child)) + :is(section.block"]).isSome)
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

/-- Each colour theme's own relationships, and only its own. beamer's
default colour theme (beamercolorthemedefault.sty) leaves the alerted and
example bodies empty and hangs the block title on `structure`, the frame
title on `titlelike` and `titlelike` on `structure`; moloch's
(beamercolorthememoloch.sty, `\moloch@setup@block@colors`) gives the block
title normal text's ink and no fill whatever `structure` holds, and the
alerted and example bodies the block body's colours. lualatex on these
frames: one body fill under the default theme and three under moloch; the
plain title and the frame title in `structure`'s colour under the default
theme, the plain title in normal text's under moloch. -/
private def parentChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let frame := "\\begin{document}\\begin{frame}[t]{Kinds}\\begin{block}{Plain}P\\end{block}" ++
    "\\begin{alertblock}{Loud}A\\end{alertblock}" ++
    "\\begin{exampleblock}{Shown}E\\end{exampleblock}\\end{frame}\\end{document}\n"
  let plain := "\\documentclass{beamer}\n"
  let moloch := "\\documentclass{beamer}\n\\usetheme{moloch}\n"
  let surface : Ir.Color := { r := 0xE8, g := 0xEE, b := 0xF6 }
  let accent : Ir.Color := { r := 0x7A, g := 0x3E, b := 0x9D }
  let body := "\\definecolor{probeSurface}{HTML}{E8EEF6}\n" ++
    "\\setbeamercolor{block body}{bg=probeSurface}\n"
  let accentDecl := "\\definecolor{probeAccent}{HTML}{7A3E9D}\n" ++
    "\\setbeamercolor{structure}{fg=probeAccent}\n"
  let (plainBodies, _, _) := blockPaint fonts (plain ++ body ++ frame)
  check ref "block parents: under beamer's default theme only the plain body is painted"
    (plainBodies == #[surface])
  let (molochBodies, _, _) := blockPaint fonts (moloch ++ body ++ frame)
  check ref "block parents: under moloch the alerted and example bodies inherit the block body"
    (molochBodies == #[surface, surface, surface])
  let (plainDoc, _) := Elab.run "block-parents.tex" (plain ++ frame)
  let (_, plainInk, _) := blockPaint fonts (plain ++ accentDecl ++ frame)
  check ref "block parents: the default theme's block title takes structure's ink"
    (plainInk == #[some accent, plainDoc.palette.find? "alert", plainDoc.palette.find? "example"])
  let (out, _) := layout fonts (plain ++ accentDecl ++ frame)
  let page := out.pages[0]?.getD {}
  let titleInk := (page.lines.find? (lineText · false == "Kinds")).bind fun l =>
    l.segs.findSome? fun
      | .run _ c _ _ _ _ _ _ _ _ _ => some c
      | _ => none
  check ref "block parents: the default theme's frame title takes structure's ink"
    (titleInk == some accent)
  let bundle := (Theme.find? "moloch").map (·.palette)
  let (_, molochInk, _) := blockPaint fonts (moloch ++ accentDecl ++ frame)
  check ref "block parents: moloch's block title keeps normal text's ink whatever structure holds"
    (molochInk == #[bundle.bind (·.find? "fg"), bundle.bind (·.find? "alert"),
      bundle.bind (·.find? "example")])

/-- A block an overlay item holds is covered with its item, whether it
opens the item or follows the item's paragraph: on the steps before the
item's, its boxes and heading ink ship at their cover, on the item's step
and after at their own colours, and no step moves a box (cover, not hide).
lualatex on this frame covers both blocks' bars and bodies on every step
that does not show their item. -/
private def coveredItemChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let src := "\\documentclass{beamer}\n\\usetheme{moloch}\n\\setbeamercovered{transparent}\n" ++
    "\\definecolor{probeInk}{HTML}{1F2A44}\n\\definecolor{probeSurface}{HTML}{E8EEF6}\n" ++
    "\\setbeamercolor{block title}{fg=white,bg=probeInk}\n" ++
    "\\setbeamercolor{block body}{fg=probeInk,bg=probeSurface}\n\\begin{document}\n" ++
    "\\begin{frame}[t]{Items}\n\\begin{itemize}\n\\item<1-> First item words.\n" ++
    "\\item<2-> \\begin{block}{Inside}Item block words.\\end{block}\n" ++
    "\\item<3-> Lead item words.\n\\begin{block}{After}Trailing block words.\\end{block}\n" ++
    "\\end{itemize}\n\\end{frame}\n\\end{document}\n"
  let (doc, _) := Elab.run "block-covered-items.tex" src
  let out := Layout.run (Layout.Geom.ofPage doc.page) fonts none doc
  let cover := (Ir.Design.ofDoc doc).cover
  let ink : Ir.Color := { r := 0x1F, g := 0x2A, b := 0x44 }
  let surface : Ir.Color := { r := 0xE8, g := 0xEE, b := 0xF6 }
  let boxes (p : Nat) : Array Layout.Fill :=
    ((out.pages[p]?.getD {}).fills.filter fun f => f.x != 0).qsort (·.y < ·.y)
  let headingInk (p : Nat) (title : String) : Option Ir.Color :=
    ((out.pages[p]?.getD {}).lines.find? (lineText · false == title)).bind fun l =>
      l.segs.findSome? fun
        | .run _ c _ _ _ _ _ _ _ _ _ => some c
        | _ => none
  let shown := #[ink, surface]
  let covered := #[cover.of ink, cover.of surface]
  check ref "block covered items: one page per step" (out.pages.size == 3)
  check ref "block covered items: the first step covers both items' blocks"
    ((boxes 0).map (·.color) == covered ++ covered)
  check ref "block covered items: the second step shows the block its item opens"
    ((boxes 1).map (·.color) == shown ++ covered)
  check ref "block covered items: the third step shows both"
    ((boxes 2).map (·.color) == shown ++ shown)
  check ref "block covered items: a covered heading ships at its cover"
    (headingInk 0 "Inside" == some (cover.of Ir.Color.white) &&
      headingInk 1 "Inside" == some Ir.Color.white &&
      headingInk 1 "After" == some (cover.of Ir.Color.white) &&
      headingInk 2 "After" == some Ir.Color.white)
  let place (p : Nat) := (boxes p).map fun f => (f.x, f.y, f.w, f.h)
  check ref "block covered items: no step moves a box"
    ((boxes 0).size == 4 && place 0 == place 1 && place 1 == place 2)

/-- The block template spends the registers in force, never their kernel
values: `\vskip\medskipamount` above the title box and `\vskip
\smallskipamount` below the body box (beamerinnerthemedefault.sty) take the
document's 20 pt and 15 pt as `\medskip` does. lualatex's distances on this
source, in thousandths of a TeX point. -/
private def skipSource : String :=
  "\\documentclass[10pt,aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
  "\\definecolor{probeInk}{HTML}{1F2A44}\n\\definecolor{probeTitle}{HTML}{C9D6E8}\n" ++
  "\\definecolor{probeSurface}{HTML}{E8EEF6}\n" ++
  "\\setbeamercolor{normal text}{fg=probeInk,bg=white}\n" ++
  "\\setbeamercolor{block title}{fg=probeInk,bg=probeTitle}\n" ++
  "\\setbeamercolor{block body}{fg=probeInk,bg=probeSurface}\n" ++
  "\\setlength{\\medskipamount}{20pt}\n\\setlength{\\smallskipamount}{15pt}\n" ++
  "\\begin{document}\n\\begin{frame}[t]{Skips}\nLead paragraph above.\n" ++
  "\\begin{block}{Alpha title words}Body words here.\\end{block}\n" ++
  "\\begin{block}{Beta title words}Third body words.\\end{block}\n" ++
  "Trailing paragraph below.\n\n\\medskip\n\nAfter the medium skip.\n\\end{frame}\n\\end{document}\n"

private def skipMeasured : Array (Mark × Mark × Int) := #[
  (.base "Lead paragraph above.", .top titleColor 0, 23402),
  (.top titleColor 0, .base "Alpha title words", 11611),
  (.bottom bodyColor 0, .top titleColor 1, 36000),
  (.bottom bodyColor 1, .base "Trailing paragraph below.", 27000),
  (.base "Trailing paragraph below.", .base "After the medium skip.", 32001)]

/-- `m` thousandths as `HtmlDoc`'s rem text. -/
private def remText (m : Nat) : String :=
  let frac := toString (m % 1000)
  s!"{m / 1000}.{"".pushn '0' (3 - frac.length) ++ frac}rem"

private def skipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let (out, _) := layout fonts skipSource
  for (a, b, want) in skipMeasured do
    match out.pages[0]?.bind (fun p => (markY p a).bind fun ya => (markY p b).map (· - ya)) with
    | some d =>
      check ref s!"block skips: distance {want} (lualatex) got {milliOf d}"
        ((milliOf d - want).natAbs ≤ tolerance.toNat)
    | none => check ref s!"block skips: marks for {want} ship" false
  let (doc, _) := Elab.run "block-skips.tex" skipSource
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let (_, sheet) := listStyles (#[], "") (head.toList ++ body.toList)
  let size := doc.page.fontSize
  let above := remText (HtmlDoc.screenMilli size (Dim.pt 20 + Layout.inkClearance))
  let below := remText (HtmlDoc.screenMilli size (Dim.pt 15))
  check ref s!"block skips HTML: a block's space above is the document's medium skip ({above})"
    (ruleValue sheet ["* + ", "section.block"] == some above)
  check ref s!"block skips HTML: a block's space below is the document's small skip ({below})"
    (((ruleValue sheet ["section.block", " + *)"]).map (·.startsWith s!"calc({below} + ")) ==
      some true)
  -- The kernel's registers are written once: the compatibility layer's
  -- spellings parse to the values both backends read, `\smallskip` and its
  -- kin spend them, and a register the document sets reaches the rewrite
  -- and the block alike.
  for (cmd, reg) in #[("smallskip", "smallskipamount"), ("medskip", "medskipamount"),
      ("bigskip", "bigskipamount")] do
    check ref s!"kernel skips: {reg}'s compatibility spelling is its kernel value"
      ((Ir.kernelSkip reg).isSome && ((Compat.kernelSkip reg).bind Decl.parseGlue) == Ir.kernelSkip reg)
    let spent (src : String) : Option Dim.SymGlue :=
      (Elab.run "kernel-skip.tex" src).1.body.findSome? fun
        | .spaced g body => if body.isEmpty then some g.value else none
        | _ => none
    let src (pre : String) : String :=
      "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\nAlpha.\n\n\\" ++ cmd ++
        "\n\nBravo.\n\\end{document}\n"
    check ref s!"kernel skips: \\{cmd} spends the kernel's {reg}"
      (spent (src "") == Ir.kernelSkip reg)
    let set := s!"\\setlength\{\\{reg}}\{7pt}\n"
    let (setDoc, _) := Elab.run "kernel-skip-set.tex" (src set)
    check ref s!"kernel skips: \\{cmd} and the blocks spend the {reg} the document sets"
      (spent (src set) == some { width := .ofSp (Dim.pt 7) } &&
        Ir.skipAmount setDoc.tokens reg == { width := .ofSp (Dim.pt 7) })

/-- A block an overlay step wraps (`HtmlDoc.overlayNode`) owns its
boundaries through the wrapper: the step's carrier takes the block's space
above where the block opens it and passes the space below on where the block
closes it, so a block after `\pause` stands the space an unwrapped one does. -/
private def stepWrapChecks (ref : IO.Ref (List String)) : IO Unit := do
  let src := "\\documentclass{beamer}\n\\begin{document}\n\\begin{frame}[t]{Steps}\n" ++
    "\\begin{block}{Plain}Early words.\\end{block}\n\\pause\n" ++
    "\\begin{block}{Later}Late words.\\end{block}\n\\end{frame}\n\\end{document}\n"
  let (doc, _) := Elab.run "block-steps.tex" src
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let (_, sheet) := listStyles (#[], "") (head.toList ++ body.toList)
  check ref "block step wrappers HTML: a wrapper a block opens takes the block's space above"
    (hasStr sheet ":is(.step, .step-set):has(> section.block:first-child)")
  check ref "block step wrappers HTML: a wrapper a block closes passes its space below on"
    (hasStr sheet ":is(.step, .step-set):has(> section.block:last-child)")

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
  parentChecks ref fonts
  coveredChecks ref fonts
  coveredItemChecks ref fonts
  skipChecks ref fonts
  stepWrapChecks ref
  let transparent := out.pages[1]?.getD {}
  check ref "block geometry: empty colour values clear the transparent frame's boxes"
    (transparent.fills.all fun f => f.color != titleColor && f.color != bodyColor)

end Tests.BlockGeometry
