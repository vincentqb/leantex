module

public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.FrameFit

/-- `n` invented paragraphs, one line each. -/
private def paras (n : Nat) : String :=
  "\n\n".intercalate ((List.range n).map fun i => s!"Kilo {i + 1} words.")

/-- An invented list of `n` one-line items. -/
private def items (n : Nat) : String :=
  "\\begin{itemize}\n" ++
    "\n".intercalate ((List.range n).map fun i => s!"\\item Kilo {i + 1} words.") ++
    "\n\\end{itemize}"

/-- The physical pages the `k`-th frame ships, frames counted in order. -/
private def framePages (out : Layout.Out) (k : Nat) : Nat :=
  let sources := (out.pages.filterMap (·.frameOrigin.map (·.source))).toList.eraseDups
  match sources[k]? with
  | some source => (out.pages.filter fun p => p.frameOrigin.any (·.source == source)).size
  | none => 0

/-- The baselines of a page's body lines, in order. -/
private def bodyBaselines (out : Layout.Out) (page : Nat) : Array Dim.Sp :=
  (((out.pages[page]?.map (·.lines)).getD #[]).filter (!·.furniture)).map (·.y)

/-- **A frame a little taller than its page stands overfull on it, as
beamer's does; only one taller than the gap above its footline continues**
(`Layout.Spacing.Page.fitCommit`, `Ir.frameFitOf`): a frame not declared
breakable whose content, its glue shrunk as far as it shrinks, stands past
its text area within that gap (beamer's `\footheight` keeps 4 pt above the
footline, beamerbaseframecomponents.sty:167) ships one page per overlay step
with its last line's ink above the footline's, and one past it continues on
the next page; each is named once by W0384, keyed by the frame. lualatex
sets every one of these frames on its one page, the text "extends
unpleasantly over the bottom" (beamer user guide §8.1). Over `Layout.Out`
on an invented moloch deck (10 pt, the shipped Fira Sans for every face):
twenty-one lines below a 2 pt rule-free skip overrun by about 1.6 pt, two
of them on two overlay steps the same, twenty-five lines by about 48 pt,
and twenty-one alone fit. At `ee2dec5d` the first frame shipped a second
page holding its last line. Invented words. -/
def overhangChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "overhang: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t", "\\vspace*{2pt}\n" ++ paras 21), ("t", paras 25), ("t", paras 21),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++ "\n\n\\pause\nKilo words.")])
  t "overhang: the deck elaborates clean" (ds.all (·.severity != .error))
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let w0384 := out.diags.filter (·.code == "W0384")
  t "overhang: a frame 1.6 pt taller than its page ships one page"
    (framePages out 0 == 1)
  t "overhang: an overlay frame within the gap ships one page per step"
    (framePages out 3 == 2)
  t "overhang: a frame 48 pt taller continues on a second page" (framePages out 1 == 2)
  t "overhang: a frame that fits ships one page, unnamed"
    (framePages out 2 == 1 && !w0384.any (·.subject == some "3"))
  t "overhang: an overhanging frame is named once, its steps' one loss, by the gap"
    ((w0384.filter (·.subject == some "1")).size == 1 &&
      (w0384.filter (·.subject == some "4")).size == 1 &&
      w0384.all fun d => !(d.subject == some "1" || d.subject == some "4") ||
        hasStr d.message "gap above its footline")
  t "overhang: the continuing frame is named once, by its continuation"
    ((w0384.filter (·.subject == some "2")).size == 1 &&
      w0384.all fun d => d.subject != some "2" || hasStr d.message "continues on the next page")
  -- The overhang stays above the footline's ink: the last body line's
  -- deepest glyph against the frame number's tallest.
  let page := out.pages[0]?.getD {}
  let body := page.lines.filter (!·.furniture)
  let foot := page.lines.filter (·.furniture)
  t "overhang: the last line's ink stays above the footline's"
    (match body.back?, foot.back? with
     | some l, some f =>
       l.y + (Layout.segsInk fira l.segs).2 < f.y - (Layout.segsInk fira f.segs).1
     | _, _ => false)

/-- **A frame's declared `[squeeze]` sets its lists as beamer's squeeze sets
them, and the web deck squeezes the lists of a frame the page fitted only by
shrinking its glue** (`Ir.frameSqueeze`, `Layout.squeezedFrames`): beamer's
`\beamer@cramped` sets `\itemsep0pt` in every list the frame opens
(beamerbaseframesize.sty:21-22), so nineteen invented items stand one
baselineskip apart, lualatex's 11.955 bp, held to a tenth of a point; a web
stage has no glue to shrink, so a frame the page fitted only past its glue's
natural size — nineteen items on a page their itemsep shrinks to fit,
lualatex's 13.317 bp apart, which the page keeps — sets its lists squeezed
on the web, the floor that glue shrinks to, and a frame of paragraphs with
no list is left alone. Over `Layout.Out` and the typed HTML tree. At
`ee2dec5d` `[squeeze]` was named and ignored, and the web stage of the
nineteen-item frame scrolled two items out of view. Invented words. -/
def squeezeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "squeeze: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,squeeze", items 19), ("t", items 19), ("t", "\\vspace*{2pt}\n" ++ paras 21)])
  t "squeeze: the deck elaborates clean, the option read"
    (ds.all (·.severity != .error) && !ds.any fun d => d.code == "N0102" && hasStr d.message "squeeze")
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let gaps (page : Nat) : Array Dim.Sp :=
    let ys := bodyBaselines out page
    (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a
  t "squeeze: a squeezed frame's items stand one baselineskip apart, as lualatex's"
    ((gaps 0).size == 18 && (gaps 0).all (withinSp (ptMilli 100) · (ptMilli 11955)))
  t "squeeze: the page keeps an unsqueezed frame's shrunk itemsep, as lualatex's"
    ((gaps 1).size == 18 &&
      withinSp (ptMilli 100) ((gaps 1).foldl (· + ·) 0 / 18) (ptMilli 13317))
  let squeezed := Layout.squeezedFrames doc out
  t "squeeze: the web squeezes the frame the page shrank, and no other"
    (squeezed == #[1])
  let web := { doc with body := Ir.squeezeFrames doc.body squeezed }
  let (head, body, _) := HtmlDoc.emitTree {} web
  let classes := (slideStages body).map fun n => match n with
    | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "class").getD ""
    | .text _ | .style _ | .script .. => ""
  t "squeeze: the declared and the shrunk frame's stages carry the squeeze class"
    (classes.map (hasStr · "squeeze") == #[true, true, false])
  let css := treeCssList "" head.toList
  t "squeeze: the sheet sets a squeezed frame's items with no itemsep"
    (hasStr css "section.slide.squeeze li")

/-- **A breakable frame keeps a block's title with its body**
(`Layout.Spacing.Page.keepHeading`): beamer's block is one box, so in a frame
declared `[allowframebreaks]` it never leaves its title alone at a page's
foot; nineteen invented paragraphs before a two-paragraph block put the
title on the page's last line, and the title opens the continuation with
its body, as lualatex sets the block whole there. Over `Layout.Out`. At
`ee2dec5d` the title stood alone at the first page's foot. Invented
words. -/
def breakableTitleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "breakable title: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,allowframebreaks", paras 19 ++
      "\n\n\\begin{block}{Alpha}\nLima words.\n\nMike words.\n\\end{block}")])
  t "breakable title: the deck elaborates clean" (ds.all (·.severity != .error))
  let out := layoutOf fira doc (Layout.Geom.ofPage doc.page)
  let pageOf (word : String) : Option Nat :=
    out.pages.findIdx? fun p => p.lines.any fun l => hasStr (lineText l) word
  t "breakable title: the block's title stands on its body's page"
    (match pageOf "Alpha", pageOf "Lima" with
     | some a, some l => a == l
     | _, _ => false)
  t "breakable title: the frame continues" (out.pages.size == 2)

end Tests.FrameFit
