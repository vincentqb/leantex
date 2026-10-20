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

/-- The physical pages the frame at body index `source` ships. -/
private def framePages (out : Layout.Out) (source : Nat) : Nat :=
  (out.pages.filter fun p => p.frameOrigin.any (·.source == source)).size

private def bodyBaselines (out : Layout.Out) (page : Nat) : Array Dim.Length :=
  (((out.pages[page]?.map (·.lines)).getD #[]).filter (!·.furniture)).map (·.y)

/-- The ladder's decision for the frame at body index `source`, step `step`. -/
private def decision (f : Layout.Fitted) (source step : Nat) : Option Ir.FrameFit :=
  (f.decisions.find? (·.1 == ⟨source, step⟩)).map (·.2)

/-- The overflow ladder's diagnostics naming frame `label`. -/
private def ladderNamed (out : Layout.Out) (label : String) : Array Diag :=
  out.diags.filter fun d => (d.code == "W0384" || d.code == "W0400") && d.subject == some label

/-- A frame slightly taller than its page stands overfull on it, one past the gap above its footline
continues, and each frame is named once with its whole overrun. -/
def overhangChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "overhang: the shipped Fira Sans parses" false
  let pic := "\\begin{tikzpicture}\\draw (0,0) rectangle (2,1.2);\\end{tikzpicture}"
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t", "\\vspace*{2pt}\n" ++ paras 21), ("t", paras 25), ("t", paras 26), ("t", paras 21),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++ "\n\n\\pause\nKilo words."),
     ("t", "\\vspace*{5pt}\nKilo words.\\footnote{Lima words.}\n\n" ++ paras 19),
     ("t", "\\vspace*{16pt}\n" ++ paras 17 ++ "\n\n" ++ pic),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++
       "\n\n\\alt<2>{Kilo words.\n\nLima words.\n\nMike words.\n\nNovember words.}{Kilo words.}"),
     ("t", "\\vspace*{2pt}\n" ++ paras 20 ++
       "\n\n\\alt<2>{\\vspace*{2pt}Kilo words.}{Kilo words.}")])
  t "overhang: the deck elaborates clean" (ds.all (·.severity != .error))
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  let gap := Dim.pt 4
  t "overhang: a frame 1.6 pt past its text area ships one page, overfull within the gap"
    (framePages out 0 == 1 && match decision f 0 1 with
      | some (.overfull o) => 0 < o && o ≤ gap
      | _ => false)
  t "overhang: the overfull frame is named once, by W0400"
    ((ladderNamed out "1").map (·.code) == #["W0400"])
  t "overhang: a frame far past its page continues, named once by W0384 with its overrun"
    (framePages out 1 == 2 && match decision f 1 1 with
      | some (.continued o) =>
        (ladderNamed out "2").map (·.message) == #[(Layout.continuedDiag (some "2") none o).message]
      | _ => false)
  let pitch := match (out.pages.findIdx? fun p => p.frameOrigin.any (·.source == 3)) with
    | some i => let ys := bodyBaselines out i; (ys[1]?.getD 0) - (ys[0]?.getD 0)
    | none => 0
  t "overhang: W0384 states the whole overrun: one more line adds one baselineskip"
    (0 < pitch && match decision f 1 1, decision f 2 1 with
      | some (.continued a), some (.continued b) => withinSp (ptMilli 100) (b - a) pitch
      | _, _ => false)
  t "overhang: a frame that fits ships one page, unnamed"
    (framePages out 3 == 1 && (ladderNamed out "4").isEmpty && decision f 3 1 == none)
  t "overhang: an overlay frame within the gap ships one page per step, named once"
    (framePages out 4 == 2 && (ladderNamed out "5").map (·.code) == #["W0400"])
  t "overhang: a frame a point past its page below a footnote continues rather than reach it"
    (framePages out 5 == 2 && (ladderNamed out "6").map (·.code) == #["W0384"] &&
      match decision f 5 1 with
      | some (.continued o) => 0 < o && o ≤ gap
      | _ => false)
  t "overhang: the body's ink never reaches the footnotes"
    (out.pages.all fun p => !p.frameOrigin.any (·.source == 5) ||
      let notes := p.lines.filter (·.note)
      let body := p.lines.filter fun l => !l.note && !l.furniture
      notes.all fun n => body.all fun l =>
        l.y + (Layout.segsInk fira l.segs).2 < n.y - (Layout.segsInk fira n.segs).1)
  t "overhang: a picture a point past the text area stands on its frame's one page"
    (framePages out 6 == 1 && (ladderNamed out "7").map (·.code) == #["W0400"])
  t "overhang: each overlay step is decided on its own, the frame named once"
    (framePages out 7 == 3 && match decision f 7 1, decision f 7 2 with
      | some (.overfull v), some (.continued c) =>
        (ladderNamed out "8").map (·.message) ==
          #[(Layout.continuedDiag (some "8") none c (some v)).message]
      | _, _ => false)
  t "overhang: steps overfull by different amounts name their frame once, by the larger"
    (framePages out 8 == 2 && match decision f 8 1, decision f 8 2 with
      | some (.overfull a), some (.overfull b) =>
        a < b && (ladderNamed out "9").map (·.message) ==
          #[(Layout.overfullDiag (some "9") none b).message]
      | _, _ => false)
  let page := out.pages[0]?.getD {}
  let body := page.lines.filter (!·.furniture)
  let foot := page.lines.filter (·.furniture)
  t "overhang: the last line's ink stays above the footline's"
    (match body.back?, foot.back? with
     | some l, some f =>
       l.y + (Layout.segsInk fira l.segs).2 < f.y - (Layout.segsInk fira f.segs).1
     | _, _ => false)
  t "overhang: the shipped pages are the setting the ladder recorded"
    (out.pages.size == (Layout.run (Layout.Geom.ofPage doc.page) fira none f.setting).pages.size)

/-- A frame past its text area under a running foot continues rather than stand in the bottom
margin. -/
def runningFootChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "running foot: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n\\runningfoot{Hikl gypsy words}\n"
    [("t", "\\vspace*{6pt}\n" ++ paras 17 ++ "\n\nKilo gypsy words jumping."),
     ("t", paras 3)])
  t "running foot: the deck elaborates clean" (ds.all (·.severity != .error))
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  t "running foot: a frame a few points past its text area continues"
    (framePages out 0 == 2 && (ladderNamed out "1").map (·.code) == #["W0384"] &&
      match decision f 0 1 with
      | some (.continued o) => 0 < o && o ≤ Dim.pt 4
      | _ => false)
  t "running foot: the body's ink stays above the running foot's on every page"
    (out.pages.all fun p =>
      let foot := p.lines.filter (·.furniture)
      let body := p.lines.filter fun l => !l.furniture && !l.note
      foot.all fun r => body.all fun l =>
        l.y + (Layout.segsInk fira l.segs).2 < r.y - (Layout.segsInk fira r.segs).1)

/-- A `[squeeze]` declared on a title-page frame marks the flattened frame, so the title page sets
as it does undeclared. -/
def titlePageSqueezeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "title page squeeze: the shipped Fira Sans parses" false
  let deck (opt : String) : String :=
    "\\documentclass[10pt]{beamer}\n\\title{Kilo invented title}\n\\author{Lima Author}\n" ++
      "\\begin{document}\n\\begin{frame}" ++ opt ++ "\n\\titlepage\n\\end{frame}\n" ++
      "\\begin{frame}{Bravo}\nLima words.\n\\end{frame}\n\\end{document}\n"
  let (sq, sds) := elabStr (deck "[squeeze]")
  let (plain, _) := elabStr (deck "")
  t "title page squeeze: the deck elaborates clean, the option read"
    (sds.all (·.severity != .error) && !sds.any fun d => d.code == "N0102")
  let lines (doc : Ir.Doc) : Array (String × Dim.Length × Dim.Length) :=
    ((fittedOf fira doc (Layout.Geom.ofPage doc.page)).out.pages.flatMap (·.lines)).map
      fun l => (lineText l, l.x, l.y)
  t "title page squeeze: the title page sets as it sets undeclared"
    (lines sq == lines plain)
  let stages (doc : Ir.Doc) : Nat := (slideStages (HtmlDoc.emitTree {} doc).2.1).size
  t "title page squeeze: one slide stage per frame, none inside another"
    (stages sq == 2 && stages plain == 2)

/-- A declared `[squeeze]` sets a frame's lists as beamer's squeeze does, and the web deck squeezes
the lists of a frame the page fitted only by shrinking its glue. -/
def squeezeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "squeeze: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,squeeze", items 19), ("t", items 19), ("t", "\\vspace*{2pt}\n" ++ paras 21)])
  t "squeeze: the deck elaborates clean, the option read"
    (ds.all (·.severity != .error) && !ds.any fun d => d.code == "N0102" && hasStr d.message "squeeze")
  let f := fittedOf fira doc (Layout.Geom.ofPage doc.page)
  let out := f.out
  let gaps (page : Nat) : Array Dim.Length :=
    let ys := bodyBaselines out page
    (ys.zip (ys.extract 1 ys.size)).map fun (a, b) => b - a
  t "squeeze: a squeezed frame's items stand one baselineskip apart, as lualatex's"
    ((gaps 0).size == 18 && (gaps 0).all (withinSp (ptMilli 100) · (ptMilli 11955)))
  t "squeeze: the page keeps an unsqueezed frame's shrunk itemsep, as lualatex's"
    ((gaps 1).size == 18 &&
      withinSp (ptMilli 100) ((gaps 1).foldl (· + ·) 0 / 18) (ptMilli 13317))
  t "squeeze: the web squeezes the frame the page shrank, and no other"
    (f.webSqueeze == #[1])
  let web := { doc with body := Ir.squeezeFrames doc.body f.webSqueeze }
  let (head, body, _) := HtmlDoc.emitTree {} web
  let classes := (slideStages body).map fun n => match n with
    | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "class").getD ""
    | .text _ | .style _ | .script .. => ""
  t "squeeze: the declared and the shrunk frame's stages carry the squeeze class"
    (classes.map (hasStr · "squeeze") == #[true, true, false])
  let css := treeCssList "" head.toList
  let rules := artCssBlocks css
  t "squeeze: the sheet sets a squeezed frame's items with no gap between them"
    (rules.any fun (sel, decls) =>
      hasStr sel "section.slide.squeeze li + li" && hasStr decls "margin-top: calc(0.000rem")
  t "squeeze: a trivlist in a squeezed frame's item takes the squeeze's half point"
    ((screenRulesOf css
      "section.slide.squeeze li, section.slide.squeeze dd, section.slide.squeeze blockquote").any
      (hasStr · s!"--{Ir.trivlistSkipName}:"))

/-- A breakable frame keeps a block's title with its body, and flow lets the body break after its
first line. -/
def breakableTitleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← shippedFira | t "breakable title: the shipped Fira Sans parses" false
  let (doc, ds) := elabStr (beamerDeck "\\usetheme{moloch}\n"
    [("t,allowframebreaks", paras 19 ++
      "\n\n\\begin{block}{Alpha}\nLima words.\n\nMike words.\n\\end{block}")])
  t "breakable title: the deck elaborates clean" (ds.all (·.severity != .error))
  let out := (fittedOf fira doc (Layout.Geom.ofPage doc.page)).out
  let pageOf (out : Layout.Out) (word : String) : Option Nat :=
    out.pages.findIdx? fun p => p.lines.any fun l => hasStr (lineText l) word
  t "breakable title: the block's title stands on its body's page"
    (match pageOf out "Alpha", pageOf out "Lima" with
     | some a, some l => a == l
     | _, _ => false)
  t "breakable title: the frame continues" (out.pages.size == 2)
  let article (n lift : Nat) : String :=
    "\\documentclass{article}\n\\usepackage{beamerarticle}\n\\clubpenalty=0\n\\widowpenalty=0\n" ++
      s!"\\begin\{document}\n\\vspace*\{{lift}pt}\n" ++
      "\n\n".intercalate ((List.range n).map fun i =>
        s!"Kilo {i + 1} words in an invented paragraph long enough to fill a line of the " ++
          "article's measure, more or less.") ++
      "\n\n\\begin{block}{Alpha}\nLima words.\\\\\nMike words.\n\\end{block}\n\\end{document}\n"
  -- Unpenalised, a club and widow line costs less than moving the body whole, as in TeX; the lifts
  -- step the room a page's last paragraph leaves finer than a line.
  let splits := ((List.range 4).flatMap fun k => (List.range 8).map (k, 4 * ·)).filter fun (k, lift) =>
    let out := (fittedOf fira (elabStr (article (16 + k) lift)).1).out
    match pageOf out "Alpha", pageOf out "Lima", pageOf out "Mike" with
    | some a, some l, some m => a == l && m == l + 1
    | _, _, _ => false
  t "breakable title: in flow a block's body breaks after its first line, as LaTeX's may"
    (!splits.isEmpty)

end Tests.FrameFit
