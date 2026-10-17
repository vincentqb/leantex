module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests.InlineBoxes

/-- The runs of a source's shipped lines whose glyphs spell `word`, with their line's baseline. -/
private def runsOf (out : Layout.Out) (word : String) : Array (Layout.Seg × Dim.Sp) :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ _ _ _ glyphs .. =>
      if String.ofList (glyphs.toList.map (·.2.1)) == word then some (s, l.y) else none
    | _ => none

/-- A run's raise. -/
private def raiseOf : Layout.Seg → Dim.Sp
  | .run _ _ _ _ _ _ _ _ raise _ _ => raise
  | _ => 0

/-- A run's x on its line, from the advances before it. -/
private def runX (out : Layout.Out) (word : String) : Option Dim.Sp :=
  (bodyLines out).findSome? fun l => Id.run do
    let mut x := l.x
    for s in l.segs do
      match s with
      | .run _ _ _ w glyphs .. =>
        if String.ofList (glyphs.toList.map (·.2.1)) == word then return some x
        x := x + w
      | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _ | .rule w _ _ _
      | .image _ w _ _ _ => x := x + w
      | .poly _ _ => pure ()
    return none

/-- Every rule and mark a source's lines paint: its kind, width, thickness, raise and colour. -/
private def paintsOf (out : Layout.Out) : Array (String × Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .rule w t r c => if w != 0 && t != 0 then some ("rule", w, t, r, c.hex) else none
    | .decoration (.highlight _ _) w t r c => some ("mark", w, t, r, c.hex)
    | _ => none

/-- The pt as sp, for a length an expectation states. -/
private def pt (n : Nat) : Dim.Sp := Dim.pt n

private def doc (pre body : String) : String := dvDoc ("\\pagestyle{empty}\\usepackage{xcolor}\n" ++ pre) body

/-- The text of a document's paragraphs, in order. -/
private def paraText (d : Ir.Doc) : String :=
  String.join (d.body.toList.filterMap fun b => match b with
    | .para xs => some (Ir.plainText xs)
    | _ => none)

/-- LaTeX's `\raisebox`, `\colorbox`, `\fcolorbox` and `\fbox` set their content in one unbreakable
box as latex.ltx and xcolor build it, and url.sty's `lowtilde` sets a URL's `~` in such a box. -/
def inlineBoxChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let layout (src : String) := layoutOf fonts (elabStr src).1
  let said (src : String) := ((elabStr src).2.filter (·.severity != .note)).toList.map (·.code)
  -- raised content
  let src := doc "" "Alpha \\raisebox{2pt}{Bravo} Charlie \\raisebox{-1pt}{Delta} Echo"
  let out := layout src
  t s!"raisebox: no warning ({said src})" (said src == [])
  t "raisebox: the content's runs stand raised by the lift, the text around on the baseline"
    ((runsOf out "Bravo").map (raiseOf ·.1) == #[pt 2] &&
      (runsOf out "Delta").map (raiseOf ·.1) == #[-pt 1] &&
      (runsOf out "Alpha" ++ runsOf out "Charlie" ++ runsOf out "Echo").all (raiseOf ·.1 == 0))
  -- the box's own height
  let natural := layout (doc "" "\\raisebox{0pt}{Bravo}")
  let halved := layout (doc "" "\\raisebox{-0.5\\height}{Bravo}")
  let ink := Layout.segsInk fonts ((runsOf natural "Bravo").map (·.1))
  t s!"raisebox: a lift of -0.5\\height lowers the content by half its own height ({ink})"
    ((runsOf halved "Bravo").map (raiseOf ·.1) == #[-(ink.1 / 2)])
  -- a declared extent claims the line
  let smashed := layout (doc "" "Alpha\\\\\n\\raisebox{0pt}[0pt][0pt]{\\Huge Bravo}Charlie\\\\\nDelta")
  let plain := layout (doc "" "Alpha\\\\\nCharlie\\\\\nDelta")
  let baselines (out : Layout.Out) (words : List String) : List Dim.Sp :=
    words.filterMap fun w => ((runsOf out w)[0]?).map (·.2)
  t "raisebox: a declared zero height and depth leave the lines where they stand without the box"
    ((baselines plain ["Alpha", "Charlie", "Delta"]).length == 3 &&
      baselines smashed ["Alpha", "Charlie", "Delta"] == baselines plain ["Alpha", "Charlie", "Delta"])
  let tall := layout (doc "" "Alpha\\\\\n\\raisebox{0pt}{\\Huge Bravo}Charlie\\\\\nDelta")
  t "raisebox: an undeclared extent is the content's, which moves the next line down"
    (baselines tall ["Charlie"] != baselines plain ["Charlie"])
  -- one unbreakable box
  let narrow := layout (dvDoc "\\page{width=200pt,height=400pt,hmargin=60pt,vmargin=40pt}\n"
    "Alpha \\raisebox{1pt}{Bravo Charlie Delta Echo Foxtrot} Golf")
  t "raisebox: the box's words share one line, where the measure would break them"
    ((["Bravo", "Charlie", "Delta", "Echo", "Foxtrot"].map fun w => (runsOf narrow w).map (·.2)).all
      (· == (runsOf narrow "Bravo").map (·.2)) && (runsOf narrow "Bravo").size == 1)
  -- a ground under the content
  let yellow := "#FFFF00"
  let boxed := layout (doc "" "Alpha \\colorbox{yellow}{Bravo} Charlie")
  let bare := layout (doc "" "Alpha {Bravo} Charlie")
  let bravoInk := Layout.segsInk fonts ((runsOf bare "Bravo").map (·.1))
  let bravoW := ((runsOf bare "Bravo")[0]?.map fun (s, _) => match s with
    | .run _ _ _ w .. => w
    | _ => 0).getD 0
  t s!"colorbox: one ground, fboxsep around the content's own box, under its text ({paintsOf boxed})"
    (paintsOf boxed == #[("mark", bravoW + 2 * pt 3, bravoInk.1 + bravoInk.2 + 2 * pt 3,
      -bravoInk.2 - pt 3, yellow)])
  t "colorbox: the content stands fboxsep into the box, the text after it a box width on"
    (match runX boxed "Bravo", runX bare "Bravo", runX boxed "Charlie", runX bare "Charlie" with
     | some a, some b, some c, some d => a == b + pt 3 && c == d + 2 * pt 3
     | _, _, _, _ => false)
  -- a frame around the ground
  let framed := layout (doc "" "Alpha \\fcolorbox{red}{yellow}{Bravo} Charlie")
  let red := "#FF0000"
  let rules := (paintsOf framed).filter (·.1 == "rule")
  t s!"fcolorbox: four fboxrule sides in the frame's colour round the ground ({rules})"
    (rules.size == 4 && rules.all (fun r => r.2.2.2.2 == red) &&
      (rules.filter fun r => r.2.1 == pt 2 / 5).size == 2 &&
      (rules.filter fun r => r.2.2.1 == pt 2 / 5).size == 2 &&
      (paintsOf framed).any (·.1 == "mark"))
  let inked := layout (doc "" "Alpha \\fbox{Bravo} Charlie")
  let ink := ((runsOf inked "Alpha")[0]?.map fun (s, _) => match s with
    | .run _ c .. => c.hex
    | _ => "").getD ""
  t s!"fbox: its frame takes the text's colour {ink} and no ground ({paintsOf inked})"
    ((paintsOf inked).size == 4 && (paintsOf inked).all fun r => r.1 == "rule" && r.2.2.2.2 == ink)
  let tight := layout (doc "\\setlength{\\fboxsep}{0pt}\n" "Alpha \\colorbox{yellow}{Bravo} Charlie")
  t "colorbox: a declared fboxsep pads the ground"
    ((paintsOf tight).map (·.2.1) == #[bravoW])
  -- the web page's box
  let (_, _, html, _) := sourceArtifacts fonts
    (doc "" "A \\raisebox{0.5ex}{B} \\fcolorbox{red}{yellow}{C} \\raisebox{0pt}[0pt][0pt]{D}")
  t "box HTML: a raised box is an inline block lifted as the PDF's"
    (hasStr html "display: inline-block; white-space: nowrap; vertical-align: 0.5ex\">B")
  t "box HTML: a framed ground pads its content by fboxsep inside fboxrule"
    (hasStr html "border: 0.4pt solid" && hasStr html "padding: 3pt\">C")
  t "box HTML: a declared zero extent claims no line height" (hasStr html "line-height: 0\">D")
  let (hds, _, sized, _) := sourceArtifacts fonts
    (doc "" "A \\raisebox{0pt}[20pt][10pt]{P} \\raisebox{2pt}[0pt][0pt]{Q} \\raisebox{\\depth}{R}")
  t "box HTML: a declared height and depth claim the line through a strut, the content's line none"
    (hasStr sized "display: inline-block; width: 0; height: 30pt; vertical-align: -10pt")
  t "box HTML: a lift beside a declared extent moves the content in place"
    (hasStr sized "position: relative; top: -2pt\">Q")
  t "box HTML: a lift by the content's own depth reads it as zero"
    (hasStr sized "white-space: nowrap\">R")
  t "box HTML: a lift by the content's own depth, which the page cannot measure, is named for it"
    (hds.any fun d => d.code == "W0110" && d.subject == some "raisebox:content" &&
      d.output == some .html)
  -- url.sty's lowtilde
  let urlSrc := "See \\url{https://example.org/~probe} here."
  let low := elabStr (doc "\\usepackage[lowtilde]{url}\n" urlSrc)
  let plainUrl := elabStr (doc "\\usepackage{url}\n" urlSrc)
  t s!"lowtilde: no warning ({said (doc "\\usepackage[lowtilde]{url}\n" urlSrc)})"
    (said (doc "\\usepackage[lowtilde]{url}\n" urlSrc) == [])
  let lowOut := layoutOf (← mathSetOf fonts) low.1
  let tildes := (bodyLines lowOut).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ _ _ _ glyphs size _ _ raise .. =>
      if glyphs.any (·.2.1 == '∼') then some (size, raise) else none
    | _ => none
  t s!"lowtilde: the URL's tilde sets as a raised script-size sim ({tildes})"
    (tildes.size == 1 && tildes.all fun (_, r) => 0 < r)
  t "lowtilde: the link's address keeps its tilde"
    (Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
      | .link url _ => acc || url == "https://example.org/~probe"
      | _ => acc) false low.1.body)
  t "lowtilde: without the option the URL ships its face's tilde"
    ((bodyLines (layoutOf fonts plainUrl.1)).any fun l => hasStr (lineText l) "~probe")

/-- The box commands' arguments as TeX reads them: through a macro, a single token, url.sty's
delimiters and lengths this engine cannot read, none of them stopping the build. -/
def boxArgumentChecks (ref : IO.Ref (List String)) (_fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let errors (src : String) := ((elabStr src).2.filter (·.severity == .error)).toList.map (·.code)
  let boxes (src : String) : Array (Ir.InlineBox × String) :=
    Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
      | .boxed b body => acc.push (b, Ir.plainText body)
      | _ => acc) #[] (elabStr src).1.body
  let texts (src : String) := (boxes src).map (·.2)
  let viaMacro := doc "\\newcommand\\hl{\\colorbox{yellow}}\n\\newcommand\\boxit{\\fbox}\n"
    "Alpha \\hl{marked} and \\boxit{framed} end."
  t s!"box arguments: a macro leaving a box command its argument sets it ({errors viaMacro})"
    (errors viaMacro == [] && texts viaMacro == #["marked", "framed"] &&
      ((boxes viaMacro)[0]?.bind (·.1.ground)).map (·.1.hex) == some "#FFFF00")
  let single := doc "" "Alpha \\fbox xyz and \\colorbox{yellow}w end."
  t s!"box arguments: a word's first character is the argument, as TeX's single token ({texts single})"
    (errors single == [] && texts single == #["x", "w"] &&
      hasStr (paraText (elabStr single).1) "xyz and")
  let delimited := doc "\\usepackage{url}\n"
    "See \\path|/usr/bin_x|, \\path+/a/b+ and \\url!https://example.org/p_q! here."
  let (ddoc, _) := elabStr delimited
  let links := Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
    | .link url _ => acc.push url
    | _ => acc) #[] ddoc.body
  t s!"box arguments: url.sty's delimited arguments set whole ({errors delimited})"
    (errors delimited == [] && links == #["https://example.org/p_q"] &&
      hasStr (paraText ddoc) "/usr/bin_x, /a/b and https://example.org/p_q here")
  let tikzPaths := ["\\path (0,0) -- (1,1);", "\\path[draw] (0,0);", "\\path ++(1,0);",
    "\\path +(1,0);", "\\path :xshift = {0s = \"0cm\"} (0,0);", "\\path |- (1,1);",
    "\\path -| (2,1);", "\\path -- (1,1);", "\\path<2> (0,0);", "\\path;"]
  let tikzToks := (Lex.lex "t.tex" (" ".intercalate tikzPaths)).1
  t "box arguments: TikZ's path operations are no url.sty delimiters"
    (!tikzToks.any (·.tok matches .verb ..) &&
      (tikzToks.filter (·.tok == .ctrl "path")).size == tikzPaths.length)
  let inPicture := (Lex.lex "t.tex" "\\begin{tikzpicture}\\path !x!;\\end{tikzpicture} \\path !x!").1
  t "box arguments: inside a TikZ picture \\path is TikZ's, outside it url.sty's"
    ((inPicture.filter (·.tok matches .verb ..)).size == 1)
  let tokens := doc "" "Alpha \\fbox\\LaTeX{} and \\colorbox{yellow}\\ldots{} and \\fbox~ words."
  t s!"box arguments: a control or a special character is a box's single token ({errors tokens})"
    (errors tokens == [] && (boxes tokens).size == 3)
  let macroUrl := doc "\\usepackage{url}\n\\newcommand\\site[1]{\\url|https://example.org/#1|}\n\\newcommand\\dir[1]{\\path+/srv/#1+}\n"
    "See \\site{page} and \\dir{data}."
  let (mdoc, _) := elabStr macroUrl
  let mlinks := Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
    | .link url _ => acc.push url
    | _ => acc) #[] mdoc.body
  t s!"box arguments: a macro's parameter in a delimited argument takes its argument ({mlinks})"
    (mlinks == #["https://example.org/page"] && hasStr (paraText mdoc) "/srv/data")
  let unread := doc "\\usepackage{calc}\n"
    "A \\raisebox{0.5\\ht\\strutbox}{x} B \\raisebox{-\\heightof{y}}{y} C \\raisebox{\\fontdimen5\\font}{z}"
  let (_, uds) := elabStr unread
  t s!"box arguments: a lift this engine cannot read is named and set at no lift ({errors unread})"
    (errors unread == [] && texts unread == #["x", "y", "z"] &&
      (boxes unread).all (·.1.raise == .lit ({} : Dim.SymGlue)) && uds.any (·.code == "W0107"))

/-- A box parameter assigned in running text holds to its group, as TeX's local assignment does, a
line break inside a box breaks nothing, and the text's own ink is judged on a box's ground. -/
def boxScopeChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let said (src : String) := ((elabStr src).2.filter (·.severity != .note)).toList.map (·.code)
  let boxes (src : String) : Array (Ir.InlineBox × String) :=
    Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
      | .boxed b body => acc.push (b, Ir.plainText body)
      | _ => acc) #[] (elabStr src).1.body
  let paras (src : String) := ((elabStr src).1.body.filter (· matches .para _)).size
  let pads (src : String) := (boxes src).map (·.1.pad.width)
  let grouped := doc "" "Alpha {\\setlength{\\fboxsep}{0pt}\\colorbox{yellow}{tight}} and \\colorbox{yellow}{normal} end."
  t s!"box scope: a body fboxsep holds to its group and keeps the paragraph ({said grouped})"
    (said grouped == [] && paras grouped == 1 &&
      pads grouped == #[Dim.Length.ofSp 0, Dim.Length.ofSp (pt 3)])
  let viaMacro := doc "\\newcommand\\tightbox[1]{{\\setlength{\\fboxsep}{1pt}\\colorbox{yellow}{#1}}}\n"
    "Alpha \\tightbox{one} and \\colorbox{yellow}{two} end."
  t s!"box scope: a macro's own group scopes its fboxsep ({(pads viaMacro).map (·.sp.toPtString)})"
    (paras viaMacro == 1 && pads viaMacro == #[Dim.Length.ofSp (pt 1), Dim.Length.ofSp (pt 3)])
  let ruled := doc "" "Alpha {\\setlength{\\fboxrule}{2pt}\\fbox{a}} \\fbox{b} end."
  t "box scope: a body fboxrule holds to its group"
    (paras ruled == 1 &&
      (boxes ruled).map (·.1.rule.width) == #[Dim.Length.ofSp (pt 2), Dim.Length.ofSp (pt 2 / 5)])
  let inBox := doc "" "Alpha \\colorbox{yellow}{{\\setlength{\\fboxsep}{0pt}\\fbox{in}}\\fbox{out}} end."
  let padOf (text : String) := ((boxes inBox).find? (·.2 == text)).map (·.1.pad.width)
  t "box scope: a setting inside a box's content ends with it"
    (padOf "inout" == some (Dim.Length.ofSp (pt 3)) && padOf "in" == some (Dim.Length.ofSp 0) &&
      padOf "out" == some (Dim.Length.ofSp (pt 3)))
  let broken := doc "" "Alpha \\colorbox{yellow}{one\\\\two} and \\fbox{three \\\\ four} end."
  let out := layoutOf fonts (elabStr broken).1
  t s!"box scope: a line break inside a box breaks nothing ({(boxes broken).map (·.2)})"
    ((boxes broken).map (·.2) == #["onetwo", "threefour"] && (bodyLines out).size == 1)
  let dark := doc "" "Alpha \\colorbox{black}{plain on black} end."
  t s!"box scope: the text's own ink is judged on a box's ground ({said dark})"
    (said dark |>.contains "W0315")
  t "box scope: legible ink on a box's ground is not named"
    (!(said (doc "" "Alpha \\colorbox{yellow}{fine} end.") |>.contains "W0315"))
  let envTight := doc "\\newenvironment{tight}{\\setlength{\\fboxsep}{0pt}}{}\n"
    "Foxtrot \\begin{tight}\\colorbox{yellow}{six}\\end{tight} words \\colorbox{yellow}{seven}.\n\n\\colorbox{yellow}{eight}"
  t s!"box scope: an environment's begin code sets its content's boxes and ends with it ({(pads envTight).map (·.sp.toPtString)})"
    (pads envTight == #[Dim.Length.ofSp 0, Dim.Length.ofSp (pt 3), Dim.Length.ofSp (pt 3)])
  let envNotes := doc "\\newenvironment{probe}{\\footnote{begin note}}{}\n"
    "Alpha \\begin{probe}text\\footnote{inner note}\\end{probe} words\\footnote{after note}."
  let notes := Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
    | .footnote n body => acc.push (n, Ir.plainText body)
    | _ => acc) #[] (elabStr envNotes).1.body
  t s!"box scope: an environment's begin code runs before its content ({notes})"
    (notes == #[(some 1, "begin note"), (some 2, "inner note"), (some 3, "after note")])
  let smashed := doc "" "Alpha\\\\\n\\raisebox{0pt}[0pt][0pt]{\\fbox{\\Huge Bravo}}Charlie\\\\\nDelta"
  let plainLines := doc "" "Alpha\\\\\nCharlie\\\\\nDelta"
  let baseline (src w : String) := ((runsOf (layoutOf fonts (elabStr src).1) w)[0]?).map (·.2)
  t "box scope: a frame inside a declared extent still claims its own height on the line, named"
    (baseline smashed "Delta" != baseline plainLines "Delta" &&
      (elabStr smashed).2.any (·.subject == some "raisebox:extent"))
  let words := String.intercalate " " ((List.range 40).map fun k =>
    if k % 5 == 4 then "\\fcolorbox{red}{yellow}{three framed words}" else s!"word{k}")
  let expanded := layoutOf fonts (elabStr (doc "" words)).1
  let framesMeet := (bodyLines expanded).all fun l => Id.run do
    let mut x := l.x
    let mut sides : Array (Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for seg in l.segs do
      match seg with
      | .rule w t _ c => if c.hex == "#FF0000" then sides := sides.push (x, w, t)
                         x := x + w
      | .run _ _ _ w .. | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _ | .image _ w _ _ _ =>
        x := x + w
      | .poly _ _ => pure ()
    -- Each frame paints its left and right sides, then its top and bottom.
    let mut ok := sides.size % 4 == 0
    for q in [0:sides.size / 4] do
      match sides[4 * q]?, sides[4 * q + 1]?, sides[4 * q + 2]?, sides[4 * q + 3]? with
      | some (lx, lw, _), some (rx, _, _), some (tx, tw, _), some (bx, bw, _) =>
        ok := ok && tx == lx + lw && bx == tx && bw == tw && rx == tx + tw
      | _, _, _, _ => ok := false
    return ok
  t "box scope: a frame's sides meet on a justified line, its content set at its natural width"
    ((bodyLines expanded).size > 1 && framesMeet)
  let labelled := doc "" "Alpha \\colorbox{blue}{\\textcolor{white}{Label}} end."
  let (ldoc, _) := elabStr labelled
  t "box scope: a light ink on a dark box is carried on the box in every scheme, which keeps them all"
    ((Contrast.schemeJudge ldoc).dropped.isEmpty && (Contrast.schemeJudge ldoc).shipped.length > 1)
  let page := doc "" "Alpha \\colorbox{yellow}{Bravo} end."
  let (pdoc, _) := elabStr page
  let (_, _, html, _) := sourceArtifacts fonts page
  let j := Contrast.schemeJudge pdoc
  let yellow : Ir.Color := { r := 255, g := 255, b := 0 }
  let var := (((html.splitOn "background-color: ")[1]?).map fun rest =>
    ((rest.splitOn ";")[0]?.getD "").replace "var(" "" |>.replace ")" "").getD ""
  let shipped := (HtmlDoc.schemeVarTexts j.shipped var).getD []
  t s!"box scope: the web page grounds a box in each scheme as the scheme judge reads it ({var})"
    (j.shipped.length > 1 && shipped.length == j.shipped.length &&
      j.frames.all fun f => shipped.lookup f.scheme == some (some (HtmlDoc.cssColor (f.ground yellow))))

end Tests.InlineBoxes
