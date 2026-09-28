import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! The kernel's environments and amsthm's, read off the page they ship. -/

/-- A shipped line's runs, left to right: the face index, the glyphs, and the
run's left edge and width on the page. -/
def lineRuns (l : Layout.LineOut) : Array (Nat × String × Dim.Sp × Dim.Sp) := Id.run do
  let mut out := #[]
  let mut x := l.x
  for seg in l.segs do
    match seg with
    | .run idx _ _ w gs _ _ _ _ _ =>
      out := out.push (idx, String.ofList (gs.map (·.2.1)).toList, x, w)
      x := x + w
    | .gap w _ => x := x + w
    | .rule w _ _ _ => x := x + w
    | .image _ w _ => x := x + w
  return out

/-- The face index of the first run on `l` whose glyphs hold `word`. -/
def faceOfWord (l : Layout.LineOut) (word : String) : Option Nat :=
  ((lineRuns l).find? fun r => hasStr r.2.1 word).map (·.1)

/-- **A theorem-like environment is a block whose first line opens with its
generated head, in the head's font, over a body in the style's font** — the
kernel's (latex.ltx `\@begintheorem`: bold head, italic body) and amsthm's
three styles and its proof (amsthm.sty), numbered by their counters with a
`[within]` counter restarting at its heading, and a proof closed by its QED
at the measure's right edge. Asserted over `Layout.Out` under the four
Source Serif faces and Fira Math, where a run's face index says its weight,
slant and whether it is maths (regular 0, bold 1, italic 2, bold italic 3,
math 4), and over the typed HTML page. On the merge base every row fails:
`\newtheorem` was an unknown preamble command and each environment's body
merged into the paragraph before it. Invented content throughout. -/
def kernelThmChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fs ← serifFacesSet | t "theorem checks: the serif faces load" false
  let linesOf (src : String) : Array Layout.LineOut :=
    bodyLines (layoutOf fs (elabStr src).1)
  let lineWith (ls : Array Layout.LineOut) (w : String) : Option Layout.LineOut :=
    ls.find? fun l => hasStr (lineText l) w
  let opensWith (ls : Array Layout.LineOut) (w : String) : Bool :=
    (lineWith ls w).any fun l => (lineText l).startsWith w
  let ams := "\\usepackage{amsthm}\n\\newtheorem{thm}{Theorem}[section]\n\
\\newtheorem{lem}[thm]{Lemma}\n\\theoremstyle{definition}\n\\newtheorem{defn}{Definition}\n\
\\theoremstyle{remark}\n\\newtheorem*{rem}{Remark}\n"
  let body := "\\section{One}\nAlder opens the section.\n\\begin{thm}\nBirch states it.\n\
\\end{thm}\n\\begin{lem}[Named]\nCedar follows.\n\\end{lem}\n\\section{Two}\n\
\\begin{thm}\\label{t:two}\nDogwood restarts.\n\\end{thm}\n\\begin{defn}\nElm is defined.\n\
\\end{defn}\n\\begin{rem}\nFir remarks.\n\\end{rem}\nHazel cites \\ref{t:two}.\n"
  let src := dvDoc ams body
  let (_, ds) := elabStr src
  t "theorems: the declarations and environments elaborate clean"
    (ds.all fun d => d.severity != .warning && d.severity != .error)
  let ls := linesOf src
  t "theorem: its head opens a line of its own, not the paragraph before"
    (opensWith ls "Theorem 1.1." && !(lineWith ls "Alder").any fun l => hasStr (lineText l) "Theorem")
  t "theorem: a shared counter numbers the next environment" (opensWith ls "Lemma 1.2")
  t "theorem: a [within] counter restarts at its heading" (opensWith ls "Theorem 2.1.")
  t "theorem: a label inside binds the environment's number" (hasStr (String.join (ls.toList.map lineText)) "Hazel cites 2.1")
  let face (w : String) : Option Nat := (lineWith ls w).bind (faceOfWord · w)
  t "plain: the head is bold" (face "Theorem" == some 1)
  t "plain: the body is italic" (face "Birch" == some 2)
  t "plain: the note is upright and medium" (face "Named" == some 0)
  t "definition: the body is upright" (face "Elm" == some 0 && face "Definition" == some 1)
  t "remark: the head is italic and unnumbered" (face "Remark" == some 2 && opensWith ls "Remark.")
  t "remark: the body under its head is upright"
    (opensWith ls "Remark." && face "Fir" == some 0)
  t "theorem: the italic stops at its end: the text after it is upright again"
    (face "Dogwood" == some 2 && face "Hazel" == some 0)
  -- The kernel's own theorem, no amsthm: bold head without the period,
  -- italic body (latex.ltx `\@begintheorem`).
  let kls := linesOf (dvDoc "\\newtheorem{thm}{Theorem}\n" "\\begin{thm}[Aside]\nJuniper.\n\\end{thm}")
  -- The head's separator is `\labelsep`, .5 em: 5 pt at the 10 pt body,
  -- from the head's last glyph to the body's first.
  let sepAfter (l : Layout.LineOut) (before after : String) : Bool :=
    let rs := lineRuns l
    match rs.find? (hasStr ·.2.1 before), rs.find? (hasStr ·.2.1 after) with
    | some a, some b => b.2.2.1 - (a.2.2.1 + a.2.2.2) == Dim.pt 5
    | _, _ => false
  t "kernel theorem: bold head and note, no head period"
    (opensWith kls "Theorem 1 (Aside)" && (lineWith kls "Theorem").bind (faceOfWord · "Aside") == some 1)
  t "kernel theorem: \\labelsep between the head and the body"
    ((lineWith kls "Juniper").any (sepAfter · ")" "Juniper"))
  t "kernel theorem: the body is italic" ((lineWith kls "Juniper").bind (faceOfWord · "Juniper") == some 2)
  -- amsthm's proof: italic head, upright body, the QED flush with the
  -- measure's right edge on the last line.
  let pdoc := (elabStr (dvDoc "\\usepackage{amsthm}\n" "\\begin{proof}\nLarch is short.\n\\end{proof}")).1
  let pout := layoutOf fs pdoc
  let pls := bodyLines pout
  let geom := Layout.Geom.ofPage pdoc.page
  t "proof: the head is italic, the body upright"
    ((lineWith pls "Proof.").bind (faceOfWord · "Proof") == some 2 &&
      (lineWith pls "Larch").bind (faceOfWord · "Larch") == some 0)
  t "proof: \\labelsep between the head and the body"
    ((lineWith pls "Larch").any (sepAfter · "." "Larch"))
  t "proof: the QED is a math glyph at the measure's right edge"
    ((lineWith pls "Larch").any fun l => (lineRuns l).any fun r =>
      r.1 == 4 && hasStr r.2.1 "□" &&
        decide (((r.2.2.1 + r.2.2.2) - (geom.hmargin + geom.textWidth)).natAbs ≤ (Dim.pt 1).natAbs))
  -- After a display or a list the QED opens a line of its own, and stands at
  -- the measure's right edge there too (amsthm.sty `\qed`: the empty
  -- `\hbox{}` before `\hfill` is what keeps the fill at a line's start).
  let qedLine (body : String) : Option Layout.LineOut :=
    let d := (elabStr (dvDoc "\\usepackage{amsthm}\n" body)).1
    let g := Layout.Geom.ofPage d.page
    (bodyLines (layoutOf fs d)).find? fun l => (lineRuns l).any fun r =>
      r.1 == 4 && hasStr r.2.1 "□" &&
        decide (((r.2.2.1 + r.2.2.2) - (g.hmargin + g.textWidth)).natAbs ≤ (Dim.pt 1).natAbs)
  let alone (l : Layout.LineOut) : Bool :=
    !hasStr (lineText l) "Larch" && !hasStr (lineText l) "Maple"
  t "proof: after a display the QED stands alone at the measure's right edge"
    ((qedLine "\\begin{proof}\nLarch opens.\n\\[ x = y \\]\n\\end{proof}").any alone)
  t "proof: after a list the QED stands alone at the measure's right edge"
    ((qedLine "\\begin{proof}\nLarch opens.\n\\begin{itemize}\n\\item Maple.\n\\end{itemize}\n\\end{proof}").any alone)
  let noQed := linesOf (dvDoc "\\usepackage{amsthm}\n"
    "\\begin{proof}\n\\renewcommand{\\qedsymbol}{}Maple ends bare.\n\\end{proof}")
  t "proof: an emptied \\qedsymbol omits the mark, the head stays"
    ((lineWith noQed "Maple").any fun l =>
      (lineText l).startsWith "Proof." && !(lineRuns l).any (hasStr ·.2.1 "□"))
  -- Kept behaviour, not a repair: passes on the merge base too.
  t "proof: without amsthm the environment is unknown, as LaTeX has it"
    ((warnCodes (dvDoc "" "\\begin{proof}\nx\n\\end{proof}")).contains "W0302")
  t "theoremstyle: a style the engine has not is named"
    ((elabStr (dvDoc "\\usepackage{amsthm}\n\\theoremstyle{fancy}\n" "x")).2.any fun d =>
      d.code == "W0110" && d.subject == some "theoremstyle:fancy")
  -- amsthm.sty's `\theoremstyle`: an undefined style warns and sets plain,
  -- whatever style stood before it.
  let fancy := linesOf (dvDoc "\\usepackage{amsthm}\n\\theoremstyle{definition}\n\
\\theoremstyle{fancy}\n\\newtheorem{thm}{Theorem}\n" "\\begin{thm}\nJuniper states.\n\\end{thm}")
  t "theoremstyle: an unknown style sets plain, as amsthm does: an italic body"
    ((lineWith fancy "Juniper").bind (faceOfWord · "Juniper") == some 2)
  -- HTML: the environment's name as its class, the head as strong text.
  let page := (HtmlDoc.emit {} (elabStr src).1).1
  t "html: a theorem is its own block under the environment's name"
    (hasStr page "<div class=\"u-thm u-trivlist-ams\">")
  t "html: the head is strong, the number upright"
    (hasStr page "<strong>Theorem <span class=\"up\">1.1</span></strong><strong>.</strong>")


/-- **A theorem-like block opens and closes the space its spelling sets**
(`Ir.thmSkips`), not the trivlist quantum a `{center}` takes: latex.ltx's
theorem is `\trivlist` itself — `\topsep`, and `\partopsep` after a blank
line — amsthm's plain and definition spend `\thm@preskip` and
`\thm@postskip`, the `\topsep`, remark half of it, and the proof `6pt plus
6pt` over `\partopsep` (size10/12.clo:215–218, amsthm.sty:74–76, 229–233,
433). Asserted over `Layout.Out`, baseline to baseline, against those
lengths; lualatex, article 10 pt, sets the kernel's theorem 22 pt from the
text around it after a blank line and 20 pt without one, amsthm's plain and
definition and the proof 20 pt, remark 16 pt (TeX Live 2026). On the base
the blocks spent one quantum over the paragraph mark. Invented words. -/
def kernelThmSpaceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let steps (src : String) (words : List String) : List Dim.Sp :=
    let c := censusOfSrc oneFace src
    let v := words.filterMap (lineYOf c 0 ·)
    (v.zip v.tail).map fun (a, b) => b - a
  let leadOf (src : String) : Dim.Sp :=
    let g := Layout.Geom.ofPage (elabStr src).1.page
    Ir.leadingFor g.fontSize g.leading
  let abc := ["Alpha.", "Bravo.", "Charlie."]
  let ams := "\\usepackage{amsthm}\n\\newtheorem{thm}{Theorem}\n\\theoremstyle{definition}\n\
\\newtheorem{defn}{Definition}\n\\theoremstyle{remark}\n\\newtheorem*{rem}{Remark}\n"
  let kern := "\\newtheorem{thm}{Theorem}\n"
  let proof := "\\usepackage{amsthm}\n"
  let env (e : String) : String := "\\begin{" ++ e ++ "}\nBravo.\n\\end{" ++ e ++ "}"
  let blank (cls pre e : String) : String := s!"\\documentclass{cls}\n" ++ pre ++
    "\\begin{document}\nAlpha.\n\n" ++ env e ++ "\n\nCharlie.\n\\end{document}"
  let inline (cls pre e : String) : String := s!"\\documentclass{cls}\n" ++ pre ++
    "\\begin{document}\nAlpha.\n" ++ env e ++ "\nCharlie.\n\\end{document}"
  let both (src : String) (g : Dim.Sp) : Bool := steps src abc == [leadOf src + g, leadOf src + g]
  t "kernel theorem after a blank line: topsep and partopsep above and below"
    (both (blank "{article}" kern "thm") (Dim.pt 10))
  t "kernel theorem in an open paragraph: topsep alone"
    (both (inline "{article}" kern "thm") (Dim.pt 8))
  for e in ["thm", "defn"] do
    t s!"amsthm {e}: thm@preskip and thm@postskip, the topsep, whatever the mode"
      (both (blank "{article}" ams e) (Dim.pt 8) && both (inline "{article}" ams e) (Dim.pt 8))
  t "amsthm remark: half the topsep" (both (blank "{article}" ams "rem") (Dim.pt 4))
  t "proof: 6pt over partopsep, whatever the mode"
    (both (blank "{article}" proof "proof") (Dim.pt 8) &&
     both (inline "{article}" proof "proof") (Dim.pt 8))
  t "12pt: size12's topsep and partopsep, and the proof's 6pt"
    (both (blank "[12pt]{article}" kern "thm") (Dim.pt 13) &&
     both (blank "[12pt]{article}" ams "thm") (Dim.pt 10) &&
     both (blank "[12pt]{article}" ams "rem") (Dim.pt 5) &&
     both (blank "[12pt]{article}" proof "proof") (Dim.pt 9))
  let two := dvDoc ams
    "Alpha.\n\n\\begin{thm}\nBravo.\n\\end{thm}\n\\begin{thm}\nCharlie.\n\\end{thm}\n\nDelta."
  t "two theorems meeting pay the larger of their spaces once"
    (steps two ["Alpha.", "Bravo.", "Charlie.", "Delta."] ==
      [leadOf two + Dim.pt 8, leadOf two + Dim.pt 8, leadOf two + Dim.pt 8])
  -- After a heading the head spends `\@nbitem`, as a list's first item:
  -- it stands where a paragraph after the heading stands. Kept behaviour,
  -- not a repair: this pair holds on the base too.
  let hd (b : String) : String := dvDoc ams ("\\section*{Alpha}\n" ++ b ++ "\n\nCharlie.")
  t "a theorem right after a heading stands where a paragraph after it stands"
    ((steps (hd (env "thm")) ["Alpha", "Bravo."]) == (steps (hd "Bravo.") ["Alpha", "Bravo."]) &&
      (steps (hd "Bravo.") ["Alpha", "Bravo."]).length == 1)
  -- The HTML half reads the same resolving site, in the screen's quanta.
  let page := (HtmlDoc.emit {} (elabStr (blank "{article}" ams "thm")).1).1
  let space (m : String) := s!"calc({m}rem + var(--parskip, 0rem))"
  t "html: a theorem's element carries its space's class, never a wrapper"
    (hasStr page "<div class=\"u-thm u-trivlist-ams\">")
  t "html: amsthm's theorem opens the topsep above, and over the parskip below"
    (hasStr page ":where(* + .u-trivlist-ams) { margin-top: 0.966rem; }" &&
     hasStr page s!":where(.u-trivlist-ams + *) \{ margin-top: {space "0.966"}; }")
  t "html: remark opens half of it, the proof 6pt over partopsep"
    (hasStr page ":where(* + .u-trivlist-remark) { margin-top: 0.483rem; }" &&
     hasStr page s!":where(* + .u-trivlist-proof) \{ margin-top: {space "0.966"}; }")


/-- **`\qedhere` sets the proof's QED where it stands, and the proof's end
sets none** (amsthm.sty:290–301): in text — a list's last item, the last
paragraph — amsthm's `\qed` right there, flush with the measure's right
edge; in an unnumbered display the equation number's slot, on the
formula's own line; and where this engine sets no such slot (an
alignment's row) the formula still sets, the QED stands on a line of its
own after it, and W0435 names the move. Outside a proof amsthm's stack is
empty and it sets nothing. Asserted over `Layout.Out` under the serif faces
and Fira Math (math is face 4). On the base `\qedhere` was an unknown
command in text and degraded a display to its source text (W0012), and the
end mark stood on its own line. Invented words. -/
def kernelQedHereChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fs ← serifFacesSet | t "qedhere checks: the serif faces load" false
  let run (body : String) : Array Layout.LineOut × Array Diag × Layout.Geom :=
    let (d, ds) := elabStr (dvDoc "\\usepackage{amsmath}\n\\usepackage{amsthm}\n" body)
    (bodyLines (layoutOf fs d), ds, Layout.Geom.ofPage d.page)
  let marks (ls : Array Layout.LineOut) : List Layout.LineOut :=
    ls.toList.filter fun l => (lineRuns l).any fun r => r.1 == 4 && hasStr r.2.1 "□"
  let atRight (g : Layout.Geom) (l : Layout.LineOut) : Bool :=
    (lineRuns l).any fun r => r.1 == 4 && hasStr r.2.1 "□" &&
      decide (((r.2.2.1 + r.2.2.2) - (g.hmargin + g.textWidth)).natAbs ≤ (Dim.pt 1).natAbs)
  let codes (ds : Array Diag) : List String := ds.toList.map (·.code)
  let (ls, ds, g) := run
    "\\begin{proof}\nAlder opens.\n\\begin{itemize}\n\\item Birch.\n\\item Cedar ends. \\qedhere\n\
\\end{itemize}\n\\end{proof}"
  t "qedhere in a list: one QED, at the right edge of the item's last line"
    (match marks ls with
     | [l] => atRight g l && hasStr (lineText l) "Cedar"
     | _ => false)
  t "qedhere in a list: no unknown command" (!(codes ds).contains "W0301")
  let (ls, ds, g) := run "\\begin{proof}\nAlder ends. \\qedhere\n\\end{proof}"
  t "qedhere at the last paragraph's end: one QED on its line, the command known"
    (match marks ls with
     | [l] => atRight g l && hasStr (lineText l) "Alder" && !(codes ds).contains "W0301"
     | _ => false)
  let (ls, ds, g) := run "\\begin{proof}\nAlder opens.\n\\[ x = y \\qedhere \\]\n\\end{proof}"
  t "qedhere in a display: one QED in the number's slot, on the formula's line"
    (match marks ls with
     | [l] => atRight g l && (lineRuns l).any fun r => r.1 == 4 && hasStr r.2.1 "="
     | _ => false)
  t "qedhere in a display: the formula sets, not its source"
    (!(codes ds).contains "W0012")
  let (ls, ds, g) := run
    "\\begin{proof}\nAlder opens.\n\\begin{align*}\na &= b \\qedhere\n\\end{align*}\n\\end{proof}"
  t "qedhere on an alignment's row: W0435 names the move, the formula sets"
    ((ds.any fun d => d.code == "W0435" && d.subject == some "qedhere:align*") &&
      !(codes ds).contains "W0012")
  -- The page half, which the base's text fallback happened to share.
  t "qedhere on an alignment's row: one QED, alone after the display"
    (match marks ls with
     | [l] => atRight g l && !(lineRuns l).any fun r => r.1 == 4 && hasStr r.2.1 "="
     | _ => false)
  let (ls, ds, _) := run "Alder ends. \\qedhere\n\n\\[ x = y \\qedhere \\]"
  t "qedhere outside a proof sets nothing, unnamed"
    ((marks ls).isEmpty && !(codes ds).contains "W0301" && !(codes ds).contains "W0435")


/-- **`verse` is a quotation of lines**: a block of its own between the
paragraphs around it, both margins in by the list indent, each `\\` a new
line one leading below the last (latex.ltx `verse`: `\list` with
`\rightmargin\leftmargin`, `\\` as `\@centercr`), and HTML's
`<blockquote>`. On the merge base the environment was unknown and its lines
merged into the paragraph before it. Invented content. -/
def kernelVerseChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let src := dvDoc "" "Alder opens.\n\\begin{verse}\nBirch is a line of verse\\\\\nCedar is the next line\n\\end{verse}\nDogwood closes.\n"
  let (doc, ds) := elabStr src
  t "verse: the environment elaborates clean"
    (ds.all fun d => d.severity != .warning && d.severity != .error)
  let geom := Layout.Geom.ofPage doc.page
  let ls := bodyLines (layoutOf oneFace doc geom)
  let lineWith (w : String) : Option Layout.LineOut := ls.find? fun l => hasStr (lineText l) w
  t "verse: its lines are not the paragraph before"
    ((lineWith "Birch").any fun l => (lineText l).startsWith "Birch")
  t "verse: both margins move in by the list indent"
    (["Birch", "Cedar"].all fun w => (lineWith w).any fun l =>
      l.x == geom.hmargin + geom.listIndent &&
        decide (l.x + l.setWidth ≤ geom.hmargin + geom.textWidth - geom.listIndent))
  t "verse: each \\\\ opens the next indented line one leading below"
    (match lineWith "Birch", lineWith "Cedar" with
     | some a, some b => a.x == geom.hmargin + geom.listIndent &&
         b.y - a.y == Ir.leadingFor geom.fontSize geom.leading
     | _, _ => false)
  t "verse: the text after it keeps the full measure, the verse does not"
    ((lineWith "Dogwood").any fun l => l.x == geom.hmargin &&
      (lineWith "Cedar").any fun c => c.x == geom.hmargin + geom.listIndent)
  t "html: verse is a blockquote"
    (hasStr (HtmlDoc.emit {} doc).1 "<blockquote>")


/-- **A description item runs its bold label in at the list's outer margin,
`\labelsep` before its text, and hangs every further line at the item's
indent** (latex.ltx `description`: `\labelwidth\z@`,
`\itemindent-\leftmargin`, `\descriptionlabel` bold): no marker glyph, the
list's vertical space itemize's, and HTML's own `<dl>`. On the merge base
the environment was unknown and every `\item` in it was E0312: the build
failed. Asserted over `Layout.Out` under the serif faces (bold is face 1).
Invented content. -/
def kernelDescChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fs ← serifFacesSet | t "description checks: the serif faces load" false
  let long := "a described term whose text runs long enough to wrap onto a second line of the list"
  let src := dvDoc "" ("Alder opens.\n\\begin{description}\n\\item[Birch] " ++ long ++
    ".\n\\item[Cedar] follows.\n\\item plain words.\n\\end{description}\nDogwood closes.\n")
  let (doc, ds) := elabStr src
  t "description: the environment and its items elaborate clean"
    (ds.all fun d => d.severity != .warning && d.severity != .error)
  let geom := Layout.Geom.ofPage doc.page
  let ls := bodyLines (layoutOf fs doc geom)
  let lineWith (w : String) : Option Layout.LineOut := ls.find? fun l => hasStr (lineText l) w
  t "description: the label opens its line at the list's outer margin, no marker before it"
    ((lineWith "Birch").any fun l => l.x == geom.hmargin && (lineText l).startsWith "Birch")
  t "description: the label is bold, the text after it is not"
    ((lineWith "Birch").any fun l => faceOfWord l "Birch" == some 1 && faceOfWord l "described" == some 0)
  -- Read on an item's last line, which is set at its natural width: a
  -- justified line's font expansion scales every box on it, a kern too.
  t "description: \\labelsep between the label and the text"
    ((lineWith "Cedar").any fun l =>
      let rs := (lineRuns l).filter (!·.2.1.isEmpty)
      match rs[0]?, rs[1]? with
      | some a, some b => a.2.1 == "Cedar" && b.2.2.1 - (a.2.2.1 + a.2.2.2) == Dim.pt 5
      | _, _ => false)
  t "description: a wrapped line hangs at the item's indent"
    (ls.any fun l => l.x == geom.hmargin + geom.listIndent && !hasStr (lineText l) "Birch" &&
      (hasStr (lineText l) "line" || hasStr (lineText l) "list"))
  t "description: an unlabelled item opens \\labelsep from the outer margin"
    ((lineWith "plain").any fun l =>
      (((lineRuns l).find? (hasStr ·.2.1 "plain")).map (·.2.2.1)) == some (l.x + Dim.pt 5))
  -- The vertical space is the list's: one-line items stand where the same
  -- items of an itemize stand.
  let short (env pre : String) : String := dvDoc "" ("Alder opens.\n\\begin{" ++ env ++
    "}\n\\item" ++ pre ++ " Birch.\n\\item" ++ pre ++ " Cedar.\n\\end{" ++ env ++ "}\nDogwood closes.\n")
  let ys (s : String) : List Dim.Sp :=
    let xs := bodyLines (layoutOf fs (elabStr s).1 geom)
    ["Alder", "Birch", "Cedar", "Dogwood"].filterMap fun w =>
      (xs.find? fun l => hasStr (lineText l) w).map (·.y)
  t "description: its items stand where itemize's do"
    (ys (short "description" "[Term]") == ys (short "itemize" "") &&
      (ys (short "itemize" "")).length == 4)
  let page := (HtmlDoc.emit {} doc).1
  t "html: a description is a dl of dt and dd"
    (hasStr page "<dl>" && hasStr page "<strong>Birch</strong>" &&
      hasStr page "<dd>follows.</dd>")
