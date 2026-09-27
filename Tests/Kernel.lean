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
      out := out.push (idx, String.ofList (gs.map (·.2)).toList, x, w)
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
  t "remark: the body is upright" (face "Fir" == some 0)
  t "theorem: the text after it is upright again" (face "Hazel" == some 0)
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
  let noQed := linesOf (dvDoc "\\usepackage{amsthm}\n"
    "\\begin{proof}\n\\renewcommand{\\qedsymbol}{}Maple ends bare.\n\\end{proof}")
  t "proof: an emptied \\qedsymbol omits the mark"
    ((lineWith noQed "Maple").any fun l => !(lineRuns l).any (hasStr ·.2.1 "□"))
  t "proof: without amsthm the environment is unknown, as LaTeX has it"
    ((warnCodes (dvDoc "" "\\begin{proof}\nx\n\\end{proof}")).contains "W0302")
  t "theoremstyle: a style the engine has not is named"
    ((elabStr (dvDoc "\\usepackage{amsthm}\n\\theoremstyle{fancy}\n" "x")).2.any fun d =>
      d.code == "W0110" && d.subject == some "theoremstyle:fancy")
  -- HTML: the environment's name as its class, the head as strong text.
  let page := (HtmlDoc.emit {} (elabStr src).1).1
  t "html: a theorem is its own block under the environment's name"
    (hasStr page "<div class=\"u-thm u-trivlist-env\">")
  t "html: the head is strong, the number upright"
    (hasStr page "<strong>Theorem <span class=\"up\">1.1</span></strong><strong>.</strong>")


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
  t "verse: each \\\\ opens the next line one leading below"
    (match lineWith "Birch", lineWith "Cedar" with
     | some a, some b => b.y - a.y == Ir.leadingFor geom.fontSize geom.leading
     | _, _ => false)
  t "verse: the text after it keeps the full measure"
    ((lineWith "Dogwood").any fun l => l.x == geom.hmargin)
  t "html: verse is a blockquote"
    (hasStr (HtmlDoc.emit {} doc).1 "<blockquote>")
