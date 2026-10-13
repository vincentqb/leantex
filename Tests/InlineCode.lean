module

public import Tests.Support
public import Tests.ShellHighlight
public import LeanTex.Cli.ListingHighlight

public section

open LeanTex.Core

namespace Tests.InlineCode

/-- A face set whose run faces tell slot, weight and slant apart: serif indices 0–3 and mono 4–7,
each regular, bold, italic and both. -/
def facesSet : IO (Option Font.FontSet) := do
  let mut loaded : Array Font.Font := #[]
  for n in #["SourceSerifPro-Regular.otf", "SourceSerifPro-Bold.otf",
      "SourceSerifPro-RegularIt.otf", "SourceSerifPro-BoldIt.otf",
      "SourceCodePro-Regular.otf"] do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    match Font.parse (← IO.FS.readBinFile p) with
    | .ok f => loaded := loaded.push f
    | .error _ => return none
  let some mono := loaded[4]? | return none
  return some {
    fonts := loaded.pop ++ #[mono, mono, mono, mono]
    index := ((List.range 3).flatMap fun slot =>
      let base := if slot == 2 then 4 else 0
      [((slot, 400, false), base), ((slot, 700, false), base + 1),
       ((slot, 400, true), base + 2), ((slot, 700, true), base + 3)]).toArray }

/-- One shipped glyph: its scalar, the face it sets in, its size and ink,
and whether its line is furniture (a footer's, say). -/
structure Glyph where
  c : Char
  face : Nat
  size : Dim.Sp
  color : Ir.Color
  furniture : Bool
  y : Dim.Sp
  deriving BEq, Repr

def glyphs (out : Layout.Out) : Array Glyph := Id.run do
  let mut acc := #[]
  for p in out.pages do
    for l in p.lines do
      for seg in l.segs do
        match seg with
        | .run face color _ _ gs size _ _ _ _ _ =>
          for (_, c, _) in gs do
            acc := acc.push { c, face, size, color, furniture := l.furniture, y := l.y }
        | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .poly .. | .image .. =>
          pure ()
  return acc

def mono (g : Glyph) : Bool := g.face ≥ 4
def bold (g : Glyph) : Bool := g.face % 4 == 1 || g.face % 4 == 3
def italic (g : Glyph) : Bool := g.face % 4 == 2 || g.face % 4 == 3

/-- The `k`th run of glyphs spelling `w` whose glyphs all satisfy `p`. -/
def word? (gs : Array Glyph) (w : String) (p : Glyph → Bool := fun _ => true)
    (k : Nat := 0) : Option (Array Glyph) := Id.run do
  let cs := w.toList.toArray
  let mut seen := 0
  for i in [0:gs.size] do
    let run := gs.extract i (i + cs.size)
    if run.size == cs.size && (run.zip cs).all (fun (g, c) => g.c == c && p g) then
      if seen == k then return some run
      seen := seen + 1
  return none

/-- One look shared by every glyph of `gs`: its face, size and ink. -/
def look (gs : Array Glyph) : Option (Nat × Dim.Sp × Ir.Color) :=
  match gs[0]? with
  | some g =>
    if gs.all (fun h => h.face == g.face && h.size == g.size && h.color == g.color) then
      some (g.face, g.size, g.color)
    else none
  | none => none

mutual

/-- The inline code elements of a tree: `code` outside any `pre`. -/
def inlineCodesOne (acc : Array Html.Node) (inPre : Bool) : Html.Node → Array Html.Node
  | n@(.elem tag _ kids) =>
    let acc := if tag == "code" && !inPre then acc.push n else acc
    inlineCodesList acc (inPre || tag == "pre") kids.toList
  | .text _ | .style _ | .script .. => acc

def inlineCodesList (acc : Array Html.Node) (inPre : Bool) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => inlineCodesList (inlineCodesOne acc inPre n) inPre rest

end

/-- An element's own attribute. -/
def attr? (n : Html.Node) (key : String) : Option String :=
  match n with
  | .elem _ attrs _ => HtmlDoc.attrOf? attrs key
  | _ => none

/-- The text an element's own text children hold. -/
def ownText (n : Html.Node) : String :=
  match n with
  | .elem _ _ kids => kids.foldl (fun s k => match k with
    | .text t => s ++ t
    | _ => s) ""
  | _ => ""

/-- The texts of the spans inside `n` that paint their own colour. -/
def paintedTexts (n : Html.Node) : Array String :=
  (elemNodesList (· == "span") #[] [n]).filterMap fun s =>
    match attr? s "style" with
    | some st => if hasStr st "color" then some (nodeTextOne "" s) else none
    | none => none

/-- The texts `strong` holds inside `n`. -/
def strongTexts (n : Html.Node) : Array String :=
  (elemNodesList (· == "strong") #[] [n]).map (nodeTextOne "")

def spaced (s : String) : String := s.map fun c => if c == '\u00a0' then ' ' else c

/-- The elements of a tree under `outer`'s that are inline code. -/
def codesUnder (body : Array Html.Node) (outer : Html.Node → Bool) : Array Html.Node :=
  (elemNodesList (fun _ => true) #[] body.toList).filter outer |>.foldl
    (fun acc n => inlineCodesOne acc false n) #[]

def classHas (n : Html.Node) (cls : String) : Bool :=
  ((attr? n "class").getD "").splitOn " " |>.contains cls

def tagIs (n : Html.Node) (tag : String) : Bool :=
  match n with
  | .elem t _ _ => t == tag
  | _ => false

/-- The size classes of the spans that hold an inline code element as their
own child, in tree order. -/
def sizesAround (body : Array Html.Node) : Array String :=
  (elemNodesList (· == "span") #[] body.toList).filterMap fun n =>
    match n with
    | .elem _ attrs kids =>
      if kids.any (fun k => tagIs k "code") then
        ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " " |>.find? (·.startsWith "size-")
      else none
    | _ => none

/-- The size the first mono `probe` ships at. -/
def probeSize (gs : Array Glyph) : Option Dim.Sp :=
  ((word? gs "probe" mono).bind look).map (·.2.1)

def deckSrc (pre body : String) : String :=
  "\\documentclass{beamer}\n\\usepackage{minted}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
    "\n\\end{document}"

def mintedDoc (pre body : String) : String := dvDoc ("\\usepackage{minted}\n" ++ pre) body

end InlineCode

open InlineCode

/-- Inline code is text: it takes the size, weight, slant and colour where it stands and only its
family becomes mono, its tokens in their roles' colours, in both artifacts and every context. -/
def inlineCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← facesSet | failures ref "inline code: the shipped faces did not load"
  let shipped (src : String) := glyphs (layoutOf fonts (elabStr src).1)
  let html (src : String) : Array Html.Node × String :=
    let (head, body, _) := HtmlDoc.emitTree {} (elabStr src).1
    (body, treeCssList "" head.toList)
  let quiet (src : String) := (elabStr src).2.all fun d =>
    d.severity != .warning && d.severity != .error
  let para := mintedDoc ""
    ("Alpha \\mintinline{python}{def probe(arg): return arg} omega.\n\n" ++
     "\\begin{minted}{python}\ndef probe(arg): return arg\n\\end{minted}")
  let gs := shipped para
  t "inline code: no warning names \\mintinline" (quiet para)
  match look <$> word? gs "Alpha", look <$> word? gs "probe" mono, look <$> word? gs "def" mono,
      look <$> word? gs "def" mono 1 with
  | some (some (_, size, ink)), some (some pf), some (some df), some (some display) =>
    t "inline code: an ink token sets regular mono at the size and ink around it"
      (pf == (4, size, ink))
    t "inline code: a keyword sets bold mono in its role's colour, a display listing's"
      (df.1 == 5 && df.2.1 == size && df.2.2 == display.2.2 && display.2.2 != ink)
  | _, _, _, _ => failures ref "inline code: the paragraph's words did not ship"
  t "inline code: the paragraph's line ships the code's scalars in order, in mono"
    ((word? gs "Alpha").any fun a => a.all fun g =>
      String.ofList ((gs.filter fun h => h.y == g.y && mono h && !h.c.isWhitespace &&
        h.c != '\u00a0').toList.map (·.c)) == "defprobe(arg):returnarg")
  let (body, css) := html para
  let codes := inlineCodesList #[] false body.toList
  t "inline code html: the code element holds the source, set in no style of its own"
    (codes.size == 1 && codes.all fun c =>
      spaced (nodeTextOne "" c) == "def probe(arg): return arg" && (attr? c "style").isNone)
  t "inline code html: a keyword is strong in a painted span, an ink token is the code's own text"
    (codes.all fun c => (strongTexts c).contains "def" && (paintedTexts c).contains "def" &&
      hasStr (spaced (ownText c)) "probe(arg)")
  t "inline code html: no stylesheet rule sizes code"
    ((cssRulesOf css "code, pre").all (!hasStr · "font-size") && !hasStr css "0.925em" &&
      (cssRulesOf css "pre > code").isEmpty)
  for (label, src, outer, want) in [
      ("bold", "\\textbf{Bold \\mintinline{python}{def probe(arg)}}", "Bold",
        fun (g : Glyph) => mono g && bold g && !italic g),
      ("italic", "\\textit{Slant \\mintinline{python}{def probe(arg)}}", "Slant",
        fun (g : Glyph) => mono g && italic g && !bold g),
      ("size", "{\\scriptsize Small \\mintinline{python}{def probe(arg)}}", "Small",
        fun (g : Glyph) => mono g && !bold g && !italic g),
      ("colour", "\\textcolor{blue}{Blue \\mintinline{python}{def probe(arg)}}", "Blue",
        fun (g : Glyph) => mono g && !bold g && !italic g)] do
    let src := mintedDoc "\\usepackage{xcolor}\n" ("Alpha " ++ src ++ " omega.")
    let gs := shipped src
    match look <$> word? gs outer, look <$> word? gs "probe" want, look <$> word? gs "def" mono,
        look <$> word? gs "Alpha" with
    | some (some (_, size, ink)), some (some (_, psize, pink)), some (some (dface, dsize, dink)),
        some (some (_, bodySize, bodyInk)) =>
      t s!"inline code {label}: an ink token takes the size and ink around it"
        (psize == size && pink == ink)
      t s!"inline code {label}: a keyword's bold adds to the weight around it"
        (dsize == size && (dface == 5 || dface == 7) && dink != ink)
      if label == "size" then
        t "inline code size: the size around it is the context's, not the body's"
          (size < bodySize)
      if label == "colour" then
        t "inline code colour: the colour around it is the context's"
          (ink != bodyInk)
    | _, _, _, _ => failures ref s!"inline code {label}: the words did not ship"
    let (body, _) := html src
    let codes := inlineCodesList #[] false body.toList
    t s!"inline code {label} html: the code sets no style of its own and its ink token none"
      (codes.size == 1 && codes.all fun c =>
        (attr? c "style").isNone && hasStr (spaced (ownText c)) "probe(arg)")
  let deck := deckSrc
    ("\\newenvironment{codefoot}[1]{\\setbeamertemplate{frame footer}{{\\scriptsize #1}}}" ++
      "{\\setbeamertemplate{frame footer}{}}\n")
    ("\\begin{codefoot}{Rule: \\mintinline{lean4}{theorem probe {a : Nat} : a = a}}\n" ++
     "\\begin{frame}{Heading \\mintinline{python}{size_of}}\n" ++
     "\\begin{block}{Title \\mintinline{python}{show_all} here}\n" ++
     "Body \\mintinline{python}{def probe(arg)} text.\n" ++
     "\\end{block}\n\\end{frame}\n\\end{codefoot}")
  t "inline code contexts: no warning names \\mintinline" (quiet deck)
  let gs := shipped deck
  match look <$> word? gs "Rule" (·.furniture), look <$> word? gs "probe" (fun g => mono g && g.furniture),
      word? gs "theorem" (fun g => mono g && g.furniture) with
  | some (some (_, size, ink)), some (some (face, psize, pink)), some kw =>
    t "inline code footer: the code sets at the footer's size, its ink token in the footer's ink"
      (face == 4 && psize == size && pink == ink)
    t "inline code footer: its keyword is bold at the footer's size"
      (kw.all fun g => bold g && g.size == size)
  | _, _, _ => failures ref "inline code footer: the footer's words did not ship"
  for (label, outer, code) in [("frame title", "Heading", "size_of"), ("block title", "Title", "show_all"),
      ("block body", "Body", "probe")] do
    match look <$> word? gs outer (!·.furniture), look <$> word? gs code (fun g => mono g && !g.furniture) with
    | some (some (face, size, ink)), some (some (cface, csize, cink)) =>
      t s!"inline code {label}: the code sets at the size, weight, slant and ink around it"
        (csize == size && cface == face + 4 && cink == ink)
    | _, _ => failures ref s!"inline code {label}: the words did not ship"
  let (body, _) := html deck
  let footCodes := codesUnder body fun n => tagIs n "footer" && classHas n "slide-foot"
  t "inline code footer html: the footer holds the code, painting its ink token nothing"
    (footCodes.size == 1 && footCodes.all fun c =>
      (attr? c "style").isNone && hasStr (spaced (ownText c)) "probe" &&
        (strongTexts c).contains "theorem")
  t "inline code frame title html: the title's heading holds the code"
    ((codesUnder body (tagIs · "h2")).any fun c => nodeTextOne "" c == "size_of")
  t "inline code block title html: the block's header holds the code"
    ((codesUnder body fun n => tagIs n "header" && !hasStr (nodeTextOne "" n) "Heading").any
      fun c => nodeTextOne "" c == "show_all")
  -- minted's layers: `\setminted`, then `\setmintedinline`, then the command's own options.
  let sizes := "{\\footnotesize Foot} {\\large Large} {\\tiny Tiny} {\\Huge Huge} "
  let sizeOf (gs : Array Glyph) (w : String) : Option Dim.Sp :=
    (word? gs w).bind fun r => (look r).map (·.2.1)
  for (label, pre, code, want) in [
      ("\\setminted reaches inline code", "", "\\mintinline{python}{probe}", "Foot"),
      ("\\setmintedinline{fontsize=\\relax} keeps the size around it",
        "\\setmintedinline{fontsize=\\relax}\n", "\\mintinline{python}{probe}", "Small"),
      ("\\setmintedinline sets inline code's size", "\\setmintedinline{fontsize=\\large}\n",
        "\\mintinline{python}{probe}", "Large"),
      ("the command's own option wins", "\\setmintedinline{fontsize=\\large}\n",
        "\\mintinline[fontsize=\\tiny]{python}{probe}", "Tiny"),
      ("a lexer's inline layer wins over the global one",
        "\\setmintedinline{fontsize=\\large}\n\\setmintedinline[python]{fontsize=\\Huge}\n",
        "\\mintinline{python}{probe}", "Huge"),
      ("another lexer keeps the global inline layer",
        "\\setmintedinline{fontsize=\\large}\n\\setmintedinline[python]{fontsize=\\Huge}\n",
        "\\mintinline{bash}{probe}", "Large")] do
    let src := mintedDoc ("\\setminted{fontsize=\\footnotesize}\n" ++ pre)
      (sizes ++ "{\\scriptsize Small " ++ code ++ "}")
    let gs := shipped src
    t s!"inline code layers: {label}"
      (quiet src && (sizeOf gs want).isSome && probeSize gs == sizeOf gs want)
    let step := match want with
      | "Foot" => "footnotesize"
      | "Small" => "scriptsize"
      | "Large" => "large"
      | "Tiny" => "tiny"
      | _ => want
    t s!"inline code layers html: {label}"
      (sizesAround (html src).1 == #["size-" ++ step])
  let wrapped := mintedDoc ("\\newcommand{\\py}[1]{\\mintinline{python}{#1}}\n" ++
      "\\newcommand{\\code}[2]{\\mintinline{#1}{#2}}\n")
    "Alpha \\py{def probe(arg)} beta \\code{python}{return arg} omega."
  let direct := mintedDoc ""
    "Alpha \\mintinline{python}{def probe(arg)} beta \\mintinline{python}{return arg} omega."
  t "inline code: a definition's parameter is its argument's code, as LaTeX binds it"
    (quiet wrapped && shipped wrapped == shipped direct)
  -- A parameter binds the argument's source, never its elaboration.
  let tricky := "d = {\"k\": 'v'} -- x~y"
  for (label, pre, call) in [
      ("xparse's definer", "\\NewDocumentCommand{\\pya}{m}{\\mintinline{python}{#1}}\n",
        "\\pya{" ++ tricky ++ "}"),
      ("a robust definition", "\\DeclareRobustCommand{\\pyb}[1]{\\mintinline{python}{#1}}\n",
        "\\pyb{" ++ tricky ++ "}"),
      ("an environment's argument",
        "\\newenvironment{codebox}[1]{\\mintinline{python}{#1}}{}\n",
        "\\begin{codebox}{" ++ tricky ++ "}\\end{codebox}")] do
    let src := mintedDoc pre ("Alpha " ++ call ++ " omega.")
    let inked := (shipped src).filter fun g => mono g && !g.c.isWhitespace && g.c != '\u00a0'
    t s!"inline code: {label} binds its argument's source as the code"
      (quiet src && String.ofList (inked.toList.map (·.c)) == "d={\"k\":'v'}--x~y")
  let shortcut := mintedDoc "\\newcommand{\\py}{\\mintinline{python}}\n"
    "Alpha \\py{def probe(arg)} beta \\py|return arg| omega."
  t "inline code: a shortcut to minted's command and the code after its use are the call"
    (quiet shortcut && shipped shortcut == shipped direct)
  t "inline code: a parameter outside any definition is the code it spells"
    ((word? (shipped (mintedDoc "" "Alpha \\mintinline{python}{#1} omega.")) "#1" mono).isSome)
  for definer in ["\\renewcommand{\\mintinline}[2]{\\textbf{#2}}",
      "\\renewcommand\\mintinline[2]{\\textbf{#2}}"] do
    let mine := mintedDoc (definer ++ "\n") "Alpha \\mintinline{python}{probe} omega."
    t "inline code: a document's own \\mintinline is the command its calls run"
      ((word? (shipped mine) "probe" fun g => !mono g && bold g).isSome)
  let standout := deckSrc "\\usetheme{metropolis}\n"
    ("\\begin{frame}[fragile,standout]\nWord \\mintinline{python}{probe = 42} here.\n" ++
     "\\begin{minted}{python}\nprobe = 42\n\\end{minted}\n\\end{frame}")
  let gs := shipped standout
  match look <$> word? gs "42" mono, look <$> word? gs "42" mono 1 with
  | some (some (_, _, inl)), some (some (_, _, disp)) =>
    t "inline code standout: its literal ships the listing's ink on the frame's ground" (inl == disp)
  | _, _ => failures ref "inline code standout: the frame's words did not ship"
  -- Read as print paints the page, a token's class colour its own.
  let (_, sbody, _) := emitIn {} (elabStr standout).1 .print
  let spanColors (n : Html.Node) := (elemNodesList (· == "span") #[] [n]).filterMap fun sp =>
    if nodeTextOne "" sp == "42" then attr? sp "style" else none
  -- The literal colour a style states, its custom property's fallback included.
  let hex (style : String) : String := ((style.splitOn "#").getLast?.getD "").take 6 |>.toString
  t "inline code standout html: its literal states the listing's ink"
    (match (inlineCodesList #[] false sbody.toList).flatMap spanColors,
        (elemNodesList (· == "pre") #[] sbody.toList).flatMap spanColors with
     | #[a], #[b] => hex a == hex b && !(hex a).isEmpty
     | _, _ => false)
  -- minted ignores a display's keys on inline code.
  let plainPage := shipped (mintedDoc "" "Alpha \\mintinline{python}{def probe(arg)} omega.")
  let keyed := mintedDoc "\\setminted{linenos,frame=single,xleftmargin=2em}\n"
    "Alpha \\mintinline{python}{def probe(arg)} omega."
  t "inline code: a display's keys reach no inline code, as minted reads them"
    (quiet keyed && shipped keyed == plainPage)
  -- `\mint` is the minted environment of one line.
  let mintPage := mintedDoc "" "Alpha.\n\n\\mint{python}|probe = 1|\n\nOmega."
  let envPage := mintedDoc "" "Alpha.\n\n\\begin{minted}{python}\nprobe = 1\n\\end{minted}\n\nOmega."
  t "\\mint: the page and the HTML of the one-line environment"
    (quiet mintPage && shipped mintPage == shipped envPage &&
      ((html mintPage).1.map (Html.render · 0)) == ((html envPage).1.map (Html.render · 0)))
  let named (src : String) := (elabStr src).2.filter (·.code == "W0411")
  for (label, code, src) in [
      ("\\mint in an argument", "W0413", "\\textbf{Alpha \\mint{python}{def probe(arg)} omega}"),
      ("an environment in an argument", "W0411",
        "\\textbf{Alpha \\begin{minted}{python}\ndef probe(arg)\n\\end{minted} omega}"),
      ("an environment on a line of text", "W0411",
        "Alpha \\begin{minted}{python}def probe(arg)\\end{minted} omega.")] do
    let src := mintedDoc "" src
    let gs := shipped src
    let ds := (elabStr src).2
    let ws := ds.filter (·.code == code)
    t s!"inline code {label}: named once, by its own code"
      (ws.size == 1 && ws.all (·.severity == .warning) &&
        !(ds.any fun d => d.code == "W0346" || (d.code != code && (d.code == "W0411" || d.code == "W0413"))))
    match word? gs "Alpha", word? gs "probe" mono, word? gs "def" mono with
    | some a, some p, some d =>
      t s!"inline code {label}: set as inline code on the line of text, its keyword painted"
        ((a.all fun g => p.all (·.y == g.y)) && d.all bold &&
          (d.all fun g => (word? gs "Alpha").any (·.all (·.color != g.color))))
    | _, _, _ => failures ref s!"inline code {label}: the words did not ship"
  let twice := mintedDoc ""
    "Alpha \\begin{minted}{python}x\\end{minted} beta \\begin{minted}{python}y\\end{minted} omega."
  t "inline code: a second listing written so is a note under the first"
    ((named twice).size == 2 && ((named twice).filter (·.severity == .warning)).size == 1)
  for (label, body) in [
      ("in its paragraph", "Alpha.\n\n\\begin{minted}{python}def probe(arg)\\end{minted}\n\nOmega."),
      ("after a heading, before a list", "\\section{S}\n\\begin{minted}{python}def probe(arg)\\end{minted}\n" ++
        "\\begin{itemize}\\item i\n\\end{itemize}"),
      ("after a label", "\\label{lab}\\begin{minted}{python}def probe(arg)\\end{minted}\n\nOmega."),
      ("before a heading", "\\begin{minted}{python}def probe(arg)\\end{minted}\n\\section{T}")] do
    let alone := mintedDoc "" body
    t s!"a one-line listing alone {label} is named and set as a display"
      ((named alone).size == 1 && (named alone).all (fun d => d.help.any (hasStr · "lines of its own")) &&
        !(elemNodesList (· == "pre") #[] (html alone).1.toList).isEmpty)
  let unknown (src : String) := (elabStr src).2.filter (·.code == "W0412")
  let typo := mintedDoc "" "Alpha \\mintinline{pyhton}{def probe} omega."
  t "inline code: a misspelt lexer is named with the nearest lexer as its help"
    ((unknown typo).size == 1 && (unknown typo).all fun d => d.help.any (hasStr · "'python'"))
  t "inline code: a misspelt lexer's code ships plain"
    ((word? (shipped typo) "def" mono).any fun r => r.all (!bold ·))
  let envTypo := (elabStr (mintedDoc "" "\\begin{minted}{pyhton}\ndef probe\n\\end{minted}")).1
  t "a listing whose lexer no lexer of the engine reads is named, and asked of the installed one"
    ((unknown (mintedDoc "" "\\begin{minted}{pyhton}\ndef probe\n\\end{minted}")).size == 1 &&
      (ListingReply.requests envTypo).size == 1)
  let listings := unknown (dvDoc "\\usepackage{listings}\n"
    "\\begin{lstlisting}[language=Elan]\nr = 8\n\\end{lstlisting}")
  t "a listings language no lexer reads is named with no respelling to suggest"
    (listings.size == 1 && listings.all (·.help.isNone))
  t "a short name is too short to judge a slip in"
    ((unknown (mintedDoc "" "Alpha \\mintinline{csv}{x} omega.")).all fun d =>
      !d.help.any (hasStr · "spell it"))
  t "a lexer only the highlighter reads is no unknown lexer"
    ((unknown (mintedDoc "" "\\begin{minted}{ruby}\nputs 1\n\\end{minted}")).isEmpty &&
      (unknown (mintedDoc "" "Alpha \\mintinline{ruby}{puts 1} omega.")).isEmpty)
  let far := unknown (mintedDoc "" "Alpha \\mintinline{zzqqxxww}{x} omega.")
  t "a lexer name near no known one is named with the registry's own spellings"
    (far.size == 1 && far.all fun d => d.help.any (hasStr · "'python'"))
  -- A comment between the command and its language is TeX's to skip.
  let commented := mintedDoc "" "Alpha \\mintinline%\n{python}{def probe(arg)} omega."
  t "inline code: a comment between the command and its language is skipped"
    (quiet commented && (word? (shipped commented) "probe" mono).isSome)
  let provided := mintedDoc "\\providecommand{\\mintinline}[2]{\\textbf{#2}}\n"
    "Alpha \\mintinline{python}{def probe(arg)} omega."
  t "inline code: a provision of minted's command keeps minted's"
    ((word? (shipped provided) "probe" mono).isSome)
  -- `\setmintedinline` reaches inline code alone, never `\mint`'s display.
  let block := mintedDoc "\\setminted{fontsize=\\footnotesize}\n\\setmintedinline{fontsize=\\tiny}\n"
    "{\\footnotesize Foot}\n\n\\mint{python}|probe = 1|"
  t "\\mint takes \\setminted's layers and none of \\setmintedinline's"
    ((sizeOf (shipped block) "Foot").isSome && probeSize (shipped block) == sizeOf (shipped block) "Foot")
  for (label, pre, opts) in [("\\relax", "", "[fontsize=\\relax]"),
      ("a \\setminted \\relax", "\\setminted{fontsize=\\relax}\n", "")] do
    let src := mintedDoc pre
      ("{\\small Small\n\n\\begin{minted}" ++ opts ++ "{text}\nprobe\n\\end{minted}\n}")
    let gs := shipped src
    t s!"display listing {label}: keeps the size around it, named nothing"
      (quiet src && (sizeOf gs "Small").isSome && sizeOf gs "Small" == probeSize gs)
  let declared := mintedDoc "\\setminted{fontsize=\\footnotesize}\n"
    ("{\\footnotesize Foot}\n\n{\\scriptsize Small\n\n\\begin{minted}{text}\nprobe\n\\end{minted}\n}")
  t "display listing: the declared size is the body's step, not the context's"
    ((sizeOf (shipped declared) "Foot").isSome &&
      sizeOf (shipped declared) "Foot" == probeSize (shipped declared))
  let alert := deckSrc "\\setbeamercolor{block body alerted}{fg=red!70!black}\n"
    ("\\begin{frame}[fragile]{F}\n\\begin{alertblock}{A}\nWord.\n" ++
     "\\begin{minted}{python}\nprobe(1)\n\\end{minted}\n\\end{alertblock}\n\\end{frame}")
  match look <$> word? (shipped alert) "Word", look <$> word? (shipped alert) "probe" mono with
  | some (some (_, _, ink)), some (some (_, _, pink)) =>
    t "display listing: its ink token takes the alert block's ink" (pink == ink)
    t "display listing html: the listing states the alert block's ink"
      ((elemNodesList (· == "pre") #[] (html alert).1.toList).any fun p =>
        (attr? p "style").any (hasStr · s!"color: {HtmlDoc.cssColor ink}"))
  | _, _ => failures ref "display listing: the alert block's words did not ship"

/-- Inline code in a language only the highlighter reads asks it through the
driver, as a listing does, and its answer paints the code on re-elaboration;
no answer leaves the code plain. -/
def inlineCodeRequestChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let src := mintedDoc "" "Alpha \\mintinline{fish}{echo $HOME} omega."
  let (toks, ld) := Lex.lex "inline.tex" src
  let (raws, pd) := Parse.parse "inline.tex" toks
  let base := Elab.prepare "inline" raws
  let (cold, _, spans) := Elab.runPrepared "inline" base (ld ++ pd)
  let requests := ListingReply.requests cold spans.code
  t "inline code request: one exact request for the code"
    (requests.size == 1 && requests.all fun r => r.language == "fish" && r.source == "echo $HOME")
  let some request := requests[0]? | failures ref "inline code request: no request"
  let reply := ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request #[
    ShellHighlight.shellTokenJson 0 "Token.Name.Builtin" "echo",
    ShellHighlight.shellTokenJson 4 "Token.Text" " ",
    ShellHighlight.shellTokenJson 5 "Token.Name.Variable" "$HOME\n"]]
  let .ok (answers, refused) := ListingReply.decode requests reply (terminalLf := true)
    | failures ref "inline code request: the synthetic reply was rejected"
  t "inline code request: the reply classifies the code" refused.isEmpty
  let (doc, _, _) := Elab.runPrepared "inline" { base with listingReplies := answers } (ld ++ pd)
  let (_, body, _) := HtmlDoc.emitTree {} doc
  let (_, coldBody, _) := HtmlDoc.emitTree {} cold
  let painted := (inlineCodesList #[] false body.toList).flatMap paintedTexts
  let builtin := (Listing.ink doc.palette none ⟨"Name.Builtin"⟩).isSome
  t "inline code request: the answer paints the code; none leaves it plain"
    ((inlineCodesList #[] false coldBody.toList).all (paintedTexts · |>.isEmpty) &&
      (!builtin || painted.any (hasStr · "echo")))
  let src := mintedDoc "" "Alpha \\mintinline{pyhton}{def probe} omega."
  let (toks, ld) := Lex.lex "inline.tex" src
  let (raws, pd) := Parse.parse "inline.tex" toks
  let base := Elab.prepare "inline" raws
  let (cold, coldDs, spans) := Elab.runPrepared "inline" base (ld ++ pd)
  let requests := ListingReply.requests cold spans.code
  t "inline code request: a language outside the registry is asked, and named while unanswered"
    (requests.size == 1 && (coldDs.filter (·.code == "W0412")).size == 1)
  let some request := requests[0]? | failures ref "inline code request: no request outside the registry"
  let answer := ShellHighlight.shellBatchJson #[ShellHighlight.shellSuccessJson request #[
    ShellHighlight.shellTokenJson 0 "Token.Keyword" "def",
    ShellHighlight.shellTokenJson 3 "Token.Text" " ",
    ShellHighlight.shellTokenJson 4 "Token.Name" "probe\n"]]
  let refusal := ShellHighlight.shellBatchJson #[ShellHighlight.shellFailureJson request "unsupported"]
  match ListingReply.decode requests answer (terminalLf := true),
      ListingReply.decode requests refusal (terminalLf := true) with
  | .ok (answers, refused), .ok (plain, failed) =>
    let (kept, driverDs) := LeanTex.Cli.ListingHighlight.settle answers refused
    let (warm, warmDs, _) := Elab.runPrepared "inline" { base with listingReplies := kept } (ld ++ pd)
    let (_, wbody, _) := HtmlDoc.emitTree {} warm
    t "inline code request: an answer for a name outside the registry paints and names nothing"
      (driverDs.isEmpty && !warmDs.any (·.code == "W0412") &&
        (inlineCodesList #[] false wbody.toList).any fun c => (strongTexts c).contains "def")
    let (left, refusalDs) := LeanTex.Cli.ListingHighlight.settle plain failed
    let (_, refusedDs, _) := Elab.runPrepared "inline" { base with listingReplies := left } (ld ++ pd)
    t "inline code request: a refusal outside the registry is the elaborator's one line"
      (left.isEmpty && refusalDs.isEmpty && (refusedDs.filter (·.code == "W0412")).size == 1 &&
        !refusedDs.any (·.code == "W0393"))
  | _, _ => failures ref "inline code request: the synthetic batches were rejected"
  let ruby := ListingReply.Request.ofSource "ruby" "puts 1"
  match ListingReply.decode #[ruby]
      (ShellHighlight.shellBatchJson #[ShellHighlight.shellFailureJson ruby "unsupported"])
      (terminalLf := true) with
  | .ok (plain, failed) =>
    let (left, ds) := LeanTex.Cli.ListingHighlight.settle plain failed
    t "inline code request: a registry language's refusal stays the driver's to name"
      (left.size == 1 && ds.all (·.code == "W0393") && ds.size == 1)
  | .error _ => failures ref "inline code request: the registry refusal was rejected"

end Tests
