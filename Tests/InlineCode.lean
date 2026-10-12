module

public import Tests.Support
public import Tests.ShellHighlight

public section

open LeanTex.Core

namespace Tests.InlineCode

/-- A face set whose run faces tell slot, weight and slant apart: the shipped
serif's four faces for the text slots (0 regular, 1 bold, 2 italic, 3 both),
and the shipped mono under four more indices for the typewriter slot (4 to 7
in the same order), so the face a run sets in says how it was asked for. -/
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

/-- The text an element's own text children hold: what it shows in the ink
and weight around it, no span of its own painting it. -/
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

/-- The size the first mono `probe` ships at. -/
def probeSize (gs : Array Glyph) : Option Dim.Sp :=
  ((word? gs "probe" mono).bind look).map (·.2.1)

def deckSrc (pre body : String) : String :=
  "\\documentclass{beamer}\n\\usepackage{minted}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
    "\n\\end{document}"

def mintedDoc (pre body : String) : String := dvDoc ("\\usepackage{minted}\n" ++ pre) body

end InlineCode

open InlineCode

/-- **Inline code is text** (`\mintinline` in both of minted's spellings,
and a listing written within a line of text or an argument): it takes the
size, weight, slant and colour of where it stands, and only its family
becomes mono; its highlighted tokens take their code roles' colours, and a
keyword's bold adds to the weight around it — as lualatex sets minted's
inline code, measured on a synthetic probe (minted 3.7, Pygments 2.21) with
`fontsize=\relax` for inline. Asserted over `Layout.Out` and the typed HTML
tree, in a paragraph, under `\textbf`, `\textit`, a colour and a size, in a
frame's footer, a frame's title and a block's title; with `\setminted` and
`\setmintedinline` layered as minted layers them; and around the display
listings, the one-line `\mint` and the listing written where LaTeX cannot
set it, named once. -/
def inlineCodeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← facesSet | failures ref "inline code: the shipped faces did not load"
  let shipped (src : String) := glyphs (layoutOf fonts (elabStr src).1)
  let html (src : String) : Array Html.Node × String :=
    let (head, body, _) := HtmlDoc.emitTree {} (elabStr src).1
    (body, treeCssList "" head.toList)
  let quiet (src : String) := (elabStr src).2.all fun d =>
    d.severity != .warning && d.severity != .error
  -- In a paragraph, beside the display listing of the same code.
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
  -- The style around it stands.
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
  -- Contexts: a frame's footer, its title and a block's title.
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
  -- minted's layers: `\setminted` reaches inline code, `\setmintedinline`
  -- after it, the command's own last; `\relax` keeps the size around it.
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
  -- A definition's parameters reach the code, the language and the
  -- options its minted command writes, bound before minted reads them.
  let wrapped := mintedDoc ("\\newcommand{\\py}[1]{\\mintinline{python}{#1}}\n" ++
      "\\newcommand{\\code}[2]{\\mintinline{#1}{#2}}\n")
    "Alpha \\py{def probe(arg)} beta \\code{python}{return arg} omega."
  let direct := mintedDoc ""
    "Alpha \\mintinline{python}{def probe(arg)} beta \\mintinline{python}{return arg} omega."
  t "inline code: a definition's parameter is its argument's code, as LaTeX binds it"
    (quiet wrapped && shipped wrapped == shipped direct)
  t "inline code: a parameter outside any definition is the code it spells"
    ((word? (shipped (mintedDoc "" "Alpha \\mintinline{python}{#1} omega.")) "#1" mono).isSome)
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
  -- A display listing where inline content stands is named once and set as
  -- inline code.
  let named (src : String) := (elabStr src).2.filter (·.code == "W0411")
  for (label, src) in [
      ("\\mint in an argument", "\\textbf{Alpha \\mint{python}{def probe(arg)} omega}"),
      ("an environment in an argument",
        "\\textbf{Alpha \\begin{minted}{python}\ndef probe(arg)\n\\end{minted} omega}"),
      ("an environment on a line of text",
        "Alpha \\begin{minted}{python}def probe(arg)\\end{minted} omega.")] do
    let src := mintedDoc "" src
    let gs := shipped src
    let ws := named src
    t s!"inline code {label}: named once, by its own code"
      (ws.size == 1 && ws.all (·.severity == .warning) &&
        !((elabStr src).2.any (·.code == "W0346")))
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
  let alone := mintedDoc "" "Alpha.\n\n\\begin{minted}{python}def probe(arg)\\end{minted}\n\nOmega."
  t "a one-line listing alone in its paragraph is named and set as a display"
    ((named alone).size == 1 && (named alone).all (fun d => d.help.any (hasStr · "lines of its own")) &&
      !(elemNodesList (· == "pre") #[] (html alone).1.toList).isEmpty)
  -- A lexer name no lexer reads is named with the nearest known one.
  let unknown (src : String) := (elabStr src).2.filter (·.code == "W0412")
  let typo := mintedDoc "" "Alpha \\mintinline{pyhton}{def probe} omega."
  t "inline code: a misspelt lexer is named with the nearest lexer as its help"
    ((unknown typo).size == 1 && (unknown typo).all fun d => d.help.any (hasStr · "'python'"))
  t "inline code: a misspelt lexer's code ships plain"
    ((word? (shipped typo) "def" mono).any fun r => r.all (!bold ·))
  let envTypo := (elabStr (mintedDoc "" "\\begin{minted}{pyhton}\ndef probe\n\\end{minted}")).1
  t "a listing whose lexer no lexer reads asks the highlighter nothing"
    (!(unknown (mintedDoc "" "\\begin{minted}{pyhton}\ndef probe\n\\end{minted}")).isEmpty &&
      (ListingReply.requests envTypo).isEmpty)
  t "a lexer only the highlighter reads is no unknown lexer"
    ((unknown (mintedDoc "" "\\begin{minted}{ruby}\nputs 1\n\\end{minted}")).isEmpty &&
      (unknown (mintedDoc "" "Alpha \\mintinline{ruby}{puts 1} omega.")).isEmpty)
  let far := unknown (mintedDoc "" "Alpha \\mintinline{zzqqxxww}{x} omega.")
  t "a lexer name near no known one is named with the registry's own spellings"
    (far.size == 1 && far.all fun d => d.help.any (hasStr · "'python'"))
  -- Display listings keep their declared size, relative to the body, and
  -- `\relax` asks for the size around them as `auto` does.
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

end Tests
