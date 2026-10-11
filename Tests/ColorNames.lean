module

public import Tests.Support
public import Tests.Artifact

public section

open LeanTex.Core

namespace Tests.ColorNames

private def article (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- A fill covering the whole page: what a declared page ground paints. -/
private def pageFills (doc : Ir.Doc) (out : Layout.Out) : Array Ir.Color :=
  let geom := Layout.Geom.ofPage doc.page
  out.pages.flatMap fun page => (page.fills.filter fun f =>
    f.x ≤ 0 && f.y ≤ 0 && f.w ≥ geom.pageW && f.h ≥ geom.pageH).map (·.color)

private def runInks (out : Layout.Out) (text : String) : Array Ir.Color :=
  (allLines out).filter (lineText · == text) |>.flatMap fun l =>
    l.segs.filterMap fun
      | .run _ ink _ _ glyphs .. => if glyphs.isEmpty then none else some ink
      | _ => none

/-- **An author colour never binds a role.** `\definecolor` and `\colorlet`
name xcolor colours, a namespace apart from the roles `\palette` keys
declare (`Palette.defineColor_design_id`): the minted manual's own
`\definecolor{bg}` paints no page, a colour named `fg` sets no text, a
`\colorlet{alert}` leaves the alert role as declared and `\alert` reads that
role (beamer's `alerted text`), while an expression (`\textcolor{bg}`,
`\textcolor{alert}`) still reads the author's colour first, as xcolor does.
minted's own
`bgcolor=bg` sets the listing — and only the listing — on that colour. Read
off the shipped pages and the emitted stylesheet. -/
public def checks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (article "\\definecolor{bg}{rgb}{.9,.9,.9}\n" "Probe text.")
  let out := layoutOf fonts doc
  t "author colours: \\definecolor{bg} elaborates clean"
    (!ds.any (·.severity == .error))
  t "author colours: \\definecolor{bg} paints no page"
    (pageFills doc out).isEmpty
  t "author colours: \\definecolor{bg} declares no page role"
    (Ir.Design.declared? doc.palette .page).isNone
  let css := (HtmlDoc.emit {} doc).1
  let authorBg := ((doc.palette.lookup (.color "bg")).map HtmlDoc.cssColor).getD "none"
  t "author colours: the HTML body takes no ground from \\definecolor{bg}"
    (hasStr css s!"--ltx-c-bg: {authorBg};" && !hasStr css s!"--ltx-bg: {authorBg};" &&
      hasStr css "background: var(--ltx-bg);" && !hasStr css "background: var(--ltx-c-bg)")
  t "author colours: the reader name --bg stays the author's colour"
    (hasStr css "--bg: var(--ltx-c-bg);" && !hasStr css "--bg: var(--ltx-bg);")
  let (fgDoc, _) := elabStr (article "\\definecolor{fg}{HTML}{1A2B3C}\n" "Probe ink.")
  let fgOut := layoutOf fonts fgDoc
  t "author colours: \\definecolor{fg} sets no text"
    (!(runInks fgOut "Probe ink.").isEmpty &&
      (runInks fgOut "Probe ink.").all (· == Ir.Color.black))
  let (exprDoc, _) := elabStr (article "\\definecolor{bg}{HTML}{224466}\n"
    "\\textcolor{bg}{Probe named.}")
  let exprOut := layoutOf fonts exprDoc
  t "author colours: an expression reads the author's colour"
    ((runInks exprOut "Probe named.").all (· == { r := 0x22, g := 0x44, b := 0x66 }) &&
      !(runInks exprOut "Probe named.").isEmpty)
  t "author colours: an expression's run names the author colour"
    (hasStr (Ir.dump exprDoc #[]) "color bg #224466") -- ir tier: the run's name is IR data
  let (alertDoc, _) := elabStr (dvDeck
    "\\theme{plain}\n\\palette{alert=#8A1C1C}\n\\colorlet{alert}{blue}\n"
    "\\begin{frame}\nAlerted \\alert{one} and named \\textcolor{alert}{two}.\n\\end{frame}")
  let alertOut := layoutOf fonts alertDoc
  let line := "Alerted one and named two."
  t "author colours: \\colorlet{alert} leaves the alert role"
    (Ir.Design.declared? alertDoc.palette .alert == some { r := 0x8A, g := 0x1C, b := 0x1C })
  t "author colours: \\textcolor{alert} reads the author colour"
    ((runInks alertOut line).contains { r := 0, g := 0, b := 255 })
  t "author colours: \\alert reads the alert role, whatever a colour named alert holds"
    ((runInks alertOut line).contains { r := 0x8A, g := 0x1C, b := 0x1C })
  let (overlayDoc, _) := elabStr (dvDeck
    "\\theme{plain}\n\\palette{alert=#8A1C1C}\n\\colorlet{alert}{blue}\n"
    "\\begin{frame}\nStepped \\alert<1>{one}.\n\\end{frame}")
  t "author colours: an overlay \\alert reads the alert role too"
    ((runInks (layoutOf fonts overlayDoc) "Stepped one.").contains { r := 0x8A, g := 0x1C, b := 0x1C })
  -- minted's manual example: a listing set on `\definecolor{bg}`.
  let (mDoc, mDs) := elabStr (article "\\usepackage{minted}\n\\definecolor{bg}{rgb}{.9,.9,.9}\n"
    "Before.\n\n\\begin{minted}[bgcolor=bg]{python}\ndef f(x):\n    return x\n\\end{minted}\n\nAfter.")
  let mOut := layoutOf fonts mDoc
  let grey := (mDoc.palette.lookup (.color "bg")).getD Ir.Color.white
  let greyFills := mOut.pages.flatMap fun p => p.fills.filter (·.color == grey)
  let baseline (text : String) : Option Int :=
    ((allLines mOut).find? (lineText · == text)).map (·.y)
  t "minted bgcolor: the listing stands on its colour and the page on none"
    ((pageFills mDoc mOut).isEmpty && greyFills.size == 1 && !mDs.any (·.code == "W0110"))
  t "minted bgcolor: the colour box holds the code lines and none of the prose"
    (greyFills.all fun f =>
      (baseline "Before.").all (· < f.y) && (baseline "After.").all (· > f.y + f.h) &&
      (baseline "def f(x):").all fun y => f.y < y && y < f.y + f.h)
  let mCss := (HtmlDoc.emit {} mDoc).1
  t "minted bgcolor: the HTML panel takes the colour, the body the page role"
    (hasStr mCss "background: var(--ltx-c-bg, " && hasStr mCss "background: var(--ltx-bg);" &&
      hasStr mCss s!"--ltx-c-bg: {HtmlDoc.cssColor grey};")
  let (pageDoc, _) := elabStr (article "\\definecolor{paper}{HTML}{F4F0E6}\n\\pagecolor{paper}\n"
    "Probe page.")
  t "author colours: \\pagecolor names the page role explicitly"
    (pageFills pageDoc (layoutOf fonts pageDoc) == #[{ r := 0xF4, g := 0xF0, b := 0xE6 }])
  -- The stylesheet's rules once read the page as `--surface`, the text as
  -- `--ink`, the code ground as `--tint` and the focus ring as `--accent`,
  -- the names an author colour was declared under too: a colour so named
  -- repainted them in the HTML alone. Each rule's value, chased through the
  -- page's own table, is the registry's colour.
  let (hjDoc, _) := elabStr (article ("\\definecolor{surface}{HTML}{112233}" ++
    "\\definecolor{tint}{HTML}{445566}\\definecolor{accent}{HTML}{778899}" ++
    "\\definecolor{ink}{HTML}{AA0000}\n") "Probe words.")
  let hjCss := (HtmlDoc.emit {} hjDoc).1
  let vars := screenRootVars hjCss
  let ruleColor (sel prop : String) : Option String :=
    ((cssRulesOf hjCss sel).reverse.findSome? (cssDeclOf · prop)).bind fun v =>
      ((v.splitOn " ").getLast?).bind (chaseCssValue vars)
  for (sel, prop, role, what) in [("body", "background", Ir.Role.page, "page"),
      ("body", "color", .ink, "text"), ("pre", "background", .codeSurface, "code ground"),
      ("a:focus-visible", "outline", .focus, "focus ring")] do
    t s!"author colours: an author colour leaves the HTML {what} the registry's"
      (ruleColor sel prop == some (HtmlDoc.cssColor (screenColor .light role)))

/-- **A `\palette` name nothing reads is named where it stands**: `ink` and
`surface` declare author colours, never the page's text and ground, so one
the document names nowhere else is one W0387 at its declaration naming the
key that sets what the document likely meant (`fg`, `bg`); named where it is
used, or declared by `\definecolor`, it is an author colour like any other
and says nothing. -/
public def unreadKeyChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let named (ds : Array Diag) (key : String) : Array Diag :=
    ds.filter fun d => d.code == "W0387" && d.subject == some s!"palette:{key}"
  let (_, unread) := elabStr (article "\\palette{ ink = #333333, surface = #F4F4F4 }\n" "Probe.")
  t "palette keys: an unread ink is named once, pointing at fg"
    ((named unread "ink").size == 1 &&
      (named unread "ink").all fun d => hasStr d.message "'fg'" && d.span.isSome)
  t "palette keys: an unread surface is named once, pointing at bg"
    ((named unread "surface").size == 1 &&
      (named unread "surface").all fun d => hasStr d.message "'bg'")
  let (_, read) := elabStr (article "\\palette{ ink = #333333 }\n" "\\textcolor{ink}{Probe}.")
  t "palette keys: an ink the document names says nothing" (named read "ink").isEmpty
  let (_, xcolor) := elabStr (article "\\definecolor{ink}{HTML}{333333}\n" "Probe.")
  t "palette keys: an xcolor definition is an author colour, never named" (named xcolor "ink").isEmpty
  let (_, roles) := elabStr (article "\\palette{ fg = #333333, bg = #FFFFFF }\n" "Probe.")
  t "palette keys: the role keys say nothing"
    (roles.all fun d => d.code != "W0387")
  -- A read is the engine's: a colour expression, a palette value, a command
  -- named for the colour, a beamer declaration, a picture's colour. The
  -- word in prose or a comment reads nothing.
  let declared := "\\palette{ ink = #333333, surface = #F4F4F4 }\n"
  let (_, prose) := elabStr (article declared
    "Water beads on the surface of the leaf, dark as ink.")
  t "palette keys: the word in prose reads neither key"
    ((named prose "ink").size == 1 && (named prose "surface").size == 1)
  let (_, comment) := elabStr (article declared "% ink and surface\nProbe.")
  t "palette keys: the word in a comment reads neither key"
    ((named comment "ink").size == 1 && (named comment "surface").size == 1)
  let reads : List (String × String × String) := [
    ("a mix", "", "\\textcolor{ink!50!white}{Probe} \\textcolor{surface!80!black}{probe}."),
    ("a palette value", "\\palette{ fg = ink, bg = surface }\n", "Probe."),
    ("a command named for the colour", "", "\\ink{Probe} \\surface{probe}."),
    ("a declaration", "", "{\\color{ink} Probe} {\\color{surface!80!black} probe}."),
    ("a picture", "\\usepackage{tikz}\n",
      "\\begin{tikzpicture}\\draw[ink] (0,0) -- (1,1);\
\\fill[surface] (0,0) rectangle (1,1);\\end{tikzpicture}")]
  for (what, pre, body) in reads do
    let (_, ds) := elabStr (article (declared ++ pre) body)
    t s!"palette keys: {what} reads both keys"
      ((named ds "ink").isEmpty && (named ds "surface").isEmpty)
  let (_, beamer) := elabStr ("\\documentclass{beamer}\n" ++ declared ++
    "\\setbeamercolor{frametitle}{fg=ink, bg=surface}\n\\begin{document}\n\
\\begin{frame}{Probe}Probe.\\end{frame}\n\\end{document}")
  t "palette keys: a beamer colour declaration reads both keys"
    ((named beamer "ink").isEmpty && (named beamer "surface").isEmpty)

/-- The artifact two builds are compared by: the PDF's bytes, and the HTML
body with the stylesheet's rules — every author colour the page declares for
a host to read left out, since a host's override is not the document's
read. -/
private def flipArtifact (fonts : Font.FontSet) (doc : Ir.Doc) : ByteArray × String × String :=
  let geom := Layout.Geom.ofPage doc.page
  let pdf := driverPdf fonts geom doc (layoutOf fonts doc)
  let (head, body, _) := HtmlDoc.emitTree {} doc
  let rules := (Html.render (Html.elem "head" head) 0).splitOn "\n" |>.filter fun l =>
    let d := l.trimAscii.toString
    !(d.startsWith "--ltx-c-" || d.startsWith "--ink:" || d.startsWith "--surface:")
  (pdf, Html.render (Html.elem "body" body) 0, "\n".intercalate rules)

/-- **W0387 is the two-build oracle** (`unreadPaletteKeys`' premise): a
document declaring `ink` and `surface` is built again with one key's value
changed, and the shipped artifact is unchanged exactly when that key draws
W0387. Each probe states which way it goes: a colour expression, a mix, a
command named for the colour as an argument or as a declaration, a cancel
mark, a rule the page draws, a picture's paint, a beamer element and a
listing ground read the key; prose, a comment, and a colour construct the
engine paints nothing for do not. -/
public def unreadKeyFlipChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let probes : List (String × String × String × String × Bool) := [
    ("prose", "ink", "", "Water beads on the leaf, dark as ink and surface.", false),
    ("a comment", "surface", "", "% surface\nProbe.", false),
    ("an expression", "ink", "", "\\textcolor{ink}{Probe}.", true),
    ("a mix", "surface", "", "\\textcolor{surface!60!black}{Probe}.", true),
    ("a command with its argument", "ink", "", "\\ink{Probe}.", true),
    ("a bare command between paragraphs", "ink", "", "First.\n\n\\ink\n\nSecond.", true),
    ("a declaration", "surface", "", "{\\color{surface!70!black} Probe}.", true),
    ("a cancel mark", "ink", "\\usepackage{cancel}\n\\renewcommand{\\CancelColor}{\\color{ink}}\n",
      "Struck: $\\cancel{x}$.", true),
    ("a rule the page draws", "surface", "\\page{ rule = \"1cm; 1cm; 3cm; 3cm; surface\" }\n",
      "Probe.", true),
    ("a picture's paint", "ink", "\\usepackage{tikz}\n",
      "\\begin{tikzpicture}\\fill[ink] (0,0) rectangle (1,1);\\end{tikzpicture}", true),
    ("a listing ground", "surface", "\\usepackage{minted}\n",
      "\\begin{minted}[bgcolor=surface]{python}\nx = 1\n\\end{minted}", true),
    ("an unpainted box", "surface", "", "\\colorbox{surface}{Probe}.", false)]
  for (what, key, pre, body, read) in probes do
    let build (v : String) := Id.run do
      let (doc, ds) := elabStr (article (s!"\\palette\{ {key} = {v} }\n" ++ pre) body)
      return (flipArtifact fonts doc, ds)
    let (a, ds) := build "#2A6F3A"
    let (b, _) := build "#C0157D"
    let changed := a.1 != b.1 || a.2.1 != b.2.1 || a.2.2 != b.2.2
    let warned := ds.any fun d => d.code == "W0387" && d.subject == some s!"palette:{key}"
    t s!"palette keys, two builds: {what} {if read then "reads" else "leaves unread"} '{key}'"
      (changed == read)
    t s!"palette keys, two builds: {what}: W0387 exactly when the artifact ignores '{key}'"
      (warned == !changed)
  -- A beamer element's declaration reads the key where the element paints.
  let deck (v : String) := Id.run do
    let (doc, ds) := elabStr ("\\documentclass{beamer}\n\\palette{ ink = " ++ v ++ " }\n" ++
      "\\setbeamercolor{frametitle}{fg=ink, bg=white}\n\\begin{document}\n" ++
      "\\begin{frame}{Probe}Probe.\\end{frame}\n\\end{document}")
    return (flipArtifact fonts doc, ds)
  let (a, ds) := deck "#2A6F3A"
  let (b, _) := deck "#C0157D"
  t "palette keys, two builds: a beamer frame title reads 'ink'"
    ((a.1 != b.1) && !(ds.any fun d => d.code == "W0387" && d.subject == some "palette:ink"))

end Tests.ColorNames
