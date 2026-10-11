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

/-- **An author colour binds no role but a code role's.** `\definecolor` and
`\colorlet` name xcolor colours, a namespace apart from the roles `\palette`
keys declare (`Palette.defineXcolor_design_id`; a code role's key declares
that role too, `xcolorCodeRoleChecks`): the minted manual's own
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

/-- Each glyph run the lines holding `word` set, as its text beside its ink. -/
private def runTexts (out : Layout.Out) (word : String) : Array (String × Ir.Color) :=
  ((allLines out).filter fun l => hasStr (lineText l) word).flatMap fun l =>
    l.segs.filterMap fun
      | .run _ ink _ _ glyphs .. =>
        if glyphs.isEmpty then none else some (String.ofList (glyphs.map (·.2.1)).toList, ink)
      | _ => none

/-- **An xcolor colour of a code role's key declares the role** (R149), the
one spelling both engines compile: a listing under
`\definecolor{codekeyword}` and `\colorlet{codeliteral}{blue}` sets its
keywords and literals in them, on the page and in the HTML alike, as the
`\palette` spelling of the two roles does, says nothing, and keeps both names
readable as colours; without them the same tokens take what the palette
derives. Read off `Layout.Out`, the typed HTML body and the stylesheet. -/
public def xcolorCodeRoleChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre : String) := elabStr (article ("\\usepackage{minted}\n" ++ pre)
    "\\begin{minted}{lean4}\ntheorem probe : 1 + 1 = 2 := by\n  sorry\n\\end{minted}")
  let (xd, xds) := doc "\\definecolor{codekeyword}{HTML}{A63D24}\n\\colorlet{codeliteral}{blue}\n"
  let (pd, _) := doc "\\palette{ codekeyword = #A63D24, codeliteral = #0000FF }\n"
  let (bare, _) := doc ""
  let red := Ir.Color.ofHtml 0xA6 0x3D 0x24
  let blue := Ir.Color.ofHtml 0 0 0xFF
  t "xcolor code roles: the two definitions declare the two roles"
    (Ir.Design.declared? xd.palette .codeKeyword == some red &&
      Ir.Design.declared? xd.palette .codeLiteral == some blue)
  t "xcolor code roles: both names stay colours an expression reads"
    (xd.palette.lookup (.color "codekeyword") == some red &&
      xd.palette.lookup (.color "codeliteral") == some blue)
  t "xcolor code roles: the definitions say nothing"
    (xds.all (·.severity == .note))
  let runs (d : Ir.Doc) := runTexts (layoutOf fonts d) "probe"
  let inksOf (d : Ir.Doc) (p : String → Bool) := ((runs d).filter (p ·.1)).map (·.2)
  let keyword (s : String) := hasStr s "theorem"
  let literal (s : String) := s.any Char.isDigit
  t "xcolor code roles: the page sets the keyword in the declared colour"
    (!(inksOf xd keyword).isEmpty && (inksOf xd keyword).all (· == red))
  t "xcolor code roles: the page sets the literals in the declared colour"
    (!(inksOf xd literal).isEmpty && (inksOf xd literal).all (· == blue))
  t "xcolor code roles: the page is the palette spelling's"
    (runs xd == runs pd)
  t "xcolor code roles: undeclared, the keyword takes another colour"
    (!(inksOf bare keyword).isEmpty && (inksOf bare keyword).all (· != red))
  let body (d : Ir.Doc) :=
    let (_, nodes, _) := HtmlDoc.emitTree {} d
    Html.render (Html.elem "body" nodes) 0
  t "xcolor code roles: the HTML body is the palette spelling's" (body xd == body pd)
  let css := (HtmlDoc.emit {} xd).1
  let vars := screenRootVars css
  t "xcolor code roles: the stylesheet's two roles are the declared colours"
    (chaseCssValue vars (HtmlDoc.roleRef .codeKeyword) == some (HtmlDoc.cssColor red) &&
      chaseCssValue vars (HtmlDoc.roleRef .codeLiteral) == some (HtmlDoc.cssColor blue))
  -- Declared in the body, inside a group: the role reaches a listing after
  -- the group ends, as the colour of that name does and as the role's
  -- `\palette` spelling does — a frame's end and an environment's alike.
  let listing := "\\begin{minted}{lean4}\ntheorem probe : 1 + 1 = 2 := by\n  sorry\n\\end{minted}"
  let groups : List (String × (String → String)) := [
    ("a frame", fun decl => dvDeck "\\usepackage{minted}\n"
      ("\\begin{frame}{One}" ++ decl ++ "Declared here.\\end{frame}\n" ++
       "\\begin{frame}[fragile]{Two}\n" ++ listing ++ "\n\\end{frame}")),
    ("an environment", fun decl => article "\\usepackage{minted}\n"
      ("\\begin{center}" ++ decl ++ "Declared here.\\end{center}\n\n" ++ listing))]
  for (what, src) in groups do
    let (gx, _) := elabStr (src "\\definecolor{codekeyword}{HTML}{A63D24}")
    let (gp, _) := elabStr (src "\\palette{ codekeyword = #A63D24 }")
    t s!"xcolor code roles: declared inside {what}, the keyword after it ships the declared colour"
      (!(inksOf gx keyword).isEmpty && (inksOf gx keyword).all (· == red))
    -- The page and the listing's HTML are the role's `\palette` spelling's;
    -- the colour of that name is declared beside the role, the one place the
    -- two spellings' HTML differs.
    let code (d : Ir.Doc) := ((body d).splitOn "<code").getD 1 "" |>.splitOn "</code>" |>.headD ""
    t s!"xcolor code roles: declared inside {what}, the page and the listing are the palette spelling's"
      (runs gx == runs gp && !(code gx).isEmpty && code gx == code gp)
    t s!"xcolor code roles: declared inside {what}, the HTML declares the colour beside the role"
      (hasStr (body gx) "--ltx-c-codekeyword: " && !hasStr (body gp) "--ltx-c-codekeyword: ")

/-- **An HTML colour's PDF decimals are lualatex's**: for every byte, the
DeviceRGB decimal the engine writes is the one lualatex's xcolor writes
(`testdata/oracles/xcolor-html-decimals.tsv`, from
`scripts/gen-xcolor-decimals.lean`), a whole one without its `.0`, for an
HTML colour and for an RGB colour a `\definecolor` stores, which xcolor
converts alike, and such a stored RGB colour shows the HTML byte xcolor
converts its stored decimals to; and a document's `\definecolor` of an HTML
colour ships that operator. -/
public def htmlDecimalChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let rows := (← IO.FS.readFile "testdata/oracles/xcolor-html-decimals.tsv").splitOn "\n" |>.filter
    fun l => !l.isEmpty && !l.startsWith "#" && !l.startsWith "byte"
  t s!"xcolor decimals: the table holds every byte ({rows.length})" (rows.length == 256)
  let mut wrong : Array String := #[]
  for row in rows do
    match row.splitOn "\t" with
    | [byte, dec] =>
      let v := (byte.toList.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48
        else c.toNat - 55)) 0)
      let html := (Ir.Color.ofHtml (UInt8.ofNat v) 0 0).pdfFill
      -- An RGB colour a `\\definecolor` stores goes through the same conversion.
      let defined := match Decl.parseColorSpec none (Decl.xcolorDefinitionPrefix ++ s!"RGB({v},0,0)") with
        | .ok spec => (({} : Ir.Palette).resolveSpec spec).map (·.pdfFill)
        | .error _ => none
      unless html == s!"{dec} 0 0 rg" && defined == some html do
        wrong := wrong.push s!"{byte}: {html} {defined}"
    | _ => wrong := wrong.push row
  t s!"xcolor decimals: every byte writes lualatex's decimal ({wrong.toList.take 4})" wrong.isEmpty
  -- An RGB colour a definition stores shows xcolor's own HTML conversion of
  -- the decimals it stores, as lualatex's `\\convertcolorspec{named}{x}{HTML}`
  -- reports them (measured: 133.5 stores 0.52353 and reports 85).
  for (v, byte) in [("0.5", 0x00), ("127.5", 0x80), ("133.5", 0x85), ("136.5", 0x88),
      ("139.5", 0x8B), ("146.5", 0x92), ("152.5", 0x98), ("178.5", 0xB2), ("229.5", 0xE5),
      ("254.5", 0xFF)] do
    let shown := match Decl.parseColorSpec none (Decl.xcolorDefinitionPrefix ++ s!"RGB({v},0,0)") with
      | .ok spec => (({} : Ir.Palette).resolveSpec spec).map (·.r)
      | .error _ => none
    t s!"xcolor decimals: a defined RGB {v} shows xcolor's own HTML byte ({shown})"
      (shown == some (UInt8.ofNat byte))
  let (doc, _) := elabStr (article "\\definecolor{probe}{HTML}{EB811B}\n" "\\textcolor{probe}{Probe words.}")
  let geom := Layout.Geom.ofPage doc.page
  let pdf := pdfText (Pdf.write geom fonts (layoutOf fonts doc geom).pages doc.info)
  t "xcolor decimals: a defined HTML colour ships lualatex's operator"
    (bytesContain pdf "0.92157 0.50587 0.10588 rg")

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
