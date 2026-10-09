module

public import Tests.Support

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

private def colorDeck (pre body : String) : String :=
  "\\documentclass{beamer}\\usetheme{moloch}" ++
    "\\definecolor{ProbeInk}{HTML}{173B58}" ++
    "\\definecolor{ProbeOther}{HTML}{582347}" ++
    "\\definecolor{ProbeThird}{HTML}{205536}" ++
    "\\definecolor{ProbePaper}{HTML}{E8EDF3}" ++ pre ++
    "\\begin{document}" ++ body ++ "\\end{document}"

private def colorFrames : String :=
  "\\begin{frame}{First}alpha\\end{frame}" ++
    "\\section{Middle}\\begin{frame}{Last}omega\\end{frame}"

private def lineHasColor (out : Layout.Out) (text : String) (c : Ir.Color) : Bool :=
  (allLines out).any fun l => (lineText l).trimAscii.toString == text &&
    l.segs.any fun s => match s with
      | .run _ ink _ _ _ _ _ _ _ _ _ => ink == c
      | _ => false

private def colorLoss (ds : Array Diag) (fragment : String) : Bool :=
  ds.any fun d => d.code == "W0104" && (d.message.splitOn fragment).length > 1

private def colorTree (doc : Ir.Doc) : Html.Node :=
  let (head, body, _) := HtmlDoc.emitTree {} doc
  .elem "html" #[] (head ++ body)

/-- Immediate and deferred colour warnings keep the declaring command's
file and position, even when resolution happens after returning from an
included theme. A lookup failure is attributed to its declaration too. -/
def beamerColorOriginChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let parse (file text : String) := (Parse.parse file (Lex.lex file text).1).1
  let child := "theme.sty"
  for (name, source, lines) in [
      ("unpainted channel", "\n\\setbeamercolor{framesubtitle}{bg=red}", [2]),
      ("unsupported key", "\n\\setbeamercolor{frametitle}{probe=red}", [2]),
      ("unused element", "\n\\setbeamercolor{unpainted}{fg=red}", [2]),
      ("unresolved value", "\n\\setbeamercolor{frametitle}{fg=MissingInk}", [2]),
      ("earlier unresolved channel", "\n\\setbeamercolor{frametitle}{fg=MissingInk}\n" ++
        "\\setbeamercolor{frametitle}{bg=red}", [2]),
      ("cycle", "\n\\setbeamercolor{frametitle}{parent=source}\n" ++
        "\\setbeamercolor{source}{parent=frametitle}", [2, 3]),
      ("earlier cyclic parent", "\n\\setbeamercolor{frametitle}{parent=source}\n" ++
        "\\setbeamercolor{source}{parent=frametitle}\n" ++
        "\\setbeamercolor{frametitle}{fg=red}\n\\setbeamercolor{source}{fg=red}", [2, 3]),
      ("implicit subtitle parent cycle", "\n\\setbeamercolor{frametitle}{parent=framesubtitle}", [2]),
      ("implicit cycle with an unrelated channel", "\n\\setbeamercolor{frametitle}{parent=framesubtitle}\n" ++
        "\\setbeamercolor{framesubtitle}{fg=red}", [2]),
      ("implicit cycle through a use edge", "\n\\setbeamercolor{frametitle}{use=framesubtitle}", [2]),
      -- beamer's default theme hangs `section title` on `titlelike` and
      -- `titlelike` on `structure` (beamercolorthemedefault.sty).
      ("implicit section chain cycle", "\n\\setbeamercolor{structure}{parent=section title}", [2])] do
    let raws := parse "root.tex" "\\documentclass{beamer}\n" ++
      #[Parse.Raw.env (Parse.inputEnv child) (parse child source) {}] ++
      parse "root.tex" "\\begin{document}\\begin{frame}{Heading}Body\\end{frame}\\end{document}"
    let ds := (Elab.runRawsSpanned "root.tex" raws).2.1.filter (·.kind == .W0104)
    t s!"beamer color origin: {name} is still diagnosed" (!ds.isEmpty)
    t s!"beamer color origin: {name} names its command"
      (ds.all (·.trigger == some "\\setbeamercolor"))
    t s!"beamer color origin: {name} names its included declaration"
      (ds.all fun d => d.span.any fun span =>
        span.file == child && lines.contains span.pos.line && span.pos.col == 1)

/-- Source-based paint invariants for Beamer colour inheritance and the
bounded native furniture sites. The synthetic LuaLaTeX oracle uses
beamerbasecolor.sty's parent order, independent channels, late lookup,
`use` aliases, and starred reset. No private document supplies these
fixtures. Both the supported effect and the unsupported no-effect are
judged on shipped layout or the typed HTML tree. -/
def beamerColorsChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  beamerColorOriginChecks ref
  let t := check ref
  let ink : Ir.Color := { r := 0x17, g := 0x3B, b := 0x58 }
  let other : Ir.Color := { r := 0x58, g := 0x23, b := 0x47 }
  let third : Ir.Color := { r := 0x20, g := 0x55, b := 0x36 }
  let paper : Ir.Color := { r := 0xE8, g := 0xED, b := 0xF3 }
  let frame := "\\begin{frame}{Heading}Body\\end{frame}"
  let build (pre : String) (body : String := frame) :=
    let (doc, ds) := elabStr (colorDeck pre body)
    (layoutOf fonts doc, colorTree doc, ds)
  let parent := "\\setbeamercolor{probe base}{fg=ProbeInk,bg=ProbePaper}" ++
    "\\setbeamercolor*{frametitle}{parent=probe base}"
  let (inherited, inheritedHtml, inheritedDs) := build parent
  t "beamer colors: parent foreground paints the frame heading"
    (lineHasColor inherited "Heading" ink)
  t "beamer colors: parent background paints the header"
    (inherited.pages.any fun p => p.fills.any fun f =>
      f.y == 0 && f.h < (Layout.Geom.ofPage (elabStr (colorDeck "" frame)).1.page).pageH / 3 &&
        f.color == paper)
  t "beamer colors: consumed named parents need no loss warning"
    (!colorLoss inheritedDs "probe base" && !colorLoss inheritedDs "parent")
  t "beamer colors: inherited colors reach a header CSS use"
    ((treeCssOne "" inheritedHtml).contains "var(--frametitlefg" &&
      (treeCssOne "" inheritedHtml).contains "--frametitlefg: #173b58")
  let (late, _, _) := build (parent ++
    "\\setbeamercolor{probe base}{fg=ProbeOther}")
  t "beamer colors: a later parent declaration changes later paint"
    (lineHasColor late "Heading" other && !lineHasColor late "Heading" ink)
  let (forward, _, forwardDs) := build
    ("\\setbeamercolor*{frametitle}{parent=probe future}" ++
      "\\setbeamercolor{probe future}{fg=ProbeInk,bg=ProbePaper}")
  t "beamer colors: a forward parent is resolved before paint"
    (lineHasColor forward "Heading" ink && !colorLoss forwardDs "probe future")
  let (ordered, _, _) := build
    ("\\setbeamercolor{probe first}{fg=ProbeInk,bg=ProbePaper}" ++
      "\\setbeamercolor{probe last}{fg=ProbeOther}" ++
      "\\setbeamercolor*{frametitle}{parent={probe first,probe last}}")
  t "beamer colors: later parents win per channel"
    (lineHasColor ordered "Heading" other &&
      ordered.pages.any fun p => p.fills.any (·.color == paper))
  let (own, _, _) := build (parent ++
    "\\setbeamercolor{frametitle}{fg=ProbeThird}" ++
    "\\setbeamercolor{probe base}{fg=ProbeOther}")
  t "beamer colors: a child's own foreground wins over its parent"
    (lineHasColor own "Heading" third)
  let (used, _, usedDs) := build
    ("\\setbeamercolor{probe source}{fg=ProbeInk,bg=ProbePaper}" ++
      "\\setbeamercolor*{frametitle}{use=probe source,fg=probe source.fg,bg=probe source.bg}" ++
      "\\setbeamercolor{probe source}{fg=ProbeOther}")
  t "beamer colors: use refreshes named channel aliases"
    (lineHasColor used "Heading" other && !colorLoss usedDs "use")
  let (reset, _, _) := build (parent ++
    "\\setbeamercolor*{frametitle}{fg=ProbeThird}")
  t "beamer colors: a starred declaration clears the inherited background"
    (lineHasColor reset "Heading" third &&
      !(reset.pages.any fun p => p.fills.any (·.color == paper)))
  -- LuaLaTeX/beamerbasecolor.sty: an empty assignment clears an inherited
  -- channel; an absent assignment leaves it alone. At the frame heading,
  -- the cleared foreground uses normal text, while an empty background
  -- leaves the header unfilled. `use` binds aliases before the parents run.
  let normal : Ir.Color := { r := 0x23, g := 0x37, b := 0x3B }
  let firstParent := "\\setbeamercolor{probe first}{fg=ProbeInk,bg=ProbePaper}"
  let clearOwn := parent ++ "\\setbeamercolor{frametitle}{fg={}}"
  let useParent :=
    "\\setbeamercolor{probe source}{fg=ProbeInk,bg=ProbePaper}" ++
      "\\setbeamercolor{probe parent}{fg=probe source.fg,bg=probe source.bg}" ++
      "\\setbeamercolor*{frametitle}{use=probe source,parent=probe parent}"
  for (name, pre, expected) in [
      ("child clear", clearOwn, normal),
      ("later parent clear", firstParent ++
        "\\setbeamercolor{probe last}{fg={}}" ++
        "\\setbeamercolor*{frametitle}{parent={probe first,probe last}}", normal),
      ("star background only", parent ++
        "\\setbeamercolor*{frametitle}{bg=ProbePaper}", normal),
      ("use missing foreground",
        "\\setbeamercolor{probe source}{bg=ProbePaper}" ++
        "\\setbeamercolor*{frametitle}{use=probe source,fg=probe source.fg,bg=probe source.bg}",
        normal),
      ("use empty foreground",
        "\\setbeamercolor{probe source}{fg={},bg=ProbePaper}" ++
        "\\setbeamercolor*{frametitle}{use=probe source,fg=probe source.fg,bg=probe source.bg}",
        normal),
      ("use before parent", useParent, ink),
      ("normal text fallback", clearOwn ++
        "\\setbeamercolor{normal text}{fg=ProbeOther}", other)] do
    let (out, html, ds) := build pre
    t s!"beamer colors: {name} paints the resolved foreground"
      (lineHasColor out "Heading" expected)
    let hex := Ir.Color.hexByte expected.r ++ Ir.Color.hexByte expected.g ++
      Ir.Color.hexByte expected.b
    t s!"beamer colors: {name} reaches the HTML header color use"
      ((treeCssOne "" html).contains ("--frametitlefg: #" ++ hex.toLower) &&
        (treeCssOne "" html).contains "var(--frametitlefg")
    t s!"beamer colors: {name} preserves the independent background without loss"
      (out.pages.any (fun p => p.fills.any (·.color == paper)) &&
        !colorLoss ds "cannot be resolved" && !colorLoss ds "unused")
  let (absent, _, _) := build (firstParent ++
    "\\setbeamercolor*{probe last}{bg=ProbePaper}" ++
    "\\setbeamercolor*{frametitle}{parent={probe first,probe last}}")
  t "beamer colors: a missing later parent channel does not clear earlier ink"
    (lineHasColor absent "Heading" ink)
  for (name, pre) in [
      ("child background clear", parent ++ "\\setbeamercolor{frametitle}{bg={}}"),
      ("later parent background clear", firstParent ++
        "\\setbeamercolor{probe last}{bg={}}" ++
        "\\setbeamercolor*{frametitle}{parent={probe first,probe last}}")] do
    let (out, _, ds) := build pre
    t s!"beamer colors: {name} leaves the header unfilled and preserves ink"
      (lineHasColor out "Heading" ink &&
        !(out.pages.any fun p => p.fills.any (·.color == paper)) &&
        !colorLoss ds "cannot be resolved")
  let (usedEpoch, _, usedEpochDs) := build useParent
    ("\\begin{frame}{Earlier}alpha\\end{frame}" ++
      "\\setbeamercolor{probe source}{fg=ProbeOther}" ++
      "\\begin{frame}{Later}omega\\end{frame}")
  t "beamer colors: a parent's use aliases follow the frame palette epoch"
    (lineHasColor usedEpoch "Earlier" ink && lineHasColor usedEpoch "Later" other &&
      !lineHasColor usedEpoch "Earlier" other &&
      !colorLoss usedEpochDs "cannot be resolved")
  let (sub, subHtml, subDs) := build
    ("\\setbeamercolor{frametitle}{fg=ProbeInk,bg=ProbePaper}" ++
      "\\setbeamercolor{framesubtitle}{fg=ProbeOther}")
    "\\begin{frame}{Heading}\\framesubtitle{Subheading}Body\\end{frame}"
  t "beamer colors: subtitle foreground paints the subtitle"
    (lineHasColor sub "Subheading" other)
  let sy := (allLines sub).find? fun l => lineText l == "Subheading"
  let hy := (allLines sub).find? fun l => lineText l == "Heading"
  let bodyLine := (allLines sub).find? fun l => lineText l == "Body"
  t "beamer colors: subtitle is a separate line between heading and body"
    (match hy, sy, bodyLine with
      | some h, some s, some b => h.y < s.y && s.y < b.y
      | _, _, _ => false)
  t "beamer colors: typed HTML carries the subtitle color use"
    ((elemStylesOne #[] subHtml).any fun (text, style) =>
      text == "Subheading" && style.contains "var(--framesubtitlefg")
  t "beamer colors: supported subtitle foreground has no loss"
    (!colorLoss subDs "framesubtitle")
  let sectionColors := "\\setbeamercolor{section title}{fg=ProbeOther}" ++
    "\\setbeamercolor{progress bar}{fg=ProbeInk,bg=ProbePaper}" ++
    "\\setbeamercolor{progress bar in section page}{fg=ProbeThird}"
  let (sec, secHtml, secDs) := build sectionColors colorFrames
  t "beamer colors: section title paints with its own foreground"
    (lineHasColor sec "Middle" other)
  t "beamer colors: section progress paints with its independent foreground"
    (sec.pages.any fun p => p.lines.any (fun l => lineText l == "Middle") &&
      p.fills.any (·.color == third) && p.fills.any (·.color == paper))
  t "beamer colors: typed HTML reads section-specific roles"
    ((treeCssOne "" secHtml).contains "var(--sectiontitlefg" &&
      (treeCssOne "" secHtml).contains "var(--sectionprogressfg")
  t "beamer colors: supported section roles have no loss"
    (!colorLoss secDs "section title" && !colorLoss secDs "section page")
  let (foot, footHtml, footDs) := build
    "\\setbeamercolor{footline}{fg=ProbeInk,bg=ProbePaper}"
  t "beamer colors: footer background paints only the footer band"
    (foot.pages.any fun p => p.fills.any fun f =>
      f.color == paper && f.y > (Layout.Geom.ofPage (elabStr (colorDeck "" frame)).1.page).pageH / 2)
  t "beamer colors: typed HTML reads the footer background"
    ((treeCssOne "" footHtml).contains "background: var(--footlinebg")
  t "beamer colors: supported footer background has no loss"
    (!colorLoss footDs "footline")
  let (unsupported, _, unsupportedDs) := build (sectionColors ++
    "\\setbeamercolor{progress bar in head/foot}{fg=ProbeOther,bg=ProbeThird}") colorFrames
  t "beamer colors: unsupported head/foot progress remains named"
    (colorLoss unsupportedDs "progress bar in head/foot")
  t "beamer colors: head/foot progress cannot recolor the section bar"
    (reprStr (unsupported.pages.map (·.fills)) == reprStr (sec.pages.map (·.fills)))
  for (element, fragment) in [("framesubtitle", "bg"), ("section title", "bg"),
      ("sidebar", "sidebar")] do
    let (_, _, ds) := build s!"\\setbeamercolor\{{element}}\{bg=ProbePaper}"
    t s!"beamer colors: unsupported {element} background remains named" (colorLoss ds fragment)
  let (plain, _, _) := build ""
  for name in ["probe venue", "probe title", "probe author"] do
    let (unused, _, ds) := build s!"\\setbeamercolor\{{name}}\{fg=ProbeOther,bg=ProbePaper}"
    t s!"beamer colors: unused custom element {name} stays diagnosed without painting"
      (colorLoss ds name && reprStr unused.pages == reprStr plain.pages)
  let (useOnly, _, _) := build
    ("\\setbeamercolor{probe source}{fg=ProbeOther,bg=ProbePaper}" ++
      "\\setbeamercolor{frametitle}{use=probe source}")
  t "beamer colors: use alone does not inherit either channel"
    (reprStr useOnly.pages == reprStr plain.pages)
  let (mixed, _, mixedDs) := build
    ("\\setbeamercolor{probe source}{fg=ProbeInk}" ++
      "\\setbeamercolor{frametitle}{use=probe source,fg=probe source.fg!70!ProbeOther,bg=ProbePaper}")
  t "beamer colors: use expressions read the shared color mixer"
    (lineHasColor mixed "Heading" (ink.mix 70 other) && !colorLoss mixedDs "cannot be resolved")
  let (cyclic, _, cycleDs) := build
    ("\\setbeamercolor{probe cycle}{parent=frametitle}" ++
      "\\setbeamercolor{frametitle}{parent=probe cycle}")
  t "beamer colors: a cycle is named and preserves the unaffected frame"
    (colorLoss cycleDs "cycle" && reprStr cyclic.pages == reprStr plain.pages)
  let (epoch, _, _) := build parent
    ("\\begin{frame}{Earlier}alpha\\end{frame}" ++
      "\\setbeamercolor{probe base}{fg=ProbeOther}" ++
      "\\begin{frame}{Later}omega\\end{frame}")
  t "beamer colors: a body parent update changes only later frames"
    (lineHasColor epoch "Earlier" ink && lineHasColor epoch "Later" other &&
      !lineHasColor epoch "Earlier" other)
  let (native, _, _) := build
    "\\palette{frametitlefg=#173B58,frametitlebg=#E8EDF3,framesubtitlefg=#173B58}"
  t "beamer colors: inherited title channels paint the native palette page"
    (reprStr native.pages == reprStr inherited.pages)
  let (nativeAfter, _, _) := build (parent ++ "\\palette{frametitlefg=#205536}")
  t "beamer colors: a later native color keeps its precedence"
    (lineHasColor nativeAfter "Heading" third)
  let (themeAfter, _, _) := build (parent ++ "\\theme{moloch}")
  t "beamer colors: a later theme keeps its foreground precedence"
    (lineHasColor themeAfter "Heading" (Ir.Design.ofDoc
      (elabStr (colorDeck "" frame)).1).frameTitleFg)
  let (separator, separatorHtml, separatorDs) := build
    "\\title{Synthetic Deck}\\setbeamercolor{title separator}{fg=ProbeOther}" "\\maketitle"
  t "beamer colors: title separator color paints the existing title rule"
    ((allLines separator).any fun l => l.segs.any fun s => match s with
      | .rule _ _ _ c => c == other
      | _ => false)
  t "beamer colors: title separator has the matching HTML color and no loss"
    ((treeCssOne "" separatorHtml).contains "--separator: #582347" &&
      !colorLoss separatorDs "title separator")
  for theme in Theme.builtin do
    t s!"beamer colors: {theme.name} satisfies the extended design contrast contract"
      (Contrast.designContract (Ir.Design.ofPalette theme.palette))
