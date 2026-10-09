module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

namespace MintedSettings

/-- Invented source only. Real tabs, interior blank lines and HTML
metacharacters must survive the typed artifact's code text. -/
def source : String := "A\tB\nAAAA\tC\nAA\tD\tE\n\n  <node>&\"value\""

def listing (options : String := "") (language : String := "text")
    (content : String := source) : String :=
  "\\begin{minted}" ++ (if options.isEmpty then "" else "[" ++ options ++ "]") ++
    "{" ++ language ++ "}\n" ++ content ++ "\n\\end{minted}\n"

mutual

/-- Read the code containers the typed artifact actually emits. -/
def preNodesOne (acc : Array Html.Node) : Html.Node → Array Html.Node
  | .text _ | .style _ | .script _ _ => acc
  | n@(.elem tag _ kids) =>
    if tag == "pre" then acc.push n else preNodesList acc kids.toList

def preNodesList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: ns => preNodesList (preNodesOne acc n) ns

end

def html (src : String) : Array Html.Node × String :=
  let (head, body, _) := HtmlDoc.emitTree {} (elabStr src).1
  (preNodesList #[] body.toList, treeCssList "" head.toList)

def preStyle (n : Html.Node) : String :=
  match n with
  | .elem _ attrs _ =>
    (((attrs.find? (·.1 == "style")).map (·.2)).getD "").replace " " ""
  | _ => ""

/-- Font and tab declarations are on the actual pre element; the listing
stylesheet separately makes its code child inherit the selected size. -/
def htmlSettings (n : Html.Node) (factor : String) (tab : Nat) (wrap : Bool) : Bool :=
  let s := preStyle n
  hasStr s ("font-size:" ++ factor ++ "em") &&
    hasStr s s!"tab-size:{tab}" &&
    (hasStr s "white-space:pre-wrap" == wrap)

/-- Ignore token paint when comparing settings: syntax highlighting has
its own tests. Read positions, content, face and size from shipped lines. -/
def pageSettings (out : Layout.Out) :=
  (bodyLines out).map fun l =>
    (l.x, l.y, metricRunsAt l, l.segs.filterMap fun s => match s with
      | .run f _ _ w glyphs size _ _ _ _ _ =>
        if glyphs.isEmpty then none else some (f, w, size)
      | .gap _ _ | .decoratedGap _ _ _ | .decoration _ _ _ _ _
      | .rule _ _ _ _ | .poly _ _ | .image _ _ _ => none)

def glyphX (l : Layout.LineOut) (wanted : Char) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c == wanted then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ => x := x + w
    | .poly _ _ => pure ()
  return none

def baselineGaps (out : Layout.Out) : Array Dim.Sp :=
  let lines := bodyLines out
  (lines.zip (lines.extract 1 lines.size)).map fun (a, b) => b.y - a.y

end MintedSettings

/-- LuaLaTeX (minted 3 / FancyVerb) synthetic probe:
global < lexer < environment; lexer lookup is case sensitive; groups and
environments restore defaults; repeated declarations update individual
keys. `fontsize=\small` selects the step, whereas bare `small` prints
literal text without changing size and must not silently select a step.
These checks assert Layout.Out and the typed HTML, never an IR dump. -/
def mintedSettingsChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some bytes ← findFont | failures ref "minted settings: body fixture font missing"
  let .ok bodyFont := Font.parse bytes | failures ref "minted settings: body fixture font invalid"
  let monoBytes ← IO.FS.readBinFile (testFonts ++ "/SourceCodePro-Regular.otf")
  let .ok mono := Font.parse monoBytes | failures ref "minted settings: mono fixture font invalid"
  let fonts : Font.FontSet := {
    fonts := #[bodyFont, mono]
    index := ((List.range 3).flatMap fun slot =>
      let f := if slot == 2 then 1 else 0
      [((slot, 400, false), f), ((slot, 700, false), f),
       ((slot, 400, true), f), ((slot, 700, true), f)]).toArray }
  let code := @MintedSettings.listing
  let rendered (src : String) := layoutOf fonts (elabStr src).1
  let hasSize (src : String) (pt : Int) :=
    let sizes := metricRunSizes (rendered src)
    !sizes.isEmpty && sizes.all (· == Dim.pt pt)
  let same (a b : String) :=
    MintedSettings.pageSettings (rendered a) == MintedSettings.pageSettings (rendered b) &&
      (MintedSettings.html a).1.map MintedSettings.preStyle ==
        (MintedSettings.html b).1.map MintedSettings.preStyle &&
      (MintedSettings.html a).1.map (nodeTextOne "") ==
        (MintedSettings.html b).1.map (nodeTextOne "")
  let simple := "Alpha Bravo"
  let globals := "\\setminted{fontsize=\\small,tabsize=3,breaklines}"
  let localOptions := "fontsize=\\small,tabsize=3,breaklines"
  let globalDoc := dvDoc globals (code "" "text" simple)
  let localDoc := dvDoc "" (code localOptions "text" simple)
  t "minted defaults: supported declaration has no unknown/key warning"
    (!(warnCodes globalDoc).contains "W0301" && !(warnCodes globalDoc).contains "W0110")
  t "minted defaults: global and local options ship the same settings" (same globalDoc localDoc)
  t "minted fontsize: declared small ships 9pt mono glyphs" (hasSize globalDoc 9)
  t "minted fontsize: actual face is the mono slot"
    ((bodyLines (rendered globalDoc)).any fun l => l.segs.any fun s => match s with
      | .run f _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty && f == 1
      | _ => false)
  let (pres, css) := MintedSettings.html globalDoc
  t "minted fontsize/tab/wrap: typed HTML declares settings without nested shrink"
    (pres.size == 1 && pres.any (MintedSettings.htmlSettings · "0.9" 3 true) &&
      hasStr css "font-family: var(--font-mono)" &&
      hasStr css "pre > code { font-size: inherit; }")
  t "minted default: inherits the body size" (hasSize (dvDoc "" (code "" "text" simple)) 10)
  t "minted auto: inherits a scoped named size"
    (hasSize (dvDoc "" ("{\\small\n" ++ code "fontsize=auto" "text" simple ++ "}")) 9)

  -- LuaLaTeX/FancyVerb selects the listing's own size and baseline skip:
  -- at the article 10pt base, footnotesize is 8/9.5pt. Native named steps
  -- use Ir.leadingFor (8/9.6pt); a 10pt body strut must not hold these
  -- lines at 12pt. Explicit \fontsize keeps its declared skip exactly.
  for (step, pt) in [("normalsize", 10), ("small", 9),
      ("footnotesize", 8), ("scriptsize", 7)] do
    let src := dvDoc "" (code ("fontsize=\\" ++ step) "text"
      "Alpha Bravo\n\nAlpha Bravo\nAlpha Bravo")
    let out := rendered src
    let gaps := MintedSettings.baselineGaps out
    t s!"minted rhythm: {step} owns its line box, including a blank line"
      (hasSize src pt && gaps.size == 3 &&
        gaps.all (· == Ir.leadingFor (Dim.pt pt)))
    t s!"minted rhythm: {step} has an explicit typed HTML baseline ratio"
      ((MintedSettings.html src).1.any fun n =>
        hasStr (MintedSettings.preStyle n) "line-height:1.2;")
  let explicit := dvDoc ""
    ("{\\fontsize{8pt}{13pt}\\selectfont\n" ++
      code "" "text" "Alpha Bravo\nAlpha Bravo\nAlpha Bravo" ++ "}")
  t "minted rhythm: inherited absolute size and leading resolve once"
    (hasSize explicit 8 && MintedSettings.baselineGaps (rendered explicit) == #[Dim.pt 13, Dim.pt 13] &&
      (MintedSettings.html explicit).1.any fun n =>
        hasStr (MintedSettings.preStyle n) "line-height:13pt;")
  -- A deck magnifies every physical font length by the same stage share.
  -- Fixed CSS points here left code behind while its surrounding prose grew.
  for ratio in ["169", "43"] do
    let src := "\\documentclass[aspectratio=" ++ ratio ++ "]{slides}\n" ++
      "\\begin{document}\\begin{frame}{}\n{\\fontsize{8pt}{13pt}\\selectfont Intro.\n\n" ++
      code "fontsize=auto" "text" "Alpha Bravo\nAlpha Bravo\nAlpha Bravo" ++
      "}\\end{frame}\\end{document}"
    let doc := (elabStr src).1
    let lines := (bodyLines (rendered src)).filter (lineText · == "AlphaBravo")
    let gaps := (lines.zip (lines.extract 1 lines.size)).map fun (a, b) => b.y - a.y
    t s!"minted deck {ratio}: absolute size shares the stage and its PDF glyph size"
      (hasSize src 8 && (MintedSettings.html src).1.any fun n =>
        cssStageLength (MintedSettings.preStyle n) "font-size" (Dim.pt 8) doc.page.height)
    t s!"minted deck {ratio}: absolute leading shares the stage and its PDF baseline"
      (gaps == #[Dim.pt 13, Dim.pt 13] &&
        (MintedSettings.html src).1.any fun n =>
          cssStageLength (MintedSettings.preStyle n) "line-height" (Dim.pt 13) doc.page.height)

  let pre := globals ++
    "\n\\setminted[python]{fontsize=\\scriptsize,tabsize=5,breaklines=false}" ++
    "\n\\setminted{fontsize=\\normalsize,tabsize=7,breaklines}"
  for (name, lang, opts) in [
      ("language beats later global", "python", "fontsize=\\scriptsize,tabsize=5,breaklines=false"),
      ("other language reads global", "text", "fontsize=\\normalsize,tabsize=7,breaklines"),
      ("lexer lookup retains case", "Python", "fontsize=\\normalsize,tabsize=7,breaklines")] do
    t s!"minted precedence: {name}"
      (same (dvDoc pre (code "" lang)) (dvDoc "" (code opts lang)))
  t "minted precedence: environment overrides all defaults and then expires"
    (same (dvDoc pre (code "fontsize=\\large,tabsize=4,breaklines" "python" simple ++
        code "" "python" simple))
      (dvDoc "" (code "fontsize=\\large,tabsize=4,breaklines" "python" simple ++
        code "fontsize=\\scriptsize,tabsize=5,breaklines=false" "python" simple)))
  t "minted precedence: later declaration updates only its keys"
    (same (dvDoc (pre ++ "\n\\setminted[python]{tabsize=9}") (code "" "python"))
      (dvDoc "" (code "fontsize=\\scriptsize,tabsize=9,breaklines=false" "python")))
  for (name, openGroup, closeGroup) in [
      ("braces", "{", "}"),
      ("environment", "\\begin{minipage}{120pt}", "\\end{minipage}")] do
    let changed := "\\setminted[python]{fontsize=\\large,tabsize=6,breaklines}"
    t s!"minted scope: {name} restore outer defaults"
      (same (dvDoc pre (openGroup ++ changed ++ "\n" ++ code "" "python" simple ++
          closeGroup ++ "\n" ++ code "" "python" simple))
        (dvDoc pre (openGroup ++ code "fontsize=\\large,tabsize=6,breaklines" "python" simple ++
          closeGroup ++ "\n" ++ code "" "python" simple)))
  t "minted defaults: lstset does not alter minted"
    (same (dvDoc ("\\lstset{tabsize=2,breaklines, basicstyle=\\tiny}\n" ++ globals)
        (code "" "text" simple)) globalDoc)
  let lst (opts : String) :=
    "\\begin{lstlisting}[" ++ opts ++ "]\n" ++ simple ++ "\n\\end{lstlisting}\n"
  let lstDefaults := "\\lstset{basicstyle=\\ttfamily\\small,tabsize=3,breaklines=true}"
  -- listings wraps with its own 20 pt continuation indent, which minted's
  -- wrap does not carry, so the global keys are held to the same keys
  -- stated locally, and to minted's size, tab and wrap.
  t "listing defaults: basicstyle size/tab/wrap reach both artifacts"
    (same (dvDoc lstDefaults (lst ""))
        (dvDoc "" (lst "basicstyle=\\ttfamily\\small,tabsize=3,breaklines=true")) &&
      MintedSettings.pageSettings (rendered (dvDoc lstDefaults (lst ""))) ==
        MintedSettings.pageSettings (rendered globalDoc) &&
      (MintedSettings.html (dvDoc lstDefaults (lst ""))).1.any
        (MintedSettings.htmlSettings · "0.9" 3 true) &&
      !(warnCodes (dvDoc lstDefaults (lst ""))).contains "W0110")
  t "listing defaults: local keys override global keys"
    (same (dvDoc lstDefaults (lst "basicstyle=\\ttfamily\\large,tabsize=5,breaklines=false"))
      (dvDoc "" (code "fontsize=\\large,tabsize=5,breaklines=false" "text" simple)))
  t "listing scope: lstset restores after a brace group"
    (same (dvDoc lstDefaults
      ("{\\lstset{basicstyle=\\ttfamily\\scriptsize,tabsize=4}" ++ lst "" ++ "}\n" ++ lst ""))
      (dvDoc lstDefaults
        ("{" ++ lst "basicstyle=\\ttfamily\\scriptsize,tabsize=4" ++ "}\n" ++ lst "")))

  let tabs := dvDoc "\\setminted{fontsize=\\normalsize,tabsize=4}"
    (code "" "text" MintedSettings.source)
  let tabOut := rendered tabs
  let tabLines := bodyLines tabOut
  let cell := Dim.pt 10 * mono.spaceAdvance / mono.unitsPerEm
  t "minted tabs: no TAB glyph is dropped"
    (!(tabOut.diags.any fun d => d.kind == .E0405))
  t "minted tabs: advance to the next stop, including an exact stop"
    (tabLines.size == 5 &&
      (tabLines[0]?.bind (MintedSettings.glyphX · 'B')) ==
        tabLines[0]?.map (fun l => l.x + cell * 4) &&
      (tabLines[1]?.bind (MintedSettings.glyphX · 'C')) ==
        tabLines[1]?.map (fun l => l.x + cell * 8) &&
      (tabLines[2]?.bind (MintedSettings.glyphX · 'D')) ==
        tabLines[2]?.map (fun l => l.x + cell * 4) &&
      (tabLines[2]?.bind (MintedSettings.glyphX · 'E')) ==
        tabLines[2]?.map (fun l => l.x + cell * 8))
  let (tabPres, _) := MintedSettings.html tabs
  t "minted source: typed HTML preserves tabs, blank lines and metacharacters"
    (tabPres.size == 1 && tabPres.any fun n => nodeTextOne "" n == MintedSettings.source)
  t "minted tabs: typed HTML uses the declared stops"
    (tabPres.any (MintedSettings.htmlSettings · "1" 4 false))

  let longLine := "Alpha Bravo Charlie Delta Echo Foxtrot Golf Hotel India"
  let narrow (wrap : String) := dvDoc ""
    ("\\begin{minipage}{96pt}\n" ++ code ("fontsize=\\normalsize,breaklines=" ++ wrap)
      "text" longLine ++ "\\end{minipage}")
  let wrapped := rendered (narrow "true")
  let unwrapped := rendered (narrow "false")
  let lines := bodyLines wrapped
  t "minted wrapping: true breaks at spaces; false keeps one source line"
    (lines.size > 1 && (bodyLines unwrapped).size == 1)
  t "minted wrapping: shipped code fits the local measure"
    (!lines.isEmpty && lines.all fun l => l.setWidth ≤ Dim.pt 96)
  t "minted wrapping: every source word ships exactly once"
    (((lines.toList.map (fun l => (lineText l).replace " " "")).foldl (· ++ ·) "") ==
      longLine.replace " " "")
  t "minted wrapping: HTML source is unchanged by the wrapping policy"
    ((MintedSettings.html (narrow "true")).1.map (nodeTextOne "") ==
      (MintedSettings.html (narrow "false")).1.map (nodeTextOne ""))
  let narrowLines (source : String) := dvDoc "" ("\\begin{minipage}{84pt}\n" ++
    code "fontsize=\\footnotesize,breaklines" "text" source ++ "\\end{minipage}")
  for (name, source) in [
      ("indented lines", "  Alpha Bravo\n  Charlie Delta\n  Echo Foxtrot"),
      ("unbreakable line", "AlphaBravoCharlieDeltaEchoFoxtrot\nAlpha Bravo\nCharlie Delta")] do
    let out := rendered (narrowLines source)
    let bare (s : String) := (s.replace "\u00a0" "").replace " " ""
    let shipped := (bodyLines out).map fun l => bare (lineText l)
    t s!"minted breaks: {name} retain their source boundaries without W0386"
      (shipped == (source.splitOn "\n").toArray.map bare &&
        !(out.diags.any fun d => d.kind == .W0386))
  let indented := bodyLines (rendered (narrowLines "  Alpha Bravo\n  Charlie Delta\n  Echo Foxtrot"))
  let smallCell := Dim.pt 8 * mono.spaceAdvance / mono.unitsPerEm
  t "minted breaks: kept indentation has its full shipped advance"
    ((indented.zip #['A', 'C', 'E']).all fun (l, c) =>
      MintedSettings.glyphX l c == some (l.x + 2 * smallCell))
  let realWrap := rendered (narrowLines "Alpha Bravo Charlie Delta Echo\nFoxtrot\nGolf")
  t "minted breaks: a genuinely split declared line still raises W0386"
    ((bodyLines realWrap).size > 3 && realWrap.diags.any fun d => d.kind == .W0386)
  t "minted wrapping: continuation baselines use the selected listing size"
    (MintedSettings.baselineGaps realWrap |>.all (· == Ir.leadingFor (Dim.pt 8)))
  for wrap in ["true", "false"] do
    let identifier := "alpha-bravo-charlie-delta-echo"
    let literal := dvDoc "" ("\\begin{minipage}{96pt}" ++
      code ("fontsize=\\normalsize,breaklines=" ++ wrap) "text" identifier ++
      "\\end{minipage}")
    let literalLines := bodyLines (rendered literal)
    t s!"minted wrapping: {wrap} preserves a literal hyphen inside an identifier"
      (literalLines.size == 1 && literalLines.any fun l => lineText l == identifier)
    let spaced := bodyLines (rendered (dvDoc ""
      (code ("fontsize=\\normalsize,breaklines=" ++ wrap) "text" "A   B  C")))
    t s!"minted wrapping: {wrap} keeps repeated spaces at the font's natural width"
      (spaced.size == 1 &&
        (spaced[0]?.bind (MintedSettings.glyphX · 'B')) ==
          spaced[0]?.map (fun l => l.x + cell * 4) &&
        (spaced[0]?.bind (MintedSettings.glyphX · 'C')) ==
          spaced[0]?.map (fun l => l.x + cell * 7))

  let refused := dvDoc
    "\\setminted{fontsize=small,tabsize=4,breaklines=false,unknownsetting=on}"
    (code "" "text" simple)
  let (_, diags) := elabStr refused
  t "minted honesty: bare fontsize is named with its corrective spelling"
    (diags.any fun d => d.kind == .W0110 && hasStr d.message "fontsize" &&
      hasStr (d.help.getD "") "\\small")
  t "minted honesty: an unsupported key is named"
    (diags.any fun d => d.kind == .W0110 && hasStr d.message "unknownsetting")
  t "minted honesty: supported neighbors of refused keys still ship"
    ((MintedSettings.html refused).1.any (MintedSettings.htmlSettings · "1" 4 false))
  for bad in ["tabsize=0", "tabsize=-2", "tabsize=101", "tabsize=wide",
      "breaklines=perhaps", "fontsize=\\unlistedsize"] do
    t s!"minted honesty: invalid option {bad} is named"
      ((warnCodes (dvDoc ("\\setminted{" ++ bad ++ "}") (code "" "text" simple))).contains "W0110")

end Tests
