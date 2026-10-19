module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- A lualatex probe of an inert row standing on `.asWithout`: the document with the setting and
without it, which LaTeX must set alike, and with a contrasting setting, which it must not; `minted`
probes run Pygments through TeX Live's restricted shell escape. -/
structure InertProbe where
  reader : String
  setting : String
  withIt : String
  without : String
  contrast : Option String
  minted : Bool

/-- A body exercising what the probed classes and packages set: a title, headings, a justified
paragraph, a numbered display, a list, a footnote and a quotation. -/
def inertProbeBody : String :=
  "\\title{Probe Title}\\author{Probe Writer}\\date{1 January 2020}\n\\begin{document}\n" ++
  "\\maketitle\n\\section{Opening}\n" ++ String.join (List.replicate 8
    "Words of an invented paragraph that run across the line and on, ") ++
  "to its end.\\footnote{An invented note.}\n\\begin{equation}a = b + c\\end{equation}\n" ++
  "\\begin{itemize}\\item One item.\\item Two items.\\end{itemize}\n" ++
  "\\begin{quote}A quoted line.\\end{quote}\n"

/-- What a package's options act on, after `\begin{document}` and the shared body. -/
def inertPackageBody : String → String
  | "amsmath" => "\\[\\sum_{i=1}^{n} i \\quad \\int_0^1 x\\,dx \\quad \\operatorname*{max}_{k} k\\]\n" ++
    "\\begin{equation}\\begin{split}a &= b\\\\ &= c\\end{split}\\end{equation}\n"
  | "csquotes" => "\\enquote{Quoted words.}\n"
  | "cleveref" => "\\begin{equation}\\label{eq:p}x = y\\end{equation}\nSee \\cref{eq:p}.\n"
  | "siunitx" => "\\num{3.14}\n"
  | "listings" => "\\begin{lstlisting}\nint x = 1;\n\\end{lstlisting}\n"
  | "nicefrac" => "\\nicefrac{1}{2}\n"
  | "algorithm2e" => "\\begin{algorithm}\\eIf{a}{b}{c}\\caption{Probe}\\end{algorithm}\n"
  | "graphicx" => "\\includegraphics[width=2cm]{example-image-a}\n"
  | "parskip" => "First paragraph.\n\nSecond paragraph.\n"
  | "xcolor" | "color" => "\\textcolor{red}{Red words.}\n"
  | "microtype" => String.join (List.replicate 12 "Justified words a margin kerns and stretches, ") ++
    "ending here.\n"
  | "hyperref" => "\\url{https://example.org}\n"
  | _ => ""

/-- Packages a probe needs beside the probed one. -/
def inertPackageCompanions : String → String
  | "csquotes" => "\\usepackage[english]{babel}\n"
  | "cleveref" => "\\usepackage{amsmath}\n"
  | _ => ""

/-- A flow document of class `cls` with `opts`, the package line before the body. -/
def inertDoc (cls opts pre extra : String) : String :=
  let bracket := if opts.isEmpty then "" else s!"[{opts}]"
  s!"\\documentclass{bracket}\{{cls}}\n{pre}" ++ inertProbeBody ++ extra ++ "\\end{document}\n"

/-- A beamer deck with `opts`, one frame of text. -/
def inertDeck (opts : String) : String :=
  let bracket := if opts.isEmpty then "" else s!"[{opts}]"
  s!"\\documentclass{bracket}\{beamer}\n\\title\{Probe Title}\n\\begin\{document}\n" ++
    "\\begin{frame}{Frame title}Frame words.\\end{frame}\n\\end{document}\n"

/-- The class a flow class option belongs to, KOMA-Script's in scrartcl. -/
def inertClassOf (o : String) : String :=
  if o.startsWith "version=" || o.startsWith "footinclude" || o.startsWith "titlepage=" then
    "scrartcl"
  else "article"

/-- A setting LaTeX sets apart from a probed one, which shows the probe can see what it judges. -/
def inertContrast : String → String → Option String
  | "amsmath", "reqno" => some "leqno"
  | "amsmath", "sumlimits" => some "nosumlimits"
  | "amsmath", "namelimits" => some "nonamelimits"
  | "amsmath", "nointlimits" => some "intlimits"
  | "amsmath", "centertags" => some "tbtags"
  | "article", "reqno" => some "leqno"
  | "article", "onecolumn" => some "twocolumn"
  | "beamer", "c" => some "t"
  | "beamer", "slidescentered" => some "slidestop"
  | "scrartcl", "footinclude=false" => some "footinclude=true"
  | "graphicx", "final" => some "draft"
  | "cleveref", "english" => some "ngerman"
  | "siunitx", _ => some "output-decimal-marker={,}"
  | "parskip", "indent=0pt" => some "indent=2em"
  | "csquotes", "english=american" => some "english=british"
  | "xcolor", "usenames" => some "gray"
  | "color", "usenames" => some "monochrome"
  | _, _ => none

/-- A beamer deck with `pre` before its title, a title page and a frame of an itemize, an
enumerate and a block, which the predefined templates draw. -/
def inertSiteDeck (pre : String) : String :=
  s!"\\documentclass\{beamer}\n{pre}\\title\{Probe Title}\\author\{Probe Writer}\n" ++
    "\\begin{document}\n\\begin{frame}\\titlepage\\end{frame}\n" ++
    "\\begin{frame}{Frame title}\\begin{itemize}\\item One item.\\end{itemize}" ++
    "\\begin{enumerate}\\item First item.\\end{enumerate}" ++
    "\\begin{block}{Probe block}Block words.\\end{block}\\end{frame}\n\\end{document}\n"

/-- A predefined template LaTeX sets apart from `default`, which shows the probe can see it. -/
def inertTemplateContrast : String → Option String
  | "itemize items" => some "circle"
  | "enumerate items" => some "square"
  | "blocks" => some "rounded"
  | "footline" => some "frame number"
  | _ => none

/-- Each display key `\setmintedinline` reads to nothing, with a value it takes. -/
def inertMintedValue : String → String
  | "numbers" => "numbers=left"
  | "firstnumber" => "firstnumber=3"
  | "stepnumber" => "stepnumber=2"
  | "numbersep" => "numbersep=9pt"
  | "numberblanklines" => "numberblanklines=false"
  | "frame" => "frame=single"
  | "framerule" => "framerule=2pt"
  | "framesep" => "framesep=6pt"
  | "rulecolor" => "rulecolor=red"
  | "label" => "label=Probe"
  | "labelposition" => "labelposition=bottomline"
  | "xleftmargin" => "xleftmargin=1cm"
  | "xrightmargin" => "xrightmargin=1cm"
  | "vspace" => "vspace=1cm"
  | "listparameters" => "listparameters=\\small"
  | "firstline" => "firstline=2"
  | "lastline" => "lastline=1"
  | "highlightlines" => "highlightlines=1"
  | "highlightcolor" => "highlightcolor=red"
  | k => k

/-- The probes of an inline inert site, one per setting its reader takes there. -/
def inertSiteProbes : Compat.InertSite → List InertProbe
  | .geometryRatio =>
    let geo (opts : String) := inertDoc "article" "" s!"\\usepackage[{opts}]\{geometry}\n" ""
    [{ reader := "usepackage geometry", setting := "vmarginratio=1:2 beside top and bottom",
       withIt := geo "top=1in,bottom=1in,vmarginratio=1:2", without := geo "top=1in,bottom=1in",
       contrast := some (geo "top=1in,bottom=2in"), minted := false },
     { reader := "usepackage geometry", setting := "vmarginratio=1:2 beside a height and top",
       withIt := geo "textheight=8in,top=1in,vmarginratio=1:2", without := geo "textheight=8in,top=1in",
       contrast := some (geo "textheight=8in,top=2in"), minted := false }]
  | .defaultTemplate => Compat.defaultTemplates.map fun e =>
    { reader := "setbeamertemplate", setting := s!"{e} [default]",
      withIt := inertSiteDeck s!"\\setbeamertemplate\{{e}}[default]\n", without := inertSiteDeck "",
      contrast := (inertTemplateContrast e).map fun c =>
        inertSiteDeck s!"\\setbeamertemplate\{{e}}[{c}]\n", minted := false }
  | .emptyTemplate => (Compat.emptyTemplates.filter (· != "navigation symbols")).map fun e =>
    { reader := "setbeamertemplate", setting := s!"{e} emptied",
      withIt := inertSiteDeck s!"\\setbeamertemplate\{{e}}\{}\n", without := inertSiteDeck "",
      contrast := some (inertSiteDeck s!"\\setbeamertemplate\{{e}}\{Probe {e}}\n"), minted := false }
  | .memoirTitle => ["titlepage", "notitlepage"].map fun o =>
    let abstract := "\\begin{abstract}An invented summary.\\end{abstract}\n"
    { reader := "documentclass memoir", setting := o, withIt := inertDoc "memoir" o "" abstract,
      without := inertDoc "memoir" "" "" abstract, contrast := none, minted := false }
  | .komaSepRule => (["headsepline", "footsepline"].flatMap fun k =>
      ["false", "off", "no"].map (k, ·)).map fun (k, v) =>
    let koma (opts : String) :=
      inertDoc "scrartcl" "" s!"\\usepackage\{scrlayer-scrpage}\\pagestyle\{scrheadings}\\ihead\{Probe head}\\ifoot\{Probe foot}{opts}\n"
        "\\clearpage\nA second page, under the running head and foot.\n"
    { reader := "KOMAoptions", setting := s!"{k}={v}", withIt := koma s!"\\KOMAoptions\{{k}={v}}",
      without := koma "", contrast := some (koma s!"\\KOMAoptions\{{k}=true}"), minted := false }
  | .mintedInline => Compat.mintedDisplayKeys.map fun k =>
    let code := "Inline \\mintinline{python}{x = 1} code.\n"
    { reader := "setmintedinline", setting := inertMintedValue k,
      withIt := inertDoc "article" "" s!"\\usepackage\{minted}\n\\setmintedinline\{{inertMintedValue k}}\n" code,
      without := inertDoc "article" "" "\\usepackage{minted}\n" code,
      contrast := some (inertDoc "article" "" "\\usepackage{minted}\n\\setmintedinline{fontsize=\\Large}\n" code),
      minted := true }

/-- Every `.asWithout` row of the class and package tables and every inline inert site, probed. -/
def inertProbes : List InertProbe :=
  let flow := ((Elab.classOptionsInert.lookup .flow).getD []).filter (·.2.premise == .asWithout)
  let frame := ((Elab.classOptionsInert.lookup .frame).getD []).filter (·.2.premise == .asWithout)
  let classes := flow.map fun (o, _) =>
    let c := inertClassOf o
    let ams := "\\usepackage{amsmath}\n"
    { reader := s!"documentclass {c}", setting := o, withIt := inertDoc c o ams "",
      without := inertDoc c "" ams "", contrast := (inertContrast c o).map (inertDoc c · ams ""),
      minted := false : InertProbe }
  let decks := frame.map fun (o, _) =>
    { reader := "documentclass beamer", setting := o, withIt := inertDeck o,
      without := inertDeck "", contrast := (inertContrast "beamer" o).map inertDeck, minted := false
      : InertProbe }
  let packages := Compat.packageOptionsInert.flatMap fun (p, rows) =>
    (rows.filter (·.2.premise == .asWithout)).map fun (o, _) =>
      let pre (opt : String) : String :=
        inertPackageCompanions p ++ s!"\\usepackage{opt}\{{p}}\n"
      -- A value holding a comma is one value, braced.
      let spelled := match o.splitOn "=" with
        | k :: v :: rest => if (String.intercalate "=" (v :: rest)).contains ',' then
            s!"{k}=\{{String.intercalate "=" (v :: rest)}}" else o
        | _ => o
      { reader := s!"usepackage {p}", setting := o,
        withIt := inertDoc "article" "" (pre s!"[{spelled}]") (inertPackageBody p),
        without := inertDoc "article" "" (pre "") (inertPackageBody p),
        contrast := (inertContrast p o).map fun c =>
          inertDoc "article" "" (pre s!"[{c}]") (inertPackageBody p), minted := p == "minted"
        : InertProbe }
  let hyper := (Compat.hyperrefInert.filter (·.2.premise == .asWithout)).map fun (o, _) =>
    { reader := "usepackage hyperref", setting := o,
      withIt := inertDoc "article" "" s!"\\usepackage[{o}]\{hyperref}\n" (inertPackageBody "hyperref"),
      without := inertDoc "article" "" "\\usepackage{hyperref}\n" (inertPackageBody "hyperref"),
      contrast := none, minted := false : InertProbe }
  let sites := Compat.InertSite.all.flatMap inertSiteProbes
  classes ++ decks ++ packages ++ hyper ++ sites

/-- Every package an `.asWithout` row is probed in has a body its options act on, every inline inert
site has a probe, and a probe loading minted runs Pygments; the oracle judges the rest. -/
def inertProbeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (p, rows) in Compat.packageOptionsInert do
    if rows.any (·.2.premise == .asWithout) then
      t s!"inert premise: {p}'s probe holds a body its options act on" !(inertPackageBody p).isEmpty
  t "inert premise: hyperref's probe holds a body its options act on"
    !(inertPackageBody "hyperref").isEmpty
  for site in Compat.InertSite.all do
    t s!"inert premise: the inline site {repr site} is probed" !(inertSiteProbes site).isEmpty
  t "inert premise: a minted probe runs Pygments through the restricted shell escape"
    (inertProbes.all fun p => p.minted == (hasStr p.withIt "{minted}" || hasStr p.without "{minted}" ||
      p.contrast.any (hasStr · "{minted}")))

end Tests
