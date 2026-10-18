module

public import Tests.Support

public section

open LeanTex.Core

namespace Tests

/-- A lualatex probe of an inert row standing on `.asWithout`: the document with the setting and
without it, which LaTeX must set alike, and with a contrasting setting, which it must not. -/
structure InertProbe where
  reader : String
  setting : String
  withIt : String
  without : String
  contrast : Option String

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
  | _, _ => none

/-- Packages whose options a probe cannot exercise here, each with why. -/
def inertUnprobed : List (String × String) :=
  [("minted", "minted runs Pygments only under -shell-escape, which the probes refuse")]

/-- Every `.asWithout` row of the class and package tables, probed. -/
def inertProbes : List InertProbe :=
  let flow := ((Elab.classOptionsInert.lookup .flow).getD []).filter (·.2.premise == .asWithout)
  let frame := ((Elab.classOptionsInert.lookup .frame).getD []).filter (·.2.premise == .asWithout)
  let classes := flow.map fun (o, _) =>
    let c := inertClassOf o
    let ams := "\\usepackage{amsmath}\n"
    { reader := s!"documentclass {c}", setting := o, withIt := inertDoc c o ams "",
      without := inertDoc c "" ams "", contrast := (inertContrast c o).map (inertDoc c · ams "")
      : InertProbe }
  let decks := frame.map fun (o, _) =>
    { reader := "documentclass beamer", setting := o, withIt := inertDeck o,
      without := inertDeck "", contrast := (inertContrast "beamer" o).map inertDeck : InertProbe }
  let packages := (Compat.packageOptionsInert.filter (fun (p, _) =>
      !(inertUnprobed.lookup p).isSome)).flatMap fun (p, rows) =>
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
          inertDoc "article" "" (pre s!"[{c}]") (inertPackageBody p) : InertProbe }
  let hyper := (Compat.hyperrefInert.filter (·.2.premise == .asWithout)).map fun (o, _) =>
    { reader := "usepackage hyperref", setting := o,
      withIt := inertDoc "article" "" s!"\\usepackage[{o}]\{hyperref}\n" (inertPackageBody "hyperref"),
      without := inertDoc "article" "" "\\usepackage{hyperref}\n" (inertPackageBody "hyperref"),
      contrast := none : InertProbe }
  classes ++ decks ++ packages ++ hyper

/-- Every package an `.asWithout` row is probed in has a body its options act on, so its probe
can see them; the oracle judges the rest. -/
def inertProbeChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  for (p, rows) in Compat.packageOptionsInert do
    if rows.any (·.2.premise == .asWithout) && (inertUnprobed.lookup p).isNone then
      t s!"inert premise: {p}'s probe holds a body its options act on" !(inertPackageBody p).isEmpty
  t "inert premise: hyperref's probe holds a body its options act on"
    !(inertPackageBody "hyperref").isEmpty

end Tests
