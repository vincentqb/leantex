import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

def diagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let codes := DiagCode.all.map (·.code)
  for c in codes.eraseDups do
    check ref s!"diag {c}: one code, one meaning"
      ((codes.filter (· == c)).length == 1)
  for c in DiagCode.all do
    check ref s!"diag {c.code}: carries a meaning" (!c.meaning.isEmpty)
    check ref s!"diag {c.code}: code string is code-shaped" (isDiagCode c.code)
  -- No constructor outlives its last emission site, and an emitted
  -- constructor's code string is registered under its own name (a
  -- `spec` arm answering another arm's number would surface here).
  -- The compiler already holds the other direction: a code that is not
  -- a constructor cannot be emitted at all.
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  let mut emitted : List String := []
  for f in files do
    if f.toString == "LeanTex/Core/Diag.lean" then continue
    let src ← IO.FS.readFile f
    for c in appliedCodes (stripNonCode src) do
      if !emitted.contains c then
        emitted := c :: emitted
  for c in emitted do
    check ref s!"diag {c}: emitted by the engine but not in the registry"
      (codes.contains c)
  for c in codes do
    check ref s!"diag {c}: registered but no longer emitted"
      (emitted.contains c)

/- Every registered diagnostic renders into one golden a person can read
whole: tests/golden/diagnostics.txt. The witness table below holds one
firing input per code — an exhaustive match, so a new `DiagCode`
constructor does not build until it names the input that fires it, and the
coverage check holds each witness to actually firing its code. -/

/-- Diagnostics of resolving a hand-built document against `.bib` text:
`Bib.apply` is pure, so the witness needs no driver. -/
def dvBib (bib : String) (cite : String) (style : Option String) : Array Diag :=
  (Bib.apply #[("refs", bib)]
    { body := #[.para #[.cite false #[cite]],
        .bibliography "refs" style #[]] }).2

/-- Diagnostics of the data-expansion pass over a source: the pass runs
before elaboration and is pure over inline records, so the witness lexes
and parses itself and needs no driver. -/
def dvData (src : String) : Array Diag :=
  (Data.expandData "t" #[] (Parse.parse "t" (Lex.lex "t" src).1).1).2

/-- A driver probe: one real driver path, run against a sandbox directory
the harness creates and deletes. A probe returns what the driver returned
and never builds a `Diag` itself, so a driver path that stops emitting its
code leaves that code's witness empty and the suite fails. -/
abbrev DriverProbe := System.FilePath → IO (Array Diag)

/-- The probed driver codes, by the code each probe must fire. Each runs a
real driver decision and returns what that decision returned; a probe never
builds a `Diag` itself, so a driver path that stops emitting its code leaves
that code's witness empty and the suite fails.

Hermetic: nothing a probe fires on depends on what this host has installed.
Three shapes appear, because a message the golden records must be the same
on every host. The sandbox probes (E0501, E0502, W0379) write into — or
read — the temp directory the harness makes and name files inside it; their
messages are path-free, and the golden drops spans, so the sandbox's random
name never reaches the file. The three document-file reads (E0001, E0503,
E0365) carry the resolved path in the message or the help, so they name a
file *relative to the working directory* — the same spelling on every host,
resolving against a tree that contains no `doc.tex`, `references.bib` or
`records.bib`. Should one appear, the read succeeds, the probe returns
nothing, and the coverage check below fails loudly: the failure mode is a
red suite, never a green one. The font-environment probes (E0402, W0008,
W0011, N0016) name paths under the suite's own shipped font directory, and
the two math-face ones hand the decision exactly those faces — a scan the
repository carries, not one the machine answers — so which family the
engine picks, and the path it names, are the same wherever the suite runs.

A driver code is probeable exactly when its emission site is reachable as a
unit and hands its diagnostics back: the modules under `LeanTex/Cli/` are.
The codes still witnessed by a constructed value below are emitted from the
entry path in Main.lean, which is not callable as a unit — or, for the
remaining font codes (E0401, E0403, E0404), decided against the host itself:
no font installed at all, the host's nearest family names, a file its scan
indexes and the parser rejects. Making one of the first kind probeable is a
driver refactor, not a new mechanism here: move the decision into a module
that returns its diagnostics, then add a row. -/
def driverProbes : Array (DiagCode × DriverProbe) :=
  let splice (dir : System.FilePath) (body : String) : IO (Array Diag) := do
    let doc := dir / "doc.tex"
    let src := "\\documentclass{article}\n\\begin{document}\n" ++ body ++
      "\n\\end{document}\n"
    IO.FS.writeFile doc src
    let path := doc.toString
    let (raws, _) := Parse.parse path (Lex.lex path src).1
    let (_, ds, _) ← Input.expandInputs path raws
    return ds
  #[(.E0502, fun dir => splice dir "\\input{chapter1}"),
    (.E0501, fun dir => do
      IO.FS.writeFile (dir / "loop.tex") "Around again.\n\\input{loop}\n"
      splice dir "\\input{loop}"),
    (.E0001, fun _ => do
      match ← Input.readSource "doc.tex" with
      | .error d => return #[d]
      | .ok _ => return #[]),
    (.E0503, fun _ => do
      let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
        "A claim\\cite{k}.\n\\bibliography{references}\n\\end{document}\n")).1
      return (← Input.resolveBibliography "doc.tex" doc).2),
    (.E0365, fun _ => do
      let src := "\\documentclass{article}\n\\data{ file = \"records\" }\n" ++
        "\\begin{document}\n\\begin{foreach}{j}{job}\\val{j.role}\\end{foreach}\n" ++
        "\\end{document}\n"
      let (raws, _) := Parse.parse "doc.tex" (Lex.lex "doc.tex" src).1
      return (← Input.resolveData "doc.tex" raws).2),
    (.E0402, fun _ => do
      let mut ds : Array Diag := #[]
      for path in ["face.ttf", "README.md"] do
        match ← FontEnv.loadOverride path with
        | .error d => ds := ds.push d
        | .ok _ => pure ()
      return ds),
    (.W0008, fun _ => do
      let doc := (elabStr ("\\documentclass{article}\n\\fonts{ dir = \"fonts\" }\n" ++
        "\\begin{document}\nx\n\\end{document}\n")).1
      return (← FontEnv.resolveDocDirs "doc.tex" doc.fonts.dirs).2),
    (.W0379, fun dir => do
      match ← Boundary.coldPicture dir "lualatex"
          (Ir.picHash "\\draw (0,0) circle (1);") with
      | .error d => return #[d]
      | .ok _ => return #[]),
    (.W0011, fun _ => do
      let faces ← FontDb.scanRoots [testFonts]
      return (← FontEnv.resolveMath faces (some "Open Sans") none false #[] #[] #[]).diags),
    (.N0016, fun _ => do
      let faces ← FontDb.scanRoots [testFonts]
      let companion ← FontEnv.resolveMath faces none (some "Fira Sans") true #[] #[] #[]
      let first ← FontEnv.resolveMath faces none (some "Open Sans") true #[] #[] #[]
      return companion.diags ++ first.diags)]

/-- Every probe run once, each in its own sandbox, removed afterwards. -/
def runDriverProbes : IO (Array (DiagCode × Array Diag)) :=
  driverProbes.mapM fun (c, probe) => do
    let ds ← IO.FS.withTempDir probe
    return (c, ds)

/-- One firing input per code. `one` maps every slot to one face;
`mapped` adds a second face and a fallback map for the substitution codes;
`withMath` carries a math face with no fallback, for the codes only a
formula can fire. `probed` reads the driver probes' own output, so a probed
code's witness is what the driver did rather than a value written here. The
remaining synthetic driver arguments mirror what Main.lean passes. -/
def diagWitness (one mapped withMath : Font.FontSet)
    (probed : DiagCode → Array Diag) : DiagCode → Array Diag
  | .E0001 => probed .E0001
  | .E0002 =>
    match Utf8.validate (ByteArray.mk #[0xC3, 0x28]) with
    | some e => #[e.toDiag "doc.tex"]
    | none => #[]
  | .E0101 => dvE "a\\"
  | .E0102 => dvE "\\begin{verbatim}\nx"
  | .E0111 => dvE (dvDeck "" ("\\setbeamertemplate{footline}{\\insertframenumber}\n" ++
      "\\begin{frame}{T}\nx\n\\end{frame}"))
  | .E0112 => dvE (dvDoc "\\titlegraphic{\\includegraphics{logo.png}}\n" "x")
  | .E0113 => dvE (dvDoc
      "\\renewcommand\\sectionlinesformat[4]{\\raisebox{-1pt}{#3}}\n" "x")
  | .E0201 => dvE "{a"
  | .E0202 => dvE "a}"
  | .E0205 => dvE "\\begin{ x"
  | .E0303 => dvE (dvDoc "\\define \\x(a b {y}\n" "x")
  | .E0304 => dvE (dvDoc "\\page\n" "x")
  | .E0305 => dvE (dvDoc "\\define \\role(who: text) {\\textbf{\\who}}\n" "\\role{$x$}")
  | .E0306 => dvE (dvDoc "\\define \\x(a?: text) {\\ifgiven{\\b}{y}}\n" "\\x{z}")
  | .E0309 => dvE "\\documentclass{proseplate}\n\\begin{document}\nx\n\\end{document}"
  | .E0310 => dvE (dvDoc "" "\\begin{itemize}\nstray\n\\item x\n\\end{itemize}")
  | .E0311 => dvE "a & b"
  | .E0312 => dvE "\\textbf{\\section{x}}"
  | .E0313 => dvE "\\documentclass{article}\nstray text\n\\begin{document}\nx\n\\end{document}"
  | .E0316 => dvE (dvDoc "\\define \\x(a?: text) {\\a}\n" "\\x[oops")
  | .E0320 => dvE (dvDoc "\\page{ oops }\n" "x")
  | .E0321 => dvE "\\includegraphics[scale=big]{x.png}"
  | .E0322 => dvE (dvDoc "\\page{ zoom = 3 }\n" "x")
  | .E0323 => dvE (dvDoc "\\page{ vmargin = \"x\" }\n" "x")
  | .E0324 => dvE (dvDoc "\\page{ size = quarto }\n" "x")
  | .E0325 => dvE (dvDoc "\\assert{ pages =~ 1 }\n" "x")
  | .E0326 => dvE (dvDoc "\\palette{ a = missingname }\n" "x")
  | .E0327 => dvE (dvDoc "\\page{ header = x }\n" "x")
  | .E0328 => dvE (dvDoc "\\style{banana}{ color = ink }\n" "x")
  | .E0329 => dvE (dvDoc "\\allow{W9999}\n" "x")
  | .E0330 =>
    (Check.one { pages := 2, fontsEmbedded := true }
      { kind := .pages .eq 1, span := none }).toArray
  | .E0331 => dvE "\\includegraphics[width=banana]{x.png}"
  | .E0332 => dvE (dvDoc "\\palette{covered = 100\\%}\n" "x")
  | .E0333 => dvE (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\fill (\\nope,0) rectangle (1,1);\n\\end{tikzpicture}"))
  | .E0336 => dvE (dvDoc "" "\\begin{banner}{Logo}\nx\n\\end{banner}")
  | .E0340 => dvE "\\faIcon{no-such-icon}"
  | .E0334 => dvE (dvDoc "" ("\\begin{ifbackend}{html}\\begin{ifbackend}{pdf}\n" ++
      "orphaned\n\\end{ifbackend}\\end{ifbackend}"))
  | .E0401 => #[DriverDiag.noFont]
  | .E0402 => probed .E0402
  | .E0403 => #[DriverDiag.familyMissing "Sourse Serif Pro" ["Source Serif Pro"] 0,
      DriverDiag.familyMissing "Kaputt Grotesk" [] 12]
  | .E0404 => #[DriverDiag.fontFileUnusable "fonts/Broken-Regular.otf"
      "not a TrueType or OpenType file"]
  | .E0405 => dvL mapped "lost \u27e8 here"
  | .E0501 => probed .E0501
  | .E0502 => probed .E0502
  | .E0503 => probed .E0503
  | .N0100 => dvE (dvDoc "\\usepackage[margin=1in]{geometry}\n" "x")
  | .N0102 => dvE (dvDeck "" "\\begin{frame}[fragile]{T}\nx\n\\end{frame}")
  | .N0103 => dvE (dvDoc "" "\\section[short]{A long title}\nx")
  | .N0104 => dvE (dvDeck ""
      "\\begin{frame}<presentation:0>[noframenumbering]{T}\nx\n\\end{frame}")
  | .N0114 =>
    dvE (dvDoc "\\ifdefined\\shiny\\sloppy\\else\\relax\\fi\n" "x") ++
    dvE (dvDoc "\\newcommand{\\shiny}{y}\\ifdefined\\shiny\\relax\\fi\n" "x")
  | .N0200 => dvL one (dvDoc "\\page{ height = 127pt, margin = 20pt }\n"
      "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc")
  | .N0016 => probed .N0016
  | .N0018 => dvL withMath "$\\mathcal{L} + \\mathsf{A}$"
  | .N0017 => (Elab.run "doc.tex" "A classless page, assumed article.").2
  | .N0019 => dvE (dvDoc "" "\\begin{ifbackend}{pdf}\nprint only\n\\end{ifbackend}")
  | .N0020 =>
    let sty := "\\AtBeginDocument{\\newgeometry{textwidth=5.5in}}\n\\def\\x#1,#2\\relax{#1}\n"
    let sraws := (Parse.parse "venueguide.sty" (Lex.lex "venueguide.sty" sty).1).1
    let draws := (Parse.parse "t" (Lex.lex "t" "\\usepackage{venueguide}\n").1).1
    let (raws, spliced) := Compat.applyLocalSty draws #[("venueguide", sraws)]
    let ds := (Elab.runRaws "t" raws).2
    spliced.map fun (s, src, p) => Compat.styRead (src.getD "t") s p ds
  | .N0021 => dvL one (dvDoc "\\page{ headsep = 20pt, footskip = 30pt }\n" "x")
  -- moloch's alert passes on its page and fails on its own frame-title
  -- bar: the pair realizes there (lighter, same hue), the note says so.
  | .N0022 => dvE (dvDeck "\\theme{moloch}\n"
      "\\begin{frame}{An \\alert{urgent} word}\nx\n\\end{frame}")
  | .W0368 => dvE (dvDoc "\\usepackage[klingon]{babel}\n" "x") ++
      dvE (dvDoc "\\pdfmeta{ language = \"xx\" }\n" "x")
  | .W0369 => dvE (dvDoc "\\babelfont[french]{rm}{Demo Serif}\n" "x")
  | .E0375 => dvE (dvDoc
      "\\newlength{\\half}\\setlength{\\half}{\\dimexpr\\textwidth/2\\relax}\n" "x")
  | .W0370 => dvE (dvDoc "" "a claim\\footnotemark stands here")
  | .W0371 => dvE (dvDoc "" "a\\footnote{first\n\nsecond}")
  | .W0372 => dvL one (dvDoc "\\page{ width = 120pt, height = 150pt, margin = 20pt }\n"
      ("x\\footnote{" ++ String.intercalate " " (List.replicate 60 "wow") ++ "}"))
  | .W0373 => dvE (dvDoc "\\title{An Invented Panel\\thanks{Synthetic Grant 1}}\n"
      "x\n\\maketitle")
  | .W0374 => dvE ("\\documentclass{card}\n\\begin{document}\n" ++
      "x\\footnote{an aside}\n\\end{document}")
  | .W0376 => dvE (dvDoc "" "\\includegraphics{chart.png}") ++
      Ir.picAltDiags (elabStr (dvDoc "\\pictures{ tool = lualatex }\n"
          "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}")).1
        (fun _ => none) (fun _ => true)
  | .W0377 => dvE (dvDoc "" "\\href{https://example.org/x}{}")
  | .W0381 => dvE (dvDoc "" "\\qty{9.81}{\\banana}")
  | .W0001 => dvE (dvDoc "" "x\n\\end{document}\nleft over")
  | .W0003 => dvL one (dvDoc "" "$x^2$")
  | .W0005 => dvL one (dvDoc "\\page{ width = 60pt, margin = 10pt, justify = on }\n"
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")
  | .W0006 =>
    let face : FontDb.Face := { path := "fonts/DemoSerif-Regular.otf"
                                family := "Demo Serif"
                                subfamily := "Regular"
                                bold := false
                                italic := false
                                fixedPitch := false
                                weight := 400 }
    let ask (declared : Option String) : Array Diag :=
      match FontDb.resolveVariant #[face] "Demo Serif" declared { bold := true } with
      | some (_, some sub) => #[DriverDiag.substituted sub]
      | _ => #[]
    ask none ++ ask (some "DemoSerif-Bold.otf")
  | .W0007 => dvH (dvDoc "\\runninghead{name}\n" "x")
  | .W0008 => probed .W0008
  | .W0009 => dvL mapped "for all is \u2200 set"
  | .W0010 => dvL one (dvDoc "" (String.join
      ((List.range 5).map fun _ => "\\begin{itemize}\\item x\n") ++
      String.join ((List.range 5).map fun _ => "\\end{itemize}\n")))
  | .W0011 => probed .W0011
  | .W0012 =>
    dvE "$\\overset{?}{=}$" ++
    -- the empty-salvage wording: markup and symbol commands end to end, so
    -- the floor is the declared placeholder and the warning says so
    dvE "$\\overset{\\alpha}{\\beta}$"
  | .W0013 => #[DriverDiag.allowUnfired "E0333"]
  | .W0014 => dvE "\\begin{align*}a &= b \\\\ c\\end{align*}"
  | .W0015 => dvE "\\begin{align}a &= b\\end{align}"
  | .W0101 => dvE (dvDoc "\\usepackage[voffset=1in]{geometry}\n" "x")
  | .W0102 => dvE (dvDoc "\\definecolor{c}{hsb}{0.5,0.5,0.5}\n" "x")
  | .W0103 => dvE (dvDoc "\\usepackage{nosuchpkg}\n" "x")
  | .W0104 => dvE (dvDoc (String.intercalate "\n"
      ["\\directlua{tex.print('x')}", "\\raggedright",
       "\\sloppy", "\\selectlanguage{german}", "\\pagestyle{headings}",
       "\\ifx\\x\\y\\fi", "\\usecolortheme{dove}",
       "\\setbeamercovered{transparent}", "\\titlegraphic{}"] ++ "\n") "x")
  | .W0105 => dvE "\\uncover<zz>{x}"
  | .W0106 => dvE (dvDoc "\\ExplSyntaxOn \\cs_new:Npn \\x { } \\ExplSyntaxOff\n" "x")
  | .W0108 => dvE "\\textbf{\\centering x}"
  | .W0110 => dvE "\\includegraphics[angle=45]{x.png}"
  | .W0111 => dvE (dvDoc "\\setkomafont{banana}{\\bfseries}\n" "x")
  | .W0201 => dvL one (dvDoc "\\page{ hmargin = 1in }\n"
      (String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")))
  | .W0202 => dvL one (dvDoc "\\style{section}{ before = 2pt, after = 10pt }\n"
      "\\section{a}\nbody")
  | .W0301 => dvE "\\mystery{x}"
  | .W0307 => dvE (dvDoc "" "\\begin{external}\nx\n\\end{external}")
  | .W0302 => dvE (dvDoc "" "\\begin{banner}\nx\n\\end{banner}")
  | .W0303 => dvE (dvDoc "\\define \\underline(a: content) {\\a}\n" "x")
  | .W0304 => dvE "\\textcolor{nope}{x}"
  | .W0309 => dvE (dvDoc "" "\\maketitle")
  | .W0310 => dvE (dvDoc "" "\\section[oops\nnever closed")
  | .W0311 => dvE (dvDeck "" ("\\begin{frame}\n\\frametitle{One}\n" ++
      "\\frametitle{Two}\nx\n\\end{frame}"))
  | .W0312 => dvE "\\title[never closes\n\\begin{document}\nx\n\\end{document}"
  | .W0314 => dvE (dvDeck "" ("\\begin{frame}{T}\\begin{columns}\n" ++
      "\\begin{column}{banana}\nx\n\\end{column}\n\\end{columns}\\end{frame}"))
  -- An anonymous mix is not a role, so it never realizes: the pairing
  -- warning is its own (a role-named failing pair realizes and is N0022).
  | .W0315 => dvE (dvDoc "" "\\textcolor{black!20}{faint}")
  | .W0316 => dvE (dvDoc "\\palette[dark]{ a = #101010 }\n" "x")
  | .W0317 => dvE ("\\documentclass{card}\n\\runninghead{name}\n" ++
      "\\begin{document}\nx\n\\end{document}")
  | .W0318 => dvE (dvDoc "\\chrome{ footer = { left = \\sectiontitle } }\n" "x")
  | .W0319 => dvE (dvDoc "\\theme{banana}\n" "x")
  | .W0320 => dvE (dvDoc "" "\\section{a}\n\n\\subsubsection{b}\nx")
  | .W0321 => dvE (dvDoc "\\title{T}\n" "\\section{a}\nx\n\n\\maketitle")
  | .W0322 => dvE (dvDoc "\\title{T}\n" "\\maketitle\n\n\\maketitle")
  | .W0323 => dvE (dvDoc "" "\\begin{ifbackend}{banana}\nx\n\\end{ifbackend}")
  | .W0325 => dvH (dvDoc "" ("\\begin{nav}\\link{#a}{A}\\end{nav}\n\n" ++
      "\\begin{nav}\\link{#b}{B}\\end{nav}\n\n\\section{a}\nx"))
  | .W0326 => dvH (dvDoc "" "\\link{#nowhere}{dead}")
  | .W0327 => dvH (dvDoc "" "\\section{Signal Path}\nx\n\n\\section{Signal, Path}\ny")
  | .W0328 => dvL one (dvDoc
      (s!"\\runningfoot\{{String.intercalate " " (List.replicate 40 "an overlong footer")}}\n")
      "x")
  | .W0329 => dvE (dvDoc "\\fontfallback{x}\n" "x")
  | .W0330 => dvE (dvDoc "\\palette{ bg = #18181B }\n" "x")
  | .W0331 => dvH (dvDoc
      "\\style{itemize}{ marker = {\\includegraphics{rects.png}} }\n"
      "\\begin{itemize}\n\\item a\n\\end{itemize}")
  | .W0348 => dvE (dvDeck "\\palette{ alert = #112233 }\n\\theme{moloch}\n"
      "\\begin{frame}{T}\nx\n\\end{frame}")
  | .W0354 => dvE (dvDoc
      "\\usepackage[tableposition=top]{caption}\n\\captionsetup[table]{labelfont=bf}\n" "x")
  | .W0355 => dvE (dvDoc "\\theme{moloch}\n" "x")
  | .W0351 => dvBib "@misc{real, year = 2024}" "ghost" none ++
      dvE (dvDoc "" "x \\cite{ghost}")
  | .W0352 => dvBib "@misc{broken, year = ?}\n@misc{kept, year = 2024}" "kept" none
  | .W0353 => dvBib "@misc{k, year = 2024}" "k" (some "mystery")
  | .W0332 => dvE (dvDeck "\\theme{moloch}\n"
      "\\framefoot{p. \\pagenumber}\n\\begin{frame}{T}\nx\n\\end{frame}")
  | .W0333 => dvL one (dvDeck "\\theme{moloch}\\title{T}\\author{A}\n"
      (s!"\\maketitle\n\\framefoot\{{String.ofList (List.replicate 100 '0')}}\n" ++
       "\\begin{frame}{F}\nx\n\\end{frame}"))
  | .W0334 => dvE (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\draw (0,0) circle (1);\n\\end{tikzpicture}"))
  | .W0335 => dvL one (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\fill (0,0) rectangle (40,1);\n\\end{tikzpicture}"))
  -- Two nodes one node distance apart by their centres, each label wider
  -- than that: the collision the picture's own box cannot show, because
  -- the box contains both labels correctly.
  | .W0336 => dvL one (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\node (a) {A Wide Enough Label};\n" ++
      "\\node (b) [right =of a] {Another Wide Label};\n\\end{tikzpicture}"))
  | .W0337 => dvE (dvDoc "" "\\begin{tabular}{ll}\na & b & c \\\\\nd \\\\\n\\end{tabular}")
  | .W0338 => dvL one (dvDoc "" ("\\begin{tabular}{p{0.8\\linewidth}p{0.8\\linewidth}}\n" ++
      "a & b \\\\\n\\end{tabular}"))
  -- A frame taller than its page with no [allowframebreaks]: the layout
  -- closes the page mid-frame and the account fires once, naming the frame.
  | .W0384 => dvL one (dvDeck "\\theme{moloch}\n"
      ("\\begin{frame}{Too tall}\n" ++
       String.join (List.replicate 30 "one line\n\n") ++ "\\end{frame}"))
  -- A colour and a font change inside math: the formula renders, the
  -- presentation does not, because a math list carries neither.
  | .W0385 =>
    dvE "$\\textcolor{indigo}{x}$" ++ dvE "$\\text{\\textbf{bold} word}$"
  -- A title whose author declared two lines and whose first does not fit
  -- the measure: the breaker finds a legal break inside the declared line,
  -- so a third line ships and its remainder returns to the flush-left
  -- margin. No line is overfull, so W0005 has nothing to say.
  | .W0386 => dvL one (dvDoc
      ("\\page{ width = 220pt, margin = 20pt }\n" ++
       "\\title{Coordinating Placeholder Schedules\\\\A Second Declared Line}\n")
      "\\maketitle")
  | .W0358 => dvL one (dvDoc "\\page{ size = a5 }\n"
      ("\\begin{table}\n\\begin{tabular}{l}\n" ++
       String.join (List.replicate 60 "alpha \\\\\n") ++
       "\\end{tabular}\n\\caption{Below the table}\n\\end{table}"))
  | .W0340 =>
    dvE (dvDoc "" "x\n\n\\page{ size = a5 }\n\ny") ++
    dvE (dvDoc "" "x\n\n\\usepackage{pgfplots}\n\ny")
  | .W0341 => dvE "\\textls[16]{spaced}.example.org"
  | .W0342 => dvE (dvDoc "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n"
      "\\muted{x}")
  | .W0343 =>
    dvE (dvDoc "\\page{ margin = 20pt }\n\\page{ margin = 30pt }\n" "x") ++
    dvE (dvDoc "\\runningfoot{one}\n\\runningfoot{two}\n" "x")
  -- The text pairs (frame title, standout) now realize (N0022 carries
  -- them); the covering judge has no lightness to choose — a cover is a
  -- relation between two states — so it keeps W0345.
  | .W0345 =>
    dvE (dvDeck "\\palette{ covered = #000000 }\n"
      "\\begin{frame}{T}\n\\uncover<2>{x}\n\\end{frame}")
  | .W0346 =>
    dvE (dvDoc "" "a {\\palette{ q = #112233 } b} c") ++
    dvE (dvDoc "" "\\textbf{\\page{ size = a5 } x}")
  | .E0347 =>
    dvE (dvDoc "" "\\runninghead{Chapter One}\n\nx") ++
    dvE (dvDoc "" "\\textbf{\\runningfoot{Y} z}")
  | .E0359 => dvE (dvDeck ""
      "\\note{\\begin{frame}{Carried}\nspoken \\note{never carried} words\n\\end{frame}}")
  | .W0601 => #[Image.imageMissing "figures/plot.png" "/documents/figures/plot.png",
      Image.imageUnreadable "figures/plot.png" "permission denied (error code: 13)"]
  | .W0362 => dvE (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\shade (0,0) rectangle (1,1);\n\\end{tikzpicture}"))
  | .W0602 => #[Image.imageUndecodable "figures/plot.gif"
      "not a PNG, JPEG, or PDF file"]
  -- The two ledger entries a plan can carry (`Image.plan_losses_accounts`),
  -- as the driver names them after `Image.fulfil`.
  | .W0603 => #[Image.imageIccDropped "figures/plot.png"]
  | .W0604 => #[Image.imageOrientationDropped "figures/photo.jpg" 6]
  -- The boundary is open by default: no declaration, and the picture
  -- routes; the trust label names it.
  | .N0023 => dvE (dvDoc ""
      "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}")
  | .W0383 => dvE (dvDoc ""
      "\\begin{algorithm}\n\\lIf{$x < 0$}{negate $x$}\\;\n\\end{algorithm}")
  | .W0387 => dvE (dvDoc "\\thispagestyle{plain}\n" "x")
  -- W0701 is the driver's: the declared contract held against the
  -- realization record of each artifact the run emits.
  | .W0701 =>
    let (doc, _) := elabStr (dvDoc "\\output{ formats = pdf, alternatives = required }\n" "x")
    Ir.contractDiags (doc.output.contract.unmet Pdf.profile)
  -- W0379 is the driver's: a stated request no available tool can fulfil.
  | .W0379 => probed .W0379
  -- E0382 is the driver's too: the tool ran and drew nothing, a dropped
  -- loss, so the run fails unless the document declares acceptance.
  | .E0382 => #[DriverDiag.boundaryFailed "lualatex"
      "! Undefined control sequence. · l.7 \\nope"]
  | .W0378 => #[DriverDiag.boundarySvgMissing "not found (error code: 2)"]
  | .W0349 => dvE "\\ref{nowhere}"
  | .W0350 => dvE "\\section{A}\\label{twice}\\label{twice}"
  | .W0380 => dvE "\\refstepcounter{section}\n\\label{stepped} see \\cref{stepped}"
  | .W0356 =>
    dvE "\\documentclass[twocolumn]{article}\n\\begin{document}\nx\n\\end{document}" ++
    dvE "\\documentclass[draft]{article}\n\\begin{document}\nx\n\\end{document}"
  | .W0367 =>
    dvE ("\\documentclass{beamer}\n\\usepackage[debug,size=a1]{beamerposter}\n" ++
      "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")
  | .W0357 =>
    dvE (dvDoc "\\edef\\x{y}\n" "x") ++
    dvE (dvDoc "\\def\\pair#1.#2{#1 and #2}\n" "x")
  | .W0361 =>
    dvE (dvDoc "\\title{T}\\newcommand{\\maketitle}{\\venuetitlebox}\n" "\\maketitle")
  | .W0364 =>
    dvData ("\\data{ @job{a, role = {X}, start = 2020} " ++
        "@job{b, role = {Y}, start = 2021, end = 2024} }\n" ++
      "\\begin{foreach}{j}{job}\\val{j.end}\\end{foreach}") ++
    dvData "\\data{ @job{a, role = {X}} }\\val{k.role}" ++
    dvData "\\data{ @job{a, role = {X}} }\\begin{foreach}{j}{trip}\\val{j.role}\\end{foreach}"
  | .E0365 => probed .E0365
  | .W0366 =>
    let mk (sub : String) (w : Nat) : FontDb.Face :=
      { path := s!"fonts/DemoSans-{sub}.otf", family := "Demo Sans"
        subfamily := sub, bold := w ≥ 600, italic := false
        fixedPitch := false, weight := w }
    let faces := #[mk "Regular" 400, mk "Bold" 700]
    let ask (family : String) (declared : Option String) : Array Diag :=
      match FontDb.resolveVariant faces family declared {} with
      | some (_, some sub) => #[DriverDiag.substituted sub]
      | _ => #[]
    -- The weighted family name and the declared weighted face, each with
    -- no such weight installed: the nearest weight answers, named.
    ask "Demo Sans Light" none ++ ask "Demo Sans" (some "Demo Sans Medium")

/-! The message lint: every fired message and help is judged mechanically.
Each check exists because the pasted real output violated it (the brief's
four defects); the golden covers what these cannot — tone, jargon, whether
a help actually helps. -/

/-- A reference only someone inside this repository can follow: a repo file,
a source path, or a milestone token (`M6`, `M8`). A diagnostic must be
actionable by someone holding only their own document. -/
def dvInternalRef (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "PLAN.md" || has "AGENTS.md" || has "LeanTex/" || has ".lean" ||
    (Id.run do
      let cs := s.toList.toArray
      for i in [0:cs.size] do
        if cs[i]! == 'M' && (cs[i+1]?.map Char.isDigit).getD false &&
            !((i > 0) && (cs[i-1]!.isAlphanum || cs[i-1]! == '_')) &&
            !(((cs[i+2]?.map (·.isAlphanum)).getD false)) then
          return true
      return false)

/-- A help either tells the reader what to write — a `\` spelling, a flag,
a `key = value`, a quoted literal, a backticked command, or a `:`-led
enumeration of the known values — or it should not exist. -/
def dvHasAction (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "\\" || has "--" || has "`" || has "=" || has ": " || has "{" ||
    (s.toList.filter (· == '\'')).length ≥ 2

/-- Message and help bounds, in characters, taken from the two longest
texts that read well rather than from a round number: the message bound is
W0315's fired message (121 characters, one clause with the ratio, the
threshold, and the source), the help bound E0322's list of every advertised
page key (187 characters, generated from `pageKeys`, decided again when the
cut-mark and line-number keys joined it; E0328's styleable-element list
stands at 181 beneath it; growing either list means deciding this bound
again). -/
def dvMsgMax : Nat := 121
def dvHelpMax : Nat := 187

/-- Sentence case: a message opens lowercase (or with a quoted construct)
unless its first word is a proper noun the engine speaks of. -/
def dvCaseOk (s : String) : Bool :=
  match s.toList with
  | [] => true
  | c :: _ =>
    !c.isUpper ||
      ["TeX", "LaTeX", "LEANTEX_FONT", "PNG", "JPEG", "WCAG", "HTML",
       "U+"].any (s.startsWith ·)

/-- One convention for terminal punctuation: none (a `?` may close a real
question). -/
def dvTerminalOk (s : String) : Bool :=
  !(s.endsWith "." || s.endsWith "!")

/-- Code-shaped tokens in prose: a reader cannot look a code up, so a
message or help may name only the code it is itself printed under. -/
def dvForeignCodes (own : String) (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut tok := ""
  for c in s.toList ++ [' '] do
    if c.isAlphanum then
      tok := tok.push c
    else
      if isDiagCode tok && tok != own && !out.contains tok then
        out := tok :: out
      tok := ""
  return out

/-- The lint over one fired diagnostic. `\allow`-teeth codes (W0013, E0329)
quote codes the user wrote in their own document, so the foreign-code check
does not apply to them. -/
def dvLint (fail : String → IO Unit) (d : Diag) : IO Unit := do
  let judge (part : String) (s : String) : IO Unit := do
    if dvInternalRef s then
      fail s!"{d.code} {part}: repo-internal reference: {s}"
    unless dvTerminalOk s do
      fail s!"{d.code} {part}: terminal punctuation: {s}"
    unless dvCaseOk s do
      fail s!"{d.code} {part}: starts uppercase without a proper noun: {s}"
    if (s.splitOn "\"\\").length > 1 then
      fail s!"{d.code} {part}: a construct is double-quoted; the convention is '...': {s}"
    unless d.code == "W0013" || d.code == "E0329" do
      for tok in dvForeignCodes d.code s do
        fail s!"{d.code} {part}: names {tok}, which the reader cannot look up: {s}"
  judge "message" d.message
  if d.message.startsWith "\\" then
    fail s!"{d.code} message: the construct it names is unquoted: {d.message}"
  unless d.message.length ≤ dvMsgMax do
    fail s!"{d.code} message: {d.message.length} chars, over {dvMsgMax}: {d.message}"
  if let some h := d.help then
    judge "help" h
    unless dvHasAction h do
      fail s!"{d.code} help: no action — nothing to write, no flag, no known values: {h}"
    unless h.length ≤ dvHelpMax do
      fail s!"{d.code} help: {h.length} chars, over {dvHelpMax}: {h}"

/-- A rendered diagnostics dump as code-keyed blocks, split on `── ` line
starts — the compare and the update both go through this one parse, so the
two cannot disagree about where a block begins. -/
def diagBlocksOf (s : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut key := ""
  let mut cur := ""
  for line in s.splitOn "\n" do
    if line.startsWith "── " then
      if !key.isEmpty then out := out.push (key, cur)
      key := (((line.drop "── ".length).toString).splitOn " ").headD ""
      cur := line ++ "\n"
    else if !key.isEmpty && !line.isEmpty then
      cur := cur ++ line ++ "\n"
  if !key.isEmpty then out := out.push (key, cur)
  return out

/-- The voice golden and its coverage: every registered code fires from its
witness, and every fired form renders into tests/golden/diagnostics.txt —
the one place the whole voice is reviewable in a diff. The driver probes run
first, before the font gate can skip anything: each has to fire its own code
from the driver's own return, which is what makes a probed code's witness
evidence that the code can still fire. Spans are dropped: the witnesses'
line numbers are noise. The file is one block per code, sorted by code on
emission, so an added code is a one-block insertion at its sorted position
and two additions to different codes never touch the same lines; the compare
is per block, so a mismatch names its code. -/
def diagVoiceChecks (ref : IO.Ref (List String)) (update : Bool) : IO Unit := do
  let probed ← runDriverProbes
  for (c, ds) in probed do
    check ref s!"driver probe {c.code}: one row per code"
      ((driverProbes.filter (·.1 == c)).size == 1)
    check ref s!"driver probe {c.code}: the driver path still emits it"
      (ds.any (·.code == c.code))
  let probeOf (c : DiagCode) : Array Diag :=
    ((probed.find? (·.1 == c)).map (·.2)).getD #[]
  let load (name : String) : IO (Option Font.Font) := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure (some f)
    | .error _ => pure none
  let some sans ← load "OpenSans-Regular.ttf"
    | failures ref "diag voice: OpenSans-Regular.ttf missing"; return
  let some code ← load "SourceCodePro-Regular.otf"
    | failures ref "diag voice: SourceCodePro-Regular.otf missing"; return
  let allVariants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let one : Font.FontSet := {
    fonts := #[sans]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let mapped : Font.FontSet := {
    fonts := #[sans, code]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 1).toArray
    fallback := #[('\u2200', 1)] }
  let some fira ← load "FiraMath-Regular.otf"
    | failures ref "diag voice: FiraMath-Regular.otf missing"; return
  let withMath : Font.FontSet := {
    fonts := #[sans, fira]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray
    math := some 1 }
  let lossLabel : Loss → String
    | .dropped => "dropped"
    | .pending => "pending"
    | .degraded => "degraded"
    | .config => "config"
    | .info => "info"
  let mut blocks : Array (String × String) := #[]
  for c in DiagCode.all do
    let fired := (diagWitness one mapped withMath probeOf c).filter (·.code == c.code)
    check ref s!"diag voice {c.code}: the witness fires it" (!fired.isEmpty)
    -- The registry meaning is prose too: self-contained, one convention.
    if dvInternalRef c.meaning then
      failures ref s!"diag voice {c.code} meaning: repo-internal reference: {c.meaning}"
    unless dvTerminalOk c.meaning do
      failures ref s!"diag voice {c.code} meaning: terminal punctuation: {c.meaning}"
    let mut block := s!"── {c.code} ({lossLabel c.loss}) {c.meaning}\n"
    let mut seen : Array String := #[]
    for d in fired do
      dvLint (fun m => failures ref s!"diag voice {m}") d
      let r := Render.human false { d with span := none }
      unless seen.contains r do
        seen := seen.push r
        block := block ++ r ++ "\n"
    blocks := blocks.push (c.code, block)
  let sorted := blocks.qsort (fun a b => a.1 < b.1)
  let out := sorted.foldl (fun acc b => acc ++ b.2) ""
  let path := "tests/golden/diagnostics.txt"
  if update then
    IO.FS.writeFile path out
    IO.println s!"updated {path}"
  else
    let golden ← try pure (some (← IO.FS.readFile path)) catch _ => pure none
    match golden with
    | none => failures ref s!"diag voice: missing {path} (run: lake exe Tests --update)"
    | some g =>
      let gBlocks := diagBlocksOf g
      let mut gKeys : Array String := #[]
      for (k, _) in gBlocks do
        if gKeys.contains k then
          failures ref s!"diag voice: duplicate golden block {k} (a mis-merge; run: lake exe Tests --update)"
        gKeys := gKeys.push k
      for (k, b) in diagBlocksOf out do
        match gBlocks.find? (·.1 == k) with
        | none =>
          failures ref s!"diag voice: golden lacks a block for {k} (run: lake exe Tests --update)"
        | some (_, gb) =>
          unless gb == b do
            failures ref s!"diag voice {k}: block mismatch, {firstDiff gb b} \
(if intended, run: lake exe Tests --update)"
      for (k, _) in gBlocks do
        unless sorted.any (·.1 == k) do
          failures ref s!"diag voice: stale golden block {k}, no longer registered \
(run: lake exe Tests --update)"
      unless g == out do
        if gBlocks.qsort (fun a b => a.1 < b.1) == diagBlocksOf out then
          failures ref s!"diag voice: golden differs only in block order or spacing \
(run: lake exe Tests --update)"

/-- The `\allow` escape hatch: declared acceptance of named losses, with its
three teeth — an unknown code is an error, a never-fired entry warns
(`Diag.unfired`, applied in the driver), and the acceptance prints. -/
def allowChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (pre : String) : String :=
    pre ++ "\n\\begin{document}\nx\n\\end{document}"
  t "allow stores its codes on the document"
    ((elabStr (doc "\\allow{W0307, E0502}")).1.allow == #["W0307", "E0502"])
  t "allow dedupes a repeated code"
    ((elabStr (doc "\\allow{W0307}\\allow{W0307}")).1.allow == #["W0307"])
  t "allow with an unknown code is an error"
    (errCodes (doc "\\allow{W9999}") == ["E0329"])
  t "allow dumps as a declaration"
    (((Ir.dump (elabStr (doc "\\allow{W0307}")).1 #[]).splitOn "allow W0307").length == 2) -- ir tier: the dump's own feature under test
  -- The total function severity resolution is: an allowed error or warning
  -- becomes a note — a declared document emits nothing at default
  -- verbosity — and the acceptance summary is what keeps it visible.
  let e := Diag.of .E0501 "gone"
  let w := Diag.of .W0338 "wide"
  t "accept downgrades an allowed error to a note, changing nothing else"
    (let (d, acc) := Diag.accept #["E0501"] false e
     acc && d.severity == .note && d.code == e.code && d.message == e.message
       && d.span == e.span && d.help == e.help)
  t "accept downgrades an allowed warning to a note"
    (let (d, acc) := Diag.accept #["W0338"] false w
     acc && d.severity == .note && d.code == w.code)
  t "accept leaves an unallowed error alone"
    (Diag.accept #["W0307"] false e == (e, false))
  t "accept leaves an unallowed warning alone"
    (Diag.accept #["E0501"] false w == (w, false))
  t "best-effort accepts every error and warning"
    (let (de, accE) := Diag.accept #[] true e
     let (dw, accW) := Diag.accept #[] true w
     accE && de.severity == .note && accW && dw.severity == .note)
  t "accept never touches a note"
    (let n := Diag.of .N0100 "idiom"
     Diag.accept #["N0100"] true n == (n, false))
  t "unfired names the stale entries only"
    (Diag.unfired #["W0307", "W0338"] #["W0338", "W0338"] == #["W0307"])
  t "accepted losses line prints codes with counts"
    (Render.humanAccepted false [("W0307", 2), ("E0502", 1)] ==
      "accepted: 3 losses (W0307 ×2, E0502)")

/-- The `--werror` exit-code matrix, over the same functions the driver
runs: diagnostics from a real elaboration are resolved against the
document's own `\allow`, and `exitFor` reads the counts. The contract:
errors are 1, failed assertions 2, and a warning is 1 only under the flag —
where an accepted loss is not a warning, which is the whole point of
accepting it. -/
def werrorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "args --werror parses" ((parse ["a.tex", "--werror"]).map (·.werror) == .ok true)
  t "args werror defaults off" ((parse ["a.tex"]).map (·.werror) == .ok false)
  let resolve (src : String) : Resolution :=
    let (doc, ds) := elabStr src
    Diag.resolveAll doc.allow false ds
  let clean := resolve "\\begin{document}\nx\n\\end{document}"
  let warned := resolve "\\sloppy\n\\begin{document}\nx\n\\end{document}"
  let allowed := resolve "\\allow{W0104}\n\\sloppy\n\\begin{document}\nx\n\\end{document}"
  t "matrix: clean document is 0 without the flag"
    (exitFor clean.errors 0 clean.warnings false == 0)
  t "matrix: clean document is 0 with the flag"
    (clean.warnings == 0 && exitFor clean.errors 0 clean.warnings true == 0)
  t "matrix: a warning is 0 without the flag"
    (warned.warnings > 0 && exitFor warned.errors 0 warned.warnings false == 0)
  t "matrix: a warning is 1 with the flag"
    (exitFor warned.errors 0 warned.warnings true == 1)
  t "matrix: an allowed loss is 0 without the flag"
    (exitFor allowed.errors 0 allowed.warnings false == 0)
  t "matrix: an allowed loss is 0 with the flag — acceptance composes"
    (allowed.warnings == 0 && allowed.accepted == #["W0104"] &&
      exitFor allowed.errors 0 allowed.warnings true == 0)
  t "matrix: an error is 1 whatever the flag"
    (exitFor 1 0 0 false == 1 && exitFor 1 0 0 true == 1)
  t "matrix: a failed assertion is 2, warnings or not"
    (exitFor 0 1 3 true == 2 && exitFor 0 1 0 false == 2)
  t "werror verdict line names the count and the flag"
    (Render.humanWerror false "a.tex" 3 17 == "✖ a.tex — 3 warnings (--werror) (17 ms)")
  t "werror porcelain summary is not ok and counts warnings"
    (Render.porcelainWerror "a.tex" 3 17 ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":0," ++
      "\"warnings\":3,\"ms\":17}")


/-- The accessibility contract's judge sites. The alt judge (W0376, WCAG
2.2 SC 1.1.1): fires on an image with no text alternative, silenced by
each declared escape — an `alt` option, a figure caption (which becomes
the alt at elaboration). The AA assertion surface: `\assert{ accessibility
= AA }` turns the judged facts into one named failing assertion (exit 2's
E0330), holds when nothing failed, and reads facts before `\allow`
resolution. Each check breaks its judge once, the AssertKind row's own
obligation. -/
def a11yChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- W0376 fires and is silenced by each escape.
  t "an image with no text alternative fires W0376"
    ((dvE (dvDoc "" "\\includegraphics{chart.png}")).any (·.code == "W0376"))
  t "a declared alt silences W0376"
    (((dvE (dvDoc "" "\\includegraphics[alt={A synthetic chart}]{chart.png}")).any
      (·.code == "W0376")) == false)
  t "a figure caption becomes the alternative and silences W0376"
    (((dvE (dvDoc "" ("\\begin{figure}\\includegraphics{chart.png}" ++
        "\\caption{A synthetic chart}\\end{figure}"))).any
      (·.code == "W0376")) == false)
  -- A boundary picture routed by the open default is in the census — the
  -- default route changes who drew the box, not what the accessibility
  -- tree gets — carries its trust note, and is left to the driver's face
  -- (`picAltDiags`, judged once shipped), never named at elaboration.
  let (routed, routedDs) := elabStr (dvDoc ""
    "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}")
  t "a default-routed boundary picture is counted, noted, and left to the driver's judge"
    ((Ir.imagesSansAlt routed).size == 1 &&
     routedDs.all (·.code != "W0376") && routedDs.any (·.code == "N0023"))
  -- The theorem's executable face: the judge and the census agree on the
  -- offender.
  let (bare, _) := elabStr (dvDoc "" "\\includegraphics{chart.png}")
  t "imagesSansAlt names the offending source"
    (Ir.imagesSansAlt bare == #["chart.png"])
  t "alt_judged_complete's face: judge silent iff census empty"
    ((Ir.altDiags bare).isEmpty == (Ir.imagesSansAlt bare).isEmpty &&
      !(Ir.altDiags bare).isEmpty)
  t "the judge names the image's own line"
    ((dvE (dvDoc "" "\\includegraphics{chart.png}")).any fun d =>
      d.code == "W0376" && d.span == some ⟨"t", ⟨3, 1⟩⟩)
  -- The picture face: judged by the driver after fulfilment, in the
  -- author's words (the source spelling is the engine's cache key).
  let door := "\\pictures{ tool = lualatex }\n"
  let pic := "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}"
  let (picDoc, picDs) := elabStr (dvDoc door pic)
  t "elaboration leaves a boundary picture to the driver's judge"
    (picDs.all (·.code != "W0376"))
  let firedPic := Ir.picAltDiags picDoc (fun _ => none) (fun _ => true)
  t "a shipped picture with no alternative fires W0376 in the author's words"
    (firedPic.size == 1 && firedPic.all fun d =>
      (d.message.splitOn "picture").length == 2 &&
      (d.message.splitOn Ir.picSrcPrefix).length == 1)
  t "a picture the tool failed on is not double-named (E0382 spoke)"
    ((Ir.picAltDiags picDoc (fun _ => none) (fun _ => false)).isEmpty)
  t "a captioned figure around the picture silences the picture face"
    ((Ir.picAltDiags (elabStr (dvDoc door ("\\begin{figure}" ++ pic ++
        "\\caption{A synthetic diagram}\\end{figure}"))).1
      (fun _ => none) (fun _ => true)).isEmpty)
  -- W0377 (WCAG 2.2 SC 2.4.4) fires on a link with no reading and is
  -- silenced by each escape: link text, or an image alternative inside.
  t "a link with no text fires W0377"
    ((dvE (dvDoc "" "\\href{https://example.org/x}{}")).any (·.code == "W0377"))
  t "link text silences W0377"
    (((dvE (dvDoc "" "\\href{https://example.org/x}{example}")).any
      (·.code == "W0377")) == false)
  t "an image with alt inside the link silences W0377"
    (((dvE (dvDoc "" ("\\href{https://example.org/x}" ++
        "{\\includegraphics[alt={A synthetic chart}]{chart.png}}"))).any
      (·.code == "W0377")) == false)
  let (bareLink, _) := elabStr (dvDoc "" "\\href{https://example.org/x}{}")
  t "linksSansText names the offending target"
    (Ir.linksSansText bareLink == #["https://example.org/x"])
  t "links_judged_complete's face: judge silent iff census empty"
    ((Ir.linkDiags bareLink).isEmpty == (Ir.linksSansText bareLink).isEmpty &&
      !(Ir.linkDiags bareLink).isEmpty)
  -- headings_no_skip_judged's executable face: the fact and the fired
  -- code travel together.
  let (gapped, gds) := elabStr (dvDoc ""
    "\\section{One}\nx\n\\subsubsection{Deep}\ny")
  t "outlineHasSkip names the fact W0320 fires on"
    (Ir.outlineHasSkip gapped && gds.any (·.code == "W0320"))
  -- The AA assertion: parse, fail on a judged fact, hold when clean.
  let (failing, fds) := elabStr (dvDoc "\\assert{ accessibility = AA }\n"
    "\\includegraphics{chart.png}")
  t "accessibility = AA parses to its kind"
    (failing.asserts.any (·.kind == Ir.AssertKind.accessibilityAA))
  let shippedOf (doc : Ir.Doc) (ds : Array Diag) : Check.Shipped :=
    { pages := 1, fontsEmbedded := true, a11y := Check.a11ySummary doc ds }
  t "AA fails on a judged fact, naming the assertion"
    ((Check.all (shippedOf failing fds) failing.asserts).size == 1 &&
      (Check.all (shippedOf failing fds) failing.asserts).all
        (·.message.startsWith "assertion failed: accessibility = AA"))
  let (clean, cds) := elabStr (dvDoc
    ("\\assert{ accessibility = AA }\n" ++
      "\\pdfmeta{ language = \"en\" }\n") "plain text")
  t "AA holds on a clean document with a declared language"
    ((Check.all (shippedOf clean cds) clean.asserts).isEmpty)
  -- The one non-diagnostic row: an undeclared language fails AA even on
  -- an otherwise clean document (SC 3.1.1: the declaration is the fact).
  let (nolang, nds) := elabStr (dvDoc "\\assert{ accessibility = AA }\n"
    "plain text")
  t "AA fails without a declared language"
    (!(Check.all (shippedOf nolang nds) nolang.asserts).isEmpty)

/-- The resolution gate, run: a document with one of each unresolved kind —
a `\ref` no label numbers, a `\cite` with no bibliography (and, in a
second document, one with a bibliography the key is absent from), an
`\includegraphics` no file answers, and a boundary picture the tool failed
on. `Ir.pending` lists what a backend would ship as `??`, `?`, or a
placeholder box; every element has a diagnostic whose subject names it
(`pending_named`, executed), no `.cite` survives `Bib.apply`
(`apply_no_cite`, executed), and the store covers every requested source
(`fulfil_covers`). The synthetic document's rendered diagnostics are the
renders in the slice report. -/
def pendingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pic := "\\begin{tikzpicture}\\draw (0,0) circle (1);\\end{tikzpicture}"
  let body := "See \\ref{none} and \\cite{none}.\n\n\\includegraphics{absent.png}\n\n" ++ pic
  let (doc, ds) := elabStr (dvDoc "\\usepackage{pgfplots}\n" body)
  let named (ds : Array Diag) (ps : Array Ir.Pending) : Bool :=
    ps.all fun p => ds.any (·.mentions p)
  -- Before resolution the census lists the citation too, named at its site.
  t "pending: the elaborated document lists the ref and the cite"
    ((Ir.pendingNodes doc).contains (.ref "none") &&
     (Ir.pendingNodes doc).contains (.cite "none"))
  t "pending: elaboration names both, by subject (W0349, W0351)"
    (named ds ((Ir.pendingNodes doc).map .node) &&
     (ds.filter fun d => d.code == "W0349" && d.subject == some "none").size == 1 &&
     (ds.filter fun d => d.code == "W0351" && d.subject == some "none").size == 1)
  -- The bibliography resolver leaves no citation node, with or without sources.
  let (doc', bibDs) := Bib.apply #[] doc
  t "apply_no_cite: no .cite node survives resolution (no bibliography)"
    (bibDs.isEmpty && (Ir.pendingNodes doc').all (!·.isCite) &&
     (Ir.pendingNodes doc').contains (.ref "none"))
  let withBib := Bib.apply #[("refs", "@misc{other, year = 2024}")]
    { doc with body := doc.body.push (.bibliography "refs" none #[]) }
  t "apply_no_cite: no .cite node survives resolution (a bibliography without the key)"
    ((Ir.pendingNodes withBib.1).all (!·.isCite) &&
     (withBib.2.filter fun d => d.code == "W0351" && d.subject == some "none").size == 1)
  -- The driver's reads, decided purely: no file, and a picture the tool failed on.
  let picSrc := (Ir.imageRefs doc').find? (·.startsWith Ir.picSrcPrefix)
  t "pending: the picture's request stands in the image refs" picSrc.isSome
  let fetched : Array (String × Image.Fetch) := (Ir.imageRefs doc').map fun src =>
    if src.startsWith Ir.picSrcPrefix then
      (src, .refused (DriverDiag.boundaryFailed "lualatex" "! Undefined control sequence."))
    else (src, .missing s!"/documents/{src}")
  let (store, imgDs) := Image.fulfil fetched
  t "fulfil_covers: one entry per requested source, in order"
    (store.entries.map (·.src) == Ir.imageRefs doc')
  let pend := Ir.pending doc' store
  t "pending: the resolved document and store list the ref and both images"
    (pend.size == 3 && pend.contains (.node (.ref "none")) && pend.contains (.image "absent.png") &&
     (picSrc.map fun s => pend.contains (.image s)).getD false)
  t "pending_named: every pending node has a diagnostic naming it"
    (named (ds ++ bibDs ++ imgDs) pend)
  t "pending_named: the refusal's subject is set at the decision, not by its words"
    (imgDs.any fun d => d.code == "E0382" && (picSrc.map fun s => d.subject == some s).getD false)
  -- A resolved document is pending-free: with the label, the file, and no
  -- picture, the census is empty and nothing needs naming.
  let (ok, okDs) := elabStr (dvDoc "" "\\section{A}\\label{a} See \\ref{a}.")
  t "pending: a resolved reference is not pending, and W0349 stays silent"
    ((Ir.pending ok { entries := #[] }).isEmpty && okDs.all (·.code != "W0349"))


/-- **The losses add up.** A construct refused once per document is named
once and *counted* every time: the visible line carries the total, and every
further site rides beside it as a note at its own position, so the number a
reader takes from the default log is the number of sites the log holds.

Before this, the key was spent at the first site and every later one was
dropped whole — ten lines standing for fifty losses on one real document,
two of them content dropped with no diagnostic at all. The rows below pin
both directions: the count is the site count (never the construct count),
and the notes are the sites (never a re-run of the first). Invented content
and design. -/
def diagSiteCountChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- One construct at three sites: three positions, one visible line.
  let thrice := dvDoc "" "\\raggedleft One.\n\n\\raggedleft Two.\n\n\\raggedleft Three."
  let ds := (elabStr thrice).2
  let of (code : String) (ds : Array Diag) : Array Diag := ds.filter (·.code == code)
  let visible (ds : Array Diag) : Array Diag := ds.filter (·.severity != .note)
  t "three sites of one construct are three diagnostics"
    ((of "W0104" ds).size == 3)
  t "three sites of one construct are one visible line"
    ((visible (of "W0104" ds)).size == 1)
  t "the visible line carries the site count"
    ((visible (of "W0104" ds)).all (·.sites == 3))
  -- The sites are the sites: each note stands where its own occurrence is,
  -- so `-v` locates every loss rather than repeating the first.
  t "every site is named at its own position"
    (((of "W0104" ds).filterMap fun d => d.span.map (·.pos.line)).toList == [3, 5, 7])
  -- Each site names the same loss, so "this loss is named" stays a lookup
  -- on the structured subject rather than a search of the message text.
  t "every site of one loss carries the same subject"
    (((of "W0104" ds).map (·.subject)).toList.eraseDups.length == 1 &&
      (of "W0104" ds).all (·.subject.isSome))
  -- The count is the number of sites the log holds — read off the log, which
  -- is the property a reader sizing the damage relies on.
  t "the count on the line is the number of diagnostics of that loss"
    ((visible (of "W0104" ds)).all fun d =>
      d.sites == (ds.filter (Diag.sameLoss d ·)).size)
  -- Only the first site is actionable prose: the help is advice about the
  -- construct, not about the occurrence, so it is never repeated.
  let helped := (elabStr (dvDoc ""
    "\\parbox{3cm}{One.}\n\n\\parbox{3cm}{Two.}\n\n\\parbox{3cm}{Three.}")).2
  t "the help is given once, at the first site"
    (((of "W0104" helped).filter (·.help.isSome)).size == 1 &&
      ((of "W0104" helped)[0]?.map (·.help.isSome)).getD false &&
      (of "W0104" helped).size == 3)
  -- A single site is a single loss: no count, no note, nothing added.
  let once := (elabStr (dvDoc "" "\\raggedleft Only one.")).2
  t "a construct at one site carries no count and no note"
    ((of "W0104" once).size == 1 && (of "W0104" once).all fun d =>
      d.sites == 1 && d.severity != .note)
  -- Two distinct losses under one code do not merge: the census is keyed by
  -- the loss, not by the code, so a count never borrows another's sites.
  let two := (elabStr (dvDoc ""
    "\\raggedleft One.\n\n\\parbox{3cm}{Two.}\n\n\\parbox{3cm}{Three.}")).2
  t "two losses sharing a code keep their own counts"
    ((visible (of "W0104" two)).size == 2 &&
      ((visible (of "W0104" two)).map (·.sites)).toList == [1, 2])
  -- Counting adds and silences nothing: the tally is the identity on every
  -- field but the count (`Diag.tallySites_id`), and idempotent, so a second
  -- pass cannot inflate a total.
  t "counting is idempotent"
    (Diag.tallySites ds == ds)
  t "counting neither adds nor drops a diagnostic"
    ((Diag.tallySites (of "W0104" two)).size == (of "W0104" two).size)
  -- What the reader actually sees, through the one renderer the driver uses.
  let rendered := ((visible (of "W0104" ds))[0]?.map (Render.human false)).getD ""
  t "the rendered line states the total"
    (hasStr rendered "(3 sites)")
  t "a single site renders no total"
    (!hasStr (((of "W0104" once)[0]?.map (Render.human false)).getD "") "sites)")
  -- The machine-readable channel carries it too, so a consumer reading one
  -- record knows the loss's multiplicity without scanning for the first.
  t "porcelain carries the site count on every site"
    ((of "W0104" ds).all fun d => hasStr (Render.porcelainDiag d) "\"sites\":3")
  -- The exit contract does not move: the further sites are notes, so a
  -- construct at three sites is still one warning under --werror.
  t "the further sites are not warnings"
    ((Diag.resolveAll #[] false ds).warnings == (Diag.resolveAll #[] false once).warnings)
  -- **A census key names its construct.** Counting made the keys legible and
  -- several were too coarse: one key stood for a family, so the family's
  -- *second* construct was dropped whole rather than merely uncounted. A
  -- float's ignored placement was such a key — the first float spent it and
  -- the next kind of float said nothing, in a message that would have named
  -- itself correctly had it been allowed to speak.
  let floats := (elabStr (dvDoc ""
    ("\\begin{figure}[htbp]\\caption{One.}\\end{figure}\n\n" ++
     "\\begin{table}[htbp]\\caption{Two.}\\end{table}"))).2
  t "two kinds of float each name their own ignored placement"
    (((of "N0102" floats).map (·.message)).toList.eraseDups.length == 2 &&
      (of "N0102" floats).all (·.sites == 1))
  -- Two heading levels likewise: the unused-short-title note used one key
  -- for every sectioning command, so only the first level ever said so.
  let shorts := (elabStr (dvDoc ""
    "\\section[One]{Section one}\n\n\\subsection[Two]{Subsection two}")).2
  t "two heading levels each name their own unused short title"
    (((of "N0103" shorts).map (·.message)).toList.eraseDups.length == 2 &&
      (of "N0103" shorts).all (·.sites == 1))
