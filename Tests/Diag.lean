module

public import LeanTex.Core.FigureLoss
public import LeanTex.Cli.FontDiscovery
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.FaceUse
public import LeanTex.Cli.LeanFactsFile
public import Tests.Support
public import Tests.CorpusStore
public import Tests.LayoutInkContracts
public import Tests.ListingStyleTable
public import Tests.DriverAssets
public import Tests.PrintX4
public import LeanTex.Core.PdfX
import LeanTex.Core.BibMacro

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

def diagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let codes := DiagCode.all.map (·.code)
  for c in codes.eraseDups do
    check ref s!"diag {c}: one code, one meaning"
      ((codes.filter (· == c)).length == 1)
  for c in DiagCode.all do
    check ref s!"diag {c.code}: carries a meaning" (!c.meaning.isEmpty)
    check ref s!"diag {c.code}: code string is code-shaped" (isDiagCode c.code)
  -- Every constructor keeps an emission site, and each emitted code string is its own.
  let mut emitted : List String := []
  for (_, applied) in ← codeSources do
    for c in applied do
      if !emitted.contains c then
        emitted := c :: emitted
  for c in emitted do
    check ref s!"diag {c}: emitted by the engine but not in the registry"
      (codes.contains c)
  for c in codes do
    check ref s!"diag {c}: registered but no longer emitted"
      (emitted.contains c)

/-- The reference list's diagnostics for a document citing `cite` against `.bib` text, resolved as a
build resolves it. -/
def dvBib (bib : String) (cite : String) (style : Option String)
    (w : WitnessRun := {}) : Array Diag :=
  let decl := match style with
    | some s => s!"\\bibliographystyle\{{s}}\n"
    | none => ""
  (bibResolve (w.rep s!"\\documentclass\{article}\n\\begin\{document}\nx \\cite\{{cite}}\n\n\
    {decl}\\bibliography\{refs}\n\\end\{document}\n") #[("refs", bib)]).2.2

/-- `dvBib` under biblatex's numeric style, `pre` before its load and
`opts` its options. -/
def dvBbl (bib cite : String) (pre : String := "") (opts : String := "style=numeric")
    (w : WitnessRun := {}) : Array Diag :=
  (bibResolve (w.rep s!"\\documentclass\{article}\n{pre}\\usepackage[{opts}]\{biblatex}\n\
    \\addbibresource\{refs.bib}\n\\begin\{document}\nx \\parencite\{{cite}}\n\n\
    \\printbibliography\n\\end\{document}\n") #[("refs.bib", bib), ("refs", bib)]).2.2

/-- Diagnostics of the data-expansion pass over a source, which needs no driver. -/
def dvData (src : String) (w : WitnessRun := {}) : Array Diag :=
  (Data.expandData "t" #[] (Parse.parse "t" (Lex.lex "t" (w.rep src)).1).1).2

/-- A driver probe: one real driver path run against a sandbox directory, returning what the driver
returned. -/
abbrev DriverProbe := System.FilePath → IO (Array Diag)

/-- The probed driver codes, by the code each probe must fire; every probe is hermetic, its message
the same on every host. -/
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
    -- The front door over in-hand bytes, read as the driver reads them, so no file is opened.
    (.W0002, fun _ => do
      let src ← Input.readDocument "doc.tex"
        ("\\documentclass{article}\n\\begin{document}\nCaf".toUTF8 ++ ⟨#[0xE9]⟩ ++
          ".\n\\end{document}\n".toUTF8)
      return src.diags),
    (.W0004, fun _ => do
      let src ← Input.readDocument "doc.tex" (("\\documentclass{article}\n" ++
        "\\usepackage[latin1]{inputenc}\n\\begin{document}\nCafé crème").toUTF8 ++
        ⟨#[0x92]⟩ ++ "s.\n\\end{document}\n".toUTF8)
      return src.diags),
    (.N0025, fun _ => do
      let src ← Input.readDocument "doc.tex" (("\\documentclass{article}\n" ++
        "\\usepackage[latin1]{inputenc}\n\\begin{document}\nCaf").toUTF8 ++ ⟨#[0xE9]⟩ ++
        ".\n\\end{document}\n".toUTF8)
      return src.ledger.notes),
    (.W0503, fun _ => do
      let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
        "A claim\\cite{k}.\n\\bibliography{references}\n\\end{document}\n")).1
      return (← Input.resolveBibliography "doc.tex" doc Bib.plainReading #[]).2.1),
    (.W0424, fun dir => do
      -- a file the run reads by its absolute path beside one that is not there
      IO.FS.writeFile (dir / "kept.bib") "@misc{k, title = {T}, year = 2024}\n"
      let kept := (dir / "kept").toString
      let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
        "A claim\\cite{k}.\n\\bibliography{" ++ kept ++ ", references}\n\\end{document}\n")).1
      return (← Input.resolveBibliography "doc.tex" doc Bib.plainReading #[]).2.1),
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
    -- The output intent's profile, named beside a document where no file answers it.
    (.W0446, fun dir => do
      let file := (dir / "doc.tex").toString
      return (← Tests.DriverAssets.loadProfile file { intent := some { profile := "absent.icc" } }).2),
    -- A file declaring PDF/X-4 with no output intent, judged as the driver judges it.
    (.W0445, fun _ => do
      let pdf := syntheticPdf #["<< /Type /Catalog /Pages 2 0 R >>",
        "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
        "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 10 10] /Contents 4 0 R >>",
        streamObj "1 0 0 rg 0 0 5 5 re f"]
      match Tests.DriverAssets.pdfxClaim { pdfx := some "X-4" } pdf 0 fun _ => .ok pdf with
      | .ok (_, ds) => return ds
      | .error _ => return #[]),
    -- A hand-built file meeting PDF/X-4, claimed over two links the claim leaves out.
    (.W0444, fun _ => do
      let pdf := Tests.PrintX4.passingPdf (Tests.PrintX4.profile 2 1 "prtr" "CMYK" "Probe Press 1")
      match Tests.DriverAssets.pdfxClaim { pdfx := some "X-4" } pdf 2 fun _ => .ok .empty with
      | .ok (_, ds) => return ds
      | .error _ => return #[]),
    -- A claim standing over a declared PDF 2.0, which it writes as 1.6.
    (.W0447, fun _ => do
      let pdf := Tests.PrintX4.passingPdf (Tests.PrintX4.profile 2 1 "prtr" "CMYK" "Probe Press 1")
      match Tests.DriverAssets.pdfxClaim { pdfx := some "X-4", pdfVersion := some "2.0" } pdf 0
          fun _ => .ok .empty with
      | .ok (_, ds) => return ds
      | .error _ => return #[]),
    (.N0448, fun _ => do
      let pdf := Tests.PrintX4.passingPdf (Tests.PrintX4.profile 2 1 "prtr" "CMYK" "Probe Press 1")
      match Tests.DriverAssets.pdfxClaim { pdfx := some "X-4" } pdf 0 fun _ => .ok .empty with
      | .ok (_, ds) => return ds
      | .error _ => return #[]),
    (.W0008, fun _ => do
      let doc := (elabStr ("\\documentclass{article}\n\\fonts{ dir = \"fonts\" }\n" ++
        "\\begin{document}\nx\n\\end{document}\n")).1
      return (← FontEnv.resolveDocDirs "doc.tex" doc.fonts.dirs).2),
    (.W0379, fun dir => do
      match ← Boundary.coldPicture dir "lualatex"
          (Ir.picHash "\\draw (0,0) parabola (1,1);") (why := "no executable file by this name on PATH") with
      | .error d => return #[d]
      | .ok _ => return #[]),
    (.W0419, fun dir => do
      let src := dvDoc "" ("\\begin{tikzpicture}\\node at (0,0) {Alpha};" ++
        "\\pattern (0,0) rectangle (1,1);\\end{tikzpicture}")
      let (raws, _) := Parse.parse "t" (Lex.lex "t" src).1
      let (doc, _, spans) := Elab.runRawsSpanned "t" raws
      let some (id, _) := doc.pictureSrcs[0]? | return #[]
      match ← Boundary.coldPicture dir "lualatex" id with
      | .error d =>
        let w := Boundary.withdraw spans.fallbacks #[(Ir.picSrcPrefix ++ id, .answered d none)]
        let (_, ds, _) := Elab.runPrepared "t" (Elab.prepare "t" raws) #[] (fun _ _ => {}) w.ids
        return Boundary.fold #[] false "lualatex" w ds
      | .ok _ => return #[]),
    (.W0011, fun _ => do
      let faces ← FontDiscovery.scanRoots [testFonts]
      return (← FontEnv.resolveMath faces (some "Open Sans") none false #[] #[] #[]).diags),
    (.N0016, fun _ => do
      let faces ← FontDiscovery.scanRoots [testFonts]
      let companion ← FontEnv.resolveMath faces none (some "Fira Sans") true #[] #[] #[]
      let first ← FontEnv.resolveMath faces none (some "Open Sans") true #[] #[] #[]
      return companion.diags ++ first.diags),
    -- Faces from the suite's own font directory, so the message is the same on every host.
    (.N0031, fun _ => do
      let code := testFonts ++ "/SourceCodePro-Regular.otf"
      let text (file : String) (bold italic : Bool) : FontDb.Face :=
        { path := testFonts ++ "/" ++ file, family := "Open Sans", subfamily := "Regular"
          bold, italic, fixedPitch := false, weight := if bold then 700 else 400 }
      let faces : Array FontDb.Face := #[text "OpenSans-Regular.ttf" false false,
        text "OpenSans-Bold.ttf" true false, text "OpenSans-Italic.ttf" false true,
        text "OpenSans-BoldItalic.ttf" true true,
        { path := code, family := "DejaVu Sans Mono", subfamily := "Book", bold := false
          italic := false, fixedPitch := true, weight := 400 },
        { path := code, family := "DejaVu Sans Mono", subfamily := "Bold", bold := true
          italic := false, fixedPitch := true, weight := 700 }]
      let doc := (elabStr ("\\documentclass{article}\n\\fonts{ body = \"Open Sans\" }\n" ++
        "\\begin{document}\nA \\textit{\\texttt{slanted}} run.\n\\end{document}\n")).1
      match ← FontAssembly.buildFontSet doc { faces, docDirs := [], dirs := #[], diags := #[] }
          (← FontEnv.Cache.mk') .settled with
      | .ok (_, _, ds, _) => return ds.filter (·.kind == .N0031)
      | .error _ => return #[]),
    (.W0390, fun _ => do
      match Font.parse (← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")) with
      | .error _ => return #[]
      | .ok body =>
        let idx := #[((0, 400, false), 0), ((1, 400, false), 0), ((2, 400, false), 0)]
        let fs : Font.FontSet := { fonts := #[body], index := idx }
        let doc := (elabStr ("\\documentclass{article}\n\\begin{document}\n" ++
          "A \\texttt{fixed pitch} run.\n\\end{document}\n")).1
        return SlotLoss.diags doc.fonts fs doc (SlotLoss.carries #[.pdf] doc.fontPolicy))]

/-- Every probe run once, each in its own sandbox, removed afterwards. -/
def runDriverProbes : IO (Array (DiagCode × Array Diag)) :=
  driverProbes.mapM fun (c, probe) => do
    let ds ← IO.FS.withTempDir probe
    return (c, ds)

/-- One firing input per code; `probed` reads the driver probes' own output. -/
def diagWitnessWith (w : WitnessRun) (one mapped withMath : Font.FontSet)
    (probed : DiagCode → Array Diag) : DiagCode → Array Diag
  | .E0001 => probed .E0001
  | .W0002 => probed .W0002
  | .W0004 => probed .W0004
  | .E0003 => #[DriverDiag.outputPathsConflict "HTML and Markdown both name 'out.html'"]
  | .E0004 => #[DriverDiag.outputUnwritable "site/out.pdf" "permission denied"]
  | .E0005 => #[DriverDiag.outputOverwritesInput (.same "Markdown" "doc.md" "doc.md")]
  | .E0006 => #[DriverDiag.outputFormatUnknown "notes.tex"]
  | .E0101 => dvE (w := w) "a\\"
  | .E0102 => dvE (w := w) "\\begin{verbatim}\nx"
  | .E0111 => dvE (w := w) (dvDeck "" ("\\addtobeamertemplate{block begin}{\\textbf{x}}{}\n" ++
      "\\begin{frame}{T}\nx\n\\end{frame}"))
  | .E0112 => dvE (w := w) (dvDoc "\\titlegraphic{\\includegraphics{logo.png}}\n" "x")
  | .E0113 => dvE (w := w) (dvDoc
      "\\renewcommand\\sectionlinesformat[4]{\\raisebox{-1pt}{#3}}\n" "x")
  | .E0201 => dvE (w := w) "{a"
  | .E0202 => dvE (w := w) "a}"
  | .E0205 => dvE (w := w) "\\begin{ x"
  | .E0303 => dvE (w := w) (dvDoc "\\define \\x(a b {y}\n" "x")
  | .E0304 => dvE (w := w) (dvDoc "\\page\n" "x")
  | .E0305 => dvE (w := w) (dvDoc "\\define \\role(who: text) {\\textbf{\\who}}\n" "\\role{$x$}")
  | .E0306 => dvE (w := w) (dvDoc "\\define \\x(a?: text) {\\ifgiven{\\b}{y}}\n" "\\x{z}")
  | .E0309 => dvE (w := w) "\\documentclass{proseplate}\n\\begin{document}\nx\n\\end{document}"
  | .E0310 => dvE (w := w) (dvDoc "" "\\begin{itemize}\nstray\n\\item x\n\\end{itemize}")
  | .E0311 => dvE (w := w) "a & b"
  | .E0312 => dvE (w := w) "\\fbox{\\section{x}}"
  | .E0313 => dvE (w := w) "\\documentclass{article}\nstray text\n\\begin{document}\nx\n\\end{document}"
  | .E0316 => dvE (w := w) (dvDoc "\\define \\x(a?: text) {\\a}\n" "\\x[oops")
  | .E0320 => dvE (w := w) (dvDoc "\\page{ oops }\n" "x")
  | .E0321 => dvE (w := w) "\\includegraphics[scale=big]{x.png}"
  | .E0322 => dvE (w := w) (dvDoc "\\page{ zoom = 3 }\n" "x")
  | .E0323 => dvE (w := w) (dvDoc "\\page{ vmargin = \"x\" }\n" "x")
  | .E0324 => dvE (w := w) (dvDoc "\\page{ size = quarto }\n" "x")
  | .E0325 => dvE (w := w) (dvDoc "\\assert{ pages =~ 1 }\n" "x")
  | .E0326 => dvE (w := w) (dvDoc "\\palette{ a = missingname }\n" "x")
  | .E0327 => dvE (w := w) (dvDoc "\\page{ header = x }\n" "x")
  | .E0328 => dvE (w := w) (dvDoc "\\style{banana}{ color = ink }\n" "x")
  | .E0329 => dvE (w := w) (dvDoc "\\allow{W9999}\n" "x")
  | .E0330 =>
    (Check.one { pages := 2, fontsEmbedded := true }
      { kind := .pages .eq 1, span := none }).toArray
  | .E0331 => dvE (w := w) "\\includegraphics[width=banana]{x.png}"
  | .E0332 => dvE (w := w) (dvDoc "\\palette{covered = 100\\%}\n" "x")
  | .E0333 => dvE (w := w) (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\fill (\\nope,0) rectangle (1,1);\n\\end{tikzpicture}"))
  | .E0336 => dvE (w := w) (dvDoc "" "\\begin{banner}{Logo}\nx\n\\end{banner}")
  | .E0340 => dvE (w := w) "\\faIcon{no-such-icon}"
  | .E0334 => dvE (w := w) (dvDoc "" ("\\begin{ifbackend}{html}\\begin{ifbackend}{pdf}\n" ++
      "orphaned\n\\end{ifbackend}\\end{ifbackend}"))
  | .E0401 => #[DriverDiag.noFont]
  | .E0402 => probed .E0402
  | .W0403 => #[DriverDiag.familyMissing "Sourse Serif Pro" ["Source Serif Pro"] 0,
      DriverDiag.familyMissing "Kaputt Grotesk" [] 12]
  | .E0404 => #[DriverDiag.fontFileUnusable "fonts/Broken-Regular.otf"
      "not a TrueType or OpenType file"]
  | .E0405 => dvL (w := w) mapped "lost \u27e8 here"
  | .E0501 => probed .E0501
  | .E0502 => probed .E0502
  | .N0100 => dvE (w := w) (dvDoc "\\usepackage[margin=1in]{geometry}\n" "x")
  | .N0102 => dvE (w := w) (dvDeck "" "\\begin{frame}[shrink]{T}\nx\n\\end{frame}")
  | .N0103 => dvE (w := w) (dvDoc "" "\\paragraph[short]{A long title} x")
  | .N0104 => dvE (w := w) (dvDeck ""
      "\\begin{frame}<presentation:0>[noframenumbering]{T}\nx\n\\end{frame}")
  | .N0105 =>
    dvE (w := w) (dvDoc "\\allow{W0341}\n" "x") ++ dvE (w := w) (dvDoc "\\allow{W0344}\n" "x") ++
      dvE (w := w) (dvDoc "\\allow{W0376}\n" "x")
  | .N0114 =>
    dvE (w := w) (dvDoc "\\ifdefined\\shiny\\sloppy\\else\\relax\\fi\n" "x") ++
    dvE (w := w) (dvDoc "\\newcommand{\\shiny}{y}\\ifdefined\\shiny\\relax\\fi\n" "x") ++
    dvE (w := w) (dvDoc "\\usepackage{booktabs}\n\\@ifpackageloaded{booktabs}{\\relax}{}\n" "x") ++
    dvE (w := w) (dvDoc "\\AtBeginDocument{\\IfPackageLoadedF{wideframe}{\\relax}}\n" "x")
  | .N0200 => dvL (w := w) one (dvDoc "\\page{ height = 127pt, margin = 20pt }\n"
      "a\n\n\\vspace{20pt minus 8pt}\nb\n\n\\vspace{20pt minus 8pt}\nc")
  | .N0016 => probed .N0016
  | .N0018 => dvL (w := w) withMath "$\\mathcal{L} + \\mathsf{A}$"
  -- A styled scalar in a covered range whose own glyph is an isolated hole.
  | .W0016 =>
    match withMath.fonts[1]? with
    | some fira =>
      let noBB : Font := { fira with
        cmap := fira.cmap.filter fun r => !(r.1.toNat ≤ 0x1D538 && 0x1D538 ≤ r.2.1.toNat) }
      let fs : Font.FontSet := { withMath with fonts := #[withMath.fonts[0]!, noBB] }
      dvL (w := w) fs "$\\mathbb{A}$"
    | none => #[]
  | .N0017 => (Elab.run "doc.tex" "A classless page, assumed article.").2
  | .N0019 => dvE (w := w) (dvDoc "" "\\begin{ifbackend}{pdf}\nprint only\n\\end{ifbackend}")
  | .N0020 =>
    let sty := "\\AtBeginDocument{\\newgeometry{textwidth=5.5in}}\n\\def\\x#1,#2\\relax{#1}\n"
    let sraws := (Parse.parse "venueguide.sty" (Lex.lex "venueguide.sty" sty).1).1
    let draws := (Parse.parse "t" (Lex.lex "t" "\\usepackage{venueguide}\n").1).1
    let (raws, spliced) := Compat.applyLocalSty draws #[("venueguide", sraws)]
    let ds := (Elab.runRaws "t" raws).2
    spliced.map fun (s, src, p) => Compat.styRead (src.getD "t") s p ds
  | .N0021 => dvL (w := w) one (dvDoc "\\page{ headsep = 20pt, footskip = 30pt }\n" "x")
  | .W0368 => dvE (w := w) (dvDoc "\\usepackage[klingon]{babel}\n" "x") ++
      dvE (w := w) (dvDoc "\\pdfmeta{ language = \"xx\" }\n" "x")
  | .W0369 => dvE (w := w) (dvDoc "\\babelfont[french]{rm}{Demo Serif}\n" "x")
  | .E0375 => dvE (w := w) (dvDoc
      "\\newlength{\\half}\\setlength{\\half}{\\dimexpr\\textwidth/2\\relax}\n" "x")
  | .W0370 => dvE (w := w) (dvDoc "" "a claim\\footnotemark stands here") ++
      dvE (w := w) (dvDoc "" "a claim\\footnotemark[3] stands here")
  | .W0371 => dvE (w := w) (dvDoc "" "a\\footnote{first\n\nsecond}")
  | .W0372 => dvL (w := w) one (dvDoc "\\page{ width = 120pt, height = 150pt, margin = 20pt }\n"
      ("x\\footnote{" ++ String.intercalate " " (List.replicate 60 "wow") ++ "}"))
  | .W0373 => dvE (w := w) (dvDoc "\\title{An Invented Panel\\thanks{Synthetic Grant 1}}\n"
      "x\n\\maketitle")
  | .W0374 => dvE (w := w) ("\\documentclass{card}\n\\begin{document}\n" ++
      "x\\footnote{an aside}\n\\end{document}")
  | .N0376 => dvE (w := w) (dvDoc "" "\\includegraphics{chart.png}") ++
      Ir.picAltDiags (elabStr (dvDoc "\\pictures{ tool = lualatex }\n"
          "\\begin{tikzpicture}\\draw (0,0) parabola (1,1);\\end{tikzpicture}")).1
        (fun _ => none) (fun _ => true)
  | .W0377 => dvE (w := w) (dvDoc "" "\\href{https://example.org/x}{}")
  | .W0381 => dvE (w := w) (dvDoc "" "\\qty{9.81}{\\banana}")
  | .W0001 => dvE (w := w) (dvDoc "" "x\n\\end{document}\nleft over")
  | .W0003 => dvL (w := w) one (dvDoc "" "$x^2$")
  | .W0005 =>
    -- Located, so each states how far it runs, a stage's with its frame or section page.
    let w := { w with located := true }
    let wide := String.ofList (List.replicate 90 'w')
    dvL (w := w) one (dvDoc "\\page{ width = 60pt, margin = 10pt, justify = on }\n"
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa") ++
    dvL (w := w) one (dvDeck "\\theme{moloch}\n" ("\\begin{frame}\n" ++ wide ++ "\\footnote{" ++
      wide ++ "}\n\\end{frame}\n\\begin{frame}\n\\begin{columns}\\column{0.7\\textwidth}Left." ++
      "\\column{0.7\\textwidth}Right.\n\\end{columns}\n\\end{frame}\n\\section{" ++ wide ++ "}\n" ++
      "\\begin{frame}\nx\n\\end{frame}"))
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
  | .W0007 => dvH (w := w) (dvDoc "\\runninghead{name}\n" "x")
  | .W0008 => probed .W0008
  | .W0009 => dvL (w := w) mapped "for all is \u2200 set"
  | .W0010 => dvL (w := w) one (dvDoc "" (String.join
      ((List.range 5).map fun _ => "\\begin{itemize}\\item x\n") ++
      String.join ((List.range 5).map fun _ => "\\end{itemize}\n")))
  | .W0011 => probed .W0011
  | .W0012 =>
    dvE (w := w) "$\\overset{?}{=}$" ++
    dvE (w := w) "$\\overset{\\alpha}{\\beta}$"
  | .W0013 => #[DriverDiag.allowUnfired "E0333"]
  | .W0014 => dvE (w := w) "\\begin{align*}a &= b \\\\ c\\end{align*}" ++
    dvE (w := w) "$\\begin{array}{c}a & b\\end{array}$"
  | .W0015 => dvE (w := w) "\\begin{align}a &= b\\end{align}"
  | .W0101 => dvE (w := w) (dvDoc "\\usepackage{natbib}\n\\bibpunct{(}{)}{;}{s}{,}{,}\n" "x")
  | .W0102 => dvE (w := w) (dvDoc "\\definecolor{c}{hsb}{0.5,0.5,0.5}\n" "x")
  | .W0103 => dvE (w := w) (dvDoc "\\usepackage{nosuchpkg}\n" "x")
  | .W0104 => dvE (w := w) (dvDoc (String.intercalate "\n"
      ["\\directlua{tex.print('x')}", "\\raggedright",
       "\\sloppy", "\\selectlanguage{german}", "\\pagestyle{headings}",
       "\\ifx\\x\\y\\fi", "\\usecolortheme{dove}",
       "\\setbeamercovered{again covered}", "\\titlegraphic{}"] ++ "\n") "x") ++
      dvE (w := w) "\\documentclass[twocolumn,draft]{article}\n\\begin{document}\nx\n\\end{document}\n"
  | .W0105 => dvE (w := w) "\\uncover<zz>{x}"
  | .W0106 => dvE (w := w) (dvDoc "\\ExplSyntaxOn \\cs_new:Npn \\x { } \\ExplSyntaxOff\n" "x")
  | .W0107 => dvE (w := w) (dvDoc "" "x \\setlength{\\parskip}{foo}")
  | .W0108 => dvE (w := w) "\\textbf{\\centering x}"
  | .W0110 => dvE (w := w) "\\includegraphics[angle=45]{x.png}" ++
      dvE (w := w) "\\documentclass[parskip=half]{scrartcl}\n\\begin{document}\nx\n\\end{document}\n"
  | .W0111 => dvE (w := w) (dvDoc "\\setkomafont{banana}{\\bfseries}\n" "x")
  | .W0201 => dvL (w := w) one (dvDoc "\\page{ hmargin = 1in }\n"
      (String.intercalate " " (List.replicate 40 "typesetting is the arrangement of type")))
  | .W0202 => dvL (w := w) one (dvDoc "\\style{section}{ before = 2pt, after = 10pt }\n"
      "\\section{a}\nbody")
  | .W0301 => dvE (w := w) "\\mystery{x}" ++ dvE (w := w) "\\mystery[16]{x}" ++
      dvE (w := w) "\\mystery[16 oops" ++ dvE (w := w) "\\mystery\n[note] stays" ++
      dvE (w := w) "\\mystery[16]{x} and \\mystery{y}"
  | .W0307 => dvE (w := w) (dvDoc "" "\\begin{external}\nx\n\\end{external}")
  | .W0302 => dvE (w := w) (dvDoc "" "\\begin{banner}\nx\n\\end{banner}")
  | .W0303 => dvE (w := w) (dvDoc "\\define \\underline(a: content) {\\a}\n" "x")
  | .W0304 => dvE (w := w) "\\textcolor{nope}{x}"
  | .W0309 => dvE (w := w) (dvDoc "" "\\maketitle")
  | .W0310 => dvE (w := w) (dvDoc "" "\\section[oops\nnever closed")
  | .W0311 => dvE (w := w) (dvDeck "" ("\\begin{frame}\n\\frametitle{One}\n" ++
      "\\frametitle{Two}\nx\n\\end{frame}"))
  | .W0312 => dvE (w := w) "\\title[never closes\n\\begin{document}\nx\n\\end{document}"
  | .W0314 => dvE (w := w) (dvDeck "" ("\\begin{frame}{T}\\begin{columns}\n" ++
      "\\begin{column}{banana}\nx\n\\end{column}\n\\end{columns}\\end{frame}"))
  -- Yellow over white meets no ratio at any mix.
  | .W0315 => dvE (w := w) (dvDoc "" "\\textcolor{yellow!50}{faint}")
  | .W0316 => dvE (w := w) (dvDoc "\\palette[dark]{ a = #101010 }\n" "x")
  -- A mid-grey ink: no neutral tone reads on it, so the seeds generate nothing.
  | .W0306 => dvE (w := w) (dvDoc "\\palette[seeds]{ ink = #808080, paper = #FFFFFF, accent = #E85D2A }\n" "x")
  | .W0411 => dvE (w := w) (dvDoc "\\usepackage{minted}\n"
      "Alpha \\begin{minted}{python}x = 1\\end{minted} omega.") ++
    dvE (w := w) (dvDoc "\\usepackage{minted}\n" "\\begin{minted}{python}x = 1\\end{minted}") ++
    dvE (w := w) (dvDoc "" "A \\fbox{\\begin{verbatim}\nx = 1\n\\end{verbatim}} b.")
  | .W0413 => dvE (w := w) (dvDoc "\\usepackage{minted}\n" "\\textbf{Alpha \\mint{python}{x = 1} omega}")
  | .W0412 => dvE (w := w) (dvDoc "\\usepackage{minted}\n" "Alpha \\mintinline{pyhton}{x} omega.")
  -- A mid-grey ink on a mid-grey page: no tone of either reaches 7:1 on the other.
  | .W0308 => dvH (w := w) (dvDoc "\\palette{ bg = #767676, fg = #777777 }\n" "x")
  -- A theorem whose statement Lean elaborated around a placeholder.
  | .W0414 => (Surface.readCode .lean "t.lean"
      "-- leantex: show = math, code\ntheorem t : True := trivial\n" (some
      { lean := "4.34.1", errors := 0, binders := #[]
        decls := #[{ name := "t", kind := .theorem, prop := true, start := (2, 0), stop := (2, 26)
                     type := some (.apps (.const "sorryAx") []) }] })).2
  -- A Lean file's facts written for another text of it, and a file whose facts were never written.
  | .W0433 => (LeanFacts.judge "Tide" "/p/.lake/build/leantex/Tide.facts" "theorem t : True := trivial\n"
      (LeanFactsFile.helpFor "lake exe leantex-export Tide"
        "/p/.lake/build/leantex/Tide.facts" false)
      (some ("{\"leantex-lean-export\":3,\"lean\":\"4.34.1\",\"errors\":0}\n" ++
        "{\"leantex-lean-export-end\":0}\n").toUTF8)).2
  | .N0032 => (LeanFacts.judge "Tide" "/p/.lake/build/leantex/Tide.facts" "theorem t : True := trivial\n"
      (LeanFactsFile.helpFor "lake exe leantex-export Tide"
        "/p/.lake/build/leantex/Tide.facts" false) none).2
  -- A linked statement in a file whose changes its commit does not hold.
  | .W0431 => (Surface.readCode .lean "t.lean"
      "-- leantex: show = math, link = https://github.com/acme/tides\ntheorem t : True := trivial\n"
      (some { lean := "4.34.1", errors := 0, binders := #[]
              decls := #[{ name := "t", kind := .theorem, prop := true, start := (2, 0), stop := (2, 26)
                           type := some (.apps (.const "True") []) }] })
      { commit := some "c0ffee", path := some "t.lean", dirty := some true, tracked := true }).2
  -- A linked statement in a file no repository holds.
  | .W0432 => (Surface.readCode .lean "t.lean"
      "-- leantex: show = math, link = https://github.com/acme/tides\ntheorem t : True := trivial\n"
      (some { lean := "4.34.1", errors := 0, binders := #[]
              decls := #[{ name := "t", kind := .theorem, prop := true, start := (2, 0), stop := (2, 26)
                           type := some (.apps (.const "True") []) }] })).2
  | .W0440 => dvE (w := w) (dvDoc "\\usepackage{colorspace}\n\\definespotcolor{ink}{Probe Ink}{0,.5,1,0}\n"
      "\\textcolor{ink!50!black}{x}")
  | .W0441 => dvE (w := w) (dvDoc "\\usepackage{colorspace}\n\\definespotcolor{one}{Probe Ink}{0,.5,1,0}\n"
      "\\definespotcolor{two}{Probe Ink}{1,0,0,0}x")
  -- A theorem whose statement names its hypothesis after it, which words do not say.
  | .W0415 => (Surface.readCode .lean "t.lean"
      "-- leantex: show = prose\ntheorem t (h : True) : h = h := rfl\n" (some
      { lean := "4.34.1", errors := 0, binders := #[]
        decls := #[{ name := "t", kind := .theorem, prop := true, start := (2, 0), stop := (2, 35)
                     type := some (.pi "h" .explicit true (.apps (.const "True") [])
                       (.apps (.const "Eq") [.apps (.const "True") [], .apps (.bvar 0) [],
                         .apps (.bvar 0) []])) }] })).2
  -- A phrase for a constant no statement names.
  | .W0416 => (Surface.readCode .lean "t.lean"
      "-- leantex: show = prose, phrase.zz = \"#1 is void\"\ntheorem t : True := trivial\n" (some
      { lean := "4.34.1", errors := 0, binders := #[]
        decls := #[{ name := "t", kind := .theorem, prop := true, start := (2, 0), stop := (2, 26)
                     type := some (.apps (.const "True") []) }] })).2
  | .W0442 => dvE (w := w) (dvDoc "\\page{ trimbox = \"9 9 700 400\" }\n" "x")
  | .W0443 => dvE (w := w) (dvDoc "\\AddToHook{shipout/before}{\\pdfvariable pageattr{/Rotate 90}}\n" "x")
  | .W0434 => dvE (w := w) (dvDoc "\\usepackage{blueprint}\n" "x")
  | .W0109 => dvE (w := w) (dvDoc "\\setbeamercovered{dynamic}\n" "x")
  | .W0436 => dvE (w := w) (dvDoc ("\\usepackage{amsthm}\n" ++
      "\\usepackage[link=https://github.com/example/widgets]{blueprint}\n\\newtheorem{lemma}{Lemma}\n")
      "\\begin{lemma}\\lean{Example.Widget} x\\end{lemma}")
  | .W0444 => probed .W0444
  | .W0445 => probed .W0445
  | .W0446 => probed .W0446
  | .N0448 => probed .N0448
  | .W0447 => probed .W0447
  | .W0317 => dvE (w := w) ("\\documentclass{card}\n\\runninghead{name}\n" ++
      "\\begin{document}\nx\n\\end{document}")
  | .W0318 => dvE (w := w) (dvDoc "\\chrome{ footer = { left = \\sectiontitle } }\n" "x")
  | .W0319 => dvE (w := w) (dvDoc "\\theme{banana}\n" "x")
  | .W0320 => dvE (w := w) (dvDoc "" "\\section{a}\n\n\\subsubsection{b}\nx")
  | .W0321 => dvE (w := w) (dvDoc "\\title{T}\n" "\\section{a}\nx\n\n\\maketitle")
  | .W0322 => dvE (w := w) (dvDoc "\\title{T}\n" "\\maketitle\n\n\\maketitle")
  | .W0323 => dvE (w := w) (dvDoc "" "\\begin{ifbackend}{banana}\nx\n\\end{ifbackend}")
  | .W0325 => dvH (w := w) (dvDoc "" ("\\begin{nav}\\link{#a}{A}\\end{nav}\n\n" ++
      "\\begin{nav}\\link{#b}{B}\\end{nav}\n\n\\section{a}\nx"))
  | .W0326 => dvH (w := w) (dvDoc "" "\\link{#nowhere}{dead}")
  | .W0327 => dvH (w := w) (dvDoc "" "\\section{Signal Path}\nx\n\n\\section{Signal, Path}\ny")
  | .W0328 => dvL (w := w) one (dvDoc
      (s!"\\runningfoot\{{String.intercalate " " (List.replicate 40 "an overlong footer")}}\n")
      "x")
  | .W0329 => dvE (w := w) (dvDoc "\\fontfallback{x}\n" "x")
  | .W0330 => dvE (w := w) (dvDoc "\\palette{ bg = #18181B }\n" "x")
  | .W0331 => dvH (w := w) (dvDoc
      "\\style{itemize}{ marker = {\\includegraphics{rects.png}} }\n"
      "\\begin{itemize}\n\\item a\n\\end{itemize}")
  | .W0348 => dvE (w := w) (dvDeck "\\palette{ alert = #112233 }\n\\theme{moloch}\n"
      "\\begin{frame}{T}\nx\n\\end{frame}")
  | .W0354 => dvE (w := w) (dvDoc
      "\\usepackage[tableposition=top]{caption}\n\\captionsetup[table]{labelfont=bf}\n" "x")
  | .W0355 => dvE (w := w) (dvDoc "\\theme{moloch}\n" "x")
  | .W0351 => dvBib (w := w) "@misc{real, year = 2024}" "ghost" none ++
      dvE (w := w) (dvDoc "" "x \\cite{ghost}")
  | .W0352 => dvBib (w := w) "@misc{broken, year = ?}\n@misc{kept, year = 2024}" "kept" none
  | .W0450 => dvBib (w := w) "@misc{k, title = {First}, year = 2024}\n@misc{k, title = {Second}, year = 2024}"
      "k" none
  | .W0451 => dvE (w := w) (dvDoc "" "A\\footnote{\\begin{center}Kqzv\\end{center}} b.")
  | .W0452 => dvE (w := w) (dvDoc "" "A \\fbox{\\begin{minipage}{2cm}Kqzv\\end{minipage}} b.")
  | .W0455 => dvE (w := w) (dvDoc "" "A \\fbox{\\begin{itemize}\\item Kqzv\\end{itemize}} b.")
  -- A Javadoc inline tag with nothing to stand for, and a link to a program element.
  | .W0453 => (Surface.read (.code .java) "t.java" (w.rep "/** {@inheritDoc} */\nvoid f() {}\n")).2
  | .W0454 => (Surface.read (.code .java) "t.java" (w.rep "/** See {@link Other}. */\nvoid f() {}\n")).2
  | .W0353 => dvBib (w := w) "@misc{k, year = 2024}" "k" (some "mystery")
  | .N0029 => dvBib (w := w) "@misc{k, title = {T}, url = {https://example.org/k}, year = 2024}" "k"
      (some "plain")
  | .W0420 => dvBib (w := w) "@misc{k, title = {T}, date = {Spring 2020}}" "k" (some "plainnat")
  | .W0421 => dvBbl (w := w) "@misc{k, title = {T}, date = {2020}}" "k" "\\usepackage[ngerman]{babel}\n"
  | .W0422 => dvBbl (w := w) "@set{s, entryset = {a,b}}\n@misc{a, title = {A}, date = {2020}}\n\
      @misc{b, title = {B}, date = {2021}}" "s"
  | .W0423 => dvBbl (w := w) "@misc{k, title = {T}, date = {2020}, related = {r}}\n\
      @misc{r, title = {R}, date = {2019}}" "k"
  | .W0424 => probed .W0424
  | .W0503 => probed .W0503
  | .W0425 => dvBib (w := w) "@inbook{k, title = {T}, crossref = {nowhere}, year = 2024}" "k" none ++
      dvBbl (w := w) "@xdata{d, publisher = {P}, location = {L}, xdata = {e}}\n@xdata{e, xdata = {d}}\n\
        @book{r, title = {R}, date = {2001}}\n@book{k, title = {T}, date = {2020}, xdata = {d, r}, \
        note = {xdata=d-note}, editor = {xdata=d-publisher}, origlocation = {xdata=d-location-3}, \
        addendum = {xdata=d}}" "k"
  | .W0426 => dvBib (w := w) "@article{k, title = {T}, journal = undefinedjt, year = 2024}" "k" none
  | .W0427 => dvBbl (w := w) "@misc{k, title = {T}, date = {2020}}" "k" (opts := "style=numeric,sortlocale=ja_JP")
  | .N0030 => dvBib (w := w) "@misc{k, title = {T}, note = {R & D}, year = 2024}" "k" none
  | .W0428 => dvE (w := w) "\\documentclass{article}\n\\usepackage{biblatex}\n\\addbibresource{refs.bib}\n\
      \\begin{document}\nx\\supercite{k}\n\\end{document}\n"
  | .W0429 => dvBib (w := w) "@misc{k, title = {T}, note = {\\section{S}}, year = 2024}" "k" none
  | .W0332 => dvE (w := w) (dvDeck "\\theme{moloch}\n"
      "\\framefoot{p. \\pagenumber}\n\\begin{frame}{T}\nx\n\\end{frame}")
  | .W0333 => dvL (w := w) one (dvDeck "\\theme{moloch}\\title{T}\\author{A}\n"
      (s!"\\maketitle\n\\framefoot\{{String.ofList (List.replicate 200 '0')}}\n" ++
       "\\begin{frame}{F}\nx\n\\end{frame}"))
  | .W0334 => dvE (w := w) (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\draw (0,0) parabola (1,1);\n\\end{tikzpicture}"))
  | .W0335 => dvL (w := w) one (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\fill (0,0) rectangle (40,1);\n\\end{tikzpicture}"))
  -- Two nodes one node distance apart, each label wider than that.
  | .W0336 => dvL (w := w) one (dvDoc "" ("\\begin{tikzpicture}\n" ++
      "\\node (a) {A Wide Enough Label};\n" ++
      "\\node (b) [right =of a] {Another Wide Label};\n\\end{tikzpicture}"))
  | .W0337 => dvE (w := w) (dvDoc "" "\\begin{tabular}{ll}\na & b & c \\\\\nd \\\\\n\\end{tabular}") ++
      dvE (w := w) (dvDoc "" ("\\begin{tabular}{lll}\n\\multicolumn{\\relax}{c}{w} & c & d \\\\\n" ++
        "a \\multicolumn{2}{c}{x} & y & z \\\\\n\\end{tabular}"))
  | .W0338 => dvL (w := w) one (dvDoc "" ("\\begin{tabular}{p{0.8\\linewidth}p{0.8\\linewidth}}\n" ++
      "a & b \\\\\n\\end{tabular}"))
  | .W0384 => dvF (w := w) one (dvDeck "\\theme{moloch}\n"
      ("\\begin{frame}{Too tall}\n" ++
       String.join (List.replicate 30 "one line\n\n") ++ "\\end{frame}\n" ++
       "\\begin{frame}[standout]\n" ++
       String.join (List.replicate 30 "one line\n\n") ++ "\\end{frame}"))
  | .W0400 => dvF (w := w) one (dvDeck "\\theme{moloch}\n"
      ("\\begin{frame}{Nearly fits}\n\\vspace*{12pt}\n" ++
       String.join (List.replicate 16 "one line\n\n") ++ "\\end{frame}"))
  | .W0399 => dvH (w := w) (dvDeck ""
      "\\begin{frame}\n\\begin{itemize}\n\\item Kilo\n\\vfill\nLima\n\\end{itemize}\n\\end{frame}")
  | .W0385 => dvE (w := w) "$\\text{\\textbf{bold} word}$"
  | .W0389 => dvE (w := w) "$\\raisebox{1pt}{\\sum_{k} x_k}$"
  | .W0390 => probed .W0390
  | .N0031 => probed .N0031
  | .W0391 =>
    let sty := "\\AtBeginDocument{\\@venueprobe{hidden words}}\n"
    let sraws := (Parse.parse "venuecode.sty" (Lex.lex "venuecode.sty" sty).1).1
    let draws := (Parse.parse "t" (Lex.lex "t"
      "\\usepackage{venuecode}\n\\begin{document}\nx\n\\end{document}\n").1).1
    (Elab.runRaws "t" (Compat.applyLocalSty draws #[("venuecode", sraws)]).1).2
  | .E0390 => dvMd (w := w) "a paragraph\n\n<div>raw</div>\n"
  | .W0392 => dvMd (w := w) "[a link](https://example.org \"the title\")\n"
  | .W0435 => dvE (w := w) (dvDoc "\\usepackage{amsthm}\n"
      "\\begin{proof}\nx\n\\begin{align*}\na &= b \\qedhere\n\\end{align*}\n\\end{proof}")
  | .W0386 => dvL (w := w) one (dvDoc
      ("\\page{ width = 220pt, margin = 20pt }\n" ++
       "\\title{Coordinating Placeholder Schedules\\\\A Second Declared Line}\n")
      "\\maketitle")
  | .W0388 => dvL (w := w) one (dvDeck "\\theme{moloch}\\title{T}\\author{A}\n"
      (s!"\\maketitle\n\\framefoot\{{String.ofList (List.replicate 200 '0')}}\n" ++
       "\\begin{frame}{F}\nx\n\\end{frame}"))
  | .W0358 => dvL (w := w) one (dvDoc "\\page{ size = a5 }\n"
      ("\\begin{table}\n\\begin{tabular}{l}\n" ++
       String.join (List.replicate 60 "alpha \\\\\n") ++
       "\\end{tabular}\n\\caption{Below the table}\n\\end{table}"))
  | .W0340 =>
    dvE (w := w) (dvDoc "" "x\n\n\\page{ size = a5 }\n\ny") ++
    dvE (w := w) (dvDoc "" "x\n\n\\usepackage{pgfplots}\n\ny")
  | .W0342 => dvE (w := w) (dvDoc "\\theme{plain}\n\\define \\muted(word: content) {\\word}\n"
      "\\muted{x}")
  | .W0343 =>
    dvE (w := w) (dvDoc "\\page{ margin = 20pt }\n\\page{ margin = 30pt }\n" "x") ++
    dvE (w := w) (dvDoc "\\runningfoot{one}\n\\runningfoot{two}\n" "x")
  | .W0345 =>
    dvE (w := w) (dvDeck "\\palette{ covered = #000000 }\n"
      "\\begin{frame}{T}\n\\uncover<2>{x}\n\\end{frame}") ++
    dvE (w := w) (dvDeck "\\palette{ covered = 80\\% }\n"
      "\\begin{frame}{T}\n\\uncover<2>{x}\n\\end{frame}")
  | .W0346 =>
    dvE (w := w) (dvDoc "" "a {\\palette{ q = #112233 } b} c") ++
    dvE (w := w) (dvDoc "" "\\textbf{\\page{ size = a5 } x}")
  | .E0347 =>
    dvE (w := w) (dvDoc "" "\\runninghead{Chapter One}\n\nx") ++
    dvE (w := w) (dvDoc "" "\\textbf{\\runningfoot{Y} z}")
  | .N0359 => dvE (w := w) (dvDeck ""
      "\\note{\\begin{frame}{Carried}\nspoken \\note{never carried} words\n\\end{frame}}")
  | .W0601 => #[Image.imageMissing "figures/plot.png" "/documents/figures/plot.png",
      Image.imageUnreadable "figures/plot.png" "permission denied (error code: 13)"]
  | .W0362 => dvE (w := w) (dvDoc "\\pictures{ tool = none }\n" ("\\begin{tikzpicture}\n" ++
      "\\pattern (0,0) rectangle (1,1);\n\\end{tikzpicture}"))
  | .W0363 => dvE (w := w) (dvDeck ("\\setbeamertemplate{title page}{\\begin{tikzpicture}" ++
      "[remember picture,overlay]\\node at (0,0) {\\inserttitle};\\end{tikzpicture}}" ++
      "\\title{T}\n") "\\titlepage")
  | .W0602 => #[Image.imageUndecodable "figures/plot.gif"
      "not a PNG, JPEG, or PDF file"]
  | .W0603 => #[Image.imageIccDropped "figures/plot.png"]
  | .W0604 => #[Image.imageOrientationDropped "figures/photo.jpg" 6]
  | .W0605 => #[HtmlDoc.undecodableDiag "figures/box.pdf",
      HtmlDoc.undecodableDiag "figures/locked.pdf"
        (some "the PDF is encrypted; its content cannot be read; pdftocairo is not on PATH")]
  | .W0609 => FigureLoss.diags
      (FigureLoss.pdfLostDiag "plot.pdf" (.unfinished "pdftocairo produced an empty image"))
      ((PdfGfx.importPage type1FigurePdf).toOption.map (·.figure.losses) |>.getD #[]) ++
    #[FigureLoss.svgLostDiag false "figures/chart.svg" .absent (.property "filter"),
      FigureLoss.svgLostDiag false "figures/glow.svg"
        (.failed "rsvg-convert exited 1: an invented refusal") (.property "filter"),
      FigureLoss.svgGlyphDiag (some .pdf) "figures/map.svg" "6F22"]
  | .N0024 => FigureLoss.diags (FigureLoss.pdfConvertedDiag "figures/plot.pdf")
      ((PdfGfx.importPage type1FigurePdf).toOption.map (·.figure.losses) |>.getD #[]) ++
    #[FigureLoss.svgConvertedDiag false "figures/chart.svg" (.property "filter")]
  | .N0026 => #[FigureLoss.svgFontDiag none "figures/chart.svg" "Example Grotesk" "Open Sans"]
  | .N0027 => #[FigureLoss.svgNoteDiag "figures/chart.svg" "a link"]
  | .W0393 => #[DriverDiag.listingHighlightUnavailable "bash" "Pygments is unavailable"]
  | .W0394 => Tests.LayoutInkContracts.boundaryWitness one .W0394
  | .E0395 => Tests.LayoutInkContracts.boundaryWitness one .E0395
  | .W0396 => Tests.LayoutInkContracts.boundaryWitness one .W0396
  | .W0398 => dvE (w := w) (dvDoc "\\setmainfont{Demo Serif}\n\\usepackage{booktabs}\n" "x")
  | .E0606 => #[DriverDiag.htmlResourceUnavailable "an image still names 'figures/plot.svg'"]
  | .E0607 => #[DriverDiag.pdfWriteRefused (.objectStreamSize 67108865),
      DriverDiag.pdfWriteRefused (.objectSpelling 4)]
  | .N0023 => dvE (w := w) (dvDoc ""
      "\\begin{tikzpicture}\\draw (0,0) parabola (1,1);\\end{tikzpicture}")
  | .N0025 => probed .N0025
  | .W0383 => dvE (w := w) (dvDoc ""
      "\\begin{algorithm}\n\\lIf{$x < 0$}{negate $x$}\\;\n\\end{algorithm}")
  | .W0387 => dvE (w := w) (dvDoc "\\thispagestyle{plain}\n\\palette{codestring = #AA0000}\n" "x")
  | .W0449 =>
    dvE (w := w) (dvDoc "\\definecolor{plum}{HTML}{AA0000}\n" "x") ++
    dvE (w := w) (dvDoc "\\style{itemize}{ gap = 4pt }\n" "x") ++
    dvE (w := w) (dvDoc "\\usepackage{listings}\n\\lstset{numbers=left}\n" "x") ++
    let faced := (elabStr (dvDoc "\\fonts{ mono = \"Probe Mono\", math = \"Probe Math\" }\n" "x")).1
    FaceUse.diags #[("mono", ⟨"t", {}⟩), ("math", ⟨"t", {}⟩)] { one with math := some 0 } faced
  | .W0701 =>
    let (doc, _) := elabStr (dvDoc "\\output{ formats = pdf, alternatives = required }\n" "x")
    Ir.contractDiags (doc.output.contract.unmet Pdf.profile)
  | .W0379 => probed .W0379
  | .W0419 => probed .W0419
  | .W0382 => #[DriverDiag.boundaryFailed "lualatex"
      "! Undefined control sequence. · l.7 \\nope" (Ir.picSrcPrefix ++ "witness"),
    DriverDiag.boundaryUnfinished "lualatex" "exit code 3" (Ir.picSrcPrefix ++ "witness")]
  | .W0378 => #[DriverDiag.boundarySvgMissing "leantex-pic:0123456789abcdef" .textless,
      DriverDiag.boundarySvgMissing "leantex-pic:0123456789abcdef" .textlessDeclined,
      DriverDiag.boundarySvgMissing "leantex-pic:0123456789abcdef"
        (.unconverted "pdftocairo: not found (error code: 2)")]
  | .W0349 => dvE (w := w) "\\ref{nowhere}"
  | .W0350 => dvE (w := w) "\\section{A}\\label{twice}\\label{twice}"
  | .W0380 => dvE (w := w) "\\refstepcounter{section}\n\\label{stepped} see \\cref{stepped}"
  | .W0367 =>
    dvE (w := w) ("\\documentclass{beamer}\n\\usepackage[debug,size=a1]{beamerposter}\n" ++
      "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}")
  | .W0357 =>
    dvE (w := w) (dvDoc "\\edef\\x{\\csname y\\endcsname}\n" "x") ++
    dvE (w := w) (dvDoc "\\def\\pair#1.#2{#1 and #2}\n" "x")
  | .W0361 =>
    dvE (w := w) (dvDoc "\\title{T}\\newcommand{\\maketitle}{\\venuetitlebox}\n" "\\maketitle")
  | .W0364 =>
    dvData (w := w) ("\\data{ @job{a, role = {X}, start = 2020} " ++
        "@job{b, role = {Y}, start = 2021, end = 2024} }\n" ++
      "\\begin{foreach}{j}{job}\\val{j.end}\\end{foreach}") ++
    dvData (w := w) "\\data{ @job{a, role = {X}} }\\val{k.role}" ++
    dvData (w := w) "\\data{ @job{a, role = {X}} }\\begin{foreach}{j}{trip}\\val{j.role}\\end{foreach}"
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
    ask "Demo Sans Light" none ++ ask "Demo Sans" (some "Demo Sans Medium")

/-- Whether a text holds `\{name}`, an interpolation its string literal never ran. -/
def dvPlaceholder (s : String) : Bool :=
  let rec go : List Char → Bool
    | '\\' :: '{' :: c :: rest =>
      (c.isAlpha && match rest.dropWhile (fun x => x.isAlphanum || x == '.') with
        | '}' :: _ => true
        | _ => false) || go (c :: rest)
    | _ :: rest => go rest
    | [] => false
  go s.toList

/-- A reference only someone inside this repository can follow: a repo file, a source path, or a
milestone token. -/
def dvInternalRef (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "PLAN.md" || has "AGENTS.md" || has "PRINCIPLES.md" || has "THEOREMS.md" ||
    has "LeanTex/" || has ".lean" ||
    (Id.run do
      let cs := s.toList.toArray
      for i in [0:cs.size] do
        if cs[i]! == 'M' && (cs[i+1]?.map Char.isDigit).getD false &&
            !((i > 0) && (cs[i-1]!.isAlphanum || cs[i-1]! == '_')) &&
            !(((cs[i+2]?.map (·.isAlphanum)).getD false)) then
          return true
      return false)

/-- Whether a help tells the reader what to write: a `\` spelling, a flag, a `key = value`, a quoted
literal, a backticked command, or a `:`-led list of known values. -/
def dvHasAction (s : String) : Bool :=
  let has (pat : String) : Bool := (s.splitOn pat).length > 1
  has "\\" || has "--" || has "`" || has "=" || has ": " || has "{" ||
    (s.toList.filter (· == '\'')).length ≥ 2

/-- Message and help bounds in characters, taken from the longest texts that read well (W0315's
message, E0328's help). -/
def dvMsgMax : Nat := 124
def dvHelpMax : Nat := 211

/-- Sentence case: a message opens lowercase (or with a quoted construct)
unless its first word is a proper noun the engine speaks of. -/
def dvCaseOk (s : String) : Bool :=
  match s.toList with
  | [] => true
  | c :: _ =>
    !c.isUpper ||
      ["TeX", "LaTeX", "LEANTEX_FONT", "PNG", "JPEG", "WCAG", "HTML", "Pygments",
       "U+"].any (s.startsWith ·)

/-- One convention for terminal punctuation: none (a `?` may close a real question). -/
def dvTerminalOk (s : String) : Bool :=
  !(s.endsWith "." || s.endsWith "!")

/-- Code-shaped tokens in prose other than `own`: a message or help names only the code it is
printed under. -/
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

/-- Whether a text states a measured length: a number with a decimal fraction before a unit. -/
def dvMeasured (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  for h : i in [0:cs.size] do
    if cs[i] == '.' && i > 0 && (cs[i - 1]?.getD ' ').isDigit && (cs[i + 1]?.getD ' ').isDigit then
      let mut k := i + 1
      for _ in [i + 1:cs.size] do
        if (cs[k]?.getD ' ').isDigit then k := k + 1 else break
      let unit := String.ofList ((cs.extract k (k + 2)).toList)
      if ["pt", "bp", "mm", "cm", "in", "px", "em", "ex"].contains unit then return true
  return false

/-- Every reading a file's bytes can take, whose names a message may read a file by. -/
def dvReadings : List Encoding.Reading :=
  [.ascii, .utf8, .utf16 true, .utf16 false, .replaced] ++
    [Encoding.Legacy.windows1252, .iso885915, .macRoman].map .legacy

theorem dvReadings_covers (r : Encoding.Reading) : r ∈ dvReadings := by
  cases r with
  | utf16 big => cases big <;> simp [dvReadings]
  | legacy e => cases e <;> simp [dvReadings]
  | _ => simp [dvReadings]

/-- Digit-bearing spellings that name no site's particular: the words of every reading's own name. -/
def dvNumberSpellings : List String :=
  dvReadings.flatMap fun r =>
    (r.name.split (fun c => c == ' ' || c == '(' || c == ')')).toList.map (·.toString)

/-- The first number a text states outside quotes, scalars, standards' citations and
`dvNumberSpellings`: a site's particular, which belongs in the record's detail. -/
def dvNumber? (s : String) : Option String := Id.run do
  let cs := (s.toList ++ [' ']).toArray
  let mut quoted := false
  let mut doubled := false
  let mut word := ""
  let mut out : Option String := none
  let mut prev := ""
  for h : i in [0:cs.size] do
    let c := cs[i]
    -- An apostrophe inside a word (`frame's`) quotes nothing.
    let before := i > 0 && (cs[i - 1]?.getD ' ').isAlphanum
    let after := (cs[i + 1]?.getD ' ').isAlphanum
    let possessive := cs[i + 1]?.getD ' ' == 's' && !(cs[i + 2]?.getD ' ').isAlphanum
    if c == '\'' && !doubled &&
        (if quoted then !(before && after) || possessive else !before) then
      quoted := !quoted
      word := ""
    else if quoted then pure ()
    else if c.isAlphanum || c == '+' || c == '-' || c == '.' then
      word := word.push c
    else
      let w := (word.dropWhile (fun x => x == '.' || x == '-')).toString
      let w := String.ofList (w.toList.reverse.dropWhile (fun x => x == '.' || x == '-')).reverse
      let scalar := w.startsWith "U+" && w.length > 2 && (w.drop 2).all fun x => x.isDigit || ('A' ≤ x && x ≤ 'F')
      -- A standard's citation and a code name are the same at every site.
      let criterion := (w.splitOn ".").length == 3 && (w.splitOn ".").all fun p =>
        !p.isEmpty && p.all Char.isDigit
      let cited := (prev == "WCAG" && ["2.0", "2.1", "2.2"].contains w) ||
        (prev == "SC" && criterion) || isDiagCode w
      if out.isNone && w.any Char.isDigit && !scalar && !cited && !dvNumberSpellings.contains w then
        out := some w
      if !w.isEmpty then prev := w
      word := ""
      if c == '"' then doubled := !doubled
  return out

/-- The number lint read in both directions: what it must name and what it must let stand. -/
def dvNumberSelfChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (text, expected) in [
      ("row 3 is short", some "3"), ("'row 3' is short", none),
      ("the frame's 3 rows", some "3"), ("'name's 3 rows", some "3"),
      ("the key \"'x\" holds 3 rows", some "3"),
      ("below the contrast WCAG 2.2 asks of text (SC 1.4.3)", none),
      ("WCAG 5 rows", some "5"), ("SC 3 rows", some "3"),
      ("bytes read as UTF-16LE and Windows-1252 (Latin-1)", none),
      ("no glyph for U+2705", none), ("W0378 names it", none)] do
    check ref s!"diag voice number lint: {text} reads {expected}" (dvNumber? text == expected)

/-- A message's words as tokens: a run of non-spaces, or a `'...'` quotation closing before a space
or the end. -/
def dvTokens (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let ch (k : Nat) : Char := cs[k]?.getD ' '
    if ch i == ' ' then
      i := i + 1
      continue
    let mut j := i + 1
    if ch i == '\'' then
      for _ in [0:cs.size] do
        if j ≥ cs.size then break
        if ch j == '\'' && ch (j + 1) == ' ' then break
        j := j + 1
      j := min cs.size (j + 1)
    else
      for _ in [0:cs.size] do
        if j ≥ cs.size || ch j == ' ' then break
        j := j + 1
    out := out.push (String.ofList (cs.extract i j).toList)
    i := j
  return out.toList

/-- The noun two or one leading tokens spell, with the tokens after it. -/
def dvNoun? : List String → Option (Diag.Noun × List String)
  | a :: b :: rest =>
    match Diag.Noun.all.find? (·.label == a ++ " " ++ b) with
    | some n => some (n, rest)
    | none => (Diag.Noun.all.find? (·.label == a)).map (·, b :: rest)
  | [a] => (Diag.Noun.all.find? (·.label == a)).map (·, [])
  | [] => none

/-- A name token as the form prints it: quoted whole, or bare with no quote at its start. -/
def dvName (t : String) : Option Diag.Name :=
  if t.length ≥ 2 && t.startsWith "'" && t.endsWith "'" then
    some { text := ((t.drop 1).dropEnd 1).toString, quoted := true }
  else if t.any (· == '\'') then none
  else some { text := t, quoted := false }

/-- The form a message reads as, when it reads as one: `qual noun [name] [for [noun] name]`. -/
def dvForm? (s : String) : Option Diag.Words := do
  let q :: rest := dvTokens s | none
  let qual ← Diag.Qual.all.find? (·.label == q)
  let (noun, rest) ← dvNoun? rest
  let (name, rest) ← match rest with
    | t :: more => if t == "for" then pure (none, rest) else (dvName t).map (fun n => (some n, more))
    | [] => pure (none, [])
  let obj ← match rest with
    | [] => pure none
    | ["for", t] => (dvName t).map fun n => some (none, n)
    | "for" :: more =>
      match dvNoun? more with
      | some (n, [t]) => (dvName t).map fun x => some (some n, x)
      | _ => none
    | _ => none
  let w : Diag.Words := { qual, noun, name, obj }
  if w.render == s then some w else none

/-- Codes whose messages are still free prose: a baseline that may fall and never rise. -/
def formDebt : List String :=
  ["E0333",
   "E0395",
   "E0405",
   "N0018",
   "N0021",
   "N0024",
   "N0026",
   "N0027",
   "N0200",
   "N0376",
   "N0448",
   "W0003",
   "W0005",
   "W0007",
   "W0009",
   "W0010",
   "W0016",
   "W0201",
   "W0202",
   "W0308",
   "W0315",
   "W0320",
   "W0321",
   "W0325",
   "W0326",
   "W0327",
   "W0328",
   "W0330",
   "W0331",
   "W0332",
   "W0333",
   "W0334",
   "W0335",
   "W0336",
   "W0338",
   "W0345",
   "W0349",
   "W0358",
   "W0361",
   "W0363",
   "W0372",
   "W0377",
   "W0384",
   "W0386",
   "W0388",
   "W0394",
   "W0396",
   "W0399",
   "W0400",
   "W0442",
   "W0444",
   "W0445",
   "W0446",
   "W0601",
   "W0602",
   "W0603",
   "W0604",
   "W0605",
   "W0609",
   "W0701"]

/-- Does a message read as its code's form: its code's word, a noun of the vocabulary, a name. -/
def dvFormOk (d : Diag) : Bool :=
  (dvForm? d.message).any (·.qual == d.kind.qual)

/-- The form reader read in both directions: what it must accept and what it must refuse. -/
def dvFormSelfChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (text, ok) in [
      ("undefined command \\foo", true), ("unsupported environment banner", true),
      ("ignored option shrink for frame", true), ("invalid value 'big' for key scale", true),
      ("substituted face 'Demo Serif Regular' for 'Demo Serif Bold'", true),
      ("missing argument for \\page", true), ("missing font", true),
      ("unknown command '\\mystery'; its {...} arguments were kept as text", false),
      ("undefined banana \\foo", false), ("undefined command \\foo bar", false),
      ("undefined command 'a b", false), ("missing font it's", false)] do
    check ref s!"diag form reader: {text} reads {ok}" ((dvForm? text).isSome == ok)

/-- The lint over one fired diagnostic; the `\allow` codes (W0013, E0329, N0105) may quote the
user's own codes. -/
def dvLint (fail : String → IO Unit) (d : Diag) : IO Unit := do
  let judge (part : String) (s : String) : IO Unit := do
    if dvInternalRef s then
      fail s!"{d.code} {part}: repo-internal reference: {s}"
    unless dvTerminalOk s do
      fail s!"{d.code} {part}: terminal punctuation: {s}"
    unless dvCaseOk s do
      fail s!"{d.code} {part}: starts uppercase without a proper noun: {s}"
    if dvPlaceholder s then
      fail s!"{d.code} {part}: an uninterpolated placeholder: {s}"
    if (s.splitOn "\"\\").length > 1 then
      fail s!"{d.code} {part}: a construct is double-quoted; the convention is '...': {s}"
    unless d.code == "W0013" || d.code == "E0329" || d.code == "N0105" do
      for tok in dvForeignCodes d.code s do
        fail s!"{d.code} {part}: names {tok}, which the reader cannot look up: {s}"
  judge "message" d.message
  unless formDebt.contains d.code || dvFormOk d do
    fail s!"{d.code} message: not the form '{d.kind.qual.label} <noun> [name] [for [noun] name]': {d.message}"
  if let some text := d.detail then judge "detail" text
  if d.kind.loss.severity.isWarning && dvMeasured d.message then
    fail s!"{d.code} message: a measure taken at the site belongs in its detail: {d.message}"
  if d.kind.loss.severity.isWarning then
    if let some n := dvNumber? d.message then
      fail s!"{d.code} message: states '{n}', a particular of its site, which belongs in its detail: {d.message}"
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

/-- A rendered diagnostics dump as code-keyed blocks, split on `── ` line starts: the one parse the
compare and the update share. -/
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

/-- The invented sources the site audit runs over, each with what it exercises. -/
def siteAccountingProbes : List (String × String) :=
  [(dvDoc "" "Alpha \\zztrack[-11]{Bravo} charlie.", "an option run on an unknown command"),
   (dvDoc "" "Delta \\zztrack[16]{Echo} foxtrot.", "a second option run, another site"),
   (dvDoc "" "Golf \\footnotemark[3] hotel.", "an option run on a known pending construct"),
   (dvDoc "" "India \\zzplain{Juliett} kilo.", "an unknown command with no option run"),
   (dvDoc "" "Lima \\zztrack[1][2]{Mike} november.", "two option runs, one command"),
   (dvDoc "" "Oscar \\zzwrap[x]{Papa}{Quebec} romeo.", "an option run and two groups"),
   (dvDeck ("\\setbeamertemplate{title page}{\\begin{tikzpicture}" ++
      "[remember picture,overlay]\\fill[black] (current page.south west) rectangle " ++
      "(current page.north east);\\node[anchor=west] at (current page.west) " ++
      "{Label: \\inserttitle};\\end{tikzpicture}}\\title{Probe}\n") "\\titlepage",
    "a mixed title-page node beside a readable full-page ground"),
   (dvDoc "\\definecolor{codestring}{HTML}{AA0000}\n" "Sierra.",
    "a translated colour declaration of a retired listing key"),
   (dvDoc "\\setlength{\\parskip}{foo}\n" "Tango.", "a length set to a word"),
   (dvDoc ("\\NewDocumentCommand{\\varul}{m}{\\ifmmode\\underline{#1}\\else#1\\fi}\n" ++
      "\\newenvironment{verbatim}{\\setlength{\\fboxsep}{2pt}}{}\n") "Uniform \\varul{victor}.",
    "a built-in's ignored definitions, their texts lossy"),
   (dvDoc "\\renewcommand{\\textbf}[1]{\\ifmmode\\mathbf{#1}\\else#1\\fi}\n" "Whiskey \\textbf{xray}.",
    "a rendered built-in's refused redefinition, its text lossy"),
   (dvDoc "\\NewDocumentCommand{\\zzcond}{m}{\\ifx\\relax#1\\relax\\else\\underline{#1}\\fi}\n"
      "Whiskey \\zzcond{xray}.", "a definition whose text holds a conditional")]

/-- Sources the site audit lays out, elaborated with their locations kept. -/
def layoutSiteAccountingProbes : List (String × String) :=
  let wide := String.ofList (List.replicate 70 'w')
  [(dvDoc "\\page{ width = 220pt, margin = 20pt }\n"
      ("Short opening line.\\\\\n" ++ wide ++ " alpha beta gamma delta alpha beta.\\\\\n" ++
        "Short closing line.\n\nTwo wide words.\\\\\n" ++ wide ++ " " ++ wide ++ "\\\\\nEnd."),
    "layout: declared lines opening on an overrun"),
   (dvDoc ("\\page{ width = 220pt, margin = 20pt }\n\\newcommand{\\zztwolines}{alpha beta " ++
      wide ++ " gamma.\\\\ delta " ++ wide ++ " epsilon.}\n") "Short.\\\\\n\\zztwolines",
    "layout: a macro setting a re-flowed declared line and an overrunning last line")]

/-- Markdown sources the site audit reads through the markdown reader. -/
def mdSiteAccountingProbes : List (String × String) :=
  [("<details>\nCedar\n</details>\n", "markdown: a disclosure with no summary"),
   ("<details>\n<summary>Amber</summary>\nCedar\n", "markdown: an unclosed disclosure"),
   ("- <details>\n  <summary>Amber</summary>\n  Cedar\n\nFir\n",
    "markdown: a disclosure its list item cuts off"),
   ("<details>\n<summary>Amber</summary>\n\nCedar\n\n</details>\n", "markdown: a disclosure"),
   ("Alder <b>Kestrel</b> Birch\n\n<div>Wren</div>\n", "markdown: raw tags inline and as a block"),
   ("<a name=\"willow\"></a>\n\n[Willow](#willow)\n", "markdown: an empty target and its link")]

/-- Site collisions that stand, each with the file that owes the change; a row whose collision
closes fails the suite. -/
def siteAccounting : List (String × String × String) :=
  [("N0100", "W0319", "LeanTex/Core/Compat.lean, the \\usetheme rewrite: its translation \
note stands beside the refusal of the theme it produced, one construct accounted twice; say \
the translation in the refusal, or note it only when the theme resolves"),
   ("N0100", "W0361", "LeanTex/Core/Compat.lean and Elab.lean, the \\renewcommand rewrite: \
its translation note stands beside the refusal of the definition it produced; the same fold \
as the row above, one class"),
   ("W0334", "W0362", "LeanTex/Core/Elab.lean, the picture diagnostics loop: each refused \
construct is reported at the picture's position, where W0362 already names the picture's \
placeholder; name the constructs in W0362, or report each at its own span"),
   ("N0100", "W0107", "LeanTex/Core/Compat.lean, the length door: a \\setlength given a word, or a \
package option given an unreadable length, keeps its translation note beside the refusal of the \
value it carried, one construct accounted twice; say the translation in the refusal"),
   ("N0100", "W0104", "LeanTex/Core/Compat.lean, the conditional pass and the definer rewrite: a \
definition whose text holds a conditional keeps its translation note beside the warning that the \
conditional's part is skipped, one construct accounted twice; say the translation in the warning")]

/-- Independent facts at one source site, witnessed by varying each separately; not merge debt. -/
def independentSiteFacts : List (String × String) :=
  [("N0100", "W0315"), ("N0100", "W0387"), ("W0005", "W0386"), ("W0358", "W0384")]

def sitePairClassified (pair : String × String) : Bool :=
  independentSiteFacts.contains pair ||
    siteAccounting.any (fun row => row.1 == pair.1 && row.2.1 == pair.2)

/-- One construct, one accounting: grouped by cause site, no group holds two codes unless registered
as merge debt or as independent facts. -/
def siteAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let mut seen : List (String × String) := []
  let mut sources : Array (String × Array Diag) := #[]
  let mut independentWitnesses : Array (String × String) := #[]
  for (color, fails) in [("888888", true), ("222222", false)] do
    let pre := "\\palette{washed=#" ++ color ++ ",bg=#FFFFFF,fg=#222222}\n"
    let (translated, ds) := elabStr (dvDoc pre "{\\color{washed}Probe text.}")
    let (native, ns) := elabStr (dvDoc pre "\\textcolor{washed}{Probe text.}")
    for (label, notes, command, col, translation) in
        [("translated", ds, "\\color", 2, true),
         ("native", ns, "\\textcolor", 1, false)] do
      let caseLabel := s!"independent site facts {color}/{label}: "
      t (caseLabel ++ "no loss but the colour's own contrast")
        (notes.all fun d => d.severity == .note || d.kind == .W0315)
      for (kind, wanted) in [(DiagCode.N0100, translation), (.W0315, fails)] do
        let found := notes.filter fun d => d.kind == kind && !d.demoted
        t (caseLabel ++ kind.code ++ " occurs exactly when its condition holds")
          (found.size == if wanted then 1 else 0)
        t (caseLabel ++ kind.code ++ " retains its complete authored site")
          (found.all fun d => d.triggerText == some command &&
            d.span.any (fun s => s.file == "t" && s.pos.line == 4 &&
              s.pos.col == col && s.pos.sourceMapped))
      sources := sources.push (caseLabel, notes)
    let (th, tb, _) := HtmlDoc.emitTree {} translated
    let (nh, nb, _) := HtmlDoc.emitTree {} native
    t s!"independent site facts {color}: translation keeps the complete HTML artifact"
      (Html.document "en" th tb == Html.document "en" nh nb)
    t s!"independent site facts {color}: native spelling has no collision"
      (siteCollisions ns == #[])
    if fails then
      independentWitnesses := siteCollisions ds
      t "independent site facts: translation and the contrast report share their owning use"
        (independentWitnesses == #[("N0100", "W0315")])
    else
      t "independent site facts: translation alone has no collision" (siteCollisions ds == #[])
  let (_, keyedDs) := elabStr (dvDoc "\\definecolor{codestring}{HTML}{AA0000}\n" "x")
  let (_, nativeKeyDs) := elabStr (dvDoc "\\palette{codestring = #AA0000}\n" "x")
  let (_, plainDefDs) := elabStr (dvDoc "\\definecolor{plum}{HTML}{AA0000}\n" "x")
  t "independent site facts N0100/W0387: the native key alone is named, untranslated"
    (nativeKeyDs.any (·.kind == .W0387) && nativeKeyDs.all (·.kind != .N0100))
  t "independent site facts N0100/W0387: a translated colour of its own is translated, not named"
    (plainDefDs.any (·.kind == .N0100) && plainDefDs.all (·.kind != .W0387))
  independentWitnesses := independentWitnesses ++ siteCollisions keyedDs
  let some macroFace ← loadTestFont "OpenSans-Regular.ttf"
    | t "independent site facts W0005/W0386: the face loads" false
  let wide := String.ofList (List.replicate 70 'w')
  let laid (pre body : String) : Array Diag :=
    let (doc, ds) :=
      elabLocated "t" (dvDoc ("\\page{ width = 220pt, margin = 20pt }\n" ++ pre) body)
    ds ++ (layoutOf (oneFaceOf macroFace) doc).diags
  let macroOf (first last : String) : String :=
    "\\newcommand{\\zztwolines}{" ++ first ++ "\\\\ " ++ last ++ "}\n"
  let reflowing := "alpha beta " ++ wide ++ " gamma."
  let overrunning := "delta " ++ wide ++ " epsilon."
  let called := "Short.\\\\\n\\zztwolines"
  let both := laid (macroOf reflowing overrunning) called
  let reflowOnly := laid (macroOf reflowing "delta epsilon.") called
  let overrunOnly := laid (macroOf "alpha gamma." overrunning) called
  let written := laid "" ("Short.\\\\\n" ++ reflowing ++ "\\\\ " ++ overrunning)
  t "independent site facts W0005/W0386: the re-flow stands alone without the overrun"
    (reflowOnly.any (·.kind == .W0386) && !reflowOnly.any (·.kind == .W0005))
  t "independent site facts W0005/W0386: the overrun stands alone without the re-flow"
    (overrunOnly.any (·.kind == .W0005) && !overrunOnly.any (·.kind == .W0386))
  t "independent site facts W0005/W0386: written out, the re-flow and the overrun stand apart"
    (written.any (·.kind == .W0386) && written.any (·.kind == .W0005) &&
      siteCollisions written == #[])
  independentWitnesses := independentWitnesses ++ siteCollisions both
  -- A frame that continues and a band no page can hold are two losses at the frame's site.
  let framed (body : String) : Array Diag :=
    let (doc, ds) := elabLocated "t" ("\\documentclass{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}\n" ++ body ++ "\n\\end{frame}\n\\end{document}\n")
    let site : Span := { file := "t", pos := {} }
    let spans := doc.body.zipIdx.filterMap fun (b, i) => match b with
      | .frame .. => some (i, site)
      | _ => none
    ds ++ (Layout.runFitted (Layout.Geom.ofPage doc.page) (oneFaceOf macroFace) none doc {}
      spans).out.diags
  let continues := framed (String.join (List.replicate 40 "Kilo words.\n\n"))
  let overruns := framed "\\rule{1cm}{12cm}"
  let frameBoth := framed "Lima words.\n\n\\rule{1cm}{12cm}"
  t "independent site facts W0358/W0384: the continuation stands alone without the overrun"
    (continues.any (·.kind == .W0384) && !continues.any (·.kind == .W0358))
  t "independent site facts W0358/W0384: the overrun stands alone without the continuation"
    (overruns.any (·.kind == .W0358) && !overruns.any (·.kind == .W0384))
  independentWitnesses := independentWitnesses ++ siteCollisions frameBoth
  sources := sources.push ("a frame's box past its page on one step and overhang on another",
    sitedFitDiags (oneFaceOf macroFace) ("\\documentclass{beamer}\n\\begin{document}\n" ++
      "\\begin{frame}\n\\only<1>{\\rule{1cm}{263pt}}\n\\only<2>{\\rule{1cm}{300pt}}\n" ++
      "\\end{frame}\n\\end{document}\n"))
  t "site accounting: another information-code pair remains unclassified"
    (!sitePairClassified ("N0100", "N0200"))
  for pair in independentSiteFacts do
    t s!"independent site facts {pair.1}/{pair.2}: an executed control witnesses the row"
      (independentWitnesses.contains pair)
  for (src, what) in siteAccountingProbes do
    sources := sources.push (what, (elabStr src).2)
  for (src, what) in mdSiteAccountingProbes do
    sources := sources.push (what, dvMd src)
  let some face ← loadTestFont "OpenSans-Regular.ttf"
    | t "site accounting: the face loads" false
  let fs := oneFaceOf face
  for n in goldenNames do
    let (doc, ds) ← goldenDoc n
    let out := layoutOf fs doc (imgs := ← corpusStore doc)
    sources := sources.push (s!"fixture {n}", ds ++ out.diags)
  for (src, what) in layoutSiteAccountingProbes do
    let (doc, ds) := elabLocated "t" src
    sources := sources.push (what, ds ++ (layoutOf fs doc).diags)
  for (what, ds) in sources do
    for pair in siteCollisions ds do
      unless seen.contains pair do seen := pair :: seen
      unless sitePairClassified pair do
        t s!"site accounting {what}: {pair.1} and {pair.2} name one site, with no row" false
  for (a, b, _) in siteAccounting do
    t s!"site accounting {a}/{b}: the row still describes a live collision"
      (seen.contains (a, b))

/-- Documents whose body drops a leading `[...]` run, each with and without the run, and a preamble
site or none. -/
def visibleRunProbes : List (String × String × String × String) :=
  [("preamble first, one body site", "\\zzvis{x}\n",
     "Alpha \\zzvis[16]{Bravo}.", "Alpha \\zzvis{Bravo}."),
   ("preamble first, a run and a plain body site", "\\zzvis{x}\n",
     "Alpha \\zzvis[16]{Bravo}.\n\nDelta \\zzvis{Echo}.",
     "Alpha \\zzvis{Bravo}.\n\nDelta \\zzvis{Echo}."),
   ("body only, one site", "", "Alpha \\zzvis[16]{Bravo}.", "Alpha \\zzvis{Bravo}."),
   ("body only, a run and a plain site", "",
     "Alpha \\zzvis[16]{Bravo}.\n\nDelta \\zzvis{Echo}.",
     "Alpha \\zzvis{Bravo}.\n\nDelta \\zzvis{Echo}.")]

/-- Probes whose dropped run no default-visible line reflects, each with what owes the change. -/
def visibleRunAccounting : List (String × String) :=
  [("preamble first, one body site",
     "LeanTex/Core/Elab.lean, the declared-accounting change: the preamble \
and body refusals share ctrl:<name>, so the preamble's words stand for body sites"),
   ("preamble first, a run and a plain body site",
     "LeanTex/Core/Elab.lean, the declared-accounting change: as above, and the \
first body note carries the group's rule")]

/-- A dropped run shows at default verbosity: the visible lines differ with the run and without it,
or the probe has a row. -/
def visibleRunAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let visible (pre body : String) : Array (String × String × Option String) :=
    ((elabStr (dvDoc pre body)).2.filter (·.severity != .note)).map
      fun d => (d.code, d.message, d.help)
  for (what, pre, withRun, without) in visibleRunProbes do
    let hidden := visible pre withRun == visible pre without
    if visibleRunAccounting.any (·.1 == what) then
      t s!"visible run accounting {what}: the row still describes a hidden run" hidden
    else
      t s!"visible run {what}: a visible line reflects the dropped run" (!hidden)
  for (what, _) in visibleRunAccounting do
    t s!"visible run accounting {what}: the row names a probe"
      (visibleRunProbes.any (·.1 == what))

/-- A construct's recovery accounts for all of its arguments: a refused command's `[...]` run adds
no diagnostic, and the one left carries a subject and a wording true of every site. -/
def optionRunAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let subjOf (ds : Array Diag) (key : String) : Array Diag :=
    ds.filter (·.subject == some key)
  let visible (ds : Array Diag) : Array Diag := ds.filter (·.severity != .note)
  let codesOf (ds : Array Diag) : Array String := ds.foldl
    (fun acc d => if acc.contains d.code then acc else acc.push d.code) (#[] : Array String)
  let (_, two) := elabStr (dvDoc ""
    "Alpha \\zztrack[-11]{Bravo} charlie.\n\nDelta \\zztrack[16]{Echo} foxtrot.")
  t "option run: two calls with runs are two diagnostics, not four"
    (two.size == 2 && codesOf two == #["W0301"])
  t "option run: the command's own code is the only one naming it"
    ((subjOf two "ctrl:zztrack").size == 2 &&
      two.all fun d => d.code == "W0301" && d.subject == some "ctrl:zztrack")
  t "option run: one visible line carries the site total"
    ((visible (subjOf two "ctrl:zztrack")).size == 1 &&
      (visible (subjOf two "ctrl:zztrack")).all (·.sites == 2))
  t "option run: no span carries two codes"
    ((siteCollisions two).isEmpty)
  let mixedMsg (pre post : String) : Option String :=
    let (_, ds) := elabStr (dvDoc "" (pre ++ "\n\n" ++ post))
    let vis := visible (ds.filter (·.subject == some "ctrl:zzmix"))
    (vis[0]?).map (·.message)
  let runFirst := mixedMsg "Alpha \\zzmix[16]{Bravo} charlie." "Delta \\zzmix{Echo} foxtrot."
  let plainFirst := mixedMsg "Alpha \\zzmix{Bravo} charlie." "Delta \\zzmix[16]{Echo} foxtrot."
  t "option run: mixed shapes read the same in either order"
    (runFirst.isSome && runFirst == plainFirst)
  t "option run: the mixed line names the command, not one site's event"
    (runFirst == some "undefined command \\zzmix")
  let mixedHelp := ((visible ((elabStr (dvDoc "" ("Alpha \\zzmix[16]{Bravo} charlie.\n\n" ++
    "Delta \\zzmix{Echo} foxtrot."))).2.filter (·.subject == some "ctrl:zzmix")))[0]?).bind (·.help)
  t "option run: the mixed line's help says where a run's '[' belongs"
    (mixedHelp.any fun h => (h.splitOn "start the '[' on the next line").length == 2)
  let uniformMsg (body : String) : Option String :=
    let (_, ds) := elabStr (dvDoc "" body)
    let vis := visible (ds.filter (·.subject == some "ctrl:zzsame"))
    (vis[0]?).map (·.message)
  t "option run: a group of one shape keeps its own sentence"
    (match uniformMsg "Alpha \\zzsame[1]{Bravo}.\n\nDelta \\zzsame[2]{Echo}.",
           uniformMsg "Alpha \\zzsame{Bravo}.\n\nDelta \\zzsame{Echo}." with
     | some a, some b => a == "undefined command \\zzsame" && b == a
     | _, _ => false)
  let edgeLine (body : String) : Option String :=
    let (_, ds) := elabStr (dvDoc "" body)
    ((ds.filter (·.subject == some "ctrl:zzedge"))[0]?).map (·.message)
  let plain := edgeLine "\\zzedge{x}"
  let (openDoc, openDs) := elabStr (dvDoc "" "\\zzedge[16 oops")
  t "option run edge: an unclosed bracket is no run, so the line is the plain call's"
    (plain.isSome && edgeLine "\\zzedge[16 oops" == plain)
  t "option run edge: the unclosed bracket is named at its own span and kept as text"
    ((openDs.filter (·.code == "W0310")).size == 1 && (siteCollisions openDs).isEmpty &&
      hasStr (Ir.blockTextList "" openDoc.body.toList) "[16 oops")
  let (nextDoc, nextDs) := elabStr (dvDoc "" "\\zzedge\n[note] stays")
  t "option run edge: a bracket on the next line is content, so the line is the plain call's"
    (plain.isSome && edgeLine "\\zzedge\n[note] stays" == plain &&
      nextDs.all (·.code != "W0310") &&
      hasStr (Ir.blockTextList "" nextDoc.body.toList) "[note] stays")
  let redefVerdict (before : String) : Option String :=
    let (_, ds) := elabStr (dvDoc "" (before ++ "\n\n" ++
      "\\renewcommand{\\maketitle}{\\begin{zzbanner}x\\end{zzbanner} \\zzmix[1]{y}}" ++
      "\n\nDelta."))
    ((ds.filter (·.code == "W0361"))[0]?).map (·.message)
  t "redefinition trial: a recorded line index does not reach into the trial"
    (let withSite := redefVerdict "Alpha \\zzmix{Bravo} charlie."
     withSite.isSome && withSite == redefVerdict "Alpha charlie.")
  t "option run: every diagnostic of the refusal is inside the census"
    ((two.filter (·.code == "W0301")).all (·.subject.isSome))
  let (rDoc, runs) := elabStr (dvDoc "" "India \\zzplain{Juliett} kilo.")
  t "option run: a call with no run keys on the command alone"
    ((subjOf runs "ctrl:zzplain").size == 1)
  t "option run: the recovery is still paid for by that key"
    (rDoc.salvage.all fun s => runs.any fun d => d.subject == some s.subject)
  let (_, train) := elabStr (dvDoc "" "Lima \\zztrain[1][2]{Mike} november.")
  t "option run: two runs on one call are still one diagnostic"
    ((subjOf train "ctrl:zztrain").size == 1 && (siteCollisions train).isEmpty)
  let (_, pend) := elabStr (dvDoc "" "Golf \\footnotemark[3] hotel.")
  t "option run: a known pending construct is named only as pending"
    ((subjOf pend "ctrl:footnotemark").all (·.code == "W0370"))
  t "option run: nothing at a known construct's span claims it is unknown"
    (pend.all (·.code != "W0301") && (siteCollisions pend).isEmpty)
  t "option run: the fragment's own code is retired from the registry"
    ((DiagCode.ofString? "W0341").isNone)
  let (retDoc, retDs) := elabStr (dvDoc "\\allow{W0341}\n" "Alpha \\zzret[16]{Bravo}.")
  t "retired allow: a retired code is not an error"
    (retDs.all (·.code != "E0329"))
  t "retired allow: a folded fragment grants no acceptance"
    (retDoc.allow.isEmpty)
  t "retired allow: and says so, once, as a note"
    ((retDs.filter (·.code == "N0105")).size == 1 &&
      (retDs.filter (·.code == "N0105")).all (·.subject == some "allow:W0341"))
  let (wrDoc, wrDs) := elabStr (dvDoc "\\allow{W0341}\n"
    "Alpha \\zzspace[16]{Bravo} charlie.\n\nDelta \\zzother{Echo} foxtrot.")
  let wr := Diag.resolveAll wrDoc.allow false wrDs
  t "retired allow: an unrelated unknown command stays a warning under --werror"
    (wr.accepted.isEmpty && wr.warnings == 2 && exitFor wr.errors 0 wr.warnings true == 1)
  let (goneDoc, goneDs) := elabStr (dvDoc "\\allow{W0344}\n" "x")
  t "retired allow: a loss that cannot occur grants no acceptance"
    (goneDs.all (·.code != "E0329") && goneDoc.allow.isEmpty &&
      (goneDs.filter (·.code == "N0105")).size == 1)
  t "retired allow: an unknown code is still an error"
    (((elabStr (dvDoc "\\allow{W9999}\n" "x")).2).any (·.code == "E0329"))
  t "retired allow: no row names a live code"
    (DiagCode.retired.all fun r => (DiagCode.ofString? r.1).isNone)
  t "retired allow: every named successor is a live code"
    (DiagCode.retired.all fun r =>
      match r.2 with
      | some s => (DiagCode.ofString? s).isSome
      | none => true)
  let (renDoc, renDs) := elabStr (dvDoc "\\allow{E0382}\n" "x")
  t "renumbered allow: the old spelling accepts its successor, with a note"
    (renDoc.allow.contains "W0382" && renDs.all (·.code != "E0329") &&
      (renDs.filter (·.code == "N0105")).size == 1)
  let renRes := Diag.resolveAll renDoc.allow false
    #[DriverDiag.boundaryFailed "lualatex" "! an invented failure" (Ir.picSrcPrefix ++ "aa")]
  t "renumbered allow: the successor is accepted, so --werror passes"
    (Diag.acceptedLosses renRes.accepted == #["W0382"] && renRes.warnings == 0 &&
      exitFor renRes.errors 0 renRes.warnings true == 0)
  t "renumbered allow: rows name no live code, a live successor, and no retired row"
    (DiagCode.renumbered.all fun (old, succ) => (DiagCode.ofString? old).isNone &&
      (DiagCode.ofString? succ).isSome && (DiagCode.retired.lookup old).isNone)

/-- A run asking for the mono slot sets in the body face when no mono family is declared, and a
diagnostic speaks of the slot, which is true either way. -/
def monoSlotChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let (doc, ds) := elabStr (dvDoc "\\usepackage{url}\n\\urlstyle{same}\n"
    "A link \\url{https://example.org/a} here.")
  t "urlstyle: a satisfied selector draws no diagnostic"
    ((ds.filter (·.code == "W0104")).isEmpty)
  let famRuns (sty : Ir.Style) (d : Ir.Doc) : Nat :=
    Ir.foldBlocks (fun n _ => n) (fun n i => match i with
      | .styled s _ => if s == sty then n + 1 else n
      | _ => n) 0 d.body
  let monoRuns (d : Ir.Doc) : Nat := famRuns .mono d
  t "urlstyle: 'same' sets no family on the URL"
    (monoRuns doc == 0)
  let (ttDoc, _) := elabStr (dvDoc "\\usepackage{url}\n\\urlstyle{tt}\n"
    "A link \\url{https://example.org/a} here.")
  t "urlstyle: 'tt', url.sty's default, still sets the mono family"
    (monoRuns ttDoc == 1)
  let (sfDoc, _) := elabStr (dvDoc "\\usepackage{url}\n\\urlstyle{sf}\n"
    "A link \\url{https://example.org/a} here.")
  t "urlstyle: 'sf' sets the sans family, not the mono one"
    (monoRuns sfDoc == 0 && famRuns .sans sfDoc == 1)
  t "urlstyle: a value url.sty does not define is named under that value"
    (((elabStr (dvDoc "\\usepackage{url}\n\\urlstyle{zzbogus}\n"
        "A link \\url{https://example.org/a} here.")).2).any fun d =>
      d.code == "W0104" && d.subject == some "ctrl:urlstyle:zzbogus")
  let w104 (pre body : String) : Array Diag :=
    ((elabStr (dvDoc pre body)).2).filter (·.code == "W0104")
  let two := w104 "\\usepackage{url}\n\\urlstyle{zzfoo}\n\\urlstyle{zzbar}\n" "x"
  t "urlstyle: two undefined preamble values are two refusals, each its own"
    (two.size == 2 && two.all (fun d => d.sites == 1 && d.severity == .warning) &&
      two.map (·.subject) == #[some "ctrl:urlstyle:zzfoo", some "ctrl:urlstyle:zzbar"])
  let twoBody := w104 "\\usepackage{url}\n"
    "A \\urlstyle{zzfoo}\\url{https://example.org/a} and \\urlstyle{zzbar}\\url{https://example.org/b}."
  t "urlstyle: two undefined body values are two refusals, each its own"
    (twoBody.size == 2 && twoBody.all (fun d => d.sites == 1 && d.severity == .warning) &&
      twoBody.map (·.subject) == #[some "ctrl:urlstyle:zzfoo", some "ctrl:urlstyle:zzbar"])
  let same := w104 "\\usepackage{url}\n\\urlstyle{zzfoo}\n\\urlstyle{zzfoo}\n" "x"
  t "urlstyle: one undefined value at two sites is one refusal counted at both"
    (same.size == 2 && (same.map (·.sites)).toList == [2, 0] &&
      (same.filter (·.severity == .warning)).size == 1)
  -- `tt` is the default and cannot tell the orders apart, so it is not a row.
  let titled (pre : String) : Ir.Doc :=
    (elabStr (dvDoc ("\\usepackage{url}\n\\title{An Invented Title}\n" ++ pre)
      "\\maketitle\nBody text.")).1
  for (what, decl) in [("an author", "\\author{A. Person \\url{https://example.org/me}}\n"),
      ("a running head", "\\runninghead{\\url{https://example.org/head}}\n")] do
    for v in ["same", "rm", "sf"] do
      let sel := s!"\\urlstyle\{{v}}\n"
      t s!"urlstyle: {what} holding a URL reads '{v}' in either order"
        (titled (decl ++ sel) == titled (sel ++ decl))
  let twoSel := titled ("\\urlstyle{sf}\n\\author{A. Person \\url{https://example.org/me}}\n" ++
    "\\urlstyle{same}\n")
  t "urlstyle: a URL declared between two selectors takes the later one"
    (twoSel == titled ("\\author{A. Person \\url{https://example.org/me}}\n\\urlstyle{same}\n") &&
      famRuns .sans twoSel == 0)
  -- One face in every slot is the no-mono default; a distinct face in slot 2 is a declared mono.
  let load (name : String) : IO (Option Font) := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure (some f)
    | .error _ => pure none
  let some body ← load "SourceSerifPro-Regular.otf"
    | failures ref "mono slot: SourceSerifPro-Regular.otf missing"; return
  let some code ← load "SourceCodePro-Regular.otf"
    | failures ref "mono slot: SourceCodePro-Regular.otf missing"; return
  let slots (idx0 idx2 : Nat) : Array ((Nat × Nat × Bool) × Nat) :=
    #[((0, 400, false), idx0), ((1, 400, false), idx0), ((2, 400, false), idx2)]
  let collapsed : Font.FontSet := { fonts := #[body], index := slots 0 0 }
  let declared : Font.FontSet := { fonts := #[body, code], index := slots 0 1 }
  t "mono slot: no declared mono resolves the slot onto the body face"
    (collapsed.slotCollapsed 2)
  t "mono slot: a declared mono resolves the slot to its own face"
    (!declared.slotCollapsed 2)
  t "mono slot: the body slot is the reference" (!collapsed.slotCollapsed 0)
  -- An unresolved key still answers, so the predicate is about resolution, not a sparse index.
  t "mono slot: the collapse is the resolved equality"
    (collapsed.slotCollapsed 2 == (collapsed.lookup 2 400 false == collapsed.lookup 0 400 false))

/-- Each code's witness as written (`diagWitnessWith`, unrepeated). -/
def diagWitness (one mapped withMath : Font.FontSet) (probed : DiagCode → Array Diag) :
    DiagCode → Array Diag :=
  diagWitnessWith {} one mapped withMath probed

/-- A witness's source written twice: its body repeated at a second site a paragraph on, or its
whole text where it names no document. -/
def twice (src : String) : String :=
  -- Two lines down, behind a line of its own, two columns in: offset, line and column all differ.
  let elsewhere (body : String) : String :=
    let lead := (body.toList.takeWhile (· == '\n')).length
    String.ofList (List.replicate lead '\n') ++ "  " ++ (body.drop lead).toString
  match src.splitOn "\\begin{document}" with
  | [pre, rest] =>
    match rest.splitOn "\\end{document}" with
    | [body] =>
      let second := elsewhere body
      pre ++ "\\begin{document}" ++ body ++ "\n\n%\n" ++ second
    | body :: post =>
      let second := elsewhere body
      pre ++ "\\begin{document}" ++ body ++ "\n\n%\n" ++ second ++ "\\end{document}" ++
        "\\end{document}".intercalate post
    | [] => src
  | _ => src ++ "\n\nZzpad.\n\n" ++ src

/-- Censused codes whose emission carries no subject: a frozen baseline that may fall and never
rise. -/
def subjectDebt : List String :=
  ["W0003", "W0006", "W0007", "W0010", "W0011", "W0102",
   "W0310", "W0311", "W0312", "W0319", "W0320",
   "W0321", "W0325", "W0326", "W0327", "W0328", "W0330", "W0331", "W0332",
   "W0333", "W0335", "W0336", "W0338", "W0342", "W0352",
   "W0353", "W0358", "W0364", "W0366", "W0368", "W0369", "W0372",
   "W0377", "W0379", "W0380", "W0381", "W0388"]

/-- Every counted loss can be counted: a censused code's witness fires with a subject, or the code
is on `subjectDebt`, read both ways. -/
def subjectCensusChecks (ref : IO.Ref (List String))
    (one mapped withMath : Font.FontSet) (probed : DiagCode → Array Diag) : IO Unit := do
  let t := check ref
  let mut owing : List String := []
  for c in DiagCode.all do
    let fired := (diagWitness one mapped withMath probed c).filter (·.code == c.code)
    -- A code whose witness fires nothing is `diagVoiceChecks`' failure, not this block's.
    if c.censused && !fired.isEmpty then
      if (fired.filter (·.subject.isNone)).isEmpty then
        t s!"subject census {c.code}: a counted loss carries its subject" true
      else
        owing := c.code :: owing
        unless subjectDebt.contains c.code do
          t s!"subject census {c.code}: a counted loss with no subject, and no baseline row" false
  for code in subjectDebt do
    t s!"subject census {code}: the baseline row still describes a real gap"
      (owing.contains code)

/-- Codes the repetition cannot exercise, each with the one reason. -/
private def unexercisedAs (why : String) (codes : List String) : List (String × String) :=
  codes.map (·, why)

/-- Warning codes whose witness written twice carries no more records than written once, each with
why: a baseline that may fall and never rise. -/
def repeatFoldUnexercised : List (String × String) :=
  unexercisedAs "its construct is a preamble declaration, which the repetition does not write twice"
    ["W0007", "W0101", "W0102", "W0103", "W0104", "W0106", "W0111", "W0202", "W0303", "W0306",
     "W0312", "W0316", "W0317", "W0318", "W0319", "W0328", "W0329", "W0330", "W0331", "W0342",
     "W0343", "W0348", "W0354", "W0355", "W0357", "W0361", "W0363", "W0367", "W0368", "W0369",
     "W0373", "W0387", "W0398", "W0434", "W0442", "W0443", "W0109", "W0449"] ++
  unexercisedAs "its witness is the emitter's own record, with no source to write twice"
    ["W0006", "W0013", "W0378", "W0382", "W0391", "W0393", "W0394", "W0396", "W0403", "W0601",
     "W0602",
     "W0603", "W0604", "W0605", "W0609", "W0701"] ++
  unexercisedAs "one record per Lean declaration, which a file declares once"
    ["W0414", "W0415"] ++
  unexercisedAs "one record per declared phrase, in the directive a file reads once"
    ["W0416"] ++
  unexercisedAs "one record per Lean file whose link it owes, which a page reads once"
    ["W0431", "W0432"] ++
  unexercisedAs "its witness is the facts reader's own record, with no source to write twice"
    ["W0433"] ++
  unexercisedAs ("its witness is the emitter's own record, with no source to write twice; the \
font assembly's records are held by `weightSubstitutionRecordChecks`")
    ["W0366"] ++
  unexercisedAs "its witness is one driver run, with no source to write twice"
    ["W0008", "W0011", "W0379", "W0390", "W0419", "W0424", "W0503"] ++
  unexercisedAs ("one record per file, its sites the offsets in its detail; a second file is a \
second loss, named in its words")
    ["W0002", "W0004"] ++
  unexercisedAs "a layout record with no source, which the layout keeps once (`Layout.uniqueDiags`)"
    ["W0010", "W0336", "W0372"] ++
  unexercisedAs ("a layout record whose witness carries no picture source, which the layout \
keeps once (`Layout.uniqueDiags`)")
    ["W0335"] ++
  unexercisedAs "content after '\\end{document}' is one loss of the document, named once"
    ["W0001"] ++
  unexercisedAs "a fact of the font set, named once per document (`warnedMath`)"
    ["W0003"] ++
  unexercisedAs "a judgement of the page's measure, made once per document"
    ["W0201"] ++
  unexercisedAs "judged once per document: the outline walk keeps one latch per code"
    ["W0320", "W0321"] ++
  unexercisedAs "judged once per page: a repeated landmark is a fact of the page"
    ["W0325"] ++
  unexercisedAs "judged once per palette in force: the repetition adds frames, not palettes"
    ["W0345"] ++
  unexercisedAs "a judgement of the declared footer, which a second '\\framefoot' replaces"
    ["W0332"] ++
  unexercisedAs ("its declared lines are the preamble's '\\title', which a second \
'\\maketitle' sets again as one record")
    ["W0386"] ++
  unexercisedAs "one record per link target, which the repetition links again"
    ["W0326", "W0377"] ++
  unexercisedAs "one record per label key, which the repetition refers to again"
    ["W0349", "W0380"] ++
  unexercisedAs "one record per citation key, which the repetition cites again"
    ["W0351"] ++
  unexercisedAs "a loss of a reference-list entry, which the list sets once however often it is cited"
    ["W0420", "W0422", "W0423", "W0425", "W0426", "W0429"] ++
  unexercisedAs "a loss of the .bib file, read once however often the body cites it"
    ["W0352", "W0450"] ++
  unexercisedAs "a judgement of the bibliography style, made once per list"
    ["W0353"] ++
  unexercisedAs "one record per scheme, colour and ground, which the repetition paints again"
    ["W0308"] ++
  unexercisedAs "a judgement of the reference list's language, made once per list"
    ["W0421"] ++
  unexercisedAs "a judgement of the reference list's collation, made once per list"
    ["W0427"] ++
  unexercisedAs "a judgement of the written file against its declared standard, made once per file"
    ["W0444", "W0445"] ++
  unexercisedAs "a loss of the output intent's profile, read once per file however often it is named"
    ["W0446"] ++
  unexercisedAs "a judgement of the declared PDF version, made once per document"
    ["W0447"]

/-- A loss written twice is one line: every warning code's witness written twice prints no more
warning lines than once, or `repeatFoldUnexercised` names it. -/
def repeatFoldChecks (ref : IO.Ref (List String))
    (one mapped withMath : Font.FontSet) (probed : DiagCode → Array Diag) : IO Unit := do
  let t := check ref
  let mut exercised : Array String := #[]
  for located in [false, true] do
    for c in DiagCode.all do
      unless c.loss.severity.isWarning do continue
      let once := diagWitnessWith { located } one mapped withMath probed c
      let doubled := diagWitnessWith { rep := twice, located } one mapped withMath probed c
      unless (once.filter (·.kind == c)).size < (doubled.filter (·.kind == c)).size do continue
      unless exercised.contains c.code do exercised := exercised.push c.code
      let shown (ds : Array Diag) : Array String :=
        ((Diag.foldRepeats ds).filter fun d => d.kind == c && d.severity.isWarning).map (·.message)
      t s!"repeat fold {c.code}{if located then " (located)" else ""}: its witness written twice \
prints no more warning lines ({shown once} once, {shown doubled} twice)"
        ((shown doubled).size ≤ (shown once).size)
  for c in DiagCode.all do
    unless c.loss.severity.isWarning do continue
    let row := repeatFoldUnexercised.find? (·.1 == c.code)
    if exercised.contains c.code then
      t s!"repeat fold {c.code}: its witness repeats, so the baseline holds no row for it"
        row.isNone
    else
      t s!"repeat fold {c.code}: its witness written twice repeats nothing, and no baseline \
row says why" (row.any (!·.2.isEmpty))
  for (code, _) in repeatFoldUnexercised do
    t s!"repeat fold: the baseline row {code} names a warning code, once"
      ((DiagCode.all.filter fun c => c.code == code && c.loss.severity.isWarning).length == 1 &&
        (repeatFoldUnexercised.filter (·.1 == code)).length == 1)

/-- A refusal about a name carries that name in `Diag.refused`, and the set of such codes is closed
against the code list. -/
def nameRefusalRegistryChecks (ref : IO.Ref (List String))
    (one mapped withMath : Font.FontSet) (probed : DiagCode → Array Diag) : IO Unit := do
  let t := check ref
  let carriers := DiagCode.all.filter fun c =>
    (diagWitness one mapped withMath probed c).any fun d =>
      d.code == c.code && d.refused.isSome
  for c in carriers do
    t s!"name refusal {c.code}: a code whose witness refuses a name has a registry row"
      (Compat.nameRefusalAsk.any fun p => p.1.code == c.code)
  for (c, _) in Compat.nameRefusalAsk do
    t s!"name refusal {c.code}: a registry row's code really does refuse a name"
      (carriers.any fun k => k.code == c.code)
  -- The refused name is concatenated into a file name, so it must be the bare name.
  let (_, pDs) := elabStr (dvDoc "\\usepackage{zznosuchpackage}\n" "Placeholder body.")
  t "name refusal W0103: the refused package name is carried structurally"
    (pDs.any fun d => d.code == "W0103" && d.refused == some "zznosuchpackage")
  let (_, tDs) := elabStr (deck169 "\\theme{zznosuchtheme}\n" "\\maketitle\n")
  t "name refusal W0319: the refused theme name is carried structurally"
    (tDs.any fun d => d.code == "W0319" && d.refused == some "zznosuchtheme")
  let (_, uDs) := elabStr (dvDoc "" "Alpha \\zzunknown{beta} omega.")
  t "name refusal: a loss that is not a name-refusal carries no refused name"
    (uDs.all fun d => d.code != "W0301" || d.refused.isNone)

/-- Every registered code fires from its witness, and every fired form renders into the diagnostics
golden, one block per code, compared per block. -/
def diagVoiceChecks (ref : IO.Ref (List String)) (update : Bool) : IO Unit := do
  Tests.LayoutInkContracts.fixtureChecks ref
  let probed ← runDriverProbes
  for (c, ds) in probed do
    check ref s!"driver probe {c.code}: one row per code"
      ((driverProbes.filter (·.1 == c)).size == 1)
    check ref s!"driver probe {c.code}: the driver path still emits it"
      (ds.any (·.code == c.code))
  let probeOf (c : DiagCode) : Array Diag :=
    ((probed.find? (·.1 == c)).map (·.2)).getD #[]
  let load (name : String) : IO (Option Font) := do
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
    math := some 1
    mathAlphabets := fira.mathAlphabetCoverage {} }
  nameRefusalRegistryChecks ref one mapped withMath probeOf
  subjectCensusChecks ref one mapped withMath probeOf
  dvNumberSelfChecks ref
  dvFormSelfChecks ref
  for code in formDebt do
    match DiagCode.ofString? code with
    | some c =>
      check ref s!"form debt {code}: the baseline row still describes a real gap"
        (((diagWitness one mapped withMath probeOf c).filter (·.kind == c)).any (!dvFormOk ·))
    | none => failures ref s!"form debt {code}: names no code"
  repeatFoldChecks ref one mapped withMath probeOf
  let mut blocks : Array (String × String) := #[]
  for c in DiagCode.all do
    let fired := (diagWitness one mapped withMath probeOf c).filter (·.code == c.code)
    check ref s!"diag voice {c.code}: the witness fires it" (!fired.isEmpty)
    if dvInternalRef c.meaning then
      failures ref s!"diag voice {c.code} meaning: repo-internal reference: {c.meaning}"
    unless dvTerminalOk c.meaning do
      failures ref s!"diag voice {c.code} meaning: terminal punctuation: {c.meaning}"
    let mut block := s!"── {c.code} ({c.loss.label}) {c.meaning}\n"
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
  let path := "testdata/golden/diagnostics.txt"
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

/-- The `\allow` escape hatch: an unknown code is an error, a never-fired entry warns, and the
acceptance prints. -/
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

/-- The `--werror` exit-code matrix over the driver's own functions: errors are 1, failed assertions
2, and a warning 1 only under the flag, an accepted loss being no warning. -/
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
    (allowed.warnings == 0 && Diag.acceptedLosses allowed.accepted == #["W0104"] &&
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

/-- The accessibility judges: N0376 fires on an image with no text alternative and is silenced by
each escape, and `\assert{ accessibility = AA }` turns judged facts into one failing assertion. -/
def a11yChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let advice := Ir.altDiags (elabStr (dvDoc "" "\\includegraphics{chart.png}")).1
  t "missing alternatives are informational in the registry and emitted records"
    (advice.size == 1 && advice.all fun d =>
      d.code == "N0376" && d.kind.loss == .info && d.severity == .note)
  let resolved := Diag.resolveAll #[] false advice
  t "alternative advice is retained without affecting --werror"
    (resolved.diags == advice && resolved.accepted.isEmpty &&
      resolved.errors == 0 && resolved.warnings == 0 &&
      exitFor resolved.errors 0 resolved.warnings true == 0)
  t "alternative advice renders with the information icon and code"
    (advice.all fun d => (Render.human false d).startsWith "info: " &&
      ((Render.human false d).splitOn "[N0376]").length == 2)
  let (oldDoc, oldDs) := elabStr (dvDoc "\\allow{W0376}\n"
    "\\includegraphics{chart.png}")
  t "the former alternative warning migrates without granting acceptance"
    (oldDoc.allow.isEmpty && oldDs.all (·.severity != .error) &&
      oldDs.any (fun d => d.code == "N0105" && d.subject == some "allow:W0376") &&
      oldDs.any (·.code == "N0376"))
  t "an image with no text alternative fires N0376"
    ((dvE (dvDoc "" "\\includegraphics{chart.png}")).any (·.code == "N0376"))
  t "a declared alt silences N0376"
    (((dvE (dvDoc "" "\\includegraphics[alt={A synthetic chart}]{chart.png}")).any
      (·.code == "N0376")) == false)
  t "a figure caption becomes the alternative and silences N0376"
    (((dvE (dvDoc "" ("\\begin{figure}\\includegraphics{chart.png}" ++
        "\\caption{A synthetic chart}\\end{figure}"))).any
      (·.code == "N0376")) == false)
  let (routed, routedDs) := elabStr (dvDoc ""
    "\\begin{tikzpicture}\\draw (0,0) parabola (1,1);\\end{tikzpicture}")
  t "a default-routed boundary picture is counted, noted, and left to the driver's judge"
    ((Ir.imagesSansAlt routed).size == 1 &&
     routedDs.all (·.code != "N0376") && routedDs.any (·.code == "N0023"))
  let (bare, _) := elabStr (dvDoc "" "\\includegraphics{chart.png}")
  t "imagesSansAlt names the offending source"
    (Ir.imagesSansAlt bare == #["chart.png"])
  t "alt_judged_complete's face: judge silent iff census empty"
    ((Ir.altDiags bare).isEmpty == (Ir.imagesSansAlt bare).isEmpty &&
      !(Ir.altDiags bare).isEmpty)
  t "the judge names the image's own line"
    ((dvE (dvDoc "" "\\includegraphics{chart.png}")).any fun d =>
      d.code == "N0376" && d.span == some ⟨"t", { line := 3, col := 1 }⟩)
  let door := "\\pictures{ tool = lualatex }\n"
  let pic := "\\begin{tikzpicture}\\draw (0,0) parabola (1,1);\\end{tikzpicture}"
  let (picDoc, picDs) := elabStr (dvDoc door pic)
  t "elaboration leaves a boundary picture to the driver's judge"
    (picDs.all (·.code != "N0376"))
  let firedPic := Ir.picAltDiags picDoc (fun _ => none) (fun _ => true)
  t "a shipped picture with no alternative fires N0376 in the author's words"
    (firedPic.size == 1 && firedPic.all fun d =>
      (d.message.splitOn "picture").length == 2 &&
      (d.message.splitOn Ir.picSrcPrefix).length == 1)
  t "a picture the tool failed on is not double-named (W0382 spoke)"
    ((Ir.picAltDiags picDoc (fun _ => none) (fun _ => false)).isEmpty)
  t "a captioned figure around the picture silences the picture face"
    ((Ir.picAltDiags (elabStr (dvDoc door ("\\begin{figure}" ++ pic ++
        "\\caption{A synthetic diagram}\\end{figure}"))).1
      (fun _ => none) (fun _ => true)).isEmpty)
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
  let (gapped, gds) := elabStr (dvDoc ""
    "\\section{One}\nx\n\\subsubsection{Deep}\ny")
  t "outlineHasSkip names the fact W0320 fires on"
    (Ir.outlineHasSkip gapped && gds.any (·.code == "W0320"))
  let (failing, fds) := elabStr (dvDoc
    "\\assert{ accessibility = AA }\n\\pdfmeta{ language = \"en\" }\n"
    "\\includegraphics{chart.png}")
  t "accessibility = AA parses to its kind"
    (failing.asserts.any (·.kind == Ir.AssertKind.accessibilityAA))
  let shippedOf (doc : Ir.Doc) (ds : Array Diag) : Check.Shipped :=
    { pages := 1, fontsEmbedded := true, a11y := Check.a11ySummary doc ds }
  t "AA fails on a judged fact, naming the assertion"
    ((Check.all (shippedOf failing fds) failing.asserts).size == 1 &&
      (Check.all (shippedOf failing fds) failing.asserts).all
        (·.message.startsWith "failed assertion 'accessibility = AA"))
  let (clean, cds) := elabStr (dvDoc
    ("\\assert{ accessibility = AA }\n" ++
      "\\pdfmeta{ language = \"en\" }\n") "plain text")
  t "AA holds on a clean document with a declared language"
    ((Check.all (shippedOf clean cds) clean.asserts).isEmpty)
  let (nolang, nds) := elabStr (dvDoc "\\assert{ accessibility = AA }\n"
    "plain text")
  t "AA fails without a declared language"
    (!(Check.all (shippedOf nolang nds) nolang.asserts).isEmpty)

/-- The resolution gate: every element `Ir.pending` lists has a diagnostic whose subject names it,
no `.cite` survives `Bib.apply`, and the store covers every requested source. -/
def pendingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pic := "\\begin{tikzpicture}\\draw (0,0) parabola (1,1);\\end{tikzpicture}"
  let body := "See \\ref{none} and \\cite{none}.\n\n\\includegraphics{absent.png}\n\n" ++ pic
  let (doc, ds) := elabStr (dvDoc "\\usepackage{pgfplots}\n" body)
  let named (ds : Array Diag) (ps : Array Ir.Pending) : Bool :=
    ps.all fun p => ds.any (·.mentions p)
  t "pending: the elaborated document lists the ref and the cite"
    ((Ir.pendingNodes doc).contains (.ref "none") &&
     (Ir.pendingNodes doc).contains (.cite "none"))
  t "pending: elaboration names both, by subject (W0349, W0351)"
    (named ds ((Ir.pendingNodes doc).map .node) &&
     (ds.filter fun d => d.code == "W0349" && d.subject == some "none").size == 1 &&
     (ds.filter fun d => d.code == "W0351" && d.subject == some "none").size == 1)
  let (doc', bibDs) := Bib.apply #[] doc Bib.plainReading
  t "apply_no_cite: no .cite node survives resolution (no bibliography)"
    (bibDs.isEmpty && (Ir.pendingNodes doc').all (!·.isCite) &&
     (Ir.pendingNodes doc').contains (.ref "none"))
  let withBib := Bib.apply #[("refs", "@misc{other, year = 2024}")]
    { doc with body := doc.body.push (.bibliography "refs" none #[]) } Bib.plainReading
  t "apply_no_cite: no .cite node survives resolution (a bibliography without the key)"
    ((Ir.pendingNodes withBib.1).all (!·.isCite) &&
     (withBib.2.filter fun d => d.code == "W0351" && d.subject == some "none").size == 1)
  let picSrc := (Ir.imageRefs doc').find? (·.startsWith Ir.picSrcPrefix)
  t "pending: the picture's request stands in the image refs" picSrc.isSome
  let fetched : Array (String × Image.Fetch) := (Ir.imageRefs doc').map fun src =>
    if src.startsWith Ir.picSrcPrefix then
      (src, .refused (DriverDiag.boundaryFailed "lualatex" "! Undefined control sequence." src))
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
    (imgDs.any fun d => d.code == "W0382" && (picSrc.map fun s => d.subject == some s).getD false)
  let (ok, okDs) := elabStr (dvDoc "" "\\section{A}\\label{a} See \\ref{a}.")
  t "pending: a resolved reference is not pending, and W0349 stays silent"
    ((Ir.pending ok { entries := #[] }).isEmpty && okDs.all (·.code != "W0349"))

/-- The losses add up: a construct refused at several sites is named once with the total, each
further site a note at its own position. -/
def diagSiteCountChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let thrice := dvDoc "" "\\sloppy One.\n\n\\sloppy Two.\n\n\\sloppy Three."
  let ds := (elabStr thrice).2
  let of (code : String) (ds : Array Diag) : Array Diag := ds.filter (·.code == code)
  let visible (ds : Array Diag) : Array Diag := ds.filter (·.severity != .note)
  t "three sites of one construct are three diagnostics"
    ((of "W0104" ds).size == 3)
  t "three sites of one construct are one visible line"
    ((visible (of "W0104" ds)).size == 1)
  t "the visible line carries the site count"
    ((visible (of "W0104" ds)).all (·.sites == 3))
  t "every site is named at its own position"
    (((of "W0104" ds).filterMap fun d => d.span.map (·.pos.line)).toList == [3, 5, 7])
  t "every site of one loss carries the same subject"
    (((of "W0104" ds).map (·.subject)).toList.eraseDups.length == 1 &&
      (of "W0104" ds).all (·.subject.isSome))
  t "the count on the line is the number of diagnostics of that loss"
    ((visible (of "W0104" ds)).all fun d =>
      d.sites == (ds.filter (Diag.sameLoss d ·)).size)
  let helped := (elabStr (dvDoc ""
    "\\makebox[3cm]{One.}\n\n\\makebox[3cm]{Two.}\n\n\\makebox[3cm]{Three.}")).2
  t "the help is given once, at the first site"
    (((of "W0104" helped).filter (·.help.isSome)).size == 1 &&
      ((of "W0104" helped)[0]?.map (·.help.isSome)).getD false &&
      (of "W0104" helped).size == 3)
  let once := (elabStr (dvDoc "" "\\sloppy Only one.")).2
  t "a construct at one site carries no count and no note"
    ((of "W0104" once).size == 1 && (of "W0104" once).all fun d =>
      d.sites == 1 && d.severity != .note)
  let two := (elabStr (dvDoc ""
    "\\sloppy One.\n\n\\makebox[3cm]{Two.}\n\n\\makebox[3cm]{Three.}")).2
  t "two losses sharing a code keep their own counts"
    ((visible (of "W0104" two)).size == 2 &&
      ((visible (of "W0104" two)).map (·.sites)).toList == [1, 2])
  t "counting is idempotent"
    (Diag.tallySites ds == ds)
  t "counting neither adds nor drops a diagnostic"
    ((Diag.tallySites (of "W0104" two)).size == (of "W0104" two).size)
  let rendered := ((visible (of "W0104" ds))[0]?.map (Render.human false)).getD ""
  t "the rendered line states the total"
    (hasStr rendered "(3 sites)")
  t "a single site renders no total"
    (!hasStr (((of "W0104" once)[0]?.map (Render.human false)).getD "") "sites)")
  let porcelainSites (d : Diag) : Nat :=
    match (Render.porcelainDiag d).splitOn "\"sites\":" with
    | [_, rest] => (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat!
    | _ => 1
  t "porcelain: the first line carries the site count, the later ones none"
    (((of "W0104" ds).map porcelainSites).toList == [3, 0, 0])
  t "porcelain: the lines' counts add up to the run's diagnostics"
    ((ds.map porcelainSites).toList.sum == ds.size &&
      (ds.map (·.sites)).toList.sum == ds.size)
  t "the further sites are not warnings"
    ((Diag.resolveAll #[] false ds).warnings == (Diag.resolveAll #[] false once).warnings)
  let floats := (elabStr (dvDoc ""
    ("\\begin{figure}[htbp]\\caption{One.}\\end{figure}\n\n" ++
     "\\begin{table}[htbp]\\caption{Two.}\\end{table}"))).2
  t "two kinds of float each name their own ignored placement"
    (((of "N0102" floats).map (·.message)).toList.eraseDups.length == 2 &&
      (of "N0102" floats).all (·.sites == 1))
  let shorts := (elabStr (dvDoc ""
    "\\paragraph[One]{Paragraph one} x\n\n\\subparagraph[Two]{Subparagraph two} y")).2
  t "two heading levels each name their own unused short title"
    (((of "N0103" shorts).map (·.message)).toList.eraseDups.length == 2 &&
      (of "N0103" shorts).all (·.sites == 1))

/-- A census reads the structured fields, never the words: the porcelain line carries the code's
`loss` and the diagnostic's `subject`. -/
def porcelainCensusChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let field (k v : String) : String := "\"" ++ k ++ "\":\"" ++ v ++ "\""
  let misfiled := DiagCode.all.filter fun c =>
    !hasStr (Render.porcelainDiag (Diag.of c "m")) (field "loss" c.loss.label)
  t s!"porcelain: every code's line carries its declared loss ({misfiled.map (·.code)})"
    misfiled.isEmpty
  let (acc, accepted) := Diag.accept #["W0301"] false (Diag.of .W0301 "m")
  let accLine := Render.porcelainDiag acc
  t "porcelain: an accepted loss reads info and keeps its declared class"
    (accepted && hasStr accLine (field "severity" "info") && hasStr accLine (field "loss" "degraded"))
  let repeated := (elabStr (dvDoc "" "\\zzpcrep{a}\n\n\\zzpcrep{b}")).2.filter (·.code == "W0301")
  t "porcelain: a repeat site's note keeps its declared class"
    (repeated.size == 2 && repeated.any (·.severity == .note) &&
      repeated.all fun d => hasStr (Render.porcelainDiag d) (field "loss" "degraded"))
  let probes : List (String × String × String) :=
    [("ctrl:zzpccmd", "ctrl:zzpccmd", "Alpha \\zzpccmd{bravo} charlie."),
     ("env:zzpcenv", "env:zzpcenv", "\\begin{zzpcenv}Delta.\\end{zzpcenv}"),
     ("math:\\zzpcsym", "math:\\\\zzpcsym", "Echo $\\zzpcsym$ foxtrot.")]
  for (key, spelled, body) in probes do
    let ds := (elabStr (dvDoc "" body)).2
    t s!"porcelain: the {key} site's line carries its subject"
      (ds.any fun d => d.subject == some key &&
        hasStr (Render.porcelainDiag d) (field "subject" spelled))
  t "porcelain: a subjectless line carries no subject field"
    (!hasStr (Render.porcelainDiag (Diag.of .W0104 "m")) "\"subject\"")

/-- Recovered ink is marked in `Doc.salvage`: it fires exactly where the engine recovered, and every
entry is paid for by a diagnostic whose subject names the command. -/
def salvageChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let named (ds : Array Diag) (ss : Array Ir.Recovered) : Bool :=
    ss.all fun s => ds.any fun d => d.subject == some s.subject
  -- `zzunknown` is refused and `emph` read: the same ink, once salvage and once prose.
  let (doc, ds) := elabStr (dvDoc ""
    "Before \\zzunknown{zzsalvaged} and \\emph{zzauthored} after.")
  t "salvage: the refused command's group is recorded"
    (doc.salvage.any fun s => s.command == "zzunknown" && s.text == "{zzsalvaged}")
  t "salvage: a command the engine reads records nothing"
    (doc.salvage.all fun s => s.command != "emph")
  t "salvage: both words are in the ink, so the bytes cannot tell them apart"
    (let ink := Ir.blocksText doc.body
     hasStr ink "zzsalvaged" && hasStr ink "zzauthored")
  t "salvage_named: every recovery has a diagnostic naming its command"
    (named ds doc.salvage)
  t "salvage_named: the subject is the refusal's own key, not its words"
    (ds.any fun d => d.code == "W0301" && d.subject == some "ctrl:zzunknown")
  let (cDoc, cDs) := elabStr (dvDoc "" "Alpha \\zzsetlayout{fullpage} omega.")
  t "salvage: a control-plane keyword on the page is attributed to its command"
    (cDoc.salvage.any fun s =>
      s.command == "zzsetlayout" && hasStr s.text "fullpage" && s.code == DiagCode.W0301)
  t "salvage_named: the control-plane recovery is named too" (named cDs cDoc.salvage)
  let (eDoc, _) := elabStr (dvDoc "" "Alpha \\zznogroup omega.")
  t "salvage: a refusal that recovered nothing records nothing" eDoc.salvage.isEmpty
  let (kDoc, kDs) := elabStr (dvDoc "" "\\section{A}\\label{a} Plain \\emph{prose} only.")
  t "salvage: a document with nothing refused carries an empty census"
    (kDoc.salvage.isEmpty && kDs.all fun d => d.code != "W0301")
  for n in goldenNames do
    let (fDoc, fDs) ← goldenDoc n
    t s!"salvage_named {n}: every recovery is paid for by a diagnostic naming it"
      (named fDs fDoc.salvage)
    -- A diagnostic code is the unambiguous machinery word: no page may show one.
    t s!"salvage {n}: no recovered ink spells a diagnostic code"
      (fDoc.salvage.all fun s =>
        DiagCode.all.all fun c => !hasStr s.text c.code)

/-- Each list read from one source holds what is written out for it here, and each help naming a
set this suite reads names that set exactly. -/
def mirrorChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let named := Definer.table.map (·.name)
  t "definer table: each definer is one row" (named.eraseDups.length == named.length)
  -- Each definer's readings written out by hand, as the Definer queries holding it.
  let readings : List (List String × List String) :=
    [(["def"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners", "nameDefiners",
        "macroDefiners", "tex"]),
     (["gdef"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners", "nameDefiners",
        "macroDefiners", "tex", "global"]),
     (["edef"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners", "nameDefiners",
        "macroDefiners", "tex", "expands"]),
     (["xdef"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners", "nameDefiners",
        "macroDefiners", "tex", "expands", "global"]),
     (["let"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners", "nameDefiners",
        "macroDefiners"]),
     (["newcommand", "renewcommand"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners",
        "nameDefiners", "macroDefiners", "latex"]),
     (["DeclareRobustCommand"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners",
        "nameDefiners", "macroDefiners", "latex", "wrapper"]),
     (["providecommand"], ["namedNext", "bindsNext", "readAsDefinition", "nameDefiners",
        "macroDefiners", "latex", "provides"]),
     (["NewDocumentCommand", "RenewDocumentCommand", "DeclareDocumentCommand"], ["namedNext",
        "bindsNext", "readAsDefinition", "redefiners", "nameDefiners", "xparse"]),
     (["ProvideDocumentCommand"], ["namedNext", "bindsNext", "readAsDefinition", "nameDefiners",
        "xparse", "provides"]),
     (["newrobustcmd", "renewrobustcmd"], ["namedNext", "nameDefiners"]),
     (["providerobustcmd"], ["namedNext", "nameDefiners", "provides"]),
     (["NewCommandCopy", "RenewCommandCopy", "DeclareCommandCopy", "LetLtxMacro"], ["namedNext"]),
     (["define"], ["namedNext", "bindsNext", "readAsDefinition", "redefiners"]),
     (["defineenv"], ["bindsNext", "readAsDefinition", "tokenListEnvs"]),
     (["DeclareMathOperator"], ["bindsNext", "readAsDefinition"]),
     (["newenvironment", "renewenvironment"], ["readAsDefinition", "envs", "tokenListEnvs",
        "codeEnvs"]),
     (["provideenvironment"], ["envs", "tokenListEnvs"]),
     (["NewDocumentEnvironment", "RenewDocumentEnvironment", "DeclareDocumentEnvironment"],
        ["xparseEnvs", "envs"]),
     (["ProvideDocumentEnvironment"], ["envs"]),
     (["NewEnviron", "RenewEnviron"], ["readAsDefinition", "codeEnvs"]),
     (["newtcolorbox", "renewtcolorbox"], ["readAsDefinition"])]
  let written := readings.flatMap (·.1)
  let readers (q : String) : List String :=
    readings.flatMap fun (ds, qs) => if qs.contains q then ds else []
  let same (a b : List String) : Bool :=
    a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)
  t "definer table: its rows are the definers written out here" (same named written)
  let queries : List (String × List String) :=
    [("namedNext", Definer.namedNext), ("bindsNext", Definer.bindsNext),
     ("readAsDefinition", Definer.readAsDefinition), ("xparseEnvs", Definer.xparseEnvs),
     ("envs", Definer.envs), ("tokenListEnvs", Definer.tokenListEnvs),
     ("redefiners", Definer.redefiners), ("nameDefiners", Definer.nameDefiners),
     ("tex", Definer.commandsOf .tex), ("latex", Definer.commandsOf .latex),
     ("xparse", Definer.commandsOf .xparse), ("provides", named.filter Definer.provides),
     ("codeEnvs", Definer.codeEnvs), ("expands", named.filter Definer.expands),
     ("global", named.filter Definer.global),
     ("wrapper", named.filter fun n => (Definer.row? n).any (·.wrapper))]
  for (q, got) in queries do
    t s!"definer table: '{q}' holds the definers written out for it" (same got (readers q))
  t "definer table: 'macroDefiners' writes the definers written out for it"
    (same Definer.macroDefiners ((readers "macroDefiners").map ("\\" ++ ·)))
  t "definer table: each reading written out is a query's" (readings.all fun (_, qs) =>
    qs.all fun q => q == "macroDefiners" || queries.any (·.1 == q))
  t "definer table: a name no row holds provides nothing" (!Definer.provides "zznotadefiner")
  t "definer table: no definer is also a control row, read through a second registry"
    (Definer.table.all fun r => (Compat.ctrlRow? r.name).isNone)
  let rewrittenCtrls (src : String) : Array String :=
    (Compat.rewrite "t" (Parse.parse "t" (Lex.lex "t" src).1).1).1.filterMap fun r =>
      match r with | .ctrl n _ => some n | _ => none
  t "definer table: a math operator's definition naming no control word stays as written"
    ((rewrittenCtrls "\\DeclareMathOperator{zz}{x}").contains "DeclareMathOperator" &&
      (rewrittenCtrls "\\DeclareMathOperator{\\zz}").contains "DeclareMathOperator" &&
      !(rewrittenCtrls "\\DeclareMathOperator{\\zz}{x}").contains "DeclareMathOperator" &&
      (rewrittenCtrls "\\DeclareMathOperator{\\zz}{x}").contains "define")
  -- The lexer reads the token after a 'namedNext' definer as the name it defines, never a call.
  let verbatimAfter (d : String) : Bool :=
    (Lex.lex "t" ("\\" ++ d ++ "\\mintinline{x}")).1.any (·.tok matches .verb "mintinline" _)
  t "definer table: the lexer reads the name after exactly the 'namedNext' definers"
    ((written ++ ["zznotadefiner"]).all fun d =>
      verbatimAfter d == !(readers "namedNext").contains d)
  -- The boundary re-emits a definition its own family spells, an etoolbox one or a copy never.
  let reEmitted (src : String) : Bool :=
    !(Elab.macroScan (Parse.parse "t" (Lex.lex "t" src).1).1).isEmpty
  t "definer table: the boundary re-emits a TeX, LaTeX or xparse definition, no other"
    (reEmitted "\\def\\zzm{a}" && reEmitted "\\newcommand{\\zzm}{a}" &&
      reEmitted "\\NewDocumentCommand{\\zzm}{}{a}" && !reEmitted "\\newrobustcmd{\\zzm}{a}" &&
      !reEmitted "\\NewCommandCopy{\\zzm}{\\textbf}")
  -- Each command definer but the math operator's, written out with whether its macro expands.
  let commandProbes : List (String × String × Bool) :=
    (readers "tex").map (fun d => (d, s!"\\{d}\\zzm\{Zzbody}", true)) ++
    (readers "latex").map (fun d => (d, s!"\\{d}\{\\zzm}\{Zzbody}", true)) ++
    (readers "xparse").map (fun d => (d, s!"\\{d}\{\\zzm}\{}\{Zzbody}", true)) ++
    [("let", "\\newcommand{\\zzold}{Zzbody}\\let\\zzm\\zzold", true),
     ("define", "\\define \\zzm() {Zzbody}", true)] ++
    ["newrobustcmd", "renewrobustcmd", "providerobustcmd"].map (fun d =>
      (d, s!"\\{d}\{\\zzm}\{Zzbody}", false)) ++
    ["NewCommandCopy", "RenewCommandCopy", "DeclareCommandCopy", "LetLtxMacro"].map (fun d =>
      (d, s!"\\newcommand\{\\zzold}\{Zzbody}\\{d}\{\\zzm}\{\\zzold}", false))
  let commands := Definer.table.filter fun r =>
    r.defines == .command && r.name != "DeclareMathOperator"
  t "definer table: each command definer but the math operator's has a probe"
    (same (commandProbes.map (·.1)) (commands.map (·.name)))
  for (d, defn, expands) in commandProbes do
    let (doc, ds) := elabStr ("\\documentclass{article}\n" ++ defn ++
      "\n\\begin{document}\nAlpha \\zzm{} omega.\n\\end{document}\n")
    let shown := ((Ir.blocksText doc.body).splitOn "Zzbody").length - 1
    t s!"definer table: '\\{d}' {if expands then "defines a macro its use expands" else "is refused"}"
      (if expands then shown == 1 && !ds.any (·.kind == .W0301)
       else shown == 0 && ds.any (·.kind == .W0301))
  -- A `.bib` `@preamble` reads the LaTeX and TeX command definers, a providing one keeping a name.
  let bibReads (d : String) : Bool :=
    let src := if (readers "tex").contains d then s!"\\{d}\\zz\{Zzbody}"
      else s!"\\{d}\{\\zz}\{Zzbody}"
    Bib.expandMacros (Bib.preambleMacros #[src]) "\\zz" == "Zzbody"
  t "bib preamble: each LaTeX and TeX command definer defines its macro"
    ((readers "latex" ++ readers "tex").all bibReads && !bibReads "NewDocumentCommand")
  t "bib preamble: a providing definer keeps the macro standing"
    (Bib.expandMacros (Bib.preambleMacros #["\\newcommand{\\zz}{Zzold}",
      "\\providecommand{\\zz}{Zzbody}"]) "\\zz" == "Zzold")
  let keys := Ir.FontAxis.all.map (·.key)
  t "font axes: each axis has its own key" (keys.eraseDups.length == keys.length)
  let helpOf (code : DiagCode) (ds : Array Diag) : String :=
    ((ds.find? (·.kind == code)).bind (·.help)).getD ""
  -- A help listing a set ends in it after its colon, each member once, in the set's order.
  let names (help : String) (members : List String) : Bool :=
    ((help.splitOn ": ").getLastD "").splitOn ", " == members
  -- A help naming a set in a sentence spells it whole between `pre` and `post`, or after `pre` last.
  let spells (help pre joined post : String) : Bool :=
    (help.splitOn (pre ++ joined ++ post)).length > 1
  let ends (help pre joined : String) : Bool := help.endsWith (pre ++ joined)
  t "class help: an unknown class's help names every class"
    (names (helpOf .E0309 (dvE "\\documentclass{zzclass}\n\\begin{document}\nx\n\\end{document}"))
      (Ir.DocClass.all.map (·.name)))
  for (site, src) in [("babel", dvDoc "\\usepackage[zzlang]{babel}\n" "x"),
      ("pdfmeta", dvDoc "\\pdfmeta{ language = \"zz\" }\n" "x"),
      ("foreignlanguage", dvDoc "" "\\foreignlanguage{zzlang}{x}"),
      ("selectlanguage", dvDoc "" "\\selectlanguage{zzlang}x"),
      ("otherlanguage", dvDoc "" "\\begin{otherlanguage}{zzlang}x\\end{otherlanguage}")] do
    t s!"locale help: a language without a record, by {site}, names every shipped locale"
      (names (helpOf .W0368 (dvE src)) (Locale.builtin.map (·.tag)))
  t "size help: a size the style key cannot read names every size"
    (names (helpOf .E0323 (dvE (dvDoc "\\style{abstract}{ body-size = zzsize }\n" "x")))
      (Ir.sizeScale.map (·.1)))
  t "format help: an unknown output format names every backend"
    (names (helpOf .E0321 (dvE (dvDoc "\\output{ formats = zzformat }\n" "x"))) Ir.backendNames)
  t "style help: an unknown bibliography style names every style the engine knows"
    (names (helpOf .W0353 (dvBib "@misc{k, year = 2024}" "k" (some "zzstyle")))
      (Bib.Style.byName.map (·.1)))
  t "sorting help: an unknown biblatex sorting names every scheme sorted"
    (names (helpOf .W0101 (dvE (dvDoc "\\usepackage[sorting=zzsort]{biblatex}\n" "x")))
      CiteDecl.sortingSchemes)
  for (key, members) in [("alternatives", Ir.AltPolicy.byName.map (·.1)),
      ("color", Ir.ColorIntent.byName.map (·.1)), ("fonts", Ir.FontPolicy.byName.map (·.1))] do
    t s!"output help: an unknown '{key}' value names every value"
      (names (helpOf .E0321 (dvE (dvDoc s!"\\output\{ {key} = zzvalue }\n" "x"))) members)
  t "backend help: content addressed to no backend names every backend"
    (spells (helpOf .E0334 (dvE (dvDoc "" "\\begin{ifbackend}{zzbackend}x\\end{ifbackend}")))
      "of " (", ".intercalate Ir.backendNames) ";")
  t "class help: a document without a class names every class but the article"
    (spells (helpOf .N0017 (Elab.run "t.tex" "\\begin{document}\nx\n\\end{document}").2) "(or "
      (", ".intercalate ((Ir.DocClass.all.filter (· != .article)).map (·.name))) ")")
  t "list spacing help: a spacing key off a list names every spacing key"
    (spells (helpOf .W0104 (dvE (dvDoc "\\style{section}{ itemsep = 1pt }\n" "x"))) "reads "
      (Diag.prose "and" Ir.listSetKeys) " on")
  let codeRoles := Ir.Role.all.filterMap fun r => if r.code?.isSome then r.row.key else none
  t "code role help: minted's formatcom names every code role, each a palette key"
    (ends (helpOf .N0102 (dvE (dvDoc "\\usepackage{minted}\n"
        "\\begin{minted}[formatcom=\\color{red}]{python}\nx = 1\n\\end{minted}")))
      "by its name: " (Diag.prose "or" codeRoles) &&
      codeRoles.all fun r => (dvE (dvDoc s!"\\palette\{ {r} = #102030 }\n" "x")).isEmpty &&
      !(dvE (dvDoc "\\palette{ zzrole = #102030 }\n" "x")).isEmpty)
  t "citation style help: a markdown CSL key names every BibTeX style the engine knows"
    (ends (helpOf .W0307 (elabMd "---\ncsl: zz.csl\n---\n\nText.\n").2) "with "
      (Diag.prose "or" CiteDecl.bibtexStyles))
  let blockStyles := SeedPalette.Blocks.all.map (·.name)
  let seeds (entries : String) : String :=
    dvDoc s!"\\palette[seeds]\{ ink = #102030, paper = #F0F0F0, accent = #A03020{entries} }\n" "x"
  let seedHelp := helpOf .E0320 (dvE (seeds ", zz = #102030"))
  let listed := (((seedHelp.splitOn "seeds: ").getLastD "").splitOn ", and blocks = ").headD ""
  t "seed help: an unknown seed names every seed, each read, and the block styles"
    (ends seedHelp ", and blocks = " ("|".intercalate blockStyles) &&
      !listed.isEmpty && (listed.splitOn ", ").all fun k =>
        !(dvE (seeds s!", {k} = #102030")).any (·.kind == .E0320))
  let blockDs := dvE (seeds ", blocks = zz")
  t "block style help: an unknown block style names every style"
    (((blockDs.find? (·.kind == .E0321)).any fun d => d.message == "invalid value 'zz' for key blocks") &&
      helpOf .E0321 blockDs == ", or ".intercalate (blockStyles.map ("blocks = " ++ ·)))
  -- url.sty's `\urlstyle` values, written out.
  let urlStyles := ["tt", "rm", "sf", "same"]
  t "url style help: an unknown style names every url.sty style, each read"
    (helpOf .W0104 (dvE (dvDoc "" "\\urlstyle{zz}x")) ==
        "url.sty defines " ++ Diag.prose "and" urlStyles &&
      urlStyles.all fun u => !(dvE (dvDoc "" s!"\\urlstyle\{{u}}x")).any (·.kind == .W0104))
  t "url style message: a style left out names every url.sty style"
    ((dvE (dvDoc "" "x \\urlstyle")).any fun d => d.kind == .E0304 &&
      spells (saidText d) "a {" ("|".intercalate urlStyles) "} group")
  t "BibTeX styles: the surfaces' list is the reference list's, which sits above them"
    (Bib.Style.byName.map (·.1) == CiteDecl.bibtexStyles)
