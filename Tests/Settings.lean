module

public import Tests.Support
import LeanTex.Core.KeyVal

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

private instance : ToString Dim.Length := ⟨reprStr⟩

/-- The shipped pages of a document as one comparable value. -/
def pagesOf (fonts : Font.FontSet) (src : String) : String :=
  reprStr (layoutOf fonts (elabStr src).1).pages

/-- A body each parameter's site reads. -/
def settingsBodies : List (String × String) :=
  [("paras", "Alpha words here.\n\nBravo words here.\n\nCharlie words here."),
   ("figure", "Alpha words.\n\n\\begin{figure}[h]\\centering\nBravo box.\n" ++
      "\\caption{Charlie caption.}\\end{figure}\n\nDelta words."),
   ("center", "Alpha words.\n\n\\begin{center}\nBravo words.\n\\end{center}\n\nCharlie words."),
   ("note", "Alpha words.\\footnote{Bravo note.}\n\n" ++
      String.join (List.replicate 70 "Filler words for a full page.\n\n")),
   ("table", "Alpha words.\n\n\\begin{tabular}{ll}\\toprule\nAlpha & Bravo\\\\\n\\midrule\n" ++
      "Charlie & Delta\\\\\n\\cmidrule(lr){1-2}\nEcho & Foxtrot\\\\\n" ++
      "\\bottomrule\n\\end{tabular}\n\nBravo words."),
    ("columns", "\\begin{paracol}{2}Alpha words.\\switchcolumn Bravo words.\\end{paracol}"),
    ("rules", "\\begin{tabular}{ll}\\toprule\\toprule\nAlpha & Bravo\\\\\n" ++
      "\\bottomrule\n\\end{tabular}"),
   ("parlist", "Alpha words.\n\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n\n" ++
      "Charlie words."),
   ("list1", "Alpha words.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}\n" ++
      "\\begin{enumerate}\n\\item Charlie item.\n\\end{enumerate}"),
   ("list2", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\end{itemize}\n\\end{itemize}"),
   ("list3", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}"),
   ("list4", "\\begin{itemize}\n\\item Alpha\n\\begin{itemize}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{itemize}\n\\item Delta\n" ++
      "\\end{itemize}\n\\end{itemize}\n\\end{itemize}\n\\end{itemize}"),
   ("list5", "\\begin{itemize}\n\\item Alpha\n\\begin{enumerate}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{description}\n\\item Delta\n" ++
      "\\begin{quote}\nEcho\n\\end{quote}\n\\end{description}\n\\end{itemize}\n" ++
      "\\end{enumerate}\n\\end{itemize}"),
   ("list6", "\\begin{itemize}\n\\item Alpha\n\\begin{enumerate}\n\\item Bravo\n" ++
      "\\begin{itemize}\n\\item Charlie\n\\begin{description}\n\\item Delta\n" ++
      "\\begin{quote}\nEcho\n\\begin{quote}\nFoxtrot\n\\end{quote}\n\\end{quote}\n" ++
      "\\end{description}\n\\end{itemize}\n\\end{enumerate}\n\\end{itemize}"),
   ("display", "Alpha words before.\n\\[ x = y \\]\nBravo words after."),
   ("boxes", "Alpha \\fbox{Bravo} words."),
   ("displaylong", "Alpha words before this display reach past it.\n\\[ x = y \\]\n" ++
      "Bravo words after.")]

/-- One probe per carried `Compat.paramSites` row: the LaTeX spelling, the native spelling of the
same value, and the body that reads it. -/
def paramProbes : List (String × String × String × String) :=
  [("parskip", "\\setlength{\\parskip}{19pt}", "\\page{ parskip = 19pt }", "paras"),
   ("fboxsep", "\\setlength{\\fboxsep}{7pt}", "\\tokens{ fboxsep = 7pt }", "boxes"),
   ("fboxrule", "\\setlength{\\fboxrule}{2pt}", "\\tokens{ fboxrule = 2pt }", "boxes"),
   ("textwidth", "\\setlength{\\textwidth}{4in}", "\\page{ textwidth = 4in }", "paras"),
   ("headsep", "\\runninghead{Alpha head}\\setlength{\\headsep}{40pt}",
     "\\runninghead{Alpha head}\\page{ headsep = 40pt }", "paras"),
   ("footskip", "\\setlength{\\footskip}{50pt}", "\\page{ footskip = 50pt }", "paras"),
   ("textheight", "\\setlength{\\textheight}{500pt}", "\\page{ textheight = 500pt }", "paras"),
   ("floatsep", "\\setlength{\\floatsep}{30pt}", "\\tokens{ floatsep = 30pt }", "figure"),
   ("abovecaptionskip", "\\setlength{\\abovecaptionskip}{23pt}",
     "\\tokens{ captionsep = 23pt }", "figure"),
   ("topsep", "\\setlength{\\topsep}{17pt}", "\\tokens{ topsep = 17pt }", "center"),
   ("partopsep", "\\setlength{\\partopsep}{9pt}", "\\tokens{ partopsep = 9pt }", "parlist"),
   ("footins", "\\setlength{\\skip\\footins}{61pt}", "\\tokens{ footins = 61pt }", "note"),
    ("tabcolsep", "\\setlength{\\tabcolsep}{13pt}", "\\tokens{ tabcolsep = 13pt }", "table"),
    ("columnsep", "\\setlength{\\columnsep}{19pt}", "\\tokens{ columnsep = 19pt }", "columns"),
   ("heavyrulewidth", "\\setlength{\\heavyrulewidth}{3pt}",
     "\\tokens{ heavyrulewidth = 3pt }", "table"),
   ("lightrulewidth", "\\setlength{\\lightrulewidth}{2pt}",
     "\\tokens{ lightrulewidth = 2pt }", "table"),
   ("cmidrulewidth", "\\setlength{\\cmidrulewidth}{2pt}",
     "\\tokens{ cmidrulewidth = 2pt }", "table"),
   ("cmidrulekern", "\\setlength{\\cmidrulekern}{9pt}",
     "\\tokens{ cmidrulekern = 9pt }", "table"),
   ("aboverulesep", "\\setlength{\\aboverulesep}{7pt}", "\\tokens{ aboverulesep = 7pt }", "table"),
   ("belowrulesep", "\\setlength{\\belowrulesep}{7pt}", "\\tokens{ belowrulesep = 7pt }", "table"),
   ("abovetopsep", "\\setlength{\\abovetopsep}{9pt}", "\\tokens{ abovetopsep = 9pt }", "table"),
   ("belowbottomsep", "\\setlength{\\belowbottomsep}{9pt}",
     "\\tokens{ belowbottomsep = 9pt }", "table"),
   ("doublerulesep", "\\setlength{\\doublerulesep}{8pt}",
     "\\tokens{ doublerulesep = 8pt }", "rules"),
   ("leftmargini", "\\setlength{\\leftmargini}{61pt}", "\\tokens{ leftmargini = 61pt }", "list1"),
   ("leftmarginii", "\\setlength{\\leftmarginii}{47pt}", "\\tokens{ leftmarginii = 47pt }", "list2"),
   ("leftmarginiii", "\\setlength{\\leftmarginiii}{43pt}", "\\tokens{ leftmarginiii = 43pt }",
     "list3"),
   ("leftmarginiv", "\\setlength{\\leftmarginiv}{41pt}", "\\tokens{ leftmarginiv = 41pt }", "list4"),
   ("leftmarginv", "\\setlength{\\leftmarginv}{37pt}", "\\tokens{ leftmarginv = 37pt }", "list5"),
   ("leftmarginvi", "\\setlength{\\leftmarginvi}{31pt}", "\\tokens{ leftmarginvi = 31pt }",
     "list6")]

/-- Does a row's site carry the value onto the page: a page key, a token, or a list level the engine
nests to? -/
def carried : Compat.ParamSite → Bool
  | .page _ | .token _ | .boxScoped _ => true
  | .listIndent _ => true
  | .sizeReset _ | .listReset | .unmodelled _ => false

/-- A LaTeX length setting lands where LaTeX's own code puts it, for every `Compat.paramSites` row,
on the shipped page. -/
def paramSiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\usepackage{booktabs}\n" ++ pre ++
      "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let bodyOf (k : String) : String := (settingsBodies.lookup k).getD ""
  for (n, site) in Compat.paramSites do
    if carried site then
      t s!"paramSites: the carried row '{n}' has a probe"
        (paramProbes.any (·.1 == n))
  for (n, _) in paramProbes do
    t s!"paramSites: the probe '{n}' names a carried row"
      (((Compat.paramSites.lookup n).map carried).getD false)
  for (n, latex, native, bodyKey) in paramProbes do
    let body := bodyOf bodyKey
    let set := pagesOf oneFace (doc latex body)
    t s!"'{n}': the LaTeX setting sets the page its native spelling sets"
      (set == pagesOf oneFace (doc native body))
    t s!"'{n}': the setting moves the page" (set != pagesOf oneFace (doc "" body))
  -- What LaTeX sets again before anything reads it sets nothing here either.
  let reset := [("abovedisplayskip", "displaylong"), ("belowdisplayskip", "displaylong"),
    ("abovedisplayshortskip", "display"), ("belowdisplayshortskip", "display"),
    ("baselineskip", "paras"), ("itemsep", "list1"), ("parsep", "list1"),
    ("leftmargin", "list1"), ("itemindent", "list1")]
  for (n, bodyKey) in reset do
    let src := doc s!"\\setlength\{\\{n}}\{31pt}" (bodyOf bodyKey)
    t s!"'{n}' in the preamble sets the page the document sets without it"
      (pagesOf oneFace src == pagesOf oneFace (doc "" (bodyOf bodyKey)))
    t s!"'{n}' in the preamble says what LaTeX does with it"
      ((dvE src).any fun d => d.code == "N0100" &&
        d.subject == some s!"ctrl:nothing:setlength:{n}")
  -- In the body a display skip stands until the next size change: its token.
  -- A line ending short of the formula spends the short skips, a longer one the others.
  for (n, bodyKey) in [("abovedisplayskip", "displaylong"), ("belowdisplayskip", "displaylong"),
      ("abovedisplayshortskip", "display"), ("belowdisplayshortskip", "display")] do
    let body := bodyOf bodyKey
    let set := pagesOf oneFace (doc "" (s!"\\setlength\{\\{n}}\{31pt}\n\n" ++ body))
    t s!"a body '\\{n}' sets the page its token sets"
      (set == pagesOf oneFace (doc "" (s!"\\tokens\{ {n} = 31pt }\n\n" ++ body)))
    t s!"a body '\\{n}' moves the display it reaches" (set != pagesOf oneFace (doc "" body))
  for (n, site) in Compat.paramSites do
    if let .unmodelled _ := site then
      let ds := dvE (doc s!"\\setlength\{\\{n}}\{7pt}" "Alpha words.")
      t s!"'{n}' is named where it is set"
        ((ds.filter fun d => d.code == "W0104" &&
          d.subject == some s!"ctrl:setlength:{n}").size == 1)
  let every := String.intercalate "\n\n" (settingsBodies.map (·.2))
  for (n, site) in Compat.paramSites do
    if let .unmodelled _ := site then
      t s!"'{n}' named as unread sets nothing on the page"
        (pagesOf oneFace (doc s!"\\setlength\{\\{n}}\{7pt}" every) ==
          pagesOf oneFace (doc "" every))
  -- A zero indent is what the engine does: honoured, said so, never named.
  let flush := dvE (doc "\\setlength{\\parindent}{0pt}" "Alpha words.")
  t "a zero '\\parindent' is honoured, not named"
    (!flush.any (·.code == "W0104") &&
      flush.any (·.subject == some "ctrl:nothing:setlength:parindent"))


/-- Raws with each run of words and spaces one word of its text and every group's body alike, every
site the default: a carrier's shape, each operand one word. -/
private def mergedRuns : List Parse.Raw → String → Array Parse.Raw → Array Parse.Raw
  | [], run, out => flushRun run out
  | .word w _ :: rest, run, out => mergedRuns rest (run ++ w) out
  | .space :: rest, run, out => mergedRuns rest (run ++ " ") out
  | .group b _ :: rest, run, out =>
    mergedRuns rest "" ((flushRun run out).push (.group (mergedRuns b.toList "" #[]) {}))
  | r :: rest, run, out => mergedRuns rest "" ((flushRun run out).push (Compat.rebase (fun _ => {}) true r))
termination_by rs => sizeOf rs
decreasing_by raws_dec
where
  flushRun (run : String) (out : Array Parse.Raw) : Array Parse.Raw :=
    if run.trimAscii.isEmpty then out else out.push (.word run.trimAscii.toString {})

/-- A native setting a translation writes reaches the elaborator entry by entry: a value whose text
holds another entry sets nothing beyond its own key and is named dropped, every native a table
writes is carried whole, and a native head reads as its spelling. -/
def nativeCarrierChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let poster (width : String) : String :=
    "\\documentclass{beamer}\n\\usepackage[size=custom,width={" ++ width ++
      "},height=20]{beamerposter}\n\\begin{document}\n\\begin{frame}\nAlpha words.\n" ++
      "\\end{frame}\n\\end{document}"
  t "a poster width holding another entry sets no other page key"
    (pagesOf oneFace (poster "30, margin=1") == pagesOf oneFace (poster "30, gutter=1"))
  t "a poster width holding another entry drops the custom size, named"
    ((dvE (poster "30, margin=1")).any fun d => d.code == "W0367" && hasStr d.message "size=custom")
  let unnumbered := dvE (poster "abc")
  t "a poster width that is no number drops the custom size, named, and ships"
    (unnumbered.any (fun d => d.code == "W0367" && hasStr d.message "size=custom") &&
      !unnumbered.any (·.severity == .error))
  let geometry (opts : String) : String :=
    "\\documentclass{article}\n\\usepackage[" ++ opts ++ "]{geometry}\n\\begin{document}\n" ++
      "Alpha words.\n\\end{document}"
  t "a geometry value opening a bracket swallows no later key"
    (pagesOf oneFace (geometry "headsep={(1pt},margin=1in") == pagesOf oneFace (geometry "margin=1in"))
  t "a geometry value standing as no single entry is that key's loss"
    ((dvE (geometry "headsep={(1pt},margin=1in")).any fun d =>
      d.code == "W0104" && d.subject == some "param:usepackage:geometry:headsep")
  -- An option length is lowered as the length door lowers it.
  let lengthDoc (pre : String) : String :=
    "\\documentclass{scrartcl}\n\\makeatletter\\newlength{\\gap}\\setlength{\\gap}{1cm}\n" ++ pre ++
      "\n\\makeatother\n\\begin{document}\n\\section{Alpha}\nAlpha words.\n\\end{document}"
  for (spelled, plain) in [("\\usepackage[margin=1IN]{geometry}", "\\usepackage[margin=1in]{geometry}"),
      ("\\usepackage[left=2\\gap,right=2 \\gap]{geometry}", "\\usepackage[hmargin=2cm]{geometry}"),
      ("\\RedeclareSectionCommand[beforeskip=-3.5ex\\@plus -1ex \\@minus -.2ex]{section}",
        "\\RedeclareSectionCommand[beforeskip=-3.5ex plus -1ex minus -.2ex]{section}"),
      ("\\usepackage[top=\\z@, bottom=12\\p@]{geometry}", "\\usepackage[top=0pt, bottom=12pt]{geometry}")] do
    t s!"the option length {spelled.quote} sets what {plain.quote} sets"
      (pagesOf oneFace (lengthDoc spelled) == pagesOf oneFace (lengthDoc plain) &&
        !(dvE (lengthDoc spelled)).any (·.severity == .error))
  t "a geometry load setting no key sets geometry's default layout, 0.7 of the paper each way"
    (pagesOf oneFace (geometry "") == pagesOf oneFace (geometry "hscale=0.7, vscale=0.7") &&
      pagesOf oneFace (geometry "") != pagesOf oneFace (geometry "margin=1in") &&
      !(dvE (geometry "")).any (·.code == "W0104"))
  let hook := dvE ("\\documentclass{article}\n\\AddToHook{shipout/background}{}\n" ++
    "\\begin{document}\nAlpha words.\n\\end{document}")
  t "an empty shipout hook is noted as nothing, never warned"
    (hook.any (·.subject == some "ctrl:nothing:AddToHook:shipout/background") &&
      !hook.any (·.severity == .warning))
  let held : Native.Setting := .page #[(.margin, "1in, numbers = off"), (.parskip, "2pt")]
  t "a value holding another entry is dropped and the rest kept"
    (held.kept == .page #[(.parskip, "2pt")] && held.dropped == [("margin", "1in, numbers = off")])
  let whole (s : Native.Setting) : Bool := s.kept == s
  t "every lineno native carries whole" (Compat.linenoNatives.all (whole ·.2))
  t "every package option native carries whole"
    (Compat.packageOptionNatives.all (·.2.all (whole ·.2)))
  t "every control row's native carries whole"
    (Compat.ctrlRows.all fun row => match row.action with
      | .native s => whole s
      | .tokens .. | .skip _ | .refuse .. | .discard .. | .inert | .lower .. => true)
  -- A head's carrier is the lexer's reading of the spelling its note names, each operand one word.
  let lexed (src : String) : Array Parse.Raw :=
    mergedRuns (Parse.parse "head.tex" (Lex.lex "head.tex" src).1).1.toList "" #[]
  let heads : List Native.Head :=
    [.documentclass #[] "poster", .documentclass #["10pt", "aspectratio=169"] "slides",
     .theme "moloch", .theoremStyle "plain", .define "probe" "",
     .define "probe" "a1: content, a2?: content", .defineEnv "probe env" "a1: content",
     .textcolor "alert", .framefoot, .bibliography none #["refs"],
     .bibliography (some "plain") #["alpha", "beta"], .captionsetup none "font=small, labelfont=bf",
     .captionsetup (some "figure") "position=bottom", .runningFrom false 2, .runningFrom true 3]
  for h in heads do
    t s!"the head {h.render} is carried as the lexer reads it, each operand one word"
      (mergedRuns (h.raws {}).toList "" #[] == h.raws {} && lexed h.render == h.raws {})
  -- What the preamble's scan reads off a setting's carrier is its declaration with its kept block.
  let settings : List Native.Setting :=
    [.page #[(.margin, "2cm"), (.bleed, "3mm")], .tokens #[("gap", "1em plus 2pt")],
     .palette #[("accent", "#123456")], .style "section" #[("before", "1em"), ("after", "")],
     .fonts #[("body", "\"Example Serif\"")], .pdfmeta #[(.language, "\"fr\"")],
     .chrome #[("standout-note", "true")]]
  let declOf : Elab.PDecl → String
    | .page b _ => s!"page {b.map Parse.declSrc}"
    | .tokens b _ => s!"tokens {b.map Parse.declSrc}"
    | .palette _ b _ => s!"palette {b.map Parse.declSrc}"
    | .style args _ => s!"style {args.map fun (e, b) => (e, Parse.declSrc b)}"
    | .fonts b _ => s!"fonts {b.map Parse.declSrc}"
    | .pdfmeta b _ => s!"pdfmeta {b.map Parse.declSrc}"
    | .chrome b _ => s!"chrome {b.map Parse.declSrc}"
    | _ => "another declaration"
  for s in settings do
    let scanned := (Elab.scanDecls "setting.tex" (s.raws {})).map declOf
    let spelled := (Elab.scanDecls "setting.tex"
      (Parse.parse "setting.tex" (Lex.lex "setting.tex" (s.opening ++ "{" ++ s.kept.body ++ "}")).1).1).map declOf
    t s!"the setting {s.render} scans as its spelling's one declaration ({scanned}, {spelled})"
      (scanned.size == 1 && scanned == spelled && scanned.all (· != "another declaration"))
  -- A TeX-valued style's carrier is the lexer's reading of the spelling its note names.
  let lexedRaws (src : String) : Array Parse.Raw :=
    (Parse.parse "style.tex" (Lex.lex "style.tex" src).1).1
  let texStyles : List (String × Array (String × Native.StyleValue)) :=
    [("itemize", #[("marker", .tex (lexedRaws "\\num{12345}"))]),
     ("titlepage", #[("font", .tex (lexedRaws "\\bfseries\\color{red}")),
       ("author-font", .tex (lexedRaws "\\itshape x"))]),
     ("section", #[("before", .text "1em plus 2pt"), ("font", .tex (lexedRaws "\\Large")),
       ("after", .text "1ex")])]
  for (el, es) in texStyles do
    t s!"the style {Native.texStyleRender el es} is carried as the lexer reads it"
      (mergedRuns (Native.texStyle el es {}).toList "" #[] == lexed (Native.texStyleRender el es))
  -- Raws read as their spelling are the lexer's reading of it, but for a control space.
  let unsited (rs : Array Parse.Raw) : Array Parse.Raw := rs.map (Compat.rebase (fun _ => {}) true)
  for src in ["\\textbullet\n\n\\textbullet", "a\n\nb", "{ \\Large } x", "\\foo{ \\bar  {y} }z",
      "$ x $ { $ y $ }", "\\begin{center} a \\end{center}", "a \\hfill \\hfill b ", "{x\n\n} {}",
      "Alpha \\ldots Bravo {\\endash x}"] do
    let rs := lexedRaws src
    t s!"raws read as their spelling are the lexer's reading of it: {src.quote}"
      (unsited (Parse.trimSpace (Parse.asSpelled rs.toList #[])) == unsited (lexedRaws (Parse.rawSrc rs)))
  -- The raw reader reads a list as the string readers read its spelling, but where a formula or a
  -- control symbol holds a comma, which it keeps whole.
  let kvOf (src : String) : List (String × Option String) :=
    (Entries.read .keyval (lexedRaws src)).toList.map fun e => (e.key, e.value.map Parse.rawSrc)
  let nativeOf (src : String) : List (String × Option String) :=
    (Entries.read .native (lexedRaws src)).toList.map fun e => (e.key, e.value.map Parse.rawSrc)
  for src in ["a=1, b = {x,y}, c, d={}", "{k=v}, e=f=g, , h = {a}{b}", "w=\\textbf{x, y} z"] do
    t s!"the keyval reader reads {src.quote} as KeyVal does"
      (kvOf src == ((KeyVal.items (Parse.rawSrc (lexedRaws src))).toList.map KeyVal.entry))
  for src in ["a = 1, b = \"q, r\", c = [x, y], d = (1, 2)", "e = {x, y}, f =, g = h = i"] do
    t s!"the native reader reads {src.quote} as the declaration grammar does"
      (nativeOf src == ((Decl.splitEntries (Parse.rawSrc (lexedRaws src))).map fun e =>
        let (k, v) := Decl.entryOf e
        (k, if (KeyVal.cutAt '=' e.toList).2.isSome then some v else none)))
  t "an option list read from raws keeps a formula's comma in its item"
    (Entries.items .keyval (lexedRaws "label=$x,y$,z") == #["label=$x,y$", "z"] &&
      KeyVal.items (Parse.rawSrc (lexedRaws "label=$x,y$,z")) != #["label=$x,y$", "z"])
  t "a comma in a formula or a control symbol cuts no keyval entry"
    (kvOf "x=$a,b$, y=c\\,d" == [("x", some "$a,b$"), ("y", some "c\\,d")])
  -- A native declaration's reader keeps a formula whole, as its raws hold it.
  let declDiags (decl : String) : Array Diag :=
    (elabStr ("\\documentclass{article}\n" ++ decl ++ "\n\\begin{document}\nAlpha.\n\\end{document}")).2
  for decl in ["\\palette{ accent = #123456, ink = $a,b$ }", "\\pdfmeta{ subject = $a,b$ }",
      "\\tokens{ gap = 1em, zzwide = $a,b$ }", "\\output{ formats = pdf, css = $a,b$ }",
      "\\chrome{ footer = { left = $a,b$ } }"] do
    t s!"a formula's comma cuts no entry of {decl.quote}"
      (!(declDiags decl).any fun d => d.kind == .E0320)
  t "a native declaration's value holding a formula reads whole"
    ((Entries.read .native (lexedRaws "accent = #123456, ink = $a,b$")).toList.map (·.text) ==
      [("accent", "#123456"), ("ink", "$a,b$")])
  -- A passed option's spaces reach the package as the load's own option's do.
  let parskipped (pre : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nAlpha words.\n\nBravo words.\n\\end{document}"
  t "a passed parskip skip sets the skip the load's own option sets"
    (pagesOf oneFace (parskipped "\\PassOptionsToPackage{skip=5pt plus 1pt}{parskip}\n\\usepackage{parskip}") ==
      pagesOf oneFace (parskipped "\\usepackage[skip=5pt plus 1pt]{parskip}"))
  -- A style value's TeX holding an opening bracket swallows no later entry.
  let marked (styles : String) : String :=
    "\\documentclass{article}\n" ++ styles ++ "\n\\begin{document}\n\\begin{itemize}\n\\item One.\n" ++
      "\\end{itemize}\n\\end{document}"
  t "a marker holding a parenthesis leaves the indent beside it read"
    (pagesOf oneFace (marked "\\style{itemize}{ marker = {(}, indent = 4em }") ==
      pagesOf oneFace (marked "\\style{itemize}{ marker = {(} }\\style{itemize}{ indent = 4em }"))
  -- A style value is read as the raws Compat leaves, never as their spelling read again.
  let p0 : Pos := {}
  let markedStyle := lexedRaws "\\documentclass{article}\n" ++
    #[.ctrl "style" p0, .group #[.word "section" p0] p0,
      .group #[.word "font = " p0, .group #[.ctrl (Marker.name .ink "red") p0] p0] p0] ++
    lexedRaws "\n\\begin{document}\n\\section{Alpha}\nWords.\n\\end{document}"
  t "a style value's marker, which no spelling reads back, sets what its command sets"
    (reprStr (layoutOf oneFace (Elab.runRaws "style.tex" markedStyle).1).pages ==
      pagesOf oneFace ("\\documentclass{article}\n\\style{section}{ font = {\\color{red}} }\n" ++
        "\\begin{document}\n\\section{Alpha}\nWords.\n\\end{document}"))
  -- An option a load is passed carries its TeX as the load's own option does.
  let loaded (pre : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nWords.\n\\end{document}"
  let ownTitle := (elabStr (loaded "\\usepackage[pdftitle={\\textbf{Alpha} Guide}]{hyperref}")).1.info.title
  t "a passed hyperref title sets the title the load's own option sets"
    (ownTitle == some "Alpha Guide" && ownTitle == (elabStr (loaded
      "\\PassOptionsToPackage{pdftitle={\\textbf{Alpha} Guide}}{hyperref}\n\\usepackage{hyperref}")).1.info.title)
  let margin := "margin=\\dimexpr 1in+2pt\\relax"
  t "a passed geometry length sets the page the load's own option sets"
    (pagesOf oneFace (loaded s!"\\PassOptionsToPackage\{{margin}}\{geometry}\n\\usepackage\{geometry}") ==
      pagesOf oneFace (loaded s!"\\usepackage[{margin}]\{geometry}") &&
     pagesOf oneFace (loaded s!"\\usepackage[{margin}]\{geometry}") != pagesOf oneFace (loaded ""))
  -- A translated value of TeX reaches the passes reading Compat's output, as main's carrier did.
  let htmlPage (src : String) : String := (HtmlDoc.emit {} (elabStr src).1).1
  let siDeck := "\\documentclass{beamer}\n\\usepackage{siunitx}\n" ++
    "\\setbeamertemplate{itemize item}{\\num{12345}}\n\\begin{document}\n" ++
    "\\begin{frame}{Placeholder}\n\\begin{itemize}\n\\item First item.\n\\end{itemize}\n" ++
    "\\end{frame}\n\\end{document}"
  t "a marker template holding \\num sets the number siunitx groups"
    (hasStr (htmlPage siDeck) "content: \"12\u2009345  \"")
  let siList := "\\documentclass{article}\n\\usepackage{siunitx}\n\\usepackage{enumitem}\n" ++
    "\\setlist[itemize]{label=\\SI{2}{\\metre}}\n\\begin{document}\n\\begin{itemize}\n" ++
    "\\item First item.\n\\end{itemize}\n\\end{document}"
  t "a list label holding \\SI sets the quantity siunitx spaces"
    (hasStr (htmlPage siList) "content: \"2\u202Fm  \"")
  let quotedFont := "\\documentclass{beamer}\n\\setbeamerfont{block title}{family=\\char\"41}\n" ++
    "\\begin{document}\n\\begin{frame}{Placeholder}\n\\begin{block}{Title}\nBody words.\n" ++
    "\\end{block}\n\\end{frame}\n\\end{document}"
  t "a beamer font holding a quote is carried as TeX, none of it dropped"
    (!(dvE quotedFont).any (·.code == "W0101"))
  -- An empty translated value reaches its reader, which refuses it as it refuses the author's.
  let doc (cls pre body : String) : String :=
    "\\documentclass{" ++ cls ++ "}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  t "an empty skip is refused as a block entry with no value"
    ((dvE (doc "article" "" "Before.\n\\vspace{}\nAfter.")).any fun d =>
      d.code == "E0320" && hasStr d.message "has no value")
  t "an empty section skip is refused as an invalid style entry"
    ((dvE (doc "scrartcl" "\\RedeclareSectionCommand[beforeskip=, afterskip=1ex]{section}"
      "\\section{One}\nWords.")).any fun d => d.code == "E0320" && hasStr d.message "invalid entry")
  -- A skip whose width stands as no entry is dropped whole, its stretch with it.
  let commaSkip := doc "article" "" "Top line.\n\\vspace{1,5cm plus 1fill}\nBottom line."
  t "a skip whose width stands as no entry sets the page its absence sets"
    (pagesOf oneFace commaSkip == pagesOf oneFace (doc "article" "" "Top line.\n%\nBottom line."))
  t "a skip whose width stands as no entry is named dropped"
    ((dvE commaSkip).any (·.code == "W0101"))

/-- A parameter set in a loaded style file ships the page its document spelling ships; only the
diagnostic's severity moves. -/
def paramDemoteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let sub (file src : String) : Array Parse.Raw := (Parse.parse file (Lex.lex file src).1).1
  let setting := "\\setlength{\\footnotesep}{7pt}\n"
  let head := sub "main.tex" "\\documentclass{article}\n"
  let tail := sub "main.tex" "\\begin{document}\nAlpha words.\\footnote{Bravo note.}\n\\end{document}"
  let (dSty, dsSty) := Elab.runRaws "main.tex"
    (head ++ #[Parse.Raw.env (Parse.inputEnv "venue.sty") (sub "venue.sty" setting)
      { line := 2, col := 1 }] ++ tail)
  let (dOwn, dsOwn) := Elab.runRaws "main.tex" (head ++ sub "main.tex" setting ++ tail)
  let named (ds : Array Diag) := ds.filter (·.subject == some "ctrl:setlength:footnotesep")
  t "a style file's parameter ships the page the document's does"
    (reprStr (layoutOf oneFace dSty).pages == reprStr (layoutOf oneFace dOwn).pages)
  t "a style file's parameter is a note, the document's a warning"
    ((named dsSty).map (·.severity) == #[.note] && (named dsOwn).map (·.severity) == #[.warning])


/-- A redefined `\normalsize` sets the document's display skips, and a size command in the preamble
sets nothing. -/
def sizeCommandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let body := "Alpha words before the display, long enough to fill a line of text here.\n" ++
    "\\[ x = y \\]\nBravo words after the display."
  let redef (skips : String) : String :=
    "\\makeatletter\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xipt\n" ++
      skips ++ "}\\makeatother"
  let skips := "\\abovedisplayskip 3\\p@ \\@plus 2\\p@ \\@minus 1\\p@\n" ++
    "\\abovedisplayshortskip \\z@ \\@plus 3\\p@\n\\belowdisplayskip \\abovedisplayskip\n"
  let native := "\\page{ fontsize = 10pt, leading = 0.913 }" ++
    "\\tokens{ abovedisplayskip = 3pt plus 2pt minus 1pt, belowdisplayskip = abovedisplayskip }"
  let set := pagesOf oneFace (doc (redef skips) body)
  t "a redefined \\normalsize ships as its native size and skips do"
    (set == pagesOf oneFace (doc native body))
  t "a redefined \\normalsize's display skips move the page"
    (set != pagesOf oneFace (doc (redef "") body))
  for name in ["normalsize", "small"] do
    let src := doc s!"\\{name}" body
    t s!"a preamble '\\{name}' sets the page the document sets without it"
      (pagesOf oneFace src == pagesOf oneFace (doc "" body))
    t s!"a preamble '\\{name}' says what LaTeX does with it, and is not unknown"
      ((dvE src).any (·.subject == some s!"ctrl:nothing:size:{name}") &&
        !(dvE src).any (·.code == "W0301"))
  -- A copy of a class skip is unknown here: named once, the skip keeping its value.
  let copy := doc (redef "\\belowdisplayskip\\abovedisplayskip\n") body
  let cds := dvE copy
  t "a redefined \\normalsize copying a skip it does not set builds"
    (!cds.any (·.severity == .error))
  t "a \\normalsize copying a skip it does not set names the copy once"
    ((cds.filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:belowdisplayskip"])
  t "a \\normalsize copying a skip it does not set ships the page without it"
    (pagesOf oneFace copy == pagesOf oneFace (doc (redef "") body))


/-- A counter set in the preamble holds where the body starts, and `secnumdepth` decides which
headings number. -/
def counterChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let heads := "\\section{Alpha}\nOne.\n\n\\subsection{Bravo}\nTwo."
  let shallow := pagesOf oneFace (doc "\\setcounter{secnumdepth}{1}" heads)
  -- An unnumbered subsection still holds its bookmark, as hyperref's does; a starred one does not.
  let unanchored (src : String) : String :=
    reprStr ((layoutOf oneFace (elabStr src).1).pages.map fun (p : Layout.PageOut) =>
      { p with lines := p.lines.map fun (l : Layout.LineOut) => { l with anchors := #[] } })
  t "secnumdepth 1 sets a subsection the page a starred one sets, its bookmark aside"
    (unanchored (doc "\\setcounter{secnumdepth}{1}" heads) ==
      unanchored (doc "" "\\section{Alpha}\nOne.\n\n\\subsection*{Bravo}\nTwo."))
  t "secnumdepth moves the page" (shallow != pagesOf oneFace (doc "" heads))
  let deeper := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{1}"
    (heads ++ "\n\n\\setcounter{secnumdepth}{2}\n\\subsection{Charlie}\nThree."))
  t "a heading above secnumdepth steps nothing: the next numbered one is 1.1"
    (pageHas deeper 0 "1.1" && !pageHas deeper 0 "1.2")
  let note := "Alpha words.\\footnote{Bravo note.}"
  t "a preamble footnote counter numbers the next note after it"
    (pagesOf oneFace (doc "\\setcounter{footnote}{4}" note) ==
      pagesOf oneFace (doc "" "Alpha words.\\footnote[5]{Bravo note.}"))
  let eq := censusOfSrc oneFace (doc "\\addtocounter{equation}{6}"
    "Alpha.\n\\begin{equation}\nx = y\n\\end{equation}")
  t "a preamble equation counter numbers the next equation after it" (pageHas eq 0 "(7)")
  -- A counter set in the body is left where it stands, so numbers only what follows it.
  t "a body counter numbers from where it stands, a preamble one from the body's start"
    (!pageHas (censusOfSrc oneFace (doc "" "\\section{Alpha}\nOne.\n\n\\setcounter{section}{4}\n\
\\section{Bravo}\nTwo.")) 0 "6" &&
      pageHas (censusOfSrc oneFace (doc "\\setcounter{section}{4}" "\\section{Alpha}\nOne.\n\n\
\\section{Bravo}\nTwo.")) 0 "6")
  t "a preamble counter command is not unknown"
    (!(dvE (doc "\\setcounter{secnumdepth}{1}\\stepcounter{footnote}" heads)).any
      (·.code == "W0301"))
  t "an unkept preamble counter is named as in the body"
    ((dvE (doc "\\setcounter{totalnumber}{2}" heads)).any fun d =>
      d.code == "W0104" && d.subject == some "ctrl:setcounter:totalnumber")
  -- Kernel constant registers read as their integers (plain.tex); any other register is named once.
  let zero := doc "\\makeatletter\\setcounter{secnumdepth}{\\z@}\\makeatother" heads
  t "a counter set to '\\z@' builds and reads zero"
    (!(dvE zero).any (·.severity == .error) &&
      pagesOf oneFace zero == pagesOf oneFace (doc "\\setcounter{secnumdepth}{0}" heads))
  t "a counter set to '\\z@' moves the page" (pagesOf oneFace zero != pagesOf oneFace (doc "" heads))
  let reg := doc "\\makeatletter\\setcounter{secnumdepth}{\\@tempcnta}\\makeatother" heads
  t "a counter set to an unreadable register builds, named once"
    (!(dvE reg).any (·.severity == .error) &&
      ((dvE reg).filter (·.code == "W0104")).map (·.subject) ==
        #[some "ctrl:setcounter:secnumdepth:value"])
  t "a counter set to a register it cannot read keeps its value"
    (pagesOf oneFace reg == pagesOf oneFace (doc "" heads))
  -- `secnumdepth` past three numbers the run-in levels (`\paragraph` four, `\subparagraph` five), each after its parent.
  let runIn := "\\section{Alpha}\\subsection{Bravo}\\subsubsection{Charlie}\n" ++
    "\\paragraph{Delta} Echo words.\n\n\\subparagraph{Foxtrot} Golf words."
  let four := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{4}" runIn)
  t "secnumdepth 4 numbers a paragraph after its parent" (pageHas four 0 "1.1.1.1")
  t "secnumdepth 4 leaves a subparagraph unnumbered" (!pageHas four 0 "1.1.1.1.1")
  let five := censusOfSrc oneFace (doc "\\setcounter{secnumdepth}{5}" runIn)
  t "secnumdepth 5 numbers a subparagraph after its parent" (pageHas five 0 "1.1.1.1.1")
  t "the class's secnumdepth numbers no paragraph"
    (!pageHas (censusOfSrc oneFace (doc "" runIn)) 0 "1.1.1.1")


/-- A list level's parameters are its class macro's, run where a list of that depth opens. -/
def listLevelChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\makeatletter\n" ++ pre ++
      "\n\\makeatother\n\\begin{document}\n" ++ body ++ "\n\\end{document}"
  let body := "Alpha words.\n\n\\begin{itemize}\n\\item One.\n\\item Two.\n" ++
    "\\begin{itemize}\n\\item Three.\n\\item Four.\n\\end{itemize}\n\\item Five.\n" ++
    "\\end{itemize}\n\nBravo words."
  let keep := "\\renewcommand{\\normalsize}{\\@setfontsize\\normalsize\\@xpt\\@xiipt}\n"
  let params := "\\setlength{\\topsep}{9pt plus 1pt minus 2pt}\n" ++
    "\\setlength{\\itemsep}{3pt plus 1pt}\n\\setlength{\\parsep}{2pt plus 1pt}\n" ++
    "\\setlength{\\leftmargin}{40pt}\n\\setlength{\\leftmargini}{\\leftmargin}\n"
  let listi := "\\def\\@listi{\\leftmargin\\leftmargini}\n"
  let outer := "\\tokens{ leftmargini = 40pt }\\style{itemize}{ before = 9pt plus 1pt minus 2pt, " ++
    "gap = 5pt plus 2pt }\\style{enumerate}{ before = 9pt plus 1pt minus 2pt, gap = 5pt plus 2pt }"
  let kept := pagesOf oneFace (doc (keep ++ params ++ listi) body)
  t "a kept \\@listi sets the outermost lists the page their native styles set"
    (kept == pagesOf oneFace (doc ("\\page{ fontsize = 10pt, leading = 1 }" ++ outer) body))
  t "a kept \\@listi moves the page" (kept != pagesOf oneFace (doc (keep ++ params) body))
  t "a class's \\normalsize resets \\@listi: the redefinition sets nothing"
    (pagesOf oneFace (doc (params ++ listi) body) == pagesOf oneFace (doc params body))
  let listii := "\\setlength{\\leftmarginii}{30pt}\n\\def\\@listii{\\leftmargin\\leftmarginii\n" ++
    "\\labelwidth\\leftmarginii \\advance\\labelwidth-\\labelsep\n" ++
    "\\topsep 4\\p@ \\@plus 1\\p@ \\parsep 1.5\\p@ \\itemsep \\parsep}\n"
  let inner := "\\tokens{ leftmarginii = 30pt }" ++
    "\\style{itemize2}{ before = 4pt plus 1pt, gap = 3pt }" ++
    "\\style{enumerate2}{ before = 4pt plus 1pt, gap = 3pt }"
  let second := pagesOf oneFace (doc listii body)
  t "a redefined \\@listii sets the second level the page its native style sets"
    (second == pagesOf oneFace (doc inner body))
  t "a redefined \\@listii moves the page"
    (second != pagesOf oneFace (doc "\\setlength{\\leftmarginii}{30pt}" body))
  let ds := dvE (doc listii body)
  t "a list level's arithmetic is read with it; unread settings are named once"
    (!ds.any (·.subject == some "ctrl:advance") &&
      (ds.filter (·.subject == some "ctrl:setlength:labelwidth")).size == 1)
  -- A body assignment between two lists reaches the second only where the level's macro leaves it be.
  let between (set : String) : String :=
    "Alpha words.\n\\begin{itemize}\n\\item One.\n\\item Two.\n\\end{itemize}\n" ++ set ++
      "\nBravo words.\n\\begin{itemize}\n\\item Three.\n\\item Four.\n\\end{itemize}\nCharlie."
  for (set, names) in [("\\setlength{\\topsep}{9pt}", #["topsep"]),
      ("\\setlength{\\itemsep}{0pt}\\setlength{\\parsep}{0pt}", #["itemsep", "parsep"])] do
    let kds := dvE (doc (keep ++ listi) (between set))
    t s!"a kept \\@listi and a body '{set}' build" (!kds.any (·.severity == .error))
    t s!"a kept \\@listi and a body '{set}' name the lists they cannot reach, once each"
      ((kds.filter (·.code == "W0104")).map (·.subject) ==
        names.map fun n => some s!"ctrl:setlength:{n}")
    t s!"the naming gate's premise: no list here reads a body '{set}' under a kept \\@listi"
      (pagesOf oneFace (doc (keep ++ listi) (between set)) ==
        pagesOf oneFace (doc (keep ++ listi) (between "")))
  let cls := doc listi (between "\\setlength{\\itemsep}{0pt}")
  t "under the class's \\@listi a body \\itemsep reaches no list, and says so"
    (!(dvE cls).any (·.code == "W0104") &&
      (dvE cls).any (·.subject == some "ctrl:nothing:setlength:itemsep") &&
      pagesOf oneFace cls == pagesOf oneFace (doc listi (between "")))



/-- Every LaTeX-valid length setting builds: one the door reads holds its value, one it cannot read
is named once and changes nothing. -/
def unreadableLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let doc (pre body : String) : String :=
    "\\documentclass{article}\n\\usepackage{calc}\n" ++ pre ++ "\n\\begin{document}\n" ++
      body ++ "\n\\end{document}"
  let body := "Alpha words here.\n\nBravo words here.\n\\begin{itemize}\n" ++
    "\\item Charlie item.\n\\item Delta item.\n\\end{itemize}\nEcho words.\n" ++
    "\\begin{tabular}{ll}\nFoxtrot & Golf\n\\end{tabular}"
  let bare := pagesOf oneFace (doc "" body)
  let fine (ds : Array Diag) : Bool :=
    !ds.any fun d => d.severity == .error || d.code == "W0104" || d.code == "W0107" ||
      d.code == "W0301"
  let read : List (String × String) :=
    [("\\newlength{\\probegap}\\setlength{\\probegap}{7pt}\\setlength{\\parskip}{-\\probegap}",
       "\\setlength{\\parskip}{-7pt}"),
     ("\\setlength{\\parskip}{\\medskipamount}",
       "\\setlength{\\parskip}{6pt plus 2pt minus 2pt}"),
     ("\\setlength{\\medskipamount}{20pt}\\setlength{\\parskip}{\\medskipamount}",
       "\\setlength{\\medskipamount}{20pt}\\setlength{\\parskip}{20pt}"),
     ("\\setlength{\\bigskipamount}{3pt}\\setlength{\\parskip}{2\\bigskipamount}",
       "\\setlength{\\bigskipamount}{3pt}\\setlength{\\parskip}{6pt}"),
     ("\\setlength{\\leftmargini}{\\dimexpr 1em+2pt\\relax}",
       "\\setlength{\\leftmargini}{1em + 2pt}"),
     ("\\parskip 6pt plus 1pt", "\\setlength{\\parskip}{6pt plus 1pt}"),
     ("\\parskip=5pt", "\\setlength{\\parskip}{5pt}"),
     ("\\setlength{\\parskip}{7pt}\\setlength{\\topsep}{\\parskip}",
       "\\setlength{\\parskip}{7pt}\\setlength{\\topsep}{7pt}"),
     ("\\makeatletter\\setlength{\\parskip}{\\z@}\\makeatother", "\\setlength{\\parskip}{0pt}"),
     ("\\makeatletter\\newlength{\\@probegap}\\setlength{\\@probegap}{7pt}" ++
        "\\setlength{\\parskip}{\\@probegap}\\makeatother", "\\setlength{\\parskip}{7pt}"),
     -- The preamble's `\baselineskip` is the class's `\normalsize` one, 12pt at 10pt.
     ("\\setlength{\\parskip}{0.5\\baselineskip}", "\\setlength{\\parskip}{6pt}"),
     ("\\tabcolsep=\\baselineskip", "\\setlength{\\tabcolsep}{12pt}")]
  for (spelled, literal) in read do
    let src := doc spelled body
    let set := pagesOf oneFace src
    t s!"'{spelled}' sets the page '{literal}' sets"
      (set == pagesOf oneFace (doc literal body))
    t s!"'{spelled}' moves the page" (set != bare)
    t s!"'{spelled}' builds, and names no loss" (fine (dvE src))
  let unread : List (String × String) :=
    [("parskip", "\\setlength{\\parskip}{0pt plus 1fil}"),
     ("parskip", "\\setlength{\\parskip}{\\stretch{1}}"),
     ("labelwidth", "\\setlength{\\labelwidth}{0.5\\leftmargini}"),
     ("arraycolsep", "\\setlength{\\arraycolsep}{0.5\\tabcolsep}"),
     ("probegap", "\\newlength{\\probegap}\\setlength{\\probegap}{\\widthof{Alpha}}"),
     ("parskip", "\\addtolength{\\parskip}{2pt}")]
  for (n, pre) in unread do
    let src := doc pre body
    let ds := dvE src
    t s!"'{pre}' builds" (!ds.any (·.severity == .error))
    t s!"'{pre}' is named once, on its parameter"
      ((ds.filter fun d => d.code == "W0107").map (·.subject) ==
        #[some s!"length:{n}"])
    t s!"'{pre}' ships the page the document ships without it" (pagesOf oneFace src == bare)
  -- A definition's body runs where the command is used, so nothing in it is judged where it is defined.
  for pre in ["\\newcommand{\\probesize}{\\setlength{\\belowdisplayskip}{\\abovedisplayskip}}",
      "\\newcommand{\\probesize}{\\belowdisplayskip\\abovedisplayskip}",
      "\\newcommand{\\probesize}{\\addtolength{\\parskip}{2pt}}"] do
    let src := doc pre body
    t s!"'{pre}' names nothing where it is defined" (fine (dvE src))
    t s!"'{pre}' ships the page the document ships without it" (pagesOf oneFace src == bare)
  let listBody (lead : String) : String :=
    "Alpha words.\n\\begin{itemize}" ++ lead ++ "\\item One.\\item Two.\\end{itemize}\nBravo words."
  let idiom := doc "" (listBody "\\setlength{\\itemsep}{0pt}")
  let ids := dvE idiom
  t "a length set before a list's first item builds" (!ids.any (·.severity == .error))
  t "a length before a list's first item is read by that list, named by nothing"
    (!ids.any (·.code == "W0104") && pagesOf oneFace idiom != pagesOf oneFace (doc "" (listBody "")))
  let enumBody (lead : String) : String :=
    "\\begin{enumerate}" ++ lead ++ "\\item Four.\\item Five.\\end{enumerate}"
  let start := dvE (doc "" (enumBody "\\setcounter{enumi}{3}"))
  t "a counter set before a list's first item builds, named once"
    (!start.any (·.severity == .error) &&
      (start.filter (·.code == "W0104")).map (·.subject) == #[some "ctrl:setcounter:enumi"])
  let heads (set : String) : String :=
    "\\section{Alpha}\nOne.\n\\subsection{Bravo}\nTwo.\n\\subsection{Charlie}\nThree.\n" ++
      set ++ "\n\\section{Delta}\nFour."
  let valued := doc "" (heads "\\setcounter{section}{\\value{subsection}}")
  t "a counter set to another's value reads it where it stands"
    (pagesOf oneFace valued == pagesOf oneFace (doc "" (heads "\\setcounter{section}{2}")))
  t "a counter set to another's value builds" (!(dvE valued).any (·.severity == .error))


/-- An assignment is the value later arithmetic reads only where TeX makes it: not in a definition's
body, not past its group. -/
def registerScopeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) :
    IO Unit := do
  let t := check ref
  let doc (pre set : String) : String :=
    "\\documentclass{article}\n\\newlength{\\probegap}\\setlength{\\probegap}{10pt}\n" ++ pre ++
      "\n\\begin{document}\n" ++ set ++ "\nAlpha words.\n\n\\vspace{\\probegap}\n\n" ++
      "Bravo words.\n\\end{document}"
  let eleven := pagesOf oneFace (doc "" "\\setlength{\\probegap}{11pt}")
  let rows : List (String × String × String) :=
    [("an unused definition's arithmetic",
       "\\newcommand{\\probebump}{\\addtolength{\\probegap}{30pt}}",
       "\\addtolength{\\probegap}{1pt}"),
     ("an unused definition's assignment",
       "\\newcommand{\\probeset}{\\setlength{\\probegap}{50pt}}",
       "\\addtolength{\\probegap}{1pt}"),
     ("a group's assignment", "",
       "{\\setlength{\\probegap}{30pt}}\\addtolength{\\probegap}{1pt}"),
     ("an environment's assignment", "",
       "\\begin{minipage}{5cm}\\setlength{\\probegap}{30pt}\\end{minipage}" ++
         "\\addtolength{\\probegap}{1pt}")]
  for (what, pre, set) in rows do
    t s!"{what} is not the value arithmetic after it reads"
      (pagesOf oneFace (doc pre set) ==
        pagesOf oneFace (doc pre ((set.splitOn "\\addtolength").headD "" ++
          "\\setlength{\\probegap}{11pt}")))
  t "the scope rows measure the value: 11pt is not the 10pt the document starts from"
    (eleven != pagesOf oneFace (doc "" ""))


/-- A parameter a command reads as its operand is not assigned. -/
def operandChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre : String) : String :=
    "\\documentclass{article}\n\\setlength{\\parskip}{12pt}\n" ++ pre ++
      "\n\\begin{document}\n" ++ ((settingsBodies.lookup "paras").getD "") ++ "\n\\end{document}"
  let plain := pagesOf oneFace (doc "")
  for pre in ["\\ifdim\\parskip=0pt\\relax\\fi",
      "\\makeatletter\\ifdim\\parskip=\\z@\\relax\\fi\\makeatother",
      "\\ifdim 2\\parskip=0pt\\relax\\fi"] do
    t s!"'{pre}' reads the parameter and assigns nothing" (pagesOf oneFace (doc pre) == plain)
  t "the operand rows measure the parameter: 12pt is not the 0pt they compare with"
    (plain != pagesOf oneFace (doc "\\setlength{\\parskip}{0pt}"))



/-- A list parameter set in a list's body is that list's, as `\list` reads it. -/
def listBodyChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let doc (pre lead : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\n\\begin{document}\nAlpha words.\n" ++
      "\\begin{itemize}" ++ lead ++ "\\item One.\\item Two.\\end{itemize}\nBravo words.\n" ++
      "\\end{document}"
  let bare := pagesOf oneFace (doc "" "")
  let fails (ds : Array Diag) : Bool := ds.any (·.severity == .error)
  for n in Compat.listSpent.filter (· != Ir.trivlistSkipName) do
    let src := doc "" s!"\\setlength\{\\{n}}\{7pt}"
    let ds := dvE src
    t s!"'\\{n}' in a list's body builds, said in a note alone"
      (!fails ds && !ds.any (·.code == "W0104") &&
        ds.any (·.subject == some s!"ctrl:nothing:setlength:{n}"))
    t s!"'\\{n}' in a list's body ships the page the list ships without it"
      (pagesOf oneFace src == bare)
  let centred (lead : String) : String :=
    "\\documentclass{article}\n\\begin{document}\nAlpha words.\n\\begin{itemize}" ++ lead ++
      "\\item One.\n\\begin{center}\nTwo.\n\\end{center}\nThree.\\end{itemize}\n\\end{document}"
  let tds := dvE (centred "\\setlength{\\topsep}{7pt}")
  t "'\\topsep' in a list's body builds, read by its trivlists"
    (!fails tds && !tds.any (·.code == "W0104") &&
      pagesOf oneFace (centred "\\setlength{\\topsep}{7pt}") != pagesOf oneFace (centred ""))
  for n in Compat.listPerItem.filter (!["itemsep", "parskip"].contains ·) do
    let src := doc "" s!"\\setlength\{\\{n}}\{7pt}"
    let ds := dvE src
    t s!"'\\{n}' in a list's body builds, named once"
      (!fails ds && (ds.filter (·.code == "W0104")).map (·.subject) ==
        #[some s!"ctrl:setlength:{n}"])
    t s!"the naming gate's premise: no list here reads '\\{n}' set in its body"
      (pagesOf oneFace src == bare)
  for n in ["itemsep", "parskip"] do
    let src := doc "" s!"\\setlength\{\\{n}}\{7pt}"
    let ds := dvE src
    t s!"'\\{n}' in a list's body builds, read by its items"
      (!fails ds && !ds.any (·.code == "W0104") && pagesOf oneFace src != bare)
  let tight := doc "\\providecommand{\\tightlist}{\\setlength{\\itemsep}{0pt}\\setlength{\\parskip}{0pt}}"
    "\\tightlist"
  let tds := dvE tight
  t "pandoc's \\tightlist in a list builds, read by its items"
    (!fails tds && !tds.any (·.code == "W0104") && pagesOf oneFace tight != bare)


/-- The lengths LaTeX's kernel and standard classes declare for a document to set, each decided in
`Compat.paramSites`, read by the door, handled by its own arm, or owed. -/
def kernelLengthNames : List String :=
  ["paperwidth", "paperheight", "textwidth", "textheight", "oddsidemargin", "evensidemargin",
   "topmargin", "headheight", "headsep", "footskip", "marginparwidth", "marginparsep",
   "marginparpush", "columnsep", "columnseprule", "columnwidth", "linewidth", "topskip",
   "footnotesep", "footins", "floatsep", "textfloatsep", "intextsep", "dblfloatsep",
   "dbltextfloatsep", "abovecaptionskip", "belowcaptionskip", "parindent", "parskip",
   "baselineskip", "lineskip", "lineskiplimit", "parfillskip", "leftmargin", "leftmargini",
   "leftmarginii", "leftmarginiii", "leftmarginiv", "leftmarginv", "leftmarginvi",
   "rightmargin", "labelwidth", "labelsep", "itemindent", "listparindent", "itemsep", "parsep",
   "topsep", "partopsep", "abovedisplayskip", "belowdisplayskip", "abovedisplayshortskip",
   "belowdisplayshortskip", "jot", "mathindent", "arraycolsep", "tabcolsep", "arrayrulewidth",
   "doublerulesep", "fboxsep", "fboxrule", "unitlength", "smallskipamount", "medskipamount",
   "bigskipamount"]

/-- The kernel lengths no row decides yet, held in both directions. -/
def openKernelLengths : List String :=
  ["paperwidth", "paperheight", "oddsidemargin", "evensidemargin", "topmargin",
   "headheight", "marginparwidth", "marginparsep", "marginparpush", "columnseprule",
   "columnwidth", "linewidth", "topskip", "textfloatsep", "intextsep", "dblfloatsep",
   "dbltextfloatsep", "lineskip", "lineskiplimit", "parfillskip", "mathindent"]

/-- A kernel length is decided where it is set, and read where it is a value. -/
def kernelLengthChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let decided (n : String) : Bool :=
    (Compat.paramSites.lookup n).isSome || (Compat.kernelSkip n).isSome ||
      n == "belowcaptionskip"
  t "every kernel length is decided, or owed by name"
    (kernelLengthNames.filter (!decided ·) == openKernelLengths)
  let doc (cls pre body : String) : String :=
    "\\documentclass{" ++ cls ++ "}\n" ++ pre ++ "\n\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let list := "Alpha words.\n\\begin{itemize}\n\\item Bravo item.\n\\end{itemize}"
  let fails (ds : Array Diag) : Bool := ds.any (·.severity == .error)
  let line := doc "article" "\\setlength{\\leftmargini}{0.1\\linewidth}" list
  t "a preamble '\\linewidth' is the measure its page takes: read, never named"
    (!fails (dvE line) && !(dvE line).any (·.code == "W0107"))
  t "a preamble '\\linewidth' margin moves the list"
    (pagesOf oneFace line != pagesOf oneFace (doc "article" "" list))
  let par := doc "article" "\\setlength{\\parindent}{0.05\\textwidth}" list
  t "a paragraph indent of the measure builds, its value read"
    (!fails (dvE par) && !(dvE par).any (·.code == "W0107"))
  let margin := "\\usepackage[margin=2cm]{geometry}"
  let geo := doc "article" (margin ++ "\\setlength{\\leftmargini}{0.1\\linewidth}") list
  t "a flow page's '\\linewidth' after a declared page is that page's measure"
    (!fails (dvE geo) && !(dvE geo).any (·.code == "W0107") &&
      pagesOf oneFace geo == pagesOf oneFace (doc "article" (margin ++
        "\\setlength{\\leftmargini}{0.1\\textwidth}") list))
  let frame (pre : String) : String :=
    doc "beamer" pre ("\\begin{frame}{Alpha}\n" ++ list ++ "\n\\end{frame}")
  let fixed := frame "\\setlength{\\leftmargini}{0.1\\linewidth}"
  t "a class that fixes its text block reads '\\linewidth' as its '\\textwidth'"
    (!fails (dvE fixed) && !(dvE fixed).any (·.code == "W0107") &&
      pagesOf oneFace fixed == pagesOf oneFace (frame "\\setlength{\\leftmargini}{0.1\\textwidth}"))
  t "a class that fixes its text block: '\\linewidth' moves the page"
    (pagesOf oneFace fixed != pagesOf oneFace (frame ""))
  t "the gate's premise: a flow page offers 'textwidth' whether or not a page is declared"
    (!fails (dvE (doc "article" "\\tokens{ probe = 0.1 * textwidth }" list)) &&
      !fails (dvE (doc "article" "\\page{ hmargin = 2cm }\\tokens{ probe = 0.1 * textwidth }" list)))
  let body := doc "article" "" ("\\newlength{\\probew}\\setlength{\\probew}{0.1\\linewidth}\n" ++ list)
  t "a body '\\linewidth' at the top level is the measure, read"
    (!fails (dvE body) && !(dvE body).any (·.code == "W0107"))
  let nested := doc "article" "" ("\\newlength{\\probew}\n\\begin{minipage}{2in}" ++
    "\\setlength{\\probew}{0.1\\linewidth}Alpha.\\end{minipage}\n" ++ list)
  t "a '\\linewidth' inside an environment, its scope's width, builds, named once on its value"
    (!fails (dvE nested) && ((dvE nested).filter (·.code == "W0107")).map (·.subject) ==
      #[some "length:probew"])
  let head (pre : String) : String :=
    doc "article" ("\\runninghead{Alpha head}" ++ pre) "Alpha words.\n\nBravo words."
  t "'\\headsep' moves a running head's page"
    (pagesOf oneFace (head "\\setlength{\\headsep}{40pt}") != pagesOf oneFace (head ""))
  let skip (pre body : String) : String := doc "article" pre ("Alpha words.\n\n" ++ body ++ "\nBravo words.")
  let medium := pagesOf oneFace (skip "\\setlength{\\medskipamount}{20pt}" "\\medskip")
  t "'\\medskip' skips the amount the document set"
    (medium == pagesOf oneFace (skip "" "\\block[before = 20pt]{}"))
  t "'\\medskip' of a set amount moves the page" (medium != pagesOf oneFace (skip "" "\\medskip"))
  let late := doc "article" "" ("\\setlength{\\textwidth}{4in}\n" ++ list)
  t "a body '\\textwidth' moves no line and says so in a note"
    (pagesOf oneFace late == pagesOf oneFace (doc "article" "" list) &&
      !(dvE late).any (fun d => d.code == "W0340" || d.code == "W0104") &&
      (dvE late).any (·.subject == some "ctrl:nothing:setlength:textwidth"))

/-- TeX's edges a document leans on, each set as lualatex sets it on an invented probe. -/
def texEdgeChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let text (src : String) : String := (docHtmlOf (elabStr src).1).replace "\u00a0" " "
  let twice := "\\newcommand\\twice[1]{#1#1}\n"
  let nested := dvDoc (twice ++ "\\edef\\foo{\\twice{\\twice{ab}}}\n") "Foo: \\foo."
  t "edef: a call inside its own argument expands, as TeX expands it"
    (hasStr (text nested) "Foo: abababab." && !(dvE nested).any (·.code == "W0357"))
  let cyclic := dvDoc "\\def\\loop{\\loop}\n\\edef\\foo{\\loop}\n" "Foo."
  t "edef: a cycle stays refused, named" ((dvE cyclic).any (·.code == "W0357"))
  let reg := "\\newlength\\len\n\\setlength\\len{2in}\n"
  let bare (assign : String) := dvDoc reg ("A\\hspace{\\len}B\n\n{" ++ assign ++ " E\\hspace{\\len}F}\n\nG\\hspace{\\len}H")
  t "a bare assignment opening a group assigns its register there, scoped to the group"
    (pagesOf oneFace (bare "\\len-0.5in") == pagesOf oneFace (bare "\\setlength\\len{-0.5in}") &&
      pagesOf oneFace (bare "\\len=0.5in") == pagesOf oneFace (bare "\\setlength\\len{0.5in}") &&
      !hasStr (text (bare "\\len=0.5in")) "0.5in")
  let classRule (cls opt w : String) := pagesOf oneFace ("\\documentclass[" ++ opt ++ "]{" ++ cls ++
    "}\n\\begin{document}\n\\noindent\\rule{" ++ w ++ "}{2pt}\n\\end{document}")
  let rule (pre body : String) := pagesOf oneFace (dvDoc pre ("\\noindent\\rule{" ++ body ++ "}{2pt}"))
  t "\\parindent reads the engine's indent, flush here as its paragraphs are, and never stops the build"
    (rule "\\newlength\\lenC\n\\setlength\\lenC{\\parindent}\n" "\\lenC" == rule "" "0pt" &&
      rule "" "\\parindent" == rule "" "0pt" &&
      classRule "scrartcl" "" "\\parindent" == classRule "scrartcl" "" "0pt" &&
      pagesOf oneFace (dvDoc "" "\\hspace*{-\\parindent}Alpha words.") ==
        pagesOf oneFace (dvDoc "" "\\hspace*{0pt}Alpha words."))
  t "a declared \\parindent, which the flush page does not take, reads as the page's"
    (rule "\\setlength{\\parindent}{40pt}\n" "\\parindent" == rule "\\setlength{\\parindent}{40pt}\n" "0pt")
  let wrapped := dvDoc "\\newlength\\mylen\n\\newcommand\\setw{\\mylen=2in}\n"
    "\\setw\\noindent\\rule{\\mylen}{2pt}\n\n{\\mylen=1in}\\noindent\\rule{\\mylen}{2pt}"
  t "an assignment with = ending its group or a definition's body still assigns"
    (!hasStr (text wrapped) "=2in" && !hasStr (text wrapped) "=1in" && !(dvE wrapped).any (·.code == "W0301"))
  t "a kernel register opening a calc argument is read there"
    (!(dvE (dvDoc "\\usepackage{calc}\n" "a\\hspace{\\columnsep-5pt}b")).any (·.severity == .error))
  let calcPre := "\\usepackage{calc}\n\\newlength\\mylen\n\\setlength\\mylen{3in}\n"
  t "a register opening an argument is read there, never assigned"
    (pagesOf oneFace (dvDoc calcPre "a\\hspace{\\mylen-1in}b") ==
        pagesOf oneFace (dvDoc calcPre "a\\hspace{2in}b") &&
      !(dvE (dvDoc calcPre "\\ifdim \\mylen=3in yes\\fi")).any (·.code == "W0104"))
  let growing := dvDoc "\\def\\grow#1{\\grow{#1#1}}\n\\edef\\foo{\\grow{x}}\n" "Alpha."
  t "edef: a text its own calls grow is refused within the budget" ((dvE growing).any (·.code == "W0357"))
  let foot (v : String) := "\\usepackage[footskip=" ++ v ++ "]{geometry}\n"
  t "a geometry key in em is fixed in the preamble's font: footskip=2em is 20pt, and the page ships"
    (!(dvE (dvDoc (foot "2em") "Alpha.")).any (·.severity == .error) &&
      pagesOf oneFace (dvDoc (foot "2em") "Alpha.") == pagesOf oneFace (dvDoc (foot "20pt") "Alpha."))
  let mylen := "\\newlength\\mylen\n\\setlength\\mylen{1in}\n\\newlength\\other\n"
  t "a \\dimexpr with no \\relax reads to its group's end"
    (rule (mylen ++ "\\setlength\\other{\\dimexpr\\mylen+2pt}\n") "\\other" ==
      rule (mylen ++ "\\setlength\\other{1in}\\addtolength\\other{2pt}\n") "\\other")
  let margin (v : String) := pagesOf oneFace (dvDoc ("\\usepackage[hmargin=" ++ v ++ "]{geometry}\n") "Alpha.")
  t "geometry's hmargin reads a \\dimexpr group" (margin "{\\dimexpr 1in+0.5in\\relax}" == margin "1.5in")
  let deferred := dvDoc "\\newcommand\\tight{\\setlength{\\parskip}{\\ht\\strutbox}}\n" "Alpha.\n\nBravo."
  t "a length a definition sets from the strut box is left to its use, never named at the definition"
    (!(dvE deferred).any (·.code == "W0107"))
  let door := "\\newlength\\lenA \\setlength\\lenA{1in}\n\\newlength\\lenB \\setlength\\lenB{2pt}\n"
  let printed := dvDoc (door ++ "\\edef\\vals{\\the\\dimexpr\\lenA+\\lenB}\n") "\\vals."
  t "an \\edef reads a \\dimexpr no \\relax ends to its group's end"
    (text printed == text (dvDoc (door ++ "\\edef\\vals{\\the\\dimexpr\\lenA+\\lenB\\relax}\n") "\\vals.") &&
      !(dvE printed).any (·.code == "W0357"))
  t "a length only an expanded \\edef reads is read, never named unread"
    (!(dvE printed).any (·.code == "W0104"))

/-- TeX's state as lualatex sets it on invented probes: assignments, scopes, sizes and the page. -/
def texStateChecks (ref : IO.Ref (List String)) (_oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let text (src : String) : String := (docHtmlOf (elabStr src).1).replace "\u00a0" " "
  let codes (src : String) : List String := ((elabStr src).2.map (·.code)).toList
  let subjects (src : String) (code : String) : List (Option String) :=
    (((elabStr src).2.filter (·.code == code)).map (·.subject)).toList
  let params := dvDoc "\\tolerance=1000\n"
    ("{\\leftskip=2em \\rightskip=2em Alpha words.\\par}\n\n\\hsize=200pt Bravo words.\n\n" ++
      "\\hbadness=10000 \\looseness=-1 \\parfillskip=0pt plus 1fil Charlie words.")
  t "a TeX parameter's assignment sets no ink"
    (!["=2em", "=200pt", "=1000", "=-1", "1fil", "10000"].any (hasStr (text params) ·) &&
      !(codes params).contains "W0301")
  t "a TeX parameter the engine does not model is named once where it changes the page"
    ((subjects params "W0104").contains (some "ctrl:setlength:leftskip") &&
      (subjects params "W0104").contains (some "ctrl:setlength:tolerance"))
  t "a TeX parameter that shapes only TeX's log is a note"
    ((subjects params "N0100").contains (some "ctrl:nothing:texparam:hbadness") &&
      !(subjects params "W0104").contains (some "ctrl:setlength:hbadness"))
  let paras (src : String) : Nat := (elabStr src).1.body.foldl (fun n b =>
    if b matches .para _ then n + 1 else n) 0
  let spaces (src : String) : Array String := Ir.foldBlocks (fun acc _ => acc) (fun acc x =>
    match x with
    | .hspace e _ => acc.push (toString (e.eval fun _ => {}).width.sp)
    | _ => acc) #[] (elabStr src).1.body
  let gap := "\\newlength\\gap\n"
  let mid := dvDoc gap "A \\setlength{\\gap}{5pt} b\\hspace{\\gap}c d.\n\nE\\hspace{\\gap}f."
  t s!"a mid-paragraph length holds from where it stands, the paragraph whole ({paras mid})"
    (paras mid == 2 && spaces mid == #[toString (Dim.pt 5), toString (Dim.pt 5)])
  let grouped := dvDoc gap
    "\\setlength{\\gap}{3pt}A {\\setlength{\\gap}{7pt} b\\hspace{\\gap}c} d\\hspace{\\gap}e."
  t s!"a length a group in a paragraph sets ends with the group ({spaces grouped})"
    (paras grouped == 1 && spaces grouped == #[toString (Dim.pt 7), toString (Dim.pt 3)])
  let boxed := dvDoc gap "A \\hbox{\\gap=2pt p\\hspace{\\gap}q} r."
  t s!"a length assigned in inline content is read there, no restore leaking ({codes boxed})"
    (!(codes boxed).contains "W0346" && !hasStr (text boxed) "restore" &&
      spaces boxed == #[toString (Dim.pt 2)])
  let pads (src : String) : Array String := Ir.foldBlocks (fun acc _ => acc) (fun acc x =>
    match x with
    | .boxed b _ => acc.push (toString b.pad.width.sp)
    | _ => acc) #[] (elabStr src).1.body
  let cells := dvDoc "" ("\\begin{tabular}{ll}\n\\setlength{\\fboxsep}{0pt}\\fbox{c} & \\fbox{d} \\\\\n" ++
    "\\fbox{e} & f\n\\end{tabular}")
  t s!"a table's cell is a group: what it sets ends at its '&' and its row's end ({pads cells})"
    (pads cells == #[toString 0, toString (Dim.pt 3), toString (Dim.pt 3)])
  let tok (src key : String) : Option Dim.Length :=
    ((elabStr src).1.tokens.find? key).map (·.width.sp)
  let skips := dvDoc "\\newlength\\la\\newlength\\lb\\setlength{\\la}{\\baselineskip}\n"
    "{\\small\\setlength{\\lb}{\\ht\\strutbox}Alpha\\hspace{\\lb}beta.}"
  t s!"the preamble's \\baselineskip is the class's: 12pt at 10pt ({tok skips "la"})"
    (tok skips "la" == some (Dim.pt 12))
  -- lualatex: `\small` at 10pt sets `\baselineskip` 11pt and the strut box 7.69997pt tall.
  t s!"a size command sets the strut box at its \\baselineskip ({spaces skips})"
    (spaces skips == #[toString (Dim.Length.ofSp (Compat.strutDimen "ht" (Dim.pt 11).toSp))])
  let geo (o : String) : Ir.PageSpec := (elabStr (dvDoc s!"\\usepackage[{o}]\{geometry}\n" "Alpha.")).1.page
  -- lualatex: letter paper's default body is 430.00462pt by 556.47656pt, 95.39737pt from the top.
  t s!"geometry's default layout: 0.7 of the paper each way, split 2:3 vertically ({(geo "").hmargin})"
    ((geo "").hmargin == Dim.bp 612 * 3 / 20 && (geo "").vmargin == (Dim.bp 792 - Dim.bp 792 * 7 / 10) * 2 / 5)
  t "geometry's scale keys size the text block"
    ((geo "hscale=0.6").hmargin == Dim.bp 612 / 5 && (geo "scale=0.8").hmargin == Dim.bp 612 / 10)
  let em := (elabStr (dvDoc "\\page{ fontsize = 12pt, hmargin = 4em }\n" "Alpha.")).1.page
  t s!"a \\page block's em is its own font size's ({em.hmargin})" (em.hmargin == Dim.pt 48)
  let strut := dvDoc "" "Alpha\\strut{} words."
  let rules := Ir.foldBlocks (fun acc _ => acc) (fun acc x => match x with
    | .rule w h _ => acc.push ((w.eval fun _ => {}).width.sp, (h.eval fun _ => {}).width.sp)
    | _ => acc) #[] (elabStr strut).1.body
  t s!"\\strut is a rule of no width the strut box tall ({rules})"
    (!(codes strut).contains "W0301" && rules == #[(0, Dim.pt 12)])
  -- The foot's skip as the page reads it: the declared key, else the engine length.
  let footOfDoc (src : String) : Option Dim.Length :=
    let d := (elabStr src).1
    d.page.footskip <|> (d.tokens.find? "footskip").map (·.width.sp)
  let footOf (o : String) : Option Dim.Length :=
    footOfDoc (dvDoc s!"\\usepackage[{o}]\{geometry}\n" "Alpha.")
  -- lualatex: geometry's top=2cm, bottom=4cm sets the folio's baseline 30pt below the text.
  t "a page geometry places sets its foot the standard class's \\footskip below the text"
    (footOf "top=2cm,bottom=4cm" == some (Dim.pt 30) && footOf "footskip=1cm" == some (Dim.mm 10))
  let paper := dvDoc "\\usepackage[letterpaper]{geometry}\n" "Alpha."
  t "geometry's paper option naming the class's paper is noted as changing nothing"
    ((subjects paper "N0100").contains (some "param:geometry:letterpaper") &&
      (elabStr paper).1.page == (elabStr (dvDoc "\\usepackage{geometry}\n" "Alpha.")).1.page)
  let koma := "\\documentclass{scrartcl}\n\\usepackage[paperwidth=20cm]{geometry}\n" ++
    "\\begin{document}\nAlpha.\n\\end{document}"
  t "a declared paper width alone keeps the class's paper height"
    ((elabStr koma).1.page.height == Ir.a4Page.2 && (elabStr koma).1.page.width == Dim.mm 200)
  let abs := "\\documentclass{book}\n\\begin{document}\n\\begin{abstract}\nShort.\n" ++
    "\\end{abstract}\n\\end{document}"
  t "book defines no abstract: its body is kept as text, the environment named unknown"
    ((codes abs).contains "W0302" && !(codes abs).contains "W0110" && hasStr (text abs) "Short.")
  t "geometry: margins or a width place the block, a scale beside them sizing nothing"
    ((geo "hscale=0.8,margin=1in").hmargin == Dim.inch 1 &&
      (geo "textwidth=5in,hscale=0.5").hmargin == (Dim.bp 612 - Dim.inch 5) / 2 &&
      (geo "margin=1in,hscale=0.5").hmargin == Dim.inch 1)
  let paperDoc (cls pre : String) : Ir.PageSpec :=
    (elabStr (cls ++ pre ++ "\\begin{document}\nAlpha.\n\\end{document}")).1.page
  let paperFoot (cls pre : String) : Option Dim.Length :=
    footOfDoc (cls ++ pre ++ "\\begin{document}\nAlpha.\n\\end{document}")
  t "geometry: a paper option is the paper in force's, a later call's and KOMA-Script's paper= alike"
    ((paperDoc "\\documentclass{article}\n" "\\usepackage[a4paper]{geometry}\n\\geometry{letterpaper}\n").width ==
        Dim.bp 612 &&
      (paperDoc "\\documentclass[paper=letter]{scrartcl}\n" "\\usepackage[a4paper]{geometry}\n").width ==
        Ir.a4Page.1)
  -- lualatex: book.cls's \footskip is .35in, 25.29494pt; a footskip set before geometry stands.
  t "geometry: book's footskip is .35in, and a footskip declared before the page stands"
    (paperFoot "\\documentclass{book}\n" "\\usepackage[margin=1in]{geometry}\n" ==
        paperFoot "\\documentclass{book}\n" "\\usepackage[margin=1in,footskip=0.35in]{geometry}\n" &&
      paperFoot "\\documentclass{article}\n"
        "\\setlength{\\footskip}{20pt}\n\\usepackage[margin=1in]{geometry}\n" == some (Dim.pt 20))
  let redefined := dvDoc "\\renewcommand{\\strut}{STRUTWORD}\n" "Alpha\\strut{} words."
  t "\\strut: a document's own definition stands" (hasStr (text redefined) "STRUTWORD")
  let boxStrut := dvDoc "\\newlength\\lh\n" "\\setbox\\strutbox\\hbox{\\vrule height 20pt}\\setlength{\\lh}{\\ht\\strutbox}Alpha."
  t "\\strut: a body \\setbox of the strut box leaves its height unread, named"
    ((subjects boxStrut "W0107").contains (some "length:lh"))
  let defined := dvDoc "\\newcommand{\\tight}{\\leftskip=2em }\n" "\\tight Alpha words."
  t "a TeX parameter's assignment in a definition is named"
    ((subjects defined "W0104").contains (some "ctrl:setlength:leftskip") && !hasStr (text defined) "=2em")
  let chain := dvDoc "\\clubpenalty10000 \\widowpenalty10000 \\displaywidowpenalty=10000\n"
    "\\linepenalty10 \\looseness=-1 Charlie words."
  t s!"TeX parameter assignments in a row are each read ({codes chain})"
    (!(codes chain).contains "W0301" && !hasStr (text chain) "=-1" && !hasStr (text chain) "10000")
  let noteSkip := dvDoc gap "Alpha\\footnote{\\setlength{\\gap}{\\baselineskip}a\\hspace{\\gap}b} words."
  -- lualatex: \footnotesize at 10pt sets \baselineskip 9.5pt.
  t s!"a footnote's text reads its own size's \\baselineskip ({spaces noteSkip})"
    (spaces noteSkip == #[toString (Dim.pt 19 / 2)])
  let headSkip := dvDoc gap "\\section{Alpha\\setlength{\\gap}{\\baselineskip}}Words."
  t "a heading's \\baselineskip, its class's size, stays unread, named"
    ((subjects headSkip "W0107").contains (some "length:gap"))
  let absSkip := dvDoc gap "\\begin{abstract}\\setlength{\\gap}{\\baselineskip}a\\hspace{\\gap}b\\end{abstract}"
  -- lualatex: article's abstract is \small, 11pt at 10pt.
  t s!"an article's abstract reads \\small's \\baselineskip ({spaces absSkip})"
    (spaces absSkip == #[toString (Dim.pt 11)])
  let setTex := dvDoc "\\setlength{\\leftskip}{2em}\n" "Alpha."
  t "\\setlength of a TeX parameter is named as its assignment is"
    ((subjects setTex "W0104").contains (some "ctrl:setlength:leftskip"))
  t "\\setlength of a TeX parameter is named once, never also as a setting nothing reads"
    ((subjects setTex "W0104").length == 1)
  let footLater := dvDoc "\\usepackage[margin=1in]{geometry}\n\\setlength{\\footskip}{20pt}\n" "Alpha."
  t "a footskip declared after the page replaces the class's with no second value named"
    (!(codes footLater).contains "W0343" && footOfDoc footLater == some (Dim.pt 20))
  let footKey := dvDoc "\\usepackage[margin=1in]{geometry}\n\\geometry{footskip=25pt}\n" "Alpha."
  t "a later geometry footskip replaces the class's with no second value named"
    (!(codes footKey).contains "W0343" && footOfDoc footKey == some (Dim.pt 25))
  -- The paper in force follows a declared paper size and a class paper the page has no size for.
  t "geometry: a paper option after a declared paper size, or beside an unsized class paper, sets it"
    ((paperDoc "\\documentclass{article}\n" "\\usepackage[paperwidth=20cm,paperheight=20cm]{geometry}\n\\geometry{letterpaper}\n").width ==
        Dim.bp 612 &&
      (paperDoc "\\documentclass[a6paper]{article}\n" "\\usepackage[letterpaper]{geometry}\n").width ==
        Dim.bp 612 &&
      !(subjects (dvDoc "\\usepackage[paperwidth=20cm]{geometry}\n\\geometry{letterpaper}\n" "Alpha.")
        "N0100").contains (some "param:geometry:letterpaper"))
  -- lualatex: article's abstract is \normalsize on a title page and in two columns, 12pt at 10pt.
  let absIn (cls : String) (pre : String := "") : Array String := spaces
    (s!"\\documentclass{cls}\n" ++ gap ++ pre ++ "\\begin{document}\n\\begin{abstract}" ++
      "\\setlength{\\gap}{\\baselineskip}a\\hspace{\\gap}b\\end{abstract}\n\\end{document}")
  t s!"an abstract on its own title page, in two columns or redefined reads no \\small ({absIn "[titlepage]{article}"})"
    (absIn "[titlepage]{article}" != #[toString (Dim.pt 11)] && absIn "[twocolumn]{article}" != #[toString (Dim.pt 11)] &&
      absIn "{report}" != #[toString (Dim.pt 11)] &&
      absIn "{article}" "\\renewenvironment{abstract}{}{}\n" != #[toString (Dim.pt 11)] &&
      absIn "[notitlepage]{report}" == #[toString (Dim.pt 11)])
  let noteRedef := dvDoc (gap ++ "\\renewcommand{\\footnotesize}{\\large}\n")
    "Alpha\\footnote{\\setlength{\\gap}{\\baselineskip}a\\hspace{\\gap}b} words."
  t s!"a footnote under a redefined \\footnotesize reads no class size ({spaces noteRedef})"
    (spaces noteRedef != #[toString (Dim.pt 19 / 2)])
