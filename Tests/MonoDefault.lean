module

public import Tests.Support
public import LeanTex.Cli.FontAssembly
public import LeanTex.Cli.SlotLoss

public section

open LeanTex.Core LeanTex.Cli LeanTex.Cli.FontAssembly FontScan

/-! An undeclared typewriter slot sets in a platform monospace wherever the font environment holds
one, font collections included. -/

namespace Tests.MonoDefault

/-- Open Sans's four files as a text family with no typewriter companion. -/
def unpaired : Array FontDb.Face :=
  #[face "Open Sans" false (path := testFonts ++ "/OpenSans-Regular.ttf"),
    face "Open Sans" false (bold := true) (path := testFonts ++ "/OpenSans-Bold.ttf"),
    face "Open Sans" false (italic := true) (path := testFonts ++ "/OpenSans-Italic.ttf"),
    face "Open Sans" false (bold := true) (italic := true)
      (path := testFonts ++ "/OpenSans-BoldItalic.ttf")]

/-- Does every table a standalone font's directory names lie inside it? -/
def directoryFits (b : ByteArray) : Bool :=
  let n := Ink.u16 b 4
  12 + 16 * n ≤ b.size && (List.range n).all fun k =>
    let e := 12 + 16 * k
    Ink.u32 b (e + 8) + Ink.u32 b (e + 12) ≤ b.size

/-- The family the HTML's typewriter stack opens with. -/
def monoFamily (html : String) : Option String :=
  match html.splitOn "--font-mono: \"" with
  | _ :: rest :: _ => (rest.splitOn "\"").head?
  | _ => none

/-- The `src` of the regular `@font-face` of the family the HTML's typewriter stack opens with. -/
def monoSrc (html : String) : Option String := do
  let family ← monoFamily html
  match html.splitOn s!"@font-face \{ font-family: \"{family}\"; font-weight: 400; \
font-style: normal; src: url(\"" with
  | _ :: rest :: _ => (rest.splitOn "\")").head?
  | _ => none

/-- The generic family closing the HTML's typewriter stack. -/
def monoGeneric (html : String) : Option String :=
  match html.splitOn "--font-mono: \"" with
  | _ :: rest :: _ => (rest.splitOn ";").head?.bind fun stack => (stack.splitOn ", ").getLast?
  | _ => none

/-- A markdown and a tex document, each with inline and displayed code. -/
def codeDocs : List (String × Ir.Doc) :=
  [("markdown", (elabMd "Words with `inline code` beside them.\n\n```\nfenced code\n```\n").1),
   ("tex", (elabStr (dvDoc "" ("Words with \\texttt{inline code} beside them.\n\n" ++
      "\\begin{verbatim}\nfenced code\n\\end{verbatim}"))).1)]

def scanOf (faces : Array FontDb.Face) : FaceScan :=
  { faces, docDirs := [], dirs := #[], diags := #[] }

/-- The platform monospace is read in order and fills the undeclared slot through the driver's
assembly; W0390 names only a scan that serves none. -/
def monoDefaultChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let menlo := family4 "Menlo" "m.ttc#0" true
  t "the platform list prefers SF Mono to Menlo"
    (FontDb.monoDefault (menlo ++ family4 "SF Mono" "s.otf" true) == some "SF Mono")
  t "the platform list prefers Menlo to DejaVu Sans Mono"
    (FontDb.monoDefault (family4 "DejaVu Sans Mono" "d.ttf" true ++ menlo) == some "Menlo")
  t "the platform list prefers DejaVu Sans Mono to Liberation Mono"
    (FontDb.monoDefault (family4 "Liberation Mono" "l.ttf" true ++
      family4 "DejaVu Sans Mono" "d.ttf" true) == some "DejaVu Sans Mono")
  t "a listed family missing a corner is passed over for the next"
    (FontDb.monoDefault (#[face "SF Mono" true] ++ menlo) == some "Menlo")
  t "a listed proportional family is passed over for the next"
    (FontDb.monoDefault (family4 "Menlo" "m.ttc#0" false ++ family4 "Liberation Mono" "l.ttf" true)
      == some "Liberation Mono")
  t "a fixed-pitch family off the list is never taken by guess"
    (FontDb.monoDefault (family4 "Aardvark Mono" "a.ttf" true) == none)
  t "the text family's companion answers before the platform list"
    (FontDb.monoFor (#[face "DejaVu Sans" false] ++ family4 "DejaVu Sans Mono" "d.ttf" true ++ menlo)
      (some "DejaVu Sans") == some "DejaVu Sans Mono")
  t "a default text family with no companion takes the platform list"
    (FontDb.monoFor (#[face "Helvetica Neue" false] ++ menlo) (some "Helvetica Neue") == some "Menlo")
  let cache ← FontEnv.Cache.mk'
  let code := testFonts ++ "/SourceCodePro-Regular.otf"
  let withList := scanOf (unpaired ++ family4 "Menlo" code true)
  let short := scanOf (unpaired ++ #[face "Menlo" true (path := code)])
  for (surface, doc) in codeDocs do
    match ← buildFontSet doc withList cache .settled, ← buildFontSet doc (scanOf unpaired) cache .settled,
        ← buildFontSet doc short cache .settled with
    | .ok (fsA, docA, diagsA, pathsA), .ok (fsB, docB, _, _), .ok (fsC, docC, diagsC, _) =>
      let loss (fs : Font.FontSet) (d : Ir.Doc) :=
        SlotLoss.diags d.fonts fs d (SlotLoss.carries #[.pdf, .html] d.fontPolicy)
      let monoA := fsA.lookup 2 400 false
      let textB := fsB.lookup 0 400 false
      t s!"{surface}: a platform monospace fills the slot whole, no loss named"
        (fsA.slotIsFixedPitch 2 && !fsA.slotCollapsed 2 && (loss fsA docA).isEmpty
          && pathsA.contains code && !diagsA.any (·.kind == .W0006))
      t s!"{surface}: no platform monospace leaves the text face, named by W0390"
        (fsB.slotCollapsed 2 && (loss fsB docB).any (·.kind == .W0390))
      let help := (((loss fsB docB).find? (·.kind == .W0390)).bind (·.help)).getD ""
      t s!"{surface}: W0390's help offers what this source can do ({help})"
        (hasStr help (if surface == "tex" then "install one of Latin Modern Mono, SF Mono"
            else "install one of SF Mono") && hasStr help "its bold and both or no italics"
          && hasStr help "\\fonts{ mono" == (surface == "tex"))
      t s!"{surface}: a family short of a corner is no default; W0390 names the slot"
        (fsC.slotCollapsed 2 && (loss fsC docC).any (·.kind == .W0390)
          && !diagsC.any (·.kind == .W0006))
      t s!"{surface} page: code ships in the platform monospace, else the text face"
        (runFace (layoutOf fsA docA) "fenced" == some monoA && (fsA.get monoA).isFixedPitch
          && runFace (layoutOf fsB docB) "fenced" == some textB && !(fsB.get textB).isFixedPitch)
      let (htmlA, _) := HtmlDoc.emit { fonts := some fsA } docA
      let (htmlB, _) := HtmlDoc.emit { fonts := some fsB } docB
      t s!"{surface} html: the typewriter stack closes on monospace, else the text face's generic"
        (monoGeneric htmlA == some "monospace" && monoGeneric htmlB == some "sans-serif")
      t s!"{surface} html: it ships the platform monospace as typewriter face, else the text face"
        (monoSrc htmlA == some (HtmlDoc.fontResource (fsA.get monoA)).uri && (fsA.get monoA).isFixedPitch
          && monoSrc htmlB == some (HtmlDoc.fontResource (fsB.get textB)).uri
          && !(fsB.get textB).isFixedPitch)
    | _, _, _ => t s!"{surface}: the three assemblies succeed" false
  IO.FS.withTempDir fun host => do
    let hostCode := (host / "Code.otf").toString
    IO.FS.writeBinFile hostCode (← IO.FS.readBinFile code)
    let shipped (own : Array FontDb.Face) (hostFaces : Array FontDb.Face) : FaceScan :=
      { faces := own ++ hostFaces, docDirs := [testFonts], dirs := #[], diags := #[] }
    let ownText := unpaired
    let ownMono := family4 "DejaVu Sans Mono" code true
    let hostMenlo := family4 "Menlo" hostCode true
    let doc := (elabStr (dvDoc "\\fonts{ dir = \"fonts\" }\n" ("Words with \\texttt{inline code} \
beside them.\n\n\\begin{verbatim}\nfenced code\n\\end{verbatim}"))).1
    -- A fresh cache per assembly: a cache belongs to one run over one scan.
    let build (scan : FaceScan) := do buildFontSet doc scan (← FontEnv.Cache.mk') .settled
    match ← build (shipped (ownText ++ ownMono) hostMenlo), ← build (shipped (ownText ++ ownMono) #[]),
        ← build (shipped ownText hostMenlo), ← build (shipped ownText #[]) with
    | .ok (fsA, _, _, pathsA), .ok (fsB, _, _, pathsB), .ok (fsC, docC, _, pathsC),
        .ok (fsD, docD, _, _) =>
      let loss (fs : Font.FontSet) (d : Ir.Doc) :=
        SlotLoss.diags d.fonts fs d (SlotLoss.carries #[.pdf, .html] d.fontPolicy)
      t "a document's shipped typewriter face wins over the host's"
        (pathsA.contains code && !pathsA.contains hostCode && pathsB.contains code
          && fsA.slotIsFixedPitch 2 && fsB.slotIsFixedPitch 2)
      t "no shipped typewriter face takes the host's monospace next"
        (pathsC.contains hostCode && fsC.slotIsFixedPitch 2 && !fsC.slotCollapsed 2
          && !(loss fsC docC).any (·.kind == .W0390))
      t "bare host, no shipped typewriter face: the text face, named by W0390"
        (fsD.slotCollapsed 2 && (loss fsD docD).any (·.kind == .W0390))
      let help := (((loss fsD docD).find? (·.kind == .W0390)).bind (·.help)).getD ""
      t s!"a font-shipping document is told to install or ship a monospace ({help})"
        (hasStr help "install one of Latin Modern Mono" && hasStr help "its bold and both or no italics"
          && hasStr help "or put it in the document's font directory" && hasStr help "\\fonts{ mono")
    | _, _, _, _ => t "the shipped-fonts assemblies succeed" false
    let italicDoc := (elabStr (dvDoc "\\fonts{ dir = \"fonts\" }\n"
      "Plain \\texttt{upright code} and \\textit{\\texttt{slanted code}}.")).1
    let ownUpright := #[face "DejaVu Sans Mono" true (path := code),
      face "DejaVu Sans Mono" true (bold := true) (path := code)]
    match ← buildFontSet italicDoc (shipped (ownText ++ ownUpright) (family4 "DejaVu Sans Mono" hostCode true))
        (← FontEnv.Cache.mk') .settled with
    | .ok (fs, _, diags, paths) =>
      t "italic code in an italic-less shipped monospace sets upright in it"
        (!paths.contains hostCode && fs.lookup 2 400 true == fs.lookup 2 400 false
          && fs.lookup 2 700 true == fs.lookup 2 700 false
          && (diags.filter (·.kind == .N0031)).size == 1 && !diags.any (·.kind == .W0006))
      let note := diags.find? (·.kind == .N0031)
      t s!"the shipped monospace's note names the document's font directory ({note.map (·.message)}, {note.bind (·.help)})"
        (note.any fun d => hasStr d.message "the document's font directory" &&
          hasStr (d.help.getD "") "put the family's italic faces in the document's font directory" &&
          !hasStr (d.help.getD "") "install")
    | .error d => t s!"the shipped upright assembly succeeds ({d.message})" false
  let uprightOnly := scanOf (unpaired ++ #[face "DejaVu Sans Mono" true (path := code),
    face "DejaVu Sans Mono" true (bold := true) (path := code)])
  for (surface, doc) in [("tex", (elabStr (dvDoc "" ("Plain \\texttt{upright code} and " ++
        "\\textit{\\texttt{slanted code}} and \\textbf{\\texttt{heavy code}}."))).1),
      ("markdown", (elabMd "Plain `upright code` and *`slanted code`* and **`heavy code`**.\n").1)] do
    match ← buildFontSet doc uprightOnly (← FontEnv.Cache.mk') .settled with
    | .ok (fs, resolved, diags, paths) =>
      let upright := fs.lookup 2 400 false
      let notes := diags.filter (·.kind == .N0031)
      t s!"{surface}: an italic-less listed family serves, its italics named once ({notes.size})"
        (paths.contains code && fs.slotIsFixedPitch 2 && !fs.slotCollapsed 2 && notes.size == 1
          && !diags.any (·.kind == .W0006) && fs.lookup 2 400 true == upright
          && (SlotLoss.diags resolved.fonts fs resolved
            (SlotLoss.carries #[.pdf, .html] resolved.fontPolicy)).isEmpty
          && notes.all (fun d => hasStr (d.help.getD "") "\\fonts{ mono" == (surface == "tex")))
      let out := layoutOf fs resolved
      t s!"{surface} page: italic code sets in the upright face, unslanted"
        (runFace out "slanted" == some upright && !(fs.get upright).isItalic
          && runFace out "upright" == some upright)
      let (html, _) := HtmlDoc.emit { fonts := some fs } resolved
      t s!"{surface} html: the page ships no italic typewriter face and synthesises no slant"
        (!hasStr html "font-family: \"ltx-mono\"; font-weight: 400; font-style: italic"
          && hasStr html "font-synthesis: small-caps;")
    | .error d => t s!"{surface}: the upright-only assembly succeeds ({d.message})" false
  for (what, doc, named) in
      [("tex code with no italic run", (elabStr (dvDoc "" ("Plain \\texttt{upright code}, " ++
          "\\textit{slanted words} and \\textbf{\\texttt{heavy code}}."))).1, false),
       ("markdown code with no italic run",
          (elabMd "Plain `upright code`, *slanted words* and **`heavy code`**.\n").1, false),
       ("a listing with no comment", (elabStr (dvDoc "" ("\\begin{lstlisting}[language=Python]\n" ++
          "x = 1\n\\end{lstlisting}"))).1, false),
       ("a listing's comment", (elabStr (dvDoc "" ("\\begin{lstlisting}[language=Python]\n" ++
          "# a remark\nx = 1\n\\end{lstlisting}"))).1, true),
       ("a markdown fence's comment", (elabMd "```python\n# a remark\nx = 1\n```\n").1, true),
       ("a heading's italic template over its code", (elabStr (dvDoc
          "\\style{section}{ font = {\\itshape} }\n" "\\section{About \\texttt{code}}\nText.")).1,
          true),
       ("a KOMA heading font over its code", (elabStr ("\\documentclass{scrartcl}\n" ++
          "\\setkomafont{section}{\\itshape}\n\\begin{document}\n" ++
          "\\section{About \\texttt{code}}\nText.\n\\end{document}")).1, true),
       ("a template no element uses", (elabStr (dvDoc
          "\\style{subsubsection}{ font = {\\itshape\\ttfamily} }\n"
          "Plain \\texttt{upright code} and no such heading.")).1, false),
       ("an italic over empty code", (elabStr (dvDoc ""
          "Plain \\texttt{upright code} and \\textit{words \\texttt{}} here.")).1, false),
       ("a typewriter switch with nothing after it", (elabStr (dvDoc ""
          "Plain \\texttt{upright code} and {\\itshape words\\ttfamily}.")).1, false)] do
    match ← buildFontSet doc uprightOnly (← FontEnv.Cache.mk') .settled with
    | .ok (fs, _, diags, _) =>
      t s!"{what}: the italic note is named exactly where italic code is set"
        ((diags.filter (·.kind == .N0031)).size == (if named then 1 else 0)
          && !diags.any (·.kind == .W0006) && fs.slotIsFixedPitch 2
          && fs.lookup 2 400 true == fs.lookup 2 400 false
          && fs.lookup 2 700 true == fs.lookup 2 700 false)
    | .error d => t s!"{what}: the assembly succeeds ({d.message})" false
  let italicSrc := "Plain \\texttt{upright code} and \\textit{\\texttt{slanted code}}."
  let declaredDoc := (elabStr (dvDoc "\\fonts{ mono = \"DejaVu Sans Mono\" }\n" italicSrc)).1
  let undeclaredDoc := (elabStr (dvDoc "" italicSrc)).1
  match ← buildFontSet declaredDoc uprightOnly (← FontEnv.Cache.mk') .settled,
      ← buildFontSet undeclaredDoc uprightOnly (← FontEnv.Cache.mk') .settled with
  | .ok (fsD, docD, diagsD, pathsD), .ok (fsU, docU, diagsU, pathsU) =>
    let subs := diagsD.filter (·.kind == .W0006)
    t s!"a declared italic-less family names each italic corner ({subs.size}), no note"
      (subs.size == 2 && !diagsD.any (·.kind == .N0031))
    t "the undeclared default names one note, and no substitution"
      ((diagsU.filter (·.kind == .N0031)).size == 1 && !diagsU.any (·.kind == .W0006))
    let outD := layoutOf fsD docD
    let outU := layoutOf fsU docU
    t "declared or not, italic code sets in the same upright face"
      (runFace outD "slanted" == some (fsD.lookup 2 400 false)
        && runFace outU "slanted" == some (fsU.lookup 2 400 false)
        && pathsD[fsD.lookup 2 400 true]? == pathsU[fsU.lookup 2 400 true]?)
  | _, _ => t "the declared and undeclared assemblies succeed" false
  let templateSrc := "\\section{About \\texttt{code}}\nText."
  let templatePre := "\\style{section}{ font = {\\itshape} }\n"
  match ← buildFontSet (elabStr (dvDoc (templatePre ++ "\\fonts{ mono = \"DejaVu Sans Mono\" }\n")
        templateSrc)).1 uprightOnly (← FontEnv.Cache.mk') .settled,
      ← buildFontSet (elabStr (dvDoc templatePre templateSrc)).1 uprightOnly
        (← FontEnv.Cache.mk') .settled with
  | .ok (fsD, docD, diagsD, pathsD), .ok (fsU, docU, diagsU, pathsU) =>
    let outD := layoutOf fsD docD
    let outU := layoutOf fsU docU
    t "a heading template's italic code: declared names its corners, undeclared one note, one page"
      ((diagsD.filter (·.kind == .W0006)).size == 2 && !diagsD.any (·.kind == .N0031)
        && (diagsU.filter (·.kind == .N0031)).size == 1 && !diagsU.any (·.kind == .W0006)
        && runFace outD "code" == some (fsD.lookup 2 400 false)
        && runFace outU "code" == some (fsU.lookup 2 400 false)
        && pathsD[fsD.lookup 2 400 true]? == pathsU[fsU.lookup 2 400 true]?)
  | _, _ => t "the template twin's assemblies succeed" false
  let menloFaces := family4 "Menlo" code true
  let noBoldItalic : Array FontDb.Face := #[face "SF Mono" true (path := code),
    face "SF Mono" true (bold := true) (path := code),
    face "SF Mono" true (italic := true) (path := code)]
  let noItalic : Array FontDb.Face := #[face "SF Mono" true (path := code),
    face "SF Mono" true (bold := true) (path := code),
    face "SF Mono" true (bold := true) (italic := true) (path := code)]
  t "a listed family missing its bold italic is no default"
    (!FontDb.servesMono noBoldItalic "SF Mono" && FontDb.monoDefault (noBoldItalic ++ menloFaces) == some "Menlo")
  t "a listed family missing its regular italic is no default"
    (!FontDb.servesMono noItalic "SF Mono" && FontDb.monoDefault (noItalic ++ menloFaces) == some "Menlo")
  t "a listed family with no italic at all serves upright"
    (FontDb.servesMono #[face "SF Mono" true (path := code), face "SF Mono" true (bold := true) (path := code)]
      "SF Mono")
  for (surface, doc) in codeDocs do
    match ← buildFontSet doc (scanOf (unpaired ++ noBoldItalic ++ menloFaces)) (← FontEnv.Cache.mk') .settled,
        ← buildFontSet doc (scanOf (unpaired ++ noBoldItalic)) (← FontEnv.Cache.mk') .settled with
    | .ok (fsA, docA, diagsA, _), .ok (fsB, docB, diagsB, _) =>
      let loss (fs : Font.FontSet) (d : Ir.Doc) :=
        SlotLoss.diags d.fonts fs d (SlotLoss.carries #[.pdf, .html] d.fontPolicy)
      t s!"{surface}: a family missing one italic is passed over, naming nothing"
        (fsA.slotIsFixedPitch 2 && (loss fsA docA).isEmpty
          && !diagsA.any (fun d => d.kind == .W0006 || d.kind == .N0031))
      t s!"{surface}: with no other, the slot is the text face, W0390 and no substitution"
        (fsB.slotCollapsed 2 && (loss fsB docB).any (·.kind == .W0390)
          && !diagsB.any (fun d => d.kind == .W0006 || d.kind == .N0031))
    | _, _ => t s!"{surface}: the one-italic assemblies succeed" false
  IO.FS.withTempDir fun tree => do
    let lm : List (String × String × Bool × Bool) :=
      [("lmmono10-regular.otf", "Latin Modern Mono", false, false),
       ("lmmonolt10-bold.otf", "Latin Modern Mono Light", true, false),
       ("lmmono10-italic.otf", "Latin Modern Mono", false, true),
       ("lmmonolt10-boldoblique.otf", "Latin Modern Mono Light", true, true)]
    let mut lmFaces : Array FontDb.Face := #[]
    for (file, fam, bold, italic) in lm do
      let path := (tree / file).toString
      IO.FS.writeBinFile path (← IO.FS.readBinFile code)
      lmFaces := lmFaces.push (face fam true (bold := bold) (italic := italic) (path := path))
    let menloAt := (tree / "Menlo.otf").toString
    IO.FS.writeBinFile menloAt (← IO.FS.readBinFile code)
    let withLm := scanOf (unpaired ++ lmFaces ++ family4 "Menlo" menloAt true)
    let shortLm := scanOf (unpaired ++ lmFaces.pop ++ family4 "Menlo" menloAt true)
    let uprightLm := scanOf (unpaired ++ lmFaces.extract 0 2)
    let src := "Plain \\texttt{upright code}, \\textbf{\\texttt{heavy code}}, " ++
      "\\textit{\\texttt{slanted code}} and \\textbf{\\textit{\\texttt{heavy slanted code}}}."
    let texDoc := (elabStr (dvDoc "\\fonts{ body = \"Open Sans\" }\n" src)).1
    let texDefault := (elabStr (dvDoc "" src)).1
    let mdDoc := (elabMd "Plain `upright code` and **`heavy code`**.\n").1
    let fileOf (fs : Font.FontSet) (paths : Array String) (w : Nat) (i : Bool) : String :=
      ((paths[fs.lookup 2 w i]?.getD "").splitOn "/").getLast?.getD ""
    let lmIn (paths : Array String) : Bool := paths.any fun p => hasStr p "lmmono"
    match ← buildFontSet texDoc withLm (← FontEnv.Cache.mk') .settled,
        ← buildFontSet mdDoc withLm (← FontEnv.Cache.mk') .settled,
        ← buildFontSet texDoc shortLm (← FontEnv.Cache.mk') .settled,
        ← buildFontSet texDefault withLm (← FontEnv.Cache.mk') .settled,
        ← buildFontSet texDefault (scanOf (unpaired ++ lmFaces)) (← FontEnv.Cache.mk') .settled,
        ← buildFontSet texDoc uprightLm (← FontEnv.Cache.mk') .settled with
    | .ok (fsT, docT, diagsT, pathsT), .ok (_, _, _, pathsM), .ok (_, _, _, pathsS),
        .ok (_, _, _, pathsU), .ok (fsL, _, diagsL, pathsL), .ok (fsR, docR, diagsR, pathsR) =>
      let f := fileOf fsT pathsT
      t s!"tex: an undeclared slot beside a declared face takes Latin Modern Mono ({f 400 false}, {f 700 false}, {f 400 true}, {f 700 true})"
        (f 400 false == "lmmono10-regular.otf" && f 700 false == "lmmonolt10-bold.otf"
          && f 400 true == "lmmono10-italic.otf" && f 700 true == "lmmonolt10-boldoblique.otf"
          && !diagsT.any (fun d => d.kind == .W0006 || d.kind == .N0031))
      let out := layoutOf fsT docT
      t "tex page: bold code sets in the Light family's bold, as lualatex sets it"
        (runFace out "heavy" == some (fsT.lookup 2 700 false)
          && runFace out "upright" == some (fsT.lookup 2 400 false))
      t "markdown: the platform list, never lualatex's shapes"
        (pathsM.contains menloAt && !lmIn pathsM)
      t "tex: a scan short of a lualatex italic shape takes the platform list"
        (pathsS.contains menloAt && !lmIn pathsS)
      t "tex: the engine's own text face puts the platform list before lualatex's"
        (pathsU.contains menloAt && !lmIn pathsU)
      let l := fileOf fsL pathsL
      t s!"tex: lualatex's shapes are its last answer before the text face ({l 400 false}, {l 700 true})"
        (l 400 false == "lmmono10-regular.otf" && l 700 true == "lmmonolt10-boldoblique.otf"
          && fsL.slotIsFixedPitch 2 && !diagsL.any (fun d => d.kind == .W0006 || d.kind == .N0031))
      let r := fileOf fsR pathsR
      t s!"tex: upright lualatex shapes alone serve, italics upright, named once ({r 400 true}, {r 700 true})"
        (r 400 false == "lmmono10-regular.otf" && r 700 false == "lmmonolt10-bold.otf"
          && r 400 true == "lmmono10-regular.otf" && r 700 true == "lmmonolt10-bold.otf"
          && (diagsR.filter (·.kind == .N0031)).size == 1 && !diagsR.any (·.kind == .W0006))
      t "tex page: italic code sets upright in lualatex's upright shapes"
        (runFace (layoutOf fsR docR) "slanted" == some (fsR.lookup 2 400 false))
    | _, _, _, _, _, _ => t "the Latin Modern assemblies succeed" false
    let semibold := (elabStr (dvDoc "\\fonts{ body = \"Open Sans\" }\n"
      "Plain \\texttt{upright code} and \\texttt{\\fontseries{sb}\\selectfont semibold code}.")).1
    match ← buildFontSet semibold withLm (← FontEnv.Cache.mk') .settled with
    | .ok (fsB, docB, diagsB, pathsB) =>
      let b := fileOf fsB pathsB
      t s!"tex: an off-corner weight sets in the nearest corner's file, named ({b 600 false})"
        (b 600 false == "lmmonolt10-bold.otf" && diagsB.any (·.kind == .W0366)
          && runFace (layoutOf fsB docB) "semibold" == some (fsB.lookup 2 600 false))
    | .error d => t s!"the off-corner Latin Modern assembly succeeds ({d.message})" false
    let serif : Array FontDb.Face :=
      #[face "Source Serif Pro" false (path := testFonts ++ "/SourceSerifPro-Regular.otf"),
        face "Source Serif Pro" false (bold := true) (path := testFonts ++ "/SourceSerifPro-Bold.otf"),
        face "Source Serif Pro" false (italic := true)
          (path := testFonts ++ "/SourceSerifPro-RegularIt.otf"),
        face "Source Serif Pro" false (bold := true) (italic := true)
          (path := testFonts ++ "/SourceSerifPro-BoldIt.otf")]
    let nimbusMonoAt := (tree / "NimbusMonoPS-Regular.otf").toString
    IO.FS.writeBinFile nimbusMonoAt (← IO.FS.readBinFile code)
    let dejavuMonoAt := (tree / "DejaVuSansMono.ttf").toString
    IO.FS.writeBinFile dejavuMonoAt (← IO.FS.readBinFile code)
    let relabel (fam : String) : Array FontDb.Face := unpaired.map fun f => { f with family := fam }
    let declaredIn (body : String) : Ir.Doc :=
      (elabStr (dvDoc ("\\fonts{ body = \"" ++ body ++ "\" }\n") src)).1
    match ← buildFontSet (declaredIn "Source Serif Pro")
          (scanOf (serif ++ family4 "Source Code Pro" code true ++ lmFaces)) (← FontEnv.Cache.mk')
          .settled,
        ← buildFontSet (declaredIn "Nimbus Sans")
          (scanOf (relabel "Nimbus Sans" ++ family4 "Nimbus Mono PS" nimbusMonoAt true ++ lmFaces))
          (← FontEnv.Cache.mk') .settled,
        ← buildFontSet texDefault
          (scanOf (relabel "DejaVu Sans" ++ family4 "DejaVu Sans Mono" dejavuMonoAt true ++ lmFaces))
          (← FontEnv.Cache.mk') .settled,
        ← buildFontSet (declaredIn "Source Serif Pro")
          (scanOf (serif ++ lmFaces ++ family4 "Menlo" menloAt true)) (← FontEnv.Cache.mk') .settled,
        ← buildFontSet (declaredIn "Source Serif Pro")
          (scanOf (serif ++ family4 "Menlo" menloAt true)) (← FontEnv.Cache.mk') .settled,
        ← buildFontSet (declaredIn "SourceSerifPro-Regular.otf")
          (scanOf (serif ++ family4 "Source Code Pro" code true ++ lmFaces)) (← FontEnv.Cache.mk')
          .settled,
        ← buildFontSet (declaredIn "Source Serif Pro Regular")
          (scanOf (serif ++ family4 "Source Code Pro" code true ++ lmFaces)) (← FontEnv.Cache.mk')
          .settled,
        ← buildFontSet (declaredIn "Source Serif Pro Light")
          (scanOf (serif ++ family4 "Source Code Pro" code true ++ lmFaces)) (← FontEnv.Cache.mk')
          .settled with
    | .ok (_, _, _, pathsC), .ok (_, _, _, pathsN), .ok (_, _, _, pathsD), .ok (_, _, _, pathsL),
        .ok (_, _, _, pathsP), .ok (_, _, _, pathsF), .ok (_, _, _, pathsW), .ok (_, _, _, pathsA) =>
      t "tex: a companion leading on x-height precedes lualatex's shapes"
        (pathsC.contains code && !lmIn pathsC)
      t "tex: a companion that does not lead follows lualatex's shapes"
        (lmIn pathsN && !pathsN.contains nimbusMonoAt)
      t "tex: the engine's own face puts its companion before lualatex's shapes"
        (pathsD.contains dejavuMonoAt && !lmIn pathsD)
      t "tex: a leading companion the scan lacks leaves lualatex's shapes next"
        (lmIn pathsL && !pathsL.contains menloAt)
      t "tex: and the platform list after them"
        (pathsP.contains menloAt && !lmIn pathsP)
      t "tex: the companion leads however the text face is spelled"
        (pathsF.contains code && !lmIn pathsF && pathsW.contains code && !lmIn pathsW)
      t "tex: and with a weight the family lacks, as the text slot reads it"
        (pathsA.contains code && !lmIn pathsA)
    | _, _, _, _, _, _, _, _ => t "the companion-first assemblies succeed" false
    let notoMonoAt := (tree / "NotoSansMono-Regular.ttf").toString
    IO.FS.writeBinFile notoMonoAt (← IO.FS.readBinFile code)
    let notoMono : Array FontDb.Face :=
      #[face "Noto Sans Mono" true (path := notoMonoAt),
        face "Noto Sans Mono" true (bold := true) (path := notoMonoAt)]
    match ← buildFontSet (declaredIn "Noto Sans") (scanOf (relabel "Noto Sans" ++ notoMono ++ lmFaces))
        (← FontEnv.Cache.mk') .settled with
    | .ok (fsU, docU, diagsU, pathsU) =>
      let notes := diagsU.filter (·.kind == .N0031)
      t s!"tex: an upright-only leading companion sets italics upright, one note offering a declaration ({notes.size})"
        (pathsU.contains notoMonoAt && !lmIn pathsU && notes.size == 1
          && notes.all (fun d => d.help.any fun h => !hasStr h "install")
          && runFace (layoutOf fsU docU) "slanted" == some (fsU.lookup 2 400 false))
    | .error d => t s!"the upright companion assembly succeeds ({d.message})" false
  for (what, body) in
      [("a picture's label", "\\begin{tikzpicture}\\node at (0,0) {\\texttt{label code}};\\end{tikzpicture}"),
       ("a formula's typewriter alphabet", "A formula $\\mathtt{abc}$ in words.")] do
    let (doc, _) := elabStr (dvDoc "\\usepackage{tikz}\n" body)
    let (bare, _) := elabStr (dvDoc "\\usepackage{tikz}\n" "Plain words only.")
    match ← buildFontSet doc withList cache .settled, ← buildFontSet bare withList cache .settled with
    | .ok (_, _, _, paths), .ok (_, _, _, barePaths) =>
      t s!"{what} alone loads the platform monospace"
        (paths.contains code && !barePaths.contains code)
    | _, _ => t s!"{what}: the assemblies succeed" false
  for (surface, doc) in
      [("markdown", (elabMd "Words and nothing set in code.\n").1),
       ("tex", (elabStr (dvDoc "" "Words and nothing set in code.")).1)] do
    match ← buildFontSet doc withList cache .settled with
    | .ok (fs, resolved, _, paths) =>
      t s!"{surface}: a document setting no typewriter run loads no typewriter face"
        (!paths.contains code && fs.slotCollapsed 2
          && (SlotLoss.diags resolved.fonts fs resolved
            (SlotLoss.carries #[.pdf, .html] resolved.fontPolicy)).isEmpty)
    | .error d => t s!"{surface}: the assembly succeeds ({d.message})" false

/-- A declared face's companion leads Latin Modern Mono only where it is measurably nearer on
x-height, within the declared bound. -/
def companionDepartureChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let thousandths (f : Font) : Option Nat :=
    f.xInkTop.get.map fun ink => (ink.toNat * 1000 + f.unitsPerEm / 2) / f.unitsPerEm
  let read (name : String) : IO (Option Font) := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => return some f
    | .error _ => return none
  let gap (a b : Nat) : Nat := if a ≥ b then a - b else b - a
  match ← read "FiraSans-Regular.otf", FontDb.companionRow FontDb.monoCompanions "Fira Sans" with
  | some fira, some row =>
    t s!"the Fira row's x-height is the engine's own measure ({thousandths fira})"
      ((thousandths fira).any fun b => row.xHeights.any (·.1 == b) && row.body == fira.family)
  | _, _ => t "the suite's Fira Sans parses and its row is sourced" false
  match ← read "SourceSerifPro-Regular.otf", ← read "SourceCodePro-Regular.otf",
      FontDb.companionRow FontDb.monoCompanions "Source Serif Pro" with
  | some serif, some code, some row =>
    match thousandths serif, thousandths code with
    | some b, some c =>
      t s!"the companion row's x-heights are the engine's own measure ({b}, {c})"
        (row.xHeights == some (b, c) && row.companion == code.family && row.body == serif.family)
      t s!"the companion beats Latin Modern Mono on x-height, within the bound ({gap c b}, {gap FontDb.latinModernMonoXHeight b})"
        (gap c b < gap FontDb.latinModernMonoXHeight b &&
          gap c b * 100 ≤ FontDb.companionXHeightBound * b && FontDb.companionLeads row)
    | _, _ => t "the suite's pair measures its x-heights" false
  | _, _, _ => t "the suite's pair parses and its row is sourced" false
  let leads := (FontDb.monoCompanions.filter FontDb.companionLeads).map (·.body)
  t s!"every measured row is decided on the axis ({leads})"
    (leads == #["DejaVu Sans", "DejaVu Serif", "Fira Sans", "Source Sans Pro", "Source Serif Pro",
      "IBM Plex Sans", "IBM Plex Serif", "IBM Plex Sans Condensed", "Noto Sans", "Noto Serif"])
  t "a companion farther than Latin Modern Mono keeps lualatex's order"
    ((FontDb.companionRow FontDb.monoCompanions "Nimbus Sans").any (!FontDb.companionLeads ·))
  let probe (xs : Nat × Nat) : FontDb.Pairing :=
    { body := "Probe Sans", companion := "Probe Mono", source := "", license := "", xHeights := some xs }
  t "a nearer companion past the bound does not lead"
    (!FontDb.companionLeads (probe (600, 520)))
  t "an in-bound companion with Latin Modern Mono nearer does not lead"
    (!FontDb.companionLeads (probe (431, 450)))
  t "an in-bound companion nearer than Latin Modern Mono leads"
    (FontDb.companionLeads (probe (500, 510)))
  let none_ := DriverDiag.monoUpright "Noto Sans Mono"
  let some_ := DriverDiag.monoUpright "DejaVu Sans Mono"
  t "an italic-less monospace is offered a declaration, not an install"
    (none_.help.any (fun h => !hasStr h "install" && hasStr h "\\fonts{ mono")
      && some_.help.any (hasStr · "install")
      && (DriverDiag.monoUpright "Noto Sans Mono" (declarable := false)).help.isNone)

/-- A font collection's faces are fonts the engine can use: read, scanned, cached and shipped as
standalone files. -/
def fontCollectionChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let read (f : String) : IO ByteArray := IO.FS.readBinFile (testFonts ++ "/" ++ f)
  let regular ← read "OpenSans-Regular.ttf"
  let bold ← read "OpenSans-Bold.ttf"
  let code ← read "SourceCodePro-Regular.otf"
  let ttc := packCollection #[regular, bold]
  t "a packed collection counts its faces" (Font.collectionCount ttc == some 2)
  t "a standalone font is no collection" (Font.collectionCount regular == none)
  let same (a b : Font) : Bool :=
    a.family == b.family && a.weight == b.weight && a.isBold == b.isBold
      && a.unitsPerEm == b.unitsPerEm && a.numGlyphs == b.numGlyphs
      && "Quartz glyphs 0123".toList.all fun c => a.advance c == b.advance c
  for (i, orig) in [(0, regular), (1, bold)] do
    match Font.collectionMember ttc i, Font.parse orig with
    | .ok m, .ok of =>
      t s!"collection face {i}: every table is its file's, byte for byte"
        ((fontTables m).map (fun (tag, _, b) => (tag, b.toList)) ==
          (fontTables orig).map (fun (tag, _, b) => (tag, b.toList)))
      t s!"collection face {i}: a standalone font, parsed as its file is"
        (Font.collectionCount m == none && directoryFits m &&
          match Font.parse m with
          | .ok f => same f of
          | .error _ => false)
    | _, _ => t s!"collection face {i} reads" false
  t "an index past the collection's count is refused"
    (Font.collectionMember ttc 2 matches .error _)
  t "a standalone font is refused as a collection"
    (Font.collectionMember regular 0 matches .error _)
  let bounded (input m : ByteArray) : Bool :=
    directoryFits m && m.size ≤ input.size + 12 + 19 * Ink.u16 m 4
  let mut cases := 0
  let mut outside := 0
  for k in [0:97] do
    for i in [0:2] do
      cases := cases + 1
      let cut := ttc.extract 0 (ttc.size * k / 97)
      if let .ok m := Font.collectionMember cut i then
        unless bounded cut m do outside := outside + 1
  let dirEnd := 12 + 8 + (12 + 16 * Ink.u16 regular 4) + (12 + 16 * Ink.u16 bold 4)
  for pos in [0:dirEnd] do
    for v in ([0x00, 0x01, 0x7F, 0xFF] : List UInt8) do
      for i in [0:2] do
        cases := cases + 1
        let mutant := ttc.set! pos v
        if let .ok m := Font.collectionMember mutant i then
          unless bounded mutant m do outside := outside + 1
  t s!"truncated and mutated collections are refused or read in bounds ({outside} of {cases} outside)"
    (outside == 0 && cases > 2000)
  let repeated := Id.run do
    let records := 400
    let region := 4096
    let dir := 16
    let tables := dir + 12 + 16 * records
    let mut b := pushBe32 (pushBe32 (pushBe32 (pushBe32 ByteArray.empty 0x74746366) 0x00010000) 1) dir
    b := pushBe16 (pushBe16 (pushBe16 (pushBe16 (pushBe32 b 0x00010000) records) 256) 8) (records * 16 - 256 * 16)
    for k in [0:records] do
      b := pushBe32 (pushBe32 (pushBe32 (pushBe32 b (0x61610000 + k)) 0) tables) region
    for _ in [0:region] do
      b := b.push 0x41
    return b
  t "a directory naming one region again and again is refused"
    (Font.collectionCount repeated == some 1 &&
      Font.collectionMember repeated 0 matches .error _)
  let appleTagged := packCollection #[regular]
  let trueMember := pushBe32 (appleTagged.extract 0 (Ink.u32 appleTagged 12)) 0x74727565 ++
    appleTagged.extract (Ink.u32 appleTagged 12 + 4) appleTagged.size
  t "a face tagged true reads as its TrueType outlines"
    (match Font.collectionMember trueMember 0 with
      | .ok m => Ink.u32 m 0 == 0x00010000 && (Font.parse m).toOption.isSome
      | .error _ => false)
  let cache ← FontEnv.Cache.mk'
  IO.FS.withTempDir fun dir => do
    let file := (dir / "Example.ttc").toString
    let mono := (dir / "Mono.otc").toString
    IO.FS.writeBinFile file ttc
    IO.FS.writeBinFile mono (packCollection #[code])
    let faces ← FontDiscovery.scanRootsIn none [dir.toString]
    t "the scan finds each face a collection holds, under its member path"
      (faces.map (·.path) == #[FontDb.memberPath file 0, FontDb.memberPath file 1,
          FontDb.memberPath mono 0]
        && faces.map (·.family) == #["Open Sans", "Open Sans", "Source Code Pro"]
        && faces.map (·.weight) == #[400, 700, 400]
        && faces.map (·.fixedPitch) == #[false, false, true])
    let expected := #[FontDb.memberPath file 0, FontDb.memberPath file 1, FontDb.memberPath mono 0]
    IO.FS.withTempDir fun cacheDir => do
      let cold ← FontDiscovery.scanRootsIn (some cacheDir) [dir.toString]
      let warm ← FontDiscovery.scanRootsIn (some cacheDir) [dir.toString]
      t "a cached scan replays a collection's faces"
        (cold.map (·.path) == expected && warm.map (·.path) == expected
          && warm.map (·.family) == faces.map (·.family))
    let damaged := (dir / "Damaged.ttc").toString
    IO.FS.writeBinFile damaged (ttc.extract 0 200)
    let after ← FontDiscovery.scanRootsIn none [dir.toString]
    t "a truncated collection on disk adds no face; the others stand"
      (after.map (·.path) == expected)
    let member := FontDb.memberPath mono 0
    let doc := (elabMd "Words with `inline code` beside them.\n\n```\nfenced code\n```\n").1
    match ← buildFontSet doc (scanOf (unpaired ++ family4 "Menlo" member true)) cache .settled,
        Font.collectionMember (packCollection #[code]) 0 with
    | .ok (fs, resolved, diags, paths), .ok standalone =>
      let slot := fs.lookup 2 400 false
      let face := fs.get slot
      t "a collection's face fills the typewriter slot through the assembly"
        (paths.contains member && face.isFixedPitch && !fs.slotCollapsed 2
          && !diags.any (·.kind == .E0404))
      t "the page's code runs set in the collection's face"
        (runFace (layoutOf fs resolved) "fenced" == some slot && face.isFixedPitch)
      let (html, _) := HtmlDoc.emit { fonts := some fs } resolved
      t "the HTML ships the collection's face as a standalone file"
        (monoSrc html == some (HtmlDoc.fontResource face).uri
          && (HtmlDoc.fontResource face).bytes == standalone
          && Font.collectionCount (HtmlDoc.fontResource face).bytes == none)
    | _, _ => t "a collection's face assembles and reads" false

/-- A face set whose every key is its own face, so a shipped run's face index reads back to the key
it asked, and those keys. -/
def keyedFaces (font : Font) : Font.FontSet × Array (Nat × Nat × Bool) :=
  let keys := ((List.range 3).flatMap fun slot =>
    ([100, 200, 300, 400, 500, 600, 700, 800, 900] : List Nat).flatMap fun w =>
      [(slot, w, false), (slot, w, true)]).toArray
  ({ fonts := Array.replicate keys.size font, index := keys.zipIdx }, keys)

/-- The keys a laid-out document's shipped runs asked, read off their face indices. -/
def shippedKeys (keys : Array (Nat × Nat × Bool)) (out : Layout.Out) :
    Array (Nat × Nat × Bool) :=
  out.pages.foldl (init := #[]) fun acc p => p.lines.foldl (init := acc) fun acc l =>
    l.segs.foldl (init := acc) fun acc s =>
      match s with
      | .run idx _ _ _ glyphs _ _ _ _ _ _ =>
        match keys[idx]? with
        | some k => if glyphs.isEmpty || acc.contains k then acc else acc.push k
        | none => acc
      | _ => acc

/-- Documents whose italic code stands where a census could miss it, or seems to stand where none is
set. -/
def faceKeyProbes : List (String × String) :=
  [("a heading's italic template", dvDoc "\\style{section}{ font = {\\itshape} }\n"
      "\\section{About \\texttt{code}}\nText."),
   ("a KOMA heading font", "\\documentclass{scrartcl}\n\\setkomafont{section}{\\itshape}\n" ++
      "\\begin{document}\n\\section{About \\texttt{code}}\nText.\n\\end{document}"),
   ("a title's template", dvDoc "\\style{titlepage}{ font = {\\itshape} }\n\\title{About \\texttt{code}}\n"
      "\\maketitle\nText."),
   ("a block title's template", "\\documentclass{slides}\n\\style{block}{ font = {\\itshape} }\n" ++
      "\\begin{document}\n\\begin{frame}\n\\begin{block}{About \\texttt{code}}\nText.\n" ++
      "\\end{block}\n\\end{frame}\n\\end{document}"),
   ("a template no element uses", dvDoc "\\style{subsubsection}{ font = {\\itshape\\ttfamily} }\n"
      "Plain \\texttt{upright code} and no such heading."),
   ("an italic over empty code", dvDoc "" "Plain \\texttt{upright code} and \\textit{words \\texttt{}}."),
   ("a switch with nothing after it", dvDoc "" "Plain \\texttt{upright code} and {\\itshape words\\ttfamily}."),
   ("italic code in a footnote and a caption", dvDoc ""
      ("Text\\footnote{A \\textit{\\texttt{noted}} run.}.\n\n\\begin{figure}\\centering x" ++
       "\\caption{A \\textit{\\texttt{captioned}} run.}\\end{figure}")),
   ("a listing's comment", dvDoc "" "\\begin{lstlisting}[language=Python]\n# a remark\nx = 1\n\\end{lstlisting}"),
   ("a theorem's italic body", dvDoc "\\newtheorem{theorem}{Theorem}\n"
      "\\begin{theorem}A \\texttt{coded} claim.\\end{theorem}")]

/-- The italic census `Layout.docFaceKeys` reads before layout matches the italic typewriter keys
the shipped runs ask. -/
def faceKeyAgreementChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some font ← loadTestFont "OpenSans-Regular.ttf"
    | t "face key agreement: the face loads" false
  let (fs, keys) := keyedFaces font
  let italicMono (ks : Array (Nat × Nat × Bool)) : Bool := ks.any fun (s, _, i) => s == 2 && i
  let mut docs : Array (String × Ir.Doc) := #[]
  for (what, src) in faceKeyProbes do
    docs := docs.push (what, (elabStr src).1)
  for n in goldenNames do
    docs := docs.push (s!"fixture {n}", (← goldenDoc n).1)
  let mut set := 0
  for (what, doc) in docs do
    let shipped := italicMono (shippedKeys keys (layoutOf fs doc))
    let census := italicMono (Layout.docFaceKeys doc)
    if shipped then set := set + 1
    t s!"face key agreement {what}: the census names italic code where the page sets it \
(census {census}, page {shipped})" (census == shipped)
  t s!"face key agreement: the documents set italic code and not ({set} of {docs.size})"
    (set ≥ 6 && set < docs.size)

end Tests.MonoDefault
