module

public import Tests.NfcBoundary
public import LeanTex.Cli.FontDiscovery
public import Tests.SlotLossWording
public import Tests.Support
public import Tests.Artifact
public import LeanTex.Core.FontSubset
public import LeanTex.Core.CaseFold

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj)

/-- A synthetic face for resolution-order tests: pure data, no host fonts. -/
def synthFace (family : String) (path : String := "") : FontDb.Face :=
  { path := if path.isEmpty then "/x/" ++ family ++ ".ttf" else path
    family := family
    subfamily := "Regular"
    bold := false
    italic := false
    fixedPitch := false
    weight := 400 }

/-- The weight axis's string half: parsing inverts printing over every series, the NFSS combination
rules hold, and OS/2 500 reads as the `m` series. -/
def weightAxisChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "every series round-trips through its NFSS spelling"
    (Ir.Weight.all.all fun w => Ir.Weight.parseSeries w.series == some (w, ""))
  t "bx is bold extended" (Ir.Weight.parseSeries "bx" == some (.b, "x"))
  t "c is medium condensed" (Ir.Weight.parseSeries "c" == some (.m, "c"))
  t "an unknown series value is refused" ((Ir.Weight.parseSeries "zz").isNone)
  t "a weight code with a non-width remainder is refused"
    ((Ir.Weight.parseSeries "bq").isNone)
  t "OS/2 500 reads as the m series (ties to the lighter)"
    (Ir.Weight.ofCss 500 == .m)

/-- The font diagnostics: a missing family suggests its neighbours instead of
dumping a thousand names, and `families` names each family once. -/
def fontDiagChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fams := #["Nimbus Sans L", "Nimbus Mono", "Latin Modern Roman", "Arial",
    "Libertinus Serif", "Libertinus Sans", "DejaVu Sans"]
  let near := FontDb.nearest fams "Nimbus Roman"
  t "nearest shares a word" (near.contains "Nimbus Sans L" && near.contains "Nimbus Mono")
  t "nearest ranks two shared words first"
    ((FontDb.nearest fams "Libertinus Serif Display")[0]? == some "Libertinus Serif")
  t "nearest omits the unrelated" (!near.contains "Arial" && !near.contains "DejaVu Sans")
  t "nearest of nothing alike is empty" ((FontDb.nearest fams "Zapfino").isEmpty)
  t "nearest caps at eight"
    ((FontDb.nearest ((List.range 20).map fun i => s!"Test Face {i}").toArray "Test").size ≤ 8)
  -- A TeX Live shape: ~3000 faces in ~1000 families, distinct so dedupe is checked exactly.
  let many := ((List.range 3000).map fun i => synthFace s!"Family {i / 3}" s!"/x/{i}.otf").toArray
  let t0 ← IO.monoMsNow
  let fams' := FontDb.families many
  -- Consumed before the clock is read again: a pure `let` floats to its first use.
  t "families dedupes" (fams'.size == 1000)
  let ms := (← IO.monoMsNow) - t0
  t s!"hang guard: families of {many.size} faces within {hangGuardMs 5} ms ({ms} ms)"
    (ms < hangGuardMs 5)
  let light : FontDb.Face := { synthFace "Alpha Sans" "/x/as-l.otf" with
    subfamily := "Light", weight := 300 }
  let lightIt : FontDb.Face := { light with
    path := "/x/as-li.otf", subfamily := "Light Italic", italic := true }
  let faces := #[synthFace "Alpha Sans", light, lightIt]
  t "family plus subfamily names a face"
    ((FontDb.resolve faces "Alpha Sans Light" {}).map (·.1.subfamily) == some "Light")
  t "the named face's italic sibling resolves satisfied"
    ((FontDb.resolve faces "Alpha Sans Light" { italic := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Light Italic", true))
  t "the named face's bold is unsatisfied, never silently heavier"
    ((FontDb.resolve faces "Alpha Sans Light" { bold := true }).map
      (fun r => (r.1.subfamily, r.2)) == some ("Light", false))
  t "a real family name still resolves its regular"
    ((FontDb.resolve faces "Alpha Sans" {}).map (·.1.subfamily) == some "Regular")

/-- The weight axis below the driver: `\fonts` series spellings, exact resolution for an installed
weight, the nearest with W0366 for a missing one, categorical italic, the declared-face override,
and `docWeightKeys`. -/
def weightResolveChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  let d := (elabStr (pre ++ "\\fonts{ body = \"X\", body.l = \"X Light\", " ++
    "body.sb.italic = \"X SemiBold Italic\" }" ++ post)).1.fonts
  t "fonts body.l names the Light face" (d.faceFor 0 300 false == some "X Light")
  t "fonts body.sb.italic names the semibold italic"
    (d.faceFor 0 600 true == some "X SemiBold Italic")
  t "a width half stays an unknown key"
    (errCodes (pre ++ "\\fonts{ body.bx = \"Y\" }" ++ post) == ["E0322"])
  -- A substitution's words, then its site's particulars (the weights).
  let subMsg : Option FontDb.Substituted → Option String
    | some s => some ((DriverDiag.substituted s).message ++
        ((DriverDiag.substituted s).detail.map ("; " ++ ·)).getD "")
    | none => none
  let light : FontDb.Face := { synthFace "Alpha Sans" "/x/as-l.otf" with
    subfamily := "Light", weight := 300 }
  let lightIt : FontDb.Face := { light with
    path := "/x/as-li.otf", subfamily := "Light Italic", italic := true }
  let faces := #[synthFace "Alpha Sans", light, lightIt]
  t "an installed weight resolves exactly and silently"
    ((FontDb.resolveWeight faces "Alpha Sans" none 300 false).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", none))
  t "italic is categorical on the axis"
    ((FontDb.resolveWeight faces "Alpha Sans" none 300 true).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light Italic", none))
  t "a missing weight takes the nearest and says both numbers"
    ((FontDb.resolveWeight faces "Alpha Sans" none 200 false).map
      (fun r => (r.1.subfamily,
        (subMsg r.2).getD "" |>.endsWith "weight 200 asked, weight 300 the nearest")) ==
      some ("Light", true))
  t "a declared face for a weight key is met exactly"
    ((FontDb.resolveWeight faces "Alpha Sans" (some "Alpha Sans Light") 300 false).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", none))
  t "a declared face the host lacks degrades and says so"
    (((FontDb.resolveWeight faces "Alpha Sans" (some "Nope Light") 300 false).map
      (fun r => (subMsg r.2).getD "")).getD "" ==
      "substituted face 'Alpha Sans Light' for 'Alpha Sans weight 300'; 'Nope Light' is not installed")
  -- A family spelled as a face file names its own upright face, not the family's first member.
  let five : FontDb.Face := { synthFace "Delta Roman" "/x/delta5-regular.otf" with subfamily := "Regular" }
  let ten : FontDb.Face := { synthFace "Delta Roman" "/x/delta10-regular.otf" with subfamily := "Regular" }
  t "a family spelled as a face file resolves its upright face to that file"
    ((FontDb.resolveVariant #[five, ten] "delta10-regular.otf" none {}).map (·.1.path) ==
      some "/x/delta10-regular.otf")
  t "the 400 and 700 corners stay resolveVariant's"
    ((FontDb.resolveWeight faces "Alpha Sans" none 700 false).map
        (fun r => (r.1.subfamily, subMsg r.2)) ==
      (FontDb.resolveVariant faces "Alpha Sans" none { bold := true }).map
        (fun r => (r.1.subfamily, subMsg r.2)))
  let doc : Ir.Doc := { body := #[.para #[.styled (.series .l)
    #[.text "x", .styled .italic #[.text "y"]]]] }
  t "docWeightKeys folds the styled ancestry"
    (Layout.docWeightKeys doc == #[(0, 300, false), (0, 300, true)])
  let corner : Ir.Doc := { body := #[.para #[.styled .bold #[.text "x"]]] }
  t "corner weights collect no extra keys" ((Layout.docWeightKeys corner).isEmpty)
  let (fsDoc, fsDs) := elabStr (pre ++ "\\begin{document}{\\fontseries{l}\\selectfont x}\\end{document}")
  t "fontseries elaborates clean" (fsDs.filter (·.severity == .error) |>.isEmpty)
  t "fontseries reaches the key census"
    (Layout.docWeightKeys fsDoc == #[(0, 300, false)])
  t "a width half warns by name and keeps its weight"
    ((elabStr (pre ++ "\\begin{document}{\\fontseries{bx}\\selectfont x}\\end{document}")).2.map
      (·.code) |>.contains "W0104")
  t "an unknown series warns and stands down"
    ((elabStr (pre ++ "\\begin{document}{\\fontseries{zz}\\selectfont x}\\end{document}")).2.map
      (·.code) |>.contains "W0104")
  let ff := (elabStr (pre ++ "\\setmainfont{Alpha Sans}[UprightFont=*-Medium, " ++
    "FontFace={l}{n}{*-Light}]" ++ post)).1.fonts
  t "FontFace declares the series face" (ff.faceFor 0 300 false == some "Alpha Sans-Light")
  t "FontFace rides beside UprightFont" (ff.faceFor 0 400 false == some "Alpha Sans-Medium")
  t "a FontFace shape off the model is named"
    ((elabStr (pre ++ "\\setmainfont{Alpha Sans}[FontFace={l}{sc}{*-Light}]" ++ post)).2.map
      (·.code) |>.contains "W0104")
  let seriesText (doc : Ir.Doc) : List String :=
    doc.body.toList.flatMap fun b => match b with
      | .para content =>
        Ir.foldInlines (fun acc x => match x with
          | .styled (.series _) body =>
            acc ++ [(Ir.plainTextList body.toList).trimAscii.toString]
          | _ => acc) [] content
      | _ => []
  let (spellDoc, _) := elabStr (pre ++
    "\\newcommand{\\quiet}{\\fontseries{l}\\selectfont}" ++
    "\\begin{document}{\\quiet x} y\\end{document}")
  t "a spelling's trailing declaration styles the rest of its group"
    (seriesText spellDoc == ["x"])

/-- fontspec's per-variant face options reach the font spec and win over the family's own variant,
and a declared face the host lacks degrades with a message naming the face used. -/
def declaredFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  let d := (elabStr (pre ++ "\\setsansfont[ItalicFont={Alpha Sans Light Italic}, " ++
    "BoldFont={Alpha Sans}, BoldItalicFont={Alpha Sans Italic}]{Alpha Sans Light}" ++
    post)).1.fonts
  t "compat sans family" (d.sans == some "Alpha Sans Light")
  t "compat BoldFont" (d.faceFor 1 700 false == some "Alpha Sans")
  t "compat ItalicFont" (d.faceFor 1 400 true == some "Alpha Sans Light Italic")
  t "compat BoldItalicFont" (d.faceFor 1 700 true == some "Alpha Sans Italic")
  t "compat no UprightFont declared" (d.faceFor 1 400 false == none)
  let d2 := (elabStr (pre ++
    "\\setsansfont{Open Sans}[Path = fonts/, BoldFont = OpenSans-Bold.ttf]" ++ post)).1.fonts
  t "compat BoldFont after the name" (d2.faceFor 1 700 false == some "OpenSans-Bold.ttf")
  let d3 := (elabStr (pre ++ "\\fonts{ body = \"X\", body.bold = \"Y\", " ++
    "mono.upright = \"Z\" }" ++ post)).1.fonts
  t "fonts body.bold" (d3.faceFor 0 700 false == some "Y")
  t "fonts mono.upright" (d3.faceFor 2 400 false == some "Z")
  t "fonts unknown variant key" (errCodes (pre ++ "\\fonts{ body.slanted = \"Y\" }" ++ post)
    == ["E0322"])
  t "fonts variant wrong type" (errCodes (pre ++ "\\fonts{ body.bold = 12 }" ++ post)
    == ["E0323"])
  let d4 := (elabStr (pre ++ "\\setsansfont[UprightFont=*-Semibold]{Ordwick}" ++ post)).1.fonts
  t "fontspec * expands to the family name" (d4.faceFor 1 400 false == some "Ordwick-Semibold")
  -- A substitution's words, then its site's particulars (the weights).
  let subMsg : Option FontDb.Substituted → Option String
    | some s => some ((DriverDiag.substituted s).message ++
        ((DriverDiag.substituted s).detail.map ("; " ++ ·)).getD "")
    | none => none
  let light : FontDb.Face := { synthFace "Alpha Sans" "/x/as-l.otf" with
    subfamily := "Light", weight := 300 }
  let lightIt : FontDb.Face := { light with
    path := "/x/as-li.otf", subfamily := "Light Italic", italic := true }
  let faces := #[synthFace "Alpha Sans", light, lightIt]
  t "declared bold face is honoured, no warning"
    ((FontDb.resolveVariant faces "Alpha Sans Light" (some "Alpha Sans") { bold := true }).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Regular", none))
  t "declared italic face is honoured"
    ((FontDb.resolveVariant faces "Alpha Sans" (some "Alpha Sans Light Italic")
      { italic := true }).map (fun r => (r.1.subfamily, subMsg r.2)) ==
        some ("Light Italic", none))
  t "declared face the host lacks degrades and says so"
    ((FontDb.resolveVariant faces "Alpha Sans Light" (some "Nope Sans") { bold := true }).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", some
        "substituted face 'Alpha Sans Light' for 'Alpha Sans Light Bold'; 'Nope Sans' is not installed"))
  t "substitution names the face actually used"
    ((FontDb.resolveVariant faces "Alpha Sans Light" none { bold := true }).map
      (subMsg ·.2) ==
      some (some "substituted face 'Alpha Sans Light' for 'Alpha Sans Light Bold'"))
  t "a satisfied variant carries no message"
    ((FontDb.resolveVariant faces "Alpha Sans" none {}).map (subMsg ·.2) == some none)
  t "a missing family is still the caller's W0403"
    ((FontDb.resolveVariant faces "Nope Sans" (some "Also Nope") { bold := true }).isNone)
  let beta700 : FontDb.Face := { synthFace "Beta Sans" "/x/bs-b.otf" with
    subfamily := "Bold", bold := true, weight := 700 }
  let betas := #[synthFace "Beta Sans" "/x/bs-r.otf", beta700]
  t "a missing weight resolves to the nearest installed weight"
    ((FontDb.resolveVariant betas "Beta Sans Light" none {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Regular",
        some ("substituted face 'Beta Sans Regular' for 'Beta Sans Light'; " ++
          "weight 300 asked, weight 400 the nearest")))
  t "a declared weighted face the host lacks takes the nearest weight"
    ((FontDb.resolveVariant betas "Beta Sans" (some "Beta Sans Medium") {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Regular",
        some ("substituted face 'Beta Sans Regular' for 'Beta Sans Medium'; " ++
          "weight 500 asked, weight 400 the nearest")))
  let betaLight : FontDb.Face := { synthFace "Beta Sans" "/x/bs-l.otf" with
    subfamily := "Light", weight := 300 }
  t "an installed weight is served exactly and stays silent"
    ((FontDb.resolveVariant (betas.push betaLight) "Beta Sans Light" none {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", none))
  let shipped ← FontDiscovery.scanRoots [testFonts]
  t "a declared file name denotes that exact face"
    ((FontDb.resolveVariant shipped "Open Sans" (some "SourceSerifPro-Bold.otf")
      { bold := true }).map (fun r => (r.1.path, subMsg r.2)) ==
      some (testFonts ++ "/SourceSerifPro-Bold.otf", none))

/-- fontawesome5 spellings elaborate to `Inline.icon`, set from the face covering their scalar
without W0009, hidden from assistive technology behind a named wrapper in HTML, and read as their
text in the markdown twin. -/
def iconChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let wrap (body : String) : String := dvDoc "" body
  let (doc, ds) := elabStr (wrap
    "\\faGithub{} \\faIcon{arrow-up} \\faIcon[label = Return to top]{arrow-up} x")
  t "icons source clean" ds.isEmpty
  let icons : Array (Char × String) := match doc.body[0]? with
    | some (Ir.Block.para xs) => xs.filterMap fun x => match x with
      | Ir.Inline.icon c label => some (c, label)
      | _ => none
    | _ => #[]
  t "the per-icon command carries the package's scalar and Font Awesome's label"
    (icons[0]? == some ('\uF09B', "GitHub"))
  t "the generic spelling resolves by icon name"
    (icons[1]? == some ('\uF062', "arrow-up"))
  t "label = overrides the default text alternative"
    (icons[2]? == some ('\uF062', "Return to top"))
  t "an unknown icon name is E0340, dropped"
    (errCodes (wrap "\\faIcon{no-such-icon} x") == ["E0340"])
  t "an unmodelled \\faIcon option is named W0110"
    (warnCodes (wrap "\\faIcon[regular]{envelope} x") == ["W0110"])
  let page := (HtmlDoc.emit {} doc).1
  let has := hasStr page
  t "html hides the glyph and names the icon"
    (has ("<span class=\"icon\" role=\"img\" aria-label=\"GitHub\">" ++
      "<span aria-hidden=\"true\">\uF09B</span></span>"))
  t "html carries the overridden name"
    (has "aria-label=\"Return to top\"")
  t "no icon renders with an empty accessible name" (!has "aria-label=\"\"")
  let md := (MarkdownDoc.emit doc)
  t "markdown renders the text alternative, never the raw scalar"
    ((md.splitOn "GitHub").length ≥ 2 && (md.splitOn "\uF09B").length == 1)
  let load (name : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"icons: {name} unparsable: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let iconsFace ← load "ExampleIcons-Regular.ttf"
  let italicFace ← load "OpenSans-Italic.ttf"
  t "the parser reads the declared slant from post"
    (italicFace.italicAngle == -12 && sans.italicAngle == 0)
  t "coverage premise: only the invented icon face has U+F09B"
    ((sans.gid '\uF09B').isNone && (iconsFace.gid '\uF09B').isSome)
  -- Every fixture face has a space glyph, so the fallback arms run on cmap-filtered copies.
  t "spaceAdvance is the space glyph's advance where one exists"
    (sans.spaceAdvance == sans.advance ' ' && sans.advance ' ' > 0)
  let noSpace : Font :=
    { sans with cmap := sans.cmap.filter fun r => r.1 > 32 || r.2.1 < 32 }
  t "a face without a space glyph takes half the em dash"
    (noSpace.advance ' ' == 0 &&
     noSpace.spaceAdvance == noSpace.advance '—' / 2 && noSpace.spaceAdvance > 0)
  let dash := '—'.toNat.toUInt32
  let noDash : Font :=
    { noSpace with cmap := noSpace.cmap.filter fun r => r.1 > dash || r.2.1 < dash }
  t "a face without space or em dash takes half the em"
    (noDash.advance '—' == 0 && noDash.spaceAdvance == noDash.unitsPerEm / 2)
  let allVariants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let bare : Font.FontSet := {
    fonts := #[sans, iconsFace]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let mapped : Font.FontSet := { bare with fallback := #[('\uF09B', 1)] }
  let geom : Layout.Geom := {}
  let (glyphDoc, _) := elabStr (wrap "\\faGithub{} beside words")
  let out := layoutOf mapped glyphDoc geom
  let runs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  t "the icon glyph ships from the covering face"
    (runs.any fun s => match s with
      | .run 1 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '\uF09B')
      | _ => false)
  t "a deliberate icon face is not a substitution warning"
    (!out.diags.any (·.code == "W0009"))
  let dropOut := layoutOf bare glyphDoc geom
  t "an uncovered icon is the ordinary coverage loss, naming the scalar"
    ((dropOut.diags.filter (·.code == "E0405")).any
      fun d => (d.message.splitOn "U+F09B").length ≥ 2)
  t "docScalars carries the icon scalar" ((Layout.docScalars glyphDoc).contains '\uF09B')

/-- The GSUB small-caps parse over every shipped face: which carry `smcp` and `c2sc`, and that the
composed map is uniform. -/
def smallCapsGsubChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"smallcaps: {name} unparsable: {e}")
  let features (name : String) : IO (Bool × Bool × Bool) := do
    let f ← load name
    pure (f.hasSmcp, f.hasC2sc, !f.smallCaps.isEmpty)
  -- The italic Source Serif faces ship without small caps: the font's own choice.
  t "source serif regular carries smcp+c2sc"
    ((← features "SourceSerifPro-Regular.otf") == (true, true, true))
  t "source serif bold carries smcp+c2sc"
    ((← features "SourceSerifPro-Bold.otf") == (true, true, true))
  t "fira sans carries smcp+c2sc"
    ((← features "FiraSans-Regular.otf") == (true, true, true))
  t "source serif italic carries neither feature"
    ((← features "SourceSerifPro-RegularIt.otf") == (false, false, false))
  t "source serif bold italic carries neither feature"
    ((← features "SourceSerifPro-BoldIt.otf") == (false, false, false))
  t "open sans carries neither feature"
    ((← features "OpenSans-Regular.ttf") == (false, false, false))
  t "source code pro carries neither feature"
    ((← features "SourceCodePro-Regular.otf") == (false, false, false))
  t "fira math carries neither feature"
    ((← features "FiraMath-Regular.otf") == (false, false, false))
  t "the icon face carries neither feature"
    ((← features "ExampleIcons-Regular.ttf") == (false, false, false))
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraSans-Regular.otf"
  let uniform (f : Font) : Bool := Id.run do
    for i in [0:26] do
      let up := (f.gid (Char.ofNat ('A'.toNat + i))).getD 0
      let low := (f.gid (Char.ofNat ('a'.toNat + i))).getD 0
      unless f.smallCapGid up == f.smallCapGid low &&
          f.smallCapGid up != up && f.smallCapGid low != low do
        return false
    return true
  t "source serif maps both cases of every letter to one small-cap glyph"
    (uniform serif)
  t "fira sans maps both cases of every letter to one small-cap glyph"
    (uniform fira)
  let sans ← load "OpenSans-Regular.ttf"
  t "a face without the features maps every gid to itself"
    ((sans.gid 'a').all fun g => sans.smallCapGid g == g)
  let geom : Layout.Geom := {}
  let allVariants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let set (f : Font) : Font.FontSet := {
    fonts := #[f]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let drawn (fs : Font.FontSet) (src : String) : Array (Array (Nat × Char × Dim.Length) × Dim.Length) :=
    (bodyLines (layoutOf fs (Elab.run "t" src).1 geom)).flatMap
      (fun l => (unindented l).filterMap fun s =>
        match s with
        | .run _ _ _ _ glyphs size _ _ _ _ _ => some (glyphs, size)
        | _ => none)
  let ink (rs : Array (Array (Nat × Char × Dim.Length) × Dim.Length)) : Array (Nat × Dim.Length) :=
    rs.flatMap fun (glyphs, size) => glyphs.map fun (g, _) => (g, size)
  let scSerif := drawn (set serif) "{\\scshape NaCl}"
  t "gsub small caps draw the same ink for NaCl, nacl, and NACL"
    (ink scSerif == ink (drawn (set serif) "{\\scshape nacl}") &&
     ink scSerif == ink (drawn (set serif) "{\\scshape NACL}") &&
     ink scSerif != ink (drawn (set serif) "NaCl"))
  t "gsub small caps set at full size with substituted glyphs, text as typed"
    (scSerif.all (·.2 == geom.fontSize) &&
     (scSerif.flatMap (·.1.map (·.2.1))) == #['N', 'a', 'C', 'l'] &&
     scSerif.all fun (glyphs, _) => glyphs.all fun (g, c, _) =>
       some g == (serif.gid c).map serif.smallCapGid)
  let scSans := drawn (set sans) "{\\scshape NaCl}"
  t "synthesised small caps draw the same ink for NaCl, nacl, and NACL"
    (ink scSans == ink (drawn (set sans) "{\\scshape nacl}") &&
     ink scSans == ink (drawn (set sans) "{\\scshape NACL}") &&
     ink scSans != ink (drawn (set sans) "NaCl"))
  t "synthesised small caps set every letter at one reduced size"
    (!scSans.isEmpty &&
     scSans.all (·.2 == geom.fontSize * Layout.smallCapScaleFor sans / 1000))
  t "synthesised small caps draw accented and special-cased letters in their capitals"
    (ink (drawn (set sans) "{\\scshape café straße}") ==
      ink (drawn (set sans) "{\\scshape CAFÉ STRASSE}"))
  t "the uppercase mapping is Unicode's full one"
    (CaseFold.upper "éàœß ﬁ ǆ σς" == "ÉÀŒSS FI Ǆ ΣΣ")
  t "synthesised small caps keep a letter whose capitals hold a combining mark or a glyph the face lacks"
    (((ink (drawn (set sans) "{\\scshape ǰ}")).map (·.1)).toList == (sans.gid 'ǰ').toList &&
      Layout.smallCapLetters (fun _ => true) #['ß', 'ǰ', 'a'] ==
        (#['S', 'S', 'ǰ', 'A'], #[2, 1, 1]) &&
      Layout.smallCapLetters (· != 'É') #['é'] == (#['é'], #[1]))
  let fira ← load "FiraSans-Regular.otf"
  let withFallback : Font.FontSet := { set sans with fonts := #[sans, fira], fallback := #[('Ƒ', 1)] }
  let runsOf (fs : Font.FontSet) (src : String) : Array (Nat × Array Nat) :=
    (bodyLines (layoutOf fs (Elab.run "t" src).1 geom)).flatMap
      (fun l => (unindented l).filterMap fun s =>
        match s with
        | .run idx _ _ _ glyphs _ _ _ _ _ _ => some (idx, glyphs.map (·.1))
        | _ => none)
  t "synthesised small caps set a capital the face lacks from the fallback face, else keep the letter"
    ((runsOf withFallback "{\\scshape ƒ}").any (· == (1, (fira.gid 'Ƒ').toArray)) &&
      (runsOf (set sans) "{\\scshape ƒ}") == #[(0, (sans.gid 'ƒ').toArray)])
  let (scDoc, scDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "{\\scshape NaCl}\\end{document}")
  t "small caps html source clean" scDs.isEmpty
  let scTree := HtmlDoc.blockNode {} scDoc.body[0]!
  let scText : Html.Node → Bool
    | .elem _ attrs kids => attrs.contains ("class", "sc") && kids.any fun k =>
        match k with
        | .text s => s == "NaCl"
        | _ => false
    | _ => false
  let hasScText : Html.Node → Bool
    | .elem _ _ kids => kids.any fun k => scText k ||
        match k with
        | .elem _ _ kids2 => kids2.any scText
        | _ => false
    | n => scText n
  t "the typed tree carries the authored casing under the sc class"
    (scText scTree || hasScText scTree)
  t "the stylesheet asks for uniform small caps"
    (((HtmlDoc.emit {} scDoc).1.splitOn
      ".sc { font-variant-caps: all-small-caps; }").length == 2)

/-- Per-glyph fallback: a scalar the styled face lacks is set from the mapped face at the same size
and named once per family and glyph, an uncovered one is E0405, and a covered document is
byte-identical. -/
def fallbackChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"fallback: {name} unparsable: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let code ← load "SourceCodePro-Regular.otf"
  t "coverage premise: only the code face has U+2200"
    ((sans.gid '∀').isNone && (code.gid '∀').isSome)
  t "coverage premise: no shipped face has U+27E8"
    ((sans.gid '⟨').isNone && (code.gid '⟨').isNone)
  let geom : Layout.Geom := {}
  let allVariants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let bare : Font.FontSet := {
    fonts := #[sans, code]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 1).toArray
  }
  let mapped : Font.FontSet := { bare with fallback := #[('∀', 1)] }
  let (faDoc, faDs) := Elab.run "t" "for all is ∀ set\n\nagain ∀ here"
  t "fallback source clean" faDs.isEmpty
  let out := layoutOf mapped faDoc geom
  let runs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  t "fallback sets the glyph from the mapped face"
    (runs.any fun s => match s with
      | .run 1 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '∀')
      | _ => false)
  t "fallback reports once per family+glyph, naming both faces"
    ((out.diags.filter (·.code == "W0009")).map
      (fun d => (d.message, d.triggerText, d.recovery)) ==
      #[("substituted font 'Source Code Pro' for font 'Open Sans'", none,
        some (.replacedBy "a glyph from 'Source Code Pro'"))])
  t "a covered scalar raises no E0405" (!out.diags.any (·.code == "E0405"))
  let (dropDoc, _) := Elab.run "t" "lost ⟨ here\n\nand ⟨ there"
  let dropOut := layoutOf mapped dropDoc geom
  t "an uncovered scalar drops once, naming the family"
    ((dropOut.diags.filter (·.code == "E0405")).map
      (fun d => (d.message, d.triggerText, d.recovery)) ==
      #[("missing glyph U+27E8 for font 'Open Sans'", none, some .skipped)])
  let (plainDoc, _) := Elab.run "t" "plain words only"
  let noMap := Pdf.write geom bare (layoutOf bare plainDoc geom).pages
  let withMap := Pdf.write geom
    { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
    (layoutOf { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
      plainDoc geom).pages
  t "a covered document is byte-identical under any map" (noMap == withMap)
  let (scDoc, _) := Elab.run "t"
    "\\section{Tz}\n\n{\\scshape hi}\\,x\n\n\\begin{verbatim}q r\\end{verbatim}"
  let scalars := Layout.docScalars scDoc
  t "docScalars carries text, titles, and verbatim"
    (scalars.contains 'T' && scalars.contains 'z' && scalars.contains 'x' &&
      scalars.contains 'q' && scalars.contains 'r')
  t "docScalars carries the uppercase small caps set"
    (scalars.contains 'H' && scalars.contains 'I')
  -- NFC at input composes e + U+0301 before any face is consulted, so é is a plain cmap hit.
  let (accDoc, accDs) := Elab.run "t" "Cafe\u0301 and \\textbf{Cafe\u0301}"
  t "combining source clean" accDs.isEmpty
  let accOut := layoutOf mapped accDoc geom
  let accGlyphs := ((accOut.pages.flatMap (·.lines)).flatMap (·.segs)).flatMap
    fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.map (·.2.1)
      | _ => #[]
  t "a combining sequence ships composed, no mark machinery"
    (accGlyphs.contains 'é' && !accGlyphs.contains '\u0301' &&
      !accOut.diags.any fun d => d.code == "W0009" || d.code == "E0405")
  t "the base letters survive whatever the mark does" (accGlyphs.contains 'C')
  let icons ← load "ExampleIcons-Regular.ttf"
  t "premise: the icon face lacks the composed form"
    ((icons.gid 'é').isNone)
  let iconSet : Font.FontSet := {
    fonts := #[icons]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let dropAcc := layoutOf iconSet accDoc geom
  t "a face lacking the composed form, with no fallback, drops it loudly by name"
    (dropAcc.diags.any fun d => d.code == "E0405" && hasStr d.message "U+00E9")
  t "docScalars excludes whitespace and kerns"
    (!scalars.contains ' ' && !scalars.contains '\u2009' && !scalars.contains '\u00a0')
  t "docScalars is sorted" (scalars == scalars.qsort (· < ·))
  let shipped ← FontDiscovery.scanRoots [testFonts]
  let picks ← FontDiscovery.fallbackPicks shipped #['∀', '₿', '𓀀']
  t "picks the first covering family in sorted order"
    (picks.contains ('∀', testFonts ++ "/FiraMath-Regular.otf"))
  t "picks the regular face of a family with variants"
    (picks.contains ('₿', testFonts ++ "/SourceSerifPro-Regular.otf"))
  t "a scalar no face covers is absent from the picks"
    (!picks.any (·.1 == '𓀀'))
  t "companion branch: Fira Sans finds Fira Math with its sourced row"
    ((← FontDiscovery.pickMathFace shipped "Fira Sans").map
        (fun (f, r) => (f.family, (r.map (·.license)).getD "")) ==
      some ("Fira Math", "SIL Open Font License"))
  t "no-companion branch: the first MATH-table face serves, rowless"
    ((← FontDiscovery.pickMathFace shipped "Source Serif Pro").map
        (fun (f, r) => (f.family, r.isNone)) == some ("Fira Math", true))
  -- −41 is hb-shape's value for Source Serif Pro "Ta" at upem 1000; Open Sans ships no pairs.
  let ssp ← load "SourceSerifPro-Regular.otf"
  let sspT := (ssp.gid 'T').getD 0
  let sspA := (ssp.gid 'a').getD 0
  t "kern: Source Serif Pro Ta matches hb-shape"
    (ssp.kernAdv sspT sspA == -41)
  t "kern: an unkerned pair answers 0" (ssp.kernAdv sspA sspA == 0)
  let osans ← load "OpenSans-Regular.ttf"
  t "kern: a face with no pairs answers 0 for every pair"
    ((osans.kernData.get).1.isEmpty && (osans.kernData.get).2.isEmpty &&
      osans.kernAdv ((osans.gid 'T').getD 0) ((osans.gid 'a').getD 0) == 0)
  let osE := (osans.gid 'é').getD 0
  let (osProg, osSub) := FontSubset.program osans #[osE]
  let osSrc := Ink.Src.make osans.data false osans.numGlyphs
  let osEmb := Ink.Src.make osProg false osans.numGlyphs
  t "subset: a composite the page paints keeps its components"
    (osSub && ((osEmb.cmdsAt osE).map (·.size != 0)) == some true &&
      osEmb.cmdsAt osE == osSrc.cmdsAt osE &&
      osEmb.cmdsAt ((osans.gid 'x').getD 0) == some #[] && osProg.size < osans.data.size)
  let sfntSum (b : ByteArray) : Nat := Id.run do
    let mut s : UInt32 := 0
    for i in [0:(b.size + 3) / 4] do
      s := s + (Ink.u32 b (4 * i)).toUInt32
    return s.toNat
  t "subset: an embedded program sums to the sfnt magic, each table to its directory checksum"
    (sfntSum osProg == 0xB1B0AFBA &&
      (List.range (Ink.u16 osProg 4)).all fun k =>
        let e := 12 + 16 * k
        let o := Ink.u32 osProg (e + 8)
        let d := osProg.extract o (o + Ink.u32 osProg (e + 12))
        let d := if osProg.extract e (e + 4) == "head".toUTF8 then
          (((d.set! 8 0).set! 9 0).set! 10 0).set! 11 0 else d
        sfntSum d == Ink.u32 osProg (e + 4))
  let sspKeep := "Typesetting".toList.foldl (fun k c =>
    match ssp.gid c with | some g => k.set! g true | none => k)
    ((Array.replicate ssp.numGlyphs false).set! 0 true)
  let fresh := Ink.Src.make ssp.data true ssp.numGlyphs
  t "subset: a CFF table read through the face is the fresh decode's"
    (match Ink.findTable ssp.data "CFF " with
     | some ct =>
       let viaFace := FontSubset.cffDrop ssp.data ct sspKeep ssp.inkSrc.get
         (ssp.yExtent · |>.isSome)
       viaFace.isSome && viaFace.map (·.data) ==
         (FontSubset.cffDrop ssp.data ct sspKeep fresh (fresh.yExtentAt · |>.isSome)).map (·.data)
     | none => false)
  -- Fira Sans keeps its kern lookups behind a GPOS extension; values are hb-shape's, upem 1000.
  let firaSans ← load "FiraSans-Regular.otf"
  let fk (a b : Char) : Int :=
    firaSans.kernAdv ((firaSans.gid a).getD 0) ((firaSans.gid b).getD 0)
  t "kern: pairs behind an extension lookup answer hb-shape's values"
    (fk 'T' 'e' == -55 && fk 'A' 'V' == -14 && fk 'L' 'T' == -83 && fk 'a' 'a' == -5 &&
      fk 'H' 'H' == 0)
  let spaceMemoExact (f : Font) : Bool :=
    match f.gid ' ' with
    | some sp => (List.range (f.numGlyphs + 2)).all fun g =>
        f.spaceKernAdv true g == f.kernAdv g sp && f.spaceKernAdv false g == f.kernAdv sp g
    | none => false
  t "kern: each glyph's memoized space pairs are its pairs with the space"
    (spaceMemoExact ssp && spaceMemoExact firaSans && spaceMemoExact osans &&
      (List.range ssp.numGlyphs).any (ssp.spaceKernAdv true · != 0) &&
      (List.range ssp.numGlyphs).any (ssp.spaceKernAdv false · != 0))
  let boundedSpaceLookup (f : Font) : Bool :=
    match f.spaceKerns.get with
    | none => false
    | some cache =>
      cache.size == f.numGlyphs && cache.depth == Font.spaceKernDepth f.numGlyphs &&
        match cache.lookup? (f.numGlyphs - 1) with
        | some (_, work) => work == cache.depth + 1 && work ≤ 17
        | none => false
  -- maxp stores numGlyphs as UInt16, so 65,535 is the largest parsed face.
  t "kern: the memo depth covers and bounds every sfnt glyph count"
    ((List.range 65536).all fun n =>
      Font.spaceKernDepth n ≤ 16 && (n == 0 || n ≤ 2 ^ Font.spaceKernDepth n))
  t "kern: one space lookup visits at most 17 memo nodes"
    (boundedSpaceLookup ssp && boundedSpaceLookup firaSans)
  t "kern: a pairless face short-circuits its space cache"
    osans.spaceKerns.get.isNone
  let sspSet := oneFaceOf ssp
  let (taDoc, _) := Elab.run "t" "Ta"
  let taOut := layoutOf sspSet taDoc ({} : Layout.Geom)
  let taRun := ((taOut.pages.flatMap (·.lines)).flatMap (·.segs)).findSome?
    fun s => match s with
      | .run _ _ _ w glyphs _ _ _ _ _ _ =>
        if (glyphs.map (·.2.1)) == #['T', 'a'] then some (w, glyphs) else none
      | _ => none
  t "kern: the run width is the advances plus the pair value"
    (match taRun with
     | some (w, glyphs) =>
       let geom : Layout.Geom := {}
       let want : Dim.Length :=
         ((ssp.widths[sspT]! : Int) * geom.fontSize / 1000
           + (-41 : Int) * geom.fontSize / 1000)
           + (ssp.widths[sspA]! : Int) * geom.fontSize / 1000
       glyphs.size == 2 && w == want
     | none => false)
  t "kern: the run carries T's advance with the pair value, a's without"
    (match taRun with
     | some (_, glyphs) =>
       let geom : Layout.Geom := {}
       glyphs.map (·.2.2) ==
         #[(ssp.widths[sspT]! : Int) * geom.fontSize / 1000 + (-41 : Int) * geom.fontSize / 1000,
           (ssp.widths[sspA]! : Int) * geom.fontSize / 1000]
     | none => false)
  -- Source Serif Pro's space pairs as lualatex applies them: (T, sp) −19, (V, sp) −39, (sp, V) −30.
  let (skDoc, _) := Elab.run "t" "T a V V x y"
  let skOut := layoutOf sspSet skDoc ({} : Layout.Geom)
  let skGaps := ((skOut.pages.flatMap (·.lines)).flatMap (·.segs)).filterMap
    fun s => match s with
      | .gap w true => some w
      | _ => none
  t "space kern: each interword gap is the space plus its neighbours' pairs"
    (let fsz := ({} : Layout.Geom).fontSize
     let u (n : Int) : Dim.Length := n * fsz / 1000
     let sp := u ssp.spaceAdvance
     skGaps == #[sp + u (-19), sp + u (-30), sp + u (-39) + u (-30), sp + u (-39), sp])
  -- A text-font command's edges stop a space kern, as ltfntcmd's `\/` does; a declaration does not.
  let some sfs ← serifFacesSet | t "font edge: the serif faces load" false
  let edgeRun (src : String) : Array Dim.Length × Array Diag :=
    let (d, ds) := Elab.run "t" src
    let gaps := ((layoutOf sfs d ({} : Layout.Geom)).pages.flatMap (·.lines)).flatMap (·.segs)
      |>.filterMap fun s => match s with
        | .gap w true => some w
        | _ => none
    (gaps, ds)
  let edgeGap (src : String) : Array Dim.Length := (edgeRun src).1
  let edgeU (n : Int) : Dim.Length := n * ({} : Layout.Geom).fontSize / 1000
  let edgeSp := edgeU ssp.spaceAdvance
  -- Two edges at one space give its pair back once (lualatex: 8.44 bp in each spelling).
  let boldSp := edgeU (sfs.get (sfs.lookup 0 700 false)).spaceAdvance
  for (src, want) in [("T a", edgeSp + edgeU (-19)), ("{\\rmfamily T} a", edgeSp + edgeU (-19)),
      ("\\textrm{T} a", edgeSp), ("T \\textrm{a}", edgeSp), ("\\textup{V} a", edgeSp),
      ("\\textbf{T} a", edgeSp), ("T \\textbf{a}", edgeSp),
      ("\\textbf{T }a", boldSp), ("\\textbf{T }\\textrm{a}", boldSp),
      ("\\textrm{\\textbf{T }}a", boldSp), ("\\textbf{T }\\textbf{a}", boldSp),
      ("V \\emph{V}", edgeSp + edgeU (-39)), ("\\emph{a} V", edgeSp + edgeU (-30))] do
    t s!"font edge: '{src}' ships the gap lualatex sets" (edgeGap src == #[want])
  for (src, want) in [("T \\textrm{\\nocorr V}", edgeSp + edgeU (-19) + edgeU (-30)),
      ("\\textrm{T\\nocorr} a", edgeSp + edgeU (-19))] do
    let got := edgeRun src
    t s!"font edge: '{src}' consumes nocorr and ships the gap lualatex sets"
      (got.1 == #[want] && got.2.isEmpty)
  let (_, nestedNocorrDs) := Elab.run "t" "\\textrm{{\\nocorr}V}"
  t "font edge: a nested nocorr is not consumed as the command's edge marker"
    (nestedNocorrDs.map (·.code) == #["W0301"])
  t "no MATH face anywhere: the pick is none"
    ((← FontDiscovery.pickMathFace
        (shipped.filter fun f => !(f.path.endsWith "FiraMath-Regular.otf"))
        "Fira Sans").isNone)
  t "every pairing row names a face, a source, and a licence"
    (FontDb.mathCompanions.all fun p =>
      !p.body.isEmpty && !p.companion.isEmpty && !p.source.isEmpty && !p.license.isEmpty)
  t "faceLt is asymmetric over the shipped faces"
    (shipped.all fun f => shipped.all fun g =>
      !(FontDb.faceLt f g && FontDb.faceLt g f))
  t "faceLt is total over the shipped faces"
    (shipped.all fun f => shipped.all fun g =>
      f.path == g.path || FontDb.faceLt f g || FontDb.faceLt g f)
  t "faceLt is transitive over the shipped faces"
    (shipped.all fun f => shipped.all fun g => shipped.all fun h =>
      !(FontDb.faceLt f g && FontDb.faceLt g h) || FontDb.faceLt f h)
  t "pickCompanion answers the same for the reversed scan"
    ((FontDb.pickCompanion shipped.reverse "Fira Sans").map (·.2.path) ==
      (FontDb.pickCompanion shipped "Fira Sans").map (·.2.path))
  t "tableImage of a missing file is none"
    ((← FontDiscovery.tableImage "/nonexistent/leantex-x.otf" (fun _ => true)).isNone)
  IO.FS.withTempDir fun dir => do
    let corrupt := dir / "corrupt-fallback.otf"
    IO.FS.writeBinFile corrupt ("OTTO".toUTF8 ++ ByteArray.mk (Array.replicate 40 0xff))
    t "a corrupt candidate yields no cmap image"
      ((← FontDiscovery.tableImage corrupt.toString (· == "cmap")).isNone)

  let prefPicks ← FontDiscovery.fallbackPicksPreferring
    (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['∀']
  t "a preferred (document-shipped) face answers first for what it covers"
    (prefPicks.contains ('∀', testFonts ++ "/SourceCodePro-Regular.otf"))
  t "what a preferred face leaves uncovered still reaches the full scan"
    (((← FontDiscovery.fallbackPicksPreferring
        (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['\uF09B']).find?
      (·.1 == '\uF09B')).any (fun e => (e.2.splitOn "ExampleIcons").length ≥ 2))

  Tests.NfcBoundary.tableChecks t

  -- Every shipped locale is served by `Hyphen.forTag` or stands on the unhyphenated list.
  let unhyphenated : List String := []
  t "every builtin locale hyphenates or is declared unhyphenated"
    (Locale.builtin.all fun l =>
      (Hyphen.forTag l.tag).isSome || unhyphenated.contains l.tag)

/-- The default family over synthetic faces: preferred names in preference order, then the first
family calling itself sans, then any face, none only when nothing is installed. -/
def defaultFontChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  t "default prefers listed names over scan order"
    (FontDb.defaultFamily #[synthFace "Arial", synthFace "Helvetica"] == some "Helvetica")
  t "default takes the first preferred name present"
    (FontDb.defaultFamily #[synthFace "Helvetica", synthFace "DejaVu Sans"] ==
      some "DejaVu Sans")
  t "default falls back to the first sans family"
    (FontDb.defaultFamily
      #[synthFace "Example Serif", synthFace "Foo Sans", synthFace "Bar Sans"] ==
      some "Foo Sans")
  t "default falls back to any face"
    (FontDb.defaultFamily #[synthFace "Example Serif"] == some "Example Serif")
  t "default is none only without any face" (FontDb.defaultFamily #[] == none)
  t "resolve breaks duplicate-install ties by scan order"
    ((FontDb.resolve #[synthFace "Tie Sans" "/z/tie.ttf", synthFace "Tie Sans" "/a/tie.ttf"]
      "Tie Sans" {}).map (·.1.path) == some "/z/tie.ttf")
  for d in ["/System/Library/Fonts", "/System/Library/Fonts/Supplemental",
      "/Library/Fonts", "/opt/homebrew/share/fonts", "/usr/local/share/fonts"] do
    t s!"searchDirs covers {d}" (FontDiscovery.searchDirs.contains d)
  if let some home ← IO.getEnv "HOME" then
    t "extraDirs covers ~/Library/Fonts"
      ((← FontDiscovery.extraDirs).contains (home ++ "/Library/Fonts"))
  -- A .ttc fed to `probe` directly classifies as unusable, never aborts.
  IO.FS.withTempDir fun dir => do
    let ttc := dir / "synthetic.ttc"
    IO.FS.writeBinFile ttc ("ttcf".toUTF8 ++ ByteArray.mk (Array.replicate 64 0x7f))
    t "probe rejects a ttc without aborting" ((← FontDiscovery.probe ttc.toString).isNone)

/-- The shipped fonts make the suite hermetic: sorted scan order, a file name denoting its face's
family, `Path=` carried into `dir`, and the sans as the default family. -/
def shippedFontChecks (ref : IO.Ref (List String)) (faces : Array FontDb.Face) : IO Unit := do
  let t := check ref
  let paths := faces.map (·.path)
  t "scan order is sorted path order" (paths == paths.qsort (· < ·))
  t "scanning again gives the same faces" ((← FontDiscovery.scanRoots [testFonts]).map (·.path) == paths)
  t "a file name denotes its family"
    (FontDb.familyOf faces "SourceSerifPro-Regular.otf" == "Source Serif Pro")
  t "an unknown file name denotes itself" (FontDb.familyOf faces "Nope.otf" == "Nope.otf")
  t "resolve by file name finds the bold beside it"
    ((FontDb.resolve faces "OpenSans-Regular.ttf" { bold := true }).map (·.1.path) ==
      some (testFonts ++ "/OpenSans-Bold.ttf"))
  t "default over the shipped faces is the first sans in listing order"
    (FontDb.defaultFamily faces == some "Fira Sans")
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  let d1 := (elabStr (pre ++ "\\setmainfont[Path=fonts/]{SourceSerifPro-Regular.otf}" ++ post)).1.fonts
  t "compat Path before the name"
    (d1.dirs == #["fonts/"] && d1.body == some "SourceSerifPro-Regular.otf")
  let d2 := (elabStr (pre ++ "\\setsansfont{Open Sans}[Path = fonts/, BoldFont = OpenSans-Bold.ttf]"
    ++ post)).1.fonts
  t "compat Path after the name" (d2.dirs == #["fonts/"] && d2.sans == some "Open Sans")
  let d3 := (elabStr (pre ++ "\\babelfont{rm}[Path=fonts/]{SourceSerifPro-Regular.otf}" ++ post)).1.fonts
  t "compat babelfont Path" (d3.dirs == #["fonts/"] && d3.body == some "SourceSerifPro-Regular.otf")
  let d5 := (elabStr (pre ++ "\\setmainfont{A.otf}[Path=serif/]\\setsansfont{B.otf}[Path=sans/]" ++ post)).1.fonts
  t "a Path per face keeps every directory" (d5.dirs == #["serif/", "sans/"])
  let d4 := (elabStr (pre ++ "\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }" ++ post)).1.fonts
  t "fonts dir" (d4.dirs == #["fonts"] && d4.body == some "Source Serif Pro")
  t "fonts dir wrong type" (errCodes (pre ++ "\\fonts{ dir = 12 }" ++ post) == ["E0323"])
  let plain : FontDb.Face := {
    path := "/x/a.otf"
    family := "X"
    subfamily := "Bold"
    bold := true
    italic := false
    fixedPitch := false
    weight := 700 }
  let condensed : FontDb.Face := { plain with path := "/x/b.otf", subfamily := "Condensed Bold" }
  t "plain face beats a condensed sibling"
    ((FontDb.resolve #[condensed, plain] "X" { bold := true }).map (·.1.path) == some "/x/a.otf")
  -- `post.isFixedPitch` is at offset 12; offset 16 is minMemType42, a memory hint.
  let pitchOf (name : String) : IO (Option Bool) := do
    match Font.classify (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok c => pure (some c.isFixedPitch)
    | .error _ => pure none
  t "face pitch: a monospace design declares fixed pitch"
    ((← pitchOf "SourceCodePro-Regular.otf") == some true)
  t "face pitch: a proportional design does not"
    ((← pitchOf "SourceSerifPro-Regular.otf") == some false)

/-- The classifier version the shipped faces' pinned classifications answer to. -/
def classifierPinsVersion : Nat := 2

def classifierPins : List (String × String × String × Bool × Bool × Bool × Nat) := [
  ("ExampleIcons-Regular.ttf", "Example Icons", "Regular", false, false, false, 400),
  ("FiraMath-Regular.otf", "Fira Math", "Regular", false, false, false, 400),
  ("FiraSans-Regular.otf", "Fira Sans", "Regular", false, false, false, 400),
  ("OpenSans-Bold.ttf", "Open Sans", "Bold", true, false, false, 700),
  ("OpenSans-BoldItalic.ttf", "Open Sans", "Bold Italic", true, true, false, 700),
  ("OpenSans-Italic.ttf", "Open Sans", "Italic", false, true, false, 400),
  ("OpenSans-Regular.ttf", "Open Sans", "Regular", false, false, false, 400),
  ("SourceCodePro-Regular.otf", "Source Code Pro", "Regular", false, false, true, 400),
  ("SourceSerifPro-Bold.otf", "Source Serif Pro", "Bold", true, false, false, 700),
  ("SourceSerifPro-BoldIt.otf", "Source Serif Pro", "Bold Italic", true, true, false, 700),
  ("SourceSerifPro-Regular.otf", "Source Serif Pro", "Regular", false, false, false, 400),
  ("SourceSerifPro-RegularIt.otf", "Source Serif Pro", "Italic", false, true, false, 400)]

/-- A stored classification is read only by the classifier that wrote it: the probe cache's file
name carries `Font.classifierVersion`, which moves with the answers. -/
def probeCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let path := testFonts ++ "/SourceCodePro-Regular.otf"
  let some key ← FontDiscovery.probeKey path
    | failures ref "probe cache: the shipped Source Code Pro cannot be stat'd"; return
  let stale := key ++ "\tOld Classifier\tRegular\tfalse\tfalse\tfalse\t400\n"
  let scanWith (file : String) : IO (Option FontDb.Face) := do
    IO.FS.withTempDir fun dir => do
      IO.FS.writeFile (dir / file) stale
      let faces ← FontDiscovery.scanRootsIn (some dir) [testFonts]
      return faces.find? (·.path == path)
  let legacy ← scanWith "fontdb.tsv"
  t "probe cache: a row an earlier classifier wrote is not read"
    ((legacy.map fun f => (f.family, f.fixedPitch)) == some ("Source Code Pro", true))
  let live ← scanWith FontDiscovery.probeCacheName
  t "probe cache: the same row in this classifier's own file is read, so the name is what refuses it"
    ((live.map fun f => (f.family, f.fixedPitch)) == some ("Old Classifier", false))
  t s!"classifier pins: recorded under version {classifierPinsVersion}, the classifier is \
version {Font.classifierVersion} — re-pin the table below when the version moves"
    (Font.classifierVersion == classifierPinsVersion)
  for (file, family, sub, bold, italic, fixed, weight) in classifierPins do
    match Font.classify (← IO.FS.readBinFile (testFonts ++ "/" ++ file)) with
    | .ok c =>
      t s!"classifier pins: {file} classifies as pinned — a changed answer moves \
Font.classifierVersion, so no stored answer of the old one is read"
        (c.family == family && c.subfamily == sub && c.isBold == bold && c.isItalic == italic
          && c.isFixedPitch == fixed && c.weight == weight)
    | .error e => t s!"classifier pins: {file} classifies: {e}" false
  let shipped := ((← (System.FilePath.mk testFonts).readDir).map (·.fileName)).filter
    fun n => n.endsWith ".otf" || n.endsWith ".ttf"
  t "classifier pins: every shipped face is pinned"
    (shipped.qsort (· < ·) == (classifierPins.map (·.1)).toArray.qsort (· < ·))

/-- A stored listing is read only by a walk with the same filter: the listing cache's file name
carries the extensions the walk keeps. -/
def listingCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let md ← (System.FilePath.mk testFonts).metadata
  let empty := s!"{testFonts}\t{md.modified.sec}.{md.modified.nsec}\n"
  let scanWith (file : String) : IO Nat := do
    IO.FS.withTempDir fun dir => do
      IO.FS.writeFile (dir / file) empty
      let faces ← FontDiscovery.scanRootsIn (some dir) [testFonts]
      return faces.size
  let legacy ← scanWith "fontdb-dirs.tsv"
  t s!"listing cache: a listing an earlier walk wrote is not read ({legacy} faces)" (legacy ≥ 2)
  let live ← scanWith FontDiscovery.listingCacheName
  t s!"listing cache: the same listing under this filter's own name is read, so the name is what \
refuses it ({live} faces)" (live == 0)
  t "listing cache: the name carries every extension the walk keeps"
    (FontDb.fontExtensions.all fun ext => hasStr FontDiscovery.listingCacheName ext)

def fontsDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let fontsSrc := "\\documentclass{article}\n" ++
    "\\fonts{ body = \"DejaVu Serif\", sf = \"DejaVu Sans\" }\n" ++
    "\\begin{document}x\\end{document}"
  let (fDoc, fDs) := elabStr fontsSrc
  t "fonts source clean" fDs.isEmpty
  t "fonts body" (fDoc.fonts.body == some "DejaVu Serif")
  t "fonts sf alias maps to sans" (fDoc.fonts.sans == some "DejaVu Sans")
  t "fonts mono unset" (fDoc.fonts.mono == none)
  t "fonts wrong type" (errCodes ("\\documentclass{article}\\fonts{ body = 12 }" ++
    "\\begin{document}x\\end{document}") == ["E0323"])
  t "fonts unknown key" (errCodes ("\\documentclass{article}\\fonts{ script = \"X\" }" ++
    "\\begin{document}x\\end{document}") == ["E0322"])

  let faces ← FontDiscovery.scanRoots [testFonts]
  t "fontdb finds the twelve shipped faces" (faces.size == 12)
  t "fontdb finds source serif" ((FontDb.families faces).any (· == "Source Serif Pro"))
  defaultFontChecks ref
  shippedFontChecks ref faces
  probeCacheChecks ref
  listingCacheChecks ref
  match FontDb.resolve faces "Source Serif Pro" { bold := true } with
  | some (face, exact) =>
    t "fontdb bold is exact" exact
    t "fontdb bold flagged" face.bold
  | none => failures ref "fontdb: Source Serif Pro Bold not found"
  match FontDb.resolve faces "Source Serif Pro" { bold := true, italic := true } with
  | some (face, exact) => t "fontdb bold italic" (exact && face.bold && face.italic)
  | none => failures ref "fontdb: Source Serif Pro BoldItalic not found"
  t "fontdb unknown family" (FontDb.resolve faces "No Such Family Here" {} |>.isNone)

def fontSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pats := Hyphen.english.get
  match ← findFont with
  | none =>
    failures ref s!"font: {testFonts}/OpenSans-Regular.ttf missing from the checkout"
  | some fontData =>
    match Font.parse fontData with
    | .error e => failures ref s!"font parse: {e}"
    | .ok font =>
      t "font name" (font.psName == "OpenSans-Regular")
      t "font upem" (font.unitsPerEm == 2048)
      t "font gid A" (font.gid 'A' |>.isSome)
      t "font advance A" (font.advance 'A' > 0)
      t "font greek" (font.gid 'α' |>.isSome)
      t "font missing emoji" (font.gid '🎉' |>.isNone)
      t "font family" (font.family == "Open Sans")
      t "font cap height from OS/2" (font.capHeight == 1462)
      t "font not bold" (!font.isBold && !font.isItalic)

      t "font parse rejects garbage"
        ((Font.parse (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])).isOk == false)
      t "font parse rejects an empty file" ((Font.parse (ByteArray.mk #[])).isOk == false)
      -- Reaching the assertion is the property: a panic would take the run down.
      let verdicts := (List.range 64).map fun k =>
        (Font.parse (fontData.extract 0 (fontData.size * k / 64))).isOk
      t "font parse is total over truncations" (verdicts.length == 64)
      t "font parse rejects short truncations" (verdicts.take 8 |>.all (· == false))
      let lying := Id.run do
        let mut b := fontData.extract 0 (min fontData.size 4096)
        for i in [0:4] do
          b := b.set! (12 + 12 + i) 0x7f
        return b
      t "font parse rejects a table that overruns the file"
        ((Font.parse lying).isOk == false)
      match Font.classify fontData with
      | .error e => failures ref s!"font classify: {e}"
      | .ok c =>
        t "classify agrees with parse on family" (c.family == font.family)
        t "classify agrees with parse on subfamily" (c.subfamily == font.subfamily)
        t "classify agrees with parse on style"
          (c.isBold == font.isBold && c.isItalic == font.isItalic &&
           c.weight == font.weight && c.isFixedPitch == font.isFixedPitch)
      t "classify is total over truncations"
        (((List.range 64).map fun k =>
          (Font.classify (fontData.extract 0 (fontData.size * k / 64))).isOk).length == 64)
      -- Forces the lazy readers on each parsable truncation; reaching the assertion is the test.
      for name in ["SourceSerifPro-Regular.otf", "FiraMath-Regular.otf"] do
        let rich ← IO.FS.readBinFile (testFonts ++ "/" ++ name)
        let mut forced := 0
        let mut acc : Int := 0
        for k in [0:65] do
          match Font.parse (rich.extract 0 (rich.size * k / 64)) with
          | .error _ => pure ()
          | .ok f =>
            forced := forced + 1
            for g in [0:min f.numGlyphs 24] do
              acc := acc + f.kernAdv g (g + 1)
              acc := acc + (f.inkAt g).size
              acc := acc + ((f.yExtent g).map (·.2)).getD 0
              acc := acc + (f.vertVariants g).size + (f.horizVariants g).size
              acc := acc + f.topAccentX g
            acc := acc + (f.xInkTop.get.getD 0)
        t s!"truncated lazy readers are total ({name})"
          (forced ≥ 1 && acc - acc == 0)
      -- The group count is the one file-derived loop bound, so the bytes present clamp it.
      let ssp ← IO.FS.readBinFile (testFonts ++ "/SourceSerifPro-Regular.otf")
      let cmap12Off : Option Nat := Id.run do
        let some ct := Ink.findTable ssp "cmap" | return none
        let n := Ink.u16 ssp (ct.offset + 2)
        for k in [0:n] do
          let entry := ct.offset + 4 + 8 * k
          let sub := ct.offset + Ink.u32 ssp (entry + 4)
          if Ink.u16 ssp sub == 12 then
            return some sub
        return none
      match cmap12Off with
      | none => failures ref "font: SourceSerifPro-Regular.otf lost its format-12 cmap"
      | some off =>
        let doctored := (((ssp.set! (off + 12) 0x00).set! (off + 13) 0x20).set!
          (off + 14) 0x00).set! (off + 15) 0x00
        match Font.parse doctored with
        | .error e => failures ref s!"font: a lying cmap-12 count should still parse: {e}"
        | .ok f =>
          t "a lying cmap-12 group count is clamped by the bytes present"
            (f.cmap.size ≤ doctored.size / 12)

      -- A one-face set: every slot and variant maps to index 0.
      let oneFace := oneFaceOf font
      t "fontset lookup body" (oneFace.lookup 0 400 false == 0)
      t "fontset lookup falls back" (oneFace.lookup 2 700 true == 0)
      let twoWeights : Font.FontSet := {
        fonts := #[font, font]
        index := #[((0, 400, false), 0), ((0, 300, false), 1)] }
      t "lookup selects the indexed weight" (twoWeights.lookup 0 300 false == 1)
      t "an unindexed weight falls to the slot regular"
        (twoWeights.lookup 0 600 false == 0)

      let (hyDoc, hyDs) := Elab.run "t" "incomprehensibility"
      t "layout hyphen source clean" hyDs.isEmpty
      let narrow : Layout.Geom := {
        pageW := Dim.pt 90
        pageH := Dim.pt 200
        hmargin := Dim.pt 10
        vmargin := Dim.pt 10
        fontSize := Dim.pt 10
      }
      let hyOut := layoutOf oneFace hyDoc narrow (some pats)
      let hyphenRendered := hyOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '-')
          | .gap _ _ | .decoratedGap _ _ _ | .rule .. | .decoration .. | .image .. | .poly .. => false
      t "layout chosen hyphen renders" (hyOut.pages[0]!.lines.size > 1 && hyphenRendered)
      let hyphens (doc : Ir.Doc) : Bool :=
        (layoutOf oneFace doc narrow (some pats)).pages.any fun p =>
          p.lines.any fun l => l.segs.any fun s => match s with
            | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '-')
            | .gap _ _ | .decoratedGap _ _ _ | .rule .. | .decoration .. | .image .. | .poly .. => false
      t "a heading never hyphenates"
        (!hyphens (Elab.run "t" "\\section{incomprehensibility}").1)
      t "a frame title never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\begin{frame}{incomprehensibility}x\\end{frame}\\end{document}")).1)
      t "the title page never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\title{incomprehensibility}\\maketitle\\end{document}")).1)
      let (jhDoc, _) := Elab.run "t"
        "\\section{one two six ten oak elm fir ash}\n\nbody text"
      let headLines := (layoutOf oneFace jhDoc narrow (some pats)).pages.flatMap
        (·.lines) |>.filter (·.size == Layout.sectionSize narrow 1)
      t "a wrapped heading is ragged, not justified"
        (headLines.size ≥ 2 && headLines.all (·.setWidth < narrow.textWidth))
      t "layout hyphen avoids overfull" (!hyOut.diags.any (·.code == "W0005"))
      -- W0005 is spanless, so after the dedup the count is the only signal of scale.
      let (ofDoc, _) := Elab.run "t"
        "aaaaaaaaaaaaaaaaaaaaaaaaaa\n\nbbbbbbbbbbbbbbbbbbbbbbbbbb"
      let ofOut := layoutOf oneFace ofDoc narrow
      t "overfull warning carries the count"
        ((ofOut.diags.filter (·.code == "W0005")).size == 1 &&
         ofOut.diags.any (·.detail == some "2 overfull lines"))

      let visualSrc := "\\section{Heading}\nBody text.\n\n" ++
        "\\begin{itemize}\\item A list item.\\end{itemize}"
      let (visualDoc, visualDs) := Elab.run "t" visualSrc
      t "layout visual source clean" visualDs.isEmpty
      let visualOut := layoutOf oneFace visualDoc {} (some pats)
      let hasSectionSize := visualOut.pages.any fun p =>
        p.lines.any (·.size == Layout.sectionSize ({} : Layout.Geom) 1)
      let hasListMarker := visualOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '•')
          | .gap _ _ | .decoratedGap _ _ _ | .rule .. | .decoration .. | .image .. | .poly .. => false
      t "layout section size" hasSectionSize
      t "layout list marker" hasListMarker

      let (doc, eds) := Elab.run "t" "hello world, a small pdf self check"
      t "pdf source clean" eds.isEmpty
      let geom : Layout.Geom := {}
      let out := layoutOf oneFace doc geom
      t "pdf one page" (out.pages.size == 1)
      let pdf := Pdf.write geom oneFace out.pages
      t "pdf header" (String.fromUTF8! (pdf.extract 0 8) == "%PDF-2.0")
      t "pdf eof" (String.fromUTF8! (pdf.extract (pdf.size - 6) pdf.size) == "%%EOF\n")
      match checkXref pdf with
      | .ok n => t s!"pdf xref valid" (n > 0)
      | .error e => failures ref s!"pdf xref: {e}"

/-- Distinct real text slots and body variants, so a face-selection check
cannot pass by aliasing every request to one font. -/
def mathTextFaces : IO Font.FontSet := do
  let names : Array String := #["OpenSans-Regular.ttf", "OpenSans-Bold.ttf",
    "OpenSans-Italic.ttf", "OpenSans-BoldItalic.ttf", "FiraSans-Regular.otf",
    "SourceCodePro-Regular.otf", "FiraMath-Regular.otf"]
  let fonts ← names.mapM fun name => do
    match Font.parse (← IO.FS.readBinFile (System.FilePath.mk (testFonts ++ "/" ++ name))) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math text face {name}: {e}")
  return {
    fonts := fonts
    index := #[((0, 400, false), 0), ((0, 700, false), 1),
      ((0, 400, true), 2), ((0, 700, true), 3),
      ((1, 400, false), 4), ((2, 400, false), 5)]
    math := some 6
    mathAlphabets := fonts[6]!.mathAlphabetCoverage {} }

mutual

/-- The emitted MathML text leaves with their declared text-face styles. -/
def mathTextLeaves (acc : Array (String × String)) : Html.Node →
    Array (String × String)
  | .elem tag attrs kids =>
    if tag == "mi" || tag == "mn" then
      acc.push (nodeTextOne "" (.elem tag attrs kids),
        ((attrs.find? (·.1 == "style")).map (·.2)).getD "")
    else mathTextLeavesList acc kids.toList
  | .text _ | .style _ | .script _ _ => acc

def mathTextLeavesList (acc : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => acc
  | n :: ns => mathTextLeavesList (mathTextLeaves acc n) ns

end

/-- The math text commands select lualatex's faces (regular, bold, italic, sans, mono) on letters
and digits, even inside bold or italic prose. -/
def mathTextAmbientChecks (ref : IO.Ref (List String)) : IO Unit := do
  let fs ← mathTextFaces
  let rows : Array (String × Nat × String) := #[
    ("mathrm", 0, "font-family: var(--font-body)"),
    ("mathbf", 1, "font-family: var(--font-body); font-weight: 700"),
    ("mathit", 2, "font-family: var(--font-body); font-style: italic"),
    ("mathsf", 4, "font-family: var(--font-sans)"),
    ("mathtt", 5, "font-family: var(--font-mono)")]
  for ambient in ["", "\\bfseries ", "\\itshape ", "\\bfseries\\itshape "] do
    for (command, face, css) in rows do
      for c in "x0123456789".toList do
        let (raw, ds) := Elab.run "synthetic.tex"
          ("\\begin{document}{" ++ ambient ++ "$\\" ++ command ++ "{" ++
            String.singleton c ++ "}$}\\end{document}")
        let (doc, ads) := Ir.resolveMathAlphas fs.mathAlphabets "Fira Math" raw
        let out := layoutOf fs doc
        let glyphs := bodyGlyphs out
        let (_, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
        let label := s!"math alphabet {command}({c}) in {ambient}"
        check ref (label ++ " reaches the artifacts without recovery")
          (!(ds ++ ads ++ out.diags).any fun d =>
            d.severity == .error || d.code == "W0012" || d.code == "W0009" ||
              d.code == "N0018")
        check ref (label ++ " selects its real PDF text face")
          (glyphs == #[(face, c)])
        check ref (label ++ " selects its real HTML text face")
          (mathTextLeavesList #[] body.toList == #[(String.singleton c, css)])

  for (source, expectedFace, expectedCss) in [
      ("$\\symit{5}$", 6, ""),
      ("$\\mathbf{\\mathit{5}}$", 2,
        "font-family: var(--font-body); font-style: italic"),
      ("$\\mathit{\\mathbf{5}}$", 1,
        "font-family: var(--font-body); font-weight: 700")] do
    let raw := (Elab.run "synthetic.tex" source).1
    let (doc, ads) := Ir.resolveMathAlphas fs.mathAlphabets "Fira Math" raw
    let out := layoutOf fs doc
    let glyphs := bodyGlyphs out
    let (_, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
    check ref (source ++ " preserves digit source and inner alphabet in PDF/HTML")
      (glyphs == #[(expectedFace, '5')] &&
        mathTextLeavesList #[] body.toList == #[("5", expectedCss)] && ads.isEmpty)

/-- A symbol alphabet resets an enclosing text family even where the math face installs no range, as
unicode-math's `\fam=-1` does. -/
def mathSymbolResetChecks (ref : IO.Ref (List String)) : IO Unit := do
  let fs ← mathTextFaces
  let bold := "font-family: var(--font-body); font-weight: 700"
  let mut rows : Array (String × Array (Nat × Char) × Array (String × String)) := #[
    ("\\mathbf{\\mathcal{A}}", #[(6, 'A')], #[("A", "")]),
    ("\\mathbf{A\\mathcal{A}A}", #[(1, 'A'), (6, 'A'), (1, 'A')],
      #[("A", bold), ("A", ""), ("A", bold)]),
    ("\\mathcal{\\mathbf{A}}", #[(1, 'A')], #[("A", bold)]),
    ("\\symbf{\\mathcal{A}}", #[(6, '𝐀')], #[("𝐀", "")]),
    ("\\mathbf{\\symit{5}}", #[(6, '5')], #[("5", "")]),
    ("\\mathit{\\mathcal{5}}", #[(6, '5')], #[("5", "")]),
    ("\\mathbf{\\mathfrak{Z}}", #[(6, 'Z')], #[("Z", "")]),
    ("\\mathit{\\symsf{A}}", #[(6, 'A')], #[("A", "")]),
    -- bm.sty's wrapper keeps a digit's family: lualatex sets it in Open Sans Italic.
    ("\\mathit{\\bm{5}}", #[(2, '5')],
      #[("5", "font-family: var(--font-body); font-style: italic")]),
    ("\\mathit{\\mathcal{\\Gamma}}", #[(6, '𝛤')], #[("𝛤", "")])]
  for command in ["mathrm", "mathit", "mathsf", "mathtt"] do
    rows := rows.push ("\\" ++ command ++ "{\\mathcal{A}}",
      #[(6, 'A')], #[("A", "")])
  for (source, expectedGlyphs, expectedLeaves) in rows do
    let (raw, ds) := Elab.run "synthetic.tex" ("$" ++ source ++ "$")
    let (doc, ads) := Ir.resolveMathAlphas fs.mathAlphabets "Fira Math" raw
    let out := layoutOf fs doc
    let glyphs := bodyGlyphs out
    let (_, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
    check ref (source ++ " reaches the artifacts without recovery")
      (!(ds ++ ads ++ out.diags).any fun d =>
        d.severity == .error || d.code == "W0012" || d.code == "W0009")
    check ref (source ++ " resets only the inner PDF text family")
      (glyphs == expectedGlyphs)
    check ref (source ++ " resets only the inner HTML text family")
      (mathTextLeavesList #[] body.toList == expectedLeaves)

/-- A discarded enclosing text family cannot suppress the unavailable symbol alphabet's note, on the
shipped glyph and typed MathML alike. -/
def mathSymbolResetAccountingChecks (ref : IO.Ref (List String)) : IO Unit := do
  let fs ← mathTextFaces
  let evidence (source : String) :
      Array (Nat × Char) × Array (String × String) × Array Diag :=
    let (raw, ds) := Elab.run "synthetic.tex" ("$" ++ source ++ "$")
    let (doc, ads) := Ir.resolveMathAlphas fs.mathAlphabets "Fira Math" raw
    let out := layoutOf fs doc
    let glyphs := bodyGlyphs out
    let (_, body, _) := HtmlDoc.emitTree { fonts := some fs } doc
    (glyphs, mathTextLeavesList #[] body.toList, ds ++ ads ++ out.diags)
  let bare := evidence "\\symsf{5}"
  let nested := evidence "\\mathbf{\\symsf{5}}"
  let styled := evidence "\\mathbf{5}"
  let notes (ds : Array Diag) := (ds.filter (·.code == "N0018")).map (·.subject)
  check ref "symbol reset accounting: sans digits are unavailable"
    (!fs.mathAlphabets.remaps .sf .digits)
  for (label, result) in [("bare", bare), ("nested", nested), ("styled", styled)] do
    check ref s!"symbol reset accounting: {label} reaches the artifacts without recovery"
      (!result.2.2.any fun d =>
        d.severity == .error || d.code == "W0012" || d.code == "W0009")
  check ref "symbol reset accounting: bare request ships ordinary math 5"
    (bare.1 == #[(6, '5')] && bare.2.1 == #[("5", "")])
  check ref "symbol reset accounting: nested request ships the identical face, scalar and MathML"
    (nested.1 == bare.1 && nested.2.1 == bare.2.1)
  check ref "symbol reset accounting: bare loss is named once"
    (notes bare.2.2 == #[some "math-alpha:sf"])
  check ref "symbol reset accounting: discarded outer style cannot silence the same loss"
    (notes nested.2.2 == notes bare.2.2)
  check ref "symbol reset accounting: retained style selects the real bold text face"
    (styled.1 == #[(1, '5')] && styled.2.1 ==
      #[("5", "font-family: var(--font-body); font-weight: 700")])
  check ref "symbol reset accounting: retained style carries no missing alphabet note"
    (notes styled.2.2 == #[])

/-- Math end to end: MATH constants from the shipped face, box widths recomputed from the font's own
advances, script sizes and shifts, and every glyph or construct the engine cannot set named while
its text survives. -/
def mathChecks (ref : IO.Ref (List String)) : IO Unit := do
  mathTextAmbientChecks ref
  mathSymbolResetChecks ref
  mathSymbolResetAccountingChecks ref
  let t := check ref
  let load (name : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math: {name} unparsable: {e}")
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraMath-Regular.otf"
  -- Expected constants come from an independent struct-unpacking of the face.
  t "text faces carry no MATH table" serif.math.isNone
  t "fira math constants" (fira.math == some {
    scales := { script := 72, scriptscript := 58 }
    axisHeight := 280
    accentBaseHeight := 527
    subscriptShiftDown := 350
    superscriptShiftUp := 400
    superscriptShiftUpCramped := 270
    superscriptBottomMin := 130
    superscriptBaselineDropMax := 360
    spaceAfterScript := 41
    displayOperatorMinHeight := 1500
    upperLimitGapMin := 150
    upperLimitBaselineRiseMin := 150
    lowerLimitGapMin := 150
    lowerLimitBaselineDropMin := 600
    stackTopShiftUp := 450
    stackTopDisplayStyleShiftUp := 580
    stackBottomShiftDown := 480
    stackBottomDisplayStyleShiftDown := 700
    stackGapMin := 200
    stackDisplayStyleGapMin := 500
    fractionNumeratorShiftUp := 450
    fractionNumeratorDisplayStyleShiftUp := 580
    fractionDenominatorShiftDown := 480
    fractionDenominatorDisplayStyleShiftDown := 700
    fractionNumeratorGapMin := 80
    fractionNumDisplayStyleGapMin := 200
    fractionRuleThickness := 76
    fractionDenominatorGapMin := 80
    fractionDenomDisplayStyleGapMin := 200
    overbarVerticalGap := 150
    overbarRuleThickness := 66
    overbarExtraAscender := 50
    radicalVerticalGap := 96
    radicalDisplayStyleVerticalGap := 142
    radicalRuleThickness := 76
    radicalExtraAscender := 76
    radicalKernBeforeDegree := 276
    radicalKernAfterDegree := -400
    radicalDegreeBottomRaisePercent := 64 })
  -- Checked against an independent struct-unpacking of the same face.
  t "fira grows ( through sixteen sizes"
    (((fira.gid '(').map fun g => fira.vertVariants g) ==
      some #[(9, 991), (1637, 1320), (1638, 1648), (1639, 1976), (1640, 2304),
             (1641, 2632), (1642, 2960), (1643, 3288), (1644, 3616), (1645, 3944),
             (1646, 4272), (1647, 4600), (1648, 4928), (1649, 5256), (1650, 5584),
             (1651, 5913)])
  t "fira grows the sum sign to display size"
    (((fira.gid '\u2211').map fun g => fira.vertVariants g) ==
      some #[(753, 863), (1584, 1528)])
  t "a text face grows nothing" (serif.mathVariants.isEmpty)
  t "sum sign ink extent brackets the axis"
    (match (fira.gid '\u2211').bind fira.yExtent with
      | some (lo, hi) => lo < -100 && hi > 600
      | none => false)
  t "period ink sits on the baseline"
    (match (fira.gid '.').bind fira.yExtent with
      | some (lo, hi) => lo ≥ -30 && lo ≤ 0 && hi > 0 && hi < 300
      | none => false)
  let allSlots : Array ((Nat × Nat × Bool) × Nat) :=
    ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
  let symSources : Math.MathAlphabetSources := { rm := .sym }
  let alphaCoverage := fira.mathAlphabetCoverage symSources
  let mfs : Font.FontSet := {
    fonts := #[serif, fira]
    index := allSlots
    math := some 1
    mathAlphabets := alphaCoverage }
  let geom : Layout.Geom := {}
  let base := geom.fontSize
  let mbase : Dim.Length := .ofUnits (Math.mathSize base.units.toNat serif.xHeightOptical
    serif.unitsPerEm fira.xHeightOptical fira.unitsPerEm)
  let bodyXh := (serif.xHeightOptical : Int) * base / serif.unitsPerEm
  let mathXhAt (sz : Dim.Length) := (fira.xHeightOptical : Int) * sz / fira.unitsPerEm
  t "x-heights disagree before scaling" (mathXhAt base != bodyXh)
  t "x-heights agree after scaling, within one sp"
    (mathXhAt mbase ≤ bodyXh && bodyXh ≤ mathXhAt mbase + Dim.Length.quantum)
  let upem : Int := fira.unitsPerEm
  let adv (size : Dim.Length) (c : Char) : Dim.Length := (fira.advance c : Int) * size / upem
  let serifUpem : Int := serif.unitsPerEm
  let serifAdv (size : Dim.Length) (c : Char) : Dim.Length :=
    (serif.advance c : Int) * size / serifUpem
  let mu (size : Dim.Length) (n : Int) : Dim.Length := size * n / 18
  let konst (size : Dim.Length) (v : Int) : Dim.Length := v * size / upem

  -- Fira has no script range and the synthetic host does, so resolution must keep the host out.
  let scriptO := UInt32.ofNat '𝒪'.toNat
  let fakeGid := UInt32.ofNat ((serif.gid 'O').getD 0)
  let fakeHost : Font := { serif with
    family := "Synthetic Host Arsenal"
    psName := "SyntheticHostArsenal"
    cmap := (serif.cmap.push (scriptO, scriptO, fakeGid)).qsort (fun a b => a.1 < b.1) }
  let alphaFs : Font.FontSet := { mfs with
    fonts := #[serif, fira, fakeHost]
    fallback := #[('𝒪', 2)] }
  let alphaRaw := (Elab.run "synthetic.tex" "$\\mathcal{O}$").1
  let (alphaDoc, alphaDiags) :=
    Ir.resolveMathAlphas alphaCoverage fira.family alphaRaw
  let alphaOut := Layout.run geom alphaFs none alphaDoc
  let alphaRuns := (bodyLines alphaOut).flatMap (·.segs)
  let alphaRun := alphaRuns.findSome? fun s => match s with
    | .run idx _ _ w glyphs _ _ _ _ _ _ =>
      if glyphs.any (·.2.1 == '𝑂') then some (idx, w) else none
    | _ => none
  t "unsupported calligraphic uses ordinary italic from the primary math face"
    (alphaRun == some (1, adv mbase '𝑂'))
  t "unsupported calligraphic never selects a host fallback carrying script O"
    (!alphaRuns.any fun s => match s with
      | .run 2 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '𝒪')
      | _ => false)
  t "unsupported calligraphic asks fallback for neither script O nor W0009"
    (!(Layout.docScalars alphaDoc).contains '𝒪' &&
      (Layout.docScalars alphaDoc).contains '𝑂' &&
      !alphaOut.diags.any (·.code == "W0009"))
  let alphaTree := HtmlDoc.blockNode { fonts := some alphaFs } alphaDoc.body[0]!
  t "typed HTML carries the same ordinary italic scalar"
    (nodeTextOne "" alphaTree == "𝑂")
  t "the missing alphabet is named once by alphabet"
    ((alphaDiags.filter (·.code == "N0018")).map (fun d => (d.subject, d.message)) ==
      #[(some "math-alpha:cal",
        "missing alphabet calligraphic for font 'Fira Math'")])
  let twiceRaw := (Elab.run "synthetic.tex"
    "$\\mathcal{O}$ and $\\mathcal{P}$ and $\\mathfrak{Q}$").1
  let (_, twiceDiags) := Ir.resolveMathAlphas alphaCoverage fira.family twiceRaw
  t "repeated misses report once per alphabet, not once per glyph"
    ((twiceDiags.filter (·.code == "N0018")).map (·.subject) ==
      #[some "math-alpha:cal", some "math-alpha:frak"])

  let holeCoverage : Math.MathAlphabetCoverage := { alphaCoverage with
    covered := alphaCoverage.covered.push (.cal, .latinUpper) }
  let (holeDoc, holeDiags) := Ir.resolveMathAlphas holeCoverage fira.family alphaRaw
  let holeOut := Layout.run geom { alphaFs with mathAlphabets := holeCoverage } none holeDoc
  let holeRuns := (bodyLines holeOut).flatMap (·.segs)
  t "a hole in a supported alphabet keeps per-character fallback"
    (holeDiags.all (·.code != "N0018") &&
      holeOut.diags.any (·.code == "W0009") &&
      holeRuns.any fun s => match s with
        | .run 2 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '𝒪')
        | _ => false)

  let (umDoc, umDiags) := Elab.run "synthetic.tex"
    "\\documentclass{article}\\usepackage[mathrm=sym]{unicode-math}\\begin{document}$\\mathrm{R}$\\end{document}"
  t "unicode-math source options elaborate without a configuration loss"
    (umDiags.all (fun d => d.severity != .error && d.code != "W0101"))
  t "mathrm=sym reaches the typed source configuration without changing its peers"
    (umDoc.fonts.mathSources.rm == .sym && umDoc.fonts.mathSources.it == .text &&
      umDoc.fonts.mathSources.bf == .text && umDoc.fonts.mathSources.sf == .text &&
      umDoc.fonts.mathSources.tt == .text)
  t "Fira coverage follows unicode-math range anchors, not one isolated hole"
    (!alphaCoverage.faceCovers .cal .latinUpper &&
      !alphaCoverage.faceCovers .cal .latinLower &&
      alphaCoverage.faceCovers .bb .latinUpper)
  -- The synthetic host carries a sans-serif R, which a per-character remap would select.
  let sfKept : Char := 'R'
  let sansScalar : Char := Char.ofNat 0x1D5B1
  let sansR : UInt32 := UInt32.ofNat 0x1D5B1
  let sansGid : UInt32 := UInt32.ofNat ((serif.gid 'R').getD 0)
  let sansHost : Font := { serif with
    family := "Synthetic Host Sans"
    psName := "SyntheticHostSans"
    cmap := (serif.cmap.push (sansR, sansR, sansGid)).qsort (fun a b => a.1 < b.1) }
  -- `lookup` takes the first matching index entry, so the sans key is rewritten in place.
  let sfFs : Font.FontSet := { mfs with
    fonts := #[serif, fira, sansHost]
    index := mfs.index.map fun e => if e.1 == (1, 400, false) then (e.1, 2) else e }
  let sansFace := sfFs.lookup 1 400 false
  t "the sans text-family slot resolves to its own face, distinct from the body"
    (sansFace == 2 && sansFace != sfFs.lookup 0 400 false)
  let sfRaw := (Elab.run "synthetic.tex" "$\\mathsf{R}$").1
  let (sfDoc, sfDiags) := Ir.resolveMathAlphas alphaCoverage fira.family sfRaw
  let sfOut := Layout.run geom sfFs none sfDoc
  let sfRuns := (bodyLines sfOut).flatMap (·.segs)
  t "text-sourced mathsf keeps its source scalar in the sans text family"
    (sfRuns.any fun s => match s with
      | .run f _ _ _ glyphs _ _ _ _ _ _ => f == sansFace && glyphs.any (·.2.1 == sfKept)
      | _ => false)
  t "text-sourced mathsf never remaps to a scalar an unrelated host face carries"
    ((Layout.docScalars sfDoc).contains sfKept &&
      !(Layout.docScalars sfDoc).contains sansScalar &&
      !sfRuns.any (fun s => match s with
        | .run 2 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == sansScalar)
        | _ => false) &&
      !sfOut.diags.any (·.code == "W0009"))
  let sfTree := HtmlDoc.blockNode { fonts := some sfFs } sfDoc.body[0]!
  t "typed HTML carries the sans-serif source scalar, not the host remap"
    (nodeTextOne "" sfTree == String.ofList [sfKept] &&
      firstAttrOne "mathvariant" sfTree == some "normal" &&
      firstAttrOne "style" sfTree == some "font-family: var(--font-sans)")
  t "the unavailable sans-serif alphabet is named once by the IR owner"
    ((sfDiags.filter (fun d => d.code == "N0018" && d.subject == some "math-alpha:sf")).isEmpty)
  t "a text source forces no remap the face cannot cover"
    (alphaCoverage.remaps .sf .latinUpper == alphaCoverage.faceCovers .sf .latinUpper &&
      !alphaCoverage.remaps .sf .latinUpper)
  t "covered text-sourced alphabets still remap in the selected face"
    (alphaCoverage.faceCovers .bf .latinUpper && alphaCoverage.remaps .bf .latinUpper &&
      alphaCoverage.faceCovers .it .latinUpper && alphaCoverage.remaps .it .latinUpper &&
      alphaCoverage.faceCovers .tt .latinUpper && alphaCoverage.remaps .tt .latinUpper)

  let rc : UInt32 := (Char.toNat 'R').toUInt32
  let noR : Font := { fira with
    cmap := fira.cmap.filter (fun r => !(r.1 ≤ rc && rc ≤ r.2.1)) }
  t "the synthetic math face genuinely lacks R" ((noR.gid 'R').isNone)
  let noRfs : Font.FontSet := {
    fonts := #[serif, noR]
    index := allSlots
    math := some 1
    mathAlphabets := alphaCoverage
    fallback := #[('R', 0)] }
  let styledRaw := (Elab.run "synthetic.tex" "$\\mathsf{R}$").1
  let (styledDoc, _) := Ir.resolveMathAlphas alphaCoverage noR.family styledRaw
  let styledOut := Layout.run geom noRfs none styledDoc
  t "text-projected styled scalar raises no spurious W0009 against the math face"
    (!styledOut.diags.any (·.code == "W0009"))
  t "the styled scalar still reaches the page (set in its text face)"
    ((Layout.docScalars styledDoc).contains 'R')
  let oneStyled : Math.MList :=
    .cons (.atom .ord (.styled { slot := .sans } 'R') .nil .nil false) .nil
  t "scalarsList false drops a styled nucleus that scalarsList true keeps"
    (Math.MList.scalarsList false #[] oneStyled == #[] &&
      Math.MList.scalarsList true #[] oneStyled == #['R'])

  t "IR: text-sourced alphabets carry their typed MathTextStyle"
    (Math.MathAlphabet.textStyle? .rm == some { slot := .body, bold := false, italic := false } &&
      Math.MathAlphabet.textStyle? .it == some { slot := .body, bold := false, italic := true } &&
      Math.MathAlphabet.textStyle? .bf == some { slot := .body, bold := true, italic := false } &&
      Math.MathAlphabet.textStyle? .sf == some { slot := .sans, bold := false, italic := false } &&
      Math.MathAlphabet.textStyle? .tt == some { slot := .mono, bold := false, italic := false } &&
      Math.MathAlphabet.textStyle? .bb == none &&
      Math.MathAlphabet.textStyle? .cal == none &&
      Math.MathAlphabet.textStyle? .frak == none &&
      Math.MathAlphabet.textStyle? .bfit == none)
  t "MathML: the mathvariant projection of each typed style"
    ((({ slot := .body, bold := false, italic := false } : Math.MathTextStyle).mathvariant == "normal") &&
      (({ slot := .body, bold := true, italic := false } : Math.MathTextStyle).mathvariant == "bold") &&
      (({ slot := .body, bold := false, italic := true } : Math.MathTextStyle).mathvariant == "italic") &&
      (({ slot := .sans, bold := false, italic := false } : Math.MathTextStyle).mathvariant == "sans-serif") &&
      (({ slot := .mono, bold := false, italic := false } : Math.MathTextStyle).mathvariant == "monospace"))
  t "MathML: the CSS projection of each typed style"
    ((({ slot := .body, bold := false, italic := false } : Math.MathTextStyle).css
        == "font-family: var(--font-body)") &&
      (({ slot := .body, bold := true, italic := false } : Math.MathTextStyle).css
        == "font-family: var(--font-body); font-weight: 700") &&
      (({ slot := .body, bold := false, italic := true } : Math.MathTextStyle).css
        == "font-family: var(--font-body); font-style: italic") &&
      (({ slot := .sans, bold := false, italic := false } : Math.MathTextStyle).css
        == "font-family: var(--font-sans)") &&
      (({ slot := .mono, bold := false, italic := false } : Math.MathTextStyle).css
        == "font-family: var(--font-mono)") &&
      (({ slot := .sans, bold := true, italic := true } : Math.MathTextStyle).css
        == "font-family: var(--font-sans); font-weight: 700; font-style: italic"))
  let bfStyle := (Math.MathAlphabet.textStyle? .bf).getD default
  t "PDF and MathML projections agree on the one typed style for mathbf"
    (bfStyle == { slot := .body, bold := true, italic := false } &&
      mfs.lookup bfStyle.slot.toNat bfStyle.weight bfStyle.italic
        == mfs.lookup 0 700 false &&
      bfStyle.weight == 700 &&
      bfStyle.css == "font-family: var(--font-body); font-weight: 700" &&
      (Math.MathTextSlot.sans.fontVar == Math.MathTextSlot.sans.fontVar) &&
      (decide (Math.MathTextSlot.body.fontVar ≠ Math.MathTextSlot.sans.fontVar)
        == decide (Math.MathTextSlot.body.toNat ≠ Math.MathTextSlot.sans.toNat)))
  t "public-entry resolution eliminates every alphabet boundary"
    ((Math.resolveMathAlphas alphaCoverage
        (.cons (.atom .ord
          (.alpha .bf .doc (.cons (.atom .ord (.sym 'x') .nil .nil false) .nil))
          .nil .nil false) .nil)).alphaFree)
  t "an unresolved alphabet reaching MathML is a loud merror, never a silent mrow"
    (match MathMl.nucNode {} false .ord
        (Math.MNucleus.alpha .bf .doc (.cons (.atom .ord (.sym 'x') .nil .nil false) .nil)) with
      | .elem tag _ kids => tag == "merror" && !kids.isEmpty
      | _ => false)

  -- Chromium honours no non-`normal` mathvariant, so the style rides a `style` attribute.
  let styledLeaf (sl : Math.MathTextSlot) (b i : Bool) (c : Char) : Html.Node :=
    MathMl.nucNode {} false .ord (.styled { slot := sl, bold := b, italic := i } c)
  let leafFacts (n : Html.Node) : Option (String × Option String × Option String × String) :=
    match n with
    | .elem tag attrs _ =>
      some (tag, (attrs.find? (·.1 == "style")).map (·.2),
        (attrs.find? (·.1 == "mathvariant")).map (·.2), nodeTextOne "" n)
    | _ => none
  t "styled normal letter: mi, body family, no weight/style, mathvariant normal, scalar kept"
    (leafFacts (styledLeaf .body false false 'x')
      == some ("mi", some "font-family: var(--font-body)", some "normal", "x"))
  t "styled bold letter: mi carries font-weight 700, scalar kept"
    (leafFacts (styledLeaf .body true false 'x')
      == some ("mi", some "font-family: var(--font-body); font-weight: 700", some "normal", "x"))
  t "styled italic letter: mi carries font-style italic, scalar kept"
    (leafFacts (styledLeaf .body false true 'x')
      == some ("mi", some "font-family: var(--font-body); font-style: italic", some "normal", "x"))
  t "styled sans letter: mi carries the sans family, scalar kept"
    (leafFacts (styledLeaf .sans false false 'x')
      == some ("mi", some "font-family: var(--font-sans)", some "normal", "x"))
  t "styled mono letter: mi carries the mono family, scalar kept"
    (leafFacts (styledLeaf .mono false false 'x')
      == some ("mi", some "font-family: var(--font-mono)", some "normal", "x"))
  t "styled bold digit: mn carries weight 700 with NO mathvariant cancel, digit kept"
    (leafFacts (styledLeaf .body true false '7')
      == some ("mn", some "font-family: var(--font-body); font-weight: 700", none, "7"))
  let nestedStyled : Math.MList :=
    .cons (.atom .ord (.sym 'a')
      (.cons (.atom .ord (.styled { slot := .sans } 'k') .nil .nil false) .nil) .nil false) .nil
  let nestedTree := MathMl.listNodes {} false none #[] nestedStyled
  t "nested styled sans scalar in a subscript keeps its family, mathvariant normal and letter"
    ((elemNodesList (· == "mi") #[] nestedTree.toList).any fun n =>
      leafFacts n == some ("mi", some "font-family: var(--font-sans)", some "normal", "k"))

  -- `\symsf` remaps into the face's sans range; `\mathsf` projects to the sans text slot.
  let sfCov : Math.MathAlphabetCoverage := { covered := #[(.sf, .latinUpper)] }
  let itR : Char := Char.ofNat 0x1D445   -- the parser's italic R
  let sansR' : Char := Char.ofNat 0x1D5B1 -- MATHEMATICAL SANS-SERIF CAPITAL R
  t "symsf forces the symbol source; mathsf consults the document policy"
    (sfCov.effectiveSource .sym .sf == .sym && sfCov.effectiveSource .doc .sf == .text)
  t "symsf remaps into the math sans range on a covering face (not a text slot)"
    (Math.resolveCharStack sfCov [(.sf, sfCov.effectiveSource .sym .sf)] itR
      == .sym sansR')
  t "mathsf under the default policy projects to the sans text slot"
    (Math.resolveCharStack sfCov [(.sf, sfCov.effectiveSource .doc .sf)] itR
      == (.styled { slot := .sans } 'R' : Math.Resolved))
  let sfSymCov : Math.MathAlphabetCoverage := { sfCov with sources := sfCov.sources.set .sf .sym }
  t "mathsf under mathsf=sym behaves exactly like symsf"
    (sfSymCov.effectiveSource .doc .sf == .sym &&
      Math.resolveCharStack sfSymCov [(.sf, sfSymCov.effectiveSource .doc .sf)] itR
        == .sym sansR')
  let e2eMathsf := (Ir.resolveMathAlphas alphaCoverage fira.family
    (Elab.run "synthetic.tex" "$\\mathsf{R}$").1)
  let e2eMathsfTree := HtmlDoc.blockNode { fonts := some alphaFs } e2eMathsf.1.body[0]!
  t "mathsf (default text) is a styled sans text slot, no N0018"
    (firstAttrOne "mathvariant" e2eMathsfTree == some "normal" &&
      firstAttrOne "style" e2eMathsfTree == some "font-family: var(--font-sans)" &&
      (e2eMathsf.2.filter (·.code == "N0018")).isEmpty)
  let e2eSymsf := (Ir.resolveMathAlphas alphaCoverage fira.family
    (Elab.run "synthetic.tex" "$\\symsf{R}$").1)
  t "symsf keeps its source scalar in the math face and is named once"
    ((Layout.docScalars e2eSymsf.1).contains itR &&
      !(Layout.docScalars e2eSymsf.1).contains sansR' &&
      (e2eSymsf.2.filter (fun d => d.code == "N0018" && d.subject == some "math-alpha:sf")).size == 1)

  -- Bold italic anchors: Latin U+1D468/U+1D482, Greek U+1D71C/U+1D736, nabla U+1D735.
  let bfitCov : Math.MathAlphabetCoverage := { covered :=
    #[(.bfit, .latinUpper), (.bfit, .latinLower), (.bfit, .greekUpper),
      (.bfit, .greekLower), (.bfit, .misc)] }
  t "symbfit maps A to bold-italic 𝑨 (U+1D468) on a covering face"
    (Math.resolveCharStack bfitCov [(.bfit, .sym)] (Char.ofNat 0x1D434)
      == .sym (Char.ofNat 0x1D468))
  t "symbfit maps gamma to bold-italic gamma (U+1D738)"
    (Math.resolveCharStack bfitCov [(.bfit, .sym)] (Char.ofNat 0x1D6FE)
      == .sym (Char.ofNat 0x1D738))
  t "symbfit maps nabla to bold-italic nabla (U+1D735)"
    (Math.resolveCharStack bfitCov [(.bfit, .sym)] '\u2207'
      == .sym (Char.ofNat 0x1D735))
  t "bfit's ranges are the four bold-italic ranges (no digits)"
    (Math.MathAlphabet.ranges .bfit == [.latinUpper, .latinLower, .greekUpper, .greekLower, .misc])
  let bmSrc := bfitCov.effectiveSource .doc .bm
  t "bm leaves Latin, digit, and Greek variables at their source scalars"
    (Math.resolveCharStack bfitCov [(.bm, bmSrc)] (Char.ofNat 0x1D434) == .sym (Char.ofNat 0x1D434) &&
      Math.resolveCharStack bfitCov [(.bm, bmSrc)] '5' == .sym '5' &&
      Math.resolveCharStack bfitCov [(.bm, bmSrc)] (Char.ofNat 0x1D6FC) == .sym (Char.ofNat 0x1D6FC))
  t "bm names no missing alphabet and carries no range"
    (Math.missingCharAlpha bfitCov [(.bm, bmSrc)] (Char.ofNat 0x1D434) == none &&
      Math.MathAlphabet.ranges .bm == [] && !Math.allAlphabets.contains .bm)

  let scriptSize := mbase * 72 / 100
  let ssSize := mbase * 58 / 100
  let lineOf (src : String) : Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    (((layoutOf mfs d geom).pages.flatMap (·.lines))[0]?).getD default
  let widthOf (src : String) : Dim.Length := (lineOf src).setWidth - lineIndent (lineOf src)
  t "box is a box: a+b is two medium spaces"
    (widthOf "$a+b$" ==
      adv mbase '𝑎' + mu mbase 4 + adv mbase '+' + mu mbase 4 + adv mbase '𝑏')
  t "leading minus is a sign, not an operation"
    (widthOf "$-x$" == adv mbase '−' + adv mbase '𝑥')
  t "relation earns thick space"
    (widthOf "$a=b$" ==
      adv mbase '𝑎' + mu mbase 5 + adv mbase '=' + mu mbase 5 + adv mbase '𝑏')
  t "superscript: script size, spaceAfterScript, shifted by the constant"
    (widthOf "$x^2$" ==
      adv mbase '𝑥' + adv scriptSize '2' + konst mbase 41)
  let supRuns (src : String) : Array (Dim.Length × Dim.Length) :=
    (lineOf src).segs.filterMap fun s => match s with
      | .run _ _ _ _ glyphs sz _ _ raise _ _ =>
        if raise != 0 && !glyphs.isEmpty then some (sz, raise) else none
      | _ => none
  t "superscript raise is superscriptShiftUp at the base size"
    (supRuns "$x^2$" == #[(scriptSize, konst mbase 400)])
  t "subscript drop is subscriptShiftDown"
    (supRuns "$x_i$" == #[(scriptSize, -konst mbase 350)])
  t "nested superscript reaches scriptscript and stacks its shifts"
    (supRuns "$x^{y^z}$" ==
      #[(scriptSize, konst mbase 400),
        (ssSize, konst mbase 400 + konst scriptSize 400)])
  t "no medium space inside a script"
    (widthOf "$x^{a+b}$" ==
      adv mbase '𝑥' + adv scriptSize '𝑎' + adv scriptSize '+' +
        adv scriptSize '𝑏' + konst mbase 41)
  t "sup and sub stack, advancing by the wider"
    (widthOf "$x^a_b$" ==
      adv mbase '𝑥' + max (adv scriptSize '𝑎') (adv scriptSize '𝑏') + konst mbase 41)
  let glyphChars (src : String) : Array Char :=
    (lineOf src).segs.flatMap fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.map (·.2.1)
      | _ => #[]
  t "variables italic, functions and digits upright"
    (glyphChars "$\\sin 2x$" == #['s', 'i', 'n', '2', '𝑥'])
  t "sin binds with a thin space"
    (widthOf "$\\sin x$" ==
      adv mbase 's' + adv mbase 'i' + adv mbase 'n' + mu mbase 3 + adv mbase '𝑥')
  let bDoc : Ir.Doc := { body := #[.para #[.formula false "₿"
    (.cons (.atom .ord (.sym '₿') .nil .nil false) .nil)]] }
  t "a glyph the math face lacks warns E0405 naming it"
    (((layoutOf mfs bDoc geom).diags.filter (·.code == "E0405")).map
      (fun d => (d.message, d.triggerText, d.recovery)) ==
      #[("missing glyph U+20BF for font 'Fira Math'", none, some .skipped)])
  t "docScalars carries a formula's math scalars"
    ((Layout.docScalars (Elab.run "t" "$x$").1).contains '𝑥')
  let cfs : Font.FontSet := { mfs with fallback := #[('₿', 0)] }
  let cOut := layoutOf cfs bDoc geom
  t "a math scalar the chain covers sets from the fallback face, named W0009"
    ((cOut.diags.filter (·.code == "E0405")).isEmpty &&
      (cOut.diags.filter (·.code == "W0009")).map
        (fun d => (d.message, d.triggerText, d.recovery)) ==
        #[("substituted font 'Source Serif Pro' for font 'Fira Math'", none,
          some (.replacedBy "a glyph from 'Source Serif Pro'"))] &&
      ((cOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 0 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == '₿')
        | _ => false))
  let bare : Font.FontSet := {
    fonts := #[serif, fira], index := allSlots
    fallback := #[('𝑥', 1), ('𝑦', 1)] }
  let (nd, _) := Elab.run "t" "$x^2$ and $y$"
  let nOut := layoutOf bare nd geom
  t "no math face warns W0003 once" ((nOut.diags.filter (·.code == "W0003")).size == 1)
  t "no math face preserves script boundaries in the shipped plaintext"
    (String.ofList ((bodyGlyphs nOut).toList.map (·.2)) == "(𝑥)^(2)and𝑦")
  let (dd, dds) := Elab.run "t" "a \\[x\\] b"
  t "display math splits its paragraph into a centred block"
    (dds.isEmpty && dd.body ==
      #[.para #[.text "a"],
        .center #[.para #[.formula true "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil)]],
        .para #[.text "b"]])
  t "paren math is inline math"
    ((Elab.run "t" "\\(y\\)").1.body ==
      #[.para #[.formula false "y" (.cons (.atom .ord (.sym '𝑦') .nil .nil false) .nil)]])
  t "equation* is display math"
    ((Elab.run "t" "\\begin{equation*}x\\end{equation*}").1.body.map unwrapDisplay ==
      #[.center #[.para #[.formula true "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil)]]])
  -- A parsed formula's scalars are content, so `\backslash` and `\{` ship their glyphs.
  t "a formula asking for a backslash or a brace ships the glyph"
    (warnCodes "$\\backslash + \\{x\\}$" == [] &&
      (glyphChars "$\\backslash$").contains '\\' &&
      (glyphChars "$\\{x\\}$").contains '{')
  -- A degraded code over a no-op would fail --werror for nothing.
  t "an upright wrapper inside \\text names no loss"
    (warnCodes "$\\text{\\textrm{plain} word}$" == [] &&
      warnCodes "$\\text{\\mbox{boxed} word}$" == [] &&
      glyphChars "$\\text{\\textrm{plain} word}$" ==
        glyphChars "$\\text{plain word}$")
  t "an out-of-scope construct degrades to its content and warns by name"
    (warnCodes "$\\overset{?}{=}$" == ["W0012"] &&
      ((Elab.run "t" "$\\overset{?}{=}$").1.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .math false _ => true
          | _ => false
        | _ => false))
  let bfvRaw := (Elab.run "synthetic.tex" "$\\textbf{v}$").1
  let (bfvDoc, _) := Ir.resolveMathAlphas alphaCoverage fira.family bfvRaw
  let bfvTree := HtmlDoc.blockNode { fonts := some mfs } bfvDoc.body[0]!
  t "the text-style commands render as their alphabets, no W0012"
    (warnCodes "$\\textbf{v}+\\textit{w}+\\texttt{m}+\\textsf{s}$" == [] &&
      glyphChars "$\\textbf{v}$" == #['v'] &&
      glyphChars "$\\textit{w}$" == glyphChars "$\\mathit{w}$" &&
      firstAttrOne "mathvariant" bfvTree == some "normal" &&
      firstAttrOne "style" bfvTree == some "font-family: var(--font-body); font-weight: 700")
  t "a colour inside math keeps its content without a presentation loss"
    (warnCodes "$\\textcolor{blue}{x}$" == [] &&
      glyphChars "$\\textcolor{blue}{x}$" == glyphChars "$x$")
  t "a colour wrapping a styled operator renders both"
    (warnCodes "$\\textcolor{blue}{\\textbf{\\sum_z}}$" == [] &&
      (glyphChars "$\\textcolor{blue}{\\textbf{\\sum_z}}$").contains '∑')
  t "a group inside \\text is grouping, not a construct"
    (warnCodes "$\\text{a{b}c}$" == [] &&
      glyphChars "$\\text{a{b}c}$" == glyphChars "$\\text{abc}$")
  t "a style command inside \\text keeps its letters, names the styling"
    (warnCodes "$\\text{\\textbf{bold} word}$" == ["W0385"] &&
      glyphChars "$\\text{\\textbf{bold} word}$" == glyphChars "$\\text{bold word}$")
  t "a symbol inside \\text contributes its scalar"
    (warnCodes "$\\text{a\\ldots b}$" == [] &&
      (glyphChars "$\\text{a\\ldots b}$").contains '…')
  t "a colour inside \\text keeps its content, names the colour"
    (warnCodes "$\\text{\\textcolor{indigo}{red} ink}$" == ["W0385"] &&
      glyphChars "$\\text{\\textcolor{indigo}{red} ink}$" ==
        glyphChars "$\\text{red ink}$")
  t "a coloured styled alignment renders as a grid, never as source"
    (let src := "\\begin{align*} &P(A) \\\\ &= \
\\textcolor{blue}{\\textbf{\\sum_z}} P(B) \\end{align*}"
     warnCodes src == [] &&
       ((Elab.run "t" src).1.body.any fun b => match unwrapDisplay b with
         | .center xs => xs.any fun bb => match bb with
           | .para ys => ys.any fun x => match x with
             | .formula _ _ _ => true
             | _ => false
           | _ => false
         | _ => false))
  let atomsOf (src : String) : Option Math.MList :=
    (Elab.run "t" src).1.body.findSome? fun b => match b with
      | .para xs => xs.findSome? fun x => match x with
        | .formula _ _ ml => some ml
        | _ => none
      | _ => none
  let sameFormula (a b : String) : Bool :=
    warnCodes a == [] && (atomsOf a).isSome && atomsOf a == atomsOf b
  t "literal lambda is the same atom as its control word"
    (sameFormula "$λ$" "$\\lambda$" && glyphChars "$λ$" == #['𝜆'])
  t "literal theta in a subscript is the same atom as its control word"
    (sameFormula "$M_θ$" "$M_\\theta$")
  t "literal φ and ε are the variant forms, ϕ and ϵ the symbol slots"
    (sameFormula "$φ$" "$\\varphi$" && sameFormula "$ε$" "$\\varepsilon$" &&
      sameFormula "$ϕ$" "$\\phi$" && sameFormula "$ϵ$" "$\\epsilon$")
  t "a literal capital sets upright from the math face"
    (sameFormula "$Ω$" "$\\Omega$" && glyphChars "$Ω$" == #['Ω'])
  t "literal Greek never ships as body-face source text"
    (glyphChars "$λ θ φ$" == #['𝜆', '𝜃', '𝜑'])
  -- Accents: TeXbook Appendix G rule 12 over MathTopAccentAttachment, in sp.
  let runXOf (src : String) (pick : Array (Nat × Char × Dim.Length) → Bool) : Option Dim.Length := Id.run do
    let l := lineOf src
    let mut x : Dim.Length := 0
    for s in unindented l do
      match s with
      | .run _ _ _ w glyphs _ _ _ _ _ _ =>
        if pick glyphs then return some x
        x := x + w
      | .gap w _ | .decoratedGap w _ _ => x := x + w
      | .rule w _ _ _ _ | .decoration _ w _ _ _ _ => x := x + w
      | .image _ w _ _ _ _ => x := x + w
      | .poly _ _ => pure ()
    return none
  let hatG := (fira.gid '\u0302').getD 0
  t "an accent adds no width: hat x advances as x alone"
    (warnCodes "$\\hat{x}$" == [] && widthOf "$\\hat{x}$" == adv mbase '𝑥')
  t "the mark's attachment point lands on the base's"
    (runXOf "$\\hat{x}$" (fun gs => gs.any (·.2.1 == '\u0302')) ==
      some (konst mbase (fira.topAccentX ((fira.gid '𝑥').getD 0))
        - konst mbase (fira.markAttachX hatG)))
  t "a base at accentBaseHeight leaves the mark unlifted"
    (supRuns "$\\hat{x}$" == #[])
  t "a taller base lifts the mark by its ink's excess over accentBaseHeight"
    (supRuns "$\\hat{H}$" ==
      #[(mbase, (((fira.gid '𝐻').bind fira.yExtent).map (·.2)).getD 0 * mbase
        / upem - konst mbase 527)])
  t "overline draws its rule and no glyph mark"
    (warnCodes "$\\overline{x+y}$" == [] &&
      ((lineOf "$\\overline{x+y}$").segs.filter fun s => match s with
        | .rule _ _ _ _ _ => true
        | _ => false).size == 1)
  t "an accented atom still takes its script"
    (warnCodes "$\\hat{x}^2$" == [] && warnCodes "$e^{\\hat{H}}$" == [])
  t "mathbb takes the Letterlike hole: R is ℝ"
    (glyphChars "$\\mathbb{R}$" == #['ℝ'] && warnCodes "$\\mathbb{R}$" == [])
  t "mathrm recovers the upright letters"
    (glyphChars "$\\mathrm{Err}$" == #['E', 'r', 'r'])
  t "mathbf keeps the spacing classes: x+y bolds with its medium spaces"
    (widthOf "$\\mathbf{x+y}$" ==
      serifAdv base 'x' + mu mbase 4 + adv mbase '+' + mu mbase 4 + serifAdv base 'y')
  t "mathbf's letters go through the styled bold body slot, not the math face"
    ((lineOf "$\\mathbf{x+y}$").segs.any fun s => match s with
      | .run f _ _ _ glyphs _ _ _ _ _ _ =>
        f == mfs.lookup 0 700 false && glyphs.any (·.2.1 == 'x')
      | _ => false)
  -- With no bold math version lualatex keeps `\boldsymbol{\beta}` italic (math-alphabet-diff).
  t "boldsymbol leaves a Greek variable at its source italic"
    (glyphChars "$\\boldsymbol{\\beta}$" == #['𝛽'])
  -- `\mathbf{5}` and `\boldsymbol{5}` share a codepoint and differ by face.
  let mbFive := (lineOf "$\\mathbf{5}$").segs.findSome? fun s => match s with
    | .run f _ _ _ glyphs _ _ _ _ _ _ => if glyphs.any (·.2.1 == '5') then some f else none
    | _ => none
  let bsFive := (lineOf "$\\boldsymbol{5}$").segs.findSome? fun s => match s with
    | .run f _ _ _ glyphs _ _ _ _ _ _ => if glyphs.any (·.2.1 == '5') then some f else none
    | _ => none
  t "boldsymbol leaves a digit plain; mathbf keeps the bold digit"
    (mbFive == some (mfs.lookup 0 700 false) && bsFive == some 1 && mbFive != bsFive)
  t "nested alphabets: calligraphic resets the text family for a digit"
    (glyphChars "$\\mathbf{\\mathcal{5}}$" == #['5'] &&
      (lineOf "$\\mathbf{\\mathcal{5}}$").segs.any fun s => match s with
        | .run f _ _ _ glyphs _ _ _ _ _ _ =>
          f == 1 && glyphs.any (·.2.1 == '5')
        | _ => false)
  t "nested alphabets: uncovered fraktur resets the text family for a letter"
    (glyphChars "$\\mathbf{\\mathfrak{Z}}$" == #['Z'] &&
      (lineOf "$\\mathbf{\\mathfrak{Z}}$").segs.any fun s => match s with
        | .run f _ _ _ glyphs _ _ _ _ _ _ =>
          f == 1 && glyphs.any (·.2.1 == 'Z')
        | _ => false)
  t "mathit sets the italic uppercase Greek block"
    (glyphChars "$\\mathit{\\Gamma}$" == #['𝛤'])
  t "boldsymbol leaves a Latin variable at its source italic"
    (glyphChars "$\\boldsymbol{O}$" == #['𝑂'])
  t "symbb takes its Letterlike double-struck scalar"
    (glyphChars "$\\symbb{R}$" == #['ℝ'])
  t "symbfup emboldens lowercase Greek upright"
    (glyphChars "$\\symbfup{\\gamma}$" == #['𝛄'])
  t "symup leaves the upright Greek capital"
    (glyphChars "$\\symup{\\Gamma}$" == #['Γ'])
  t "the sym family raises no unknown-command warning"
    (warnCodes "$\\symbb{R}$" == [] && warnCodes "$\\symup{\\Gamma}$" == [] &&
      warnCodes "$\\symbfup{\\gamma}$" == [])
  t "fira math covers the bb, bf, bfit, tt, it, and rm letter alphabets"
    ([Math.MathAlphabet.bb, .bf, .bfit, .tt, .it, .rm].all fun a =>
      Math.latinLetters.all fun c => (fira.gid (a.apply c)).isSome)
  t "fira math lacks cal, frak, and sf letters (all but ℊ): the fallback path"
    (([Math.MathAlphabet.cal, .frak, .sf].all fun a =>
      Math.latinLetters.all fun c =>
        (fira.gid (a.apply c)).isNone || a.apply c == '\u210A'))
  t "a word is a script's argument"
    (warnCodes "$V^\\text{null}$" == [] &&
      glyphChars "$V^\\text{null}$" == #['𝑉', 'n', 'u', 'l', 'l'])
  t "a fraction is a script's argument"
    (warnCodes "$2^\\frac{1}{2}$" == [])
  t "an alphabet is a script's argument"
    (glyphChars "$x^\\mathbb{R}$" == #['𝑥', 'ℝ'])
  t "ensuremath is transparent in math"
    (glyphChars "$\\ensuremath{x}$" == #['𝑥'])
  -- A definition sees only those before it, so a self-reference stays unexpanded.
  let wrapDoc (pre body : String) : String :=
    "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++
      "\n\\end{document}"
  let glyphsOf (pre body : String) : Array Char := glyphChars (wrapDoc pre body)
  let codesOf (pre body : String) : List String :=
    warnCodes (wrapDoc pre body)
  t "a defined macro expands inside math"
    (codesOf "\\define \\R {\\mathbb{R}}\n" "$\\R^d$" == [] &&
      glyphsOf "\\define \\R {\\mathbb{R}}\n" "$\\R^d$" == #['ℝ', '𝑑'])
  t "a parameterized macro binds its math argument"
    (glyphsOf "\\define \\abs(x: content) {|\\x|}\n" "$\\abs{u}$" ==
      #['|', '𝑢', '|'])
  t "an argument expands under the caller's definitions, later ones included"
    (glyphsOf "\\define \\wrap(x: content) {(\\x)}\n\\define \\g {y}\n"
      "$\\wrap{\\g}$" == #['(', '𝑦', ')'])
  t "a self-reference stays outside its own visible prefix and degrades named"
    (codesOf "\\define \\loop {z \\loop}\n" "$\\loop$" == ["W0012"])
  t "DeclareMathOperator declares an upright operator with Op spacing"
    (codesOf "\\DeclareMathOperator{\\Err}{Err}\n" "$\\Err(p)$" == [] &&
      glyphsOf "\\DeclareMathOperator{\\Err}{Err}\n" "$\\Err(p)$" ==
        #['E', 'r', 'r', '(', '𝑝', ')'])
  t "operator spacing: a declared operator binds like sin"
    (widthOf (wrapDoc "\\DeclareMathOperator{\\Err}{Err}\n" "$x \\Err y$") ==
      adv mbase '𝑥' + mu mbase 3 + adv mbase 'E' + adv mbase 'r'
        + adv mbase 'r' + mu mbase 3 + adv mbase '𝑦')
  t "ensuremath in text enters math"
    (glyphsOf "" "\\ensuremath{x^2}" == #['𝑥', '2'])
  let calOut := layoutOf mfs (Elab.run "t" "$\\mathcal{L}$").1 geom
  t "an unsupported calligraphic range keeps ordinary italic, named once"
    ((calOut.diags.filter (·.code == "E0405")).isEmpty &&
      (calOut.diags.filter (·.code == "W0009")).isEmpty &&
      (calOut.diags.filter (·.code == "N0018")).map (·.message) ==
        #["missing alphabet calligraphic for font 'Fira Math'"] &&
      glyphChars "$\\mathcal{L}$" == #['𝐿'])
  t "a covered alphabet stays silent"
    ((layoutOf mfs (Elab.run "t" "$\\mathbb{R}$").1 geom).diags.all
      (·.code != "N0018"))
  let noBBFira : Font := { fira with
    cmap := fira.cmap.filter fun r => !(r.1.toNat ≤ 0x1D538 && 0x1D538 ≤ r.2.1.toNat) }
  let noBBSet : Font.FontSet := { mfs with fonts := #[serif, noBBFira] }
  let bbOut := layoutOf noBBSet (Elab.run "t" "$\\mathbb{A}$").1 geom
  t "a bold letter in a covered range whose glyph is an isolated hole stands its base, named W0016"
    ((bbOut.diags.filter (·.code == "W0016")).map
      (fun d => (d.message, d.subject, d.triggerText, d.recovery)) ==
      #[("substituted glyph A for U+1D538", some "math-alpha:bb",
        none, some (.replacedBy "the base letter 'A'"))] &&
      !bbOut.diags.any (·.code == "N0018") &&
      ((bbOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 1 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == 'A')
        | _ => false))
  t "align renders as a grid; its numbers warn W0015"
    (warnCodes "\\begin{align}a &= b\\end{align}" == ["W0015"] &&
      ((Elab.run "t" "\\begin{align}a &= b\\end{align}").1.body.any fun b => match unwrapDisplay b with
        | .center bs => bs.any fun b2 => match b2 with
          | .para xs => xs.any fun x => match x with
            | .formula true _ _ => true
            | _ => false
          | _ => false
        | _ => false))
  t "a ragged align row is W0014 and still renders"
    (warnCodes "\\begin{align*}a &= b \\\\ z\\end{align*}" == ["W0014"])
  t "ragged rows of two environments each warn in their own words"
    (warnCodes ("\\begin{align*}a &= b \\\\ z\\end{align*}\n\n" ++
      "$\\begin{pmatrix}a & b \\\\ c\\end{pmatrix}$") == ["W0014", "W0014"])
  -- Per-glyph positions: (char, gid, x, raise, advance) over every line.
  let glyphInfo (src : String) : Array (Char × Nat × Dim.Length × Dim.Length × Dim.Length) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Char × Nat × Dim.Length × Dim.Length × Dim.Length) := #[]
    for page in (layoutOf mfs d geom).pages do
      for l in page.lines.filter (!·.furniture) do
        let mut x := l.x
        for s in unindented l do
          match s with
          | .gap w _ | .decoratedGap w _ _ => x := x + w
          | .rule w _ _ _ _ | .decoration _ w _ _ _ _ => x := x + w
          | .image _ w _ _ _ _ => x := x + w
          | .poly _ _ => pure ()
          | .run _ _ _ w glyphs sz _ _ raise _ _ =>
            let mut gx := x
            for (g, c, _) in glyphs do
              let a := (fira.widths[g]?.getD 0 : Int) * sz / upem
              out := out.push (c, g, gx, raise, a)
              gx := gx + a
            x := x + w
    return out
  let rules (src : String) : Array (Dim.Length × Dim.Length × Dim.Length) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Dim.Length × Dim.Length × Dim.Length) := #[]
    for page in (layoutOf mfs d geom).pages do
      for l in page.lines.filter (!·.furniture) do
        for s in l.segs do
          if let .rule w thickness raise _ _ := s then
            out := out.push (w, thickness, raise)
    return out
  t "frac advance is the wider part plus null delimiters"
    (widthOf "$\\frac12$" ==
      2 * (mbase * 12 / 100) + max (adv scriptSize '1') (adv scriptSize '2'))
  t "frac raises its numerator and drops its denominator"
    (match (glyphInfo "$\\frac12$").toList with
      | [('1', _, _, up, _), ('2', _, _, down, _)] => up > 0 && down < 0
      | _ => false)
  t "the fraction bar is fractionRuleThickness thick, as wide as the parts"
    (rules "$\\frac12$" ==
      #[(max (adv scriptSize '1') (adv scriptSize '2'), konst mbase 76,
         konst mbase 280 - konst mbase 76 / 2)])
  t "sqrt draws surd and overbar over the radicand"
    ((glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '\u221A') &&
      (rules "$\\sqrt{x}$").size == 1 &&
      (glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '𝑥'))
  t "a root index sets small before the surd"
    ((glyphInfo "$\\sqrt[3]{x}$").any (fun g => g.1 == '3' && g.2.2.2.1 > 0))
  -- The paren's base glyph is gid 9 in Fira Math.
  t "left paren grows over a display fraction"
    ((glyphInfo "\\[\\left(\\frac{a}{b}\\right)\\]").any fun g =>
      g.1 == '(' && g.2.1 != 9)
  t "an inline paren around a scalar stays the base glyph"
    ((glyphInfo "$\\left(a\\right)$").any fun g => g.1 == '(' && g.2.1 == 9)
  -- Fira Math's display-size sum is gid 1584, its base glyph 753.
  t "display sum takes the display variant"
    ((glyphInfo "\\[\\sum_{i=1}^{n} i\\]").any fun g => g.1 == '\u2211' && g.2.1 == 1584)
  t "inline sum keeps the text-size glyph and scripts beside"
    ((glyphInfo "$\\sum_{i=1}^{n} i$").any fun g => g.1 == '\u2211' && g.2.1 == 753)
  t "display limits centre on the operator within a scaled point"
    (Id.run do
      let gs := glyphInfo "\\[\\sum_{j=2}^{m} j\\]"
      let some (_, _, sx, _, sa) := gs.find? (fun g => g.1 == '\u2211') | return false
      let some (_, _, mx, mraise, ma) := gs.find? (fun g => g.1 == '𝑚') | return false
      return mraise > 0 && ((2 * mx + ma) - (2 * sx + sa)).abs ≤ 2 * Dim.Length.quantum)
  t "the lower limit sits below the operator"
    ((glyphInfo "\\[\\sum_{j=2}^{m} j\\]").any fun g => g.1 == '2' && g.2.2.2.1 < 0)
  t "align columns share their alignment point"
    (Id.run do
      let gs := glyphInfo "\\begin{align*}ab &= c \\\\ x &= yz\\end{align*}"
      let eqs := gs.filter (fun g => g.1 == '=')
      let some (_, _, x1, r1, _) := eqs[0]? | return false
      let some (_, _, x2, r2, _) := eqs[1]? | return false
      return x1 == x2 && r1 != r2)
  t "a right-aligned align cell pads by the width difference"
    (Id.run do
      let gs := glyphInfo "\\begin{align*}ab &= c \\\\ x &= yz\\end{align*}"
      let some (_, _, ax, _, _) := gs.find? (fun g => g.1 == '𝑎') | return false
      let some (_, _, xx, _, _) := gs.find? (fun g => g.1 == '𝑥') | return false
      return xx - ax == (adv mbase '𝑎' + adv mbase '𝑏') - adv mbase '𝑥')
  t "gather centres its rows on one axis"
    (Id.run do
      let gs := glyphInfo "\\begin{gather*}aaaa \\\\ b\\end{gather*}"
      let some (_, _, ax, _, _) := gs.find? (fun g => g.1 == '𝑎') | return false
      let some (_, _, bx, _, ba) := gs.find? (fun g => g.1 == '𝑏') | return false
      let w1 := 4 * adv mbase '𝑎'
      return ((2 * bx + ba) - (2 * ax + w1)).abs ≤ 2 * Dim.Length.quantum)
  t "a prime is a raised superscript prime"
    ((glyphInfo "$x'$").any fun g => g.1 == '\u2032' && g.2.2.2.1 == konst mbase 400)
  t "text inside math keeps its letters and spaces upright"
    (glyphChars "$\\text{if }x$" == #['i', 'f', ' ', '𝑥'] ||
      glyphChars "$\\text{if }x$" == #['i', 'f', '𝑥'])
  t "operatorname binds like a named function"
    (widthOf "$\\operatorname{foo} x$" ==
      adv mbase 'f' + adv mbase 'o' + adv mbase 'o' + mu mbase 3 + adv mbase '𝑥')
  t "an explicit space inside operatorname sets its width between the word's runs"
    (widthOf "$\\operatorname{ab\\,c} x$" ==
      adv mbase 'a' + adv mbase 'b' + mu mbase 3 + adv mbase 'c' + mu mbase 3 + adv mbase '𝑥')
  t "operatorname reads its group in math mode, a space in it ignored"
    (widthOf "$\\operatorname{ab\\, c} x$" == widthOf "$\\operatorname{ab\\,c} x$" &&
      widthOf "$\\operatorname{a b}$" == widthOf "$\\operatorname{ab}$")
  t "setmathfont fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\setmathfont{Fira Math}" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")
  t "fonts math key fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\fonts{ math = \"Fira Math\" }" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")

/-- The isolated-glyph-hole owner (W0016) and the whole-alphabet owner (N0018) partition by the
`remaps` bit, two builds apart. -/
def isolatedHoleChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"isolatedHole: {name} unparsable: {e}")
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraMath-Regular.otf"
  let allSlots : Array ((Nat × Nat × Bool) × Nat) :=
    ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
  let mfs : Font.FontSet := {
    fonts := #[serif, fira]
    index := allSlots
    math := some 1
    mathAlphabets := fira.mathAlphabetCoverage {} }
  let geom : Layout.Geom := {}
  let calOut := layoutOf mfs (Elab.run "t" "$\\mathcal{L}$").1 geom
  t "partition: an uncovered range keeps its source scalar, named N0018 alone"
    ((calOut.diags.filter (·.code == "N0018")).map (·.subject) ==
        #[some "math-alpha:cal"] &&
      !calOut.diags.any (·.code == "W0016"))
  let noBBFira2 : Font := { fira with
    cmap := fira.cmap.filter fun r => !(r.1.toNat ≤ 0x1D538 && 0x1D538 ≤ r.2.1.toNat) }
  let noBBSet2 : Font.FontSet := { mfs with fonts := #[serif, noBBFira2] }
  let bbOut2 := layoutOf noBBSet2 (Elab.run "t" "$\\mathbb{A}$").1 geom
  t "partition: a covered range with an isolated glyph hole is named W0016 alone, base stands"
    ((bbOut2.diags.filter (·.code == "W0016")).map (·.subject) ==
        #[some "math-alpha:bb"] &&
      !bbOut2.diags.any (·.code == "N0018") &&
      ((bbOut2.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 1 _ _ _ glyphs _ _ _ _ _ _ => glyphs.any (·.2.1 == 'A')
        | _ => false))

/-- Which artifacts one row builds, as its document declares them. -/
inductive SlotArt where
  | pdf
  | htmlEmbedded
  | htmlOwn
  | pdfHtmlOwn
  deriving Repr, BEq, Inhabited

def SlotArt.decl : SlotArt → String
  | .pdf => "formats = pdf"
  | .htmlEmbedded => "formats = html"
  | .htmlOwn => "formats = html, css = own"
  | .pdfHtmlOwn => "formats = pdf, html, css = own"

def SlotArt.name : SlotArt → String
  | .pdf => "pdf"
  | .htmlEmbedded => "html"
  | .htmlOwn => "html/css=own"
  | .pdfHtmlOwn => "pdf+html/css=own"

/-- One row: a class, its declared `\fonts` keys (none: the `LEANTEX_FONT` override), the pitch of
every family it names, its artifacts, and the slot its construct sets. -/
structure SlotRow where
  cls : String
  decl : List String
  fixed : Bool
  art : SlotArt
  slot : String
  deriving Repr, Inhabited

/-- The family a row names for a key: the monospace face in a fixed-pitch row, else a proportional
design per key. -/
def SlotRow.family (r : SlotRow) (key : String) : String :=
  if r.fixed then "Source Code Pro"
  else if key == "body" then "Source Serif Pro"
  else if key == "sans" then "Open Sans"
  else "Fira Sans"

/-- The face `LEANTEX_FONT` names for a row that declares nothing. -/
def SlotRow.overrideFile (r : SlotRow) : String :=
  if r.fixed then "SourceCodePro-Regular.otf" else "SourceSerifPro-Regular.otf"

def SlotRow.label (r : SlotRow) : String :=
  let d := if r.decl.isEmpty then "LEANTEX_FONT" else ",".intercalate r.decl
  s!"{r.cls} [{d}] {if r.fixed then "fixed" else "proportional"} {r.art.name} {r.slot}"

/-- A row's document: one paragraph whose `\texttt` or `\textsf` run spells `zqx`, a word nothing
else on the page spells. -/
def SlotRow.src (r : SlotRow) : String :=
  let fonts := if r.decl.isEmpty then "" else
    "\\fonts{ dir = \"fonts\", " ++
      ", ".intercalate (r.decl.map fun k => s!"{k} = \"{r.family k}\"") ++ " }\n"
  let run := if r.slot == "mono" then "\\texttt{zqx}" else "\\textsf{zqx}"
  let para := "Plain words and " ++ run ++ " here."
  let content := if r.cls == "beamer" then "\\begin{frame}\n" ++ para ++ "\n\\end{frame}"
    else para
  "\\documentclass{" ++ r.cls ++ "}\n" ++ fonts ++ "\\output{ " ++ r.art.decl ++ " }\n" ++
    "\\begin{document}\n" ++ content ++ "\n\\end{document}\n"

/-- The generated matrix: class × declared slots × pitch × artifacts × slot. -/
def slotRows : Array SlotRow := Id.run do
  let decls : List (List String) := [[], ["body"], ["sans"], ["mono"], ["body", "sans"],
    ["body", "mono"], ["sans", "mono"], ["body", "sans", "mono"]]
  let mut out : Array SlotRow := #[]
  for cls in ["article", "beamer", "webpage"] do
    for d in decls do
      for fixed in [false, true] do
        for art in [SlotArt.pdf, .htmlEmbedded, .htmlOwn, .pdfHtmlOwn] do
          for slot in ["mono", "sans"] do
            out := out.push { cls, decl := d, fixed, art, slot }
  return out

/-- A font file's own `post.isFixedPitch`, read from the table directory with no engine code between
the bytes and the answer. -/
def postIsFixedPitch (data : ByteArray) : Option Bool := Id.run do
  let byte (i : Nat) : Nat := (data[i]?.map (·.toNat)).getD 0
  let u16 (i : Nat) : Nat := byte i * 256 + byte (i + 1)
  let u32 (i : Nat) : Nat := u16 i * 65536 + u16 (i + 2)
  if data.size < 12 then return none
  for k in [0:u16 4] do
    let entry := 12 + 16 * k
    if byte entry == 0x70 && byte (entry + 1) == 0x6F && byte (entry + 2) == 0x73
        && byte (entry + 3) == 0x74 then
      let off := u32 (entry + 8)
      return if off + 16 ≤ data.size then some (u32 (off + 12) != 0) else none
  return none

/-- What a written PDF sets in each face resource: its name, the text its runs spell through its
`/ToUnicode`, its descriptor's `/Flags`, and its embedded program's `post` pitch. -/
def pdfFaceRuns (pdf : ByteArray) :
    Except String (Array (String × String × Int × Option Bool)) := do
  let es := (← PdfRead.objects pdf).val
  let deref := PdfCensus.deref es
  let mut texts : Std.HashMap String String := {}
  let mut flags : Std.HashMap String Int := {}
  let mut programs : Std.HashMap String (Option Bool) := {}
  for e in es do
    unless e.val.get? "Type" == some (.name "Page") do continue
    let resources := deref ((e.val.get? "Resources").getD .null)
    let mut fonts : Std.HashMap String ArtFont := {}
    if let .dict fs := deref ((resources.get? "Font").getD .null) then
      for (nm, v) in fs do
        let fo := deref v
        fonts := fonts.insert nm (artFontOf es fo)
        let cid := match deref ((fo.get? "DescendantFonts").getD .null) with
          | .arr xs => deref (xs[0]?.getD .null)
          | d => d
        let fd := deref ((cid.get? "FontDescriptor").getD .null)
        flags := flags.insert nm (((fd.get? "Flags").bind Obj.int?).getD 0)
        let program : Option Bool :=
          match (fd.get? "FontFile2").orElse fun _ => fd.get? "FontFile3" with
          | some (.ref n _) =>
            match es.find? (·.num == n) with
            | some pe =>
              match pe.decoded with
              | .ok (some bytes) => postIsFixedPitch bytes
              | _ => none
            | none => none
          | _ => none
        programs := programs.insert nm program
    let data ← match e.val.get? "Contents" with
      | some (.ref n _) =>
        match es.find? (·.num == n) with
        | some c =>
          match c.decoded with
          | .ok (some d) => pure d
          | _ => throw "a page content stream does not decode"
        | none => throw "a page's /Contents names no object"
      | _ => throw "a page has no /Contents reference"
    let mut cur : Option String := none
    let mut stack : Array CTok := #[]
    for tok in scanContent data do
      match tok with
      | .op "Tf" =>
        cur := stack.findSome? fun
          | .name n => some n
          | _ => none
        stack := #[]
      | .op o =>
        if o == "TJ" || o == "Tj" then
          if let some nm := cur then
            let toUni := (fonts[nm]?.map (·.toUni)).getD {}
            for it in stack do
              if let .hex d := it then
                texts := texts.insert nm ((texts[nm]?.getD "") ++
                  String.join ((artCodes d).toList.map fun g => toUni[g]?.getD artUnmapped))
        stack := #[]
      | other => stack := stack.push other
  return texts.toArray.map fun (nm, s) =>
    (nm, s, flags[nm]?.getD 0, (programs[nm]?).getD none)

/-- The face resource whose runs spell `needle`, with its `/Flags` and its
embedded program's own pitch. -/
def faceSetting (runs : Array (String × String × Int × Option Bool)) (needle : String) :
    Option (String × Int × Option Bool) :=
  (runs.find? fun (_, s, _, _) => hasStr s needle).map fun (nm, _, fl, p) => (nm, fl, p)

/-- The `src` of the `@font-face` rule a page sets a slot in: the first family of the slot's last
`--font-<slot>` stack with a regular upright rule, as the browser walks it. -/
def htmlSlotSource (html slot : String) : Option String := do
  let parts := html.splitOn ("--font-" ++ slot ++ ": ")
  if parts.length < 2 then none
  let decl ← parts.getLast?
  let stack ← (decl.splitOn ";").head?
  let unquote (f : String) : Option String :=
    let cs := f.trimAscii.toString.toList
    if cs.head? == some '"' && cs.getLast? == some '"' then
      some (String.ofList (cs.drop 1).dropLast)
    else none
  let fams := (stack.splitOn ",").filterMap unquote
  fams.findSome? fun fam =>
    let rule := "@font-face { font-family: \"" ++ fam ++
      "\"; font-weight: 400; font-style: normal; src: url(\""
    ((html.splitOn rule)[1]?).bind fun rest => (rest.splitOn "\"").head?

/-- One row's outcome: the driver's exit code and log, its W0390 lines, and what the artifacts say
about the slot's face. -/
structure SlotOutcome where
  exit : UInt32
  log : String
  reports : Array String
  lost : Bool
  textFace : Bool
  flagsAgree : Bool
  oracle : String

/-- Build one row with the driver in a private environment (cache, empty home, empty `PATH`) and
read its artifacts back. -/
def slotRunRow (bin : String) (dir : System.FilePath) (cache : String) (i : Nat)
    (r : SlotRow) : IO SlotOutcome := do
  let tex := dir / s!"row{i}.tex"
  IO.FS.writeFile tex r.src
  let out := dir / s!"out{i}"
  let env : Array (String × Option String) := #[("XDG_CACHE_HOME", some cache),
    ("HOME", some (dir / "home").toString), ("PATH", some (dir / "no-tools").toString),
    ("LEANTEX_FONT_PATH", none),
    ("LEANTEX_FONT", if r.decl.isEmpty then some (dir / "fonts" / r.overrideFile).toString
      else none)]
  let p ← IO.Process.output
    { cmd := bin, args := #[tex.toString, "-o", out.toString ++ "/", "--porcelain"], env := env }
  let reports := (p.stdout.splitOn "\n").toArray.filter fun l =>
    hasStr l "\"event\":\"diagnostic\"" && hasStr l "\"code\":\"W0390\""
  let mut lost := false
  let mut textFace := false
  let mut flagsAgree := true
  let mut oracle := ""
  if r.art == .pdf || r.art == .pdfHtmlOwn then
    let pdf ← IO.FS.readBinFile (out / s!"row{i}.pdf")
    match pdfFaceRuns pdf with
    | .error e => oracle := s!"pdf unreadable: {e}"
    | .ok runs =>
      match faceSetting runs "zqx", faceSetting runs "Plain" with
      | some (runFace, runFlags, runFixed), some (textRes, _, _) =>
        let same := runFace == textRes
        textFace := same
        let fixed := runFixed.getD false
        lost := if r.slot == "mono" then !fixed else same
        flagsAgree := runFixed.isSome && (runFlags % 2 == 1) == fixed
        oracle := s!"pdf: run in {runFace} (program fixed {runFixed}, flags {runFlags}), \
text in {textRes}"
      | _, _ => oracle := s!"pdf: the run or the text is not in the file: {runs.map (·.2.1)}"
  if r.art == .htmlEmbedded then
    let html ← IO.FS.readFile (out / s!"row{i}.html")
    match htmlSlotSource html r.slot, htmlSlotSource html "body" with
    | some runSource, some textSource =>
      let same := runSource == textSource
      textFace := same
      let (media, program) ← htmlDataDecode runSource
      unless media.startsWith "font/" do
        throw <| IO.userError "the slot's embedded program has no font media type"
      let pitch := (postIsFixedPitch program).getD false
      lost := if r.slot == "mono" then !pitch else same
      oracle := s!"html: embedded {media}, {program.size} bytes, fixed {pitch}, \
same as running text {same}"
    | _, _ => oracle := "html: the page ships no face for the slot or the text"
  return { exit := p.exitCode, log := p.stdout ++ p.stderr, reports, lost, textFace,
           flagsAgree, oracle }

/-- W0390 fires exactly when an artifact sets a slot's runs in a face not of the slot's kind and the
document declared no family for the slot. -/
def slotMatrixChecks (ref : IO.Ref (List String)) : IO Unit := do
  let before := (← ref.get).length
  let t := check ref
  let build ← IO.Process.output { cmd := "lake", args := #["build", "leantex", "-q"] }
  t s!"slot matrix: leantex builds:\n{build.stdout}{build.stderr}" (build.exitCode == 0)
  if build.exitCode != 0 then return
  let bin := ".lake/build/bin/leantex"
  let dir ← IO.FS.createTempDir
  IO.FS.createDirAll (dir / "fonts")
  IO.FS.createDirAll (dir / "home")
  for e in ← (System.FilePath.mk testFonts).readDir do
    if e.fileName.endsWith ".otf" || e.fileName.endsWith ".ttf" then
      IO.FS.writeBinFile (dir / "fonts" / e.fileName) (← IO.FS.readBinFile e.path)
  let cache := (dir / "cache").toString
  -- One run first, so every parallel run after it reads a warm probe cache.
  let rows := slotRows
  let warm ← slotRunRow bin dir cache rows.size (rows[0]?.getD default)
  t s!"slot matrix: the warm-up run builds: {warm.log}" (warm.exit == 0)
  let mut outcomes : Array (Option (Except IO.Error SlotOutcome)) := Array.replicate rows.size none
  -- Sixteen workers measured fastest on a 192-core host, ahead of 4, 32 and 64.
  let width := 16
  -- Workers over a static partition share no state, so a slow row delays only its own worker.
  let mut tasks := #[]
  for j in [0:width] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      let mut mine : Array (Nat × Except IO.Error SlotOutcome) := #[]
      for n in [0:rows.size / width + 1] do
        let k := j + n * width
        if rows.size ≤ k then break
        mine := mine.push (k, ← (slotRunRow bin dir cache k rows[k]!).toBaseIO)
      return mine)
  for tk in tasks do
    match tk.get with
    | .ok mine => for (k, o) in mine do outcomes := outcomes.set! k (some o)
    | .error _ => pure ()
  let mut expectedReports := 0
  let mut expectedSilent := 0
  let mut flagDisagree : Array String := #[]
  for k in [0:rows.size] do
    let r := rows[k]!
    match (outcomes[k]?).bind id with
    | some (.ok o) =>
      IO.FS.writeFile (dir / s!"row{k}.log") (o.oracle ++ "\n" ++ o.log)
      t s!"slot matrix {r.label}: the build succeeds: {o.log}" (o.exit == 0)
      unless o.flagsAgree do flagDisagree := flagDisagree.push s!"{r.label} ({o.oracle})"
      let declared := r.decl.contains r.slot
      let want := !declared && o.lost
      if want then expectedReports := expectedReports + 1
      else expectedSilent := expectedSilent + 1
      t s!"slot matrix {r.label}: {if want then "reported" else "silent"} ({o.oracle}); \
got {o.reports.size} W0390" (o.reports.size == (if want then 1 else 0))
      if want then
        let word := if r.slot == "mono" then SlotLoss.monoWord else SlotLoss.sansWord
        let served := if o.textFace then SlotLoss.Served.bodyFace else .bodyFamily
        let only := if r.art == .pdfHtmlOwn then
          some (Tests.SlotLossWording.artifactWord .pdf) else none
        let expect := Render.porcelainDiag
          (DriverDiag.slotCollapsed word.key word.runs
            (Tests.SlotLossWording.servedWords served) word.note only true (!r.decl.isEmpty))
        t s!"slot matrix {r.label}: the report says {Tests.SlotLossWording.servedWords served}{if only.isSome then " in the PDF" else ""}: \
{o.reports}" (o.reports.map (·.trimAscii.toString) == #[expect])
    | some (.error e) => t s!"slot matrix {r.label}: the row runs: {e}" false
    | none => t s!"slot matrix {r.label}: the row ran" false
  -- Non-vacuity: the matrix reaches both answers.
  t s!"slot matrix: some rows are losses ({expectedReports})" (0 < expectedReports)
  t s!"slot matrix: some rows are not ({expectedSilent})" (0 < expectedSilent)
  t s!"slot matrix: every PDF declares the run face's pitch its embedded program does: \
{flagDisagree}" flagDisagree.isEmpty
  if (← ref.get).length == before then
    IO.FS.removeDirAll dir
  else
    IO.eprintln s!"slot matrix: retained artifacts in {dir}"

/-- A family slot set in a face not of its kind is reported: the census, the decision's four
conditions, and the message. -/
def slotLossChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (body : String) : Ir.Doc := (elabStr ("\\documentclass{article}\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}")).1
  t "slot census: a plain paragraph asks for no family slot past the body"
    ((SlotLoss.slotsUsed (doc "Plain body prose here.")).isEmpty)
  t "slot census: '\\texttt' asks for the mono slot"
    ((SlotLoss.slotsUsed (doc "A \\texttt{fixed pitch} run.")).contains 2)
  t "slot census: '\\url' asks for the mono slot"
    ((SlotLoss.slotsUsed (doc "A link \\url{https://example.org/a} here.")).contains 2)
  t "slot census: a verbatim block asks for the mono slot"
    ((SlotLoss.slotsUsed (doc "\\begin{verbatim}\nliteral\n\\end{verbatim}")).contains 2)
  t "slot census: '\\textsf' asks for the sans slot"
    ((SlotLoss.slotsUsed (doc "A \\textsf{sans} run.")).contains 1)
  t "slot census: '\\texttt' asks for no sans slot"
    (!(SlotLoss.slotsUsed (doc "A \\texttt{fixed pitch} run.")).contains 1)
  t "slot census: a link with no typewriter style asks for no mono slot"
    (!(SlotLoss.slotsUsed (doc "A link \\href{https://example.org/a}{here}.")).contains 2)
  -- Registered debt: a `\style` font template counts as a mono use with no such element.
  let debtDoc := (elabStr ("\\documentclass{article}\n\\style{section}{ font = {\\ttfamily} }\n" ++
    "\\begin{document}\nPlain body prose here, and no section at all.\n\\end{document}")).1
  let debtSlots := SlotLoss.slotsUsed debtDoc
  if debtSlots == #[2] then
    t "slot census debt: an unused furniture template still counts (owner: Layout per-run slots)"
      true
  else
    failures ref ("slot census debt: the registered answer no longer holds — a furniture " ++
      s!"template now yields {debtSlots.toList}; if the layout-s per-run slot landed, " ++
      "delete this row and the PLAN registration")
  t "slot census: the fold reaches a footnote body"
    ((SlotLoss.slotsUsed (doc "Text\\footnote{A \\texttt{note} run.}")).contains 2)
  t "slot census: the fold reaches a running head"
    ((SlotLoss.slotsUsed ((elabStr ("\\documentclass{article}\n" ++
      "\\runninghead{A \\texttt{head} run}\n\\begin{document}\nx\n\\end{document}")).1)).contains 2)
  -- `collapsed`: one face in every slot; `declared`: a distinct mono in slot 2.
  let load (name : String) : IO (Option Font) := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure (some f)
    | .error _ => pure none
  let some body ← load "SourceSerifPro-Regular.otf"
    | failures ref "slot loss: SourceSerifPro-Regular.otf missing"; return
  let some code ← load "SourceCodePro-Regular.otf"
    | failures ref "slot loss: SourceCodePro-Regular.otf missing"; return
  let slots (idx0 idx1 idx2 : Nat) : Array ((Nat × Nat × Bool) × Nat) :=
    #[((0, 400, false), idx0), ((1, 400, false), idx1), ((2, 400, false), idx2)]
  let collapsed : Font.FontSet := { fonts := #[body], index := slots 0 0 0 }
  let declared : Font.FontSet := { fonts := #[body, code], index := slots 0 0 1 }
  let monoSpec : Ir.FontSpec := { mono := some "Source Code Pro" }
  let usesMono := doc "A \\texttt{fixed pitch} run."
  let usesNeither := doc "Plain body prose here."
  -- A PDF always carries its faces; an HTML-only page under a declared stylesheet carries none.
  let pdf := SlotLoss.carries #[.pdf] .embedded
  let bare := SlotLoss.carries #[.html, .md] .none
  t "slot loss: an undeclared mono slot on the body face is reported"
    ((SlotLoss.diags {} collapsed usesMono pdf).size == 1)
  t "slot loss: the report is the mono slot"
    ((SlotLoss.losses {} collapsed #[2] pdf).map (·.key) == #["mono"])
  t "slot loss: a declared mono family is not reported"
    ((SlotLoss.diags monoSpec declared usesMono pdf).isEmpty)
  t "slot loss: a declared family resolving onto the body face is still the document's own choice"
    ((SlotLoss.diags monoSpec collapsed usesMono pdf).isEmpty)
  t "slot loss: a slot the document never asks for is not reported"
    ((SlotLoss.diags {} collapsed usesNeither pdf).isEmpty)
  t "slot loss: a slot on its own fixed-pitch face is not reported"
    ((SlotLoss.losses {} declared #[2] pdf).isEmpty)
  let monoBody : Font.FontSet := { fonts := #[code], index := slots 0 0 0 }
  t "slot loss: a fixed-pitch body face loses no mono, though the index collapsed"
    ((SlotLoss.diags {} monoBody usesMono pdf).isEmpty)
  t "slot loss: the mono slot's face answers for its pitch"
    (monoBody.slotIsFixedPitch 2 && !collapsed.slotIsFixedPitch 2)
  let some sans ← load "OpenSans-Regular.ttf"
    | failures ref "slot loss: OpenSans-Regular.ttf missing"; return
  let deck : Font.FontSet := { fonts := #[sans, body], index := slots 0 0 1 }
  let deckOnCode : Font.FontSet := { fonts := #[sans, code], index := slots 0 0 1 }
  let deckSpec : Ir.FontSpec := { body := some "Source Serif Pro", sans := some "Open Sans" }
  t "slot loss: a deck's mono slot on the proportional body family is reported, though the index is its own"
    (!deck.slotCollapsed 2 && (SlotLoss.losses deckSpec deck #[2] pdf).map (·.key) == #["mono"])
  t "slot loss: a deck's mono slot on a fixed-pitch body family is not"
    ((SlotLoss.losses deckSpec deckOnCode #[2] pdf).isEmpty)
  -- The sans slot claims no pitch: no face flag records a sans design.
  t "slot loss: the sans slot is reported on a fixed-pitch body too"
    ((SlotLoss.losses {} monoBody #[1] pdf).map (·.key) == #["sans"])
  t "slot loss: a slot on the text's own face was served by the body face"
    (SlotLoss.served collapsed 2 == .bodyFace)
  t "slot loss: a deck's mono slot was served by the body family"
    (SlotLoss.served deck 2 == .bodyFamily)
  t "slot loss: the deck's report says the body family served the slot"
    (((SlotLoss.diags deckSpec deck usesMono pdf).map fun d => (d.message, d.detail)) ==
      #[("missing family mono",
        some "typewriter runs set in the body family, which is not fixed-pitch")])
  t "slot loss: an artifact carrying no face reports nothing"
    ((SlotLoss.diags {} collapsed usesMono bare).isEmpty)
  t "slot loss: a PDF carries a face whatever the font policy"
    ((SlotLoss.carries #[.pdf] .none).faced == #[.pdf] &&
      (SlotLoss.carries #[.pdf] .embedded).faced == #[.pdf])
  t "slot loss: an HTML page carries a face only when it embeds one"
    ((SlotLoss.carries #[.html] .embedded).faced == #[.html] &&
      (SlotLoss.carries #[.html] .none).faced.isEmpty)
  t "slot loss: a markdown twin carries no face and sets no run in one"
    (SlotLoss.carries #[.md] .embedded == { faced := #[], unfaced := #[] })
  let mixed := SlotLoss.carries #[.pdf, .html] .none
  t "slot loss: a PDF beside an unfaced page is the one artifact named"
    (Tests.SlotLossWording.carryOnly mixed == some "the PDF")
  t "slot loss: a build whose every artifact carries the face names none"
    (Tests.SlotLossWording.carryOnly (SlotLoss.carries #[.pdf, .html, .md] .embedded) == none &&
      Tests.SlotLossWording.carryOnly pdf == none)
  t "slot loss: the mixed build's report says the PDF lost"
    (((SlotLoss.diags {} collapsed usesMono mixed).map fun d => (d.message, d.detail)) ==
      #[("missing family mono",
        some "in the PDF, typewriter runs set in the body face, which is not fixed-pitch")])
  t "slot loss: the body slot is never reported"
    ((SlotLoss.losses {} collapsed #[0, 1, 2] pdf).all (·.slot != 0))
  let manyRuns := doc ("A \\texttt{one} run, a \\texttt{two} run, a \\texttt{three} run, " ++
    "\\url{https://example.org/a}, and \\textsf{sans}.\n" ++
    "\\begin{verbatim}\nliteral\n\\end{verbatim}")
  t "slot loss: one report per lost slot, not one per run"
    ((SlotLoss.diags {} collapsed manyRuns pdf).size == 2)
  let monoDiag := (SlotLoss.diags {} collapsed usesMono pdf)[0]?
  t "slot loss: the report is its own code, not the variant axis (W0390)"
    ((monoDiag.map (·.code)) == some "W0390")
  t "slot loss: the report carries its slot as subject, so it is counted"
    ((monoDiag.bind (·.subject)) == some "slot:mono")
  t "slot loss: a counted loss is what W0390 declares"
    (DiagCode.W0390.censused && DiagCode.W0390.loss == Loss.degraded)
  t "slot loss: the report names no face, so it reads the same on every host"
    ((monoDiag.map fun d => !hasStr d.message "Serif").getD false)
  t "slot loss: the report names the slot's runs, not constructs the document may not have written"
    ((monoDiag.map fun d => !hasStr d.message "\\url").getD false)

  -- A provisional assembly's index has no entry past the body; the report reads the settled set.
  let provisional : Font.FontSet := { fonts := #[body], index := #[((0, 400, false), 0)] }
  t "slot loss: a slot-0-only index would report every other slot, which only the settled set avoids"
    ((SlotLoss.losses {} provisional #[1, 2] pdf).size == 2)
  t "slot loss: the same document on a settled index reports only what it lost"
    ((SlotLoss.losses monoSpec declared #[1, 2] pdf).size == 1)
  slotMatrixChecks ref
