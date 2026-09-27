import Tests.Support
import Tests.Artifact

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

/-- The weight axis's string half, executable because String does not
kernel-reduce (`Weight.ofCss_css_id` in Ir.lean carries the numeric half
as a theorem): parsing inverts printing over every series, the NFSS
combination rules hold, and a face's OS/2 500 reads as the `m` series —
a Medium face serving as a document's regular. -/
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
dumping a thousand names, and `families` is linear in the face count. -/
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
  -- families must be linear in the face count. The shape that made the
  -- quadratic version cost two seconds was a TeX Live tree: ~3000 faces in
  -- ~1000 families, so `seen` grew to a thousand names re-normalised for
  -- every face. Synthesised here in that shape — the suite reads no host
  -- fonts — with distinct families, so dedupe is checked exactly too.
  let many := ((List.range 3000).map fun i => synthFace s!"Family {i / 3}" s!"/x/{i}.otf").toArray
  let t0 ← IO.monoMsNow
  let fams' := FontDb.families many
  -- Consumed before the clock is read again: a pure `let` floats to its
  -- first use, so a timing with nothing between the two reads measures
  -- nothing (the quadratic version "took 0 ms" that way; forced, 21 s).
  t "families dedupes" (fams'.size == 1000)
  let ms := (← IO.monoMsNow) - t0
  t s!"families is linear ({ms} ms for {many.size} faces)" (ms < 200)
  -- A fontspec name like "Alpha Sans Light" is no family, but it names a
  -- face: family plus subfamily matches it, its italic sibling comes along,
  -- and its true bold is honestly unsatisfied rather than silently heavier.
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

/-- The weight axis below the driver: series spellings in `\fonts`, exact
resolution for an installed weight, the nearest-with-W0366 substitution
for a missing one, categorical italic, and the declared-face override —
plus `docWeightKeys`, the precompute contract that tells the driver which
off-corner keys a document's styles can ask for. -/
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
  -- Resolution on the axis, over synthetic faces.
  let subMsg : Option FontDb.Substituted → Option String
    | some s => some (DriverDiag.substituted s).message
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
        (subMsg r.2).getD "" |>.startsWith "'Alpha Sans' asks for weight 200")) ==
      some ("Light", true))
  t "a declared face for a weight key is met exactly"
    ((FontDb.resolveWeight faces "Alpha Sans" (some "Alpha Sans Light") 300 false).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", none))
  t "a declared face the host lacks degrades and says so"
    (((FontDb.resolveWeight faces "Alpha Sans" (some "Nope Light") 300 false).map
      (fun r => (subMsg r.2).getD "")).getD "" |>.startsWith
      "'Alpha Sans' declares 'Nope Light' as its weight-300 face")
  t "the 400 and 700 corners stay resolveVariant's"
    ((FontDb.resolveWeight faces "Alpha Sans" none 700 false).map
        (fun r => (r.1.subfamily, subMsg r.2)) ==
      (FontDb.resolveVariant faces "Alpha Sans" none { bold := true }).map
        (fun r => (r.1.subfamily, subMsg r.2)))
  -- The key census: exactly the off-corner keys the styled ancestry
  -- reaches, with slot and italic applied as layout will apply them.
  let doc : Ir.Doc := { body := #[.para #[.styled (.series .l)
    #[.text "x", .styled .italic #[.text "y"]]]] }
  t "docWeightKeys folds the styled ancestry"
    (Layout.docWeightKeys doc == #[(0, 300, false), (0, 300, true)])
  let corner : Ir.Doc := { body := #[.para #[.styled .bold #[.text "x"]]] }
  t "corner weights collect no extra keys" ((Layout.docWeightKeys corner).isEmpty)
  -- The surface, end to end: \fontseries rides Compat's @series marker
  -- through declStyleOf into a .series style the collector then sees.
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
  -- FontFace lands as the native declaration, * expanding to the family.
  let ff := (elabStr (pre ++ "\\setmainfont{Alpha Sans}[UprightFont=*-Medium, " ++
    "FontFace={l}{n}{*-Light}]" ++ post)).1.fonts
  t "FontFace declares the series face" (ff.faceFor 0 300 false == some "Alpha Sans-Light")
  t "FontFace rides beside UprightFont" (ff.faceFor 0 400 false == some "Alpha Sans-Medium")
  t "a FontFace shape off the model is named"
    ((elabStr (pre ++ "\\setmainfont{Alpha Sans}[FontFace={l}{sc}{*-Light}]" ++ post)).2.map
      (·.code) |>.contains "W0104")
  -- A 0-ary definition ending in a declaration styles the rest of the
  -- enclosing group — expansion is token replacement, so the declaration
  -- must take the same scope written directly. The invariant whose absence
  -- was the card defect: the body elaborated in isolation left the style
  -- wrapping the empty rest of the body, and every {\cardlight …} run
  -- rendered upright beside an empty styled node.
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

/-- fontspec's per-variant face options (`BoldFont=` and siblings) reach the
font spec and win over the family's own variant; a declared face the host
lacks degrades with a message that says the declaration could not be met and
names the face actually used. -/
def declaredFaceChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let pre := "\\documentclass{article}"
  let post := "\\begin{document}x\\end{document}"
  -- The compat layer carries the four face options into the spec.
  let d := (elabStr (pre ++ "\\setsansfont[ItalicFont={Alpha Sans Light Italic}, " ++
    "BoldFont={Alpha Sans}, BoldItalicFont={Alpha Sans Italic}]{Alpha Sans Light}" ++
    post)).1.fonts
  t "compat sans family" (d.sans == some "Alpha Sans Light")
  t "compat BoldFont" (d.faceFor 1 700 false == some "Alpha Sans")
  t "compat ItalicFont" (d.faceFor 1 400 true == some "Alpha Sans Light Italic")
  t "compat BoldItalicFont" (d.faceFor 1 700 true == some "Alpha Sans Italic")
  t "compat no UprightFont declared" (d.faceFor 1 400 false == none)
  -- ...from either side of the name, a file name included.
  let d2 := (elabStr (pre ++
    "\\setsansfont{Open Sans}[Path = fonts/, BoldFont = OpenSans-Bold.ttf]" ++ post)).1.fonts
  t "compat BoldFont after the name" (d2.faceFor 1 700 false == some "OpenSans-Bold.ttf")
  -- The native spelling.
  let d3 := (elabStr (pre ++ "\\fonts{ body = \"X\", body.bold = \"Y\", " ++
    "mono.upright = \"Z\" }" ++ post)).1.fonts
  t "fonts body.bold" (d3.faceFor 0 700 false == some "Y")
  t "fonts mono.upright" (d3.faceFor 2 400 false == some "Z")
  t "fonts unknown variant key" (errCodes (pre ++ "\\fonts{ body.slanted = \"Y\" }" ++ post)
    == ["E0322"])
  t "fonts variant wrong type" (errCodes (pre ++ "\\fonts{ body.bold = 12 }" ++ post)
    == ["E0323"])
  -- fontspec's `*` in a per-variant name stands for the family name.
  let d4 := (elabStr (pre ++ "\\setsansfont[UprightFont=*-Medium]{Inter}" ++ post)).1.fonts
  t "fontspec * expands to the family name" (d4.faceFor 1 400 false == some "Inter-Medium")
  -- Resolution: the declared face wins over the family's own variant.
  let subMsg : Option FontDb.Substituted → Option String
    | some s => some (DriverDiag.substituted s).message
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
  -- A declared face the host lacks: family fallback, message says so.
  t "declared face the host lacks degrades and says so"
    ((FontDb.resolveVariant faces "Alpha Sans Light" (some "Nope Sans") { bold := true }).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", some
        ("'Alpha Sans Light' declares 'Nope Sans' as its bold face, " ++
         "which is not installed; 'Alpha Sans Light' substitutes")))
  -- No declaration: the substitution message names the face actually used.
  t "substitution names the face actually used"
    ((FontDb.resolveVariant faces "Alpha Sans Light" none { bold := true }).map
      (subMsg ·.2) ==
      some (some "'Alpha Sans Light' has no bold face; 'Alpha Sans Light' substitutes"))
  t "a satisfied variant carries no message"
    ((FontDb.resolveVariant faces "Alpha Sans" none {}).map (subMsg ·.2) == some none)
  t "a missing family is still the caller's E0403"
    ((FontDb.resolveVariant faces "Nope Sans" (some "Also Nope") { bold := true }).isNone)
  -- A weighted name with no such weight installed: the nearest installed
  -- weight substitutes and the message names both weights (W0366).
  let beta700 : FontDb.Face := { synthFace "Beta Sans" "/x/bs-b.otf" with
    subfamily := "Bold", bold := true, weight := 700 }
  let betas := #[synthFace "Beta Sans" "/x/bs-r.otf", beta700]
  t "a missing weight resolves to the nearest installed weight"
    ((FontDb.resolveVariant betas "Beta Sans Light" none {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Regular",
        some ("'Beta Sans Light' asks for weight 300, which is not installed; " ++
          "'Beta Sans Regular' (weight 400) is the nearest")))
  t "a declared weighted face the host lacks takes the nearest weight"
    ((FontDb.resolveVariant betas "Beta Sans" (some "Beta Sans Medium") {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Regular",
        some ("'Beta Sans Medium' asks for weight 500, which is not installed; " ++
          "'Beta Sans Regular' (weight 400) is the nearest")))
  let betaLight : FontDb.Face := { synthFace "Beta Sans" "/x/bs-l.otf" with
    subfamily := "Light", weight := 300 }
  t "an installed weight is served exactly and stays silent"
    ((FontDb.resolveVariant (betas.push betaLight) "Beta Sans Light" none {}).map
      (fun r => (r.1.subfamily, subMsg r.2)) == some ("Light", none))
  -- A declared file name denotes that exact scanned face.
  let shipped ← FontDb.scanRoots [testFonts]
  t "a declared file name denotes that exact face"
    ((FontDb.resolveVariant shipped "Open Sans" (some "SourceSerifPro-Bold.otf")
      { bold := true }).map (fun r => (r.1.path, subMsg r.2)) ==
      some (testFonts ++ "/SourceSerifPro-Bold.otf", none))

/-- Icons: the fontawesome5 spellings elaborate to `Inline.icon` — the
package's own name-to-scalar table, a required text alternative — layout
sets the glyph from whichever face the per-scalar chain covers it with,
deliberately and without the W0009 substitution warning, and an icon no
face covers is the ordinary coverage loss (E0405). HTML hides the glyph
from assistive technology and names the icon on its wrapper (WCAG 2.2
SC 1.1.1); the markdown twin renders the text alternative itself. -/
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
  -- HTML: the glyph is aria-hidden, the accessible name rides the wrapper.
  let page := (HtmlDoc.emit {} doc).1
  let has := hasStr page
  t "html hides the glyph and names the icon"
    (has ("<span class=\"icon\" role=\"img\" aria-label=\"GitHub\">" ++
      "<span aria-hidden=\"true\">\uF09B</span></span>"))
  t "html carries the overridden name"
    (has "aria-label=\"Return to top\"")
  -- Every icon has an accessible name: an empty aria-label is
  -- unrepresentable upstream (the constructor requires a label), and the
  -- rendered page witnesses it.
  t "no icon renders with an empty accessible name" (!has "aria-label=\"\"")
  -- The markdown twin renders the text alternative.
  let md := (MarkdownDoc.emit doc)
  t "markdown renders the text alternative, never the raw scalar"
    ((md.splitOn "GitHub").length ≥ 2 && (md.splitOn "\uF09B").length == 1)
  -- Layout: the icon sets from the covering face without a substitution
  -- warning; no coverage is the ordinary E0405.
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"icons: {name} unparsable: {e}")
  let sans ← load "OpenSans-Regular.ttf"
  let iconsFace ← load "ExampleIcons-Regular.ttf"
  -- post.italicAngle is the PDF descriptor's derivation: the parser reads
  -- the face's own declared slant, zero when it declares none.
  let italicFace ← load "OpenSans-Italic.ttf"
  t "the parser reads the declared slant from post"
    (italicFace.italicAngle == -12 && sans.italicAngle == 0)
  t "coverage premise: only the invented icon face has U+F09B"
    ((sans.gid '\uF09B').isNone && (iconsFace.gid '\uF09B').isSome)
  -- The interword space from the face, never zero: the fontloader's own
  -- chain (space glyph; else half the em dash; else half the em). Every
  -- fixture face carries a space glyph, so the fallback arms are
  -- exercised on copies with the covering cmap ranges filtered out.
  t "spaceAdvance is the space glyph's advance where one exists"
    (sans.spaceAdvance == sans.advance ' ' && sans.advance ' ' > 0)
  let noSpace : Font.Font :=
    { sans with cmap := sans.cmap.filter fun r => r.1 > 32 || r.2.1 < 32 }
  t "a face without a space glyph takes half the em dash"
    (noSpace.advance ' ' == 0 &&
     noSpace.spaceAdvance == noSpace.advance '—' / 2 && noSpace.spaceAdvance > 0)
  let dash := '—'.toNat.toUInt32
  let noDash : Font.Font :=
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
      | .run 1 _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '\uF09B')
      | _ => false)
  t "a deliberate icon face is not a substitution warning"
    (!out.diags.any (·.code == "W0009"))
  let dropOut := layoutOf bare glyphDoc geom
  t "an uncovered icon is the ordinary coverage loss, naming the scalar"
    ((dropOut.diags.filter (·.code == "E0405")).any
      fun d => (d.message.splitOn "U+F09B").length ≥ 2)
  -- The icon scalar enters the same fallback precompute text does.
  t "docScalars carries the icon scalar" ((Layout.docScalars glyphDoc).contains '\uF09B')

/-- The GSUB small-caps parse, measured over every shipped corpus face: which
carry `smcp` and `c2sc`, and that the composed map is uniform — a capital and
its lowercase land on the same small-cap glyph, which is what lets mixed-case
source render at one height. The presence facts double as the coverage
premises for the layout checks: real substitution is exercised on a face that
has the features, synthesis on one that does not. -/
def smallCapsGsubChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"smallcaps: {name} unparsable: {e}")
  let features (name : String) : IO (Bool × Bool × Bool) := do
    let f ← load name
    pure (f.hasSmcp, f.hasC2sc, !f.smallCaps.isEmpty)
  -- Measured presence, per shipped face. The italic Source Serif faces ship
  -- without small caps; that is the font's own choice, recorded here so a
  -- change of shipped fixture is a visible test change.
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
  -- Uniformity of the composed map: for every letter, A and a substitute to
  -- the same small-cap glyph, distinct from the full capital.
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraSans-Regular.otf"
  let uniform (f : Font.Font) : Bool := Id.run do
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
  -- A face without the features substitutes nothing: identity, so synthesis
  -- is the layout's decision, never a half-applied map.
  let sans ← load "OpenSans-Regular.ttf"
  t "a face without the features maps every gid to itself"
    ((sans.gid 'a').all fun g => sans.smallCapGid g == g)
  -- The rendered claim, over Layout.Out (never an IR dump): what the page
  -- draws for a small-caps run is the same glyphs at the same sizes
  -- whatever the casing of the source — that is what "uniform" means — and
  -- differs from the plain rendering. Both mechanisms are held to it: real
  -- substitution on the serif face, synthesis on the sans face.
  let geom : Layout.Geom := {}
  let allVariants (slot idx : Nat) : List ((Nat × Nat × Bool) × Nat) :=
    [((slot, 400, false), idx), ((slot, 700, false), idx),
     ((slot, 400, true), idx), ((slot, 700, true), idx)]
  let set (f : Font.Font) : Font.FontSet := {
    fonts := #[f]
    index := (allVariants 0 0 ++ allVariants 1 0 ++ allVariants 2 0).toArray }
  let drawn (fs : Font.FontSet) (src : String) : Array (Array (Nat × Char × Dim.Sp) × Dim.Sp) :=
    (bodyLines (layoutOf fs (Elab.run "t" src).1 geom)).flatMap
      (·.segs.filterMap fun s =>
        match s with
        | .run _ _ _ _ glyphs size _ _ _ _ => some (glyphs, size)
        | _ => none)
  let ink (rs : Array (Array (Nat × Char × Dim.Sp) × Dim.Sp)) : Array (Nat × Dim.Sp) :=
    rs.flatMap fun (glyphs, size) => glyphs.map fun (g, _) => (g, size)
  let scSerif := drawn (set serif) "{\\scshape PhD}"
  t "gsub small caps draw the same ink for PhD, phd, and PHD"
    (ink scSerif == ink (drawn (set serif) "{\\scshape phd}") &&
     ink scSerif == ink (drawn (set serif) "{\\scshape PHD}") &&
     ink scSerif != ink (drawn (set serif) "PhD"))
  t "gsub small caps set at full size with substituted glyphs, text as typed"
    (scSerif.all (·.2 == geom.fontSize) &&
     (scSerif.flatMap (·.1.map (·.2.1))) == #['P', 'h', 'D'] &&
     scSerif.all fun (glyphs, _) => glyphs.all fun (g, c, _) =>
       some g == (serif.gid c).map serif.smallCapGid)
  let scSans := drawn (set sans) "{\\scshape PhD}"
  t "synthesised small caps draw the same ink for PhD, phd, and PHD"
    (ink scSans == ink (drawn (set sans) "{\\scshape phd}") &&
     ink scSans == ink (drawn (set sans) "{\\scshape PHD}") &&
     ink scSans != ink (drawn (set sans) "PhD"))
  t "synthesised small caps set every letter at one reduced size"
    (!scSans.isEmpty &&
     scSans.all (·.2 == geom.fontSize * Layout.smallCapScaleFor sans / 1000))
  -- The HTML side, judged on the typed tree and the stylesheet: the run
  -- keeps the authored casing as text under the `sc` class, and the class
  -- asks for uniform small caps (CSS Fonts 4: `all-small-caps` is c2sc +
  -- smcp, the same pair the PDF path reads).
  let (scDoc, scDs) := elabStr ("\\documentclass{article}\\begin{document}" ++
    "{\\scshape PhD}\\end{document}")
  t "small caps html source clean" scDs.isEmpty
  let scTree := HtmlDoc.blockNode {} scDoc.body[0]!
  let scText : Html.Node → Bool
    | .elem _ attrs kids => attrs.contains ("class", "sc") && kids.any fun k =>
        match k with
        | .text s => s == "PhD"
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

/-- Per-glyph fallback: a scalar the styled face lacks is set from the face
the driver's map names, at the same size; the diagnostic is one line per
family+glyph, naming both families; a scalar no face covers is still an
honest E0405 naming the family; and a document whose faces cover their text
is untouched by the map — byte-identical output. The pick order over scanned
faces is the documented one, not scan order. -/
def fallbackChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
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
  -- The mapped face sets the glyph, at the styled size, in its own run.
  let (faDoc, faDs) := Elab.run "t" "for all is ∀ set\n\nagain ∀ here"
  t "fallback source clean" faDs.isEmpty
  let out := layoutOf mapped faDoc geom
  let runs := (out.pages.flatMap (·.lines)).flatMap (·.segs)
  t "fallback sets the glyph from the mapped face"
    (runs.any fun s => match s with
      | .run 1 _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '∀')
      | _ => false)
  t "fallback reports once per family+glyph, naming both faces"
    ((out.diags.filter (·.code == "W0009")).map (·.message) ==
      #["'Open Sans' has no glyph for '∀' (U+2200); set from 'Source Code Pro'"])
  t "a covered scalar raises no E0405" (!out.diags.any (·.code == "E0405"))
  -- No face covers it: dropped once per family+glyph, family named.
  let (dropDoc, _) := Elab.run "t" "lost ⟨ here\n\nand ⟨ there"
  let dropOut := layoutOf mapped dropDoc geom
  t "an uncovered scalar drops once, naming the family"
    ((dropOut.diags.filter (·.code == "E0405")).map (·.message) ==
      #["'Open Sans' has no glyph for '⟨' (U+27E8); dropped"])
  -- A document whose faces cover their text is untouched by the map.
  let (plainDoc, _) := Elab.run "t" "plain words only"
  let noMap := Pdf.write geom bare (layoutOf bare plainDoc geom).pages
  let withMap := Pdf.write geom
    { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
    (layoutOf { bare with fallback := #[('p', 1), ('a', 1), ('o', 1)] }
      plainDoc geom).pages
  t "a covered document is byte-identical under any map" (noMap == withMap)
  -- The document's scalars: text and titles, uppercase for small caps,
  -- verbatim content, no whitespace and no fixed-space kerns.
  let (scDoc, _) := Elab.run "t"
    "\\section{Tz}\n\n{\\scshape hi}\\,x\n\n\\begin{verbatim}q r\\end{verbatim}"
  let scalars := Layout.docScalars scDoc
  t "docScalars carries text, titles, and verbatim"
    (scalars.contains 'T' && scalars.contains 'z' && scalars.contains 'x' &&
      scalars.contains 'q' && scalars.contains 'r')
  t "docScalars carries the uppercase small caps set"
    (scalars.contains 'H' && scalars.contains 'I')
  -- The reported accent class: a combining sequence (e + U+0301) in
  -- regular and bold. NFC at input (UAX #15, Nfc.lean) composes it before
  -- any face is consulted, so the accent is a plain cmap hit — é ships as
  -- one glyph from every corpus face, no mark anchoring needed. What
  -- remains of the old loss class: a face that lacks the *composed* form
  -- falls back (W0009) or drops loudly naming the scalar (E0405) — never
  -- silently.
  let (accDoc, accDs) := Elab.run "t" "Be\u0301lair and \\textbf{Be\u0301lair}"
  t "combining source clean" accDs.isEmpty
  let accOut := layoutOf mapped accDoc geom
  let accGlyphs := ((accOut.pages.flatMap (·.lines)).flatMap (·.segs)).flatMap
    fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.map (·.2.1)
      | _ => #[]
  t "a combining sequence ships composed, no mark machinery"
    (accGlyphs.contains 'é' && !accGlyphs.contains '\u0301' &&
      !accOut.diags.any fun d => d.code == "W0009" || d.code == "E0405")
  t "the base letters survive whatever the mark does" (accGlyphs.contains 'B')
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
  -- The scanned-face pick order is documented: families in normalised order,
  -- upright regular first — never scan luck.
  let shipped ← FontDb.scanRoots [testFonts]
  let picks ← FontDb.fallbackPicks shipped #['∀', '₿', '𓀀']
  t "picks the first covering family in sorted order"
    (picks.contains ('∀', testFonts ++ "/FiraMath-Regular.otf"))
  t "picks the regular face of a family with variants"
    (picks.contains ('₿', testFonts ++ "/SourceSerifPro-Regular.otf"))
  t "a scalar no face covers is absent from the picks"
    (!picks.any (·.1 == '𓀀'))
  -- The undeclared-math resolution over the shipped faces, branch by
  -- branch: a body with a sourced pairing row and its companion installed
  -- gets the companion; one with no row gets the first MATH-table face
  -- under the documented order; a scan with no MATH face at all gets none
  -- (and layout degrades with W0003, pinned in mathChecks).
  t "companion branch: Fira Sans finds Fira Math with its sourced row"
    ((← FontDb.pickMathFace shipped "Fira Sans").map
        (fun (f, r) => (f.family, (r.map (·.license)).getD "")) ==
      some ("Fira Math", "SIL Open Font License"))
  t "no-companion branch: the first MATH-table face serves, rowless"
    ((← FontDb.pickMathFace shipped "Source Serif Pro").map
        (fun (f, r) => (f.family, r.isNone)) == some ("Fira Math", true))
  -- GPOS pair kerning (PairPos formats 1+2 + ClassDef; legacy kern
  -- table as HarfBuzz's fallback rule). The −41 is hb-shape's own
  -- number for Source Serif Pro "Ta" at upem 1000; Open Sans ships no
  -- pairs and must read as zero everywhere, costing nothing.
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
  -- Fira Sans keeps every kern lookup behind an extension (GPOS type 9):
  -- read through the hop, its pairs answer hb-shape's own numbers (Te −55,
  -- AV −14, LT −83, aa −5 at upem 1000, HH none); without it the face read
  -- as unkerned.
  let firaSans ← load "FiraSans-Regular.otf"
  let fk (a b : Char) : Int :=
    firaSans.kernAdv ((firaSans.gid a).getD 0) ((firaSans.gid b).getD 0)
  t "kern: pairs behind an extension lookup answer hb-shape's values"
    (fk 'T' 'e' == -55 && fk 'A' 'V' == -14 && fk 'L' 'T' == -83 && fk 'a' 'a' == -5 &&
      fk 'H' 'H' == 0)
  -- The applied value reaches the box: a "Ta" word's width is the two
  -- advances plus the (negative) kern, exactly
  -- (kern_measure_exact holds the general fact).
  let sspSet := oneFaceOf ssp
  let (taDoc, _) := Elab.run "t" "Ta"
  let taOut := layoutOf sspSet taDoc ({} : Layout.Geom)
  let taRun := ((taOut.pages.flatMap (·.lines)).flatMap (·.segs)).findSome?
    fun s => match s with
      | .run _ _ _ w glyphs _ _ _ _ _ =>
        if (glyphs.map (·.2.1)) == #['T', 'a'] then some (w, glyphs) else none
      | _ => none
  t "kern: the run width is the advances plus the pair value"
    (match taRun with
     | some (w, glyphs) =>
       let geom : Layout.Geom := {}
       let want : Dim.Sp :=
         ((ssp.widths[sspT]! : Int) * geom.fontSize / 1000
           + (-41 : Int) * geom.fontSize / 1000)
           + (ssp.widths[sspA]! : Int) * geom.fontSize / 1000
       glyphs.size == 2 && w == want
     | none => false)
  -- The run carries each glyph's laid advance, the pair value in the
  -- first: where the second glyph starts is the ink's to honour, not only
  -- the measure's (`Seg.run`; the PDF writer places by it).
  t "kern: the run carries T's advance with the pair value, a's without"
    (match taRun with
     | some (_, glyphs) =>
       let geom : Layout.Geom := {}
       glyphs.map (·.2.2) ==
         #[(ssp.widths[sspT]! : Int) * geom.fontSize / 1000 + (-41 : Int) * geom.fontSize / 1000,
           (ssp.widths[sspA]! : Int) * geom.fontSize / 1000]
     | none => false)
  t "no MATH face anywhere: the pick is none"
    ((← FontDb.pickMathFace
        (shipped.filter fun f => !(f.path.endsWith "FiraMath-Regular.otf"))
        "Fira Sans").isNone)
  t "every pairing row names a face, a source, and a licence"
    (FontDb.mathCompanions.all fun p =>
      !p.body.isEmpty && !p.companion.isEmpty && !p.source.isEmpty && !p.license.isEmpty)
  -- The order axioms pickCompanion_set_eq assumes — faceLt transitive,
  -- asymmetric, total — hold over the shipped faces, and the pick really is
  -- scan-order independent there: the theorem's hypotheses, witnessed.
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
  -- Malformed and missing candidates stay total: no answer, never an abort.
  t "tableImage of a missing file is none"
    ((← FontDb.tableImage "/nonexistent/leantex-x.otf" (fun _ => true)).isNone)
  let corrupt := System.FilePath.mk "/tmp" / "leantex-test-corrupt-fallback.otf"
  IO.FS.writeBinFile corrupt ("OTTO".toUTF8 ++ ByteArray.mk (Array.replicate 40 0xff))
  t "a corrupt candidate yields no cmap image"
    ((← FontDb.tableImage corrupt.toString (· == "cmap")).isNone)
  IO.FS.removeFile corrupt

  -- The document's own faces outrank the host's: the documented order
  -- picks Fira Math for '∀' (asserted above), but a preference on the
  -- Source Code Pro path — a document that ships that face — wins.
  let prefPicks ← FontDb.fallbackPicksPreferring
    (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['∀']
  t "a preferred (document-shipped) face answers first for what it covers"
    (prefPicks.contains ('∀', testFonts ++ "/SourceCodePro-Regular.otf"))
  t "what a preferred face leaves uncovered still reaches the full scan"
    (((← FontDb.fallbackPicksPreferring
        (fun p => (p.splitOn "SourceCodePro").length ≥ 2) shipped #['\uF09B']).find?
      (·.1 == '\uF09B')).any (fun e => (e.2.splitOn "ExampleIcons").length ≥ 2))

  -- NFC idempotence (UAX #15 §4: "the result of normalizing a string that
  -- is already normalized is the string itself") over the strings that
  -- exercise the machinery at all: every decomposition key, alone, doubled,
  -- and with a combining acute appended so reorder and blocked composition
  -- run too. The ASCII fast path is the theorem `normalizeChars_ascii_id`;
  -- this is the rest of the domain, where a reorder or compose bug breaks
  -- the fixed point.
  let acute := String.ofList ['\u0301']
  let notIdempotent := Nfc.tables.get.decomp.fold (init := #[]) fun bad k _ =>
    let c := String.ofList [Char.ofNat k.toNat]
    [c, c ++ c, c ++ acute, acute ++ c].foldl (init := bad) fun bad s =>
      let once := Nfc.normalize s
      if Nfc.normalize once == once then bad else bad.push s
  t s!"nfc is idempotent over the decomposition keys ({notIdempotent.size} broke it)"
    notIdempotent.isEmpty

  -- `Nfc.field` reads a byte past a table's end as zero, so a malformed
  -- generated table loads quietly; these are what refuse one. A
  -- decomposition record is variable-width (a 7-digit head, then 6 per
  -- part), and one cut short at the end still loads with its key and part
  -- count, so its census is byte accounting rather than an entry count.
  let tb := Nfc.load ()
  t "nfc: every fixed-width table is a whole number of entries"
    (NfcData.ccc.toUTF8.size % 8 == 0 && NfcData.comp.toUTF8.size % 18 == 0 &&
     NfcData.letters.toUTF8.size % 12 == 0 && NfcData.lower.toUTF8.size % 12 == 0)
  t "nfc: the loader keeps one entry per fixed-width entry the generator wrote"
    (tb.ccc.size == NfcData.ccc.toUTF8.size / 8 &&
     tb.comp.size == NfcData.comp.toUTF8.size / 18 &&
     tb.letters.size == NfcData.letters.toUTF8.size / 12 &&
     tb.lower.size == NfcData.lower.toUTF8.size / 12)
  t "nfc: the decomposition records account for every byte of their table"
    (tb.decomp.fold (init := 0) (fun n _ parts => n + 7 + 6 * parts.size) ==
      NfcData.decomp.toUTF8.size)

  -- A new language touches four hand-maintained sites (gen-hyphen row,
  -- gen-locale list, the Hyphen thunk, the forTag arm) — the Diag-registry
  -- lesson: a miscount must be a test failure, not a silent gap. Every
  -- shipped locale is served by Hyphen.forTag or stands on the named
  -- unhyphenated list beside this check; a tag on neither is a locale
  -- whose text silently stopped hyphenating.
  let unhyphenated : List String := []
  t "every builtin locale hyphenates or is declared unhyphenated"
    (Locale.builtin.all fun l =>
      (Hyphen.forTag l.tag).isSome || unhyphenated.contains l.tag)

/-- The default-family choice and the search roots are what make a fresh
machine work with no configuration, so they are pinned here on synthetic
faces: preference order beats scan order among preferred names; then the
first family calling itself sans; then any face; none only when nothing is
installed. Ties between duplicate installs go to scan order. -/
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
    t s!"searchDirs covers {d}" (FontDb.searchDirs.contains d)
  if let some home ← IO.getEnv "HOME" then
    t "extraDirs covers ~/Library/Fonts"
      ((← FontDb.extraDirs).contains (home ++ "/Library/Fonts"))
  -- A .ttc never reaches probe via the scan (isFontFile skips it), but probe
  -- fed one directly must classify it as unusable, never abort: its reads
  -- are bounded checks, not trusted offsets.
  let ttc := System.FilePath.mk "/tmp" / "leantex-test-synthetic.ttc"
  IO.FS.writeBinFile ttc ("ttcf".toUTF8 ++ ByteArray.mk (Array.replicate 64 0x7f))
  t "probe rejects a ttc without aborting" ((← FontDb.probe ttc.toString).isNone)
  IO.FS.removeFile ttc

/-- The shipped fonts make the suite hermetic: what `lake test` sees is a
function of the checkout, not of the host. Pinned here: scan order is sorted
path order (so ties resolve the same everywhere), a font file name denotes
its face's family (fontspec's `Path=` idiom), the compat layer carries
`Path=` into `dir` from either side of the name, the default family over the
shipped faces is the sans, and a plain face beats a condensed sibling. -/
def shippedFontChecks (ref : IO.Ref (List String)) (faces : Array FontDb.Face) : IO Unit := do
  let t := check ref
  let paths := faces.map (·.path)
  t "scan order is sorted path order" (paths == paths.qsort (· < ·))
  t "scanning again gives the same faces" ((← FontDb.scanRoots [testFonts]).map (·.path) == paths)
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
  -- **A face's pitch is the face's own `post.isFixedPitch`.** The field is
  -- at offset 12 of `post`; offset 16 is minMemType42, a memory hint most
  -- faces leave at 0 and some do not, so a reader four bytes late answers
  -- "proportional" for every monospace design and "fixed-pitch" for a
  -- proportional face whose hint is set. Two faces whose declared answers
  -- differ pin it: the shipped monospace says yes, the shipped serif no.
  -- The PDF descriptor's FixedPitch flag and every slot stack's generic
  -- both read this, as does the slot report's face test. Read through
  -- `classify` rather than a scan: the scan answers from a disk cache, and
  -- this is a claim about the parser (the artifact tier reads the two
  -- fields it reaches, `artifactPitchChecks`).
  let pitchOf (name : String) : IO (Option Bool) := do
    match Font.classify (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok c => pure (some c.isFixedPitch)
    | .error _ => pure none
  t "face pitch: a monospace design declares fixed pitch"
    ((← pitchOf "SourceCodePro-Regular.otf") == some true)
  t "face pitch: a proportional design does not"
    ((← pitchOf "SourceSerifPro-Regular.otf") == some false)

/-- The shipped faces as `classify` answers them, pinned to the classifier
version that answers so: file, family, subfamily, bold, italic, fixed pitch,
weight — every field the probe cache stores. -/
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

/-- **A stored classification is read only by the classifier that wrote
it.** Two halves. The probe cache's file name carries
`Font.classifierVersion`, checked by two scans of the shipped directory
through a private cache that differ only in which file holds one stale
row — the answer an offset-16 classifier left for Source Code Pro,
proportional and under a family no scan answers: under the unversioned
name every earlier binary wrote, the scan answers from the face; under
this version's own name the same row is served, so the cache is live and
only the name stands between the scan and the stale answer. And the
version moves with the answer: the shipped faces' classifications are
pinned to the version, so changing what `classify` says about any of them
without moving the version fails here. -/
def probeCacheChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let path := testFonts ++ "/SourceCodePro-Regular.otf"
  let some key ← FontDb.probeKey path
    | failures ref "probe cache: the shipped Source Code Pro cannot be stat'd"; return
  let stale := key ++ "\tOld Classifier\tRegular\tfalse\tfalse\tfalse\t400\n"
  let scanWith (file : String) : IO (Option FontDb.Face) := do
    let dir ← IO.FS.createTempDir
    IO.FS.writeFile (dir / file) stale
    let faces ← FontDb.scanRootsIn (some dir) [testFonts]
    IO.FS.removeDirAll dir
    return faces.find? (·.path == path)
  let legacy ← scanWith "fontdb.tsv"
  t "probe cache: a row an earlier classifier wrote is not read"
    ((legacy.map fun f => (f.family, f.fixedPitch)) == some ("Source Code Pro", true))
  let live ← scanWith FontDb.probeCacheName
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

def fontsDeclChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  -- \fonts declarations and family resolution
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

  -- Resolution runs on the shipped faces, never the host's.
  let faces ← FontDb.scanRoots [testFonts]
  t "fontdb finds the twelve shipped faces" (faces.size == 12)
  t "fontdb finds source serif" ((FontDb.families faces).any (· == "Source Serif Pro"))
  defaultFontChecks ref
  shippedFontChecks ref faces
  probeCacheChecks ref
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
  -- font parsing on the system font
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

      -- A parser is fed arbitrary files, so it has to be total over them. Every
      -- byte read used to go through `b[i]!`, which aborts the process: one
      -- font in a TeX Live tree took the whole run down with it.
      t "font parse rejects garbage"
        ((Font.parse (ByteArray.mk #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])).isOk == false)
      t "font parse rejects an empty file" ((Font.parse (ByteArray.mk #[])).isOk == false)
      -- Truncation at every length must return a verdict rather than abort.
      -- Reaching the assertion at all is the property: a panic would take the
      -- whole run down. Some truncations parse legitimately -- the metrics
      -- tables can all survive when only glyph data is lost.
      let verdicts := (List.range 64).map fun k =>
        (Font.parse (fontData.extract 0 (fontData.size * k / 64))).isOk
      t "font parse is total over truncations" (verdicts.length == 64)
      t "font parse rejects short truncations" (verdicts.take 8 |>.all (· == false))
      -- A valid font with a table header claiming more than the file holds.
      let lying := Id.run do
        let mut b := fontData.extract 0 (min fontData.size 4096)
        -- the first table entry's length field, made absurd
        for i in [0:4] do
          b := b.set! (12 + 12 + i) 0x7f
        return b
      t "font parse rejects a table that overruns the file"
        ((Font.parse lying).isOk == false)
      -- `classify` is what a family scan uses, and it must agree with `parse`
      -- about what a face is called. It used to be `parse` fed a sparse image
      -- with the metric tables missing, which is how the scan read out of
      -- bounds in the first place.
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
      -- Parse totality alone leaves the lazy readers unfuzzed. On the
      -- feature-rich faces (Source Serif: GPOS kern, GSUB, format-12 cmap;
      -- Fira Math: MATH), every truncation whose parse succeeds also forces
      -- the deferred readers -- kern pairs, underline ink, ink extents, the
      -- x ink top, the MATH variant and accent reads -- so a short table
      -- obstructs there too, never aborts. Reaching the assertion is the
      -- property; acc only forces the reads, its value is face data.
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
      -- A format-12 cmap whose group count claims ~2M groups: the count is
      -- the one file-derived loop bound with no structural limit, and it
      -- must be clamped by the bytes actually present, never trusted -- a
      -- malformed installed face otherwise demands gigabytes of pushes at
      -- every resolve.
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
      -- Two faces on one slot's weight axis: the declared weight answers,
      -- an unindexed weight falls to the slot's regular.
      let twoWeights : Font.FontSet := {
        fonts := #[font, font]
        index := #[((0, 400, false), 0), ((0, 300, false), 1)] }
      t "lookup selects the indexed weight" (twoWeights.lookup 0 300 false == 1)
      t "an unindexed weight falls to the slot regular"
        (twoWeights.lookup 0 600 false == 0)

      -- layout: hyphenation is materialized only at a chosen break; headings
      -- and list markers carry visual structure into the positioned page.
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
          | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '-')
          | .gap _ _ | .rule .. | .image .. => false
      t "layout chosen hyphen renders" (hyOut.pages[0]!.lines.size > 1 && hyphenRendered)
      -- Display type never hyphenates (Butterick, "Hyphenation"): the same
      -- word that hyphenates as body text must set unbroken as a heading,
      -- a frame title, and the document title, patterns loaded or not.
      let hyphens (doc : Ir.Doc) : Bool :=
        (layoutOf oneFace doc narrow (some pats)).pages.any fun p =>
          p.lines.any fun l => l.segs.any fun s => match s with
            | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '-')
            | .gap _ _ | .rule .. | .image .. => false
      t "a heading never hyphenates"
        (!hyphens (Elab.run "t" "\\section{incomprehensibility}").1)
      t "a frame title never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\begin{frame}{incomprehensibility}x\\end{frame}\\end{document}")).1)
      t "the title page never hyphenates"
        (!hyphens (Elab.run "t" ("\\documentclass{slides}\\begin{document}" ++
          "\\title{incomprehensibility}\\maketitle\\end{document}")).1)
      -- Display type sets ragged: justification without hyphenation would
      -- stretch a short display line across the whole measure (Butterick,
      -- "Justified text"; moloch's title templates are \raggedright).
      let (jhDoc, _) := Elab.run "t"
        "\\section{one two six ten oak elm fir ash}\n\nbody text"
      let headLines := (layoutOf oneFace jhDoc narrow (some pats)).pages.flatMap
        (·.lines) |>.filter (·.size == Layout.sectionSize narrow 1)
      t "a wrapped heading is ragged, not justified"
        (headLines.size ≥ 2 && headLines.all (·.setWidth < narrow.textWidth))
      t "layout hyphen avoids overfull" (!hyOut.diags.any (·.code == "W0005"))
      -- Scale must survive the dedup: W0005 is spanless, so the count is
      -- the only signal of how much of the document overflowed.
      let (ofDoc, _) := Elab.run "t"
        "aaaaaaaaaaaaaaaaaaaaaaaaaa\n\nbbbbbbbbbbbbbbbbbbbbbbbbbb"
      let ofOut := layoutOf oneFace ofDoc narrow
      t "overfull warning carries the count"
        ((ofOut.diags.filter (·.code == "W0005")).size == 1 &&
         ofOut.diags.any (·.message == "2 overfull lines (no feasible break)"))

      let visualSrc := "\\section{Heading}\nBody text.\n\n" ++
        "\\begin{itemize}\\item A list item.\\end{itemize}"
      let (visualDoc, visualDs) := Elab.run "t" visualSrc
      t "layout visual source clean" visualDs.isEmpty
      let visualOut := layoutOf oneFace visualDoc {} (some pats)
      let hasSectionSize := visualOut.pages.any fun p =>
        p.lines.any (·.size == Layout.sectionSize ({} : Layout.Geom) 1)
      let hasListMarker := visualOut.pages.any fun p => p.lines.any fun l =>
        l.segs.any fun s => match s with
          | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '•')
          | .gap _ _ | .rule .. | .image .. => false
      t "layout section size" hasSectionSize
      t "layout list marker" hasListMarker

      -- pdf: build a tiny document and re-verify the xref stream offsets
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



/-- M6's first slice, pinned end to end: the MATH constants read from the
shipped face, the box-is-box widths in sp (a math box's advance is the sum
of its atoms plus the spacing the table gives — recomputed here from the
font's own advances, sharing nothing with the layout walk), script sizes
and shifts from the constants, Bin degradation, script-style spacing
suppression, the italic/upright convention, and that nothing is silently
dropped: a glyph the math face lacks earns E0405 naming it, a document with
no math face earns one W0003 and its formulas set as their glyph text, and
every out-of-scope construct earns a code naming it while its text content
survives — never its markup (`Ir.floorInk_mem`). -/
def mathChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let load (name : String) : IO Font.Font := do
    match Font.parse (← IO.FS.readBinFile (testFonts ++ "/" ++ name)) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"math: {name} unparsable: {e}")
  let serif ← load "SourceSerifPro-Regular.otf"
  let fira ← load "FiraMath-Regular.otf"
  -- The MATH table parses to the face's own constants (read independently
  -- with a struct-unpacking script against the OpenType spec offsets).
  t "text faces carry no MATH table" serif.math.isNone
  t "fira math constants" (fira.math == some {
    scales := { script := 72, scriptscript := 58 }
    axisHeight := 280
    accentBaseHeight := 527
    subscriptShiftDown := 350
    superscriptShiftUp := 400
    superscriptShiftUpCramped := 270
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
  -- MathVariants: the vertical size variants a delimiter grows through,
  -- checked against an independent struct-unpacking of the same face.
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
  -- Glyph vertical ink extents from the outline: the sum sign reaches well
  -- below the baseline and above the x-height; a period hugs the baseline.
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
  let mfs : Font.FontSet := {
    fonts := #[serif, fira]
    index := allSlots
    math := some 1 }
  let geom : Layout.Geom := {}
  let base := geom.fontSize
  -- The engine sets the math face at the size that matches its x-height to
  -- the surrounding face's (`Math.mathSize`); every width below recomputes
  -- at that size from the font's own tables.
  let mbase : Dim.Sp := (Math.mathSize base.toNat serif.xHeightOptical
    serif.unitsPerEm fira.xHeightOptical fira.unitsPerEm : Nat)
  -- Optical agreement over the shipped pair, in sp: unscaled the two
  -- x-heights disagree (the mismatch the scaling exists to remove); at
  -- `mathSize` they agree to the division quantum — `mathSize_matches` and
  -- `body_xheight_le_mathSize_next`, witnessed on real faces.
  let bodyXh := (serif.xHeightOptical : Int) * base / serif.unitsPerEm
  let mathXhAt (sz : Dim.Sp) := (fira.xHeightOptical : Int) * sz / fira.unitsPerEm
  t "x-heights disagree before scaling" (mathXhAt base != bodyXh)
  t "x-heights agree after scaling, within one sp"
    (mathXhAt mbase ≤ bodyXh && bodyXh ≤ mathXhAt mbase + 1)
  let upem : Int := fira.unitsPerEm
  let adv (size : Dim.Sp) (c : Char) : Dim.Sp := (fira.advance c : Int) * size / upem
  let mu (size : Dim.Sp) (n : Int) : Dim.Sp := size * n / 18
  let konst (size : Dim.Sp) (v : Int) : Dim.Sp := v * size / upem
  let scriptSize := mbase * 72 / 100
  let ssSize := mbase * 58 / 100
  let lineOf (src : String) : Layout.LineOut :=
    let (d, _) := Elab.run "t" src
    (((layoutOf mfs d geom).pages.flatMap (·.lines))[0]?).getD default
  let widthOf (src : String) : Dim.Sp := (lineOf src).setWidth
  -- A box is a box: the advance equals the sum of what it contains plus
  -- the spacing the table gives, in sp, recomputed from the font alone.
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
  let supRuns (src : String) : Array (Dim.Sp × Dim.Sp) :=
    (lineOf src).segs.filterMap fun s => match s with
      | .run _ _ _ _ glyphs sz _ raise _ _ =>
        if raise != 0 && !glyphs.isEmpty then some (sz, raise) else none
      | _ => none
  t "superscript raise is superscriptShiftUp at the base size"
    (supRuns "$x^2$" == #[(scriptSize, konst mbase 400)])
  t "subscript drop is subscriptShiftDown"
    (supRuns "$x_i$" == #[(scriptSize, -konst mbase 350)])
  -- Nested scripts: scriptscript size, shifts accumulating, the inner one
  -- scaled at its own base (the script size), cramped nowhere here.
  t "nested superscript reaches scriptscript and stacks its shifts"
    (supRuns "$x^{y^z}$" ==
      #[(scriptSize, konst mbase 400),
        (ssSize, konst mbase 400 + konst scriptSize 400)])
  -- Script styles suppress the conditional spacing: the + inside the
  -- superscript gets no medium space.
  t "no medium space inside a script"
    (widthOf "$x^{a+b}$" ==
      adv mbase '𝑥' + adv scriptSize '𝑎' + adv scriptSize '+' +
        adv scriptSize '𝑏' + konst mbase 41)
  -- Both scripts stack at one position: the atom advances by the wider.
  t "sup and sub stack, advancing by the wider"
    (widthOf "$x^a_b$" ==
      adv mbase '𝑥' + max (adv scriptSize '𝑎') (adv scriptSize '𝑏') + konst mbase 41)
  -- Variables italic, digits and function names upright (ISO 80000-2 §7,
  -- TeXbook ch. 18): x maps to U+1D465, sin and 2 stay ASCII.
  let glyphChars (src : String) : Array Char :=
    (lineOf src).segs.flatMap fun s => match s with
      | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.map (·.2.1)
      | _ => #[]
  t "variables italic, functions and digits upright"
    (glyphChars "$\\sin 2x$" == #['s', 'i', 'n', '2', '𝑥'])
  t "sin binds with a thin space"
    (widthOf "$\\sin x$" ==
      adv mbase 's' + adv mbase 'i' + adv mbase 'n' + mu mbase 3 + adv mbase '𝑥')
  -- Nothing is silently dropped: a scalar the math face lacks warns,
  -- naming the face.
  let bDoc : Ir.Doc := { body := #[.para #[.formula false "₿"
    (.cons (.atom .ord (.sym '₿') .nil .nil false) .nil)]] }
  t "a glyph the math face lacks warns E0405 naming it"
    (((layoutOf mfs bDoc geom).diags.filter (·.code == "E0405")).map (·.message)
      == #["'Fira Math' has no glyph for '₿' (U+20BF); dropped"])
  -- The chain, extended to math scalars: the census walk carries a
  -- formula's scalars to the driver's precompute, and a scalar the math
  -- face lacks that the precomputed chain covers sets from that face,
  -- named W0009 — never dropped.
  t "docScalars carries a formula's math scalars"
    ((Layout.docScalars (Elab.run "t" "$x$").1).contains '𝑥')
  let cfs : Font.FontSet := { mfs with fallback := #[('₿', 0)] }
  let cOut := layoutOf cfs bDoc geom
  t "a math scalar the chain covers sets from the fallback face, named W0009"
    ((cOut.diags.filter (·.code == "E0405")).isEmpty &&
      (cOut.diags.filter (·.code == "W0009")).map (·.message) ==
        #["'Fira Math' has no glyph for '₿' (U+20BF); set from 'Source Serif Pro'"] &&
      ((cOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 0 _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == '₿')
        | _ => false))
  -- No math face: one W0003 for the document, formulas set as their floor —
  -- the glyph text the parse produced, never the source, so the missing
  -- face costs the typesetting and not the mathematics.
  let bare : Font.FontSet := { fonts := #[serif], index := allSlots }
  let (nd, _) := Elab.run "t" "$x^2$ and $y$"
  let nOut := layoutOf bare nd geom
  t "no math face warns W0003 once" ((nOut.diags.filter (·.code == "W0003")).size == 1)
  t "no math face sets the formula's glyph text, not its source"
    (let chars := (nOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.flatMap fun s =>
       match s with
       | .run _ _ _ _ glyphs _ _ _ _ _ => glyphs.map (·.2.1)
       | _ => #[]
     !chars.contains '^' && !chars.contains '\\' && chars.contains '2')
  -- Elaboration shapes: display math is its own centred block; \(..\) is
  -- inline; equation* renders; align and \frac stay warned source.
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
    ((Elab.run "t" "\\begin{equation*}x\\end{equation*}").1.body ==
      #[.center #[.para #[.formula true "x" (.cons (.atom .ord (.sym '𝑥') .nil .nil false) .nil)]]])
  -- A parsed formula's scalars are content by the parser's own decision, so
  -- `\backslash` and `\{` ship their glyphs: that is the author asking for
  -- the character, not markup leaking. The distinction is provenance, not
  -- the character — which is why `markupChars` governs salvage from a
  -- source string and `formulaFloor` runs no filter, and why the corpus ink
  -- watch is per character (`inkMarkupExempt`) rather than per fixture.
  t "a formula asking for a backslash or a brace ships the glyph"
    (warnCodes "$\\backslash + \\{x\\}$" == [] &&
      (glyphChars "$\\backslash$").contains '\\' &&
      (glyphChars "$\\{x\\}$").contains '{')
  -- The style-neutral wrappers lose nothing inside \text, so they say
  -- nothing: a degraded code firing over a no-op would fail --werror for
  -- free and dilute the one meaning W0385 carries.
  t "an upright wrapper inside \\text names no loss"
    (warnCodes "$\\text{\\textrm{plain} word}$" == [] &&
      warnCodes "$\\text{\\mbox{boxed} word}$" == [] &&
      glyphChars "$\\text{\\textrm{plain} word}$" ==
        glyphChars "$\\text{plain word}$")
  -- What still is not modelled keeps its text content and its name.
  t "an out-of-scope construct degrades to its content and warns by name"
    (warnCodes "$\\overset{?}{=}$" == ["W0012"] &&
      ((Elab.run "t" "$\\overset{?}{=}$").1.body.any fun b => match b with
        | .para xs => xs.any fun x => match x with
          | .math false _ => true
          | _ => false
        | _ => false))
  -- LaTeX's text-style commands inside math resolve to the math alphabets
  -- they mean, so a formula wrapped in one renders instead of degrading:
  -- `\textbf{x}` is an upright bold roman x, which is `\mathbf{x}`.
  t "the text-style commands render as their alphabets, no W0012"
    (warnCodes "$\\textbf{v} + \\textit{w} + \\texttt{m} + \\textsf{s}$" == [] &&
      glyphChars "$\\textbf{v}$" == #['𝐯'] &&
      glyphChars "$\\textit{w}$" == glyphChars "$\\mathit{w}$")
  -- A colour inside math: the mathematics renders, the colour is named as
  -- lost (W0385) because the math list carries no colour to put it in.
  t "a colour inside math keeps its content and names the colour"
    (warnCodes "$\\textcolor{indigo}{x}$" == ["W0385"] &&
      glyphChars "$\\textcolor{indigo}{x}$" == glyphChars "$x$")
  t "a colour wrapping a styled operator renders both"
    (warnCodes "$\\textcolor{indigo}{\\textbf{\\sum_z}}$" == ["W0385"] &&
      (glyphChars "$\\textcolor{indigo}{\\textbf{\\sum_z}}$").contains '∑')
  -- A group inside \text is grouping, a known symbol contributes its
  -- scalar, and a style command contributes its letters with the styling
  -- named as lost — none of the three degrades the formula any more.
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
  -- An alignment body carries the same coverage: this is the shape a talk's
  -- coloured, styled align rows take, and it used to degrade whole.
  t "a coloured styled alignment renders as a grid, never as source"
    (let src := "\\begin{align*} &P(A) \\\\ &= \
\\textcolor{indigo}{\\textbf{\\sum_z}} P(B) \\end{align*}"
     warnCodes src == ["W0385"] &&
       ((Elab.run "t" src).1.body.any fun b => match b with
         | .center xs => xs.any fun bb => match bb with
           | .para ys => ys.any fun x => match x with
             | .formula _ _ _ => true
             | _ => false
           | _ => false
         | _ => false))
  -- Literal Greek in math is unicode-math's second spelling of the control
  -- word (math-style=TeX): the two spellings elaborate to one atom list
  -- (the formula's source field alone differs), and the shipped glyph is
  -- the Mathematical Italic scalar from the math face, never the body-face
  -- U+03xx letter (`greek_literal_agree`).
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
  -- Accents: TeXbook Appendix G rule 12 over MathTopAccentAttachment,
  -- pinned in sp over Layout's own output.
  let runXOf (src : String) (pick : Array (Nat × Char × Dim.Sp) → Bool) : Option Dim.Sp := Id.run do
    let l := lineOf src
    let mut x : Dim.Sp := 0
    for s in l.segs do
      match s with
      | .run _ _ _ w glyphs _ _ _ _ _ =>
        if pick glyphs then return some x
        x := x + w
      | .gap w _ => x := x + w
      | .rule w _ _ _ => x := x + w
      | .image _ w _ => x := x + w
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
        | .rule _ _ _ _ => true
        | _ => false).size == 1)
  t "an accented atom still takes its script"
    (warnCodes "$\\hat{x}^2$" == [] && warnCodes "$e^{\\hat{H}}$" == [])
  -- Math alphabets: one remap per letter (Math.MathAlphabet.apply), the
  -- Letterlike holes individually — \mathbb{R} is ℝ, never tofu at
  -- U+1D549 — and the classes projection untouched
  -- (remapList_classes_id), so spacing survives the remap.
  t "mathbb takes the Letterlike hole: R is ℝ"
    (glyphChars "$\\mathbb{R}$" == #['ℝ'] && warnCodes "$\\mathbb{R}$" == [])
  t "mathrm recovers the upright letters"
    (glyphChars "$\\mathrm{Err}$" == #['E', 'r', 'r'])
  t "mathbf keeps the spacing classes: x+y bolds with its medium spaces"
    (widthOf "$\\mathbf{x+y}$" ==
      adv mbase '𝐱' + mu mbase 4 + adv mbase '+' + mu mbase 4 + adv mbase '𝐲')
  t "boldsymbol bolds a Greek variable italic"
    (glyphChars "$\\boldsymbol{\\beta}$" == #['𝜷'])
  -- The corpus math face's cmap, per mapped scalar: the alphabets it
  -- covers render from it; the ones it lacks take the diagnosed fallback
  -- path (per-scalar chain, N0018 synthesis where the chain is empty).
  t "fira math covers the bb, bf, bfit, tt, it, and rm letter alphabets"
    ([Math.MathAlphabet.bb, .bf, .bfit, .tt, .it, .rm].all fun a =>
      Math.latinLetters.all fun c => (fira.gid (a.apply c)).isSome)
  t "fira math lacks cal, frak, and sf letters (all but ℊ): the fallback path"
    (([Math.MathAlphabet.cal, .frak, .sf].all fun a =>
      Math.latinLetters.all fun c =>
        (fira.gid (a.apply c)).isNone || a.apply c == '\u210A'))
  -- A construction stands as a script's argument: the pending chain.
  t "a word is a script's argument"
    (warnCodes "$V^\\text{null}$" == [] &&
      glyphChars "$V^\\text{null}$" == #['𝑉', 'n', 'u', 'l', 'l'])
  t "a fraction is a script's argument"
    (warnCodes "$2^\\frac{1}{2}$" == [])
  t "an alphabet is a script's argument"
    (glyphChars "$x^\\mathbb{R}$" == #['𝑥', 'ℝ'])
  t "ensuremath is transparent in math"
    (glyphChars "$\\ensuremath{x}$" == #['𝑥'])
  -- \define expansion inside math: the hook where MathParse meets the
  -- elaborator's macro table. Arguments bind already expanded (the walk
  -- runs right to left), matching takeArgs' text-mode order; a definition
  -- sees only definitions before it, so a self-reference stays unexpanded
  -- and the formula degrades with its name — the same rule that bounds
  -- the expansion (expandMathList's measure).
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
  -- The diagnosed synthesis: an alphabet scalar no face covers renders as
  -- its base letter — bold/italic from the text face where that is the
  -- alphabet's essence, the plain letter for the shape alphabets — and
  -- N0018 names the styling difference. Never dropped: E0405 stays for
  -- scalars with no stand-in.
  let calOut := layoutOf mfs (Elab.run "t" "$\\mathcal{L}$").1 geom
  t "an uncovered calligraphic letter sets plain, named N0018"
    ((calOut.diags.filter (·.code == "E0405")).isEmpty &&
      (calOut.diags.filter (·.code == "N0018")).map (·.message) ==
        #["'Fira Math' has no calligraphic 'L' (U+2112); the plain letter stands in"] &&
      glyphChars "$\\mathcal{L}$" == #['L'])
  t "a covered alphabet stays silent"
    ((layoutOf mfs (Elab.run "t" "$\\mathbb{R}$").1 geom).diags.all
      (·.code != "N0018"))
  let noBoldFira : Font.Font := { fira with
    cmap := fira.cmap.filter fun r => !(r.1.toNat ≤ 0x1D400 && 0x1D400 ≤ r.2.1.toNat) }
  let noBoldSet : Font.FontSet := { mfs with fonts := #[serif, noBoldFira] }
  let bfOut := layoutOf noBoldSet (Elab.run "t" "$\\mathbf{A}$").1 geom
  t "a bold letter the math face lacks synthesizes from the text face"
    ((bfOut.diags.filter (·.code == "N0018")).map (·.message) ==
      #["'Fira Math' has no bold 'A' (U+1D400); set bold from 'Source Serif Pro'"] &&
      ((bfOut.pages.flatMap (·.lines)).flatMap (·.segs) |>.any fun s => match s with
        | .run 0 _ _ _ glyphs _ _ _ _ _ => glyphs.any (·.2.1 == 'A')
        | _ => false))
  -- The alignment family renders as grids now; the numbered forms warn
  -- W0014 (numbers are owed, the mathematics is not), a ragged row is
  -- W0013 and still renders padded.
  t "align renders as a grid; its numbers warn W0015"
    (warnCodes "\\begin{align}a &= b\\end{align}" == ["W0015"] &&
      ((Elab.run "t" "\\begin{align}a &= b\\end{align}").1.body.any fun b => match b with
        | .center bs => bs.any fun b2 => match b2 with
          | .para xs => xs.any fun x => match x with
            | .formula true _ _ => true
            | _ => false
          | _ => false
        | _ => false))
  t "a ragged align row is W0014 and still renders"
    (warnCodes "\\begin{align*}a &= b \\\\ z\\end{align*}" == ["W0014"])
  -- Per-glyph positions: (char, gid, x, raise, advance) over every line.
  let glyphInfo (src : String) : Array (Char × Nat × Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Char × Nat × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for page in (layoutOf mfs d geom).pages do
      for l in page.lines.filter (!·.furniture) do
        let mut x := l.x
        for s in l.segs do
          match s with
          | .gap w _ => x := x + w
          | .rule w _ _ _ => x := x + w
          | .image _ w _ => x := x + w
          | .run _ _ _ w glyphs sz _ raise _ _ =>
            let mut gx := x
            for (g, c, _) in glyphs do
              let a := (fira.widths[g]?.getD 0 : Int) * sz / upem
              out := out.push (c, g, gx, raise, a)
              gx := gx + a
            x := x + w
    return out
  let rules (src : String) : Array (Dim.Sp × Dim.Sp × Dim.Sp) := Id.run do
    let (d, _) := Elab.run "t" src
    let mut out : Array (Dim.Sp × Dim.Sp × Dim.Sp) := #[]
    for page in (layoutOf mfs d geom).pages do
      for l in page.lines.filter (!·.furniture) do
        for s in l.segs do
          if let .rule w thickness raise _ := s then
            out := out.push (w, thickness, raise)
    return out
  -- Fractions: parts at their styles' sizes, numerator raised and
  -- denominator dropped, the bar fractionRuleThickness thick, and the
  -- advance the wider part plus \nulldelimiterspace each side.
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
  -- The radical: the surd's ink top meets the overbar, radicand under it.
  t "sqrt draws surd and overbar over the radicand"
    ((glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '\u221A') &&
      (rules "$\\sqrt{x}$").size == 1 &&
      (glyphInfo "$\\sqrt{x}$").any (fun g => g.1 == '𝑥'))
  t "a root index sets small before the surd"
    ((glyphInfo "$\\sqrt[3]{x}$").any (fun g => g.1 == '3' && g.2.2.2.1 > 0))
  -- \left...\right grows through the variant ladder: around a tall display
  -- fraction the paren is no longer the base glyph (gid 9 in Fira Math).
  t "left paren grows over a display fraction"
    ((glyphInfo "\\[\\left(\\frac{a}{b}\\right)\\]").any fun g =>
      g.1 == '(' && g.2.1 != 9)
  t "an inline paren around a scalar stays the base glyph"
    ((glyphInfo "$\\left(a\\right)$").any fun g => g.1 == '(' && g.2.1 == 9)
  -- Big operators: display style takes the face's display-size variant
  -- (gid 1584) with limits above and below, centred; text style keeps the
  -- base glyph (753) and its scripts beside.
  t "display sum takes the display variant"
    ((glyphInfo "\\[\\sum_{i=1}^{n} i\\]").any fun g => g.1 == '\u2211' && g.2.1 == 1584)
  t "inline sum keeps the text-size glyph and scripts beside"
    ((glyphInfo "$\\sum_{i=1}^{n} i$").any fun g => g.1 == '\u2211' && g.2.1 == 753)
  t "display limits centre on the operator within a scaled point"
    (Id.run do
      let gs := glyphInfo "\\[\\sum_{j=2}^{m} j\\]"
      let some (_, _, sx, _, sa) := gs.find? (fun g => g.1 == '\u2211') | return false
      let some (_, _, mx, mraise, ma) := gs.find? (fun g => g.1 == '𝑚') | return false
      return mraise > 0 && ((2 * mx + ma) - (2 * sx + sa)).natAbs ≤ 2)
  t "the lower limit sits below the operator"
    ((glyphInfo "\\[\\sum_{j=2}^{m} j\\]").any fun g => g.1 == '2' && g.2.2.2.1 < 0)
  -- Alignment points align: the relation opening every even align cell
  -- sits at one x for every row, and the right-aligned column pushes a
  -- short cell right by exactly the width difference.
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
      return ((2 * bx + ba) - (2 * ax + w1)).natAbs ≤ 2)
  -- Primes and \text.
  t "a prime is a raised superscript prime"
    ((glyphInfo "$x'$").any fun g => g.1 == '\u2032' && g.2.2.2.1 == konst mbase 400)
  t "text inside math keeps its letters and spaces upright"
    (glyphChars "$\\text{if }x$" == #['i', 'f', ' ', '𝑥'] ||
      glyphChars "$\\text{if }x$" == #['i', 'f', '𝑥'])
  t "operatorname binds like a named function"
    (widthOf "$\\operatorname{foo} x$" ==
      adv mbase 'f' + adv mbase 'o' + adv mbase 'o' + mu mbase 3 + adv mbase '𝑥')
  t "setmathfont fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\setmathfont{Fira Math}" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")
  t "fonts math key fills the math slot"
    ((Elab.run "t" ("\\documentclass{article}\\fonts{ math = \"Fira Math\" }" ++
      "\\begin{document}x\\end{document}")).1.fonts.math == some "Fira Math")



/-! ## The slot matrix: the driver end to end, judged on its artifacts

`slotLossChecks` pins the decision's conditions over sets built by hand.
This block runs the path that ships — the `leantex` binary — over
documents that differ only in the dimension a row names, and judges each
report against what the artifact itself says about the face a run is set
in: the PDF's content stream and descriptor, or the page's slot stack and
the file its `@font-face` names. The expected answer is never the
engine's rule restated: it is the artifact's face, and whether the
document declared the slot. -/

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

/-- One row: a class, the `\fonts` keys it declares (none: the
`LEANTEX_FONT` override instead of a declaration), the pitch of every
family it names, the artifacts it builds, and the one slot its one
construct sets. -/
structure SlotRow where
  cls : String
  decl : List String
  fixed : Bool
  art : SlotArt
  slot : String
  deriving Repr, Inhabited

/-- The family a row names for a key: the monospace face for every key of
a fixed-pitch row, else a proportional design per key — Fira Sans for
mono, a proportional family a document may declare for its typewriter
slot, and has then chosen. -/
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

/-- A row's document: one paragraph of plain words carrying the row's one
construct, a `\texttt` or a `\textsf` run spelling `zqx` — a word nothing
else on the page spells, so the face that sets it can be read back. -/
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

/-- A font file's own `post.isFixedPitch`, read through the OpenType table
directory — the uint32 at offset 12 of `post` (OpenType spec, the `post`
table header) — with no engine code between the bytes and the answer, so
the matrix's pitch oracle does not share the reader it judges. `none`: no
readable `post` table. -/
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

/-- What a written PDF sets in each face resource: the resource's name,
the text its runs spell through that face's own `/ToUnicode`, the `/Flags`
its descriptor declares, and the pitch the embedded program's own `post`
table declares (`postIsFixedPitch`). The artifact tier's tokenizer and CMap
reading, plus the one fact that tier does not keep: which face a run is
set in. -/
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

/-- The file a page sets a slot in: walk the slot's `--font-<slot>` stack
— the last declaration, which is the one the cascade keeps — to the first
family that has an `@font-face` rule at the regular weight and upright
style, as the browser's per-family walk does (CSS Fonts 4 §5.2: a
synthetic family with no rule names no face, and the walk moves on), and
return that rule's `src` file. `none`: no family of the stack has a rule,
so the page ships no face for the slot. -/
def htmlSlotFile (html slot : String) : Option String := do
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

/-- One row's outcome: the driver's exit code and log, the W0390 lines it
printed, and what the artifact says — whether any artifact carrying a
face sets the slot's run in a face that is not of the slot's kind, whether
that face is the running text's own, and whether the PDF's descriptor
declares the pitch its embedded program does. -/
structure SlotOutcome where
  exit : UInt32
  log : String
  reports : Array String
  lost : Bool
  textFace : Bool
  flagsAgree : Bool
  oracle : String

/-- Build one row with the driver and read its artifacts back. The driver
runs in an environment of its own: a private cache, an empty home, and a
`PATH` holding nothing, so no TeX tree, user font directory or tool on
this host reaches the scan — every family a row names is in the copied
corpus directory beside the document. -/
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
    match htmlSlotFile html r.slot, htmlSlotFile html "body" with
    | some runFile, some textFile =>
      let same := runFile == textFile
      textFace := same
      let pitch := (postIsFixedPitch (← IO.FS.readBinFile (out / runFile))).getD false
      lost := if r.slot == "mono" then !pitch else same
      oracle := s!"html: run in {runFile} (fixed {pitch}), text in {textFile}"
    | _, _ => oracle := "html: the page ships no face for the slot or the text"
  return { exit := p.exitCode, log := p.stdout ++ p.stderr, reports, lost, textFace,
           flagsAgree, oracle }

/-- **W0390 fires exactly when an artifact sets a slot's runs in a face
not of the slot's kind, and the document declared no family for the
slot.** For mono the kind is fixed pitch, read from the face program the
artifact carries — the PDF's embedded program, the page's shipped file —
through its `post` table directly (`postIsFixedPitch`), never through the
engine's classifier, which is what the report rests on; and every PDF's
descriptor must declare the pitch its own program does. For sans the kind
is contrast with the running text — no face field says "is a sans design"
— so the loss is the run set in the text's own face. An artifact carrying
no face (a page under a declared `css =`) sets no run in a resolved face
and loses nothing. -/
def slotMatrixChecks (ref : IO.Ref (List String)) : IO Unit := do
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
  -- One run first, so every parallel run after it reads a warm probe cache
  -- instead of each probing the host's font tree for itself.
  let rows := slotRows
  let warm ← slotRunRow bin dir cache rows.size (rows[0]?.getD default)
  t s!"slot matrix: the warm-up run builds: {warm.log}" (warm.exit == 0)
  let mut outcomes : Array (Option (Except IO.Error SlotOutcome)) := Array.replicate rows.size none
  -- Sixteen workers: measured on a 192-core host, the matrix took 3.4 s at
  -- 16, 4.2 s at 32, 5.7 s at 64 and 5.0 s at 4.
  let width := 16
  -- Workers over a static partition — worker `j` builds rows `j`,
  -- `j + width`, … — so no state is shared and a slow row delays only its
  -- own worker, not a whole batch.
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
      t s!"slot matrix {r.label}: the build succeeds: {o.log}" (o.exit == 0)
      unless o.flagsAgree do flagDisagree := flagDisagree.push s!"{r.label} ({o.oracle})"
      let declared := r.decl.contains r.slot
      let want := !declared && o.lost
      if want then expectedReports := expectedReports + 1
      else expectedSilent := expectedSilent + 1
      t s!"slot matrix {r.label}: {if want then "reported" else "silent"} ({o.oracle}); \
got {o.reports.size} W0390" (o.reports.size == (if want then 1 else 0))
      -- What the report says is the artifact's answer too: which face served
      -- the run, and, where the page beside the PDF carries none, the PDF.
      if want then
        let word := if r.slot == "mono" then SlotLoss.monoWord else SlotLoss.sansWord
        let served := if o.textFace then SlotLoss.Served.bodyFace else .bodyFamily
        let only := if r.art == .pdfHtmlOwn then some (SlotLoss.artifactWord .pdf) else none
        let expect := Render.porcelainDiag
          (DriverDiag.slotCollapsed word.key word.runs served.words word.note only)
        t s!"slot matrix {r.label}: the report says {served.words}{if only.isSome then " in the PDF" else ""}: \
{o.reports}" (o.reports.map (·.trimAscii.toString) == #[expect])
    | some (.error e) => t s!"slot matrix {r.label}: the row runs: {e}" false
    | none => t s!"slot matrix {r.label}: the row ran" false
  -- Non-vacuity: the matrix reaches both answers, and the deck setup the
  -- defect was found in is one of the rows whose artifact says "lost".
  t s!"slot matrix: some rows are losses ({expectedReports})" (0 < expectedReports)
  t s!"slot matrix: some rows are not ({expectedSilent})" (0 < expectedSilent)
  t s!"slot matrix: every PDF declares the run face's pitch its embedded program does: \
{flagDisagree}" flagDisagree.isEmpty
  IO.FS.removeDirAll dir

/-- **A family slot set in a face not of its kind, and the report that
names it.** The mono-slot defect: a `\texttt`, `\url` or verbatim run in a
document with no `\fonts{ mono = ... }` sets in body prose, and said
nothing. Measured from the bytes on a synthetic document carrying all three
constructs against the shipped corpus fonts — with `mono` declared the PDF
embeds two faces, without it one — and both builds were silent.

Three groups, each falsifying one thing this could get wrong. The census:
a document that never asks for the slot is never told about it, and the
descent is the fold's, so a `\texttt` inside a footnote or a running head
counts. The decision, over sets built here: its four conditions (a face
carried, the slot used, no family declared, the face not of the slot's
kind) are each load-bearing, the face answers where the index says the
opposite in both directions — a fixed-pitch body the index calls
collapsed, and a deck's serif body family the index calls the slot's own —
the body slot is the reference rather than a subject, and the message says
what served the slot and, in a build where only the PDF carries the face,
that the PDF lost. The matrix (`slotMatrixChecks`): the same invariant
through the driver binary, judged on each artifact's own face.

Hermetic and synthetic throughout: the faces are ones the corpus ships,
every index here is built here, and the driver runs read the shipped faces
from a copy of the corpus directory under a private cache. Invented
content, `example.org` links. -/
def slotLossChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let doc (body : String) : Ir.Doc := (elabStr ("\\documentclass{article}\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}")).1
  -- The census: which slots a document's own content asks for.
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
  -- A link whose text carries no typewriter style asks for no mono slot: the
  -- census reads the style the IR carries, never the construct that made it.
  -- That is why honouring `\urlstyle{same}` where `\url` elaborates — no
  -- family style for `same` — is all it takes for a URL in the running face
  -- to stop counting as a lost mono run, with no change here.
  t "slot census: a link with no typewriter style asks for no mono slot"
    (!(SlotLoss.slotsUsed (doc "A link \\href{https://example.org/a}{here}.")).contains 2)
  -- **Registered debt: the census counts declarations, not shipped runs.**
  -- A style-s font template is a furniture region, so a `\style` naming
  -- `\ttfamily` counts as a mono use even in a document with no element of
  -- that kind, and the report names a loss no page shows (measured: one
  -- W0390 on such a document). The answer belongs to the layout, which
  -- resolves each run-s slot as it sets it (`Layout.Out`), and this census
  -- cannot see provenance: `Ir.furnitureInlines` hands over runs, not the
  -- elements they came from. The row fails in both directions — when the
  -- over-count grows past what is registered, and when the fix lands and
  -- the registered answer stops holding, which is the signal to delete it.
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
  -- The descent is the fold's: a construct nested where a hand-rolled walk
  -- would have stopped still counts. An image inside a footnote once
  -- shipped a silent placeholder for exactly this reason.
  t "slot census: the fold reaches a footnote body"
    ((SlotLoss.slotsUsed (doc "Text\\footnote{A \\texttt{note} run.}")).contains 2)
  t "slot census: the fold reaches a running head"
    ((SlotLoss.slotsUsed ((elabStr ("\\documentclass{article}\n" ++
      "\\runninghead{A \\texttt{head} run}\n\\begin{document}\nx\n\\end{document}")).1)).contains 2)
  -- The resolved sets. `collapsed` is the no-declaration default: one face
  -- serves every slot. `declared` is a distinct mono in slot 2.
  let load (name : String) : IO (Option Font.Font) := do
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
  -- What the build carries: a PDF always carries its faces; an HTML-only
  -- page under a declared stylesheet carries none.
  let pdf := SlotLoss.carries #[.pdf] .embedded
  let bare := SlotLoss.carries #[.html, .md] .none
  -- The report, and each of its conditions.
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
  -- **The face, not the index — in both directions.** A monospace body
  -- sets typewriter runs in fixed pitch whichever slot they came through,
  -- so the index's "collapsed" is no loss. And a deck sets its text in the
  -- sans family while an undeclared mono slot falls to the body family —
  -- a face of its own, by the index, and a proportional serif all the
  -- same: that deck was silent, and the index was why.
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
  -- The sans slot claims no pitch: no flag in a face records "is a sans
  -- design", so the loss reported is the missing contrast, and a
  -- fixed-pitch body does not exempt it.
  t "slot loss: the sans slot is reported on a fixed-pitch body too"
    ((SlotLoss.losses {} monoBody #[1] pdf).map (·.key) == #["sans"])
  -- **What served the slot, said so.** The body face where the slot sits on
  -- the text's own face; the body family where the text is set in another.
  t "slot loss: a slot on the text's own face was served by the body face"
    (SlotLoss.served collapsed 2 == .bodyFace)
  t "slot loss: a deck's mono slot was served by the body family"
    (SlotLoss.served deck 2 == .bodyFamily)
  t "slot loss: the deck's report says the body family served the slot"
    (((SlotLoss.diags deckSpec deck usesMono pdf).map (·.message)) ==
      #["nothing declares a 'mono' family; typewriter runs set in the body family, \
which is not fixed-pitch"])
  -- **The carrying gate is load-bearing.** One document, one index, two
  -- values of the gate's own condition: an artifact carrying a face
  -- reports the lost slot, one carrying none reports nothing. An HTML-only
  -- page under a declared `css =` is the second, and it is what the site
  -- port builds.
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
  -- **A mixed build names the artifact that lost.** A PDF beside a page
  -- under its own stylesheet: the page sets code from its own monospace
  -- stack, so the loss is the PDF's alone and the report says so; where
  -- every emitted artifact carries the face, the report holds of the build
  -- and names none.
  let mixed := SlotLoss.carries #[.pdf, .html] .none
  t "slot loss: a PDF beside an unfaced page is the one artifact named"
    (mixed.only == some "the PDF")
  t "slot loss: a build whose every artifact carries the face names none"
    ((SlotLoss.carries #[.pdf, .html, .md] .embedded).only == none && pdf.only == none)
  t "slot loss: the mixed build's report says the PDF lost"
    (((SlotLoss.diags {} collapsed usesMono mixed).map (·.message)) ==
      #["nothing declares a 'mono' family; in the PDF, typewriter runs set in the body face, \
which is not fixed-pitch"])
  -- The body slot is the reference, never a subject: no report names it,
  -- whatever is asked of it.
  t "slot loss: the body slot is never reported"
    ((SlotLoss.losses {} collapsed #[0, 1, 2] pdf).all (·.slot != 0))
  -- One loss per slot, not one per run: five mono sites and one sans site
  -- are two diagnostics.
  let manyRuns := doc ("A \\texttt{one} run, a \\texttt{two} run, a \\texttt{three} run, " ++
    "\\url{https://example.org/a}, and \\textsf{sans}.\n" ++
    "\\begin{verbatim}\nliteral\n\\end{verbatim}")
  t "slot loss: one report per lost slot, not one per run"
    ((SlotLoss.diags {} collapsed manyRuns pdf).size == 2)
  -- The diagnostic itself: the code, and the subject the census counts on.
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

  -- **A provisional index is not a document's loss.** A provisional
  -- assembly resolves slot 0 and skips the others, so its index has no
  -- entry past the body and every slot reads as collapsed. The report is
  -- reached only from `build`, which holds the settled set; this row keeps
  -- the difference visible, so a caller handing the provisional shape in
  -- would be handing in an index that answers about the driver's shortcut
  -- rather than about the document.
  let provisional : Font.FontSet := { fonts := #[body], index := #[((0, 400, false), 0)] }
  t "slot loss: a slot-0-only index would report every other slot, which only the settled set avoids"
    ((SlotLoss.losses {} provisional #[1, 2] pdf).size == 2)
  t "slot loss: the same document on a settled index reports only what it lost"
    ((SlotLoss.losses monoSpec declared #[1, 2] pdf).size == 1)
  slotMatrixChecks ref
