module

public import Tests.Support
import LeanTex.Core.Layout.Quality

public section

open LeanTex.Core

namespace Tests.PageBoxes

/-- An invented print card: a 3.5 by 2 in trim with a 1/8 in bleed, its boxes computed by
`\edef` from its lengths and assigned at shipout, as a LaTeX print document writes them. -/
private def card (extra body : String) : String :=
  "\\documentclass{article}\n\\usepackage{calc}\n" ++
    "\\newlength{\\tw}\\newlength{\\tht}\\newlength{\\bl}\\newlength{\\pw}\\newlength{\\ph}\n" ++
    "\\setlength{\\tw}{3.5truein}\\setlength{\\tht}{2truein}\\setlength{\\bl}{0.125truein}\n" ++
    "\\setlength{\\pw}{\\tw+2\\bl}\\setlength{\\ph}{\\tht+2\\bl}\n" ++
    "\\usepackage[paperwidth=3.75in,paperheight=2.25in,margin=0.3in]{geometry}\n" ++
    "\\makeatletter\n\\newcommand*{\\pb@bp}[1]{\\strip@pt\\dimexpr(#1)*7200/7227\\relax}\n" ++
    "\\edef\\pbtrim{\\pb@bp{\\bl} \\pb@bp{\\bl} \\pb@bp{\\bl+\\tw} \\pb@bp{\\bl+\\tht}}\n" ++
    "\\edef\\pbbleed{0 0 \\pb@bp{\\pw} \\pb@bp{\\ph}}\n" ++
    "\\edef\\pbattr{/TrimBox [\\pbtrim] /BleedBox [\\pbbleed]}\n\\makeatother\n" ++ extra ++
    "\\pagestyle{empty}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

private def hook : String := "\\AddToHook{shipout/before}{\\pdfvariable pageattr\\expandafter{\\pbattr}}\n"

/-- A shipout hook assigning the page attribute `attr` literally. -/
private def attrHook (attr : String) : String :=
  "\\AddToHook{shipout/before}{\\pdfvariable pageattr{" ++ attr ++ "}}\n"

private def codes (ds : Array Diag) (c : DiagCode) : Nat := (ds.filter (·.code == c.code)).size

/-- One elaborated document's diagnostics, its PDF with streams inflated, and its web page. -/
private def artifacts (oneFace : Font.FontSet) (src : String) :
    Ir.Doc × Array Diag × ByteArray × String :=
  let (doc, ds) := elabStr src
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf oneFace doc geom
  (doc, ds, pdfText (Pdf.write geom oneFace out.pages doc.info), (HtmlDoc.emit {} doc).1)

/-- An `\edef` text is expanded where it stands, from the definitions and lengths in force there as
TeX scopes them, or refused by name; never from a later or an out-of-scope value. -/
def edefChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let pageOf (pre body : String) : Array Diag × String :=
    let (_, ds, _, html) := artifacts oneFace (card pre body)
    (ds, html)
  let (_, text) := pageOf ""
    "\\makeatletter\\edef\\pa{\\the\\tw}\\edef\\pb{\\number\\dimexpr\\bl\\relax}\\edef\\pc{\\strip@pt\\tht}\\makeatother W \\pa; N \\pb; S \\pc"
  -- lualatex 1.24 prints W 252.94499pt; N 592035; S 144.54.
  t "the, number and strip@pt print a length as TeX reads and prints it"
    (hasStr text "W 252.94499pt; N 592035; S 144.54")
  let (_, redef) := pageOf "\\newcommand\\unit{Older}\\edef\\saved{\\unit}\\renewcommand\\unit{Newer}\n"
    "Saved \\saved."
  t "an edef keeps the meaning in force where it stands, not a later one"
    (hasStr redef "Saved Older." && !hasStr redef "Saved Newer.")
  let (fds, fwd) := pageOf "\\edef\\early{\\later}\\newcommand\\later{Later}\n" "Early \\early."
  t "an edef of a macro defined only after it is refused, not expanded from the later definition"
    (codes fds .W0357 == 1 && !hasStr fwd "Early Later.")
  let (_, grp) := pageOf "\\def\\inner{one}\n" "{\\edef\\inner{two}}\\edef\\outer{\\inner}Outer \\outer."
  t "a definition a group makes is gone when the group closes"
    (hasStr grp "Outer one." && !hasStr grp "Outer two.")
  let (_, lens) := pageOf "\\newlength{\\probe}\\setlength{\\probe}{1in}\n"
    ("{\\setlength{\\probe}{2in}}\\begin{minipage}{1in}\\setlength{\\probe}{3in}\\end{minipage}" ++
      "\\edef\\after{\\the\\probe}Probe \\after.")
  t "a length a group or an environment assigns is restored when it closes"
    (hasStr lens "Probe 72.26999pt.")
  let (_, gset) := pageOf "\\newlength{\\probe}\\setlength{\\probe}{1in}\n"
    "{\\global\\setlength{\\probe}{2in}}\\edef\\after{\\the\\probe}Probe \\after."
  t "a length a global setlength assigns keeps its value past the group"
    (hasStr gset "Probe 144.54pt.")
  let refusedAfter (pre body : String) : Bool :=
    codes (pageOf ("\\newlength{\\probe}\\newlength{\\other}\\setlength{\\probe}{1in}" ++
      "\\setlength{\\other}{4in}\n" ++ pre) (body ++ "\\edef\\after{\\the\\probe}x")).1 .W0357 == 1
  for (what, pre, body) in [
      ("register arithmetic", "", "{\\global\\advance\\probe by 1in}"),
      ("a measuring assignment", "\\settowidth{\\probe}{abc}\n", ""),
      ("a primitive assignment", "\\probe=2in\n", ""),
      ("a signed primitive assignment", "", "\\noindent\\probe-1in "),
      ("a register-to-register assignment", "", "\\noindent\\probe\\other "),
      ("an environment's code", "\\newenvironment{wide}{\\setlength{\\probe}{3in}}{}\n", "\\begin{wide}"),
      ("a macro the pass leaves to its use", "\\newcommand{\\grow}{\\probe=5in}\n", "\\grow{}")] do
    t s!"a length {what} sets is refused, never read stale" (refusedAfter pre (body ++
      (if body.startsWith "\\begin" then "\\edef\\inside{\\the\\probe}\\end{wide}" else "")))
  let (rds, _) := pageOf "" "\\begin{minipage}{1in}\\edef\\after{\\the\\textwidth}\\end{minipage}"
  let (zds, _) := pageOf "\\setlength{\\abovedisplayskip}{30pt}\n" "\\edef\\after{\\the\\abovedisplayskip}x"
  t "a length the document does not allocate is refused, its kernel resets unseen"
    (codes rds .W0357 == 1 && codes zds .W0357 == 1)
  let (_, reads) := pageOf
    ("\\newlength{\\probe}\\setlength{\\probe}{1in}\\edef\\one{\\the\\probe.}" ++
      "\\ifdim\\probe=1in \\fi\\edef\\two{\\the\\probe}\n")
    "One \\one; two \\two."
  t "a length read after the, number or a comparison keeps its value"
    (hasStr reads "One 72.26999pt.; two 72.26999pt.")
  let (_, kept) := pageOf
    ("\\protected\\def\\shield{X}\\edef\\held{\\shield}\\def\\shield{Y}\\edef\\shown{\\held}\n" ++
      "\\def\\late{P}\\edef\\put@{\\noexpand\\late}\\def\\late{Q}\\edef\\got{\\put@}\n")
    "Shown \\shown; got \\got."
  t "a protected definition and a control after noexpand stand in the text, for a later edef to expand"
    (hasStr kept "Shown Y; got Q.")
  let (ids, inline) := pageOf "\\newcommand\\wrap[1]{[#1]}\n"
    ("Text \\textbf{\\edef\\x{a}\\x} more\\footnote{\\edef\\y{\\wrap{b}}\\y}. " ++
      "Plain \\edef\\z{c}\\z{} here; \\edef\\today{Someday}\\today.")
  t "an edef inside a paragraph, a command or a note is used where it is called, the paragraph whole"
    (ids.all (·.severity != .error) && codes ids .W0357 == 0 &&
      hasStr inline "Text <strong>a</strong> more" && hasStr inline "[b]" &&
      hasStr inline "Plain c here; Someday.")
  -- Level k + 1 holds two groups of level k, so level 20 walks two million steps.
  let level (k : Nat) : String := "\\lv" ++ String.ofList [Char.ofNat (97 + k)]
  let doubling := String.join ((List.range 20).map fun k =>
    "\\def" ++ level (k + 1) ++ "{{" ++ level k ++ "}{" ++ level k ++ "}}")
  let (bds, _) := pageOf ("\\def" ++ level 0 ++ "{x}" ++ doubling ++ "\\edef\\big{" ++ level 20 ++ "}\n") "x"
  t "an expansion past the step cap is refused, its nested groups counted"
    (codes bds .W0357 == 1)
  let (_, pds, ppdf, _) := artifacts oneFace
    ("\\documentclass{article}\n\\newlength{\\pw}\\newlength{\\ph}\\setlength{\\pw}{270pt}" ++
      "\\setlength{\\ph}{162pt}\n\\usepackage[paperwidth=270pt,paperheight=162pt,margin=20pt]{geometry}\n" ++
      "\\makeatletter\\edef\\pbattr{/BleedBox [0 0 \\strip@pt\\dimexpr\\pw*7200/7227\\relax\\space" ++
      "\\strip@pt\\dimexpr\\ph*7200/7227\\relax]}\\makeatother\n" ++ hook ++
      "\\begin{document}\nx\n\\end{document}")
  t "a length reads its units as the paper does, so a box computed from it fits the medium"
    (bytesContain ppdf "/MediaBox [0 0 268.991 161.395]" &&
      bytesContain ppdf "/BleedBox [0 0 268.991 161.395]" && codes pds .W0442 == 0)
  let (cds, _) := pageOf
    "\\newcommand{\\pp}{\\pq}\\newcommand{\\pq}{\\pp}\\edef\\pr{\\pp}\n\\edef\\ps{\\csname x\\endcsname}\n" "x"
  t "an edef whose expansion meets a cycle, or a control outside the subset, stays refused"
    (codes cds .W0357 == 2 && cds.all (·.severity != .error))

/-- A shipout hook's page boxes are written exactly from `\edef` text, each assignment replacing
the attribute, a box past the medium clamped or dropped and named, any other entry named, and the
web page ships no print furniture. -/
def checks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  edefChecks ref oneFace
  let (doc, ds, pdf, _) := artifacts oneFace (card hook "\\noindent Placeholder")
  t "the edef chain and the page attribute read with no skip"
    (codes ds .W0357 == 0 && codes ds .W0104 == 0 && codes ds .W0443 == 0 &&
      ds.all (·.severity != .error))
  t "the boxes are the lengths in big points: a trim 1/8 in inside a 3.75 by 2.25 in medium"
    (bytesContain pdf "/MediaBox [0 0 270 162]" && bytesContain pdf "/TrimBox [9 9 261 153]" &&
      bytesContain pdf "/BleedBox [0 0 270 162]" && !bytesContain pdf "/ArtBox")
  t "the declared boxes stand on the page's declaration"
    (doc.page.boxes.map (·.kind.key) == #["TrimBox", "BleedBox"])
  let (_, wds, wpdf, _) := artifacts oneFace (card (attrHook "/TrimBox [9 9 300 153] /Rotate 90") "x")
  t "a box past the medium is written inside it and named for the PDF at its site; another attribute is named"
    (bytesContain wpdf "/TrimBox [9 9 270 153]" && codes wds .W0442 == 1 &&
      wds.any (fun d => d.code == DiagCode.W0442.code && d.output == some .pdf && d.span.isSome) &&
      codes wds .W0443 == 1 && !bytesContain wpdf "/Rotate")
  let (_, eds, _, _) := artifacts oneFace (card (attrHook "/BleedBox [0 0 270.001 162]") "x")
  t "a box a thousandth of a big point past the medium's spelling is named"
    (codes eds .W0442 == 1)
  let (_, zds, zpdf, _) := artifacts oneFace
    (card (attrHook "/TrimBox [300 300 400 400] /CropBox [0 0 0 0] /BleedBox [0 0 270 162]") "x")
  t "a box with no area inside the medium is not written, and named"
    (!bytesContain zpdf "/TrimBox" && !bytesContain zpdf "/CropBox" &&
      bytesContain zpdf "/BleedBox [0 0 270 162]" && codes zds .W0442 == 2)
  let (_, _, lpdf, _) := artifacts oneFace (card
    "\\AddToHook{shipout/before}{\\pdfpageattr{/CropBox [0 0 135 81]}}\n" "x")
  t "a literal page attribute writes its box"
    (bytesContain lpdf "/CropBox [0 0 135 81]")
  let (_, _, rpdf, _) := artifacts oneFace
    (card (attrHook "/TrimBox [9 9 261 153]" ++ attrHook "/BleedBox [0 0 270 162]") "x")
  let keepHook := "\\AddToHook{shipout/before}{\\pdfvariable pageattr\\expandafter" ++
    "{\\the\\pdfvariable pageattr /BleedBox [0 0 270 162]}}\n"
  let (_, kds, kpdf, _) := artifacts oneFace (card (attrHook "/TrimBox [9 9 261 153]" ++ keepHook) "x")
  let (_, uds2, updf2, _) := artifacts oneFace (card (attrHook "/TrimBox [9 9 261 153]" ++
    attrHook "\\the\\pdfvariable pageattr /BleedBox [0 0 270 162]") "x")
  t "a second assignment replaces the attribute, one expanding the attribute in force first keeps it, \
and one holding it unexpanded is named and replaces it"
    (!bytesContain rpdf "/TrimBox" && bytesContain rpdf "/BleedBox [0 0 270 162]" &&
      bytesContain kpdf "/TrimBox [9 9 261 153]" && bytesContain kpdf "/BleedBox [0 0 270 162]" &&
      codes kds .W0343 == 0 && codes uds2 .W0443 == 1 && !bytesContain updf2 "/TrimBox")
  let (_, nds, npdf, _) := artifacts oneFace (card (attrHook "/TrimBox [1.2.3 0 10 10] /BleedBox [0 0 270 162]") "x")
  t "a box whose numbers do not read is named, and the rest of the attribute written"
    (codes nds .W0443 == 1 && nds.all (·.severity != .error) && !bytesContain npdf "/TrimBox" &&
      bytesContain npdf "/BleedBox [0 0 270 162]")
  let (_, tds, tpdf, _) := artifacts oneFace (card "\\pdfvariable pageattr{/TrimBox [9 9 261 153]}\n" "x")
  t "a page attribute assigned outside a hook writes its box for every page"
    (bytesContain tpdf "/TrimBox [9 9 261 153]" && codes tds .W0301 == 0 &&
      tds.all (·.severity != .error))
  let (_, _, dpdf, _) := artifacts oneFace (card (attrHook "/TrimBox [9.5 10.25 260.125 152.5]") "x")
  t "a box's decimals read to the thousandth of a point and write back as spelled"
    (bytesContain dpdf "/TrimBox [9.5 10.25 260.125 152.5]")
  let (_, uds, updf, _) := artifacts oneFace (card (attrHook "/TrimBox [9 9 261 153] /ArtBox [10 10") "x")
  let (_, mds, _, _) := artifacts oneFace
    (card (attrHook "\\the\\pdfvariable pageattr \\pbtrim") "x")
  t "an attribute that is not literal PDF entries is named once, its hook read, no box written"
    (codes uds .W0443 == 1 && codes uds .W0104 == 0 && !bytesContain updf "/TrimBox" &&
      codes mds .W0443 == 1 && codes mds .W0104 == 0)
  let (_, _, ppdf, _) := artifacts oneFace (card (attrHook "/TrimBox [.5 +3 150. 90]") "x")
  t "a box's numbers read as PDF writes them, a sign or a bare point included"
    (bytesContain ppdf "/TrimBox [0.5 3 150 90]")
  let (_, _, bpdf, _) := artifacts oneFace
    ("\\documentclass{article}\n\\page{ width = 252bp, height = 144bp, bleed = 9bp }\n" ++
      attrHook "/TrimBox [20 20 190 90]" ++ "\\pagestyle{empty}\n\\begin{document}\nx\n\\end{document}")
  t "with a declared bleed, a declared trim stands and the art box follows it"
    (bytesContain bpdf "/TrimBox [20 20 190 90]" && bytesContain bpdf "/ArtBox [20 20 190 90]" &&
      bytesContain bpdf "/BleedBox [0 0 270 162]")
  let marks := "\\AddToHook{shipout/background}{\\put(0pt,-\\ph){\\put(\\bl,0pt)" ++
    "{\\rule{0.5pt}{0.05in}}}}\n"
  let (mdoc, _, mpdf, mhtml) := artifacts oneFace (card (hook ++ marks) "\\noindent Placeholder")
  let (_, _, _, phtml) := artifacts oneFace (card "" "\\noindent Placeholder")
  t "print furniture is the PDF's: the mark ships in the file, and the web page is the same \
without the marks and the boxes"
    (mdoc.page.drawn.size == 1 && bytesContain mpdf "re f" && mhtml == phtml)

  let fg := "\\AddToHook{shipout/foreground}{\\put(0pt,-\\ph){\\put(\\bl,\\bl){\\rule{0.5in}{0.5in}}}}\n"
  let bg := "\\AddToHook{shipout/background}{\\put(0pt,-\\ph){\\put(\\bl,\\bl){\\rule{0.25in}{0.25in}}}}\n"
  let (odoc, _) := elabStr (card (hook ++ fg ++ bg) "\\noindent Placeholder")
  let ogeom := Layout.Geom.ofPage odoc.page
  let oout := layoutOf oneFace odoc ogeom
  let stream := ((Pdf.pageStreams ogeom oneFace oout.pages)[0]?).bind String.fromUTF8? |>.getD ""
  let before (a b : String) : Bool :=
    match stream.splitOn a with
    | head :: _ :: _ => !hasStr head b && hasStr stream b
    | _ => false
  t "a background hook's rule paints under the text, a foreground hook's over it, as the kernel's"
    (odoc.page.drawn.map (·.front) == #[true, false] &&
      before "9 9 18 18 re f" "BT" && before "ET" "9 9 36 36 re f")
  t "the page's record names the foreground rule and the declared boxes"
    (hasStr (Ir.dump odoc #[]) " front" && -- ir tier: the dump's own record of the page
      hasStr (Ir.dump odoc #[]) " box TrimBox 9 9 261 153") -- ir tier: the dump's own record of the page
  t "a foreground rule is paint over the text, so no page ground is assumed under it"
    (oout.pages.all fun p => Contrast.uniformTextGround? ogeom p == none)
  let (xdoc, _) := elabStr (card
    "\\AddToHook{shipout/foreground}{\\put(0pt,-\\ph){\\put(\\pw,\\bl){\\rule{0.5in}{0.5in}}}}\n"
    "\\noindent Placeholder")
  let xgeom := Layout.Geom.ofPage xdoc.page
  t "a foreground rule off the medium counts as ink off the medium"
    (Layout.Quality.offMediumCount xgeom oneFace (layoutOf oneFace xdoc xgeom).pages == 1)

end Tests.PageBoxes
