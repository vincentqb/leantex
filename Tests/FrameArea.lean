import Tests.Support

open LeanTex.Core

namespace Tests.FrameArea

/-- The invented moloch deck the checks lay out, the one source each value
below was first measured on under lualatex (beamer 10 pt, 4:3, the shipped
Fira Sans for every face): a standout frame, a standout frame whose note the
deck's footline hook restores, a titled control, a bottom-aligned standout,
and a section page. The footline hook is the one a moloch deck spells to
restore an explicit note on a standout frame. -/
private def deck : String :=
  "\\documentclass[10pt]{beamer}\n\\usetheme{moloch}\n" ++
  "\\newenvironment{framefooter}[1]{%\n" ++
  "  \\setbeamertemplate{frame footer}{{\\scriptsize #1}}%\n" ++
  "}{\\setbeamertemplate{frame footer}{}}\n" ++
  "\\makeatletter\n" ++
  "\\apptocmd{\\KV@beamerframe@standout}{%\n" ++
  "  \\ifbeamertemplateempty{frame footer}{}{%\n" ++
  "    \\setbeamercolor{footline}{use={standout,background canvas},\n" ++
  "      fg=standout.fg,bg=background canvas.bg}%\n" ++
  "    \\setbeamertemplate{footline}[plain]%\n" ++
  "    \\ifbeamer@noframenumbering\n" ++
  "      \\setbeamertemplate{page number in head/foot}{}%\n" ++
  "    \\fi\n" ++
  "  }%\n" ++
  "}{}{\\PackageError{probe}{hook}{}}\n" ++
  "\\makeatother\n" ++
  "\\begin{document}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n" ++
  "\\begin{framefooter}{Lima mike}\n" ++
  "\\begin{frame}[standout]\nKilo words.\n\\end{frame}\n" ++
  "\\end{framefooter}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\begin{frame}[standout,b]\nKilo words.\n\\end{frame}\n" ++
  "\\section{Hotel words}\n" ++
  "\\begin{frame}{Foxtrot}\nAlpha words.\n\\end{frame}\n" ++
  "\\end{document}\n"

/-- **Every frame stands its content box in beamer's text area**
(`Layout.FrameArea`, `Layout.frameFloor_exact`). beamer's `\textheight` is
the paper less `\footheight` — the footline's box plus 4 pt, the 4 pt alone
where the footline is empty — and a frame's content opens at its top on
`\vskip-\parskip\vbox{}`; a plain frame, as moloch's section page is,
centres on the whole paper with its first box flush on that `\vbox{}`.
Asserted over `Layout.Out` against lualatex's measurements of `deck` (TeX
Live 2026; bp from the page top to the baseline): a standout frame's line
at 142.951, the same frame with its note restored at 138.197 (the note's
own baseline at 268.057), and the section page's title at 127.894. The
lines are held to 0.5 bp: what remains is the standout size's leading,
17.28 pt on the engine's ladder against size10.clo's 18 pt, half of it
after centring (0.36 bp). At `fa516a82` the standout frame stood 2.06 bp
high, the restored note sent its line 9.12 bp low — the page took the
note's band off a floor still at the slides margin, the paper's top still
26.4 bp above its content — and the section page stood 9.99 bp low.
Invented words. -/
def checks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fira ← (do
      match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
      | .ok f => pure (some (oneFaceOf f))
      | .error _ => pure none : IO (Option Font.FontSet))
    | t "frame area: the shipped Fira Sans parses" false
  let (doc, _) := elabStr deck
  let geom := Layout.Geom.ofPage doc.page
  let out := layoutOf fira doc geom
  let bp (milli : Int) : Dim.Sp := Dim.pt 1 * milli / 1000
  let near (a b : Dim.Sp) : Bool := a - b ≤ bp 500 && b - a ≤ bp 500
  let line (page : Nat) (word : String) (furniture : Bool := false) :
      Option Layout.LineOut :=
    out.pages[page]?.bind fun p => p.lines.find? fun l =>
      l.furniture == furniture && hasStr (lineText l) word
  let at? (page : Nat) (word : String) (milli : Int) (furniture : Bool := false) : Bool :=
    ((line page word furniture).map fun l => near l.y (bp milli)).getD false
  t "frame area: a standout frame centres in beamer's text area, as lualatex does"
    (at? 0 "Kilo" 142951)
  t "frame area: a restored standout note lifts its frame by half its footheight, as lualatex does"
    (at? 1 "Kilo" 138197 && at? 1 "Lima" 268057 true)
  t "frame area: a section page centres on the whole paper, as lualatex does"
    (at? 4 "Hotel" 127894)
  -- The floor itself, exactly: a bottom-aligned standout frame's content
  -- ends on it, the glyphs' depth below its last baseline (`B.contentEnd`),
  -- 4 pt above the paper's edge where no footline stands.
  t "frame area: an empty footline's text area ends its gap above the paper's edge"
    (((line 3 "Kilo").map fun l =>
      l.y + (Layout.segsInk fira l.segs).2 ==
        Layout.frameFloor geom.pageH Ir.footline.sep none).getD false)

end Tests.FrameArea
