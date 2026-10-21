module

public import Tests.Support

public section

open LeanTex.Core

/-! A LaTeX class's text block, margins and furniture distances stand where lualatex sets them. -/

namespace Tests.ClassArea

/-- lualatex 1.24's `\textwidth`, `\textheight`, the paper's top to the text block, a recto's and
a verso's left margin, `\headsep` and `\footskip`, in thousandths of a point, per class line. -/
def lualatex : List (String × Int × Int × Int × Int × Int × Int × Int) :=
  [("\\documentclass{article}", 345000, 550000, 125270, 134270, 134270, 25000, 30000),
   ("\\documentclass[11pt]{article}", 360000, 541400, 130270, 126270, 126270, 25000, 30000),
   ("\\documentclass[12pt]{article}", 390000, 548500, 126270, 111270, 111270, 25000, 30000),
   ("\\documentclass[a4paper]{article}", 345000, 598000, 126270, 125270, 125270, 25000, 30000),
   ("\\documentclass[11pt,a4paper]{article}", 360000, 595800, 127270, 118270, 118270, 25000, 30000),
   ("\\documentclass[12pt,a4paper]{article}", 390000, 592000, 129270, 103270, 103270, 25000, 30000),
   ("\\documentclass[twoside]{article}", 345000, 550000, 125270, 107270, 161270, 25000, 30000),
   ("\\documentclass[landscape]{article}", 345000, 370000, 125270, 224270, 224270, 25000, 30000),
   ("\\documentclass[a5paper]{article}", 276000, 346000, 128270, 72270, 72270, 25000, 30000),
   ("\\documentclass{report}", 345000, 550000, 125270, 134270, 134270, 25000, 30000),
   ("\\documentclass[11pt,twoside,a4paper]{report}", 360000, 595800, 127270, 94270, 142270, 25000,
     30000),
   ("\\documentclass{book}", 345000, 550000, 124337, 107270, 161270, 18067, 25295),
   ("\\documentclass[11pt]{book}", 360000, 541400, 128144, 101270, 152270, 19874, 27463),
   ("\\documentclass[12pt]{book}", 390000, 548500, 124144, 89270, 134270, 19874, 30000),
   ("\\documentclass[12pt,a4paper]{book}", 390000, 592000, 127144, 82270, 124270, 19874, 30000),
   ("\\documentclass[oneside]{book}", 345000, 550000, 124337, 134270, 134270, 18067, 25295),
   ("\\documentclass{memoir}", 341000, 550000, 124337, 109270, 163270, 18067, 25295),
   ("\\documentclass[11pt]{memoir}", 369000, 541400, 129744, 97270, 147270, 19874, 27463),
   ("\\documentclass[12pt,a4paper]{memoir}", 383000, 592000, 128644, 85270, 128270, 19874, 30000),
   ("\\documentclass[oneside]{memoir}", 341000, 550000, 124337, 136270, 136270, 18067, 25295),
   ("\\documentclass{scrartcl}", 418256, 595800, 84505, 89626, 89626, 20400, 47600),
   ("\\documentclass[10pt]{scrartcl}", 373442, 538000, 105631, 112033, 112033, 18000, 42000),
   ("\\documentclass[12pt]{scrartcl}", 448131, 635500, 70421, 74688, 74688, 21750, 50750),
   ("\\documentclass{scrreprt}", 418256, 595800, 84505, 89626, 89626, 20400, 47600),
   ("\\documentclass{scrbook}", 418256, 595800, 84505, 59751, 119502, 20400, 47600),
   ("\\documentclass[twoside]{scrartcl}", 418256, 595800, 84505, 59751, 119502, 20400, 47600),
   ("\\documentclass[DIV=calc]{scrartcl}", 373442, 541400, 105631, 112033, 112033, 20400, 47600),
   ("\\documentclass[DIV=classic]{scrartcl}", 418256, 595800, 84505, 89626, 89626, 20400, 47600),
   ("\\documentclass[DIV=12]{scrartcl}", 448131, 636600, 70421, 74688, 74688, 20400, 47600),
   ("\\documentclass[BCOR=10mm]{scrbook}", 398339, 595800, 84505, 85358, 113811, 20400, 47600),
   ("\\documentclass[BCOR=8mm]{scrartcl}", 402322, 595800, 84505, 108974, 108974, 20400, 47600),
   ("\\documentclass[DIV=9,BCOR=12mm,twoside]{scrartcl}", 375576, 568600, 93894, 96739, 125192,
     20400, 47600),
   ("\\documentclass[headinclude]{scrartcl}", 418256, 555000, 121905, 89626, 89626, 20400, 47600),
   ("\\documentclass[headinclude=true,footinclude=true]{scrartcl}", 418256, 514200, 121905, 89626,
     89626, 20400, 47600),
   ("\\documentclass[headinclude,DIV=calc]{scrartcl}", 373442, 500600, 143031, 112033, 112033,
     20400, 47600),
   ("\\documentclass[fontsize=14pt]{scrartcl}", 492065, 711000, 49709, 52721, 52721, 25500, 59500),
   ("\\documentclass[fontsize=9pt]{scrartcl}", 298754, 425100, 140841, 149377, 149377, 16425, 38325),
   ("\\documentclass[headinclude,headinclude=false]{scrartcl}", 418256, 595800, 84505, 89626, 89626,
     20400, 47600),
   ("\\documentclass{letter}", 345000, 550000, 156270, 134648, 134648, 45000, 25000),
   ("\\documentclass[twoside]{letter}", 345000, 550000, 156270, 134648, 134648, 45000, 25000),
   ("\\documentclass[fontsize=12pt,fontsize=10pt]{scrartcl}", 373442, 538000, 105631, 112033, 112033,
     18000, 42000),
   ("\\documentclass[12pt,10pt]{article}", 390000, 548500, 126270, 111270, 111270, 25000, 30000),
   ("\\documentclass[paper=letter,paper=a4]{scrartcl}", 418256, 595800, 84505, 89626, 89626, 20400,
     47600),
   ("\\documentclass[a4paper,letterpaper]{article}", 345000, 550000, 125270, 134270, 134270, 25000,
     30000),
   ("\\documentclass[letterpaper]{scrartcl}", 351026, 459800, 113567, 131635, 131635, 20400, 47600),
   ("\\documentclass[10pt,letterpaper]{scrartcl}", 307148, 406000, 132495, 153574, 153574, 18000,
     42000),
   ("\\documentclass[12pt,letterpaper]{scrartcl}", 383934, 505000, 99371, 115180, 115180, 21750,
     50750)]

/-- Ordinary words, enough for two full pages. -/
def prose : String :=
  String.intercalate "\n\n" (List.replicate 24 (String.intercalate " " (List.replicate 6
    "The river bends past the old mill where quiet water gathers fallen leaves.")))

def near (a : Dim.Length) (milli tol : Int) : Bool := (a - Dim.pt milli / 1000).abs ≤ Dim.pt tol / 1000

def classAreaChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let some fonts ← shippedFira | t "class area: the shipped face loads" false
  for (cls, tw, th, top, left, verso, hs, fs) in lualatex do
    let (doc, _) := Elab.run "t.tex" (cls ++ "\\begin{document}\n" ++ prose ++ "\n\\end{document}")
    let p := doc.page
    t s!"{cls}: the text block is lualatex's {tw}×{th} at {top} from the top"
      (near (p.width - 2 * p.hmargin) tw 300 && near (p.height - p.vmargin - p.bottomMargin) th 300 &&
        near p.vmargin top 1000)
    t s!"{cls}: the margins are lualatex's, {left} on a recto and {verso} on a verso"
      (near (p.leftMargin 1) left 1000 && near (p.leftMargin 2) verso 1000)
    t s!"{cls}: the furniture stands {hs} and {fs} from the block"
      (p.classSeps.any fun (h, f) => near h hs 10 && near f fs 10)
    let out := layoutOf fonts doc
    let first := (out.pages[0]?.map (·.lines.filter (!·.furniture))).bind (·[0]?)
    let topskip := Dim.pt ((p.fontSize * (2 : Int) + Dim.pt 1) / Dim.pt 2)
    t s!"{cls}: the first line stands a topskip under the block's top, at its left edge"
      (first.any fun l => (l.y - (p.vmargin + topskip)).abs ≤ Dim.pt 1 &&
        (l.x + l.hang - p.leftMargin 1).abs ≤ Dim.pt 1)
    let furniture := (out.pages[1]?.map (·.lines.filter (·.furniture))).getD #[]
    let head := furniture.filter (·.y < p.vmargin)
    let foot := furniture.filter (·.y > p.height - p.bottomMargin)
    t s!"{cls}: the second page's head stands a headsep over the block, its foot a footskip under"
      (!furniture.isEmpty &&
        head.all (fun l => (l.y - (p.vmargin - Dim.pt hs / 1000)).abs ≤ Dim.pt 1) &&
        foot.all (fun l => (l.y - (p.height - p.bottomMargin + Dim.pt fs / 1000)).abs ≤ Dim.pt 1))
  let long := String.intercalate " " (List.replicate 120
    "The river bends past the old mill where quiet water gathers fallen leaves.")
  for (cls, lines) in [("article", 46), ("book", 46), ("scrartcl", 44)] do
    let (doc, _) := Elab.run "t.tex"
      ("\\documentclass{" ++ cls ++ "}\\begin{document}\n" ++ long ++ "\n\\end{document}")
    let held := ((layoutOf fonts doc).pages[0]?.map (·.lines.filter (!·.furniture))).map (·.size)
    t s!"{cls}: a page of prose holds lualatex's {lines} lines, the last one's depth below the block"
      (held == some lines)
  let n0021 (pre : String) : Bool :=
    let (doc, _) := Elab.run "t.tex" ("\\documentclass{article}" ++ pre ++
      "\\runninghead{Notes}\\begin{document}x\\end{document}")
    (layoutOf fonts doc).diags.any (·.code == "N0021")
  t "a class's own head and foot distances differ unnamed, declared ones named"
    (!n0021 "" && !n0021 "\\page{ headsep = 10pt }" &&
      n0021 "\\page{ headsep = 10pt, footskip = 20pt }" &&
      (layoutOf fonts (Elab.run "t.tex" ("\\documentclass{resume}\\tokens{ headsep = 20pt, " ++
        "footskip = 30pt }\\runninghead{N}\\begin{document}x\\end{document}")).1).diags.any
        (·.code == "N0021"))
  let page (src : String) : Ir.PageSpec :=
    (Elab.run "t.tex" (src ++ "\\begin{document}x\\end{document}")).1.page
  t "a declared side margin claims the page across, the class's area standing down"
    (let p := page "\\documentclass{article}\\page{ hmargin = 1in }"
     p.hmargin == Dim.inch 1 && near p.vmargin 125270 1000 &&
       p.classSeps == some (Dim.pt 25, Dim.pt 30))
  t "a declared top margin claims the page down, the class's area standing across"
    (let p := page "\\documentclass{article}\\page{ vmargin = 1in }"
     p.vmargin == Dim.inch 1 && p.classSeps == none && p.width - 2 * p.hmargin == Dim.pt 345)
  t "the kernel's text height stands under the class's top"
    (let p := page "\\documentclass{article}\\setlength{\\textheight}{500pt}"
     near p.vmargin 125270 1000 && p.height - p.vmargin - p.bottomMargin == Dim.pt 500)
  t "a declared foot skip stands over the class's"
    ((page "\\documentclass{book}\\page{ footskip = 20pt }").footskip == some (Dim.pt 20))
  t "a bleed claims neither axis"
    (let p := page "\\documentclass{article}\\page{ bleed = 3mm }"
     p.width - 2 * p.hmargin == Dim.pt 345 && near p.vmargin 125270 1000)
  let tokensUnder (pre : String) (n : String) : Option Dim.Length :=
    let (doc, _) := Elab.run "t.tex" (pre ++ "\\begin{document}x\\end{document}")
    (doc.tokens.find? n).map (·.width.fixed)
  t "a page geometry places keeps the class's head and foot distances"
    (let pre := "\\documentclass{scrartcl}\\usepackage[margin=2cm]{geometry}"
     tokensUnder pre "headsep" == some (Dim.pt 204 / 10) &&
       tokensUnder pre "footskip" == some (Dim.pt 476 / 10) &&
     tokensUnder "\\documentclass[fontsize=14pt]{scrartcl}\\usepackage[margin=2cm]{geometry}"
       "headsep" == some (Dim.pt 255 / 10))
  t "a declared foot skip under geometry keeps the class's head separation"
    (tokensUnder "\\documentclass{book}\\usepackage[margin=2cm,footskip=20pt]{geometry}" "headsep" ==
      some ((Dim.inch 1).ofRatioRound 25 100))
  t "geometry's default body is its scale 0.7"
    (let p := page "\\documentclass{article}\\usepackage{geometry}"
     near (p.width - 2 * p.hmargin) 430005 300 && near (p.height - p.vmargin - p.bottomMargin) 556477 300)
  t "a class with no area keeps the engine's text block"
    (let p := page "\\documentclass{resume}"
     p.width - 2 * p.hmargin == Ir.articleTextBlock)
  t "typearea's text height is the least whole baselines reaching its target"
    (Ir.linesReaching (Dim.pt 591) (Dim.pt 11) (Dim.pt 136 / 10) == Dim.pt 11 + 43 * (Dim.pt 136 / 10))

end Tests.ClassArea
