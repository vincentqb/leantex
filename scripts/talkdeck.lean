import LeanTex.Core.Flate
import LeanTex.Core.PngEncode
import Tests.Support.Rand

/-
An invented talk-sized deck and its figures, or a deck of distinct rasters, for `bench.lean`.
Usage: lake build talkDeck && .lake/build/bin/talkDeck <dir> [frames] [rasters] [flat] [side]
-/

open LeanTex.Core

namespace TalkDeck

def vocabulary : Array String :=
  #["orbit", "cedar", "lumen", "prism", "quill", "raven", "sable", "tundra", "willow", "zephyr",
    "harbor", "meadow", "nectar", "ember", "fable", "gamut"]

def word (i : Nat) : String := vocabulary.getD (i % vocabulary.size) ""

def phrase (seed len : Nat) : String :=
  String.intercalate " " ((List.range len).map fun j => word (seed * 5 + j * 3))

/-- An invented Lean 4 listing of about `lines` lines, its names seeded by `i`. -/
def leanListing (i lines : Nat) : String := Id.run do
  let n := s!"{(word i).capitalize}{i}"
  let mut out := s!"/-- The invented {word (i + 1)} table. -/\nstructure {n} where\n" ++
    "  radius : Nat\n  steps  : List Nat\nderiving Repr\n\n" ++
    s!"def {n}.total (o : {n}) : Nat :=\n  o.steps.foldl (· + o.radius * ·) 0\n"
  let mut k := 0
  while out.foldl (fun c ch => if ch == '\n' then c + 1 else c) 0 < lines do
    out := out ++ match (i + k) % 4 with
      | 0 => s!"theorem {n}.nil{k} (r : Nat) :\n    ({n}.mk r []).total = 0 := by\n  simp [{n}.total]\n"
      | 1 => s!"example : ∀ x : Nat, x + {k} = {k} + x :=\n  fun x => Nat.add_comm x {k}\n"
      | 2 => s!"def step{k} : List Nat → Nat × Nat\n  | [] => (0, 0)\n  | x :: xs =>\n    let (a, b) := step{k} xs\n    (a + x, b + 1)  -- {word (i + k)}\n"
      | _ => s!"#eval ({n}.mk {i % 9 + 1} [1, 2, {k + 3}]).total  -- ⟨{k}⟩\n"
    k := k + 1
  return out

/-- An invented Python listing of about `lines` lines. -/
def pythonListing (i lines : Nat) : String := Id.run do
  let mut out := s!"from dataclasses import dataclass\n\n@dataclass\nclass Orbit{i}:\n" ++
    "    radius: int\n    steps: list[int]\n\n    def total(self) -> int:\n" ++
    s!"        \"\"\"Sum the invented {word i} orbit.\"\"\"\n        return sum(self.radius * k\n" ++
    "                   for k in self.steps)\n"
  let mut k := 0
  while out.foldl (fun c ch => if ch == '\n' then c + 1 else c) 0 < lines do
    out := out ++ s!"\no = Orbit{i}({k + 2}, [1, 2, {k}])\nprint(o.total(), f\"\{o.radius:.2f}\")  # {word (i + k)}"
    k := k + 1
  return out ++ "\n"

def leanShort (i : Nat) : String :=
  s!"def area (r : Nat) : Nat :=\n  3 * r * r\n#eval area {i}\ntheorem area_zero :\n    area 0 = 0 := rfl\n"

def pythonShort (i : Nat) : String :=
  s!"def area(r):\n    return 3 * r * r\n\nprint(area({i}))\n"

def bashListing (i : Nat) : String :=
  s!"#!/bin/sh\nset -eu\nfor step in 1 2 {i % 5 + 3}; do\n  echo \"step $step of the {word i} run\"\ndone\n" ++
    "lake build && lake test  # invented check\n"

def minted (lang body : String) (opts : String := "") : String :=
  "\\begin{minted}" ++ opts ++ "{" ++ lang ++ "}\n" ++ body ++ "\\end{minted}\n"

def tableRows (seed count : Nat) : String := Id.run do
  let mut out := ""
  for k in [0:count] do
    let i := seed + k
    out := out ++ (word i).capitalize ++ " & " ++ toString (i * 37 % 1000) ++ " & " ++
      toString (i * 13 % 100) ++ "\\% \\\\\n"
  return out

def frameOpen (i : Nat) (title : String) (fragile : Bool := false) : String :=
  "\\begin{frame}" ++ (if fragile then "[fragile]" else "") ++ "{" ++ title ++ " " ++
    toString i ++ "}\n"

/-- Frame `i`'s body, by a twelve-frame cycle of what a technical talk shows. -/
def frame (i : Nat) : String :=
  let cap := (phrase i 4).capitalize
  match i % 12 with
  | 0 => frameOpen i "Invented definitions" true ++ minted "lean4" (leanListing i 12) ++
      "\\end{frame}\n"
  | 1 => frameOpen i "Reveal in order" ++ "\\begin{itemize}\n\\item<1-> " ++ phrase i 7 ++
      "\n\\item<2-> \\alert{" ++ word i ++ "} " ++ phrase (i + 1) 6 ++ "\n\\item<3-> " ++
      phrase (i + 2) 8 ++ " with $\\forall x,\\ f(x) = x$\n\\end{itemize}\n\\uncover<3>{" ++
      cap ++ ".}\n\\end{frame}\n"
  | 2 => frameOpen i "A Python counterpart" true ++ minted "python" (pythonListing i 12) ++
      "\\end{frame}\n"
  | 3 => frameOpen i "Blocks" true ++ "\\begin{block}{" ++ cap ++ "}\n" ++ phrase i 14 ++
      " \\texttt{" ++ word (i + 1) ++ "}.\n\\end{block}\n\\begin{alertblock}{Caution}\n" ++
      phrase (i + 3) 10 ++ " $a^2 + b^2 = c^2$.\n\\end{alertblock}\n\\pause\n" ++
      "\\begin{exampleblock}{Example}\n" ++ minted "lean4" (leanShort i) ++
      "\\end{exampleblock}\n\\end{frame}\n"
  | 4 => frameOpen i "Side by side" true ++ "\\begin{columns}[T]\n\\begin{column}{0.48\\textwidth}\n" ++
      minted "lean4" (leanShort i) ++ "\\end{column}\n\\begin{column}{0.48\\textwidth}\n" ++
      minted "python" (pythonShort i) ++ "\\end{column}\n\\end{columns}\n\\end{frame}\n"
  | 5 => frameOpen i "A measured figure" ++ "\\begin{center}\n" ++
      (if i % 24 == 5 then "\\includegraphics[height=0.66\\textheight,alt={An invented panel diagram}]{figures/panels.png}\n"
       else "\\includegraphics[width=0.7\\textwidth,alt={An invented scatter chart}]{figures/scatter.pdf}\n") ++
      "\\end{center}\n\\end{frame}\n"
  | 6 => frameOpen i "Numbers" ++ "\\begin{tabular}{lrr}\n\\toprule\nName & Count & Share \\\\\n\\midrule\n" ++
      tableRows i 5 ++ "\\bottomrule\n\\end{tabular}\n\n\\medskip\n" ++ cap ++
      "\\footnote{" ++ (phrase (i + 2) 6).capitalize ++ ".}\n\\end{frame}\n"
  | 7 => frameOpen i "A proof in steps" true ++ minted "lean4" (leanListing (i + 1) 10) ++
      "\\pause\n" ++ (phrase i 9).capitalize ++ ", see \\href{https://example.org/" ++ word i ++
      "}{the invented notes}.\n\\end{frame}\n"
  | 8 => frameOpen i "Scripts" true ++ minted "bash" (bashListing i) ++
      "\\begin{verbatim}\n$ ./run.sh --steps " ++ toString (i % 7 + 2) ++ "\nstep 1 of the " ++ word i ++
      " run\n\\end{verbatim}\n\\end{frame}\n"
  | 9 => frameOpen i "Charts" ++ "\\begin{columns}\n\\begin{column}{0.5\\textwidth}\n" ++
      (if i % 24 == 9 then "\\includegraphics[width=\\linewidth,alt={An invented line chart}]{figures/lines.svg}\n"
       else "\\includegraphics[width=\\linewidth,alt={An invented bar chart}]{figures/bars.pdf}\n") ++
      "\\end{column}\n\\begin{column}{0.5\\textwidth}\n\\begin{itemize}\n\\item " ++ phrase i 5 ++
      "\n\\item<2-> \\alert<2>{" ++ word (i + 4) ++ "} " ++ phrase (i + 1) 4 ++
      "\n\\end{itemize}\n\\end{column}\n\\end{columns}\n\\end{frame}\n"
  | 10 => frameOpen i "Longer listing" true ++ minted "lean4" (leanListing (i + 2) 12) ++
      "\\end{frame}\n"
  | _ => frameOpen i "Takeaways" true ++ "\\begin{enumerate}\n\\item " ++ phrase i 6 ++ "\n\\item " ++
      phrase (i + 1) 6 ++ "\n\\item \\alert{" ++ phrase (i + 2) 3 ++ "}\n\\end{enumerate}\n" ++
      minted "python" (pythonShort i) ++ "\\only<2>{" ++ cap ++ " (second step).}\n\\end{frame}\n"

def fontsDecl : String :=
  "\\fonts{ dir = \"fonts\", body = \"Open Sans\", sans = \"Open Sans\", " ++
  "mono = \"Source Code Pro\", math = \"Fira Math\", mono.bold = \"SourceCodePro-Regular\", " ++
  "mono.italic = \"SourceCodePro-Regular\", mono.bolditalic = \"SourceCodePro-Regular\" }\n"

def deck (frames : Nat) : String := Id.run do
  let mut s := "\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\palette{ alert = #C2185B }\n\\usepackage{minted}\n\\usepackage{booktabs}\n\\usepackage{graphicx}\n" ++ fontsDecl ++
    "\\title{An invented talk on orbit tables}\n\\subtitle{Listings, figures and overlays}\n" ++
    "\\author{Pat Placeholder}\n\\date{}\n\\begin{document}\n\\maketitle\n" ++
    "\\begin{frame}{Outline}\n\\begin{itemize}\n\\item Invented definitions and their proofs\n" ++
    "\\item Figures, tables and scripts\n\\item Takeaways\n\\end{itemize}\n\\end{frame}\n"
  for i in [0:frames - 2] do
    if i % 10 == 0 then s := s ++ "\\section{Invented part " ++ toString (i / 10 + 1) ++ "}\n"
    s := s ++ frame i
  return s ++ "\\end{document}\n"

/-- An invented deck of `count` frames, each showing its own panels raster. -/
def rasterDeck (count : Nat) : String := Id.run do
  let mut s := "\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n\\usepackage{graphicx}\n" ++
    fontsDecl ++ "\\begin{document}\n"
  for i in [0:count] do
    s := s ++ s!"\\begin\{frame}\{Invented panels {i + 1}}\n\\centering\n" ++
      s!"\\includegraphics[height=0.75\\textheight,alt=\{Invented panels {i + 1}}]\{figures/raster{i}.png}\n" ++
      "\\end{frame}\n"
  return s ++ "\\end{document}\n"

/-! Figures. -/

/-- A diagram-like RGBA raster: panels on a light ground, flat, graded or grained, ruled with
text-like strokes, inside transparent margins. -/
def panelsRaw (side : Nat) (start : UInt64 := 731) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (side * (4 * side + 1))
  let mut seed : UInt64 := start
  for y in [:side] do
    out := out.push 0
    for x in [:side] do
      let margin := x < side / 32 || y < side / 32 || x ≥ side - side / 32 || y ≥ side - side / 32
      let px := (x * 6) / side
      let py := (y * 5) / side
      let inPanel := (x * 6) % side > side / 20 && (y * 5) % side > side / 16
      let stroke := inPanel && (y * 40 / side) % 2 == 0 && (y * 160 / side) % 4 == 1 &&
        ((x * 37 + y) / 23) % 7 != 0
      let (next, v) := nextRand seed
      seed := next
      let grain := (v >>> 61).toUInt8
      let (r, g, b) : UInt8 × UInt8 × UInt8 :=
        if !inPanel then (248, 247, 244)
        else if stroke then (34, 40, 49)
        else if (px + py) % 3 == 0 then (226, 236, 250)
        else if (px + py) % 3 == 1 then ((200 + x * 40 / side).toUInt8, 230, 214)
        else if (x / 8 + y / 8) % 5 == 0 then (252, 214 + grain, 180 + grain)
        else (252, 222, 190)
      out := out.push r |>.push g |>.push b |>.push (if margin then 0 else 255)
  return out

/-- A photograph-like RGB raster with no alpha, which planning passes through: gradients under
per-pixel grain that deflate barely shrinks. -/
def grainRaw (side : Nat) (start : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (side * (3 * side + 1))
  let mut seed : UInt64 := start
  for y in [:side] do
    out := out.push 0
    for x in [:side] do
      let (next, v) := nextRand seed
      seed := next
      out := out.push ((x * 160 / side + 40).toUInt8 + (v >>> 59).toUInt8)
        |>.push ((y * 160 / side + 40).toUInt8 + ((v >>> 54) &&& 31).toUInt8)
        |>.push (((x + y) * 80 / side + 60).toUInt8 + ((v >>> 49) &&& 31).toUInt8)
  return out

def pdfOf (content : ByteArray) (width height : Nat) : ByteArray := Id.run do
  let z := Flate.deflate content
  let objs : Array ByteArray := #[
    "<< /Type /Catalog /Pages 2 0 R >>".toUTF8,
    s!"<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 {width} {height}] >>".toUTF8,
    "<< /Type /Page /Parent 2 0 R /Resources << >> /Contents 4 0 R >>".toUTF8,
    s!"<< /Length {z.size} /Filter /FlateDecode >>\nstream\n".toUTF8 ++ z ++ "\nendstream".toUTF8]
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offsets := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{i + 1} 0 obj\n".toUTF8 ++ obj ++ "\nendobj\n".toUTF8
  let xref := out.size
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n".toUTF8
  for offset in offsets do
    let digits := toString offset
    out := out ++ (String.ofList (List.replicate (10 - digits.length) '0') ++ digits ++ " 00000 n \n").toUTF8
  return out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n".toUTF8

def palette : Array String := #["0.12 0.47 0.71", "1 0.5 0.05", "0.17 0.63 0.17", "0.84 0.15 0.16"]

/-- A font-free scatter chart of `points` markers in four series over a grid. -/
def scatterContent (points : Nat) : ByteArray := Id.run do
  let mut s := "1 1 1 rg 0 0 640 400 re f\n0.85 0.85 0.85 RG 0.5 w\n"
  for k in [0:11] do
    s := s ++ s!"{40 + k * 56} 30 m {40 + k * 56} 380 l S\n{40} {30 + k * 35} m 600 {30 + k * 35} l S\n"
  s := s ++ "0 0 0 RG 1 w 40 30 m 600 30 l S 40 30 m 40 380 l S\n"
  let mut seed : UInt64 := 99
  let mut out := s.toUTF8
  for p in [0:points] do
    let (next, v) := nextRand seed
    seed := next
    let x := 42 + (v >>> 40).toNat % 556
    let y := 32 + ((v >>> 20).toNat % 346 + p % 346) / 2
    let c := palette.getD (p % 4) ""
    out := out ++ s!"{c} rg {x}.{p % 10} {y}.{(p / 10) % 10} 2.4 2.4 re f\n".toUTF8
  return out

/-- A font-free bar chart of `bars` bars. -/
def barsContent (bars : Nat) : ByteArray := Id.run do
  let mut s := "1 1 1 rg 0 0 480 320 re f\n0 0 0 RG 1 w 30 20 m 460 20 l S 30 20 m 30 300 l S\n"
  for k in [0:bars] do
    let h := 20 + (k * 53 + 17) % 260
    let w := 400 / bars
    s := s ++ s!"{palette.getD (k % 4) ""} rg {32 + k * w} 21 {w - 2} {h} re f\n"
  return s.toUTF8

/-- An invented SVG line chart of `series` polylines of `points` points, every fourth marked,
over vertical grid lines. -/
def linesSvg (series points : Nat) : String := Id.run do
  let colours := #["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728"]
  let mut s := "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"640\" height=\"400\" viewBox=\"0 0 640 400\">\n" ++
    "<title>An invented line chart</title>\n<rect x=\"0\" y=\"0\" width=\"640\" height=\"400\" fill=\"#ffffff\"/>\n"
  for k in [0:11] do
    s := s ++ s!"<line x1=\"{40 + k * 56}\" y1=\"20\" x2=\"{40 + k * 56}\" y2=\"370\" stroke=\"#dddddd\" stroke-width=\"0.5\"/>\n"
  for j in [0:series] do
    let mut d := ""
    for p in [0:points] do
      let x := 40 + p * 560 / points
      let y := 360 - ((p * (j + 3) * 7 + j * 61) % 300)
      d := d ++ (if p == 0 then "M " else " L ") ++ s!"{x} {y}"
    s := s ++ s!"<path d=\"{d}\" fill=\"none\" stroke=\"{colours.getD (j % 4) ""}\" stroke-width=\"1.5\"/>\n"
    for p in [0:points] do
      if p % 4 == 0 then
        let x := 40 + p * 560 / points
        let y := 360 - ((p * (j + 3) * 7 + j * 61) % 300)
        s := s ++ s!"<circle cx=\"{x}\" cy=\"{y}\" r=\"2.5\" fill=\"{colours.getD (j % 4) ""}\"/>\n"
  return s ++ "</svg>\n"

end TalkDeck

open TalkDeck in
def main (args : List String) : IO UInt32 := do
  let some dir := args.head? | IO.eprintln "usage: talkDeck <dir> [frames] [rasters]"; return 2
  let frames := ((args[1]?).bind (·.toNat?)).getD 60
  let rasters := ((args[2]?).bind (·.toNat?)).getD 0
  let flat := args[3]? == some "flat"
  let side := ((args[4]?).bind (·.toNat?)).getD 2048
  let dir := System.FilePath.mk dir
  IO.FS.createDirAll (dir / "figures")
  if rasters > 0 then
    IO.FS.writeFile (dir / "deck.tex") (rasterDeck rasters)
    for i in [0:rasters] do
      let png := if flat then
          PngEncode.encodeIdat { width := side, height := side, bitDepth := 8, colorType := 2 }
            (Flate.deflate (grainRaw side (731 + i.toUInt64)))
        else
          PngEncode.encodeIdat { width := side, height := side, bitDepth := 8, colorType := 6 }
            (Flate.deflate (panelsRaw side (731 + i.toUInt64)))
      IO.FS.writeBinFile (dir / "figures" / s!"raster{i}.png") png
    return 0
  IO.FS.writeFile (dir / "deck.tex") (deck frames)
  IO.FS.writeBinFile (dir / "figures" / "panels.png") (PngEncode.encodeIdat
    { width := 4096, height := 4096, bitDepth := 8, colorType := 6 } (Flate.deflate (panelsRaw 4096)))
  IO.FS.writeBinFile (dir / "figures" / "scatter.pdf") (pdfOf (scatterContent 60000) 640 400)
  IO.FS.writeBinFile (dir / "figures" / "bars.pdf") (pdfOf (barsContent 24) 480 320)
  IO.FS.writeFile (dir / "figures" / "lines.svg") (linesSvg 4 2000)
  return 0
