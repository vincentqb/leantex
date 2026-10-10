/-
What a document costs to build: invented documents at any size, built by the
compiled engine in a sealed environment, each build's cost read from the
engine's own porcelain record — its milliseconds, its peak resident set size
(`rssKiB`) — beside the artifact's bytes. The scoreboard's `doccost` tier
(hermetic, gated) and `bench --doc-cost` (host-dependent, reported) both build
through here, so the gate and the report measure the same documents the same
way.

The peak is the engine's own (`VmHWM` on Linux), never the spawning
process's: `getrusage` alone let this interpreter's resident set leak into
every child it measured.

A sealed build sees what the repository ships and nothing else it could pick
up: the document's files, the corpus's fonts staged beside it as `fonts/`, the
corpus's invented images, an empty `HOME`, and a `PATH` that reaches no tool.
The font scan still visits the system's standard font roots, so a cold scan's
time is the host's; but a build whose page resolved a face from outside the
staged set does not count (`fontsSealed`), so every artifact measured here is a
function of the repository alone.

Every document is invented: a vocabulary of plain words, placeholder names,
`example.org` links, and the corpus's own synthetic images.
-/
import Lean.Data.Json
import scripts.PerfHistory

namespace DocBench

/-! ## Invented text -/

def vocabulary : Array String :=
  #["alpha", "brisk", "cedar", "delta", "ember", "fable", "gamut", "harbor", "ivory", "jasper",
    "kettle", "lumen", "meadow", "nectar", "orbit", "prism", "quill", "raven", "sable", "tundra",
    "umber", "vapor", "willow", "xenon", "yarrow", "zephyr"]

def word (i : Nat) : String := vocabulary[i % vocabulary.size]!

def capital (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- `len` words, seeded so neighbouring units differ. -/
def phrase (seed len : Nat) : String :=
  String.intercalate " " ((List.range len).map fun j => word (seed * 7 + j * 3))

/-- Every face a document may name: the corpus's shipped families, with the
one-face monospace family's variants declared rather than substituted, so a
sealed build raises no font loss at all. -/
def fontsDecl (body : String) : String :=
  "\\fonts{ dir = \"fonts\", body = \"" ++ body ++ "\", sans = \"Open Sans\", " ++
  "mono = \"Source Code Pro\", math = \"Fira Math\", mono.bold = \"SourceCodePro-Regular\", " ++
  "mono.italic = \"SourceCodePro-Regular\", mono.bolditalic = \"SourceCodePro-Regular\" }\n"

/-- The line an edit changes: the watch report rewrites the source with the
next revision and times the artifact that answers it. -/
def revision (rev : Nat) : String := s!"Revision {rev} of the invented text."

def pythonLines (seed count : Nat) : String := Id.run do
  let mut out := ""
  for k in [0:count] do
    let i := seed + k
    out := out ++ match k % 5 with
      | 0 => s!"def orbit_{i}(radius, steps):\n"
      | 1 => s!"    total = {i % 7}  # {word i} {word (i + 1)}\n"
      | 2 => "    for k in range(steps):\n"
      | 3 => s!"        total += radius * k + len(\"{word (i + 2)}\")\n"
      | _ => "    return total\n"
  return out

def tableRows (seed count : Nat) : String := Id.run do
  let mut out := ""
  for k in [0:count] do
    let i := seed + k
    out := out ++ capital (word i) ++ " & " ++ toString (i * 37 % 1000) ++ " & " ++
      toString (i * 13 % 100) ++ "\\% \\\\\n"
  return out

/-! ## The document families

Each is a fixed opening that already uses every face and feature its repeated
unit uses, then `n` units: the size-0 document carries every constant cost
(each face embedded, each image decoded), so what `n` units add is what grows. -/

/-- One paragraph in the shape the audit's styled-paragraph probes used:
thirty words, one bold, one typewriter, one emphasised. -/
def reportPara (i : Nat) : String := Id.run do
  let mut out := ""
  for j in [0:30] do
    let w := word (i * 7 + j * 3)
    let w := if j == 3 then "\\textbf{" ++ w ++ "}"
      else if j == 10 then "\\texttt{" ++ w ++ "}"
      else if j == 20 then "\\emph{" ++ w ++ "}" else w
    out := out ++ (if j == 0 then w else " " ++ w)
  return out ++ "."

def report (n rev : Nat) : Array (String × String) := Id.run do
  let mut s := "\\documentclass{article}\n" ++ fontsDecl "Source Serif Pro" ++
    "\\begin{document}\n\\section{Opening}\n" ++ revision rev ++ " " ++ reportPara 0 ++
    " With $x_1^2 + y_1^2 = r^2$ inline.\n\n"
  for i in [0:n] do
    if i % 50 == 0 then s := s ++ "\\section{Invented section " ++ toString (i / 50 + 1) ++ "}\n"
    s := s ++ reportPara (i + 1) ++ "\n\n"
  return #[("report.tex", s ++ "\\end{document}\n")]

def deckFrame (i : Nat) : String :=
  let open_ := "\\begin{frame}{Invented frame " ++ toString (i + 1) ++ "}\n"
  match i % 4 with
  | 0 => open_ ++ "\\begin{itemize}\n\\item " ++ phrase i 6 ++ "\n\\item \\alert{" ++ word i ++
      "} " ++ phrase (i + 1) 5 ++ "\n\\item " ++ phrase (i + 2) 6 ++ "\n\\end{itemize}\n" ++
      "\\[ \\sum_{k=1}^{" ++ toString (i + 2) ++ "} k^2 = \\frac{m(m+1)(2m+1)}{6} \\]\n\\end{frame}\n"
  | 1 => "\\begin{frame}[fragile]{Invented frame " ++ toString (i + 1) ++ "}\n" ++
      "\\begin{lstlisting}[language=Python]\n" ++ pythonLines i 5 ++ "\\end{lstlisting}\n\\end{frame}\n"
  | 2 => open_ ++ "\\begin{tabular}{lrr}\n\\toprule\nName & Count & Share \\\\\n\\midrule\n" ++
      tableRows i 4 ++ "\\bottomrule\n\\end{tabular}\n\\end{frame}\n"
  | _ => open_ ++ capital (phrase i 8) ++ ".\n\n" ++
      "\\includegraphics[width=0.3\\textwidth,alt={Invented colour grid}]{rects.png}\n\\end{frame}\n"

def deck (n rev : Nat) : Array (String × String) := Id.run do
  let mut s := "\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\usepackage{listings}\n\\usepackage{booktabs}\n" ++ fontsDecl "Open Sans" ++
    "\\title{An invented deck}\n\\author{Pat Placeholder}\n\\date{}\n\\begin{document}\n" ++
    "\\maketitle\n\\begin{frame}{Opening}\n" ++ revision rev ++ "\n\\end{frame}\n"
  for i in [0:4] do s := s ++ deckFrame i
  for i in [0:n] do s := s ++ deckFrame (i + 4)
  return #[("deck.tex", s ++ "\\end{document}\n")]

def paperSection (s : Nat) : String :=
  let k := toString s
  "\\section{Invented topic " ++ k ++ "}\\label{sec:" ++ k ++ "}\n" ++
  capital (phrase s 40) ++ " \\citep{k" ++ toString (3 * s) ++ "}. " ++ capital (phrase (s + 1) 20) ++
  " \\citet{k" ++ toString (3 * s + 1) ++ "} " ++ phrase (s + 2) 12 ++ ".\\footnote{" ++
  capital (phrase (s + 3) 8) ++ ".}\n\n" ++
  "\\begin{equation}\\label{eq:" ++ k ++ "}\nE_{" ++ k ++ "} = \\sum_{k=1}^{" ++ toString (s + 3) ++
  "} \\frac{a_k}{k^2}\n\\end{equation}\n" ++
  "As \\eqref{eq:" ++ k ++ "} shows for Section~\\ref{sec:" ++ k ++ "}, " ++ phrase (s + 4) 30 ++
  " \\citep{k" ++ toString (3 * s + 2) ++ "}.\n\n" ++
  (if s % 3 == 0 then "\\begin{figure}[t]\n\\centering\n" ++
    "\\includegraphics[width=0.5\\linewidth,alt={Invented colour grid}]{rects.png}\n" ++
    "\\caption{" ++ capital (phrase (s + 5) 9) ++ ".}\\label{fig:" ++ k ++ "}\n\\end{figure}\n\n"
   else "") ++
  (if s == 0 || s % 4 == 1 then "\\begin{table}[t]\n\\centering\n\\caption{" ++ capital (phrase (s + 6) 6) ++
    "}\\label{tab:" ++ k ++ "}\n\\begin{tabular}{lrr}\n\\toprule\nName & Count & Share \\\\\n" ++
    "\\midrule\n" ++ tableRows s 5 ++ "\\bottomrule\n\\end{tabular}\n\\end{table}\n\n"
   else "") ++
  capital (phrase (s + 7) 60) ++ ".\n\n"

def bibEntries (count : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:count] do
    out := out ++ "@article{k" ++ toString i ++ ",\n  author = {Alex " ++ capital (word i) ++
      " and Blair " ++ capital (word (i + 11)) ++ "},\n  title = {Invented result number " ++
      toString i ++ "},\n  journal = {Journal of Invented Results},\n  year = {" ++
      toString (2000 + i % 25) ++ "},\n  volume = {" ++ toString (i % 40 + 1) ++ "},\n  pages = {" ++
      toString (i + 1) ++ "--" ++ toString (i + 9) ++ "}\n}\n"
  return out

def paper (n rev : Nat) : Array (String × String) := Id.run do
  let mut s := "\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{natbib}\n" ++
    "\\usepackage{graphicx}\n\\usepackage{booktabs}\n" ++ fontsDecl "Source Serif Pro" ++
    "\\title{An invented study of orbits}\n\\author{Pat Placeholder}\n\\date{}\n" ++
    "\\bibliographystyle{plainnat}\n\\begin{document}\n\\maketitle\n\\begin{abstract}\n" ++
    revision rev ++ " " ++ capital (phrase 1 40) ++ ".\n\\end{abstract}\n\n"
  for i in [0:n + 1] do s := s ++ paperSection i
  return #[("paper.tex", s ++ "\\bibliography{refs}\n\\end{document}\n"),
    ("refs.bib", bibEntries (3 * (n + 1)))]

def noteBlock (i : Nat) : String :=
  let head := if i % 10 == 0 then "## Invented heading " ++ toString (i / 10 + 1) ++ "\n\n" else ""
  head ++ match i % 6 with
  | 0 => capital (phrase i 12) ++ " *" ++ word i ++ "* and **" ++ word (i + 1) ++ "** with `" ++
      word (i + 2) ++ "` and a [link](https://example.org/" ++ toString i ++ ").\n\n"
  | 1 => "- " ++ phrase i 5 ++ "\n- *" ++ word i ++ "* " ++ phrase (i + 1) 4 ++ "\n- " ++
      phrase (i + 2) 5 ++ "\n\n"
  | 2 => "```python\n" ++ pythonLines i 5 ++ "```\n\n"
  | 3 => "> " ++ capital (phrase i 14) ++ ".\n\n"
  | 4 => "1. " ++ phrase i 4 ++ "\n2. " ++ phrase (i + 1) 4 ++ "\n3. " ++ phrase (i + 2) 4 ++ "\n\n"
  | _ => if i % 30 == 5 then "![Invented colour grid](rects.png)\n\n"
      else capital (phrase i 30) ++ ".\n\n"

/-- Markdown through its TeX inclusion, the one surface that declares fonts:
the reader and the desugaring are what grows, inside a document the sealed
build can resolve. -/
def notes (n rev : Nat) : Array (String × String) := Id.run do
  let mut md := "# Invented notes\n\n![Invented colour grid](rects.png)\n\n"
  for i in [0:6] do md := md ++ noteBlock (i + 1)
  for i in [0:n] do md := md ++ noteBlock (i + 7)
  return #[("notes.tex", "\\documentclass{article}\n\\usepackage{markdown}\n" ++
      fontsDecl "Source Serif Pro" ++ "\\begin{document}\n" ++ revision rev ++
      "\n\n\\markdownInput{notes.md}\n\\end{document}\n"),
    ("notes.md", md)]

def listing (n rev : Nat) : Array (String × String) :=
  #[("listing.tex", "\\documentclass{article}\n\\usepackage{listings}\n" ++
    fontsDecl "Source Serif Pro" ++ "\\begin{document}\n" ++ revision rev ++ "\n\n" ++
    "\\begin{lstlisting}[language=Python]\n" ++ pythonLines 0 5 ++ pythonLines 5 n ++
    "\\end{lstlisting}\n\\end{document}\n")]

/-- A family of invented documents: `source n rev` is the document with `n`
repeated units at revision `rev`, its main source first. `gate` is the size
the growth gate compares with four times it, and `far` says whether it also
compares `4n` with `16n`; `reference` is the size of the document the report
times. -/
structure Gen where
  name : String
  unit : String
  source : Nat → Nat → Array (String × String)
  gate : Nat
  far : Bool
  reference : Nat

/-- The deck's, the paper's and the notes' `16n` builds are cheap (under 2 s
here), and at sixteen times the squared size the pair sees a far smaller
quadratic term (`growthWithin_quadratic_exact`). The report's and the
listing's are not yet: their time grows faster than their input (3.8 s and
8.4 s at `16n`). -/
def gens : Array Gen := #[
  { name := "deck", unit := "frames", source := deck, gate := 32, far := true, reference := 64 },
  { name := "report", unit := "paragraphs", source := report, gate := 100, far := false,
    reference := 2000 },
  { name := "paper", unit := "sections", source := paper, gate := 4, far := true, reference := 12 },
  { name := "notes", unit := "blocks", source := notes, gate := 100, far := true, reference := 400 },
  { name := "listing", unit := "lines", source := listing, gate := 250, far := false,
    reference := 2000 }]

def formats : Array String := #["pdf", "html"]

/-! ## Sealed builds -/

/-- A staged document directory: the document's files at its root beside the
corpus's fonts (`fonts/`) and images, an empty `home/`, and a `no-tools/`
that is the whole `PATH`. -/
structure Stage where
  root : System.FilePath

def Stage.fonts (s : Stage) : System.FilePath := s.root / "fonts"

def stage (dir : System.FilePath) : IO Stage := do
  let corpus : System.FilePath := "testdata/corpus"
  IO.FS.createDirAll (dir / "fonts")
  for e in ← (corpus / "fonts").readDir do
    if e.fileName.endsWith ".otf" || e.fileName.endsWith ".ttf" then
      IO.FS.writeBinFile (dir / "fonts" / e.fileName) (← IO.FS.readBinFile e.path)
  for image in ["rects.png", "rects-alpha.png"] do
    IO.FS.writeBinFile (dir / image) (← IO.FS.readBinFile (corpus / image))
  for d in ["home", "no-tools", "out"] do IO.FS.createDirAll (dir / d)
  return { root := ← IO.FS.realPath dir }

def Stage.write (s : Stage) (files : Array (String × String)) : IO String := do
  for (name, text) in files do IO.FS.writeFile (s.root / name) text
  return (files[0]?.map (·.1)).getD ""

def Stage.noTools (s : Stage) : System.FilePath := s.root / "no-tools"

/-- What the child sees of the environment: everything named here, and the
font and tool variables the engine reads removed. -/
def sealedEnv (s : Stage) (cache : System.FilePath) : Array (String × Option String) :=
  #[("HOME", some (s.root / "home").toString), ("PATH", some s.noTools.toString),
    ("XDG_CACHE_HOME", some cache.toString), ("LC_ALL", some "C"), ("TZ", some "UTC"),
    ("NO_COLOR", some "1"), ("LEANTEX_FONT", none), ("LEANTEX_FONT_PATH", none)]

/-- The command line of a build counted by `perf`, sealed again inside it:
`perf` puts its own directory and `/usr/bin` before the `PATH` it was given,
which handed the engine `kpsewhich` and with it the TeX tree's fonts (191
faces scanned where the sealed build scans 67) and cost the first counted
build a hundred million instructions of scanning them. -/
def perfArgs (perf : String) (s : Stage) (binary : System.FilePath) (args : Array String) :
    String × Array String :=
  (perf, #["stat", "-x", ",", "-e", "instructions:u", "--", "env", s!"PATH={s.noTools}",
    binary.toString] ++ args)

/-- The user-space instruction count `perf stat -x ,` wrote to `stderr`. -/
def perfCount (stderr : String) : Option Nat :=
  ((stderr.splitOn "\n").find? fun l => (l.splitOn "instructions:u").length > 1).bind fun l =>
    (l.splitOn ",").head?.bind (·.toNat?)

structure Phase where
  name : String
  detail : String
  ms : Nat
deriving Inhabited

/-- One build, as the engine reported it and as the harness saw it. -/
structure Build where
  ms : Nat
  wall : Nat := 0
  rssKiB : Nat
  pages : Nat
  artifact : ByteArray := .empty
  phases : Array Phase
  /-- Codes of the warnings and errors, in emission order. -/
  losses : Array String
  /-- The face files the build's font set loaded and how many faces its scan
  found: the typed fields of its `font` phase. -/
  faces : Option (Array String × Nat)
  /-- User-space instructions retired, where the build ran under `perf`. -/
  instructions : Option Nat := none
deriving Inhabited

def Build.phase? (b : Build) (name : String) : Option Phase := b.phases.find? (·.name == name)

def facesText : Option (Array String × Nat) → String
  | some (paths, scanned) => s!"{String.intercalate ", " paths.toList} of {scanned} scanned faces"
  | none => "no typed faces"

/-- Every face file the build loaded lies under the staged `fonts/`, as its
`font` phase's typed fields say. A build without them is not sealed. -/
def fontsSealed (s : Stage) (b : Build) : Bool :=
  match b.faces with
  | some (paths, _) =>
    let dir := s.fonts.toString ++ "/"
    !paths.isEmpty && paths.all (·.startsWith dir)
  | none => false

def jsonStr (j : Lean.Json) (key : String) : String := (j.getObjValAs? String key).toOption.getD ""

def jsonNat (j : Lean.Json) (key : String) : Option Nat := (j.getObjValAs? Nat key).toOption

/-- Read one run's porcelain: every line a record, at most one `font` phase,
whose typed fields, where it has them, must read, and exactly one summary,
which must say the artifact was written and how much the run held at its peak. -/
def readReport (stdout : String) : Except String Build := do
  let mut phases : Array Phase := #[]
  let mut losses : Array String := #[]
  let mut faces : Option (Array String × Nat) := none
  let mut summary : Option (Nat × Nat × Nat) := none
  for line in stdout.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let j ← Lean.Json.parse line
    match jsonStr j "event" with
    | "phase" =>
      let p : Phase :=
        { name := jsonStr j "name", detail := jsonStr j "detail", ms := (jsonNat j "ms").getD 0 }
      if p.name == "font" then
        if phases.any (·.name == "font") then throw "more than one font phase"
        if let .ok v := j.getObjVal? "faces" then
          let paths ← (Lean.fromJson? v : Except String (Array String))
          let some scanned := jsonNat j "scanned" | throw "the font phase names faces but no scan"
          faces := some (paths, scanned)
      phases := phases.push p
    | "diagnostic" =>
      if jsonStr j "severity" != "note" then losses := losses.push (jsonStr j "code")
    | "summary" =>
      if summary.isSome then throw "more than one summary"
      unless (j.getObjValAs? Bool "ok").toOption == some true do throw "the run wrote no artifact"
      let some rss := jsonNat j "rssKiB" | throw "the summary states no peak resident set size"
      summary := some ((jsonNat j "ms").getD 0, rss, (jsonNat j "pages").getD 0)
    | _ => pure ()
  let some (ms, rssKiB, pages) := summary | throw "no summary"
  return { ms, rssKiB, pages, phases, losses, faces }

/-- Build `main` (staged at `s`) to `format` under the sealed environment with
`cache` as its application cache, counted by `perf` when one is named. -/
def build (binary : System.FilePath) (s : Stage) (cache : System.FilePath) (main format : String)
    (perf : Option String := none) : IO (Except String Build) := do
  let stem := ((System.FilePath.mk main).fileStem).getD main
  let out := s.root / "out" / (stem ++ "." ++ format)
  if ← out.pathExists then IO.FS.removeFile out
  let args := #["build", (s.root / main).toString, "-o", out.toString, "--porcelain", "-v"]
  let (cmd, args) := match perf with
    | some p => perfArgs p s binary args
    | none => (binary.toString, args)
  let t0 ← IO.monoMsNow
  let r ← IO.Process.output { cmd, args, env := sealedEnv s cache }
  let wall := (← IO.monoMsNow) - t0
  match readReport r.stdout with
  | .error e => return .error s!"{main} → {format}: {e} (exit {r.exitCode}) {r.stderr.trimAscii}"
  | .ok b =>
    let b := { b with wall, artifact := ← IO.FS.readBinFile out,
                      instructions := perf.bind fun _ => perfCount r.stderr }
    if !fontsSealed s b then
      return .error s!"{main} → {format}: a face resolved outside the staged fonts: \
        {facesText b.faces}"
    return .ok b

/-! ## Growth and size -/

/-- Four times the input may add at most eight times the memory above the
engine's fixed footprint. Linear growth reads at most 4 (`phasePeak_between`),
a structure whose capacity doubles in between at most 8
(`growthWithin_doubled_covers`), quadratic 16. -/
def growthBound : Nat := 8

/-- Builds of each size the gate keeps the least peak of. A peak moves with
how many paragraph tasks happen to be in flight at once: a 128-frame deck's
moved between 115 and 136 MiB across eight runs on a many-core host. The
least of a few is what the document needs; what remains of the spread is far
inside the bound, where healthy builds read under 2x of its 8x. -/
def gateRuns : Nat := 3

/-- Runs the fixed footprint keeps the least peak of: it is the bound's base,
so it must not read high, and a run that reads no document costs milliseconds. -/
def footprintRuns : Nat := 8

/-- Peak resident set size above the engine's fixed footprint, at `n` and
`4n` units, within the bound. -/
def growthWithin (fixed small big : Nat) : Bool :=
  big - fixed ≤ growthBound * (small - fixed)

theorem growthWithin_monotone {fixed small big big' : Nat} (h : big' ≤ big)
    (w : growthWithin fixed small big = true) : growthWithin fixed small big' = true := by
  unfold growthWithin growthBound at *
  have := of_decide_eq_true w
  exact decide_eq_true (by omega)

/-- A run's peak, modelled: the largest of its phases' memories, each phase an
intercept plus a slope times the document's size. -/
def phasePeak (phases : List (Nat × Nat)) (n : Nat) : Nat :=
  phases.foldl (fun m p => max m (p.1 + p.2 * n)) 0

/-- However one phase hides another, four times the size moves such a peak
between itself and four times itself. -/
theorem phasePeak_between (phases : List (Nat × Nat)) (n : Nat) :
    phasePeak phases n ≤ phasePeak phases (4 * n) ∧
      phasePeak phases (4 * n) ≤ 4 * phasePeak phases n := by
  have step : ∀ (ps : List (Nat × Nat)) (a a' : Nat), a ≤ a' → a' ≤ 4 * a →
      ps.foldl (fun m p => max m (p.1 + p.2 * n)) a ≤
          ps.foldl (fun m p => max m (p.1 + p.2 * (4 * n))) a' ∧
        ps.foldl (fun m p => max m (p.1 + p.2 * (4 * n))) a' ≤
          4 * ps.foldl (fun m p => max m (p.1 + p.2 * n)) a := by
    intro ps
    induction ps with
    | nil => intro a a' h₁ h₂; exact ⟨h₁, h₂⟩
    | cons p ps ih =>
      intro a a' h₁ h₂
      have e : p.2 * (4 * n) = 4 * (p.2 * n) := Nat.mul_left_comm _ _ _
      apply ih
      · dsimp only
        rw [e]
        generalize p.2 * n = x
        omega
      · dsimp only
        rw [e]
        generalize p.2 * n = x
        omega
  exact step phases 0 0 (Nat.le_refl 0) (Nat.zero_le _)

/-- The gate accepts every peak made of phases that each grow linearly,
standing on the fixed footprint every phase holds. The bound it replaced, drawn
above the size-0 document, did not: a linear phase overtaking a constant one
between `n` and `4n` read as a jump of any size, and failed a linear engine. -/
theorem growthWithin_phasePeak_covers (fixed : Nat) (phases : List (Nat × Nat)) (n : Nat) :
    growthWithin fixed (fixed + phasePeak phases n) (fixed + phasePeak phases (4 * n)) = true := by
  have := (phasePeak_between phases n).2
  unfold growthWithin growthBound
  exact decide_eq_true (by omega)

/-- The bound is eight, not four, for what an engine holds rather than what it
needs: a structure whose capacity doubles as it fills holds between its size
and twice it, so a run whose memory lies between a linear peak at `n` and
twice that peak at `4n` still passes. A bound of four would fail it: an array
full at `n` and just doubled at `4n` reads nearly 8x. -/
theorem growthWithin_doubled_covers (fixed : Nat) (phases : List (Nat × Nat)) (held : Nat → Nat)
    (n : Nat) (lo : phasePeak phases n ≤ held n)
    (hi : held (4 * n) ≤ 2 * phasePeak phases (4 * n)) :
    growthWithin fixed (fixed + held n) (fixed + held (4 * n)) = true := by
  have := (phasePeak_between phases n).2
  unfold growthWithin growthBound
  exact decide_eq_true (by omega)

/-- What the bound sees, exactly. A term quadratic in the document's size adds
some `q` at `n` units and `16q` at `4n`; added to a run's peaks it fails the
run exactly when `8q` exceeds the run's headroom, what eight times the `n`
build's memory leaves above the `4n` build's. A term `c·u²` therefore fails a
pair measured at `n` units once `c` exceeds the headroom over `8n²`
(`Growth.quadraticBytes`): the larger the pair, the smaller the term it sees. -/
theorem growthWithin_quadratic_exact (fixed small big q : Nat) (hs : fixed ≤ small)
    (hb : fixed ≤ big) :
    growthWithin fixed (small + q) (big + 16 * q) = true ↔
      8 * q + (big - fixed) ≤ growthBound * (small - fixed) := by
  unfold growthWithin growthBound
  constructor
  · intro h
    have := of_decide_eq_true h
    omega
  · intro h
    exact decide_eq_true (by omega)

/-- Eighth octaves of KiB: `floor(8 log2 KiB)`, and 0 under a KiB. -/
def halfClass (bytes : Nat) : Nat := Nat.log2 (bytes ^ 8 / 2 ^ 80)

theorem halfClass_monotone {a b : Nat} (h : a ≤ b) : halfClass a ≤ halfClass b := by
  unfold halfClass
  have hdiv : a ^ 8 / 2 ^ 80 ≤ b ^ 8 / 2 ^ 80 :=
    Nat.div_le_div_right (Nat.pow_le_pow_left h 8)
  by_cases ha : a ^ 8 / 2 ^ 80 = 0
  · simp [ha]
  · have hb : b ^ 8 / 2 ^ 80 ≠ 0 := by omega
    exact (Nat.le_log2 hb).2 (Nat.le_trans (Nat.log2_self_le ha) hdiv)

/-- Quarter octaves of KiB: class `k` holds artifacts from `2^(k/4)` KiB up to
the next quarter octave, every artifact under 1 KiB is class 0, and one class
is a 19% change — coarse, so a commit's ordinary drift seldom moves it and a
material change of weight always does. -/
def sizeClass (bytes : Nat) : Nat := halfClass bytes / 2

theorem sizeClass_monotone {a b : Nat} (h : a ≤ b) : sizeClass a ≤ sizeClass b :=
  Nat.div_le_div_right (halfClass_monotone h)

/-- The class an artifact reads against the class its baseline commits: the
committed one while the artifact stays inside it widened by an eighth of an
octave on each side, its own otherwise. Without the margin, an artifact a few
bytes under a boundary moves its item on any drift at all. -/
def heldClass (committed : Option Nat) (bytes : Nat) : Nat :=
  match committed with
  | some k => if 2 * k ≤ halfClass bytes + 1 ∧ halfClass bytes ≤ 2 * k + 2 then k else sizeClass bytes
  | none => sizeClass bytes

/-- Holding a class never lets a heavier artifact read lighter: the size
encoding still points one way. -/
theorem heldClass_monotone {committed : Option Nat} {a b : Nat} (h : a ≤ b) :
    heldClass committed a ≤ heldClass committed b := by
  have hh := halfClass_monotone h
  cases committed with
  | none => exact sizeClass_monotone h
  | some k =>
    simp only [heldClass, sizeClass]
    generalize halfClass a = x at *
    generalize halfClass b = y at *
    split <;> split <;> omega

/-- The KiB at which class `k` starts, to one decimal, for the provenance. -/
def classStartKiB (k : Nat) : String :=
  -- 2^(k/4) = 2^(k div 4) * 2^((k mod 4)/4); the quarter powers to four places.
  let quarter := #[10000, 11892, 14142, 16818][k % 4]!
  let tenths := (2 ^ (k / 4)) * quarter / 1000
  s!"{tenths / 10}.{tenths % 10}"

/-- The summary's peak, whether or not the run wrote an artifact. -/
def summaryPeak (stdout : String) : Option Nat :=
  (stdout.splitOn "\n").findSome? fun line =>
    match Lean.Json.parse line with
    | .ok j => if jsonStr j "event" == "summary" then jsonNat j "rssKiB" else none
    | .error _ => none

/-- The engine's fixed footprint: the least peak of `runs` runs that read no
document — the runtime and every module's initialized data, which stay
resident through every phase of every build, so every phase's memory stands on
it. Measured alone, before any build runs beside it. -/
def footprint (binary : System.FilePath) (dir : System.FilePath) (runs : Nat) :
    IO (Except String Nat) := do
  let s ← stage dir
  let mut least : Option Nat := none
  for _ in [0:runs] do
    let r ← IO.Process.output {
      cmd := binary.toString
      args := #["build", (s.root / "absent.tex").toString, "-o",
        (s.root / "out" / "absent.pdf").toString, "--porcelain"]
      env := sealedEnv s (dir / "cache") }
    match summaryPeak r.stdout with
    | some k => least := some ((least.map (min · k)).getD k)
    | none => return .error s!"a run that reads no document stated no peak: {r.stderr.trimAscii}"
  return match least with
    | some k => .ok k
    | none => .error "no footprint run"

/-- One family in one format at `n` units and `4n`, after a priming build:
each document built `runs` times — every repeat required to write the same
bytes — the least peak of each over the fixed footprint, and the larger
document's artifact. `pair` names the item: `rss-growth` from the gate size,
`rss-growth-16n` from four times it. -/
structure Growth where
  gen : String
  unit : String
  format : String
  pair : String
  n : Nat
  fixed : Nat
  small : Nat
  big : Nat
  smallWall : Nat
  bigWall : Nat
  bytes : Nat
  pages : Nat
deriving Inhabited

def Growth.key (g : Growth) : String := s!"{g.gen}/{g.format}"

def Growth.item (g : Growth) : String := s!"{g.key}/{g.pair}"

def Growth.within (g : Growth) : Bool := growthWithin g.fixed g.small g.big

/-- The ratio the bound reads, in hundredths: within it is at most 800. -/
def Growth.rssPct (g : Growth) : Nat := (g.big - g.fixed) * 100 / max (g.small - g.fixed) 1

def Growth.wallPct (g : Growth) : Nat := g.bigWall * 100 / max g.smallWall 1

/-- What the `4n` build may add, the `n` build unchanged, before the item
fails: the bound's slack, in KiB. -/
def Growth.headroomKiB (g : Growth) : Nat := growthBound * (g.small - g.fixed) - (g.big - g.fixed)

/-- The coefficient, in bytes per unit squared, above which a term quadratic
in the document's size fails the item: the headroom over `8n²`
(`growthWithin_quadratic_exact`). -/
def Growth.quadraticBytes (g : Growth) : Nat := g.headroomKiB * 1024 / (8 * g.n * g.n)

def measureGrowth (binary : System.FilePath) (dir : System.FilePath) (gen : Gen) (format : String)
    (runs fixed : Nat) : IO (Except String (Array Growth)) := do
  let s ← stage dir
  let cache := dir / "cache"
  let main ← s.write (gen.source gen.gate 0)
  if let .error e ← build binary s cache main format then return .error e
  let sizes := #[gen.gate, 4 * gen.gate] ++ (if gen.far then #[16 * gen.gate] else #[])
  let mut least : Array (Nat × Nat × Build) := #[]
  for size in sizes do
    let main ← s.write (gen.source size 0)
    let mut peak : Option Nat := none
    let mut wall : Option Nat := none
    let mut first : Option ByteArray := none
    let mut last : Build := default
    for _ in [0:runs] do
      match ← build binary s cache main format with
      | .error e => return .error e
      | .ok b =>
        if let some bytes := first then
          if bytes != b.artifact then
            return .error s!"{gen.name} {size} → {format}: a repeated build wrote different bytes"
        first := some b.artifact
        peak := some ((peak.map (min · b.rssKiB)).getD b.rssKiB)
        wall := some ((wall.map (min · b.wall)).getD b.wall)
        last := b
    least := least.push (peak.getD 0, wall.getD 0, last)
  let pairAt (k : Nat) (pair : String) : Growth :=
    let (small, smallWall, _) := least[k]!
    let (big, bigWall, b) := least[k + 1]!
    { gen := gen.name, unit := (gen.unit.dropEnd 1).toString, format, pair, n := sizes[k]!,
      fixed, small, big, smallWall, bigWall, bytes := b.artifact.size, pages := b.pages }
  return .ok (#[pairAt 0 "rss-growth"] ++ (if gen.far then #[pairAt 1 "rss-growth-16n"] else #[]))

/-- The fixed footprint, then every family in every format, `width` groups at
a time. Groups side by side disturb one another's milliseconds, which is why
nothing gates on them, and nudge one another's peaks, which the bound has the
slack for. -/
def measureAll (binary : System.FilePath) (root : System.FilePath) (runs width : Nat) :
    IO (Except String (Nat × Array Growth)) := do
  let fixed ← match ← footprint binary (root / "footprint") footprintRuns with
    | .ok k => pure k
    | .error e => return .error e
  let mut jobs : Array (Gen × String) := #[]
  for g in gens do
    for f in formats do jobs := jobs.push (g, f)
  let some first := jobs[0]? | return .ok (fixed, #[])
  let mut out : Array Growth := #[]
  let mut i := 0
  while i < jobs.size do
    let stop := min jobs.size (i + width)
    let mut batch := #[]
    for k in [i:stop] do
      let (g, f) := jobs[k]?.getD first
      batch := batch.push (← IO.asTask (prio := .dedicated)
        (measureGrowth binary (root / s!"{g.name}-{f}") g f runs fixed))
    for t in batch do
      match ← IO.wait t with
      | .ok (.ok gs) => out := out.append gs
      | .ok (.error e) => return .error e
      | .error e => return .error (toString e)
    i := stop
  return .ok (fixed, out)

/-! ## The report

The host's numbers: reported, recorded in the history, never gated. -/

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s.getD ((s.size + 1) / 2 - 1) 0

def padRight (s : String) (w : Nat) : String := s ++ "".pushn ' ' (w - s.length)

def padLeft (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s

def mib (kib : Nat) : String :=
  let tenths := kib * 10 / 1024
  s!"{tenths / 10}.{tenths % 10} MiB"

def kibOf (bytes : Nat) : String :=
  let tenths := bytes * 10 / 1024
  s!"{tenths / 10}.{tenths % 10} KiB"

def bytesText (bytes : Nat) : String :=
  if bytes < 1024 then s!"{bytes} B" else if bytes < 1048576 then kibOf bytes else mib (bytes / 1024)

/-- A reference document's builds: `runs` pairs of a cold build over an empty
application cache and a warm one over the cache it filled; medians, and the
warm builds' peak. -/
structure Timing where
  gen : String
  n : Nat
  format : String
  cold : Nat
  warm : Nat
  rssKiB : Nat
  bytes : Nat
  pages : Nat
  layoutMs : Nat
  losses : Array String
deriving Inhabited

def Timing.name (t : Timing) : String := s!"{t.gen}-{t.n}"

def timeReference (binary dir : System.FilePath) (gen : Gen) (format : String) (runs : Nat) :
    IO (Except String Timing) := do
  let s ← stage dir
  let main ← s.write (gen.source gen.reference 0)
  let mut colds := #[]
  let mut warms := #[]
  let mut peaks := #[]
  let mut layouts := #[]
  let mut last : Build := default
  for i in [0:runs] do
    let cache := dir / s!"cache-{i}"
    let cold ← match ← build binary s cache main format with
      | .ok b => pure b
      | .error e => return .error e
    let warm ← match ← build binary s cache main format with
      | .ok b => pure b
      | .error e => return .error e
    colds := colds.push cold.wall
    warms := warms.push warm.wall
    peaks := peaks.push warm.rssKiB
    layouts := layouts.push (((warm.phase? "layout").map (·.ms)).getD 0)
    last := warm
  return .ok { gen := gen.name, n := gen.reference, format, cold := median colds,
               warm := median warms, rssKiB := median peaks, bytes := last.artifact.size,
               pages := last.pages, layoutMs := median layouts, losses := last.losses }

/-- The next summary on the watcher's output, or `none` at its end. -/
def nextSummary (h : IO.FS.Handle) : IO (Option String) := do
  repeat
    let line ← h.getLine
    if line.isEmpty then return none
    if (line.splitOn "\"event\":\"summary\"").length > 1 then return some line
  return none

def waitFor (t : Task (Except IO.Error α)) (ms : Nat) : IO (Option α) := do
  let start ← IO.monoMsNow
  while !(← IO.hasFinished t) && (← IO.monoMsNow) - start < ms do
    IO.sleep 2
  if !(← IO.hasFinished t) then return none
  match ← IO.wait t with
  | .ok v => return some v
  | .error _ => return none

/-- Edit to artifact: the engine watching the reference document, the main
source replaced by its next revision (renamed into place, so the watcher never
reads half a file), and the time until the summary of the build that answers
it — the watcher's poll included, as a writer waits for it. Median over
`edits`, with the rebuilds' own milliseconds. -/
def editLatency (binary dir : System.FilePath) (gen : Gen) (format : String) (edits : Nat) :
    IO (Except String (Nat × Nat)) := do
  let s ← stage dir
  let cache := dir / "cache"
  let main ← s.write (gen.source gen.reference 0)
  if let .error e ← build binary s cache main format then return .error e
  let stem := ((System.FilePath.mk main).fileStem).getD main
  let child ← IO.Process.spawn {
    cmd := binary.toString
    args := #["build", (s.root / main).toString, "-o",
      (s.root / "out" / (stem ++ "." ++ format)).toString, "--porcelain", "--watch"]
    env := sealedEnv s cache
    stdin := .null, stdout := .piped, stderr := .null }
  -- The watcher dies with the run, whatever the edits throw.
  try
    let next : IO (Option String) := do
      let t ← IO.asTask (prio := .dedicated) (nextSummary child.stdout)
      return (← waitFor t 300000).join
    let mut result : Except String (Nat × Nat) := .error s!"{gen.name} → {format}: no first build"
    if (← next).isSome then
      let mut latencies := #[]
      let mut rebuilds := #[]
      let mut lost := false
      for k in [1:edits + 1] do
        IO.sleep 1100
        let tmp := s.root / (main ++ ".next")
        IO.FS.writeFile tmp (((gen.source gen.reference k)[0]?.map (·.2)).getD "")
        let t0 ← IO.monoMsNow
        IO.FS.rename tmp (s.root / main)
        match ← next with
        | none =>
          lost := true
          break
        | some line =>
          latencies := latencies.push ((← IO.monoMsNow) - t0)
          if let .ok j := Lean.Json.parse line then
            rebuilds := rebuilds.push ((jsonNat j "ms").getD 0)
      result := if lost then .error s!"{gen.name} → {format}: an edit went unanswered"
        else .ok (median latencies, median rebuilds)
    return result
  finally
    try child.kill catch _ => pure ()
    discard <| child.wait

/-- `perf`, where the host has it and lets it count this user's instructions. -/
def perfTool : IO (Option String) := do
  try
    let found ← IO.Process.output { cmd := "sh", args := #["-c", "command -v perf"] }
    let path := found.stdout.trimAscii.toString
    if found.exitCode != 0 || path.isEmpty then return none
    let probe ← IO.Process.output
      { cmd := path, args := #["stat", "-x", ",", "-e", "instructions:u", "--", "true"] }
    return if probe.exitCode == 0 then some path else none
  catch _ => return none

/-- User-space instructions retired by `runs` warm builds after a priming one:
their median, and their spread (largest less least) in basis points of the
least. Close to the same count run to run however loaded the host is, which
milliseconds are not; the spread is the noise the band stands above. Each
counted build must load the very faces, out of as many scanned, as the priming
one did, so a wrapper that leaks the host into the build fails here rather
than inflating the count. -/
def instructions (perf : String) (binary dir : System.FilePath) (gen : Gen) (format : String)
    (runs : Nat) : IO (Except String (Nat × Nat)) := do
  let s ← stage dir
  let cache := dir / "cache"
  let main ← s.write (gen.source gen.reference 0)
  let primed ← match ← build binary s cache main format with
    | .ok b => pure b
    | .error e => return .error e
  let mut counts : Array Nat := #[]
  for _ in [0:runs] do
    match ← build binary s cache main format (perf := some perf) with
    | .error e => return .error e
    | .ok b =>
      if b.faces != primed.faces then
        return .error s!"{gen.name} → {format}: under perf the build loaded {facesText b.faces}, \
unsealed, where the sealed build loaded {facesText primed.faces}"
      let some k := b.instructions
        | return .error s!"{gen.name} → {format}: perf counted no instructions"
      counts := counts.push k
  let some first := counts[0]? | return .error s!"{gen.name} → {format}: no counted build"
  let least := counts.foldl min first
  let most := counts.foldl max first
  return .ok (median counts, (most - least) * 10000 / max least 1)

/-- Every corpus fixture in each format, `runs` builds each, in place, sealed,
over one primed cache: the median of the peaks its summaries state, whether or
not the fixture wrote its artifact, and the median of its milliseconds. -/
def corpusPeaks (binary dir : System.FilePath) (runs : Nat) :
    IO (Array (String × String × Nat × Nat)) := do
  let s ← stage dir
  let cache := dir / "cache"
  let corpus ← IO.FS.realPath "testdata/corpus"
  let mut names : Array String := #[]
  for e in ← corpus.readDir do
    if e.fileName.endsWith ".tex" then names := names.push e.fileName
  names := names.qsort (· < ·)
  let mut out := #[]
  for name in names do
    let stem := (name.dropEnd 4).toString
    for format in formats do
      let mut peaks : Array Nat := #[]
      let mut mss : Array Nat := #[]
      for _ in [0:runs] do
        let r ← IO.Process.output {
          cmd := binary.toString
          args := #["build", (corpus / name).toString, "-o",
            (s.root / "out" / (stem ++ "." ++ format)).toString, "--porcelain"]
          env := sealedEnv s cache }
        let summary := (r.stdout.splitOn "\n").findSome? fun line =>
          match Lean.Json.parse line with
          | .ok j => if jsonStr j "event" == "summary" then
              (jsonNat j "rssKiB").map fun k => (k, (jsonNat j "ms").getD 0)
            else none
          | .error _ => none
        if let some (k, ms) := summary then
          peaks := peaks.push k
          mss := mss.push ms
      if !peaks.isEmpty then out := out.push (stem, format, median peaks, median mss)
  return out

/-- Targets a reference document's warm build is reported against, never
gated: the audit's budgets for a deck and for a long styled report. The
invented deck is lighter than a working deck — no pictures, no figures, one
listing in four frames — so its verdict is a floor, not a deck's. -/
def budgets : List (String × String × Nat) :=
  [("deck", "pdf", 400), ("deck", "html", 1200), ("report", "pdf", 2500)]

def historyPath : System.FilePath := "testdata/perf/documents.tsv"

def historyHeader : Array String := #[
  "# Document-cost history: one run per block, appended by \
`lake env lean --run scripts/bench.lean --doc-cost --record` from a clean checkout \
of a commit main holds; never edited by hand.",
  "# Format: scripts/PerfHistory.lean. Items: \
<document>-<size>/<format>/{cold,warm,rss,bytes,layout,edit,rebuild,instructions}, \
growth/footprint/rss, growth/<family>/<format>/{rss,wall}[-16n], corpus/<fixture>/<format>/rss, \
corpus/all/<format>/ms.",
  "# Sealed builds (scripts/DocBench.lean): staged corpus fonts and images, no tool on PATH, \
empty HOME. Host-dependent; nothing here gates."]

/-- A ratio in hundredths, as `3.8x`. -/
def times (pct : Nat) : String := s!"{pct / 100}.{pct % 100 / 10}x"

/-- `num / den` to one decimal. -/
def tenths (num den : Nat) : String :=
  let t := num * 10 / max den 1
  s!"{t / 10}.{t % 10}"

/-- A count in millions, to one decimal. -/
def millions (n : Nat) : String := tenths n 1000000 ++ "M"

def say (line : String) : IO Unit := do
  IO.println line
  (← IO.getStdout).flush

/-- Why `--record` may not write `history` from this run, if it may not. A row
names a committed tree, and the committed history only trees `main` holds,
built from themselves: a branch's commits vanish when it lands rebased, and a
saved or stale binary measures some other tree. -/
def recordRefusal (binary : System.FilePath) (dirty : Bool) (history : System.FilePath) :
    IO (Option String) := do
  let committed ← IO.FS.realPath historyPath
  let scratch ← if ← history.pathExists then pure ((← IO.FS.realPath history) != committed)
    else pure true
  if scratch then return none
  if dirty then
    return some s!"--record writes {historyPath} only for a committed tree; commit or set aside \
the changes first, or name a scratch history with --history <path>"
  unless ← PerfHistory.onMain do
    return some s!"--record writes {historyPath} only from a commit main holds, so each row \
names a tree that outlives the branch that measured it; measure a branch made from main, or \
name a scratch history with --history <path>"
  let own ← IO.FS.realPath ".lake/build/bin/leantex"
  if (← IO.FS.realPath binary) != own then
    return some s!"--record writes {historyPath} only for the tree's own build, {own}"
  let fresh ← IO.Process.output { cmd := "lake", args := #["build", "--no-build", "leantex"] }
  if fresh.exitCode != 0 then
    return some "the tree's leantex is older than its sources; run lake build leantex, then record"
  return none

/-- One measurement against the earlier run's: `old → new (±x.xx%)`, or
nothing when that run did not measure it. -/
def against (base : Array PerfHistory.Row) (item : String) (now : Nat) (fmt : Nat → String) :
    Option String :=
  (base.find? (·.item == item)).map fun r =>
    let change := ((PerfHistory.changeBp r.value now).map fun c => s!" ({PerfHistory.bpText c})").getD ""
    s!"{fmt r.value.toNat} → {fmt now}{change}"

def runReport (binary : System.FilePath) (runs : Nat) (record : Bool) (history : System.FilePath) :
    IO UInt32 := do
  let fail (why : String) : IO UInt32 := do
    IO.eprintln s!"doc-cost: {why}"
    return 1
  let some run ← PerfHistory.now | fail "the system clock gave no UTC time"
  let some commit ← PerfHistory.commit | fail "git could not name the measured tree"
  let dirty := commit.endsWith "+"
  let some binaryKey ← PerfHistory.binaryKey binary
    | fail s!"could not take the SHA-256 of {binary}: neither sha256sum nor shasum answered"
  let host ← PerfHistory.host
  if record then
    if let some why ← recordRefusal binary dirty history then return ← fail why
  let past ← match ← PerfHistory.read history with
    | .ok h => pure h
    | .error e => return ← fail e
  let base := PerfHistory.lastRun past.rows host run
  let load := ((← (IO.FS.readFile "/proc/loadavg").toBaseIO).toOption.getD "unavailable").trimAscii
  say s!"doc-cost report v2: {run}; tree {commit}{if dirty then " (uncommitted changes)" else ""}; \
binary {binaryKey} ({binary}); N={runs}"
  say s!"host: {host}; load {load}"
  match base[0]? with
  | some b => say s!"against the last run on this host class in {history}: {b.run}, tree {b.commit}, \
binary {b.binary}{if b.binary == binaryKey then " — the same binary, so what moved is the host" else ""}"
  | none => say s!"no earlier run on this host class in {history}: nothing to compare against"
  say "Sealed builds: staged corpus fonts and images, no tool on PATH, empty HOME. \
Shared-host milliseconds are provisional."
  let row := fun (item : String) (value : Nat) (unit : String) =>
    ({ run, commit, binary := binaryKey, host, item, value := value, unit } : PerfHistory.Row)
  let ms := fun (v : Nat) => s!"{v} ms"
  let perf ← perfTool
  IO.FS.withTempDir fun dir => do
    let mut rows : Array PerfHistory.Row := #[]
    let mut band : Array (String × Bool × String) := #[]
    say ""
    say "reference documents (median of N; cold = empty application cache):"
    for g in gens do
      for f in formats do
        let t ← match ← timeReference binary (dir / s!"time-{g.name}-{f}") g f runs with
          | .ok t => pure t
          | .error e => return ← fail e
        let (edit, rebuild) ← match ← editLatency binary (dir / s!"edit-{g.name}-{f}") g f runs with
          | .ok v => pure v
          | .error e => return ← fail e
        let instr ← match perf with
          | some p => match ← instructions p binary (dir / s!"perf-{g.name}-{f}") g f runs with
            | .ok v => pure (some v)
            | .error e => return ← fail e
          | none => pure none
        let budget := (budgets.find? fun (n, fmt, _) => n == g.name && fmt == f).map (·.2.2)
        let verdict := match budget with
          | some b => s!"  budget {b} ms: {if t.warm ≤ b then "within" else s!"over by {t.warm - b} ms"}"
          | none => ""
        say <| String.intercalate "  " [s!"  {padRight s!"{t.name} {f}" 18}",
          s!"cold {padLeft (toString t.cold) 6} ms", s!"warm {padLeft (toString t.warm) 6} ms",
          s!"edit {padLeft (toString edit) 6} ms (rebuild {rebuild})",
          s!"peak {padLeft (mib t.rssKiB) 10}", padLeft (kibOf t.bytes) 11,
          s!"{t.pages} pages{verdict}"]
        if !t.losses.isEmpty then say s!"    losses: {t.losses}"
        if g.name == "report" && f == "pdf" && t.pages > 0 then
          say s!"    layout {t.layoutMs} ms over {t.pages} pages: \
{tenths t.layoutMs t.pages} ms per page"
        let key := t.name ++ "/" ++ f ++ "/"
        if let some (k, spread) := instr then
          say s!"    instructions:u (warm, perf, {if runs > 1 then s!"median of {runs}, spread \
{PerfHistory.bpMag spread}" else "one build"}) {k}"
          if let some r := base.find? (·.item == key ++ "instructions") then
            let change := ((PerfHistory.changeBp r.value k).map PerfHistory.bpText).getD "?"
            band := band.push (key ++ "instructions", PerfHistory.withinBand r.value k, change)
        let readings : List (String × Option String) := [
            ("warm", against base (key ++ "warm") t.warm ms),
            ("cold", against base (key ++ "cold") t.cold ms),
            ("edit", against base (key ++ "edit") edit ms),
            ("peak", against base (key ++ "rss") t.rssKiB mib),
            ("bytes", against base (key ++ "bytes") t.bytes kibOf),
            ("instructions", instr.bind fun (k, _) => against base (key ++ "instructions") k millions)]
        let vs := readings.filterMap fun (n, v) => v.map (s!"{n} {·}")
        if !vs.isEmpty then say s!"    vs earlier: {String.intercalate "; " vs}"
        rows := rows ++ #[row (key ++ "cold") t.cold "ms", row (key ++ "warm") t.warm "ms",
          row (key ++ "rss") t.rssKiB "KiB", row (key ++ "bytes") t.bytes "B",
          row (key ++ "layout") t.layoutMs "ms", row (key ++ "edit") edit "ms",
          row (key ++ "rebuild") rebuild "ms"]
        if let some (k, _) := instr then rows := rows.push (row (key ++ "instructions") k "instr")
    say ""
    say s!"growth, n → 4n and, where it is cheap, 4n → 16n (least of {gateRuns} builds each; \
the doccost tier gates the peak, never the milliseconds):"
    let (fixed, growth) ← match ← measureAll binary (dir / "growth") gateRuns 4 with
      | .ok r => pure r
      | .error e => return ← fail e
    say s!"  fixed footprint (a run that reads no document, least of {footprintRuns}): {mib fixed}\
{((against base "growth/footprint/rss" fixed mib).map (s!"; vs earlier {·}")).getD ""}"
    rows := rows.push (row "growth/footprint/rss" fixed "KiB")
    for g in growth do
      let far := if g.pair == "rss-growth" then "" else "-16n"
      let key := s!"growth/{g.gen}/{g.format}/"
      say <| String.intercalate "  " [s!"  {padRight s!"{g.gen} {g.format} {g.n}→{4 * g.n}" 22}",
        s!"least peaks {padLeft (mib g.small) 10} → {padLeft (mib g.big) 10}:",
        s!"{times g.rssPct} above the footprint \
({if g.within then s!"within the bound; fails once the larger build holds {mib g.headroomKiB} \
more, or a quadratic term exceeds {bytesText g.quadraticBytes} per {g.unit}²" else "OVER the bound"})",
        s!"wall {g.smallWall} → {g.bigWall} ms ({times g.wallPct})\
{((against base (key ++ "rss" ++ far) g.rssPct times).map (s!"; peak growth vs earlier {·}")).getD ""}"]
      rows := rows ++ #[row (key ++ "rss" ++ far) g.rssPct "pct",
        row (key ++ "wall" ++ far) g.wallPct "pct"]
    say ""
    say s!"peak resident set size per corpus fixture (median of N builds each):"
    let peaks ← corpusPeaks binary (dir / "corpus") runs
    for f in formats do
      let mine := peaks.filter (·.2.1 == f)
      let sorted := mine.qsort (fun a b => a.2.2.1 > b.2.2.1)
      let total := mine.foldl (fun t p => t + p.2.2.2) 0
      let mid := median (mine.map (·.2.2.1))
      say s!"  {f}: {mine.size} fixtures, median peak {mib mid}, all builds {total} ms\
{((against base s!"corpus/all/{f}/ms" total ms).map (s!" (vs earlier {·})")).getD ""}; highest:"
      for (name, _, k, t) in sorted.toList.take 5 do
        say s!"    {padRight name 24} {padLeft (mib k) 10}  {padLeft (toString t) 6} ms"
      let moved := mine.filterMap fun (name, _, k, _) =>
        (base.find? (·.item == s!"corpus/{name}/{f}/rss")).bind fun r =>
          (PerfHistory.changeBp r.value k).bind fun c =>
            if c.natAbs > 1000 then some s!"{name} {PerfHistory.bpText c}" else none
      if !moved.isEmpty then
        say s!"    peaks that moved more than 10% since the earlier run: \
{String.intercalate ", " moved.toList}"
      for (name, _, k, _) in mine do rows := rows.push (row s!"corpus/{name}/{f}/rss" k "KiB")
      rows := rows.push (row s!"corpus/all/{f}/ms" total "ms")
    if let some b := base[0]? then
      let outside := band.filter (!·.2.1)
      say ""
      say s!"instructions:u against {b.run}: {band.size - outside.size} of {band.size} within \
±{PerfHistory.bandBp / 100}%{if outside.isEmpty then "" else "; outside: " ++
        String.intercalate ", " (outside.toList.map fun (i, _, c) => s!"{i} {c}")}"
    if record then
      IO.FS.createDirAll "testdata/perf"
      match ← PerfHistory.append history historyHeader rows with
      | .ok n => say s!"\nrecorded {n} rows to {history}"
      | .error e => return ← fail e
    return 0

end DocBench
