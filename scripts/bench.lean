import Lean.Data.Json
import LeanTex.Cli.ConvCache
import LeanTex.Core.Image

/-
Benchmark leantex against lualatex on the bench corpus, median of `N` runs (default 5), or the
measurement a flag selects; never a gate. `LEANTEX_BENCH_BINARY` names a saved compiler.
Usage: lake build && lake env lean --run scripts/bench.lean [--boundary-only | --concurrency-only | --slides-only | --slides-compressed-only | --slides-selftest | --decode-only | --listings-only | --bib-only | --passes-only | --svg-only | --pdf-pages-only <f.pdf> | --faces-only <f.pdf>... | --doc-cost [--record] [--history <path>]]
-/

def compiler : IO String := do
  return (← IO.getEnv "LEANTEX_BENCH_BINARY").getD ".lake/build/bin/leantex"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- `--doc-cost`: `scripts/doccost.lean --bench` with the remaining arguments, after
building what it imports and the engine it measures. -/
def docCost (rest : List String) : IO UInt32 := do
  let engine := if (← IO.getEnv "LEANTEX_BENCH_BINARY").isSome then #[] else #["leantex"]
  let targets := engine ++ #["scripts.doccost"]
  let built ← (← IO.Process.spawn { cmd := "lake", args := #["build", "-q"] ++ targets }).wait
  if built != 0 then die s!"lake build {String.intercalate " " targets.toList} failed"
  let report ← IO.Process.spawn
    { cmd := "lake", args := #["env", "lean", "--run", "scripts/doccost.lean", "--bench"] ++
        rest.toArray }
  report.wait

def runMs (cmd : String) (args : Array String) : IO Nat := do
  let t0 ← IO.monoMsNow
  let out ← IO.Process.output { cmd, args }
  let t1 ← IO.monoMsNow
  if out.exitCode != 0 then
    die s!"benchmark command failed: {cmd} {String.intercalate " " args.toList}"
  return t1 - t0

def median (times : Array Nat) : Nat :=
  let sorted := times.qsort (· < ·)
  sorted.getD ((sorted.size + 1) / 2 - 1) 0

def padRight (s : String) (w : Nat) : String :=
  s ++ String.ofList (List.replicate (w - s.length) ' ')

def padLeft (s : String) (w : Nat) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

def bench (n : Nat) (label : String) (cmd : String) (args : Array String) : IO Unit := do
  let mut times : Array Nat := #[]
  for _ in [0:n] do
    times := times.push (← runMs cmd args)
  IO.println s!"{padRight label 42} {padLeft (toString (median times)) 6} ms (median of {n})"

def hasCmd (cmd : String) (args : Array String := #["--version"]) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args }
    return out.exitCode == 0
  catch _ =>
    return false

/-- An invented `.bib` of `n` entries, half sharing their authors and year, so plainnat's
label letters are in play. -/
def bibOf (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    let (au, yr) := if i % 2 == 0 then ("Alex Placeholder and Bryn Example", 2019)
      else (s!"Casey Invented{i} and Drew Sample{i}", 2000 + i % 20)
    out := out ++ s!"@misc\{k{i}, author = \{{au}}, title = \{Invented entry number {i}},\n\
      year = \{{yr}}}\n"
  return out

/-- An invented `.bib` of `n` entries written as a real one is: accented names,
case-protected words, formulas, dashes, page ranges, DOIs, and a third sharing authors and
year. -/
def bibRichOf (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    let au := if i % 3 == 0 then "M{\\\"u}ller, Ada and {\\'E}tienne Placeholder"
      else s!"Casey Invented{i} and de la Sample{i}, Drew"
    let yr := if i % 3 == 0 then 2019 else 1990 + i % 30
    out := out ++ s!"@article\{r{i}, author = \{{au}}, title = \{The \{DNA} of $\\alpha$-values \
      --- part {i}}, journal = \{Journal of Invented Results {i % 7}}, year = \{{yr}},\n\
      volume = \{{i % 40}}, pages = \{{i}--{i + 9}}, doi = \{10.0000/example.{i}}}\n"
  return out

/-- An invented `.bib` of `n` entries whose every field the document's elaborator reads,
over four entry types. -/
def bibHeavyOf (n : Nat) : String := Id.run do
  let given := #["Ann", "Bo", "Cy", "Di", "Ed", "Flo", "Gil", "Ray"]
  let family := #["Alpha", "Beta", "Gamma", "Delta", "Iota", "Sigma", "Theta", "Xi"]
  let mut out := ""
  for i in [0:n] do
    let au := s!"{given[i % 8]!} {family[(i / 8) % 8]!} and {given[(i + 3) % 8]!} {family[(i + 5) % 8]!}"
    let head := s!"author = \{{au}}, title = \{On \\emph\{Placeholder} Number {i} and \{\\'E}tudes \
      with $x^\{{i}}$}, year = \{{1990 + i % 30}}"
    let note := "note = {See also \\textit{notes} \\& more}"
    out := out ++ match i % 4 with
      | 0 => s!"@misc\{h{i}, {head}, howpublished = \{\\url\{https://example.org/item{i}}}, {note}}\n"
      | 1 => s!"@book\{h{i}, {head}, publisher = \{Example Press}, address = \{Exampleville}, {note}}\n"
      | 2 => s!"@inproceedings\{h{i}, {head}, booktitle = \{Proceedings of the Invented Workshop}, \
          pages = \{{i}--{i + 5}}, {note}}\n"
      | _ => s!"@article\{h{i}, {head}, journal = \{Journal of Invented \{R}esults}, \
          volume = \{{i % 40}}, number = \{{i % 12}}, pages = \{{i}--{i + 10}}, {note}}\n"
  return out

/-- An invented `.bib` of `n` entries each citing the next in its `note`, completed entry
by entry. -/
def bibChainOf (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    let next := if i + 1 < n then s!" Continued in \\cite\{c{i + 1}}." else ""
    out := out ++ s!"@misc\{c{i}, author = \{Ann Invented{i}}, title = \{Part {i}},\n\
      year = \{{2000 + i % 20}}, note = \{Note {i}.{next}}}\n"
  return out

/-- The milliseconds `-v` reports for a phase. -/
def phaseMs (phase log : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun l =>
    if l.startsWith (phase ++ ": ") then ((l.splitOn "(").getLast?.bind fun t =>
      ((t.splitOn " ms").head?).bind (·.trimAscii.toString.toNat?)) else none

def bibPhaseMs (log : String) : Option Nat := phaseMs "bib" log

/-- The reference-list phase over `entries` invented entries, all listed under plainnat's
`\nocite{*}`: the median of `n` runs. -/
def benchBib (n : Nat) (entries : Nat) (label : String := "plainnat")
    (bib : Nat → String := bibOf)
    (doc : String := "\\documentclass{article}\n\\usepackage{natbib}\n\\bibliographystyle{plainnat}\n\
      \\begin{document}\nAlpha words \\citep{k0}.\n\\nocite{*}\n\\bibliography{refs}\n\
      \\end{document}\n") : IO Nat := do
  let leantex ← compiler
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "refs.bib") (bib entries)
  IO.FS.writeFile (dir / "scale.tex") doc
  let mut times : Array Nat := #[]
  let src := (dir / "scale.tex").toString
  let pdf := (dir / "scale.pdf").toString
  for _ in [0:n] do
    let out ← IO.Process.output { cmd := leantex, args := #["-v", "build", src, "-o", pdf] }
    if out.exitCode != 0 then die s!"benchmark command failed: {leantex} on {entries} entries"
    match bibPhaseMs (out.stdout ++ out.stderr) with
    | some ms => times := times.push ms
    | none => die "no bib phase in the -v report"
  IO.FS.removeDirAll dir
  let ms := median times
  IO.println s!"{padRight s!"leantex  bib phase, {label}, {entries} entries" 42} {padLeft (toString ms) 6} ms (median of {n})"
  return ms

/-- An invented document of about `mib` MiB, its words ASCII or accented, its lines ending
at LF or CR LF. -/
def decodeDoc (accented crlf : Bool) (mib : Nat) : String := Id.run do
  let words := if accented then #["café", "crème", "naïve", "déjà", "señor", "über"]
    else #["lorem", "ipsum", "dolor", "sitam", "elita", "sedut"]
  let nl := if crlf then "\r\n" else "\n"
  let target := mib * 1024 * 1024
  let mut out := s!"\\documentclass\{article}{nl}\\begin\{document}{nl}"
  for i in [0:target] do
    if out.utf8ByteSize ≥ target then break
    let gap := if i % 120 == 119 then nl ++ nl else if i % 12 == 11 then nl else " "
    out := out ++ words.getD (i % words.size) "" ++ gap
  return out ++ s!"\\end\{document}{nl}"

/-- The milliseconds `-v` reports for the decode phase, `decode` or the older `utf8`. -/
def decodePhaseMs (log : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun l =>
    if l.startsWith "decode: " || l.startsWith "utf8: " then ((l.splitOn "(").getLast?.bind
      fun t => ((t.splitOn " ms").head?).bind (·.trimAscii.toString.toNat?)) else none

/-- The decode phase over an invented 3 MiB document of each shape: the median of `n` runs
of `-v dump`. -/
def benchDecode (n : Nat) : IO Unit := do
  let leantex ← compiler
  let dir ← IO.FS.createTempDir
  let src := (dir / "decode.tex").toString
  for (accented, crlf, label) in [(false, false, "ASCII LF"), (false, true, "ASCII CR LF"),
      (true, false, "accented LF"), (true, true, "accented CR LF")] do
    IO.FS.writeFile src (decodeDoc accented crlf 3)
    let mut times : Array Nat := #[]
    for _ in [0:n] do
      let child ← IO.Process.spawn
        { cmd := leantex, args := #["-v", "dump", src], stdout := .null, stderr := .piped }
      let err ← child.stderr.readToEnd
      if (← child.wait) != 0 then die s!"benchmark command failed: {leantex} dump, {label}"
      match decodePhaseMs err with
      | some ms => times := times.push ms
      | none => die "no decode phase in the -v report"
    IO.println s!"{padRight s!"leantex  decode 3 MiB, {label}" 42} \
{padLeft (toString (median times)) 6} ms (median of {n})"
  IO.FS.removeDirAll dir

/-- Listings in every natively lexed language: the invented highlight snippets, each a
minted listing, `copies` times over. -/
def benchListings (n copies : Nat) : IO Unit := do
  let leantex ← compiler
  let root : System.FilePath := "testdata/highlight/snippets"
  let mut body := ""
  for k in [0:copies] do
    body := body ++ s!"\\section\{Listings, copy {k}}\n"
    for d in (← root.readDir).qsort (·.fileName < ·.fileName) do
      for f in (← d.path.readDir).qsort (·.fileName < ·.fileName) do
        let src ← IO.FS.readFile f.path
        body := body ++ "\\begin{minted}{" ++ d.fileName ++ "}\n" ++ src
        body := body ++ "\\end{minted}\n"
  IO.FS.withTempDir fun dir => do
    let input := dir / "listings.tex"
    IO.FS.writeFile input ("\\documentclass{article}\n\\usepackage{minted}\n" ++
      "\\setminted{style=friendly}\n\\begin{document}\n" ++ body ++ "\\end{document}\n")
    bench n s!"leantex  listings, {copies} copies (PDF)" leantex
      #["-q", "build", input.toString, "-o", (dir / "listings.pdf").toString]
    bench n s!"leantex  listings, {copies} copies (HTML)" leantex
      #["-q", "build", input.toString, "-o", (dir / "listings.html").toString]

/-- The median `elab` and `layout` phases of `n` builds of a document holding one minted
listing; a build past two minutes is a failure. -/
def listingPhasesMs (n : Nat) (label lang body : String) : IO (Nat × Nat) := do
  let leantex ← compiler
  IO.FS.withTempDir fun tmp => do
    let src := tmp / "long.tex"
    IO.FS.writeFile src ("\\documentclass{article}\n\\usepackage{minted}\n\\begin{document}\n" ++
      "\\begin{minted}{" ++ lang ++ "}\n" ++ body ++ "\\end{minted}\n\\end{document}\n")
    let mut elabs : Array Nat := #[]
    let mut layouts : Array Nat := #[]
    for _ in [0:n] do
      let out ← IO.Process.output
        { cmd := "timeout", args := #["120", leantex, "-v", "build", src.toString, "-o",
            (tmp / "long.pdf").toString] }
      if out.exitCode == 124 then die s!"{label}: the build outlasted 120 s"
      if out.exitCode != 0 then die s!"benchmark command failed: {leantex} on {label}"
      match phaseMs "elab" (out.stdout ++ out.stderr), phaseMs "layout" (out.stdout ++ out.stderr) with
      | some e, some l =>
        elabs := elabs.push e
        layouts := layouts.push l
      | _, _ => die "no elab or layout phase in the -v report"
    let (e, l) := (median elabs, median layouts)
    IO.println s!"{padRight s!"leantex  elab, {label}" 42} {padLeft (toString e) 6} ms (median of {n})"
    IO.println s!"{padRight s!"leantex  layout, {label}" 42} {padLeft (toString l) 6} ms (median of {n})"
    return (e, l)

/-- The median `elab` and `layout` phases of a document holding one Python listing of
`lines` lines. -/
def listingElabMs (n lines : Nat) : IO (Nat × Nat) := do
  let mut pool : Array String := #[]
  let dir : System.FilePath := "testdata/highlight/snippets/python"
  for f in (← dir.readDir).qsort (·.fileName < ·.fileName) do
    pool := pool ++ ((← IO.FS.readFile f.path).splitOn "\n").toArray
  let mut body := ""
  for i in [0:lines] do
    body := body ++ (pool.getD (i % max pool.size 1) "").trimAscii.toString
    body := body ++ "\n"
  listingPhasesMs n s!"one {lines}-line listing" "python" body

/-- Invented adversarial listings of size proportional to `len`, in the shapes that can
make a lexer, painting or setting superlinear. -/
def adversarialListings (len : Nat) : List (String × String × String) :=
  let rep (s : String) (k : Nat) : String := String.join (List.replicate k s)
  let lines (s : String) : String := rep (s ++ "\n") 8
  [("console", "prompt", lines (rep "a" (len / 2) ++ rep "@a" (len / 4) ++ "\n" ++
      "$ fetch\n[" ++ rep "{\"k\":[0],\"v\":\"x\"}," (len / 20) ++ "]\n" ++ rep "a" len)),
   ("bash", "heredoc", lines ("cat <<" ++ rep "a" (len / 2) ++ "\n" ++
      rep (rep "a" (len / 4) ++ "b\n") 2)),
   ("bash", "heredocs", String.join ((List.range (2 * len)).map fun i =>
      "cat <<q" ++ toString i ++ "z\n")),
   ("lean4", "nesting", lines (rep "/-" (len / 2) ++ rep "-/" (len / 2))),
   ("python", "brackets", lines ("x = " ++ rep "(" (len / 2) ++ rep ")" (len / 2))),
   ("python", "blank lines", lines (rep "   \n" (len / 2) ++ "x = 1")),
   ("python", "open docstring", rep " \n" len ++ "\"\"\"" ++ rep "x\n" len),
   ("python", "format keys", lines (rep "s = '{a['\n" (len / 4))),
   ("python", "format names", lines ("s = '" ++ rep "{a[" (len / 6) ++ "]" ++ rep ".b" (len / 4) ++ "'")),
   ("python", "format widths", lines ("s = '" ++ rep "{a[" (len / 6) ++ "]:" ++ rep "0" (len / 2) ++ "'")),
   ("python", "named escapes", lines ("s = '" ++ rep "\\N{" (len / 3))),
   ("python", "long line", lines (rep "x " (len / 2))),
   ("lean4", "long line", lines (rep "x " (len / 2))),
   ("console", "long command", lines ("$ " ++ rep "x " (len / 2))),
   ("text", "long line", lines (rep "x " (len / 2))),
   ("text", "tabbed line", lines (rep "x\t" (len / 2)))]
/-- A repeated image deck, whose builds must not re-encode the embedded font programs for
each closure check. -/
def benchImageDeck (n frames : Nat) : IO Unit := do
  let leantex ← compiler
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  let image ← IO.FS.readBinFile "testdata/corpus/rects.png"
  IO.FS.withTempDir fun dir => do
    IO.FS.writeBinFile (dir / "figure.png") image
    let mut source := "\\documentclass{beamer}\n\\usetheme{moloch}\n" ++
      "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Open Sans\" }\n" ++
      "\\begin{document}\n"
    for i in [0:frames] do
      source := source ++ "\\begin{frame}{Repeated figure " ++ toString i ++ "}\n" ++
        "\\includegraphics[width=0.25\\textwidth,alt={Invented color grid}]{figure.png}\n" ++
        "\\end{frame}\n"
    source := source ++ "\\end{document}\n"
    let input := dir / "deck.tex"
    IO.FS.writeFile input source
    bench n s!"leantex  image deck, {frames} frames (HTML)" leantex
      #["-q", "build", input.toString, "-o", (dir / "deck.html").toString]

/-- The milliseconds `-v` reports for its `images` phase. -/
def imagesPhaseMs (log : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun l =>
    if l.startsWith "images: " then ((l.splitOn "(").getLast?.bind fun t =>
      ((t.splitOn " ms").head?).bind (·.trimAscii.toString.toNat?)) else none

/-- SVG figures in a document, each a distinct invented source, built to PDF and HTML cold
and warm: each run's wall time and `images` phase. -/
def benchSvg (n figures : Nat) : IO Unit := do
  let leantex ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  let chart ← IO.FS.readFile "testdata/corpus/figures/chart.svg"
  let pulse ← IO.FS.readBinFile "testdata/corpus/figures/pulse.svg"
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "figures")
    let mut body := ""
    for i in [0:figures] do
      let digits := String.ofList (Nat.toDigits 16 ((0x1f77b4 + 4099 * (i + 1)) % 0x1000000))
      let shade := "#" ++ "".pushn '0' (6 - digits.length) ++ digits
      IO.FS.writeFile (dir / "figures" / s!"chart{i}.svg") (chart.replace "#1f77b4" shade)
      body := body ++ s!"\\includegraphics[width=0.6\\textwidth,alt=\{Invented chart {i}}]\{figures/chart{i}.svg}\n\n"
    IO.FS.writeBinFile (dir / "figures" / "pulse.svg") pulse
    body := body ++ "\\includegraphics[width=0.4\\textwidth,alt={An invented pulse}]{figures/pulse.svg}\n"
    IO.FS.writeFile (dir / "svg.tex")
      ("\\documentclass{article}\n\\fonts{ dir = \"" ++ fonts.toString ++
        "\", body = \"Source Serif Pro\", sans = \"Fira Sans\" }\n\\begin{document}\n" ++ body ++
        "\\end{document}\n")
    for format in ["pdf", "html"] do
      for warm in [false, true] do
        let cache := dir / s!"cache-{format}"
        if !warm && (← cache.pathExists) then IO.FS.removeDirAll cache
        let run : IO (Nat × Nat) := do
          if !warm && (← cache.pathExists) then IO.FS.removeDirAll cache
          let t0 ← IO.monoMsNow
          let spawn : IO.Process.SpawnArgs :=
            { cmd := leantex.toString, cwd := some dir, args := #["-v", "build", "svg.tex", "-o", s!"svg.{format}"],
              env := #[("XDG_CACHE_HOME", some cache.toString)] }
          let out ← IO.Process.output spawn
          let t1 ← IO.monoMsNow
          if out.exitCode != 0 then die s!"svg benchmark failed:\n{out.stdout}{out.stderr}"
          return (t1 - t0, (imagesPhaseMs (out.stdout ++ out.stderr)).getD 0)
        if warm then discard run
        let mut wall : Array Nat := #[]
        let mut phase : Array Nat := #[]
        for _ in [0:n] do
          let (w, p) ← run
          wall := wall.push w
          phase := phase.push p
        let label := s!"leantex  {figures + 1} SVG figures ({format}, {if warm then "warm" else "cold"})"
        IO.println s!"{padRight label 42} {padLeft (toString (median wall)) 6} ms, images \
{median phase} ms (median of {n})"

/-- The real picture boundary: a private content cache per cold run, and a warm run that
ships identical bytes with every picture cached. -/
def benchPictures (n requests : Nat) : IO Unit := do
  let leantex ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  IO.FS.withTempDir fun dir => do
    let head := "\\documentclass{article}\n\\usepackage{tikz}\n" ++
      "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Open Sans\" }\n" ++
      "\\begin{document}\n"
    let mut source := head
    for i in [:requests] do
      source := source ++ "\\begin{tikzpicture}\n" ++
        "\\node[text width=4cm] at (0,0) {Invented request " ++ toString i ++ "};\n" ++
        "\\end{tikzpicture}\n"
    let input := dir / "pictures.tex"
    let output := dir / "pictures.pdf"
    let cache := dir / "cache"
    let pictures := cache / "leantex" / "pics"
    let run (input : System.FilePath) : IO Nat := do
      let start ← IO.monoMsNow
      let out ← IO.Process.output {
        cmd := leantex.toString
        args := #["-q", "build", input.toString, "-o", output.toString]
        env := #[("XDG_CACHE_HOME", some cache.toString)] }
      if out.exitCode != 0 then
        die s!"picture benchmark failed:\n{out.stdout}{out.stderr}"
      return (← IO.monoMsNow) - start
    let primer := dir / "fonts.tex"
    IO.FS.writeFile primer (head ++ "Invented text.\n\\end{document}\n")
    discard <| run primer
    IO.FS.writeFile input (source ++ "\\end{document}\n")
    let mut cold := #[]
    let mut warm := #[]
    for _ in [:n] do
      if ← pictures.pathExists then IO.FS.removeDirAll pictures
      cold := cold.push (← run input)
      let cached ← pictures.readDir
      let mut drawings := 0
      for entry in cached do
        -- Older compilers cache raw PDFs, current ones `.answer` files; a refusal is no drawing.
        let bytes ← IO.FS.readBinFile entry.path
        let pdf? := if entry.path.extension == some "answer" then
            match LeanTex.Cli.ConvCache.decode bytes with
            | some (.ok pdf) => some pdf
            | _ => none
          else if entry.path.extension == some "pdf" then some bytes else none
        if let some pdf := pdf? then
          if pdf.extract 0 5 == "%PDF-".toUTF8 then drawings := drawings + 1
      unless drawings == requests do
        die "picture benchmark did not render every external request"
      let bytes ← IO.FS.readBinFile output
      warm := warm.push (← run input)
      unless (← IO.FS.readBinFile output) == bytes do
        die "picture benchmark changed the PDF when replaying the same cache"
    for (label, times) in [("cold", cold), ("warm", warm)] do
      IO.println s!"{padRight s!"leantex  {requests} picture requests ({label})" 42} {padLeft (toString (median times)) 6} ms (median of {n})"

structure Phase where
  name : String
  detail : String
  ms : Nat

/-- One compiler run's sample, timing apart from the structured diagnostics and page count
the equivalence check reads. -/
structure Sample where
  ms : Nat := 0
  compilerMs : Nat
  diagnostics : Array String
  pages : Nat
  phases : Array Phase

def Sample.phase? (r : Sample) (name : String) : Option Phase :=
  r.phases.find? (·.name == name)

/-- A summary that is missing, duplicated or unsuccessful certifies no run; diagnostics
keep every structured field, in emission order. -/
def parseSample (log : String) : Except String Sample := do
  let mut diagnostics := #[]
  let mut phases : Array Phase := #[]
  let mut summary : Option (Nat × Nat) := none
  for line in log.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let j ← Lean.Json.parse line
    match ← j.getObjValAs? String "event" with
    | "diagnostic" =>
      unless (← j.getObjValAs? String "severity") == "note" do
        throw s!"fixture has a rendering loss: {j.compress}"
      diagnostics := diagnostics.push j.compress
    | "phase" =>
      let name ← j.getObjValAs? String "name"
      if name.isEmpty || phases.any (·.name == name) then
        throw s!"empty or duplicate phase: {name}"
      phases := phases.push {
        name, detail := ← j.getObjValAs? String "detail", ms := ← j.getObjValAs? Nat "ms" }
    | "summary" =>
      if summary.isSome then throw "more than one output summary"
      unless (← j.getObjValAs? Bool "ok") && (← j.getObjValAs? Nat "errors") == 0 do
        throw "unsuccessful output summary"
      if (← j.getObjValAs? String "output").isEmpty then throw "summary names no output"
      let pages ← j.getObjValAs? Nat "pages"
      if pages == 0 then throw "summary has no pages"
      summary := some (pages, ← j.getObjValAs? Nat "ms")
    | event => throw s!"unexpected porcelain event: {event}"
  let some (pages, compilerMs) := summary | throw "no output summary"
  return { pages, compilerMs, diagnostics, phases }

def sample (binary input output cache : System.FilePath) (verbose : Bool := false) : IO Sample := do
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := binary.toString
    args := #["build", input.toString, "-o", output.toString, "--porcelain"] ++
      (if verbose then #["-v"] else #[])
    env := #[("XDG_CACHE_HOME", some cache.toString), ("LC_ALL", some "C"), ("TZ", some "UTC")] }
  let ms := (← IO.monoMsNow) - start
  if out.exitCode != 0 then
    throw (IO.userError s!"benchmark compile failed:\n{out.stdout}{out.stderr}")
  let report ← match parseSample (out.stdout ++ out.stderr) with
    | .ok report => pure report
    | .error reason => throw (IO.userError s!"benchmark needs a complete porcelain report: {reason}")
  return { report with ms }

/-- Time one cached operation over this benchmark's own caches, font discovery warmed
first. -/
def benchCached (n pages : Nat) (label : String)
    (binary input output cache : System.FilePath) (operation : String) : IO Unit := do
  let mut cold := #[]
  let mut warm := #[]
  for _ in [:n] do
    let entries := cache / "leantex" / operation
    if ← entries.pathExists then IO.FS.removeDirAll entries
    let first ← sample binary input output cache
    let bytes ← IO.FS.readBinFile output
    let second ← sample binary input output cache
    unless first.pages == pages && second.pages == pages do
      die s!"{label}: expected {pages} pages, got {first.pages} and {second.pages}"
    unless !bytes.isEmpty && (← IO.FS.readBinFile output) == bytes &&
        first.diagnostics == second.diagnostics do
      die s!"{label}: cache replay changed output bytes or diagnostic order"
    unless ← entries.pathExists do die s!"{label}: operation populated no cache"
    cold := cold.push first.ms
    warm := warm.push second.ms
  for (kind, times) in [("cold", cold), ("warm", warm)] do
    IO.println s!"{padRight s!"leantex  {label} ({kind})" 42} {padLeft (toString (median times)) 6} ms (median of {n})"

/-- Distinct page streams and captured vector images through the production workers,
sources generated before timing. -/
def benchConcurrent (n requests : Nat) (images : Bool) : IO Unit := do
  let binary ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  IO.FS.withTempDir fun dir => do
    let head := "\\documentclass{beamer}\n" ++
      "\\fonts{ dir = \"" ++ fonts.toString ++ "\", body = \"Open Sans\" }\n" ++
      "\\begin{document}\n"
    let finish := "\\end{document}\n"
    let cache := dir / "cache"
    let primer := dir / "primer.tex"
    IO.FS.writeFile primer
      (head ++ "\\begin{frame}{Invented figure}Font primer.\\end{frame}\n" ++ finish)
    discard <| sample binary primer (dir / "primer.pdf") cache
    let mut source := head
    for i in [:requests] do
      source := source ++ s!"\\begin\{frame}\{Invented request {i}}\n"
      if images then
        let asset := dir / s!"figure{i}.pdf"
        IO.FS.writeFile primer (head ++
          s!"\\begin\{frame}\{Invented vector {i}}A captured vector image.\\end\{frame}\n" ++ finish)
        discard <| sample binary primer asset cache
        source := source ++ s!"\\includegraphics[width=0.8\\textwidth,alt=\{Invented vector {i}}]\{figure{i}.pdf}\n"
      else
        for j in [:8] do
          source := source ++ s!"\\noindent Invented page {i}, line {j}: measured text in source order.\\par\n"
      source := source ++ "\\end{frame}\n"
    let input := dir / "deck.tex"
    let output := dir / (if images then "deck.html" else "deck.pdf")
    IO.FS.writeFile input (source ++ finish)
    benchCached n requests
      (if images then s!"{requests} PDF images (HTML)" else s!"{requests} page streams (PDF)")
      binary input output cache (if images then "convs" else "flate")

namespace Slides

open LeanTex.Core

/-- The images phase's detail counts; the fixture has one cacheable alpha PNG. -/
def imageCounts (r : Sample) : Except String (Nat × Nat) := do
  let some p := r.phase? "images" | throw "no images phase (use --porcelain -v)"
  let number := fun s : String => match s.toNat? with
    | some n => Except.ok n
    | none => Except.error s!"bad image count: {s}"
  let words := p.detail.splitOn " "
  let (files, hits) ← match words with
    | [n, "files"] => pure (← number n, 0)
    | [n, "files,", h, "cached"] =>
      pure (← number n, ← number h)
    | _ => throw s!"unrecognized images detail: {p.detail}"
  if hits > files then throw "more image hits than requests"
  return (files, hits)

/-- The same source and cache replay owes the same nonempty artifact, page count,
diagnostic order and font environment. -/
def equivalent (pages : Nat) (a b : Sample) (x y : ByteArray) : Bool :=
  !x.isEmpty && x == y && a.pages == pages && b.pages == pages &&
    a.diagnostics == b.diagnostics &&
    a.phases.map (·.name) == b.phases.map (·.name) &&
    (a.phase? "font").map (·.detail) == (b.phase? "font").map (·.detail) &&
    (a.phase? "fontdb").map (·.detail) == (b.phase? "fontdb").map (·.detail)

/-- The fixture resolves only copied, unchanged fonts. -/
def fixtureFonts (root : String) (r : Sample) : Bool :=
  match (r.phase? "font").map (·.detail.splitOn " (") with
  | some [_, paths] =>
    if !paths.endsWith ")" then false else
    let paths := (paths.dropEnd 1).toString.splitOn ", "
    !paths.isEmpty && paths.all (·.startsWith (root ++ "/fonts/"))
  | _ => false

/-- A changed input owes changed bytes and the fresh-cache answer. -/
def invalidated (pages : Nat) (old changed fresh : ByteArray)
    (a b : Sample) : Bool :=
  old != changed && equivalent pages a b changed fresh

/-- The content answers among cache files, font-discovery metadata excluded. -/
def answers (files : Array (String × String)) : Array (String × String) :=
  files.filter fun (name, _) =>
    name.startsWith "imgs/" || name.startsWith "flate/" || name.startsWith "convs/"

def require (ok : Bool) (why : String) : IO Unit := do
  unless ok do throw (IO.userError s!"slides benchmark: {why}")

def checked (answer : Except String α) : IO α :=
  match answer with
  | .ok value => pure value
  | .error why => throw (IO.userError s!"slides benchmark: {why}")

def say (text : String) : IO Unit := do
  IO.println text
  (← IO.getStdout).flush

/-- The executable's hash, outside timing. -/
def binaryHash (binary : System.FilePath) : IO String := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #["--", binary.toString] }
  let key := (result.stdout.splitOn " ").headD ""
  require (result.exitCode == 0 && key.length == 64 &&
    key.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) "could not SHA-256 the compiler"
  return key

def toolVersions : IO (Array (String × String)) := do
  let mut versions := #[]
  for (tool, args) in [("pdftocairo", #["-v"])] do
    let result ← IO.Process.output { cmd := tool, args }
    let version := (result.stdout ++ result.stderr).trimAscii.toString
    require (result.exitCode == 0 && !version.isEmpty) s!"could not read {tool}'s version"
    versions := versions.push (tool, version)
  return versions

def be32 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
    UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]⟩

-- PNG CRC-32 (ISO/IEC 15948 Annex D), so the browser accepts the fixture too.
def crc32 (bytes : ByteArray) : UInt32 := Id.run do
  let mut crc : UInt32 := 0xffffffff
  for byte in bytes do
    crc := crc ^^^ byte.toUInt32
    for _ in [:8] do
      crc := (crc >>> 1) ^^^ (if crc &&& 1 == 1 then 0xedb88320 else 0)
  return crc ^^^ 0xffffffff

def pngChunk (tag : String) (data : ByteArray) : ByteArray :=
  let payload := tag.toUTF8 ++ data
  be32 data.size ++ payload ++ be32 (crc32 payload).toNat

def png (width height : Nat) (compressed : ByteArray) : ByteArray :=
  ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩ ++
    pngChunk "IHDR" (be32 width ++ be32 height ++ ⟨#[8, 6, 0, 0, 0]⟩) ++
    pngChunk "IDAT" compressed ++ pngChunk "IEND" ByteArray.empty

/-- Two same-sized RGBA fixtures under one filename, so a colour change must invalidate
alpha decoding by content. -/
def raster (edited : Bool) : ByteArray := Id.run do
  let mut raw := ByteArray.empty
  for y in [:80] do
    raw := raw.push 0
    for x in [:128] do
      raw := raw ++ ⟨#[if edited then 200 else 40, UInt8.ofNat (x + y),
        if edited then 40 else 200, if x % 16 < 8 then 255 else 128]⟩
  return png 128 80 (Flate.deflateStored raw)

/-- Seeded low-entropy noise, needing both literals and matches; the edit changes one
colour sample. -/
def compressedRaster (side : Nat) (edited : Bool) : ByteArray := Id.run do
  let mut raw := ByteArray.emptyWithCapacity (side * (4 * side + 1))
  let mut seed : UInt64 := 731
  for y in [:side] do
    raw := raw.push 0
    for x in [:side] do
      for c in [:4] do
        seed := seed ^^^ (seed >>> 12)
        seed := seed ^^^ (seed <<< 25)
        seed := seed ^^^ (seed >>> 27)
        let value := (seed * 2685821657736338717).toUInt8
        let value := if c == 3 then 128 + value % 128 else value % 32
        raw := raw.push (if edited && x == 0 && y == 0 && c == 0 then value ^^^ 16 else value)
  return png side side (Flate.deflate raw)

/-- A font-free vector asset, generated outside timing. -/
def vector (edited : Bool := false) : ByteArray := Id.run do
  let colour := if edited then "0.7 0.4 0.1" else "0.1 0.4 0.7"
  let content := colour ++ " rg 0 0 100 64 re f\n1 0.7 0.1 rg 12 12 40 40 re f"
  let objs := #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R] /Count 1 /MediaBox [0 0 100 64] >>",
    "<< /Type /Page /Parent 2 0 R /Resources << >> /Contents 4 0 R >>",
    s!"<< /Length {content.utf8ByteSize} >>\nstream\n{content}\nendstream"]
  let mut out := "%PDF-1.7\n"
  let mut offsets := #[]
  for (obj, i) in objs.zipIdx do
    offsets := offsets.push out.utf8ByteSize
    out := out ++ s!"{i + 1} 0 obj\n{obj}\nendobj\n"
  let xref := out.utf8ByteSize
  out := out ++ s!"xref\n0 {objs.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    out := out ++ String.ofList (List.replicate (10 - digits.length) '0') ++ digits ++ " 00000 n \n"
  return (out ++ s!"trailer\n<< /Size {objs.size + 1} /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n").toUTF8

def deck (frames : Nat) (edited : Bool := false) : String := Id.run do
  let mut src := "\\documentclass[aspectratio=169]{beamer}\n\\usetheme{moloch}\n" ++
    "\\usepackage{graphicx}\n" ++
    "\\fonts{dir=\"fonts\",body=\"Open Sans\"}\n" ++
    "\\begin{document}\n"
  for i in [:frames] do
    let word := if edited && i == 0 then "Comet" else "Orbit"
    src := src ++ s!"\\begin\{frame}\{Invented slide {i + 1}}\n{word} samples travel through a small model.\n" ++
      "\\begin{itemize}\n\\item A stable observation and its label.\n" ++
      "\\item \\alert{Repeated assets} retain their colours.\n\\end{itemize}\n" ++
      "\\includegraphics[width=0.18\\textwidth,alt={Invented alpha grid}]{grid.png}\n" ++
      "\\includegraphics[width=0.18\\textwidth,alt={The same alpha grid}]{grid.png}\n" ++
      "\\includegraphics[width=0.18\\textwidth,alt={Invented vector blocks}]{blocks.pdf}\n" ++
      "\\end{frame}\n"
  return src ++ "\\end{document}\n"

def selftest : IO Unit := do
  require (median #[9, 1, 5] == 5 && median #[8, 3, 5, 1, 7] == 5) "median"
  let a := "{\"event\":\"diagnostic\",\"severity\":\"note\",\"message\":\"first\"}"
  let b := "{\"event\":\"diagnostic\",\"severity\":\"note\",\"message\":\"second\"}"
  let ph := "{\"event\":\"phase\",\"name\":\"images\",\"detail\":\"2 files\",\"ms\":7}"
  let done := "{\"event\":\"summary\",\"ok\":true,\"errors\":0,\"output\":\"deck.pdf\",\"pages\":8,\"ms\":20}"
  let log := String.intercalate "\n" [a, b, ph, done]
  let r ← checked (parseSample log)
  require (r.compilerMs == 20 && (r.phase? "images").map (·.ms) == some 7 &&
    (imageCounts r).toOption == some (2, 0)) "phase parser lost data"
  let warm ← checked (parseSample (log.replace "2 files" "2 files, 1 cached"))
  require ((imageCounts warm).toOption == some (2, 1)) "image hit parser"
  let bytes := "invented artifact".toUTF8
  require (equivalent 8 r warm bytes bytes) "timing/cache detail affected equivalence"
  for (name, bad) in [
      ("missing summary", String.intercalate "\n" [a, ph]),
      ("duplicate summary", log ++ "\n" ++ done),
      ("duplicate phase", log ++ "\n" ++ ph),
      ("failed summary", log.replace "\"ok\":true" "\"ok\":false"),
      ("summary errors", log.replace "\"errors\":0" "\"errors\":1"),
      ("empty pages", log.replace "\"pages\":8" "\"pages\":0"),
      ("negative timing", log.replace "\"ms\":7" "\"ms\":-1"),
      ("loss diagnostic", log.replace "\"note\"" "\"warning\""),
      ("non-JSON", log ++ "\ncompiler crashed")] do
    require (!(parseSample bad).isOk) s!"parser accepted {name}"
  for detail in ["two files", "2 files, 3 cached", "2 files, 1 cached extra"] do
    let bad ← checked (parseSample (log.replace "2 files" detail))
    require (!(imageCounts bad).isOk) s!"parser accepted {detail}"
  let swapped ← checked (parseSample (String.intercalate "\n" [b, a, ph, done]))
  require (!equivalent 8 r swapped bytes bytes) "diagnostic reordering was hidden"
  let font : Phase := { name := "font", detail := "OpenSans (/fixture/fonts/face.ttf)", ms := 9 }
  let withFont := { r with phases := r.phases.push font }
  let otherFont := { r with phases := r.phases.push { font with detail := "Other (/host/font.ttf)" } }
  require (fixtureFonts "/fixture" withFont && !fixtureFonts "/fixture" otherFont)
    "fixture font guard accepted host substitution"
  require (!fixtureFonts "/fixture"
    { r with phases := #[{ font with detail := "OpenSans (/fixture/fonts/face.ttf" }] })
    "fixture font guard accepted a truncated record"
  require (!equivalent 8 withFont otherFont bytes bytes)
    "different font environment was hidden"
  require (!equivalent 8 withFont { withFont with phases := withFont.phases.reverse } bytes bytes)
    "different phase order was hidden"
  require (!equivalent 9 r r bytes bytes) "wrong page count was hidden"
  require (!equivalent 8 r r ByteArray.empty ByteArray.empty) "empty artifact passed"
  let edited := "edited artifact".toUTF8
  require (!equivalent 8 r r bytes edited) "different artifact passed"
  require (invalidated 8 bytes edited edited r r) "valid invalidation failed"
  require (!invalidated 8 bytes bytes bytes r r) "unchanged artifact passed invalidation"
  require (!invalidated 8 bytes edited bytes r r) "stale cache passed invalidation"
  let files := #[("fontdb-2.tsv", "old metadata"), ("imgs/grid.img", "answer")]
  let metadataEdit := #[("fontdb-2.tsv", "new metadata"), ("imgs/grid.img", "answer")]
  require (files != metadataEdit && answers files == answers metadataEdit)
    "answer judge must ignore only metadata changes"
  require (answers files != answers #[("imgs/grid.img", "changed answer")] &&
    answers files != answers #[("imgs/grid.img", "answer"), ("convs/new.answer", "new")])
    "answer judge hid changed or added content answers"
  require (crc32 "123456789".toUTF8 == 0xcbf43926) "PNG CRC test vector"
  for edit in [false, true] do
    let png ← checked (Image.decode (raster edit))
    require (png.pxW == 128 && png.pxH == 80 && png.losses.isEmpty) "RGBA fixture dimensions/losses"
    require (match png.alpha with | .soft _ 8 => true | _ => false) "fixture lost alpha"
  require ((raster false).size == (raster true).size && raster false != raster true)
    "asset edit must preserve size, change content"
  for edit in [false, true] do
    let source ← checked (Image.probe (compressedRaster 16 edit))
    require ((source.payload[2]?.getD 0 >>> 1) &&& 3 == 2)
      "compressed fixture must exercise dynamic-Huffman decoding"
    let image ← checked (Image.decode (compressedRaster 16 edit))
    require (image.pxW == 16 && image.pxH == 16 && image.losses.isEmpty &&
      match image.alpha with | .soft _ 8 => true | _ => false) "compressed RGBA fixture"
  require (compressedRaster 16 false != compressedRaster 16 true) "compressed asset edit"
  require ((vector false).size == (vector true).size && vector false != vector true)
    "vector edit must preserve size, change content"
  require (deck 8 != deck 8 true) "source edit must change content"
  say "slides benchmark selftest: parser, equivalence, invalidation and fixtures passed"

/-- The answers a cache publishes, at its root or one directory below; a deeper layout is
refused. -/
def inventory (root : System.FilePath) : IO (Array (String × String)) := do
  if !(← root.pathExists) then return #[]
  let mut out := #[]
  for entry in ← root.readDir do
    if ← entry.path.isDir then
      for child in ← entry.path.readDir do
        require (!(← child.path.isDir)) "cache inventory needs a deeper traversal"
        out := out.push (entry.fileName ++ "/" ++ child.fileName,
          Flate.contentKey (← IO.FS.readBinFile child.path))
    else
      out := out.push (entry.fileName, Flate.contentKey (← IO.FS.readBinFile entry.path))
  return out.qsort (fun a b => a.1 < b.1)

def entries (files : Array (String × String)) (dir ext : String) : Nat :=
  files.filter (fun (name, _) => name.startsWith (dir ++ "/") && name.endsWith ext) |>.size

def fingerprint (files : Array (String × String)) : String :=
  Flate.contentKey (String.intercalate "\n" (files.toList.map fun (p, k) => p ++ "\t" ++ k)).toUTF8

structure Run where
  report : Sample
  bytes : ByteArray
  cache : Array (String × String)

/-- One timed child compiler run; everything else is outside the measurement. -/
def compile (binary dir cache : System.FilePath) (format : String) : IO Run := do
  let output := dir / ("deck." ++ format)
  if ← output.pathExists then IO.FS.removeFile output
  let report ← sample binary (dir / "deck.tex") output cache true
  for name in ["read", "prepare", "elab", "fontdb", "font", "images", "layout", format] do
    require ((report.phase? name).isSome) s!"missing phase {name}"
  require (!report.diagnostics.isEmpty) "fixture must exercise diagnostic replay"
  require (fixtureFonts dir.toString report) "fixture resolved a font outside its private copy"
  let bytes ← IO.FS.readBinFile output
  require (!bytes.isEmpty) "no output bytes"
  return { report, bytes, cache := ← inventory (cache / "leantex") }

def replay (pages : Nat) (a b : Run) : IO Unit := do
  require (equivalent pages a.report b.report a.bytes b.bytes)
    "replay changed artifact, page count, diagnostic order or font environment"
  let before := answers a.cache
  let after := answers b.cache
  let removed := before.filter fun entry => !after.contains entry
  let added := after.filter fun entry => !before.contains entry
  require (before == after)
    s!"repeat changed cache entries: before={removed.map (·.1)}, after={added.map (·.1)}"

def work (r : Run) (hits : Nat) : IO Unit := do
  let counts ← checked (imageCounts r.report)
  require (counts == (2, hits)) s!"expected 2 unique images / {hits} hits, got {counts}"

def printSample (label : String) (r : Run) : IO Unit := do
  let phases := r.report.phases.toList.map fun p => s!"{p.name}={p.ms}"
  say s!"  {label}: wall={r.report.ms} compiler={r.report.compilerMs} ms; {String.intercalate " " phases}"

/-- The edited input's cached build must agree with an empty-cache oracle, then repeat
without new answers. -/
def checkEdit (binary dir cache : System.FilePath) (format label : String)
    (pages hits : Nat) (old : Run) : IO Run := do
  let changed ← compile binary dir cache format
  work changed hits
  IO.FS.withTempDir fun freshCache => do
    let fresh ← compile binary dir freshCache format
    work fresh 0
    require (invalidated pages old.bytes changed.bytes fresh.bytes changed.report fresh.report)
      s!"{label}: changed-input cache answer disagrees with a fresh build, or output did not change"
  let repeated ← compile binary dir cache format
  work repeated 1
  replay pages changed repeated
  say s!"  {label}: changed bytes = fresh-cache oracle; repeat identical (not in medians)"
  return changed

def bench (binary dir : System.FilePath) (n frames : Nat) (format : String)
    (image : Bool → ByteArray := raster) : IO Run := do
  IO.FS.writeFile (dir / "deck.tex") (deck frames)
  IO.FS.writeBinFile (dir / "grid.png") (image false)
  IO.FS.writeBinFile (dir / "blocks.pdf") (vector false)
  let cache := dir / "cache"
  let mut cold : Array Run := #[]
  let mut warm : Array Run := #[]
  say s!"slides {frames} {format}: source={Flate.contentKey (deck frames).toUTF8}; {3 * frames} image uses / 2 sources"
  for i in [:n] do
    if ← cache.pathExists then IO.FS.removeDirAll cache
    let first ← compile binary dir cache format
    let second ← compile binary dir cache format
    work first 0
    work second 1
    replay frames first second
    if let some earlier := cold[0]? then
      require (equivalent frames earlier.report first.report earlier.bytes first.bytes)
        "cold runs changed the workload or artifact"
    require (entries first.cache "imgs" ".img" == 1) "expected one alpha decode answer"
    require (first.cache.any fun (name, _) => name.startsWith "fontdb-" && name.endsWith ".tsv")
      "font discovery populated no private cache"
    let operation := if format == "pdf" then "flate" else "convs"
    require (entries first.cache operation ".answer" > 0) s!"no {operation} cache answers"
    printSample s!"pair {i + 1} cold" first
    printSample s!"pair {i + 1} repeat" second
    cold := cold.push first
    warm := warm.push second
  let some first := cold[0]? | die "slides benchmark needs at least one pair"
  for (label, samples) in [("cold", cold), ("repeat", warm)] do
    say s!"  median {label}: wall={median (samples.map (·.report.ms))} compiler={median (samples.map (·.report.compilerMs))} ms (N={n})"
  for p in first.report.phases do
    let time := fun r : Run => ((r.report.phase? p.name).map (·.ms)).getD 0
    say s!"  phase {padRight p.name 12} cold={median (cold.map time)} repeat={median (warm.map time)} ms"
  let coldMs := median (cold.map (·.report.ms))
  if coldMs > 0 then
    say s!"  repeat/cold wall={median (warm.map (·.report.ms)) * 100 / coldMs}% (descriptive, no threshold)"
  say s!"  work: alpha decodes 1 -> 0, image hits 0 -> 1; unique requests 2 -> 2"
  say s!"  inventory: imgs={entries first.cache "imgs" ".img"} flate={entries first.cache "flate" ".answer"} convs={entries first.cache "convs" ".answer"} (published answers; identical on repeat)"
  say s!"  artifact={Flate.contentKey first.bytes} bytes={first.bytes.size} pages={first.report.pages} diagnostics={first.report.diagnostics.size}"
  say s!"  font environment: {((first.report.phase? "fontdb").map (·.detail)).getD ""}; {((first.report.phase? "font").map (·.detail)).getD ""}"
  IO.FS.writeBinFile (dir / "grid.png") (image true)
  let changed ← checkEdit binary dir cache format "same-path asset edit" frames 0 first
  require (entries changed.cache "imgs" ".img" == 2) "asset edit reused the old alpha answer"
  IO.FS.writeBinFile (dir / "blocks.pdf") (vector true)
  let vectorEdit ← checkEdit binary dir cache format "same-path vector edit" frames 1 changed
  IO.FS.writeFile (dir / "deck.tex") (deck frames true)
  let sourceEdit ← checkEdit binary dir cache format "same-path source edit" frames 1 vectorEdit
  require (entries sourceEdit.cache "imgs" ".img" == 2) "source edit repeated unchanged alpha work"
  return first

def load : IO String := do
  return ((← (IO.FS.readFile "/proc/loadavg").toBaseIO).toOption.getD "unavailable").trimAscii.toString

def run (n : Nat) (compressed : Bool := false) : IO Unit := do
  require (n ≥ 3) "N must be at least 3 for slide medians"
  selftest
  let versions ← toolVersions
  let binary ← IO.FS.realPath (← compiler)
  let binaryKey ← binaryHash binary
  let comparison ← match ← IO.getEnv "LEANTEX_BENCH_COMPARE_BINARY" with
    | none => pure none
    | some path =>
      let path ← IO.FS.realPath path
      pure (some (path, ← binaryHash path))
  let image := if compressed then compressedRaster 256 else raster
  -- Capture the exact encoded inputs once; generation is outside all samples.
  let original := image false
  let edited := image true
  let image := fun edit => if edit then edited else original
  say s!"slides runtime benchmark v1; N={n}; binary={binary}; sha256={binaryKey}"
  say s!"PNG workload: {if compressed then "256x256 dynamic-Huffman" else "128x80 stored"}"
  for (tool, version) in versions do
    say s!"tool {tool}: {(Lean.Json.str version).compress}"
  say "Application-cache cold; OS caches uncontrolled. Shared-host timings are provisional; rerun on a quiet host for before/after claims."
  say "Phases overlap: font includes fontdb. Do not sum phase medians. Tool invocations and conversion/compression hits are uninstrumented."
  say s!"host load before: {← load}"
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "fonts")
    for file in ← (System.FilePath.mk "testdata/corpus/fonts").readDir do
      if file.path.extension == some "otf" || file.path.extension == some "ttf" then
        IO.FS.writeBinFile (dir / "fonts" / file.fileName) (← IO.FS.readBinFile file.path)
    let fonts ← inventory (dir / "fonts")
    say s!"inputs: fonts={fingerprint fonts} ({fonts.size} files) png={Flate.contentKey original} pdf={Flate.contentKey (vector false)}; LC_ALL=C TZ=UTC"
    for frames in (if compressed then [8] else [8, 32]) do
      for format in ["pdf", "html"] do
        say s!"primary compiler sha256={binaryKey}"
        let primary ← bench binary dir n frames format image
        if let some (other, key) := comparison then
          say s!"comparison compiler={other}; sha256={key}"
          let reference ← bench other dir n frames format image
          require (equivalent frames primary.report reference.report primary.bytes reference.bytes)
            "compiler comparison changed artifacts, diagnostics or font environment"
          require ((← binaryHash other) == key) "comparison compiler changed during the benchmark"
          say "compiler comparison: byte-identical artifact and ordered diagnostics"
    require ((← inventory (dir / "fonts")) == fonts) "font bytes changed during the benchmark"
  require ((← binaryHash binary) == binaryKey) "compiler changed during the benchmark"
  require ((← toolVersions) == versions) "external tool versions changed during the benchmark"
  say s!"host load after: {← load}"
  say "slides sanity passed: deterministic artifacts/diagnostics, bounded repeated image work, source/asset invalidation."

end Slides

/-- Four times the input may cost at most `bound` times the phase (linear 4, quadratic 16,
cubic 64). -/
def growthBound (label : String) (small big : Nat) (bound : Nat := 8) : IO Unit := do
  let ratio := (big * 10 + max small 1 / 2) / max small 1
  IO.println s!"{padRight s!"leantex  growth, {label}" 42} {padLeft s!"{ratio / 10}.{ratio % 10}" 6} ×  (bound {bound}.0)"
  if big > bound * max small 1 then
    die s!"{label}: the phase grew {ratio / 10}.{ratio % 10}× for 4× the input (bound {bound})"

/-- A listing's lexing and setting are linear in its length, in lines and within a
line. -/
def listingGrowth (n : Nat) : IO Unit := do
  let (smallElab, smallLayout) ← listingElabMs n 2000
  let (bigElab, bigLayout) ← listingElabMs n 8000
  growthBound "8000 / 2000 lines" smallElab bigElab
  growthBound "layout, 8000 / 2000 lines" smallLayout bigLayout
  for ((lang, what, small), (_, _, big)) in (adversarialListings 2000).zip (adversarialListings 8000) do
    let (smallElab, smallLayout) ← listingPhasesMs n s!"{lang} {what}, 2000 scale" lang small
    let (bigElab, bigLayout) ← listingPhasesMs n s!"{lang} {what}, 8000 scale" lang big
    growthBound s!"{lang} {what}, 8000 / 2000" smallElab bigElab
    growthBound s!"layout, {lang} {what}, 8000 / 2000" smallLayout bigLayout

/-- The reference list's growth rows, which `--bib-only` runs alone. -/
def benchBibGrowth (n : Nat) : IO Unit := do
  -- Four times the entries may cost at most eight times the phase, under each style family.
  let biblatexDoc (style : String) (key : String := "r0") : String :=
    s!"\\documentclass\{article}\n\\usepackage[style={style}]\{biblatex}\n\
      \\addbibresource\{refs.bib}\n\\begin\{document}\nAlpha words \\parencite\{{key}}.\n\
      \\nocite\{*}\n\\printbibliography\n\\end\{document}\n"
  let richNat := "\\documentclass{article}\n\\usepackage{natbib}\n\\bibliographystyle{plainnat}\n\
    \\begin{document}\nAlpha words \\citep{r0}.\n\\nocite{*}\n\\bibliography{refs}\n\
    \\end{document}\n"
  let heavyNat := "\\documentclass{article}\n\\usepackage{natbib}\n\\bibliographystyle{plainnat}\n\
    \\begin{document}\nAlpha words \\citep{h0}.\n\\nocite{*}\n\\bibliography{refs}\n\
    \\end{document}\n"
  let chainNat := "\\documentclass{article}\n\\usepackage{natbib}\n\\bibliographystyle{plainnat}\n\
    \\begin{document}\nAlpha words \\citep{c0}.\n\\bibliography{refs}\n\\end{document}\n"
  -- A field citation chain runs last, at a quarter of the sizes.
  let rows : List (String × (Nat → String) × String × Nat) :=
    [("plainnat", bibOf, "", 400), ("plainnat, TeX fields", bibRichOf, richNat, 400),
     ("plainnat, TeX-heavy fields", bibHeavyOf, heavyNat, 400),
     ("biblatex numeric", bibRichOf, biblatexDoc "numeric", 400),
     ("biblatex authoryear", bibRichOf, biblatexDoc "authoryear", 400),
     ("biblatex authoryear, TeX-heavy fields", bibHeavyOf, biblatexDoc "authoryear" "h0", 400),
     ("plainnat, field citation chain", bibChainOf, chainNat, 100)]
  for (label, bib, doc, size) in rows do
    let small ← if doc.isEmpty then benchBib n size label bib else benchBib n size label bib doc
    let big ← if doc.isEmpty then benchBib n (4 * size) label bib
      else benchBib n (4 * size) label bib doc
    let ratio := (big * 10 + max small 1 / 2) / max small 1
    IO.println s!"{padRight s!"leantex  bib growth, {label}, {4 * size} / {size}" 42} {padLeft s!"{ratio / 10}.{ratio % 10}" 6} ×  (bound 8.0)"
    if big > 8 * max small 1 then
      die s!"the reference-list phase ({label}) grew {ratio / 10}.{ratio % 10}× for 4× the entries (bound 8)"

/-- The compiled passes' runs, label, size and nanoseconds each, after building them. -/
def passRuns (n : Nat) : IO (Array (String × Nat × Nat)) := do
  let built ← (← IO.Process.spawn { cmd := "lake", args := #["build", "-q", "passBench"] }).wait
  if built != 0 then die "lake build passBench failed"
  let out ← IO.Process.output { cmd := ".lake/build/bin/passBench", args := #[toString n] }
  if out.exitCode != 0 then die s!"passBench failed:\n{out.stderr}"
  return (out.stdout.splitOn "\n").toArray.filterMap fun l =>
    match l.splitOn "\t" with
    | ["pass", label, size, ns] => do pure (label, ← size.toNat?, ← ns.toNat?)
    | _ => none

/-- Nanoseconds as milliseconds to a tenth. -/
def msOf (ns : Nat) : String := s!"{ns / 1000000}.{ns / 100000 % 10}"

/-- Compiled passes at a size and four times it, judged by growth (anchors, each probing the ids
before it, bounded as not cubic), and a memoized glyph ink read at most a tenth of a decode. -/
def benchPasses (n : Nat) : IO Unit := do
  let runs ← passRuns n
  let row (label : String) (size : Nat) (what : String) : IO Nat := do
    let times := (runs.filter fun (l, s, _) => l == label && s == size).map (·.2.2)
    unless times.size == n do
      die s!"passBench printed {times.size} runs of {label} at {size}, not {n}"
    let ns := median times
    IO.println s!"{padRight s!"leantex  {what}" 42} {padLeft (msOf ns) 6} ms (median of {n})"
    return ns
  let growth : List (String × Nat × String × Nat) :=
    [("anchors", 600, "same-titled", 32), ("families", 30000, "faces", 8),
     ("merge", 400000, "keys", 8), ("legible", 20000, "runs", 8), ("failing", 6000, "uses", 8)]
  for (label, size, what, bound) in growth do
    let small ← row label size s!"{label}, {size} {what}"
    let big ← row label (4 * size) s!"{label}, {4 * size} {what}"
    growthBound s!"{label}, {4 * size} / {size}" small big bound
  let decodes ← row "decodes" 2000 "glyph ink, 2000 decodes"
  let reads ← row "reads" 2000000 "glyph ink, 2000000 memo reads"
  let ratio := decodes * 1000 / max reads 1
  IO.println s!"{padRight "leantex  glyph ink, decode / memo read" 42} {padLeft (toString ratio) 6} ×  (bound 10)"
  if reads > 100 * decodes then
    die s!"glyph ink: a decode costs {ratio}× a memoized read (bound 10)"

/-- Every page of a PDF embedded, one build per page, warm: the images phase's median of
`n`. -/
def benchPdfPages (n : Nat) (pdf : System.FilePath) : IO Unit := do
  let binary ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  let source ← IO.FS.realPath pdf
  let bytes ← IO.FS.readBinFile source
  let d ← match LeanTex.Core.PdfRead.Doc.ofBytes bytes with
    | .ok d => pure d
    | .error e => die s!"the PDF does not read: {e}"
  -- A page tree holds no more pages than the file holds objects.
  let mut pages := 0
  for k in [1:d.objectCount + 1] do
    if (d.page (.number k)).isOk then pages := k else break
  IO.FS.withTempDir fun dir => do
    let cache := dir / "cache"
    let mut times : Array (Nat × Nat) := #[]
    for k in [1:pages + 1] do
      let doc := dir / s!"page{k}.tex"
      IO.FS.writeFile doc ("\\documentclass{article}\n\\fonts{ dir = \"" ++ fonts.toString ++
        "\", body = \"Open Sans\" }\n\\begin{document}\n\\includegraphics[page=" ++ toString k ++
        ", width=4cm]{" ++ source.toString ++ "}\n\\end{document}\n")
      let mut warm : Array Nat := #[]
      for _ in [0:n] do
        let _ ← sample binary doc (dir / s!"page{k}.pdf") cache true
        let second ← sample binary doc (dir / s!"page{k}.pdf") cache true
        let some p := second.phase? "images" | die s!"page {k}: no images phase"
        warm := warm.push p.ms
      times := times.push (k, median warm)
    let slowest := times.foldl (fun a b => if b.2 > a.2 then b else a) (0, 0)
    let first := (times[0]?.map (·.2)).getD 0
    IO.println s!"{padRight s!"leantex  pdf page 1 embedded (warm)" 42} {padLeft (toString first) 6} ms (median of {n})"
    IO.println s!"{padRight s!"leantex  slowest page, {slowest.1} of {pages}" 42} {padLeft (toString slowest.2) 6} ms (median of {n})"
    IO.println s!"leantex  pages under 150 ms: {(times.filter (·.2 < 150)).size} of {pages}"

/-- A PDF figure's web face, cold and warm: an HTML build of a document including each
figure, the html phase (and faces phase where reported) and the whole build, the median of
`n` pairs. -/
def benchFaces (n : Nat) (pdfs : List String) : IO Unit := do
  let binary ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "testdata/corpus/fonts"
  IO.FS.withTempDir fun dir => do
    for pdf in pdfs do
      let source ← IO.FS.realPath pdf
      let name := (System.FilePath.mk pdf).fileName.getD pdf
      let doc := dir / "figure.tex"
      IO.FS.writeFile doc ("\\documentclass{article}\n\\fonts{ dir = \"" ++ fonts.toString ++
        "\", body = \"Open Sans\" }\n\\begin{document}\n\\includegraphics[width=8cm,alt={An invented figure}]{" ++
        source.toString ++ "}\n\\end{document}\n")
      let mut rows : Array (String × Array Nat × Array Nat) := #[]
      let mut htmlCold : Array Nat := #[]
      let mut htmlWarm : Array Nat := #[]
      let mut facesCold : Array Nat := #[]
      let mut facesWarm : Array Nat := #[]
      let mut buildCold : Array Nat := #[]
      let mut buildWarm : Array Nat := #[]
      for i in [0:n] do
        let cache := dir / s!"cache-{name}-{i}"
        let first ← sample binary doc (dir / "figure.html") cache true
        let second ← sample binary doc (dir / "figure.html") cache true
        let some h1 := first.phase? "html" | die s!"{name}: no html phase"
        let some h2 := second.phase? "html" | die s!"{name}: no html phase"
        htmlCold := htmlCold.push h1.ms
        htmlWarm := htmlWarm.push h2.ms
        if let some f := first.phase? "faces" then facesCold := facesCold.push f.ms
        if let some f := second.phase? "faces" then facesWarm := facesWarm.push f.ms
        buildCold := buildCold.push first.compilerMs
        buildWarm := buildWarm.push second.compilerMs
      rows := rows ++ #[("html", htmlCold, htmlWarm), ("build", buildCold, buildWarm)] ++
        (if facesCold.isEmpty then #[] else #[("faces", facesCold, facesWarm)])
      for (what, c, w) in rows do
        IO.println s!"{padRight s!"leantex  {name} {what}, cold" 42} {padLeft (toString (median c)) 6} ms (median of {n})"
        IO.println s!"{padRight s!"leantex  {name} {what}, warm" 42} {padLeft (toString (median w)) 6} ms (median of {n})"

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--doc-cost" then return ← docCost args.tail
  if args == ["--slides-selftest"] then
    Slides.selftest
    return 0
  let leantex ← compiler
  let n := ((← IO.getEnv "N").bind (·.toNat?)).getD 5
  if n == 0 then die "N must be positive"
  if args == ["--bib-only"] then
    benchBibGrowth n
    return 0
  if args == ["--passes-only"] then
    benchPasses n
    return 0
  if args == ["--slides-only"] then
    Slides.run n
    return 0
  if args == ["--slides-compressed-only"] then
    Slides.run n true
    return 0
  if args == ["--listings-only"] then
    benchListings n 1
    benchListings n 8
    listingGrowth n
    return 0
  if let ["--pdf-pages-only", file] := args then
    benchPdfPages n file
    return 0
  if let "--faces-only" :: files := args then
    benchFaces n files
    return 0
  if args == ["--svg-only"] then
    for count in [4, 16] do benchSvg n count
    return 0
  if args == ["--boundary-only"] then
    unless ← hasCmd "lualatex" do die "picture benchmark needs lualatex"
    benchPictures n 8
    benchPictures n 16
    return 0
  if args == ["--decode-only"] then
    benchDecode n
    return 0
  if args == ["--concurrency-only"] then
    unless ← hasCmd "pdftocairo" #["-v"] do
      die "HTML vector benchmark needs pdftocairo"
    for count in [8, 32] do benchConcurrent n count false
    for count in [8, 16] do benchConcurrent n count true
    return 0
  let genLorem ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--run", "scripts/gen-lorem.lean"] }
  if genLorem.exitCode != 0 then
    die s!"gen-lorem failed:\n{genLorem.stderr}"
  let genPaper ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", "--run", "scripts/gen-paper.lean"] }
  if genPaper.exitCode != 0 then
    die s!"gen-paper failed:\n{genPaper.stderr}"
  let haveLualatex ← hasCmd "lualatex"
  for doc in ["testdata/corpus/paragraphs.tex", "bench/lorem.tex", "bench/underline.tex"] do
    let base := (doc.splitOn "/").getLastD doc
    bench n s!"leantex  {base}" leantex #["-q", "build", doc]
    if haveLualatex then
      let workdir ← IO.FS.createTempDir
      IO.FS.writeBinFile (workdir / base) (← IO.FS.readBinFile doc)
      bench n s!"lualatex {base}" "lualatex"
        #["--interaction=batchmode", s!"--output-directory={workdir}", (workdir / base).toString]
      IO.FS.removeDirAll workdir
  -- A themed deck, leantex only: the theme passes and the HTML backend.
  let outDir ← IO.FS.createTempDir
  bench n "leantex  themed.tex" leantex
    #["-q", "build", "testdata/corpus/themed.tex", "-o", (outDir / "themed.pdf").toString]
  bench n "leantex  themed.tex -o html" leantex
    #["-q", "build", "testdata/corpus/themed.tex", "-o", (outDir / "themed.html").toString]
  -- The paper-shaped fixture, leantex only: one-run citation resolution.
  bench n "leantex  paper.tex" leantex
    #["-q", "build", "bench/paper.tex", "-o", (outDir / "paper.pdf").toString]
  bench n "leantex  paper.tex -o html" leantex
    #["-q", "build", "bench/paper.tex", "-o", (outDir / "paper.html").toString]
  IO.FS.removeDirAll outDir
  benchImageDeck n 32
  benchImageDeck n 128
  benchDecode n
  benchListings n 8
  listingGrowth n
  benchBibGrowth n
  benchPasses n
  return 0
