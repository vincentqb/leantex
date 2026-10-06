import Lean.Data.Json
import LeanTex.Cli.ConvCache

/-
Benchmark leantex against lualatex on the bench corpus. Run from the
repository root after `lake build`:

  lake env lean --run scripts/bench.lean

Reference point, not a fair fight: lualatex loads formats and fonts per run,
and does far more. Median of N runs (env var `N`, default 5), milliseconds.
`LEANTEX_BENCH_BINARY` selects a saved compiler for before/after comparisons
over the same inputs, environment and benchmark driver.
`--boundary-only` measures independent picture requests with a cold and a
warm content cache, after warming font discovery.
`--concurrency-only` measures PDF compression and HTML image conversion
with private cold/warm caches, identical output bytes and diagnostic order.
-/

def compiler : IO String := do
  return (← IO.getEnv "LEANTEX_BENCH_BINARY").getD ".lake/build/bin/leantex"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

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

/-- An invented `.bib` of `n` entries: half share their authors and year, so
the letters plainnat gives entries that share a label are in play. -/
def bibOf (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    let (au, yr) := if i % 2 == 0 then ("Alex Placeholder and Blair Example", 2019)
      else (s!"Casey Invented{i} and Drew Sample{i}", 2000 + i % 20)
    out := out ++ s!"@misc\{k{i}, author = \{{au}}, title = \{Invented entry number {i}},\n\
      year = \{{yr}}}\n"
  return out

/-- The milliseconds `-v` reports for its `bib` phase: reading the `.bib`,
ordering and lettering the list, formatting every entry, resolving every
citation. -/
def bibPhaseMs (log : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun l =>
    if l.startsWith "bib: " then ((l.splitOn "(").getLast?.bind fun t =>
      ((t.splitOn " ms").head?).bind (·.trimAscii.toString.toNat?)) else none

/-- The reference-list phase over `entries` invented entries, every one
listed (`\nocite{*}` under plainnat, which sorts and letters them): the
median of `n` runs' `bib` phase. -/
def benchBib (n : Nat) (entries : Nat) : IO Nat := do
  let leantex ← compiler
  let dir ← IO.FS.createTempDir
  IO.FS.writeFile (dir / "refs.bib") (bibOf entries)
  IO.FS.writeFile (dir / "scale.tex")
    "\\documentclass{article}\n\\usepackage{natbib}\n\\bibliographystyle{plainnat}\n\
    \\begin{document}\nAlpha words \\citep{k0}.\n\\nocite{*}\n\\bibliography{refs}\n\
    \\end{document}\n"
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
  IO.println s!"{padRight s!"leantex  bib phase, {entries} entries" 42} {padLeft (toString ms) 6} ms (median of {n})"
  return ms

/-- A repeated image must not repeatedly encode the embedded font programs
while checking HTML resource closure. Both sizes use the same captured assets. -/
def benchImageDeck (n frames : Nat) : IO Unit := do
  let leantex ← compiler
  let fonts ← IO.FS.realPath "tests/corpus/fonts"
  let image ← IO.FS.readBinFile "tests/corpus/rects.png"
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

/-- Measure the real picture boundary, not a synthetic sleep. A private
content cache makes each cold run comparable; the following warm run must
ship identical bytes and every requested picture must have a cached PDF. -/
def benchPictures (n requests : Nat) : IO Unit := do
  let leantex ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "tests/corpus/fonts"
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
        -- Saved older compilers publish raw PDFs; current compilers publish
        -- checked answers, including refusals which must not count as drawings.
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

/-- Keep timing out of the equivalence check; diagnostics retain their exact
structured fields and source order. The page count comes from the completed
compiler run, so a spilling fixture cannot silently change the workload. -/
structure Sample where
  ms : Nat
  diagnostics : Array String
  pages : Nat

def sample (binary input output cache : System.FilePath) : IO Sample := do
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := binary.toString
    args := #["build", input.toString, "-o", output.toString, "--porcelain"]
    env := #[("XDG_CACHE_HOME", some cache.toString)] }
  let ms := (← IO.monoMsNow) - start
  if out.exitCode != 0 then die s!"benchmark compile failed:\n{out.stdout}{out.stderr}"
  let mut diagnostics := #[]
  let mut pages := none
  for line in (out.stdout ++ out.stderr).splitOn "\n" do
    if line.isEmpty then continue
    let record ← match Lean.Json.parse line with
      | .ok record => pure record
      | .error reason => die s!"benchmark needs JSON diagnostics: {reason}"
    match (record.getObjValAs? String "event").toOption with
    | some "diagnostic" =>
      if (record.getObjValAs? String "severity").toOption != some "note" then
        die s!"benchmark fixture has a rendering loss: {record.compress}"
      diagnostics := diagnostics.push record.compress
    | some "summary" =>
      if let .ok count := record.getObjValAs? Nat "pages" then pages := some count
    | _ => pure ()
  let some pageCount := pages | die "benchmark compile reported no output pages"
  return { ms, diagnostics, pages := pageCount }

/-- Each cache is owned by this benchmark's temporary directory. Font discovery
is warmed first; only the operation being measured is evicted between runs. -/
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

/-- Distinct page streams and captured vector images exercise the production
workers. Source PDFs are generated before timing; no TeX installation or
private document is involved. -/
def benchConcurrent (n requests : Nat) (images : Bool) : IO Unit := do
  let binary ← IO.FS.realPath (← compiler)
  let fonts ← IO.FS.realPath "tests/corpus/fonts"
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

def main (args : List String) : IO UInt32 := do
  let leantex ← compiler
  let n := ((← IO.getEnv "N").bind (·.toNat?)).getD 5
  if n == 0 then die "N must be positive"
  if args == ["--boundary-only"] then
    unless ← hasCmd "lualatex" do die "picture benchmark needs lualatex"
    benchPictures n 8
    benchPictures n 16
    return 0
  if args == ["--concurrency-only"] then
    unless (← hasCmd "pdftocairo" #["-v"]) && (← hasCmd "xmllint") do
      die "HTML vector benchmark needs pdftocairo and xmllint"
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
  for doc in ["tests/corpus/paragraphs.tex", "bench/lorem.tex", "bench/underline.tex"] do
    let base := (doc.splitOn "/").getLastD doc
    bench n s!"leantex  {base}" leantex #["-q", "build", doc]
    if haveLualatex then
      let workdir ← IO.FS.createTempDir
      IO.FS.writeBinFile (workdir / base) (← IO.FS.readBinFile doc)
      bench n s!"lualatex {base}" "lualatex"
        #["--interaction=batchmode", s!"--output-directory={workdir}", (workdir / base).toString]
      IO.FS.removeDirAll workdir
  -- The theme/roles/chrome and recovery passes run only on a themed deck,
  -- and the HTML backend was off the measured path entirely; leantex-only
  -- (lualatex does not build the native theme declarations).
  let outDir ← IO.FS.createTempDir
  bench n "leantex  themed.tex" leantex
    #["-q", "build", "tests/corpus/themed.tex", "-o", (outDir / "themed.pdf").toString]
  bench n "leantex  themed.tex -o html" leantex
    #["-q", "build", "tests/corpus/themed.tex", "-o", (outDir / "themed.html").toString]
  -- The paper-shaped fixture: sections, numbered equations with \eqref,
  -- floats with captions, natbib citations resolved from refs.bib in the
  -- same run — the one-run resolution that is the engine's headline claim.
  -- leantex-only, and that asymmetry is the honest story: a comparable
  -- lualatex figure needs lualatex+bibtex+lualatex twice (or latexmk),
  -- which this single-command runner deliberately does not spell.
  bench n "leantex  paper.tex" leantex
    #["-q", "build", "bench/paper.tex", "-o", (outDir / "paper.pdf").toString]
  bench n "leantex  paper.tex -o html" leantex
    #["-q", "build", "bench/paper.tex", "-o", (outDir / "paper.html").toString]
  IO.FS.removeDirAll outDir
  benchImageDeck n 32
  benchImageDeck n 128
  -- The reference list's growth: a thesis-sized .bib under \nocite{*} is
  -- thousands of entries, and a phase quadratic in them (75 s at 1600)
  -- passed every row above. Four times the entries may cost at most eight
  -- times the phase: linear is 4, n log n about 4.6, quadratic 16.
  let small ← benchBib n 400
  let big ← benchBib n 1600
  let ratio := (big * 10 + max small 1 / 2) / max small 1
  IO.println s!"{padRight "leantex  bib growth, 1600 / 400 entries" 42} {padLeft s!"{ratio / 10}.{ratio % 10}" 6} ×  (bound 8.0)"
  if big > 8 * max small 1 then
    die s!"the reference-list phase grew {ratio / 10}.{ratio % 10}× for 4× the entries (bound 8)"
  return 0
