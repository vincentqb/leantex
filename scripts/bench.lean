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

def hasCmd (cmd : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd, args := #["--version"] }
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
      unless (cached.filter (·.path.extension == some "pdf")).size == requests do
        die "picture benchmark did not render every external request"
      let bytes ← IO.FS.readBinFile output
      warm := warm.push (← run input)
      unless (← IO.FS.readBinFile output) == bytes do
        die "picture benchmark changed the PDF when replaying the same cache"
    for (label, times) in [("cold", cold), ("warm", warm)] do
      IO.println s!"{padRight s!"leantex  {requests} picture requests ({label})" 42} {padLeft (toString (median times)) 6} ms (median of {n})"

def main (args : List String) : IO UInt32 := do
  let leantex ← compiler
  let n := ((← IO.getEnv "N").bind (·.toNat?)).getD 5
  if args == ["--boundary-only"] then
    unless ← hasCmd "lualatex" do die "picture benchmark needs lualatex"
    benchPictures n 8
    benchPictures n 16
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
