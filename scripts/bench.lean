import Lean.Data.Json
import LeanTex.Cli.ConvCache
import LeanTex.Core.Image

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
`--slides-only` measures whole PDF and HTML builds of invented 8/32-slide
decks with repeated assets (N must be at least 3). Each pair starts with
empty private content AND font caches; the repeat is a new process over the same source and output
path. Cold means application caches, not the OS page cache. Phases and
image work counts come from verbose porcelain records. Cache inventories
are not hit counters for operations the compiler does not instrument.
Its gates are equivalence, invalidation and work counts, never milliseconds.
`--slides-compressed-only` applies those same checks to eight slides with a
256x256 dynamic-Huffman alpha PNG, exercising the token decoder rather than
stored blocks. Optional `LEANTEX_BENCH_COMPARE_BINARY` runs a second compiler
on the same fixtures and requires identical artifacts and diagnostics.
`--slides-selftest` tests those judges without compiling any documents.
`--decode-only` measures the decode phase alone over invented 3 MiB
documents: ASCII or accented words, LF or CR LF line ends.
The slide run also needs sha256sum, pdftocairo and xmllint.
For before/after runs use this same driver, N, font/tool environment and an
otherwise idle host; shared-host timings are provisional. Redirect stdout
to retain every sample, phase median and input/binary fingerprint.
`--doc-cost` reports what the invented reference documents of
`scripts/DocBench.lean` cost in sealed builds — cold and warm milliseconds,
edit-to-artifact latency under `--watch`, peak resident set size, bytes,
user-space instructions where `perf` runs, growth from `n` to `4n` — and the
peak of every corpus fixture (N defaults to 3 there), each against the last
run on this host class in `testdata/perf/documents.tsv`, the instructions held
to ±3% of it. It is `scripts/doccost.lean --bench`, whose script modules
`lake build` does not build, so it builds them, and the engine unless
`LEANTEX_BENCH_BINARY` names one, before it runs. `--doc-cost --record`
appends the run there, from a clean checkout of a commit main holds;
`--history <path>` compares with and records into a scratch history instead.
-/

def compiler : IO String := do
  return (← IO.getEnv "LEANTEX_BENCH_BINARY").getD ".lake/build/bin/leantex"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

/-- `--doc-cost`: `scripts/doccost.lean --bench` with the remaining arguments,
after building what it imports and the engine it measures, since
`lake env lean --run` interprets whatever the last build left. -/
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

/-- An invented `.bib` of `n` entries: half share their authors and year, so
the letters plainnat gives entries that share a label are in play. -/
def bibOf (n : Nat) : String := Id.run do
  let mut out := ""
  for i in [0:n] do
    let (au, yr) := if i % 2 == 0 then ("Alex Placeholder and Bryn Example", 2019)
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

/-- An invented document of about `mib` MiB, its words ASCII or accented and
its lines ending at LF or at CR LF: the shapes the decode phase's cost turns
on (a byte past 0x7F, a CR to settle). -/
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

/-- The milliseconds `-v` reports for the phase that reads a document's
bytes as text: `decode`, or `utf8` in a binary from before the decoding
door, so a before/after run reads both. -/
def decodePhaseMs (log : String) : Option Nat :=
  (log.splitOn "\n").findSome? fun l =>
    if l.startsWith "decode: " || l.startsWith "utf8: " then ((l.splitOn "(").getLast?.bind
      fun t => ((t.splitOn " ms").head?).bind (·.trimAscii.toString.toNat?)) else none

/-- The decode phase over an invented 3 MiB document of each shape, the
median of `n` runs of `-v dump`, which reads and elaborates and lays
nothing out: the cost of reading bytes as text, which every build pays
first. -/
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

/-- A repeated image must not repeatedly encode the embedded font programs
while checking HTML resource closure. Both sizes use the same captured assets. -/
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

/-- Measure the real picture boundary, not a synthetic sleep. A private
content cache makes each cold run comparable; the following warm run must
ship identical bytes and every requested picture must have a cached PDF. -/
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

structure Phase where
  name : String
  detail : String
  ms : Nat

/-- Keep timing out of the equivalence check; diagnostics retain their exact
structured fields and source order. The page count comes from the completed
compiler run, so a spilling fixture cannot silently change the workload. -/
structure Sample where
  ms : Nat := 0
  compilerMs : Nat
  diagnostics : Array String
  pages : Nat
  phases : Array Phase

def Sample.phase? (r : Sample) (name : String) : Option Phase :=
  r.phases.find? (·.name == name)

/-- A missing, duplicate or unsuccessful summary cannot certify a run.
Diagnostics are compared with all structured fields, in emission order. -/
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

/-- This is the existing images phase's detail protocol, not a guessed
count from cache filenames. The fixture has one cacheable alpha PNG. -/
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

/-- The same source/cache replay owes the same nonempty artifact, page
count, diagnostic order and resolved font environment. Timing is excluded. -/
def equivalent (pages : Nat) (a b : Sample) (x y : ByteArray) : Bool :=
  !x.isEmpty && x == y && a.pages == pages && b.pages == pages &&
    a.diagnostics == b.diagnostics &&
    a.phases.map (·.name) == b.phases.map (·.name) &&
    (a.phase? "font").map (·.detail) == (b.phase? "font").map (·.detail) &&
    (a.phase? "fontdb").map (·.detail) == (b.phase? "fontdb").map (·.detail)

/-- The fixture must resolve only copied, unchanged fonts. Discovery still
visits host roots, so its cost remains dependent on the host font installation. -/
def fixtureFonts (root : String) (r : Sample) : Bool :=
  match (r.phase? "font").map (·.detail.splitOn " (") with
  | some [_, paths] =>
    if !paths.endsWith ")" then false else
    let paths := (paths.dropEnd 1).toString.splitOn ", "
    !paths.isEmpty && paths.all (·.startsWith (root ++ "/fonts/"))
  | _ => false

/-- A changed input owes changed bytes AND the fresh-cache answer. Merely
noticing a new cache file would also pass a stale artifact. -/
def invalidated (pages : Nat) (old changed fresh : ByteArray)
    (a b : Sample) : Bool :=
  old != changed && equivalent pages a b changed fresh

/-- Content answers must remain unchanged. Font-discovery TSVs are mutable
metadata (including hash-map row order); they are not content-cache entries.
Their resolved environment is checked by `equivalent` instead. -/
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

/-- Hash the executable outside timing. A native checksum avoids interpreting
two byte-by-byte fingerprint passes over a large debug executable. -/
def binaryHash (binary : System.FilePath) : IO String := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #["--", binary.toString] }
  let key := (result.stdout.splitOn " ").headD ""
  require (result.exitCode == 0 && key.length == 64 &&
    key.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) "could not SHA-256 the compiler"
  return key

def toolVersions : IO (Array (String × String)) := do
  let mut versions := #[]
  for (tool, args) in [("pdftocairo", #["-v"]), ("xmllint", #["--version"])] do
    let result ← IO.Process.output { cmd := tool, args }
    let version := (result.stdout ++ result.stderr).trimAscii.toString
    require (result.exitCode == 0 && !version.isEmpty) s!"could not read {tool}'s version"
    versions := versions.push (tool, version)
  return versions

def be32 (n : Nat) : ByteArray :=
  ⟨#[UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
    UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]⟩

-- PNG CRC-32 (ISO/IEC 15948 Annex D). The browser must accept the fixture
-- too; a header-only probe with dummy checksums would not establish that.
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

/-- Two same-sized RGBA fixtures, one filename. Changing the colour must
invalidate alpha decoding by content even when the dimensions are identical. -/
def raster (edited : Bool) : ByteArray := Id.run do
  let mut raw := ByteArray.empty
  for y in [:80] do
    raw := raw.push 0
    for x in [:128] do
      raw := raw ++ ⟨#[if edited then 200 else 40, UInt8.ofNat (x + y),
        if edited then 40 else 200, if x % 16 < 8 then 255 else 128]⟩
  return png 128 80 (Flate.deflateStored raw)

/-- Seeded low-entropy noise needs both literals and matches. Long flat runs
would hide repeated prefix copying in the compressed-token decoder. The edit
changes one colour sample, retaining the path, dimensions and alpha format. -/
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

/-- A font-free vector asset, generated outside timing. Its conversion
has no dependency on a host font substitution. -/
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

/-- Inventories witness published answers, not hits or tool invocations.
All current cache files are at the root or one directory below it. Refuse
a deeper layout rather than silently omit answers from the comparison. -/
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

/-- Only the child compiler is timed. Fixture generation, verification,
inventory hashing, and Lean/Lake compilation are outside the measurement. -/
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

/-- The edited input's cached build must agree with an empty-cache oracle,
then repeat without new answers. Invalidation checks are not timed samples. -/
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

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--doc-cost" then return ← docCost args.tail
  if args == ["--slides-selftest"] then
    Slides.selftest
    return 0
  let leantex ← compiler
  let n := ((← IO.getEnv "N").bind (·.toNat?)).getD 5
  if n == 0 then die "N must be positive"
  if args == ["--slides-only"] then
    Slides.run n
    return 0
  if args == ["--slides-compressed-only"] then
    Slides.run n true
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
  for doc in ["testdata/corpus/paragraphs.tex", "bench/lorem.tex", "bench/underline.tex"] do
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
    #["-q", "build", "testdata/corpus/themed.tex", "-o", (outDir / "themed.pdf").toString]
  bench n "leantex  themed.tex -o html" leantex
    #["-q", "build", "testdata/corpus/themed.tex", "-o", (outDir / "themed.html").toString]
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
  benchDecode n
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
