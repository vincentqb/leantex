module

public import Tests.Support
public import LeanTex.Cli.RunCost

public section

open LeanTex.Cli

/-- Every porcelain summary states the run's milliseconds and the engine's own peak resident set
(`rssKiB`). -/
def runCostChecks (ref : IO.Ref (List String))
    (executable : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  t "summary cost: the peak is appended after ms"
    (Render.porcelainDone "a.tex" "a.pdf" (some 3) 17 (some 2048) ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":true,\"output\":\"a.pdf\"," ++
      "\"pages\":3,\"errors\":0,\"ms\":17,\"rssKiB\":2048}")
  t "summary cost: an unmeasured peak is absent, never zero"
    (Render.porcelainDone "a.tex" "a.pdf" (some 3) 17 none ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":true,\"output\":\"a.pdf\"," ++
      "\"pages\":3,\"errors\":0,\"ms\":17}")
  t "summary cost: a build that sets no pages states none"
    (Render.porcelainDone "a.md" "a.html" none 17 none ==
      "{\"event\":\"summary\",\"file\":\"a.md\",\"ok\":true,\"output\":\"a.html\"," ++
      "\"errors\":0,\"ms\":17}")
  t "summary cost: a partial publication states what it wrote and its peak"
    (Render.porcelainSummary "a.tex" false 1 17 #["a.html"] (some 5) ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"output\":\"a.html\",\"errors\":1,\"ms\":17,\"rssKiB\":5}")
  t "summary cost: a refusal and a werror verdict carry it too"
    (Render.porcelainSummary "a.tex" false 2 17 (rssKiB := some 5) ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":2,\"ms\":17,\"rssKiB\":5}" &&
     Render.porcelainWerror "a.tex" 3 17 (some 5) ==
      "{\"event\":\"summary\",\"file\":\"a.tex\",\"ok\":false,\"errors\":0," ++
      "\"warnings\":3,\"ms\":17,\"rssKiB\":5}")
  let own ← RunCost.peakKiB
  t s!"summary cost: this platform measures a peak ({own})"
    (own.any (1024 ≤ ·))
  let binary ← IO.FS.realPath executable
  let corpus ← IO.FS.realPath testFonts
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (corpus / "SourceSerifPro-Regular.otf"))
    let head := "\\documentclass{article}\n\\fonts{ dir = \"fonts\", body = \"Source Serif Pro\" }\n\
      \\begin{document}\n"
    let cases : List (String × String × Array String × Nat) := [
      ("written", "An invented line.\n", #[], 1),
      ("refused", "An invented line.\n\\input{absent-part}\n", #[], 1),
      ("werror", "An invented \\texttt{line}.\n", #["--werror"], 2)]
    for (name, body, flags, summaries) in cases do
      let source := dir / s!"{name}.tex"
      IO.FS.writeFile source (head ++ body ++ "\\end{document}\n")
      let out ← IO.Process.output {
        cmd := binary.toString
        args := #["build", source.toString, "-o", (dir / s!"{name}.pdf").toString,
          "--porcelain"] ++ flags
        env := sealedRunEnv dir }
      let records := (out.stdout.splitOn "\n").filterMap (Lean.Json.parse · |>.toOption)
      let peaks := records.filterMap fun j =>
        if (j.getObjValAs? String "event").toOption == some "summary" then
          some ((j.getObjValAs? Nat "rssKiB").toOption)
        else none
      t s!"summary cost: the {name} run's summaries each state a peak ({peaks})"
        (peaks.length == summaries && peaks.all (·.any (1024 ≤ ·)))
    -- getrusage's maximum carries a parent's resident set across fork and exec.
    let held ← (← IO.FS.Handle.mk "/dev/zero" .read).read (USize.ofNat (256 * 1048576))
    let out ← IO.Process.output {
      cmd := binary.toString
      args := #["build", (dir / "written.tex").toString, "-o", (dir / "held.pdf").toString,
        "--porcelain"]
      env := sealedRunEnv dir }
    let peak := summaryPeak out.stdout
    t s!"summary cost: a run spawned by a process holding {held.size / 1048576} MiB states \
its own peak ({peak} KiB)"
      (peak.any (· < held.size / 1024))
    let staged ← IO.FS.realPath (dir / "fonts" / "SourceSerifPro-Regular.otf")
    let fontPhases (flags : Array String) : IO (List Lean.Json) := do
      let out ← IO.Process.output {
        cmd := binary.toString
        args := #["build", (dir / "written.tex").toString, "-o", (dir / "faces.pdf").toString,
          "--porcelain"] ++ flags
        env := sealedRunEnv dir }
      return (out.stdout.splitOn "\n").filterMap fun line =>
        (Lean.Json.parse line).toOption.filter fun j =>
          (j.getObjValAs? String "event").toOption == some "phase" &&
            (j.getObjValAs? String "name").toOption == some "font"
    let verbose ← fontPhases #["-v"]
    let paths := verbose.head?.bind fun j => (j.getObjValAs? (Array String) "faces").toOption
    let scanned := verbose.head?.bind fun j => (j.getObjValAs? Nat "scanned").toOption
    let loaded ← (paths.getD #[]).toList.mapM fun (p : String) => do
      return ((← (IO.FS.realPath (System.FilePath.mk p)).toBaseIO).toOption.map (·.toString)).getD p
    t s!"faces: the -v font phase names its one loaded face ({paths}) of {scanned} scanned"
      (verbose.length == 1 && loaded == [staged.toString] && scanned.any (1 ≤ ·))
    t "faces: a run that is not verbose writes no font phase" (← fontPhases #[]).isEmpty

/-- The resident memory of a running process in KiB, from `/proc/<pid>/status` where the platform
has one. -/
private def residentKiB (pid : UInt32) : IO (Option Nat) := do
  let .ok status ← (IO.FS.readFile s!"/proc/{pid}/status").toBaseIO | return none
  return (status.splitOn "\n").findSome? fun line =>
    if line.startsWith "VmRSS:" then
      match (line.drop 6).toString.trimAscii.toString.splitOn " " with
      | [n, "kB"] => n.toNat?
      | _ => none
    else none

/-- A watcher's records reach a reader as each build ends, and each rebuild states its own peak. -/
def watchDeliveryChecks (ref : IO.Ref (List String))
    (executable : System.FilePath := ".lake/build/bin/leantex") : IO Unit := do
  let t := check ref
  let binary ← IO.FS.realPath executable
  let corpus ← IO.FS.realPath testFonts
  IO.FS.withTempDir fun dir => do
    IO.FS.createDirAll (dir / "fonts")
    IO.FS.writeBinFile (dir / "fonts" / "SourceSerifPro-Regular.otf")
      (← IO.FS.readBinFile (corpus / "SourceSerifPro-Regular.otf"))
    let source := dir / "watched.tex"
    let para := "An invented paragraph of plain words, long enough to fill a line or two, \
      so that a long revision lays out pages of them and holds their memory while it does."
    let text (rev paragraphs : Nat) := s!"\\documentclass\{article}\n\\fonts\{ dir = \"fonts\", \
      body = \"Source Serif Pro\" }\n\\begin\{document}\nRevision {rev} of an invented line.\n\n\
      {String.join (List.replicate paragraphs (para ++ "\n\n"))}\\end\{document}\n"
    IO.FS.writeFile source (text 0 500)
    let child ← IO.Process.spawn {
      cmd := binary.toString
      args := #["build", source.toString, "-o", (dir / "watched.pdf").toString, "--porcelain",
        "--watch"]
      env := sealedRunEnv dir
      stdin := .null, stdout := .piped, stderr := .null }
    try
      let next := watcherSummary child.stdout
      let first ← next
      t "watch: the first build's summary reaches a pipe while the watcher runs" first.isSome
      if let some first := first then
        let long := summaryPeak first
        t s!"watch: the first build states its peak ({long} KiB)" (long.any (1024 ≤ ·))
        let mut rebuilds : Array (String × Option Nat) := #[]
        for rev in [1, 2] do
          -- Wait past the mtime granule, and rename into place so the watcher never reads half a file.
          IO.sleep 1100
          let held ← residentKiB child.pid
          IO.FS.writeFile (dir / "watched.next") (text rev 1)
          IO.FS.rename (dir / "watched.next") source
          match ← next with
          | some line => rebuilds := rebuilds.push (line, held)
          | none => break
        t "watch: the rebuilds answering two edits reach the pipe too" (rebuilds.size == 2)
        if ← RunCost.resetPeak then
          for (line, held) in rebuilds, k in [1:rebuilds.size + 1] do
            let peak := summaryPeak line
            t s!"watch: rebuild {k}'s peak ({peak} KiB) counts the {held} KiB held as it began"
              (match peak, held with
               | some p, some h => 31 * h ≤ 32 * p
               | some _, none => true
               | none, _ => false)
          if let some (last, _) := rebuilds[1]? then
            let short := summaryPeak last
            t s!"watch: the second short rebuild ({short} KiB) reads below the long revision's peak ({long} KiB)"
              (match long, short with
               | some a, some b => 8 * b < 7 * a
               | _, _ => false)
        else
          t "watch: where a peak cannot be reset, a rebuild states none"
            (rebuilds.all fun (l, _) => (summaryPeak l).isNone)
    finally
      try child.kill catch _ => pure ()
      discard child.wait
