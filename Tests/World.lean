module

public import LeanTex.Cli.Host
public import LeanTex.Cli.ToolProbe
public import Tests.Support
public import LeanTex.Cli.RunBounded

public section

open LeanTex.Cli
open LeanTex.Cli.World

namespace Tests.World

/-- A world read off a trace, `dflt` answering every question the trace
does not hold. -/
def traceWorld (tr : List Fact) (dflt : (q : Ask) → Reply q) : (q : Ask) → Reply q :=
  fun q => match tr.find? (·.1 == q) with
    | some ⟨q', r⟩ => if h : q' = q then h ▸ r else dflt q
    | none => dflt q

def quiet : (q : Ask) → Reply q
  | .env _ => none
  | .cwd => .error .absent
  | .stat _ => .error .absent
  | .readFile _ => .error .absent
  | .listDir _ => .error .absent
  | .run _ => { ran := .unstarted "unasked", out := "", err := "", complete := false, outputs := #[] }
  | .writeAtomic .. => .error .absent
  | .createDirAll _ => .error .absent

def loud : (q : Ask) → Reply q
  | .env _ => some "loud"
  | .cwd => .ok "/loud"
  | .stat p => .ok { kind := .file, size := 7, mtimeSec := 1, mtimeNsec := 0, real := p }
  | .readFile _ => .ok "loud".toUTF8
  | .listDir _ => .ok #[("loud", .file)]
  | .run _ => { ran := .exited 0, out := "loud\n", err := "", complete := true, outputs := #[] }
  | .writeAtomic .. => .ok ()
  | .createDirAll _ => .ok ()

/-- Sizes of the regular files a directory lists, and whether a variable
is set: a program whose later questions depend on earlier replies. -/
def sizes (dir : String) : Prog String := do
  match ← ask (.listDir dir) with
  | .error _ => return "unlisted"
  | .ok entries =>
    let mut seen := #[]
    for (name, kind) in entries do
      if kind == .file then
        match ← ask (.readFile (ToolPath.join dir name)) with
        | .ok bytes => seen := seen.push s!"{name}={bytes.size}"
        | .error _ => seen := seen.push s!"{name}=?"
    let unset ← ask (.env "LEANTEX_WORLD_CHECK_UNSET")
    return s!"{String.intercalate "," seen.toList};{unset.isSome}"

/-- The host with PATH and the working directory replaced: every other
question is the machine's. -/
def hybrid (path : String) (cwd : Except Failure String) : (q : Ask) → BaseIO (Reply q)
  | .env "PATH" => pure (some path)
  | .cwd => pure cwd
  | q => Host.answer q

def under {α : Type} (path : String) (cwd : Except Failure String) (p : Prog α) : BaseIO α :=
  p.runM (hybrid path cwd)

/-- One spelling per directory entry: `.` components and repeated
separators name the same place. -/
def normalPath (p : String) : String :=
  let parts := (p.splitOn "/").filter fun s => !s.isEmpty && s != "."
  (if p.startsWith "/" then "/" else "") ++ String.intercalate "/" parts

/-- POSIX's own answer: the shell's `command -v` under that PATH, from that
directory (removed first when `remove` is set). -/
def commandV (path : String) (cwd : System.FilePath) (remove : Bool) (tool : String) :
    IO (Option String) := do
  let script := (if remove then "command -p rmdir \"$PWD\" || exit 3\n" else "") ++ "command -v \"$1\""
  let out ← IO.Process.output {
    cmd := "/bin/sh", args := #["-c", script, "sh", tool], cwd := some cwd,
    env := #[("PATH", some path), ("PWD", none)] }
  return if out.exitCode == 0 then some out.stdout.trimAscii.toString else none

def symlink (target link : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  unless out.exitCode == 0 do throw <| IO.userError s!"ln -s failed: {out.stderr}"

def script (path : System.FilePath) (body : String) (exec : Bool := true) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path ("#!/bin/sh\n" ++ body ++ "\n")
  IO.setAccessRights path
    { user := ⟨true, true, exec⟩, group := ⟨true, false, exec⟩, other := ⟨true, false, exec⟩ }

/-- A recorded program is the replay of its trace, and a world that differs
only where the program never asked gives the same answer. -/
def replayChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let t := check ref
  let root := dir / "listed"
  IO.FS.createDirAll (root / "sub")
  IO.FS.writeFile (root / "b.txt") "bb"
  IO.FS.writeFile (root / "a.txt") "a"
  IO.FS.writeFile (root / "c.txt") "ccc"
  let prog := sizes root.toString
  let (answer, trace) ← Host.recordIO prog
  t "world/replay: the synthetic program read the directory in name order"
    (answer == "a.txt=1,b.txt=2,c.txt=3;false")
  t "world/replay: the recorded run is the replay of its trace"
    (prog.replay trace == some answer)
  t "world/replay: the trace holds exactly the questions the program asked"
    (trace.map (·.1) == prog.asks (traceWorld trace quiet))
  t "world/replay: replies the program never read change nothing"
    (prog.run (traceWorld trace quiet) == answer && prog.run (traceWorld trace loud) == answer)
  let listing : Ask := .listDir root.toString
  let emptied : (q : Ask) → Reply q := fun q =>
    if h : listing = q then h ▸ (.ok #[] : Reply listing) else traceWorld trace quiet q
  t "world/replay: a reply the program read does move it"
    (prog.run emptied == ";false")
  t "world/replay: a trace that runs short or runs long replays nothing"
    (prog.replay trace.dropLast == none &&
      prog.replay (trace ++ [⟨.cwd, .ok "/extra"⟩]) == none)
  let (_, witnessTrace) ← Host.recordIO (ToolPath.witness "lean")
  t "world/replay: taking a witness records no run"
    (!witnessTrace.isEmpty && witnessTrace.all fun f => !f.1.isRun)

/-- Every question the host can be asked comes back as a typed reply,
however the filesystem or the tool misbehaves. -/
def faultChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let t := check ref
  let missing := (dir / "missing").toString
  let isAbsent {α : Type} (r : Except Failure α) : Bool := match r with
    | .error .absent => true
    | _ => false
  t "world/host: a missing path is absent to stat, read and listing"
    (isAbsent (← Host.answer (.stat missing)) && isAbsent (← Host.answer (.readFile missing)) &&
      isAbsent (← Host.answer (.listDir missing)))
  t "world/host: a directory read as a file is refused, not read"
    (match ← Host.answer (.readFile dir.toString) with | .error .notRegular => true | _ => false)
  t "world/host: a directory's stat says so"
    (match ← Host.answer (.stat dir.toString) with | .ok st => st.kind == .dir | _ => false)
  let locked := dir / "locked"
  IO.FS.writeFile locked "secret"
  IO.setAccessRights locked {}
  let lockedDir := dir / "lockedDir"
  IO.FS.createDir lockedDir
  IO.setAccessRights lockedDir {}
  let direct ← (IO.FS.readBinFile locked).toBaseIO
  let directDir ← (System.FilePath.readDir lockedDir).toBaseIO
  t "world/host: a mode 000 file is denied, as the OS denies it"
    (match direct, ← Host.answer (.readFile locked.toString) with
      | .error (.permissionDenied ..), .error .denied => true
      | .ok bytes, .ok got => bytes == got
      | _, _ => false)
  t "world/host: a mode 000 directory's listing is denied, as the OS denies it"
    (match directDir, ← Host.answer (.listDir lockedDir.toString) with
      | .error (.permissionDenied ..), .error .denied => true
      | .ok _, .ok _ => true
      | _, _ => false)
  IO.setAccessRights lockedDir { user := ⟨true, true, true⟩ }
  let fifo := dir / "fifo"
  let made ← IO.Process.output { cmd := "mkfifo", args := #[fifo.toString] }
  t "world/host: the FIFO fixture was made" (made.exitCode == 0)
  let read ← IO.asTask (Host.answer (.readFile fifo.toString)) Task.Priority.dedicated
  let mut waited := 0
  while !(← IO.hasFinished read) && waited < 5000 do
    IO.sleep 10
    waited := waited + 10
  let finished ← IO.hasFinished read
  t "world/host: a FIFO is refused without blocking"
    (finished && match read.get with | .ok (.error .notRegular) => true | _ => false)
  unless finished do
    discard <| IO.Process.output { cmd := "/bin/sh", args := #["-c", "printf x > \"$1\"", "sh", fifo.toString] }
  let listedDir := dir / "order"
  IO.FS.createDirAll (listedDir / "m")
  for name in ["q", "b", "z", "a"] do IO.FS.writeFile (listedDir / name) name
  symlink (listedDir / "q") (listedDir / "l")
  t "world/host: a listing is sorted by name, with each entry's kind"
    (match ← Host.answer (.listDir listedDir.toString) with
      | .ok entries => entries == #[("a", .file), ("b", .file), ("l", .symlink), ("m", .dir),
          ("q", .file), ("z", .file)]
      | .error _ => false)
  let call (tool : String) (args : Array String) (budgetMs : Nat) : ToolCall :=
    { tool, args, budgetMs, graceMs := 100, captureLimit := 65536 }
  let ghost := (dir / "no-such-tool").toString
  let absentRun ← Host.answer (.run (call ghost #["--version"] 10000))
  t "world/host: a tool that is not there ends as the exec-failure signature"
    (absentRun.complete && ToolPath.execFailed ghost absentRun)
  let start ← IO.monoMsNow
  let hung ← Host.answer (.run (call "/bin/sh" #["-c", "sleep 5"] 300))
  let spent := (← IO.monoMsNow) - start
  t s!"world/host: a run past its budget is killed and ends incomplete ({spent} ms)"
    (!hung.complete && hung.ran == .overran 0 && spent < 4000)
  let copied ← Host.answer (.run { call "/bin/sh" #["-c", "cat in/data > out.txt; pwd"] 10000 with
    inputs := #[("in/data", "payload".toUTF8)], outputs := #["out.txt", "never.txt"] })
  let scratch := copied.out.trimAscii.toString
  t "world/host: a run reads its inputs and returns its declared outputs"
    (copied.complete && copied.ran == .exited 0 &&
      copied.outputs == #[("out.txt", some "payload".toUTF8), ("never.txt", none)])
  t "world/host: a run's scratch directory is removed after it"
    (!scratch.isEmpty && !(← System.FilePath.pathExists scratch))
  let escaped ← Host.answer (.run { call "/bin/sh" #["-c", "true"] 10000 with
    inputs := #[("../escaped", "x".toUTF8)] })
  t "world/host: a run never writes outside its scratch directory"
    (match escaped.ran with | .unstarted _ => true | _ => false)
  let target := (dir / "published").toString
  t "world/host: an atomic write is read back whole"
    (match ← Host.answer (.writeAtomic target "whole".toUTF8),
        ← Host.answer (.readFile target) with
      | .ok (), .ok got => got == "whole".toUTF8
      | _, _ => false)
  t "world/host: an atomic write into a missing directory is absent"
    (isAbsent (← Host.answer (.writeAtomic (dir / "nowhere" / "x").toString ByteArray.empty)))
  let nested := (dir / "made" / "deep").toString
  t "world/host: a created directory tree stats as a directory"
    (match ← Host.answer (.createDirAll nested), ← Host.answer (.stat nested) with
      | .ok (), .ok st => st.kind == .dir
      | _, _ => false)
  let here ← IO.currentDir
  t "world/host: the working directory and PATH are answered"
    ((match ← Host.answer .cwd with
      | .ok d => d == here.toString
      | .error _ => false) && (← Host.answer (.env "PATH")).isSome)

/-- Resolution agrees with POSIX's `command -v` on every PATH spelling that
names a different rule, the decoy through the probe's fall-through. -/
def pathChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let t := check ref
  let root ← IO.FS.realPath dir
  let r := root.toString
  script (root / "abs" / "tool") "echo abs 1.0"
  script (root / "rel" / "bin" / "tool") "echo rel 1.0"
  script (root / "tool") "echo here 1.0"
  script (root / "real" / "tool") "echo real 1.0"
  script (root / "decoy" / "tool") "echo decoy 1.0" (exec := false)
  IO.FS.createDirAll (root / "lnk")
  symlink (root / "abs" / "tool") (root / "lnk" / "tool")
  IO.FS.createDirAll (root / "dirtool" / "tool")
  let rows : List (String × String × Bool) := [
    ("absolute entry", s!"{r}/abs", false),
    ("relative entry", "rel/bin", false),
    ("empty entry", ":/nonexistent-leantex-entry", false),
    ("empty last entry", "/nonexistent-leantex-entry:", false),
    ("trailing slash", s!"{r}/abs/", false),
    ("symlink", s!"{r}/lnk", false),
    ("a directory named like the tool", s!"{r}/dirtool:{r}/abs", false),
    ("a removed cwd with a relative entry", s!"rel/bin:{r}/abs", true)]
  for (label, path, remove) in rows do
    let cwdDir := if remove then root / "gone" else root
    if remove then IO.FS.createDirAll cwdDir
    let oracle ← commandV path cwdDir remove "tool"
    let cwd : Except Failure String := if remove then .error .absent else .ok cwdDir.toString
    let ours ← under path cwd (ToolPath.resolve "tool")
    t s!"world/path {label}: resolution {ours} agrees with command -v {oracle}"
      (oracle.isSome && ours.map normalPath == oracle.map normalPath)
  let decoyPath := s!"{r}/decoy:{r}/real"
  let oracle ← commandV decoyPath root false "tool"
  let statOnly ← under decoyPath (.ok r) (ToolPath.resolve "tool")
  let probed ← under decoyPath (.ok r) (ToolPath.probe "tool" (ToolPath.versionCall 10000))
  t s!"world/path decoy: stats alone take the first regular file {statOnly}"
    (statOnly == some s!"{r}/decoy/tool")
  t s!"world/path decoy: the probe falls through to {probed.map (·.1)}, as command -v {oracle}"
    (oracle == some s!"{r}/real/tool" && probed.map (·.1) == oracle)
  let version ← under decoyPath (.ok r) (ToolPath.version "tool")
  t "world/path decoy: the version is the tool that started"
    (version == .present "real 1.0")
  let refused ← under s!"{r}/decoy" (.ok r) (ToolPath.version "tool")
  t "world/path decoy: a PATH of only refused candidates identifies no tool"
    (match refused with | .absent _ => true | .present _ => false)
  t "world/path: an unset PATH resolves nothing"
    ((← (ToolPath.resolve "tool").runM (m := BaseIO) fun q => match q with
      | .env "PATH" => pure none
      | q => Host.answer q) == none)
  script (root / "hang" / "tool") "sleep 30"
  let start ← IO.monoMsNow
  let hung ← under s!"{r}/hang" (.ok r) (ToolPath.version "tool" (budgetMs := 300))
  let spent := (← IO.monoMsNow) - start
  t s!"world/path: a version question that hangs is killed within its budget ({spent} ms)"
    ((match hung with | .absent _ => true | .present _ => false) && spent < 4000)
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError "world checks require the Lean interpreter on PATH"
  let md ← lean.metadata
  let legacy := String.intercalate "\t" [(← IO.FS.realPath lean).toString,
    toString md.byteSize, toString md.modified.sec, toString md.modified.nsec]
  t "world/path: the witness keeps the spelling every existing memo and slot was keyed by"
    ((← ToolProbe.witness "lean") == legacy)

def checks (ref : IO.Ref (List String)) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    for part in ["replay", "faults", "path"] do IO.FS.createDirAll (dir / part)
    replayChecks ref (dir / "replay")
    faultChecks ref (dir / "faults")
    pathChecks ref (dir / "path")

end Tests.World
