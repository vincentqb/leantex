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
def hybrid (path : Option String) (cwd : Except Failure String) : (q : Ask) → BaseIO (Reply q)
  | .env "PATH" => pure path
  | .cwd => pure cwd
  | q => Host.answer q

def under {α : Type} (path : String) (cwd : Except Failure String) (p : Prog α) : BaseIO α :=
  p.runM (hybrid (some path) cwd)

/-- One spelling per directory entry: `.` components and repeated
separators name the same place. -/
def normalPath (p : String) : String :=
  let parts := (p.splitOn "/").filter fun s => !s.isEmpty && s != "."
  (if p.startsWith "/" then "/" else "") ++ String.intercalate "/" parts

/-- A fixture tool: its version line, then the path it was started by. -/
def tool (path : System.FilePath) (label : String) (exec : Bool := true) : IO Unit :=
  writeScript path s!"#!/bin/sh\nprintf '%s\\n' '{label} 1.0' \"$0\"\n" exec

/-- execvp's own choice, the oracle every PATH row is held to: the command
name spawned by Lean's runtime, which calls execvp, under that PATH from that
directory. The kernel hands a script the path execve was given, so a
fixture's `$0` is the candidate execvp started, read back absolute. -/
def execvpChoice (path : String) (cwd : System.FilePath) (name : String) :
    IO (Option String) := do
  let got ← RunBounded.runBounded name #[] cwd 10000 100 (env := #[("PATH", some path)])
  unless got.complete && got.ran == .exited 0 do return none
  let some started := (got.out.splitOn "\n")[1]? | return none
  return some (if started.startsWith "/" then started else ToolPath.join cwd.toString started)

/-- A file's identity as every earlier memo and slot spelled it. -/
def legacyStamp (p : System.FilePath) : IO String := do
  let md ← p.metadata
  return String.intercalate "\t" [(← IO.FS.realPath p).toString, toString md.byteSize,
    toString md.modified.sec, toString md.modified.nsec]

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
  t "world/replay: the shipped interpreter returns the recorded run's result"
    ((← Host.runIO prog) == answer)
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
  let secret := dir / "outside-secret"
  IO.FS.writeFile secret "not the tool's"
  let linked ← Host.answer (.run { call "/bin/sh"
      #["-c", "ln -s \"$1\" out.txt; mkdir sub; ln -s \"$2\" sub/up", "sh", secret.toString, dir.toString]
      10000 with
    outputs := #["out.txt", "sub/up/outside-secret"] })
  t "world/host: a declared output that links outside the scratch directory is no output"
    (linked.complete && linked.ran == .exited 0 &&
      linked.outputs == #[("out.txt", none), ("sub/up/outside-secret", none)])
  -- A directory outside every scratch directory, with a file and a subtree.
  let outsideAt (name : String) : IO (System.FilePath × IO Bool) := do
    let outside := dir / name
    IO.FS.createDirAll (outside / "keep")
    IO.FS.writeFile (outside / "outside-secret") "not the tool's"
    IO.FS.writeFile (outside / "keep" / "file") "kept"
    return (outside, do
      return (← (outside / "outside-secret").pathExists) && (← (outside / "keep" / "file").pathExists))
  let (outside, untouched) ← outsideAt "outside"
  let moved ← Host.answer (.run { call "/bin/sh"
      #["-c", "d=$PWD; mv \"$d\" \"$d.moved\" && ln -s \"$1\" \"$d\" && printf '%s' \"$d\"", "sh",
        outside.toString] 10000 with
    outputs := #["outside-secret"] })
  let movedScratch := moved.out.trimAscii.toString
  t "world/host: a run that leaves a link where its scratch directory stood gets nothing outside back"
    (moved.complete && moved.ran == .exited 0 && moved.outputs == #[("outside-secret", none)])
  t "world/host: cleanup removes a link where the scratch directory stood, and nothing it names"
    (!movedScratch.isEmpty && (← untouched) && !(← System.FilePath.pathExists movedScratch))
  unless movedScratch.isEmpty do
    discard <| (IO.FS.removeDirAll (movedScratch ++ ".moved")).toBaseIO
  let (elsewhere, kept) ← outsideAt "elsewhere"
  let linkedAway ← Host.answer (.run (call "/bin/sh"
    #["-c", "ln -s \"$1\" away && ln -s /nonexistent-leantex-target dangling && mkdir -p a/b && " ++
      "ln -s \"$1\" a/b/away && printf '%s' \"$PWD\"", "sh", elsewhere.toString] 10000))
  let awayScratch := linkedAway.out.trimAscii.toString
  t "world/host: cleanup removes the links a run left, dangling or to a directory outside, and nothing they name"
    (linkedAway.complete && linkedAway.ran == .exited 0 && (← kept) && !awayScratch.isEmpty &&
      !(← System.FilePath.pathExists awayScratch))
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

/-- Every PATH spelling that names a different rule, held to the path the
fixture determines and to execvp itself, never to a shell's `command -v`,
whose answers differ between shells. A deleted working directory is empty,
so execvp finds nothing under a relative entry that stays inside it; the
cache identity child checks a really removed one. -/
def pathChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let t := check ref
  let root ← IO.FS.realPath dir
  let r := root.toString
  tool (root / "abs" / "tool") "abs"
  tool (root / "rel" / "bin" / "tool") "rel"
  tool (root / "tool") "here"
  tool (root / "real" / "tool") "real"
  tool (root / "decoy" / "tool") "decoy" (exec := false)
  IO.FS.createDirAll (root / "lnk")
  symlink (root / "abs" / "tool") (root / "lnk" / "tool")
  IO.FS.createDirAll (root / "dirtool" / "tool")
  let call := ToolPath.versionCall 10000
  let rows : List (String × String × String × String) := [
    ("absolute entry", s!"{r}/abs", s!"{r}/abs/tool", s!"{r}/abs/tool"),
    ("relative entry", "rel/bin", s!"{r}/rel/bin/tool", s!"{r}/rel/bin/tool"),
    ("empty entry", ":/nonexistent-leantex-entry", s!"{r}/tool", s!"{r}/tool"),
    ("empty last entry", "/nonexistent-leantex-entry:", s!"{r}/tool", s!"{r}/tool"),
    ("trailing slash", s!"{r}/abs/", s!"{r}/abs/tool", s!"{r}/abs/tool"),
    ("symlink", s!"{r}/lnk", s!"{r}/lnk/tool", s!"{r}/lnk/tool"),
    ("a directory named like the tool", s!"{r}/dirtool:{r}/abs", s!"{r}/abs/tool",
      s!"{r}/abs/tool"),
    ("a decoy the OS refuses", s!"{r}/decoy:{r}/real", s!"{r}/real/tool", s!"{r}/decoy/tool")]
  for (label, path, started, first) in rows do
    let oracle ← execvpChoice path root "tool"
    let probed ← under path (.ok r) (ToolPath.probe "tool" call)
    let resolved ← under path (.ok r) (ToolPath.resolve "tool")
    t s!"world/path {label}: execvp starts {oracle}, the fixture's {started}"
      (oracle.map normalPath == some (normalPath started))
    t s!"world/path {label}: the probe starts {probed.map (·.1)}, as execvp does"
      (probed.map (normalPath ·.1) == some (normalPath started))
    t s!"world/path {label}: stats alone take the first regular file {resolved}"
      (resolved.map normalPath == some (normalPath first))
  let gonePath := s!"rel/bin:{r}/abs"
  t "world/path a removed cwd with a relative entry: only the absolute entry is a candidate"
    ((← under gonePath (.error .absent) (ToolPath.resolve "tool")) == some s!"{r}/abs/tool" &&
      ((← under gonePath (.error .absent) (ToolPath.probe "tool" call)).map (·.1)) ==
        some s!"{r}/abs/tool")
  let decoyPath := s!"{r}/decoy:{r}/real"
  t "world/path decoy: the version is the tool that started"
    ((← under decoyPath (.ok r) (ToolPath.version "tool")) == .present "real 1.0")
  t "world/path decoy: a PATH of only refused candidates identifies no tool"
    (match ← under s!"{r}/decoy" (.ok r) (ToolPath.version "tool") with
      | .absent _ => true
      | .present _ => false)
  t "world/path: one regular file's witness keeps the spelling earlier memos and slots were keyed by"
    ((← under s!"{r}/abs" (.ok r) (ToolPath.witness "tool")) == (← legacyStamp (root / "abs" / "tool")))
  t "world/path decoy: the witness stamps every regular file the name reaches"
    ((← under decoyPath (.ok r) (ToolPath.witness "tool")) ==
      (← legacyStamp (root / "decoy" / "tool")) ++ "\t" ++ (← legacyStamp (root / "real" / "tool")))
  let memo := root / "tool.ver"
  let identifyNow (probe : IO PicCache.Tool) : IO PicCache.Tool := do
    ToolProbe.identify memo (← under decoyPath (.ok r) (ToolPath.witness "tool")) probe
  let probe : IO PicCache.Tool := under decoyPath (.ok r) (ToolPath.version "tool")
  let cold ← identifyNow probe
  let warm ← identifyNow (pure (.absent "unexpected probe"))
  writeScript (root / "real" / "tool") "#!/bin/sh\nprintf '%s\\n' 'real 2.0 upgraded' \"$0\"\n"
  let upgraded ← identifyNow probe
  t "world/path decoy: an upgrade of the file that runs behind a decoy is probed again"
    (cold == .present "real 1.0" && warm == .present "real 1.0" &&
      upgraded == .present "real 2.0 upgraded")
  let unset {α : Type} (p : Prog α) : BaseIO α := p.runM (hybrid none (.ok r))
  t "world/path: an unset PATH resolves nothing and gives no witness"
    ((← unset (ToolPath.resolve "tool")) == none && (← unset (ToolPath.witness "tool")) == "")
  let bareCall (exe : String) : ToolCall :=
    { tool := exe, args := #[], budgetMs := 10000, graceMs := 100, captureLimit := 65536,
      env := #[("PATH", none)] }
  let started ← unset (ToolPath.probe "sh" bareCall)
  t s!"world/path: with PATH unset the probe runs the bare name and execvp's default path finds it ({started.map (·.1)})"
    (match started with
      | some (exe, e) => exe == "sh" && e.complete && e.ran == .exited 0
      | none => false)
  t "world/path: with PATH unset a name the default path lacks starts nothing"
    ((← unset (ToolPath.probe "leantex-no-such-tool" bareCall)).isNone)
  writeScript (root / "hang" / "tool") "#!/bin/sh\nexec sleep 30\n"
  let start ← IO.monoMsNow
  let hung ← under s!"{r}/hang" (.ok r) (ToolPath.version "tool" (budgetMs := 300))
  let spent := (← IO.monoMsNow) - start
  t s!"world/path: a version question that hangs is killed within its budget ({spent} ms)"
    ((match hung with | .absent _ => true | .present _ => false) && spent < 4000)

/-- The driver's own entry point, `ToolProbe.probeVersion` at its default
budget, under a version question that never ends: a child whose PATH starts
with a shim that sleeps. An unbounded probe holds the child past the
parent's budget. -/
def probeChildChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let (lean, leanPath) ← leanChild "world checks"
  writeScript (dir / "hang" / "leantex-hang-probe") "#!/bin/sh\nexec sleep 30\n"
  let driver := dir / "probe.lean"
  IO.FS.writeFile driver <|
    "import LeanTex.Cli.ToolProbe\n" ++
    "def main : IO UInt32 := do\n" ++
    "  let start ← IO.monoMsNow\n" ++
    "  let got ← LeanTex.Cli.ToolProbe.probeVersion \"leantex-hang-probe\"\n" ++
    "  let spent := (← IO.monoMsNow) - start\n" ++
    "  IO.println s!\"probe ended after {spent} ms\"\n" ++
    "  return match got with\n" ++
    "    | .absent _ => if spent < 5000 then 0 else 2\n" ++
    "    | .present _ => 1\n"
  let path := s!"{dir / "hang"}:{(← IO.getEnv "PATH").getD ""}"
  let result ← RunBounded.runBounded lean.toString #["--run", driver.toString] dir 20000 100
    (env := #[("PATH", some path), ("LEAN_PATH", some leanPath)])
  check ref s!"world/path: the driver's version probe ends a tool that hangs: {result.out}{result.err}"
    (result.complete && result.ran == .exited 0)

/-- A run under a temporary root that cannot hold its scratch directory, in a
child whose TMPDIR names a missing directory: the reply is a run that never
started. `IO.FS.createTempDir` ends such a process with a segmentation fault
on Lean v4.34.1. -/
def scratchChildChecks (ref : IO.Ref (List String)) (dir : System.FilePath) : IO Unit := do
  let (lean, leanPath) ← leanChild "world checks"
  let driver := dir / "scratch.lean"
  IO.FS.writeFile driver <|
    "import LeanTex.Cli.Host\n" ++
    "def main : IO UInt32 := do\n" ++
    "  let call : LeanTex.Cli.World.ToolCall :=\n" ++
    "    { tool := \"/bin/sh\", args := #[\"-c\", \"true\"], budgetMs := 5000, graceMs := 100, captureLimit := 1024 }\n" ++
    "  let e ← LeanTex.Cli.Host.answer (.run call)\n" ++
    "  IO.println s!\"ran {repr e.ran}\"\n" ++
    "  return match e.ran with\n" ++
    "    | .unstarted _ => 0\n" ++
    "    | _ => 1\n"
  let result ← RunBounded.runBounded lean.toString #["--run", driver.toString] dir 20000 100
    (env := #[("TMPDIR", some (dir / "no-such-root").toString), ("LEAN_PATH", some leanPath)])
  check ref s!"world/host: a run under a missing temporary root never starts, and the host answers ({repr result.ran}): {result.out}{result.err}"
    (result.complete && result.ran == .exited 0)

def checks (ref : IO.Ref (List String)) : IO Unit :=
  IO.FS.withTempDir fun dir => do
    for part in ["replay", "faults", "path", "child", "scratch"] do IO.FS.createDirAll (dir / part)
    replayChecks ref (dir / "replay")
    faultChecks ref (dir / "faults")
    pathChecks ref (dir / "path")
    probeChildChecks ref (dir / "child")
    scratchChildChecks ref (dir / "scratch")

end Tests.World
