/-
The parity ladder's tier. Run from the repository root:

  lake build parity
  .lake/build/bin/parity --selftest
  .lake/build/bin/parity --check      # the gate
  .lake/build/bin/parity --repin      # re-pin a comment-only edit
  .lake/build/bin/parity              # regenerate the baseline

The three tier modes are `Scoreboard.tierMain`'s, so the ratchet is the one
every tier shares (`Scoreboard.ratchet`): a fall fails, an unretired vanish
fails, an unrecorded rise fails as `stale`, and regeneration refuses to
write a fall no human-written `# lowered:` line authorises. Nothing here
decides any of that; this file measures, and says when a measurement is not
one.

Compiled rather than interpreted, for two reasons: it imports test-suite
internals other branches edit, so a build is what fails when one of them
moves; and interpreting it cost 7.4 s against 0.1 s for the binary.
`lake env lean --run scripts/parity.lean` works too, and is what the
scoreboard aggregate runs.

Nothing here invokes another engine, reads PATH, or touches the network: it
builds each fixture the way the driver builds it, reads the *committed*
reference beside it, and holds the level each pair reaches against
`testdata/scoreboard/parity.tsv`.

Two things stop a run before the ratchet sees it, in every mode, and exit 2
with nothing written:

  fault       the measurement is not of the committed pairings: a source or
              an input moved since its reference was built (regenerate, or
              `--repin` when only comments moved), or a sidecar or a
              reference cannot be read. Such a pairing is not measured.
  accounting  a fixture's `% diverges:` declaration does not account for
              where it stops — it excuses a level the fixture does not stop
              on, or the fixture reaches the top anyway. Either would sit in
              the file excusing the next regression. Correct the line, then
              `--repin`. A fixture that fell to such a stop, read against
              the committed floor by the one ratchet, is named as a fall
              first: that is the engine's to fix before the line is.

The oracle is never "must match". Every fixture's number is what the engine
reaches today; the ladder's whole claim is that it does not go down.
-/
import LeanTex.Cli.FontDiscovery
import scripts.ParityCore
import scripts.Board

open LeanTex.Core LeanTex.Cli Parity

/-- What one fixture reached, and why it stopped there. -/
structure Reached where
  fixture : String
  level : Int
  /-- The level that failed, and what it saw. Empty at the top. -/
  stopped : Option (Level × String)
  /-- What the fixture declares about its own pairing. -/
  declared : List Divergence
  /-- Anything worth printing that is not a verdict: the reference's own
  overfull count, a divergence the pairing declares. -/
  notes : Array String
  deriving Inhabited

/-- Does the fixture's declaration account for where it stopped? A stop at a
level some declared divergence excuses is explained; a declaration that does
not excuse the level the fixture stopped on explains nothing, which is the
`unexplained` arm and a failure; and reaching the top while declaring
anything at all is a declaration that `outlived` its stop, also a failure.
A fixture outside the denominator stops at no level, so anything it
declares is unexplained.

A fixture that declares nothing is `clean` whatever it reaches: the ladder
records the level it measures and does not ask for prose. What fails is a
declaration that is *wrong* — one that names a divergence which does not
account for the stop, and would therefore sit in the file excusing whatever
regression came next. -/
inductive Accounting where
  | explained (d : Divergence)
  | unexplained
  | outlived
  | clean
  deriving Repr, BEq, Inhabited

def accountingOf (r : Reached) : Accounting :=
  if r.declared.isEmpty then .clean
  else if r.level == refuses then .unexplained
  else match r.stopped with
    | none => .outlived
    | some (g, _) =>
      match r.declared.find? (·.excuses.contains g) with
      | some d => .explained d
      | none => .unexplained

/-- The engine's side of a pairing: the document elaborated, laid out and
written exactly as the driver writes it, then read back from its bytes.
`driverPdf` is the one spelling every artifact claim reads. -/
def engineSide (oneFace mathSet : Font.FontSet) (shipped : Array FontDb.Face)
    (pats : Hyphen.Patterns) (stem : String) :
    IO (Array Diag × Except String (Array ArtPage)) := do
  let src ← fixtureText (System.FilePath.mk parityDir / (stem ++ ".tex")).toString
  let (doc, diags) ← elabFixture stem src
  let geom := Layout.Geom.ofPage doc.page
  let fs ← fixtureFontSet oneFace mathSet shipped doc
  let out := layoutOf fs doc geom (some pats) {}
  let pdf := driverPdf fs geom doc out {}
  return (diags ++ out.diags, readArtifact pdf)

/-- Judge one pairing, level by level, stopping at the first that does not
hold. Cumulative by construction: the loop cannot reach a level whose
predecessor failed, so a level never has to restate its predecessor's
premise. -/
def judge (stem : String) (side : Sidecar) (declared : List Divergence)
    (engineDiags : Array Diag)
    (engine : Except String (Array ArtPage))
    (reference : Array ArtPage) : Reached := Id.run do
  let mut notes : Array String := #[]
  if 0 < side.overfull then
    notes := notes.push s!"the reference reports {side.overfull} overfull box(es)"
  unless side.compiles do
    return { fixture := stem, level := refuses, stopped := none, declared := declared
             notes := notes.push "the reference engine refuses this document, so it is outside the denominator" }
  let errs := engineDiags.filter fun d => d.severity == .error
  let stop (r : Level) (why : String) : Reached :=
    { fixture := stem, level := (Level.all.findIdx? (· == r)).getD 0, stopped := some (r, why)
      declared := declared, notes := notes }
  match engine with
  | .error e => return stop .build s!"the engine's own reader refuses its own bytes: {e}"
  | .ok ep =>
    let rp := reference
    unless errs.isEmpty do
      return stop .build s!"the engine raised {errs.size} error(s): \
{String.intercalate ", " (errs.toList.map (·.code))}"
    unless ep.size == rp.size do
      return stop .pages s!"engine {ep.size} pages, reference {rp.size}"
    for i in [0:ep.size] do
      let a := censusKey ep[i]!
      let b := censusKey rp[i]!
      unless a == b do
        return stop .census s!"p{i + 1}: {firstGap a b}"
    for i in [0:ep.size] do
      let a := orderKey ep[i]!
      let b := orderKey rp[i]!
      unless a == b do
        return stop .order s!"p{i + 1}: {firstGap a b}"
    for i in [0:ep.size] do
      let el := linesOf ep[i]!
      let rl := linesOf rp[i]!
      unless el.size == rl.size do
        return stop .lines s!"p{i + 1}: engine {el.size} line(s), reference {rl.size}"
      for j in [0:el.size] do
        unless el[j]! == rl[j]! do
          return stop .lines s!"p{i + 1} line {j + 1}: engine {repr el[j]!}, reference {repr rl[j]!}"
    return { fixture := stem, level := Level.all.length, stopped := none
             declared := declared, notes := notes }

/-- Why a run is not a measurement of the committed pairings: one
constructor per arm of `measureAll`, so a staged break is judged by the arm
it reached (`Fault.arm`) and never by the words of its sentence. -/
inductive Fault where
  | noSidecar
  | sidecarUnreadable (why : String)
  | declaration (why : String)
  | engineSourceMoved
  | referenceSourceMoved
  | inputGone (path : String)
  | inputMoved (path : String)
  | referenceNotRecorded
  | referenceUnreadable (why : String)
  deriving Repr, BEq, Inhabited

def Fault.render : Fault → String
  | .noSidecar => "no reference sidecar — regenerate it (scripts/parity-regen.lean)"
  | .sidecarUnreadable e => s!"the sidecar is unreadable: {e}"
  | .declaration e => e
  | .engineSourceMoved => "the engine's source has changed since its reference was built \
(if only a comment or a declaration moved, --repin clears it without the reference engine)"
  | .referenceSourceMoved => "the reference source has changed since the reference was built"
  | .inputGone p => s!"the reference read {p}, which is gone"
  | .inputMoved p => s!"{p} has changed since the reference read it"
  | .referenceNotRecorded => "the committed reference is not the one the sidecar records"
  | .referenceUnreadable e => s!"the committed reference is unreadable — {e}"

/-- The arm a fault came from, and the path it names: what the selftest
compares, never the sentence. -/
def Fault.arm : Fault → String
  | .noSidecar => "no-sidecar"
  | .sidecarUnreadable _ => "sidecar-unreadable"
  | .declaration _ => "declaration"
  | .engineSourceMoved => "engine-source-moved"
  | .referenceSourceMoved => "reference-source-moved"
  | .inputGone p => s!"input-gone {p}"
  | .inputMoved p => s!"input-moved {p}"
  | .referenceNotRecorded => "reference-not-recorded"
  | .referenceUnreadable _ => "reference-unreadable"

/-- One run over the corpus: what each fixture reached, and every reason the
run is not a measurement of the committed pairings at all, fixture by
fixture. A fault is collected rather than returned at once, so one run
names every one. -/
structure Measured where
  reached : Array Reached
  faults : Array (String × Fault)
  deriving Inhabited

/-- What every fixture is measured under: the shipped faces and the
hyphenation patterns, read once per run. -/
structure Env where
  pats : Hyphen.Patterns
  oneFace : Font.FontSet
  mathSet : Font.FontSet
  shipped : Array FontDb.Face

def envOf : IO Env := do
  let some fontData ← findFont | throw (IO.userError "parity: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "parity: corpus font unparsable")
  let oneFace := oneFaceOf font
  return { pats := Hyphen.english.get, oneFace, mathSet := ← mathSetOf oneFace
           shipped := ← FontDiscovery.scanRoots [testFonts] }

/-- Every pairing is read relative to the working directory — `testdata/parity`,
and the pinned inputs beside it — so the selftest drives this over a staged
copy by changing directory. -/
def measureWith (env : Env) : IO Measured := do
  let mut reached : Array Reached := #[]
  let mut faults : Array (String × Fault) := #[]
  for stem in ← parityNames do
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    unless ← sidecarPath.pathExists do
      faults := faults.push (stem, .noSidecar)
      continue
    let side ← match Sidecar.parse (← IO.FS.readFile sidecarPath) with
      | .ok s => pure s
      | .error e => do
          faults := faults.push (stem, .sidecarUnreadable e)
          continue
    -- The pairing's two halves, pinned. A source edited since the reference
    -- was built is a stale pairing, never a level result.
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrc ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
    let declared ← match declaredDivergences src with
      | .ok ds => pure ds
      | .error e => do
          faults := faults.push (stem, .declaration e)
          continue
    if srcKeyOf src != side.srcKey then
      faults := faults.push (stem, .engineSourceMoved)
    if srcKeyOf refSrc != side.refSrcKey then
      faults := faults.push (stem, .referenceSourceMoved)
    -- Every in-repo file the reference read, pinned. The shipped font is the
    -- one this catches: it is read by both engines, and an update to it
    -- would otherwise leave the engine on the new face and the committed
    -- reference on the old one, silently.
    for (p, k) in inputPins side.inputs do
      let path := System.FilePath.mk parityDir / p
      unless ← path.pathExists do
        faults := faults.push (stem, .inputGone p)
        continue
      if Flate.contentKey (← IO.FS.readBinFile path) != k then
        faults := faults.push (stem, .inputMoved p)
    let refPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let refBytes ← if ← refPath.pathExists then IO.FS.readBinFile refPath else pure .empty
    if side.compiles then
      if refBytes.size != side.pdfSize || Flate.contentKey refBytes != side.pdfKey then
        faults := faults.push (stem, .referenceNotRecorded)
    -- A pairing that is not the committed one has no level to report: the
    -- engine is not measured against a reference built from other inputs.
    if faults.any (·.1 == stem) then continue
    -- A reference the reader cannot read is a fault in the harness, not a
    -- level: every fixture would read as having fallen, and a regeneration
    -- would store it. One reader reads both sides, so a regression in it is
    -- exactly the thing a measurement must not be allowed to express.
    let rPages ← if side.compiles then
        match readArtifact refBytes with
        | .ok ps => pure ps
        | .error e => do
            faults := faults.push (stem, .referenceUnreadable e)
            continue
      else pure #[]
    let (diags, ePages) ← engineSide env.oneFace env.mathSet env.shipped env.pats stem
    reached := reached.push (judge stem side declared diags ePages rPages)
  return { reached, faults }

def measureAll : IO Measured := do measureWith (← envOf)

/-- The baseline's own header lines: what the integers mean. The ratchet's
rules are `Scoreboard`'s and are not restated here. -/
def provenance : Array String :=
  #[s!"# the parity ladder against lualatex: one integer per fixture, the number of \
levels that hold, of {Level.all.length}",
    s!"# ({String.intercalate ", " (Level.all.map fun l => s!"{l.tag} {l.word}")}); \
-1 means lualatex refuses the reference, which puts the fixture outside the denominator"]

def report (r : Reached) : IO Unit := do
  let stopped := match r.stopped with
    | some (g, why) => s!" — {g.tag} ({g.what}): {why}"
    | none => ""
  IO.println s!"{r.fixture}: level {levelName r.level}{stopped}"
  unless r.declared.isEmpty do
    IO.println s!"    declares: {String.intercalate ", " (r.declared.map Divergence.name)}"
  match accountingOf r with
  | .explained d => IO.println s!"    the stop is declared: {d.name} — {d.why}"
  | .unexplained => IO.println "    the stop is not declared by any divergence this fixture names"
  | .outlived => IO.println "    the fixture reaches the top, so its declaration explains nothing"
  | .clean => pure ()
  for n in r.notes do IO.println s!"    note: {n}"

/-- A declaration the gate refuses, with the fall behind it when there is
one: a fixture that fell to a stop its declaration never excused is a
regression before it is a wrong declaration. -/
structure Refusal where
  fixture : String
  /-- The committed level and the measured one, when the one ratchet reads a
  fall between them. -/
  fell : Option (Int × Int)
  stopped : Option (Level × String)
  accounting : Accounting
  declared : List Divergence
  deriving Inhabited

/-- The falls `Scoreboard.ratchet` reads between a committed baseline and
this measurement. An unreadable baseline reads none. -/
def fallsSince (board : String) (m : Measured) : Array Scoreboard.Change :=
  match Scoreboard.parse board with
  | .error _ => #[]
  | .ok base =>
    let rows := m.reached.map fun r => ({ item := r.fixture, value := r.level } : Scoreboard.Row)
    let now : Scoreboard.Tsv :=
      { provenance := #[], rows, retired := #[], lowered := #[], encoding := some .raw }
    (Scoreboard.ratchet base now).losses.filter fun
      | .fell .. => true
      | _ => false

/-- The declarations the gate refuses, the fixtures that fell first. -/
def refusals (m : Measured) (falls : Array Scoreboard.Change) : Array Refusal := Id.run do
  let fellOf (f : String) : Option (Int × Int) := falls.findSome? fun
    | .fell i o n => if i == f then some (o, n) else none
    | _ => none
  let mut fell : Array Refusal := #[]
  let mut rest : Array Refusal := #[]
  for r in m.reached do
    let a := accountingOf r
    unless a == .unexplained || a == .outlived do continue
    let x : Refusal := { fixture := r.fixture, fell := fellOf r.fixture, stopped := r.stopped
                         accounting := a, declared := r.declared }
    if x.fell.isSome then fell := fell.push x else rest := rest.push x
  for x in rest do fell := fell.push x
  return fell

/-- A measurement held against the baseline. `main` is `measureAll` then
this, so the selftest drives exactly the path that ships with measurements
it wrote by hand. -/
def gate (m : Measured) (args : List String) : IO UInt32 := do
  for r in m.reached do report r
  if !m.faults.isEmpty then
    IO.eprintln "parity: the measurement is not of the committed pairings, so nothing is judged \
and nothing is written"
    for (stem, f) in m.faults do IO.eprintln s!"    {stem}: {f.render}"
    IO.eprintln "  Regenerate with: lake env lean --run scripts/parity-regen.lean --force <fixture>"
    IO.println (Scoreboard.tierLine "parity" 0 0 0 "fault")
    return 2
  let refused := refusals m (fallsSince (← Scoreboard.readFileOr (Scoreboard.tsvPath "parity")) m)
  if !refused.isEmpty then
    let anyFell := refused.any (·.fell.isSome)
    IO.eprintln (if anyFell then
      "parity: a fixture fell, to a stop its divergence declaration does not excuse either, \
so nothing is judged and nothing is written"
      else "parity: a divergence declaration does not account for where its fixture stops, \
so nothing is judged and nothing is written")
    for r in refused do
      let names := String.intercalate ", " (r.declared.map Divergence.name)
      if let some (o, n) := r.fell then
        let stopAt := match r.stopped with
          | some (g, why) => s!" — {g.tag} ({g.what}): {why}"
          | none => ""
        IO.eprintln s!"    {r.fixture}: fell from {o} to {n}{stopAt}"
      IO.eprintln <| match r.accounting, r.stopped with
        | .outlived, _ => s!"    {r.fixture}: declares {names} and reaches the top anyway"
        | _, some (g, _) =>
          s!"    {r.fixture}: stops at {g.tag} and declares {names}, which excuses no stop at {g.tag}"
        | _, none => s!"    {r.fixture}: declares {names}, and no level is measured for it to excuse"
    if anyFell then
      IO.eprintln "  A fall is the engine's to fix first: the declaration explains the stop the \
fixture had. If the new stop is the intended one, correct the '% diverges:' line, run \
.lake/build/bin/parity --repin, and request the fall with a '# lowered:' line"
    else
      IO.eprintln "  Correct or remove the '% diverges:' line, then: .lake/build/bin/parity --repin"
    IO.println (Scoreboard.tierLine "parity" 0 (refused.filter (·.fell.isSome)).size 0 "fault")
    return 2
  IO.println s!"parity: {m.reached.size} fixture(s), \
{(m.reached.filter (·.level == refuses)).size} outside the denominator, \
top level {Level.all.length}"
  let rows := m.reached.map fun r => ({ item := r.fixture, value := r.level } : Scoreboard.Row)
  -- The selftest argument is unreachable: `main` answers `--selftest` before
  -- measuring. It fails closed if that ever stops being true.
  Scoreboard.tierMain "parity" .raw (pure (provenance, rows)) (pure 1) args

/-- Re-pin every sidecar whose engine source moved in comments only. -/
def repinAll : IO UInt32 := do
  let mut repinned : Nat := 0
  let mut refused : Array String := #[]
  for stem in ← parityNames do
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    unless ← sidecarPath.pathExists do continue
    let side ← match Sidecar.parse (← IO.FS.readFile sidecarPath) with
      | .ok s => pure s
      | .error e => do
          IO.eprintln s!"parity --repin {stem}: the sidecar is unreadable: {e}"
          return 1
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrc ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
    let refPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let refBytes ← if ← refPath.pathExists then IO.FS.readBinFile refPath else pure .empty
    let mut moved : Array String := #[]
    for (p, k) in inputPins side.inputs do
      let path := System.FilePath.mk parityDir / p
      if ← path.pathExists then
        if Flate.contentKey (← IO.FS.readBinFile path) != k then moved := moved.push p
      else moved := moved.push p
    match repinDecision side src refSrc (Flate.contentKey refBytes) refBytes.size moved.toList with
    | .unnecessary => pure ()
    | .refused why =>
      refused := refused.push s!"{stem}: {why}"
    | .repinned s =>
      IO.FS.writeFile sidecarPath s.render
      repinned := repinned + 1
      IO.println s!"parity --repin {stem}: the engine's source is pinned again \
(comments only; the reference is untouched)"
  IO.println s!"parity --repin: {repinned} re-pinned"
  unless refused.isEmpty do
    IO.eprintln "parity --repin: refused, and those sidecars are untouched"
    for r in refused do IO.eprintln s!"    {r}"
    IO.eprintln "  Regenerate with: lake env lean --run scripts/parity-regen.lean --force <fixture>"
    return 1
  return 0

/-- `gate` over a scratch baseline, in a scratch directory: its exit code,
the baseline it left, and its porcelain line. The tier's paths are
relative, so the directory is the whole of the isolation and the committed
baseline is never touched. -/
def gateLine (board : String) (m : Measured) (args : List String) :
    IO (UInt32 × String × String) := do
  let home ← IO.currentDir
  let root ← IO.FS.createTempDir
  let path := root / "testdata" / "scoreboard" / "parity.tsv"
  try
    IO.FS.createDirAll (root / "testdata" / "scoreboard")
    IO.FS.writeFile path board
    IO.Process.setCurrentDir root
    let (out, code) ← IO.FS.withIsolatedStreams (gate m args)
    IO.Process.setCurrentDir home
    let line := ((out.splitOn "\n").find? (·.startsWith "scoreboard: tier=")).getD ""
    return (code, ← IO.FS.readFile path, line)
  finally
    IO.Process.setCurrentDir home
    IO.FS.removeDirAll root

/-- `gateLine` with its porcelain line read down to `result=`. -/
def gateIn (board : String) (m : Measured) (args : List String) :
    IO (UInt32 × String × String) := do
  let (code, after, line) ← gateLine board m args
  return (code, after, (Scoreboard.field line "result").getD "")

/-- `measureWith` over a staged copy of one committed pairing, after `brk`
has edited the copy: how the selftest reaches each fault arm through the
loop `main` runs. The copy is the pairing's four files and the shipped
faces, in a scratch directory, so the committed tree is never touched. -/
def measureStaged (env : Env) (stem : String) (brk : System.FilePath → IO Unit) :
    IO Measured := do
  let home ← IO.currentDir
  let root ← IO.FS.createTempDir
  try
    let pdir := root / parityDir
    IO.FS.createDirAll pdir
    for ext in [".tex", ".ref.tex", ".ref.pdf", ".ref.txt"] do
      let name := stem ++ ext
      IO.FS.writeBinFile (pdir / name) (← IO.FS.readBinFile (System.FilePath.mk parityDir / name))
    let fdir := root / testFonts
    IO.FS.createDirAll fdir
    for e in ← System.FilePath.readDir testFonts do
      IO.FS.writeBinFile (fdir / e.fileName) (← IO.FS.readBinFile e.path)
    brk pdir
    IO.Process.setCurrentDir root
    let m ← measureWith env
    IO.Process.setCurrentDir home
    return m
  finally
    IO.Process.setCurrentDir home
    IO.FS.removeDirAll root

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  unless inked "a b\tc\nd" == ['a', 'b', 'c', 'd'] do bad := bad.push "inked drops whitespace"
  unless levelName refuses == "refuses" do bad := bad.push "levelName refuses"
  unless levelName 5 == "5 (top)" do bad := bad.push s!"levelName top: {levelName 5}"
  unless levelName 0 == "0 (next: P0)" do bad := bad.push s!"levelName 0: {levelName 0}"
  unless (Level.all.map Level.tag) == ["P0", "P1", "P2", "P3", "P4"] do bad := bad.push "level tags"
  unless Level.all.length == 5 do bad := bad.push "level count"
  -- The registry: every divergence names a reason, and only the permanently
  -- out-of-scope one is allowed to excuse nothing while also being unread.
  for d in Divergence.all do
    if (d.why).isEmpty then bad := bad.push s!"divergence {d.name} has no reason"
    if d.outOfScope && !(d.excuses).isEmpty then
      bad := bad.push s!"divergence {d.name} is out of scope yet excuses a level"
    unless Divergence.ofName? d.name == some d do
      bad := bad.push s!"divergence {d.name} does not round trip through its name"
  unless (Divergence.all.filter (·.outOfScope)).length == 1 do
    bad := bad.push "exactly one divergence is permanently out of scope"
  -- A fixture's declaration: read, unknown names refused, both directions.
  match declaredDivergences "% parity: x\n% diverges: default-measure\n\\documentclass{article}" with
  | .ok [.defaultMeasure] => pure ()
  | r => bad := bad.push s!"declaredDivergences: {repr r}"
  match declaredDivergences "% diverges: no-such-thing\n" with
  | .error _ => pure ()
  | .ok _ => bad := bad.push "an unregistered divergence name was accepted"
  unless (declaredDivergences "\\documentclass{article}").toOption == some [] do
    bad := bad.push "a fixture declaring nothing did not read as nothing"
  -- The accounting, every arm.
  let mk (lvl : Int) (st : Option (Level × String)) (ds : List Divergence) : Reached :=
    { fixture := "x", level := lvl, stopped := st, declared := ds, notes := #[] }
  unless accountingOf (mk 5 none []) == .clean do bad := bad.push "accounting clean"
  unless accountingOf (mk 5 none [.defaultMeasure]) == .outlived do bad := bad.push "accounting outlived"
  unless accountingOf (mk 2 (some (.census, "")) [.defaultMeasure]) == .explained .defaultMeasure do
    bad := bad.push "accounting explained"
  unless accountingOf (mk 2 (some (.census, "")) [.pointUnit]) == .unexplained do
    bad := bad.push "accounting unexplained"
  unless accountingOf (mk refuses none [.defaultMeasure]) == .unexplained do
    bad := bad.push "a declaration on a fixture outside the denominator was not unexplained"
  unless accountingOf (mk refuses none []) == .clean do
    bad := bad.push "a fixture outside the denominator declaring nothing was not clean"
  -- A fixture that declares nothing is clean wherever it stops: the ladder
  -- records what it measures and does not ask for prose. What fails is a
  -- declaration that explains nothing, which is the arm above.
  unless accountingOf (mk 2 (some (.census, "")) []) == .clean do
    bad := bad.push "a fixture declaring nothing was called unexplained"
  -- The line reading, which is the new level's whole content.
  let line (y : Dim.Sp) (t : String) : ArtRun :=
    { marks := #[], x := 0, y := y, w := 0, size := Dim.pt 10, ascent := 0
      inkAscent := 0, descent := 0, widest := 0, text := t }
  let page (rs : Array ArtRun) : ArtPage :=
    { media := (0, 0, 0, 0), runs := rs, boxes := #[], content := .empty }
  unless linesOf (page #[line 100 "ab", line 100 " c", line 80 "d"]) == #["abc", "d"] do
    bad := bad.push s!"linesOf: {repr (linesOf (page #[line 100 "ab", line 100 " c", line 80 "d"]))}"
  unless linesOf (page #[line 100 "  "]) == #[] do bad := bad.push "linesOf keeps a blank line"
  -- Lines are read top to bottom and left to right, not in the order the
  -- writer happened to paint them: a float or a footnote painted at its
  -- source position and placed elsewhere would otherwise read as reading
  -- order. The premise a docstring used to carry, now the measurement.
  unless linesOf (page #[line 80 "cd", line 100 "ab"]) == #["ab", "cd"] do
    bad := bad.push s!"linesOf is in paint order: {repr (linesOf (page #[line 80 "cd", line 100 "ab"]))}"
  let pd : ArtPage := page #[line 100 "ab", line 80 "cd"]
  let du : ArtPage := page #[line 80 "cd", line 100 "ab"]
  unless lineKey pd == lineKey du && orderKey pd == orderKey du do
    bad := bad.push "two paintings of one page read differently"
  let wide : ArtRun :=
    { marks := #[], x := Dim.pt 100, y := 100, w := 0, size := Dim.pt 10, ascent := 0
      inkAscent := 0, descent := 0, widest := 0, text := "z" }
  unless linesOf (page #[wide, line 100 "ab"]) == #["abz"] do
    bad := bad.push s!"a line is not read left to right: {repr (linesOf (page #[wide, line 100 "ab"]))}"
  -- Order is blind to the line partition; the line level is not. That is the
  -- measured reason the level exists, so it is asserted here rather than told.
  let split := page #[line 100 "ab", line 80 "cd"]
  let joined := page #[line 100 "abcd"]
  unless orderKey split == orderKey joined do bad := bad.push "orderKey is not blind to lines"
  unless lineKey split != lineKey joined do bad := bad.push "lineKey is blind to lines"
  -- And the level below: census is blind to order, order is not. The pair
  -- the obligation row owes for every comparison level with a declared
  -- blind spot — one equal under the level, unequal under the one above it.
  let ab := page #[line 100 "ab"]
  let ba := page #[line 100 "b", { line 100 "a" with x := Dim.pt 50 }]
  unless censusKey ab == censusKey ba do bad := bad.push "censusKey is not blind to order"
  unless orderKey ab != orderKey ba do bad := bad.push "orderKey is blind to order"
  -- --repin, every arm. A comment moved is re-pinned; anything the reference
  -- depends on moved, and it is not.
  let pinSrc := "% parity: a claim\n\\documentclass{article}\n"
  let pinRef := "\\documentclass{article}\n"
  let pinned : Sidecar :=
    { fixture := "x", compiles := true, pdfKey := "K", pdfSize := 7
      srcKey := srcKeyOf pinSrc, srcBodyKey := srcBodyKeyOf pinSrc
      refSrcKey := srcKeyOf pinRef, engine := "eng", format := "fmt", argv := "a"
      inputs := "", pages := 1, overfull := 0, provenance := "a claim" }
  unless repinDecision pinned pinSrc pinRef "K" 7 [] matches .unnecessary do
    bad := bad.push "--repin moved a pin nothing asked it to move"
  let edited := "% parity: a claim\n% diverges: default-measure\n\\documentclass{article}\n"
  match repinDecision pinned edited pinRef "K" 7 [] with
  | .repinned s =>
    unless s.srcKey == srcKeyOf edited && s.srcBodyKey == pinned.srcBodyKey
        && s.pdfKey == pinned.pdfKey do
      bad := bad.push s!"--repin wrote more than the source pin: {repr s}"
  | r => bad := bad.push s!"--repin refused a comment-only edit: {repr (r matches .unnecessary)}"
  match repinDecision pinned "\\documentclass{book}\n" pinRef "K" 7 [] with
  | .refused _ => pure ()
  | _ => bad := bad.push "--repin accepted an edit to the document itself"
  match repinDecision pinned edited "\\documentclass{book}\n" "K" 7 [] with
  | .refused _ => pure ()
  | _ => bad := bad.push "--repin accepted an edited reference source"
  match repinDecision pinned edited pinRef "OTHER" 7 [] with
  | .refused _ => pure ()
  | _ => bad := bad.push "--repin accepted a reference the sidecar does not record"
  match repinDecision pinned edited pinRef "K" 7 ["../corpus/fonts/x.ttf"] with
  | .refused _ => pure ()
  | _ => bad := bad.push "--repin accepted a moved input"
  unless bodyOf "% a comment\n\\documentclass{article}\n% another\n"
      == "\\documentclass{article}\n" do
    bad := bad.push s!"bodyOf: {repr (bodyOf "% a\nx\n")}"
  -- Inside a verbatim body a `%` line is text the engine sets: an edit there
  -- is an edit to the document, and a repin must not clear it.
  let verb := "\\documentclass{article}\n\\begin{document}\n\\begin{verbatim}\n% set as text\n\
\\end{verbatim}\n\\end{document}\n"
  let verbEdited := "\\documentclass{article}\n\\begin{document}\n\\begin{verbatim}\n% set as other text\n\
\\end{verbatim}\n\\end{document}\n"
  unless lexesVerbatim verb && !lexesVerbatim pinSrc do
    bad := bad.push "lexesVerbatim does not read the lexer's verbatim capture"
  unless srcBodyKeyOf verb != srcBodyKeyOf verbEdited do
    bad := bad.push "the body key is blind to an edit inside a verbatim body"
  let verbPinned : Sidecar := { pinned with srcKey := srcKeyOf verb, srcBodyKey := srcBodyKeyOf verb }
  match repinDecision verbPinned verbEdited pinRef "K" 7 [] with
  | .refused _ => pure ()
  | _ => bad := bad.push "--repin cleared an edit inside a verbatim body"
  unless firstGap "abc" "abd" == "offset 2: engine some 'c', reference some 'd'" do
    bad := bad.push s!"firstGap: {firstGap "abc" "abd"}"
  unless firstGap "ab" "ab" == "no difference" do bad := bad.push "firstGap equal"
  unless (firstGap "ab" "abc").startsWith "the readings agree for 2" do
    bad := bad.push s!"firstGap prefix: {firstGap "ab" "abc"}"
  -- The gate, through the path that ships: `gate` is what `main` runs after
  -- measuring, and each case hands it a measurement and a baseline.
  let reach (f : String) (lvl : Int) : Reached :=
    { fixture := f, level := lvl, stopped := none, declared := [], notes := #[] }
  let measured (rs : List Reached) : Measured := { reached := rs.toArray, faults := #[] }
  let board (lines : List String) : String := String.join (lines.map (· ++ "\n"))
  let at5 := board ["# encoding: raw", "prose\t5"]
  -- 1. an unchanged measurement passes.
  let (c, _, _) ← gateIn at5 (measured [reach "prose" 5]) ["--check"]
  unless c == 0 do bad := bad.push s!"gate: an unchanged measurement exited {c}"
  -- 2. a fall with no lowering line fails the check and is not written.
  let (c, _, _) ← gateIn at5 (measured [reach "prose" 4]) ["--check"]
  unless c == 1 do bad := bad.push s!"gate: a fall with no lowering exited {c} under --check"
  let (c, after, _) ← gateIn at5 (measured [reach "prose" 4]) []
  unless c != 0 && after == at5 do
    bad := bad.push s!"gate: a fall with no lowering was written (exit {c}): {repr after}"
  -- 3. a fall under a new lowering line naming exactly that fall is written.
  let lowered := board ["# encoding: raw",
    "# lowered: prose 5→4 — a line-break change somebody reviewed", "prose\t5"]
  let (c, after, _) ← gateIn lowered (measured [reach "prose" 4]) []
  unless c == 0 && (after.splitOn "\nprose\t4\n").length == 2 do
    bad := bad.push s!"gate: a fall under an exact lowering was not written (exit {c}): {repr after}"
  -- ... and a lowering naming other numbers authorises nothing.
  let other := board ["# encoding: raw", "# lowered: prose 5→2 — a different fall", "prose\t5"]
  let (c, after, _) ← gateIn other (measured [reach "prose" 4]) []
  unless c != 0 && after == other do
    bad := bad.push s!"gate: a lowering for other numbers authorised a fall (exit {c})"
  -- 4. an unrecorded rise fails the check as stale.
  let at4 := board ["# encoding: raw", "prose\t4"]
  let (c, _, result) ← gateIn at4 (measured [reach "prose" 5]) ["--check"]
  unless c == 1 && result == "stale" do
    bad := bad.push s!"gate: an unrecorded rise exited {c} with result={result}, not stale"
  -- 5. a measurement that is not of the committed pairings is a fault in
  -- every mode, and writes nothing.
  let staleM : Measured :=
    { reached := #[reach "prose" 5], faults := #[("prose", .engineSourceMoved)] }
  let (c, _, result) ← gateIn at5 staleM ["--check"]
  unless c == 2 && result == "fault" do
    bad := bad.push s!"gate: a stale pairing exited {c} with result={result} under --check"
  let (c, after, _) ← gateIn at4 staleM []
  unless c == 2 && after == at4 do
    bad := bad.push s!"gate: a stale pairing was recorded (exit {c}): {repr after}"
  -- 6. a declaration that excuses nothing about the stop fails, in every
  -- mode — the re-review's case: `pagebreak` stops at P4 and declares
  -- `point-unit`, which excuses no level.
  let unexplained : Reached :=
    { fixture := "prose", level := 4, stopped := some (.lines, "p2 line 1")
      declared := [.pointUnit], notes := #[] }
  let (c, _, _) ← gateIn at4 (measured [unexplained]) ["--check"]
  unless c == 2 do bad := bad.push s!"gate: an unexplained declaration exited {c} under --check"
  let (c, after, _) ← gateIn at4 (measured [unexplained]) []
  unless c == 2 && after == at4 do
    bad := bad.push s!"gate: an unexplained declaration was recorded (exit {c})"
  -- 7. a declaration on a fixture that reaches the top fails too.
  let outlived : Reached := { reach "prose" 5 with declared := [.defaultMeasure] }
  let (c, _, _) ← gateIn at5 (measured [outlived]) ["--check"]
  unless c == 2 do bad := bad.push s!"gate: a declaration that outlived its stop exited {c}"
  -- 8. an explained stop passes: the declaration names the level it stops on.
  let explained : Reached :=
    { fixture := "prose", level := 2, stopped := some (.census, "p1")
      declared := [.defaultMeasure], notes := #[] }
  let (c, _, _) ← gateIn (board ["# encoding: raw", "prose\t2"]) (measured [explained]) ["--check"]
  unless c == 0 do bad := bad.push s!"gate: an explained stop exited {c}"
  -- 9. a spent lowering authorises nothing again: the fall it named is
  -- written, a recorded rise takes the item back up, and the same fall is
  -- then refused with the baseline untouched. The rule is the Board's
  -- (`Scoreboard.authorises_exact`: a line authorises a change exactly when
  -- it is a request and the change is the fall it names); this is the
  -- tier's own path to it.
  let (c1, after1, _) ← gateIn lowered (measured [reach "prose" 4]) []
  let (c2, after2, _) ← gateIn after1 (measured [reach "prose" 5]) []
  unless c1 == 0 && c2 == 0 && (after2.splitOn "\nprose\t5\n").length == 2 do
    bad := bad.push s!"gate: a lowering and the recorded rise back did not both write \
(exits {c1}, {c2}): {repr after2}"
  let (c3, after3, _) ← gateIn after2 (measured [reach "prose" 4]) []
  unless c3 == 1 && after3 == after2 do
    bad := bad.push s!"gate: the same fall after a recorded rise was written on the strength \
of a spent lowering (exit {c3})"
  -- 10. The fault arms of the loop `measureAll` runs, each reached by one
  -- staged break of a copy of the committed `prose` pairing and judged by the
  -- arm it names. The untouched copy names none, so each arm below is its
  -- break's alone.
  let editText (d : System.FilePath) (n : String) (f : String → String) : IO Unit := do
    IO.FS.writeFile (d / n) (f (← IO.FS.readFile (d / n)))
  let pinAlso (extra : String) (d : System.FilePath) : IO Unit :=
    editText d "prose.ref.txt" fun s => s.replace "\ninputs: " s!"\ninputs: {extra} "
  let garbage := "not a pdf\n".toUTF8
  let unreadable (d : System.FilePath) : IO Unit := do
    IO.FS.writeBinFile (d / "prose.ref.pdf") garbage
    let side ← IO.ofExcept (Sidecar.parse (← IO.FS.readFile (d / "prose.ref.txt")))
    let side := { side with pdfKey := Flate.contentKey garbage, pdfSize := garbage.size }
    IO.FS.writeFile (d / "prose.ref.txt") side.render
  let cases : List (String × (System.FilePath → IO Unit) × List String) := [
    ("an untouched copy", fun _ => pure (), []),
    ("an edit to the engine's source body",
      fun d => editText d "prose.tex" fun s =>
        s.replace "\\end{document}" "One more sentence.\n\\end{document}",
      ["engine-source-moved"]),
    ("an edit to the reference source",
      fun d => editText d "prose.ref.tex" fun s => "% an edit\n" ++ s,
      ["reference-source-moved", "input-moved ./prose.ref.tex"]),
    ("a pinned input that changed",
      fun d => do
        IO.FS.writeFile (d / "extra.sty") "x"
        pinAlso "./extra.sty=0" d,
      ["input-moved ./extra.sty"]),
    ("a pinned input that is gone", pinAlso "./gone.sty=0", ["input-gone ./gone.sty"]),
    ("a reference that is not the recorded one",
      fun d => do
        IO.FS.writeBinFile (d / "prose.ref.pdf") ((← IO.FS.readBinFile (d / "prose.ref.pdf")).push 10),
      ["reference-not-recorded"]),
    ("a recorded reference the reader cannot read", unreadable, ["reference-unreadable"]),
    ("an unreadable sidecar",
      fun d => IO.FS.writeFile (d / "prose.ref.txt") "fixture: prose\n",
      ["sidecar-unreadable"]),
    ("no sidecar", fun d => IO.FS.removeFile (d / "prose.ref.txt"), ["no-sidecar"]),
    ("an unregistered divergence",
      fun d => editText d "prose.tex" fun s => "% diverges: no-such-thing\n" ++ s,
      ["declaration"])]
  let env ← envOf
  for (what, brk, want) in cases do
    let m ← measureStaged env "prose" brk
    let got := m.faults.toList.map fun (s, f) => (s, f.arm)
    unless got == want.map ("prose", ·) do
      bad := bad.push s!"staged: {what} named {repr got}, not {repr want}"
    -- A faulted pairing is never a level result; the untouched one is one.
    let expect := if want.isEmpty then 1 else 0
    unless m.reached.size == expect do
      bad := bad.push s!"staged: {what} measured {m.reached.size} fixture(s), not {expect}"
  -- 11. a fixture that fell to a stop its declaration does not excuse is
  -- refused as a fall first: the one ratchet reads the fall against the
  -- committed floor, and the refusal lists it before a declaration that is
  -- only wrong. `b` falls from 2 to P0 behind `default-measure`, which
  -- excuses P1 to P4, and `a` declares a divergence while reaching the top.
  let top : Int := Level.all.length
  let a : Reached := { reach "a" top with declared := [.defaultMeasure] }
  let b : Reached := { fixture := "b", level := 0, stopped := some (.build, "an engine error")
                       declared := [.defaultMeasure], notes := #[] }
  let ab := measured [a, b]
  let fellBoard := board ["# encoding: raw", s!"a\t{top}", "b\t2"]
  let order := (refusals ab (fallsSince fellBoard ab)).toList.map fun r => (r.fixture, r.fell)
  unless order == [("b", some (2, 0)), ("a", none)] do
    bad := bad.push s!"refusals: a fall behind a declaration is not named first: {repr order}"
  let steadyBoard := board ["# encoding: raw", s!"a\t{top}", "b\t0"]
  let order := (refusals ab (fallsSince steadyBoard ab)).toList.map fun r => (r.fixture, r.fell)
  unless order == [("a", none), ("b", none)] do
    bad := bad.push s!"refusals: a stop that did not move read as a fall: {repr order}"
  for args in [["--check"], []] do
    let (c, after, line) ← gateLine fellBoard ab args
    unless c == 2 && Scoreboard.field line "result" == some "fault" && after == fellBoard
        && Scoreboard.field line "regressed" == some "1" do
      bad := bad.push s!"gate: a fall behind a declaration exited {c} as {line} under {repr args}"
  let (c, _, line) ← gateLine steadyBoard ab ["--check"]
  unless c == 2 && Scoreboard.field line "regressed" == some "0" do
    bad := bad.push s!"gate: a declaration whose fixture did not move exited {c} as {line}"
  if bad.isEmpty then
    IO.println "parity --selftest: all passed"
    return 0
  for b in bad do IO.eprintln s!"FAIL {b}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  if args.contains "--repin" then return ← repinAll
  gate (← measureAll) args
