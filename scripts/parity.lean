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
`tests/scoreboard/parity.tsv`.

Two things stop a run before the ratchet sees it, in every mode, and exit 2
with nothing written:

  fault       the measurement is not of the committed pairings: a source or
              an input moved since its reference was built (regenerate, or
              `--repin` when only comments moved), or a sidecar or a
              reference cannot be read.
  accounting  a fixture's `% diverges:` declaration does not account for
              where it stops — it excuses a level the fixture does not stop
              on, or the fixture reaches the top anyway. Either would sit in
              the file excusing the next regression. Correct the line, then
              `--repin`.

The oracle is never "must match". Every fixture's number is what the engine
reaches today; the ladder's whole claim is that it does not go down.
-/
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
  let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
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

/-- One run over the corpus: what each fixture reached, and every reason the
run is not a measurement of the committed pairings at all. A fault is
collected rather than returned at once, so one run names every one. -/
structure Measured where
  reached : Array Reached
  faults : Array String
  deriving Inhabited

def measureAll : IO Measured := do
  let pats := Hyphen.english.get
  let some fontData ← findFont | throw (IO.userError "parity: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "parity: corpus font unparsable")
  let oneFace := oneFaceOf font
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
  let mut reached : Array Reached := #[]
  let mut faults : Array String := #[]
  for stem in ← parityNames do
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    unless ← sidecarPath.pathExists do
      faults := faults.push s!"{stem}: no reference sidecar — regenerate it (scripts/parity-regen.lean)"
      continue
    let side ← match Sidecar.parse (← IO.FS.readFile sidecarPath) with
      | .ok s => pure s
      | .error e => do
          faults := faults.push s!"{stem}: the sidecar is unreadable: {e}"
          continue
    -- The pairing's two halves, pinned. A source edited since the reference
    -- was built is a stale pairing, never a level result.
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrc ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
    let declared ← match declaredDivergences src with
      | .ok ds => pure ds
      | .error e => do
          faults := faults.push s!"{stem}: {e}"
          continue
    if srcKeyOf src != side.srcKey then
      faults := faults.push s!"{stem}: the engine's source has changed since its reference was built \
(if only a comment or a declaration moved, --repin clears it without the reference engine)"
    if srcKeyOf refSrc != side.refSrcKey then
      faults := faults.push s!"{stem}: the reference source has changed since the reference was built"
    -- Every in-repo file the reference read, pinned. The shipped font is the
    -- one this catches: it is read by both engines, and an update to it
    -- would otherwise leave the engine on the new face and the committed
    -- reference on the old one, silently.
    for (p, k) in inputPins side.inputs do
      let path := System.FilePath.mk parityDir / p
      unless ← path.pathExists do
        faults := faults.push s!"{stem}: the reference read {p}, which is gone"
        continue
      if Flate.contentKey (← IO.FS.readBinFile path) != k then
        faults := faults.push s!"{stem}: {p} has changed since the reference read it"
    let refPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let refBytes ← if ← refPath.pathExists then IO.FS.readBinFile refPath else pure .empty
    if side.compiles then
      if refBytes.size != side.pdfSize || Flate.contentKey refBytes != side.pdfKey then
        faults := faults.push s!"{stem}: the committed reference is not the one the sidecar records"
    let (diags, ePages) ← engineSide oneFace mathSet shipped pats stem
    -- A reference the reader cannot read is a fault in the harness, not a
    -- level: every fixture would read as having fallen, and a regeneration
    -- would store it. One reader reads both sides, so a regression in it is
    -- exactly the thing a measurement must not be allowed to express.
    let rPages ← if side.compiles then
        match readArtifact refBytes with
        | .ok ps => pure ps
        | .error e => do
            faults := faults.push s!"{stem}: the committed reference is unreadable — {e}"
            continue
      else pure #[]
    reached := reached.push (judge stem side declared diags ePages rPages)
  return { reached, faults }

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

/-- A measurement held against the baseline. `main` is `measureAll` then
this, so the selftest drives exactly the path that ships with measurements
it wrote by hand. -/
def gate (m : Measured) (args : List String) : IO UInt32 := do
  for r in m.reached do report r
  if !m.faults.isEmpty then
    IO.eprintln "parity: the measurement is not of the committed pairings, so nothing is judged \
and nothing is written"
    for f in m.faults do IO.eprintln s!"    {f}"
    IO.eprintln "  Regenerate with: lake env lean --run scripts/parity-regen.lean --force <fixture>"
    IO.println (Scoreboard.tierLine "parity" 0 0 0 "fault")
    return 2
  let wrong := m.reached.filterMap fun r =>
    let names := String.intercalate ", " (r.declared.map Divergence.name)
    match accountingOf r, r.stopped with
    | .unexplained, some (g, _) =>
      some s!"{r.fixture}: stops at {g.tag} and declares {names}, which excuses no stop at {g.tag}"
    | .unexplained, none =>
      some s!"{r.fixture}: declares {names}, and no level is measured for it to excuse"
    | .outlived, _ => some s!"{r.fixture}: declares {names} and reaches the top anyway"
    | _, _ => none
  if !wrong.isEmpty then
    IO.eprintln "parity: a divergence declaration does not account for where its fixture stops, \
so nothing is judged and nothing is written"
    for w in wrong do IO.eprintln s!"    {w}"
    IO.eprintln "  Correct or remove the '% diverges:' line, then: .lake/build/bin/parity --repin"
    IO.println (Scoreboard.tierLine "parity" 0 0 0 "fault")
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
the baseline it left, and the `result=` of its porcelain line. The tier's
paths are relative, so the directory is the whole of the isolation and the
committed baseline is never touched. -/
def gateIn (board : String) (m : Measured) (args : List String) :
    IO (UInt32 × String × String) := do
  let home ← IO.currentDir
  let root ← IO.FS.createTempDir
  let path := root / "tests" / "scoreboard" / "parity.tsv"
  try
    IO.FS.createDirAll (root / "tests" / "scoreboard")
    IO.FS.writeFile path board
    IO.Process.setCurrentDir root
    let (out, code) ← IO.FS.withIsolatedStreams (gate m args)
    IO.Process.setCurrentDir home
    let line := ((out.splitOn "\n").find? (·.startsWith "scoreboard: tier=")).getD ""
    return (code, ← IO.FS.readFile path, (Scoreboard.field line "result").getD "")
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
  -- measuring, and each case hands it a measurement and a baseline. The
  -- ratchet cases are the ones that hold whatever `Scoreboard.ratchet`
  -- decides about a lowering line that has already been applied once.
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
    { reached := #[reach "prose" 5], faults := #["prose: the engine's source has changed"] }
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
  -- Owed to `Scoreboard.ratchet`, reported and never gated here: once a
  -- lowering has been applied, a recorded rise back followed by the same
  -- fall must not be written on the strength of the line left behind. Which
  -- way it goes is the Board's decision, not this tier's, so the selftest
  -- only says what it saw.
  let (c1, after1, _) ← gateIn lowered (measured [reach "prose" 4]) []
  let (c2, after2, _) ← gateIn after1 (measured [reach "prose" 5]) []
  let (c3, _, _) ← gateIn after2 (measured [reach "prose" 4]) []
  if c1 == 0 && c2 == 0 then
    let seen := if c3 == 0 then "re-accepted by the lowering line left behind" else "refused"
    IO.println s!"parity --selftest: owed to Scoreboard.ratchet, not gated here — the same \
fall after a recorded rise is {seen} (exit {c3})"
  if bad.isEmpty then
    IO.println "parity --selftest: all passed"
    return 0
  for b in bad do IO.eprintln s!"FAIL {b}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  if args.contains "--repin" then return ← repinAll
  gate (← measureAll) args
