/-
The parity ladder's gate. Run from the repository root:

  lake build ParityLib
  lake env lean --run scripts/parity.lean --selftest
  lake env lean --run scripts/parity.lean --check
  lake env lean --run scripts/parity.lean --record   # rewrite the scoreboard

`--check` is the spelling siblings call by convention and is what a bare
invocation does: the flag is accepted so a caller need not know that.

Nothing here invokes another engine, reads PATH, or touches the network: it
builds each fixture the way the driver builds it, reads the *committed*
reference beside it, and holds the rung each pair reaches against
`tests/scoreboard/parity.tsv`.

The gate is not part of `lake test` — not for hermeticity, which it has, but
because the suite's entry point is a file this slice does not own. Adding it
there is one line, and the routing note in PLAN says so.

What a failure means:

  fell    a rung that used to hold does not. A regression.
  rose    a rung now holds that the scoreboard does not record. Also a
          failure: an unrecorded rise means the next fall lands on a number
          nobody set, and the fix is to record it (--record).
  stale   a source has changed since its reference was built, so the two
          halves of the pairing are no longer the same document. Regenerate.
  stale declaration
          a fixture names a divergence and reaches the top anyway, so the
          declaration would excuse a future regression it no longer
          explains. Remove the line.

The oracle is never "must match". Every fixture's number is what the engine
reaches today; the ladder's whole claim is that it does not go down.
-/
import scripts.ParityCore

open LeanTex.Core LeanTex.Cli Parity

/-- What one fixture reached, and why it stopped there. -/
structure Reached where
  fixture : String
  level : Int
  /-- The rung that failed, and what it saw. Empty at the top. -/
  stopped : Option (Rung × String)
  /-- What the fixture declares about its own pairing. -/
  declared : List Divergence
  /-- Anything worth printing that is not a verdict: the reference's own
  overfull count, a divergence the pairing declares. -/
  notes : Array String
  deriving Inhabited

/-- Does the fixture's declaration account for where it stopped? A stop at a
rung some declared divergence excuses is explained; a stop at a rung none of
them excuses is not; and reaching the top while declaring anything at all is
a stale declaration. The third is the failure, for the reason a rise is one. -/
inductive Accounting where
  | explained (d : Divergence)
  | unexplained
  | stale
  | clean
  deriving Repr, BEq, Inhabited

def accountingOf (r : Reached) : Accounting :=
  match r.stopped with
  | none => if r.declared.isEmpty then .clean else .stale
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

/-- Judge one pairing, rung by rung, stopping at the first that does not
hold. Cumulative by construction: the loop cannot reach a rung whose
predecessor failed, so a rung never has to restate its predecessor's
premise. -/
def judge (stem : String) (side : Sidecar) (declared : List Divergence)
    (engineDiags : Array Diag)
    (engine : Except String (Array ArtPage))
    (reference : Except String (Array ArtPage)) : Reached := Id.run do
  let mut notes : Array String := #[]
  if 0 < side.overfull then
    notes := notes.push s!"the reference reports {side.overfull} overfull box(es)"
  unless side.compiles do
    return { fixture := stem, level := refuses, stopped := none, declared := declared
             notes := notes.push "the reference engine refuses this document, so it is outside the denominator" }
  let errs := engineDiags.filter fun d => d.severity == .error
  let stop (r : Rung) (why : String) : Reached :=
    { fixture := stem, level := (Rung.all.findIdx? (· == r)).getD 0, stopped := some (r, why)
      declared := declared, notes := notes }
  match engine, reference with
  | .error e, _ => return stop .build s!"the engine's own reader refuses its own bytes: {e}"
  | _, .error e => return stop .build s!"the committed reference is unreadable: {e}"
  | .ok ep, .ok rp =>
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
    return { fixture := stem, level := Rung.all.length, stopped := none
             declared := declared, notes := notes }

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  unless inked "a b\tc\nd" == ['a', 'b', 'c', 'd'] do bad := bad.push "inked drops whitespace"
  unless levelName refuses == "refuses" do bad := bad.push "levelName refuses"
  unless levelName 5 == "5 (top)" do bad := bad.push s!"levelName top: {levelName 5}"
  unless levelName 0 == "0 (next: T0)" do bad := bad.push s!"levelName 0: {levelName 0}"
  unless (Rung.all.map Rung.tag) == ["T0", "T1", "T2", "T3", "T4"] do bad := bad.push "rung tags"
  unless Rung.all.length == 5 do bad := bad.push "rung count"
  -- The registry: every divergence names a reason, and only the permanently
  -- out-of-scope one is allowed to excuse nothing while also being unread.
  for d in Divergence.all do
    if (d.why).isEmpty then bad := bad.push s!"divergence {d.name} has no reason"
    if d.outOfScope && !(d.excuses).isEmpty then
      bad := bad.push s!"divergence {d.name} is out of scope yet excuses a rung"
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
  -- The accounting, all four arms.
  let mk (lvl : Int) (st : Option (Rung × String)) (ds : List Divergence) : Reached :=
    { fixture := "x", level := lvl, stopped := st, declared := ds, notes := #[] }
  unless accountingOf (mk 5 none []) == .clean do bad := bad.push "accounting clean"
  unless accountingOf (mk 5 none [.defaultMeasure]) == .stale do bad := bad.push "accounting stale"
  unless accountingOf (mk 2 (some (.census, "")) [.defaultMeasure]) == .explained .defaultMeasure do
    bad := bad.push "accounting explained"
  unless accountingOf (mk 2 (some (.census, "")) [.pointUnit]) == .unexplained do
    bad := bad.push "accounting unexplained"
  -- The scoreboard's format and the ratchet's arithmetic, both directions.
  match parseBaseline "# a comment\nprose\t4\nmeasure\t3\n\nbroken\t-1\n" with
  | .error e => bad := bad.push s!"parseBaseline: {e}"
  | .ok rows =>
    unless rows.length == 3 do bad := bad.push s!"parseBaseline rows: {rows.length}"
    unless (rows.find? (·.fixture == "broken")).map (·.level) == some (-1) do
      bad := bad.push "parseBaseline negative"
  match parseBaseline "prose four\n" with
  | .error _ => pure ()
  | .ok _ => bad := bad.push "a space-separated scoreboard row parsed"
  match parseBaseline "prose\tfour\n" with
  | .error _ => pure ()
  | .ok _ => bad := bad.push "a non-numeric scoreboard level parsed"
  match parseBaseline "prose\t1\nprose\t2\n" with
  | .error _ => pure ()
  | .ok _ => bad := bad.push "a scoreboard listing one fixture twice parsed"
  let board := renderBaseline [{ fixture := "b", level := 1 }, { fixture := "a", level := 2 }] ["note"]
  unless board.startsWith "# note\n" do bad := bad.push s!"scoreboard provenance: {repr board}"
  unless (board.splitOn "\n")[1]! == "a\t2" do bad := bad.push s!"scoreboard is not sorted: {repr board}"
  match parseBaseline board with
  | .ok [x, y] => unless x.fixture == "a" && x.level == 2 && y.fixture == "b" do
      bad := bad.push "scoreboard round trip"
  | _ => bad := bad.push "scoreboard round trip shape"
  unless retiredOf "# retired: gone — it moved to the corpus\nprose\t4\n" == ["gone"] do
    bad := bad.push s!"retiredOf: {repr (retiredOf "# retired: gone — why\n")}"
  unless retiredOf "prose\t4\n" == [] do bad := bad.push "retiredOf finds a retirement nobody wrote"
  -- The line reading, which is the new rung's whole content.
  let line (y : Dim.Sp) (t : String) : ArtRun :=
    { marks := #[], x := 0, y := y, w := 0, size := Dim.pt 10, ascent := 0
      inkAscent := 0, descent := 0, widest := 0, text := t }
  let page (rs : Array ArtRun) : ArtPage :=
    { media := (0, 0, 0, 0), runs := rs, boxes := #[], content := .empty }
  unless linesOf (page #[line 100 "ab", line 100 " c", line 80 "d"]) == #["abc", "d"] do
    bad := bad.push s!"linesOf: {repr (linesOf (page #[line 100 "ab", line 100 " c", line 80 "d"]))}"
  unless linesOf (page #[line 100 "  "]) == #[] do bad := bad.push "linesOf keeps a blank line"
  -- Order is blind to the line partition; the line rung is not. That is the
  -- measured reason the rung exists, so it is asserted here rather than told.
  let split := page #[line 100 "ab", line 80 "cd"]
  let joined := page #[line 100 "abcd"]
  unless orderKey split == orderKey joined do bad := bad.push "orderKey is not blind to lines"
  unless lineKey split != lineKey joined do bad := bad.push "lineKey is blind to lines"
  unless firstGap "abc" "abd" == "offset 2: engine some 'c', reference some 'd'" do
    bad := bad.push s!"firstGap: {firstGap "abc" "abd"}"
  unless firstGap "ab" "ab" == "no difference" do bad := bad.push "firstGap equal"
  unless (firstGap "ab" "abc").startsWith "the readings agree for 2" do
    bad := bad.push s!"firstGap prefix: {firstGap "ab" "abc"}"
  if bad.isEmpty then
    IO.println "parity --selftest: all passed"
    return 0
  for b in bad do IO.eprintln s!"FAIL {b}"
  return 1

def main (args : List String) : IO UInt32 := do
  if args.contains "--selftest" then return ← selftest
  let record := args.contains "--record"
  let pats := Hyphen.english.get
  let some fontData ← findFont | throw (IO.userError "parity: no corpus font")
  let .ok font := Font.parse fontData | throw (IO.userError "parity: corpus font unparsable")
  let oneFace := oneFaceOf font
  let mathSet ← mathSetOf oneFace
  let shipped ← FontDb.scanRoots [testFonts]
  let boardText ← if ← scoreboardPath.pathExists then IO.FS.readFile scoreboardPath else pure ""
  let recorded ← match parseBaseline boardText with
    | .ok rows => pure rows
    | .error e => throw (IO.userError s!"parity: the scoreboard is unreadable: {e}")
  let retired := retiredOf boardText
  let names ← parityNames
  let mut reached : Array Reached := #[]
  let mut stale : Array String := #[]
  for stem in names do
    let sidecarPath := System.FilePath.mk parityDir / (stem ++ ".ref.txt")
    unless ← sidecarPath.pathExists do
      IO.eprintln s!"parity {stem}: no reference sidecar — regenerate it (scripts/parity-regen.lean)"
      return 1
    let side ← match Sidecar.parse (← IO.FS.readFile sidecarPath) with
      | .ok s => pure s
      | .error e => do
          IO.eprintln s!"parity {stem}: the sidecar is unreadable: {e}"
          return 1
    -- The pairing's two halves, pinned. A source edited since the reference
    -- was built is a stale pairing, never a rung result.
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrc ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
    let declared ← match declaredDivergences src with
      | .ok ds => pure ds
      | .error e => do
          IO.eprintln s!"parity {stem}: {e}"
          return 1
    if srcKeyOf src != side.srcKey then
      stale := stale.push s!"{stem}: the engine's source has changed since its reference was built"
    if srcKeyOf refSrc != side.refSrcKey then
      stale := stale.push s!"{stem}: the reference source has changed since the reference was built"
    let refPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let refBytes ← if ← refPath.pathExists then IO.FS.readBinFile refPath else pure .empty
    if side.compiles then
      if refBytes.size != side.pdfSize || Flate.contentKey refBytes != side.pdfKey then
        stale := stale.push s!"{stem}: the committed reference is not the one the sidecar records"
    let (diags, ePages) ← engineSide oneFace mathSet shipped pats stem
    let rPages := if side.compiles then readArtifact refBytes else .ok #[]
    reached := reached.push (judge stem side declared diags ePages rPages)
  if record then
    IO.FS.createDirAll (scoreboardPath.parent.getD ".")
    IO.FS.writeFile scoreboardPath
      (renderBaseline (reached.toList.map fun r => { fixture := r.fixture, level := r.level })
        ["the parity ladder against lualatex: one integer per fixture, the number of",
         s!"rungs that hold, of {Rung.all.length} ({String.intercalate ", " (Rung.all.map Rung.tag)}). -1 means the",
         "reference engine refuses the document, which puts it outside the denominator.",
         "A level may rise and the rise must be recorded here; it may never fall.",
         "Retire a fixture with a '# retired: <fixture> — <why>' line, never by",
         "deleting its row.",
         "Written only by: lake env lean --run scripts/parity.lean --record"])
    IO.println s!"parity --record: wrote {reached.size} row(s) to {scoreboardPath}"
  for r in reached do
    let stopped := match r.stopped with
      | some (g, why) => s!" — {g.tag} ({g.what}): {why}"
      | none => ""
    IO.println s!"{r.fixture}: level {levelName r.level}{stopped}"
    unless r.declared.isEmpty do
      IO.println s!"    declares: {String.intercalate ", " (r.declared.map Divergence.name)}"
    match accountingOf r with
    | .explained d => IO.println s!"    the stop is declared: {d.name} — {d.why}"
    | .unexplained => IO.println "    the stop is not declared by any divergence this fixture names"
    | _ => pure ()
    for n in r.notes do IO.println s!"    note: {n}"
  unless stale.isEmpty do
    IO.eprintln "parity: the pairing is stale"
    for s in stale do IO.eprintln s!"    {s}"
    IO.eprintln "  Regenerate with: lake env lean --run scripts/parity-regen.lean --force <fixture>"
    return 1
  if record then return 0
  -- The ratchet.
  let mut fell : Array String := #[]
  let mut rose : Array String := #[]
  for r in reached do
    match recorded.find? (·.fixture == r.fixture) with
    | none => rose := rose.push s!"{r.fixture}: reaches level {r.level} and the scoreboard has no row for it"
    | some row =>
      if r.level < row.level then
        fell := fell.push s!"{r.fixture}: was level {row.level}, now {r.level}"
      else if row.level < r.level then
        rose := rose.push s!"{r.fixture}: was level {row.level}, now {r.level}"
  for row in recorded do
    unless names.contains row.fixture || retired.contains row.fixture do
      fell := fell.push s!"{row.fixture}: the scoreboard records level {row.level} and the fixture is gone \
(retire it with a '# retired:' line if that is intended)"
  -- A declaration that outlived what it explained.
  let mut staleDecl : Array String := #[]
  for r in reached do
    if accountingOf r == .stale then
      staleDecl := staleDecl.push s!"{r.fixture}: declares \
{String.intercalate ", " (r.declared.map Divergence.name)} and reaches the top anyway"
  IO.println s!"parity: {reached.size} fixture(s), \
{(reached.filter (·.level == refuses)).size} outside the denominator, \
top level {Rung.all.length}"
  unless fell.isEmpty do
    IO.eprintln "parity: a rung fell"
    for f in fell do IO.eprintln s!"    {f}"
    return 1
  unless rose.isEmpty do
    IO.eprintln "parity: a rung rose and the scoreboard does not record it"
    for f in rose do IO.eprintln s!"    {f}"
    IO.eprintln "  Record it with: lake env lean --run scripts/parity.lean --record"
    return 1
  unless staleDecl.isEmpty do
    IO.eprintln "parity: a divergence declaration is stale"
    for f in staleDecl do IO.eprintln s!"    {f}"
    IO.eprintln "  Remove the '% diverges:' line the engine no longer needs."
    return 1
  return 0
