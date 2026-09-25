/-
The parity ladder's gate. Run from the repository root:

  lake build parity
  .lake/build/bin/parity --selftest
  .lake/build/bin/parity --check      # the default
  .lake/build/bin/parity --repin      # re-pin a comment-only edit
  .lake/build/bin/parity --record     # rewrite the scoreboard

Compiled rather than interpreted, for two reasons: it imports test-suite
internals other branches edit, so a build is what fails when one of them
moves; and interpreting it cost 7.4 s against 0.1 s for the binary, on a
gate that will grow.

`--check` is the spelling siblings call by convention and is what a bare
invocation does: the flag is accepted so a caller need not know that.

Nothing here invokes another engine, reads PATH, or touches the network: it
builds each fixture the way the driver builds it, reads the *committed*
reference beside it, and holds the level each pair reaches against
`tests/scoreboard/parity.tsv`.

The gate is not part of `lake test` — not for hermeticity, which it has, but
because the suite's entry point is a file this slice does not own. Adding it
there is one line, and the routing note in PLAN says so.

What a failure means:

  fell    a level that used to hold does not. A regression.
  rose    a level now holds that the scoreboard does not record. Also a
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
anything at all is a stale declaration, also a failure.

A fixture that declares nothing is `clean` whatever it reaches: the ladder
records the level it measures and does not ask for prose. What fails is a
declaration that is *wrong* — one that names a divergence which does not
account for the stop, and would therefore sit in the file excusing whatever
regression came next. -/
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
    | none => if r.declared.isEmpty then .clean else .unexplained

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

def selftest : IO UInt32 := do
  let mut bad : Array String := #[]
  unless inked "a b\tc\nd" == ['a', 'b', 'c', 'd'] do bad := bad.push "inked drops whitespace"
  unless levelName refuses == "refuses" do bad := bad.push "levelName refuses"
  unless levelName 5 == "5 (top)" do bad := bad.push s!"levelName top: {levelName 5}"
  unless levelName 0 == "0 (next: L0)" do bad := bad.push s!"levelName 0: {levelName 0}"
  unless (Level.all.map Level.tag) == ["L0", "L1", "L2", "L3", "L4"] do bad := bad.push "level tags"
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
  -- The accounting, all four arms.
  let mk (lvl : Int) (st : Option (Level × String)) (ds : List Divergence) : Reached :=
    { fixture := "x", level := lvl, stopped := st, declared := ds, notes := #[] }
  unless accountingOf (mk 5 none []) == .clean do bad := bad.push "accounting clean"
  unless accountingOf (mk 5 none [.defaultMeasure]) == .stale do bad := bad.push "accounting stale"
  unless accountingOf (mk 2 (some (.census, "")) [.defaultMeasure]) == .explained .defaultMeasure do
    bad := bad.push "accounting explained"
  unless accountingOf (mk 2 (some (.census, "")) [.pointUnit]) == .unexplained do
    bad := bad.push "accounting unexplained"
  -- A fixture that declares nothing is clean wherever it stops: the ladder
  -- records what it measures and does not ask for prose. What fails is a
  -- declaration that explains nothing, which is the arm above.
  unless accountingOf (mk 2 (some (.census, "")) []) == .clean do
    bad := bad.push "a fixture declaring nothing was called unexplained"
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
  -- The lowering line, the ratchet's one exception: read, both numbers
  -- pinned, and a line with no reason is not a lowering.
  unless loweredOf "# lowered: prose 5→4 — a font update moved a line\n"
      == [{ item := "prose", old := 5, new := 4 }] do
    bad := bad.push s!"loweredOf: {repr (loweredOf "# lowered: prose 5→4 — why\n")}"
  unless loweredOf "# lowered: prose 5→4\n" == [] do
    bad := bad.push "a lowering with no reason was accepted"
  unless loweredOf "# lowered: prose five→4 — why\n" == [] do
    bad := bad.push "a lowering with an unreadable number was accepted"
  unless carriedOf "# a header\n# retired: gone — why\n# lowered: prose 5→4 — why\nprose\t4\n"
      == ["retired: gone — why", "lowered: prose 5→4 — why"] do
    bad := bad.push s!"carriedOf: {repr (carriedOf "# retired: gone — why\n")}"
  -- --record, every arm broken once. The board is the argument and the
  -- decision is the value, so each case is a fact about the writer rather
  -- than about a file it left behind.
  let board5 := "# header\nprose\t5\n"
  let prov := ["header"]
  let wrote (w : Write) : Option String := match w with | .ok t => some t | .refused _ => none
  let refusedFor (w : Write) : List String :=
    match w with | .refused rs => rs | .ok _ => []
  -- 1. a fall no line accepts writes nothing.
  match recordDecision board5 [{ fixture := "prose", level := 4 }] [] prov with
  | .ok t => bad := bad.push s!"--record wrote a fall nobody accepted: {repr t}"
  | .refused rs =>
    unless rs.length == 1 && (rs[0]!).startsWith "prose: was level 5, now 4" do
      bad := bad.push s!"--record fall reason: {repr rs}"
  -- 2. the same fall with a matching lowering line writes, and carries the
  -- line forward so the decision stays in the file.
  let lowBoard := board5 ++ "# lowered: prose 5→4 — a font update moved one line\n"
  match wrote (recordDecision lowBoard [{ fixture := "prose", level := 4 }] [] prov) with
  | none => bad := bad.push "--record refused a fall a lowering line accepts"
  | some t =>
    unless (t.splitOn "prose\t4").length == 2 do
      bad := bad.push s!"--record did not write the lowered level: {repr t}"
    unless (t.splitOn "# lowered: prose 5→4 — a font update moved one line").length == 2 do
      bad := bad.push s!"--record dropped the lowering line: {repr t}"
  -- 3. a lowering whose numbers do not match this fall accepts nothing: it
  -- is one decision about one pair of numbers, not a standing permission.
  match recordDecision (board5 ++ "# lowered: prose 5→2 — why\n")
      [{ fixture := "prose", level := 4 }] [] prov with
  | .ok _ => bad := bad.push "a lowering for a different pair of numbers accepted a fall"
  | .refused _ => pure ()
  -- 4. a vanished fixture needs a retirement line; with one, the write goes
  -- through and the line survives.
  match recordDecision board5 [] [] prov with
  | .ok t => bad := bad.push s!"--record dropped a vanished fixture's row: {repr t}"
  | .refused rs =>
    unless (rs[0]!).startsWith "prose: the scoreboard records level 5" do
      bad := bad.push s!"--record vanished reason: {repr rs}"
  match wrote (recordDecision (board5 ++ "# retired: prose — it moved to the probes set") [] [] prov) with
  | none => bad := bad.push "--record refused a retired fixture's absence"
  | some t =>
    unless (t.splitOn "# retired: prose — it moved to the probes set").length == 2 do
      bad := bad.push s!"--record dropped the retirement line: {repr t}"
  -- 5. a stale pairing writes nothing, whatever the levels say. The
  -- staleness is an argument, so this is the ordering itself under test.
  match recordDecision board5 [{ fixture := "prose", level := 5 }]
      ["prose: the engine's source has changed"] prov with
  | .ok t => bad := bad.push s!"--record wrote over a stale pairing: {repr t}"
  | .refused rs =>
    unless rs.any (·.startsWith "the pairing is stale") do
      bad := bad.push s!"--record stale reason: {repr rs}"
  -- A rise needs no line, and an unchanged board round trips.
  match wrote (recordDecision board5 [{ fixture := "prose", level := 5 }] [] prov) with
  | none => bad := bad.push "--record refused an unchanged measurement"
  | some _ => pure ()
  unless (refusedFor (recordDecision board5 [{ fixture := "prose", level := 5 },
      { fixture := "new", level := 3 }] [] prov)).isEmpty do
    bad := bad.push "--record refused a new fixture"
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
  -- the obligation row this branch adds owes for every comparison level with
  -- a declared blind spot — one equal under the level, unequal under the one
  -- above it.
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
  if args.contains "--repin" then
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
    -- was built is a stale pairing, never a level result.
    let src ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".tex"))
    let refSrc ← IO.FS.readFile (System.FilePath.mk parityDir / (stem ++ ".ref.tex"))
    let declared ← match declaredDivergences src with
      | .ok ds => pure ds
      | .error e => do
          IO.eprintln s!"parity {stem}: {e}"
          return 1
    if srcKeyOf src != side.srcKey then
      stale := stale.push s!"{stem}: the engine's source has changed since its reference was built \
(if only a comment or a declaration moved, --repin clears it without the reference engine)"
    if srcKeyOf refSrc != side.refSrcKey then
      stale := stale.push s!"{stem}: the reference source has changed since the reference was built"
    -- Every in-repo file the reference read, pinned. The shipped font is the
    -- one this catches: it is read by both engines, and an update to it
    -- would otherwise leave the engine on the new face and the committed
    -- reference on the old one, silently.
    for (p, k) in inputPins side.inputs do
      let path := System.FilePath.mk parityDir / p
      unless ← path.pathExists do
        stale := stale.push s!"{stem}: the reference read {p}, which is gone"
        continue
      if Flate.contentKey (← IO.FS.readBinFile path) != k then
        stale := stale.push s!"{stem}: {p} has changed since the reference read it"
    let refPath := System.FilePath.mk parityDir / (stem ++ ".ref.pdf")
    let refBytes ← if ← refPath.pathExists then IO.FS.readBinFile refPath else pure .empty
    if side.compiles then
      if refBytes.size != side.pdfSize || Flate.contentKey refBytes != side.pdfKey then
        stale := stale.push s!"{stem}: the committed reference is not the one the sidecar records"
    let (diags, ePages) ← engineSide oneFace mathSet shipped pats stem
    -- A reference the reader cannot read is a fault in the harness, not a
    -- level: every fixture would read as having fallen, and --record would
    -- store it. One reader reads both sides, so a regression in it is
    -- exactly the thing a measurement must not be allowed to express.
    let rPages ← if side.compiles then
        match readArtifact refBytes with
        | .ok ps => pure ps
        | .error e => do
            IO.eprintln s!"parity {stem}: the committed reference is unreadable — {e}"
            IO.eprintln "  This is a harness fault, not a level: no fixture is judged."
            return 1
      else pure #[]
    reached := reached.push (judge stem side declared diags ePages rPages)
  let boardProvenance : List String :=
    ["the parity ladder against lualatex: one integer per fixture, the number of",
     s!"levels that hold, of {Level.all.length} ({String.intercalate ", " (Level.all.map Level.tag)}). -1 means the",
     "reference engine refuses the document, which puts it outside the denominator.",
     "A level may rise and the rise must be recorded here; it may never fall.",
     "Retire a fixture with a '# retired: <fixture> — <why>' line, never by",
     "deleting its row. Lower a floor only with a",
     "'# lowered: <fixture> <old>→<new> — <why>' line, which accepts exactly",
     "that one fall.",
     "Written only by: .lake/build/bin/parity --record"]
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
  if record then
    match recordDecision boardText
        (reached.toList.map fun r => { fixture := r.fixture, level := r.level })
        stale.toList boardProvenance with
    | .refused rs =>
      IO.eprintln "parity --record: refused, and the scoreboard is untouched"
      for r in rs do IO.eprintln s!"    {r}"
      return 1
    | .ok text =>
      IO.FS.createDirAll (scoreboardPath.parent.getD ".")
      IO.FS.writeFile scoreboardPath text
      IO.println s!"parity --record: wrote {reached.size} row(s) to {scoreboardPath}"
      return 0
  unless stale.isEmpty do
    IO.eprintln "parity: the pairing is stale"
    for s in stale do IO.eprintln s!"    {s}"
    IO.eprintln "  Regenerate with: lake env lean --run scripts/parity-regen.lean --force <fixture>"
    return 1
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
top level {Level.all.length}"
  unless fell.isEmpty do
    IO.eprintln "parity: a level fell"
    for f in fell do IO.eprintln s!"    {f}"
    return 1
  unless rose.isEmpty do
    IO.eprintln "parity: a level rose and the scoreboard does not record it"
    for f in rose do IO.eprintln s!"    {f}"
    IO.eprintln "  Record it with: .lake/build/bin/parity --record"
    return 1
  unless staleDecl.isEmpty do
    IO.eprintln "parity: a divergence declaration is stale"
    for f in staleDecl do IO.eprintln s!"    {f}"
    IO.eprintln "  Remove the '% diverges:' line the engine no longer needs."
    return 1
  return 0
