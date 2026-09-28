import Tests.DiagAudit
import Tests.Regress
import Tests.Census
import Tests.Conditionals
import Tests.BoxRow
import Tests.PackageCode
import Tests.Artifact
import Tests.HtmlTokens
import Tests.Settings
import Tests.Redefine
import scripts.LandCore

/-!
# Every breakage the user reported, and what holds it closed

The user's rule: a reported breakage gets assertions, theorems or tests that
reproduce it, so the error is never seen again. A row here is one report as a
value: when it came, what broke in abstract words — the construct, never the
document — the pins to its guards, and the run that saw them fail on the
broken tree.

A pin is `DiagAudit.Pin`, so it resolves or does not compile: `thm%` carries
the proof, `check%` elaborates the block and holds only while the suite runs
it, a tier pin while the committed baseline holds its item. What no in-tree
check can see — a private document's own build, a port that invokes the
binary — is an acceptance run, named in abstract words.

A report is closed only as `guarded`, naming the tree its guards failed on
and whose record says so. What is not closed stays visible: `unwitnessed`
(guards, but no failing run on record) and `owed` (no guard yet, the owner
and the guard's name once it lands) are counts the suite holds in both
directions, and an owed guard that lands fails the suite until its row is
promoted.
-/

open LeanTex.Core
open DiagAudit (Pin suiteText)

namespace Reports

/-- Whose record shows a guard failing. -/
inductive Seen where
  /-- An independent reviewer's run. -/
  | reviewer
  /-- The fix's author, in its commit or its plan entry. -/
  | author
  /-- This registry's own run. -/
  | audit
  deriving Repr, BEq

/-- The tree a failing run built. -/
inductive Run where
  /-- The tree at the named commit, before the fix. -/
  | before
  /-- The tree at the named commit with the fix reverted. -/
  | revert
  deriving Repr, BEq

/-- Where a report stands. -/
inductive State where
  /-- Its guards failed on `sha` (built as `run`, recorded by `seen`) and
  pass on this tree. -/
  | guarded (sha : String) (run : Run) (seen : Seen)
  /-- Guarded, but no failing run is on record. -/
  | unwitnessed
  /-- Measured or decided: no defect of the engine as it stands; the pins
  hold the measurement. -/
  | answered
  /-- Not closed: `owner` owes it, and `guards` are the names its guards
  land under. -/
  | owed (owner : String) (guards : List String)

structure Report where
  id : String
  date : String
  what : String
  pins : List Pin
  accept : List String := []
  state : State

/-- The reports, oldest first. -/
def reports : List Report := [
  { id := "R01", date := "2026-09-16"
    what := "two section headings vanished in one PDF viewer and showed in two others: a text-positioning adjustment past sixteen bits"
    pins := [check% pdfStreamChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R02", date := "2026-09-16"
    what := "a résumé did not build as written, set the gap under its large name line far too wide, ran onto a second page, and let a built-in shadow the document's own macro"
    pins := [check% spacingChecks, check% compatChecks]
    accept := ["the résumé's own check recipe, against its lualatex build"]
    state := .unwitnessed },
  { id := "R03", date := "2026-09-16"
    what := "a fixture failed on another machine: fixtures named the host's fonts, and the harness read the host's font directories"
    pins := [check% runGoldens]
    accept := ["the corpus built in a mount namespace with every system and TeX font directory emptied"]
    state := .unwitnessed },
  { id := "R04", date := "2026-09-17"
    what := "unsupported constructs shipped as warnings or in silence where the content was lost"
    pins := [check% diagChecks]
    state := .unwitnessed },
  { id := "R05", date := "2026-09-17"
    what := "the footline's right slot must stay pinned to the right margin, a lower-priority slot painted over rather than reflowed"
    pins := [thm% Layout.bandSlotX_right_pinned, check% bandChecks]
    state := .unwitnessed },
  { id := "R06", date := "2026-09-17"
    what := "a slide's frame footer was not visible"
    pins := [thm% Layout.bodyBottom_clears_footer, check% footerBandChecks,
      check% chromeFooterChecks]
    state := .guarded "7ff2ddec" .revert .author },
  { id := "R07", date := "2026-09-17"
    what := "six defects visible on one rendered page while every check was green"
    pins := [check% censusChecks]
    state := .unwitnessed },
  { id := "R08", date := "2026-09-17"
    what := "caption and float spacing drifted from document to document"
    pins := [thm% Ir.caption_gaps_rhythm, check% tableChecks]
    state := .unwitnessed },
  { id := "R09", date := "2026-09-17"
    what := "a site's metadata title drifted from its visible title, and anchor slugs folded to ASCII, merging two distinct titles"
    pins := [check% webMetaChecks, thm% Ir.slug_no_whitespace]
    state := .guarded "29173800" .revert .author },
  { id := "R10", date := "2026-09-18"
    what := "the math face never matched the text face's size, so documents aligned the two by hand"
    pins := [thm% Math.mathSize_matches]
    state := .unwitnessed },
  { id := "R11", date := "2026-09-18"
    what := "the vertical rhythm held for PDF by theorem and for HTML only by a comment"
    pins := [thm% HtmlDoc.backend_gaps_agree, check% htmlRhythmChecks]
    state := .unwitnessed },
  { id := "R12", date := "2026-09-18"
    what := "a site port rendered a declared 32 px gap as 52 px: two rules owned one boundary"
    pins := [check% htmlRhythmChecks]
    accept := ["the site port's build and its structural comparison"]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R13", date := "2026-09-18"
    what := "a declared scroll reveal did not play in a browser's release version; decided since: the reveal is declarative where supported, and elsewhere the content stands visible with no script"
    pins := [check% pinChecks]
    state := .answered },
  { id := "R14", date := "2026-09-18"
    what := "a site port's alternate markdown link named a file other than the one served, and a face installed on the host displaced the face the document ships"
    pins := [check% mdNameChecks, check% fallbackChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R15", date := "2026-09-20"
    what := "a picture on a slide shipped far too small, and an image sized against the text height emitted nothing in HTML"
    pins := [thm% HtmlDoc.image_share_agrees, check% deckImageChecks]
    state := .unwitnessed },
  { id := "R16", date := "2026-09-21"
    what := "the HTML deck advanced on the wrong axis, took several key presses per frame, showed partial slides between frames and drew step-counter chrome"
    pins := [thm% HtmlDoc.deck_script_constant, thm% HtmlDoc.snap_pages_partition_frames,
      check% deckCssChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R17", date := "2026-09-21"
    what := "a construct the engine misunderstands reached a backend with no warning naming it"
    pins := [thm% pending_named, check% pendingChecks]
    state := .unwitnessed },
  { id := "R18", date := "2026-09-23"
    what := "a build stayed slow: pictures the external tool refused were re-rendered on every build"
    pins := [thm% LeanTex.Cli.PicCache.probed_present_exact, check% picCacheChecks]
    state := .guarded "fe4de50f" .revert .author },
  { id := "R19", date := "2026-09-24"
    what := "a diagram node's anchors sat on its letters rather than its border, so edges started inside the text"
    pins := [thm% Picture.borderHalf_between, check% pictureInnerSepChecks]
    state := .guarded "af457b47" .before .author },
  { id := "R20", date := "2026-09-24"
    what := "a diagram node written with a second key bracket was refused, so its label went missing and edges naming it were refused"
    pins := [thm% Picture.prologue_swap_agree, check% pictureNodePrologueChecks]
    state := .guarded "b0b3ec31" .before .author },
  { id := "R21", date := "2026-09-24"
    what := "two words side by side, one with a descender, looked vertically misaligned; measured: no glyph moves a label's baseline here"
    pins := [thm% Layout.labelVStep_glyph_id, check% labelBaselineChecks]
    state := .answered },
  { id := "R22", date := "2026-09-24"
    what := "a deck's HTML front page rendered nearly blank: a title page inside the author's own frame opened a slide inside a slide"
    pins := [check% nestedStageChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R23", date := "2026-09-24"
    what := "a themed deck's HTML ignored the frame-title bar's padding token and emitted no title band"
    pins := [check% htmlTokenClosureChecks, check% artBandParityChecks]
    state := .guarded "6a143e3f" .before .author },
  { id := "R24", date := "2026-09-24"
    what := "a title's declared two-line break shipped as three lines, flush left, then indented, then flush left"
    pins := [check% titleBreakChecks]
    state := .guarded "3294654b" .before .author },
  { id := "R25", date := "2026-09-24"
    what := "a style file's package-loaded test printed the tested package's name, and both branches, at the top of a paper's first page; reported again after a first fix"
    pins := [check% loadedTestChecks, check% packageCodeChecks,
      thm% Elab.recoverPackageCmd_accounts]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R26", date := "2026-09-24"
    what := "a cancel-to construct met a package that does not load, and its floor set the two arguments as a product"
    pins := [check% pictureNodeFloorChecks, check% mathContainChecks, check% compatIndexChecks]
    state := .guarded "0417420a" .before .author },
  { id := "R27", date := "2026-09-25"
    what := "a theme declared a full-bleed title-page ground, and the title page still rendered the built-in"
    pins := [check% artGroundParityChecks, thm% Ir.Design.titleGround_exact]
    state := .guarded "32ef2dd7" .revert .author },
  { id := "R28", date := "2026-09-25"
    what := "a URL-style selector drew a warning that URLs set monospace, which the page contradicted, and the selector was discarded rather than honoured"
    pins := [check% monoSlotChecks, check% compatIndexChecks, .tier "compat" "url.impl"]
    state := .guarded "efcd27e2" .before .reviewer },
  { id := "R29", date := "2026-09-25"
    what := "one unknown command carrying an option run printed two warnings for one construct at one site"
    pins := [check% optionRunAccountingChecks, check% siteAccountingChecks,
      thm% Elab.unknownCmdDiag_code_exact]
    state := .guarded "efcd27e2" .before .reviewer },
  { id := "R30", date := "2026-09-26"
    what := "a deck's title page ignored its theme's title-page template: the default ground, sizes and separator"
    pins := [check% themeTitleShipChecks, check% titleSlotShipChecks,
      thm% Layout.slotShift_exact]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R31", date := "2026-09-26"
    what := "two boxes declared side by side stacked one above the other"
    pins := [check% minipageRowChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R32", date := "2026-09-26"
    what := "a picture drawn under different macro states drew the same branch every time"
    pins := [check% condAccountingChecks, check% picStateChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R33", date := "2026-09-26"
    what := "a picture node's bold text set in the regular face"
    pins := [check% pictureNodeStyleChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R34", date := "2026-09-26"
    what := "the space around a drawn picture on a slide was too tight"
    pins := [check% pictureBoxChecks, check% trivlistChecks, check% frameBodyChecks,
      thm% Ir.Pic.Picture.box_declared_exact]
    state := .guarded "f9ebb1e5" .before .reviewer },
  { id := "R35", date := "2026-09-26"
    what := "main was pushed to the public remote twice with nobody's approval; the harness mechanism is guarded, the cause is unproven"
    pins := [thm% Land.hcall_writes_owned, thm% Land.hpush_owned]
    state := .owed "the user: a pre-push hook that refuses an unapproved push" [] },
  { id := "R36", date := "2026-09-27"
    what := "declared settings were reported as ignored across documents rather than implemented"
    pins := [check% paramSiteChecks, check% abstractRedefChecks]
    state := .guarded "da9b049d" .before .author },
  { id := "R37", date := "2026-09-27"
    what := "a business card rendered wrong: its page boxes, bleed, marks, lengths and faces"
    pins := [check% filChecks, check% driverOptionChecks, check% drawnMarkChecks,
      check% pdfVersionChecks]
    accept := ["the card's own print check recipe — page boxes, cut marks, fonts, exact strings — against the engine's PDF"]
    state := .guarded "da9b049d" .before .author },
  { id := "R38", date := "2026-09-27"
    what := "a website broke: every centred environment gained a wrapper element"
    pins := [check% trivlistChecks, thm% HtmlDoc.pictureSvg_overflow_contract,
      thm% HtmlDoc.blockGap_owner_contract]
    accept := ["the site port's build script and its structural comparison at three widths"]
    state := .guarded "da9b049d" .before .author },
  { id := "R39", date := "2026-09-27"
    what := "a website's build named a declared line break lost where the author's line held and only the prose after it wrapped"
    pins := [check% titleBreakChecks]
    accept := ["the site port's build, whose diagnostics name no declared-line-break loss"]
    state := .guarded "f66f9381" .before .author },
  { id := "R40", date := "2026-09-27"
    what := "a business card's text did not stand vertically centred on its faces: the gaps above and below its block differed"
    pins := [check% faceCentreChecks]
    accept := ["the card's own print check recipe, against its lualatex build"]
    state := .guarded "f16b1321" .before .author }
]

/-- The reports guarded but never seen failing: a count that may fall and
never rise, and falls only when this line does. -/
def unwitnessedBaseline : Nat := 10

/-- The reports not closed, the same way. -/
def owedBaseline : Nat := 1

def Report.unwitnessed (r : Report) : Bool := r.state matches .unwitnessed

def Report.owed (r : Report) : Bool := r.state matches .owed ..

/-- The owed guard names of a row. -/
def Report.owedGuards (r : Report) : List String :=
  match r.state with
  | .owed _ gs => gs
  | _ => []

/-- A commit named by at least eight lowercase hex digits. -/
def isSha (s : String) : Bool :=
  s.length ≥ 8 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- `YYYY-MM-DD`. -/
def isDate (s : String) : Bool :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] =>
    [y1, y2, y3, y4, m1, m2, d1, d2].all Char.isDigit
  | _ => false

/-- A description in abstract words: no path, no file, no address. -/
def isAbstract (s : String) : Bool :=
  !(["/", "\\", "@", ".tex", ".sty", ".pdf", "http"].any (hasStr s ·))

/-- What is wrong with a row, or nothing: its identity, its words, and a
state its pins can carry. -/
def Report.faults (r : Report) (i : Nat) : List String :=
  let name := if i + 1 < 10 then s!"R0{i + 1}" else s!"R{i + 1}"
  (if r.id == name then [] else [s!"{r.id}: ids run R01, R02, … in order; expected {name}"]) ++
  (if isDate r.date then [] else [s!"{r.id}: the date '{r.date}' is not YYYY-MM-DD"]) ++
  (if isAbstract r.what && !r.what.isEmpty then []
    else [s!"{r.id}: the description names a path, a file or an address"]) ++
  (if r.accept.all isAbstract then [] else [s!"{r.id}: an acceptance run names a path"]) ++
  match r.state with
  | .guarded sha _ _ =>
    (if isSha sha then [] else [s!"{r.id}: '{sha}' is not a commit"]) ++
    (if r.pins.isEmpty then [s!"{r.id}: a guarded report pins its guards"] else [])
  | .unwitnessed | .answered =>
    if r.pins.isEmpty then [s!"{r.id}: a closed report pins what holds it"] else []
  | .owed owner _ => if owner.isEmpty then [s!"{r.id}: an owed report names its owner"] else []

/-- Every Lean source the tree builds but this registry, stripped to code:
where an owed guard's name appears once it lands. -/
def treeText : IO String := do
  let mut text := ""
  for dir in ["LeanTex", "Tests"] do
    for f in ← System.FilePath.walkDir dir do
      if f.toString.endsWith ".lean" && f.toString != "Tests/Reports.lean" then
        text := text ++ stripNonCode (← IO.FS.readFile f)
  return text

end Reports

open Reports in
/-- **Every reported breakage is a row, and every row is held.** Rows are
well formed and in order; every pin resolves; an owed guard that has landed
fails until its row is promoted; and the unwitnessed and owed counts equal
their baselines, so closing a report and opening one are both edits here. -/
def reportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let suite ← suiteText
  let tree ← treeText
  let faults := (reports.zipIdx.map fun (r, i) => r.faults i).flatten
  t s!"reports: every row is well formed ({faults})" faults.isEmpty
  let mut dead : List String := []
  for r in reports do
    for p in r.pins do
      unless ← p.resolves suite do dead := s!"{r.id}: {p.name}" :: dead
  t s!"reports: every pin holds a guard ({dead.reverse})" dead.isEmpty
  let landed := reports.filterMap fun r =>
    let hit := r.owedGuards.filter (wordCount tree · ≥ 1)
    if hit.isEmpty then none else some s!"{r.id}: {hit}"
  t s!"reports: no owed guard has landed unrecorded ({landed})" landed.isEmpty
  let dates := reports.map (·.date)
  t "reports: rows run oldest first" (dates.zip (dates.drop 1) |>.all fun (a, b) => a ≤ b)
  let unw := (reports.filter (·.unwitnessed)).length
  t s!"reports: {unw} unwitnessed, the baseline {unwitnessedBaseline}"
    (unw == unwitnessedBaseline)
  let owed := (reports.filter (·.owed)).length
  t s!"reports: {owed} owed, the baseline {owedBaseline}" (owed == owedBaseline)
  -- The judges, once each way.
  t "reports: a short or cased sha is not a commit"
    (isSha "17ac92f4" && !isSha "17ac92f" && !isSha "17AC92F4")
  t "reports: a path is not an abstract description"
    (isAbstract "a picture node's bold text" && !isAbstract "a file under tests/corpus")
  t "reports: an owed name is found once it is written, and only then"
    (wordCount "def paramSiteChecks" "paramSiteChecks" == 1 &&
      wordCount "def paramSiteChecksMore" "paramSiteChecks" == 0)
