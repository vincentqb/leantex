module

public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Cli.PicCache
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.PictureAssets

/-! The boundary's decisions. Whether a tool is runnable is a fact about the
machine, and what a tool that ran said is that tool's own words — neither is
this module's. What is this module's is the judgement taken once the answers
are in. When "nothing ran", an earlier render of the same request serves,
and where none exists the placeholder ships and the loss is named
(`coldPicture`). When a request was refused either way, a picture the
rendered subset draws in part is withdrawn from the boundary and drawn by
the subset (`withdraw`); an attempt that never reached an answer is no
refusal, and stands. One step here runs tools: a picture's HTML face is
its PDF converted to SVG and checked as publication checks it (`htmlFace`,
which runs the converter and the checks); a picture left
without one ships the page's labelled placeholder (`markFaceless`), as does
an included image whose plan a fact about the machine stopped
(`markUnplanned`). Each decision returns its diagnostics, so a test can run
it rather than restate it, and a driver that stopped naming the loss fails
the suite instead of passing it. -/

namespace LeanTex.Cli.Boundary

open LeanTex.Core

/-- With no tool, a complete checked drawing of the same request can serve.
Otherwise W0379 names the missing drawing at its source span, with `why`,
how the tool's version question ended. Refusals are not replayed here:
without the tool, its identity cannot be established. -/
public def coldPicture (picDir : System.FilePath) (tool key : String)
    (span : Option Span := none) (why : String := "") : IO (Except Diag ByteArray) := do
  match ← PictureAssets.previous picDir key with
  | some bytes => return .ok bytes
  | none => return .error (DriverDiag.boundaryToolUnavailable tool span why)

/-- What the boundary's refusals leave standing, once the rendered subset
has been asked to stand in: the picture ids whose requests are withdrawn,
the refusals that still stand, and why each withdrawn picture's request
came back undrawn — by picture id, the tool's own last words where it ran,
none where no tool looked. -/
public structure Withdrawal where
  ids : Array String := #[]
  standing : Array (String × Diag) := #[]
  said : Array (String × Option String) := #[]
  deriving Repr

/-- How a boundary request came back with no drawing. `answered` is an
answer the withdrawal may act on: no tool looked at the request (W0379,
`said` none), or the tool ran and said no, in its own words. `unfinished` is
an attempt that never reached an answer — a budget kill, a spawn that
raised, a nonzero exit that left no log (`PicCache.outcome`): a fact about
the machine, not the request. -/
public inductive Undrawn where
  | answered (why : Diag) (said : Option String)
  | unfinished (why : Diag)
  deriving Repr

/-- The refusal an undrawn request stands on when nothing withdraws it. -/
def Undrawn.why : Undrawn → Diag
  | .answered d _ => d
  | .unfinished d => d

/-- One attempt's ending as the withdrawal reads it: a drawing is nothing to
withdraw, the tool's own no is an answer in its words, and an attempt that
never finished is no answer at all. -/
public def undrawnOf (tool : String) (o : PicCache.Outcome) (span : Option Span) (src : String) :
    Option Undrawn :=
  match o with
  | .drawn => none
  | .refused says => some (.answered (DriverDiag.boundaryFailed tool says src span) (some says))
  | .inconclusive says => some (.unfinished (DriverDiag.boundaryUnfinished tool says src span))

/-- One undrawn request folded into the withdrawal: an answered one whose
picture the subset draws in part is withdrawn, with why it came back
undrawn; everything else stands. -/
public def withdrawStep (fallbacks : Array String) (w : Withdrawal)
    (r : String × Undrawn) : Withdrawal :=
  match r.2, fallbacks.find? (Ir.picSrcPrefix ++ · == r.1) with
  | .answered _ said, some id =>
    { w with ids := w.ids.push id, said := w.said.push (id, said) }
  | u, _ => { w with standing := w.standing.push (r.1, u.why) }

/-- **An attempt that never finished is never withdrawn** (`_exact`): it
joins the refusals that stand, whatever the subset could draw, so the run
stays as loud as a failed render — the artifact never changes on a fact
about the machine. The defect withdrew it like the tool's own verdict: a
killed or crashed tool shipped the subset's drawing with exit 0, its cause
a note printed only under `-v`. -/
public theorem withdrawStep_unfinished_exact (fallbacks : Array String) (w : Withdrawal)
    (src : String) (d : Diag) :
    withdrawStep fallbacks w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } := by
  unfold withdrawStep
  cases fallbacks.find? (Ir.picSrcPrefix ++ · == src) <;> rfl

/-- **A refusal withdraws a request the subset can stand in for.** An
answered request — no tool looked, or the tool said no — whose picture the
rendered subset draws in part (`fallbacks`, by picture id, the elaborator's
record) is withdrawn: the driver elaborates again with its id
(`Elab.runPrepared`'s `picWithdrawn`), and the subset's drawing ships with
one W0419 at the picture's span naming every construct it leaves out, its
help saying why the boundary did not draw it (`fold`), in the tool's own
words where it ran. Every other refusal stands: a picture the subset draws
nothing of keeps W0379's or W0382's placeholder, and an attempt that never
finished keeps its W0382 (`withdrawStep_unfinished_exact`). Pure, so the
decision is a value a test runs rather than a sentence about the driver. -/
public def withdraw (fallbacks : Array String) (undrawn : Array (String × Undrawn)) :
    Withdrawal :=
  undrawn.foldl (withdrawStep fallbacks) {}

/-- Is `d` one of withdrawn picture `id`'s losses? The elaborator names each
refusal the rendered subset states for a withdrawn picture under the
picture (`Ir.picFragmentKey`), so this reads the structured subject, never
the message; a note names a decision, not missing ink, and stands as it is. -/
public def fragmentOf (id : String) (d : Diag) : Bool :=
  d.subject.any (·.startsWith (Ir.picFragmentKey id "")) && d.kind.floor != .inert

/-- Is `d` the line that names withdrawn picture `id` where it stands in a
line of text, which the rendered subset never draws (`Ir.picInlineKey`)? -/
public def inlineOf (id : String) (d : Diag) : Bool :=
  d.subject == some (Ir.picInlineKey id)

/-- The fragments the fold takes: a loss the document's `\allow` accepts
(`accepted`) stays the elaborator's line, so its acceptance, and the
`\allow` entry it fires, are the document's as written. -/
private def taken (accepted : String → Bool) (id : String) (d : Diag) : Bool :=
  fragmentOf id d && !accepted d.code

/-- What a picture's one line says beside its refusals: why the boundary drew
none of it, for the picture in a paragraph of its own (`block`) and in a line
of text (`inline`; `none` leaves that line's own help). -/
public structure LineHelp where
  block : String
  inline : Option String := none
  deriving Repr, BEq

/-- A withdrawn picture's: the tool's own last words where it ran, or that
no tool looked (`DriverDiag.withdrawnHelp`). -/
public def withdrawnLine (tool : String) (said : Option String) : LineHelp :=
  { block := DriverDiag.withdrawnHelp tool said
    inline := some (DriverDiag.withdrawnInlineHelp tool said) }

/-- A declined picture's — one the document's `\pictures{ tool = none }`
leaves to the rendered subset (`Elab.ReqSpans.declined`): the declaration,
and what drawing it whole would take (`DriverDiag.declinedHelp`). -/
public def declinedLine : LineHelp := { block := DriverDiag.declinedHelp }

/-- The pictures whose refusals the driver folds, each with what its line
says: the withdrawn ones (`Withdrawal.said`) and the declined ones. -/
public def linesOf (tool : String) (w : Withdrawal) (declined : Array String) :
    Array (String × LineHelp) :=
  w.said.map (fun p => (p.1, withdrawnLine tool p.2)) ++ declined.map (·, declinedLine)

/-- One site of a picture as the line that names it: every loss the
rendered subset states for the picture there, in order, a clause after the
line's lead — in the record of the site's first fragment, so its span, its
site count and whether it is a repeat site stay what the elaborator made
them — under the picture's image source, with why the boundary drew none of
it (`help`). -/
public def lineOf (accepted : String → Bool) (help id : String) (ds : Array Diag)
    (first : Diag) : Diag :=
  let here := ((ds.filter fun e => taken accepted id e && e.span == first.span).map
    (·.message)).foldl (fun acc m => if acc.contains m then acc else acc.push m) #[]
  { first with
    kind := .W0419
    message := "the rendered subset draws this picture in part: " ++ " · ".intercalate here.toList
    help := first.help.map fun _ => help
    subject := some (Ir.picSrcPrefix ++ id)
    refused := none
    recovery := some (.replacedBy "the rendered subset's drawing") }

/-- A picture in a line of text keeps the line its own refusal names it by,
and takes why the boundary drew nothing as that line's help. -/
private def inlineHelp (p : String × LineHelp) (d : Diag) : Diag :=
  match p.2.inline with
  | some h => if inlineOf p.1 d && d.help.isSome then { d with help := some h } else d
  | none => d

/-- A refusal the document accepts that still says why the boundary drew
nothing: the first at a place where every refusal is accepted, since no
line is built there to say it. -/
private def voiced (accepted : String → Bool) (id : String) (ds : Array Diag)
    (spans : Array (Option Span)) (d : Diag) : Bool :=
  fragmentOf id d && d.help.isSome && !spans.contains d.span &&
    !ds.any fun e => taken accepted id e && e.span == d.span

/-- One step of one picture's fold: a site's line where its first fragment
stood, no other fragment, and everything else as it was. -/
private def placeLine (accepted : String → Bool) (p : String × LineHelp) (ds : Array Diag)
    (acc : Array Diag × Array (Option Span)) (d : Diag) : Array Diag × Array (Option Span) :=
  if taken accepted p.1 d then
    if acc.2.contains d.span then acc
    else (acc.1.push (lineOf accepted p.2.block p.1 ds d), acc.2.push d.span)
  else if voiced accepted p.1 ds acc.2 d then
    (acc.1.push { d with help := some p.2.block }, acc.2.push d.span)
  else (acc.1.push (inlineHelp p d), acc.2)

/-- One picture folded. -/
private def foldOne (accepted : String → Bool) (ds : Array Diag) (p : String × LineHelp) :
    Array Diag :=
  (ds.foldl (placeLine accepted p ds) (#[], #[])).1

/-- **A picture the rendered subset draws in part is named once at each
place it stands.** The elaboration names every construct the subset leaves
out of a withdrawn or declined picture, each keyed under the picture
(`fragmentOf`); this folds the ones the document does not accept (`allow`,
`allowAll`, read as `Diag.accept` reads them) into one line per site of the
picture (W0419, `lineOf`), a degraded warning, so an expression the subset
could not read no longer fails the document the picture stands in, and a
repeat site stays a repeat site with its count. Where the document accepts
every refusal at a place, the first keeps why the boundary drew nothing as
its help. A picture in a line of text, which the subset never draws, keeps
the line that says so, with why the boundary did not draw it as its help.
Every other diagnostic is still there (`foldLines_covers`). The refusals
once stood beside a note as several lines, an error among them, and a
picture no renderer could draw cost the whole run. -/
public def foldLines (allow : Array String) (allowAll : Bool) (lines : Array (String × LineHelp))
    (ds : Array Diag) : Array Diag :=
  -- premise: pictureRouteChecks — every refusal folded is a clause of its
  -- picture's line, and an accepted one is left as the document accepts it
  lines.foldl (foldOne fun c => allowAll || allow.contains c) ds

/-- The withdrawn pictures alone (`foldLines` over `linesOf tool w #[]`). -/
public def fold (allow : Array String) (allowAll : Bool) (tool : String) (w : Withdrawal)
    (ds : Array Diag) : Array Diag :=
  foldLines allow allowAll (linesOf tool w #[]) ds

private theorem placeLine_keeps (accepted : String → Bool) (p : String × LineHelp)
    (ds : Array Diag) (d : Diag) :
    ∀ (xs : List Diag) (acc : Array Diag × Array (Option Span)), d ∈ acc.1 →
      d ∈ (xs.foldl (placeLine accepted p ds) acc).1 := by
  intro xs
  induction xs with
  | nil => intro acc hd; exact hd
  | cons x rest ih =>
    intro acc hd
    apply ih
    unfold placeLine
    split
    · split
      · exact hd
      · exact Array.mem_push_of_mem _ hd
    · split
      · exact Array.mem_push_of_mem _ hd
      · exact Array.mem_push_of_mem _ hd

private theorem placeLine_adds (accepted : String → Bool) (p : String × LineHelp)
    (ds : Array Diag) (d : Diag) (h : fragmentOf p.1 d = false) (hi : inlineOf p.1 d = false) :
    ∀ (xs : List Diag) (acc : Array Diag × Array (Option Span)), d ∈ xs →
      d ∈ (xs.foldl (placeLine accepted p ds) acc).1 := by
  intro xs
  induction xs with
  | nil => intro _ hd; cases hd
  | cons x rest ih =>
    intro acc hd
    rcases List.mem_cons.mp hd with rfl | hr
    · apply placeLine_keeps accepted p ds d rest
      have hk : inlineHelp p d = d := by
        unfold inlineHelp
        split <;> simp [hi]
      simp only [placeLine, taken, voiced, h, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hk]
      exact Array.mem_push_self
    · exact ih _ hr

/-- **The fold changes only the folded pictures' own lines** (`_covers`):
every diagnostic that is neither a fragment of a picture the fold names nor
that picture's line in a line of text is still there after the fold — the
document's other losses, and the pictures' notes. -/
public theorem foldLines_covers (allow : Array String) (allowAll : Bool)
    (lines : Array (String × LineHelp)) (ds : Array Diag) (d : Diag) (hd : d ∈ ds)
    (h : ∀ p ∈ lines, fragmentOf p.1 d = false ∧ inlineOf p.1 d = false) :
    d ∈ foldLines allow allowAll lines ds := by
  unfold foldLines
  rw [← Array.foldl_toList]
  have key : ∀ (ps : List (String × LineHelp)) (acc : Array Diag), d ∈ acc →
      (∀ p ∈ ps, fragmentOf p.1 d = false ∧ inlineOf p.1 d = false) →
      d ∈ ps.foldl (foldOne fun c => allowAll || allow.contains c) acc := by
    intro ps
    induction ps with
    | nil => intro acc hacc _; exact hacc
    | cons q rest ih =>
      intro acc hacc hall
      have hq := hall q (List.mem_cons_self ..)
      apply ih _ _ fun p hp => hall p (List.mem_cons_of_mem _ hp)
      unfold foldOne
      rw [← Array.foldl_toList]
      exact placeLine_adds _ q acc d hq.1 hq.2 acc.toList _ (Array.mem_toList_iff.mpr hacc)
  exact key lines.toList ds hd fun p hp => h p (Array.mem_toList_iff.mp hp)

/-- **The withdrawal's fold changes only the withdrawn pictures' own lines**
(`_covers`): `foldLines_covers` for the withdrawn pictures alone. -/
public theorem fold_covers (allow : Array String) (allowAll : Bool) (tool : String)
    (w : Withdrawal) (ds : Array Diag) (d : Diag) (hd : d ∈ ds)
    (h : ∀ p ∈ w.said, fragmentOf p.1 d = false ∧ inlineOf p.1 d = false) :
    d ∈ fold allow allowAll tool w ds := by
  apply foldLines_covers allow allowAll _ ds d hd
  intro p hp
  simp only [linesOf, Array.mem_append, Array.mem_map] at hp
  rcases hp with ⟨q, hq, rfl⟩ | ⟨id, hid, rfl⟩
  · exact h q hq
  · simp at hid

/-- **The HTML face withdraws a drawing it cannot show.** A boundary
picture's page face is its PDF, and its HTML face the SVG converted from
that PDF, checked (`htmlFace`). Where it is missing (W0378) — the
conversion failed, or its check did not finish — the image has nothing to
show but a request key, so a picture the rendered subset draws in part —
`fallbacks`, the elaborator's record — is withdrawn from the HTML face
alone, which the driver elaborates again with it drawn by the subset; the
PDF keeps the boundary's drawing. The ids, by picture: those among the
fallbacks whose image source has no checked SVG (`unconverted`). -/
public def htmlWithdraw (fallbacks unconverted : Array String) : Array String :=
  fallbacks.filter fun id => unconverted.contains (Ir.picSrcPrefix ++ id)

/-- A converted face, read by the check publication will run on it. A check
that never finished leaves the picture unconverted, as a failed conversion
does: the page cannot publish bytes it could not check, and a fact about the
machine must not refuse the page. A check that reached a verdict keeps the
face, and publication reads that verdict (`Publication.svgVerdict`). -/
public def checkedFace (svg : ByteArray) : PicCache.Outcome → Except String ByteArray
  -- premise: machineLossChecks — an unchecked face takes the unconverted path, whose
  -- W0378 the driver emits at the picture's span; a validator's own refusal is a
  -- verdict and never lands here
  | .inconclusive why => .error why
  | .drawn | .refused _ => .ok svg

/-- **A check that never finished leaves the picture unconverted** (`_exact`):
the face is withdrawn exactly when its check is inconclusive, in the check's
own words, so a machine that could not check a face takes the path a machine
that could not convert it takes — W0378 at the picture's span, and the
rendered subset's drawing where it draws the picture in part. The defect
kept the unchecked face, which publication then omitted after the withdrawal
was decided: the subset never stood in, and W0378 lost its span. -/
public theorem checkedFace_unfinished_exact (svg : ByteArray) (o : PicCache.Outcome)
    (why : String) : checkedFace svg o = .error why ↔ o = .inconclusive why := by
  cases o <;> simp [checkedFace]

/-- **A check that reached a verdict keeps the face** (`_exact`): drawn or
refused, the converted bytes stand, so the boundary's refusal still refuses
the page through publication's own check. -/
public theorem checkedFace_verdict_exact (svg : ByteArray) (o : PicCache.Outcome)
    (h : ∀ why, o ≠ .inconclusive why) : checkedFace svg o = .ok svg := by
  cases o with
  | inconclusive why => exact absurd rfl (h why)
  | drawn | refused _ => rfl

/-- One boundary picture's HTML face: its PDF converted to SVG
(`ImageAssets.picFace`), then checked as publication checks every embedded
SVG (`ImageAssets.validateSvgResult`), and read by `checkedFace`. -/
public def htmlFace (pdf : ByteArray) : IO (Except String ByteArray) := do
  match ← ImageAssets.picFace pdf with
  | .error why => return .error why
  | .ok svg => return checkedFace svg (← ImageAssets.validateSvgResult svg)

/-- A boundary picture's HTML face is missing whatever the cause — no tool
drew it (W0379), the tool drew nothing or did not finish (W0382), or its face was not
converted or not checked (W0378) — and that loss was named where it
happened, so the reason the page records is this constant and adds no
diagnostic. -/
public def facelessReason : String :=
  "the boundary picture has no browser face"

/-- A boundary-picture entry the HTML page holds neither a face nor a
reason for: its image would keep the request key as its `src`, which no
resource answers. -/
public def faceless (en : Image.Loaded) : Bool :=
  en.src.startsWith Ir.picSrcPrefix && en.webSvg.isNone && en.webError.isNone

private def markOne (en : Image.Loaded) : Image.Loaded :=
  -- premise: machineLossChecks — a faceless picture's loss was named where it happened
  -- (W0379, W0382, or W0378), so the mark names none
  if faceless en then { en with webError := some facelessReason } else en

/-- **A missing face degrades the page instead of refusing it.** The closure
check refused the whole HTML artifact (E0606) for a boundary picture with no
face — the store kept its request key as the image's `src`, which resolves
to no resource — although the PDF shipped its placeholder and the loss was
already named. Marked, the entry takes the page's existing failed-face arm:
a span labelled with the picture's text alternative, which reserves the
drawing's intrinsic box when the boundary drew one, and is only as large as
its label when nothing did — while the PDF draws a placeholder box. That the
marked page closes is evidence, not a theorem: `machineLossChecks` closes it
over the fixture's IR and through the built binary. -/
public def markFaceless (s : Image.Store) : Image.Store :=
  { entries := s.entries.map markOne }

/-- **Every boundary picture has a face or a reason** (`_covers`). -/
public theorem markFaceless_covers (s : Image.Store) :
    ∀ en ∈ (markFaceless s).entries, en.src.startsWith Ir.picSrcPrefix = true →
      en.webSvg.isSome = true ∨ en.webError.isSome = true := by
  intro en hen hsrc
  simp only [markFaceless, Array.mem_map] at hen
  obtain ⟨e, -, rfl⟩ := hen
  unfold markOne at hsrc ⊢
  cases hf : faceless e with
  | true => simp
  | false =>
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hsrc ⊢
    cases hs : e.webSvg with
    | some _ => exact .inl rfl
    | none =>
      cases hw : e.webError with
      | some _ => exact .inr rfl
      | none => simp [faceless, hsrc, hs, hw] at hf

/-- **Only the HTML face's reason changes** (`_exact`): with `webError`
erased, the marked store is the store — every native plan, request, size and
captured byte. Only the HTML backend reads `webError`; the layout and the
PDF writer read the rest, which this holds fixed. -/
public theorem markFaceless_info_exact (s : Image.Store) :
    (markFaceless s).entries.map (fun en => { en with webError := none }) =
      s.entries.map (fun en => { en with webError := none }) := by
  simp only [markFaceless, Array.map_map]
  congr 1
  funext en
  simp only [Function.comp, markOne]
  split <;> rfl

/-- **An entry with a face, or a reason, or no picture is unchanged** (`_exact`). -/
public theorem markFaceless_face_exact (s : Image.Store) (k : Nat) (en : Image.Loaded)
    (h : s.get? k = some en) (hface : faceless en = false) :
    (markFaceless s).get? k = some en := by
  simp only [Image.Store.get?, markFaceless, Array.getElem?_map] at h ⊢
  simp [h, markOne, hface]

/-- The reason an included image's HTML face records when a fact about the
machine stopped its plan: W0602 named it where the plan stopped, so the
page's placeholder adds no diagnostic. -/
public def unplannedReason : String :=
  "the image's plan did not finish on this machine"

/-- An entry a stopped plan left: no plan, and no face or reason yet. -/
public def unplanned (stopped : Array Image.Request) (en : Image.Loaded) : Bool :=
  stopped.contains en.toRequest && en.info.isNone && en.webError.isNone

private def markStopped (stopped : Array Image.Request) (en : Image.Loaded) : Image.Loaded :=
  -- premise: machineLossChecks — W0602 named the include where its plan stopped, and the
  -- page names no image that has no plan, so the mark names none
  if unplanned stopped en then { en with webError := some unplannedReason } else en

/-- **A plan the machine stopped degrades the page instead of refusing it.**
An included SVG whose check or conversion did not finish — a tool missing,
killed or out of time — has no plan, so the PDF places its placeholder box
and W0602 names it; the page kept the authored path as the image's source,
which no checked resource answers, and the closure check refused the whole
HTML artifact (E0606). Marked, the entry takes the page's failed-face arm, a
span labelled with the image's text alternative, and W0602 stays the one
accounting. A file the tools read and refused keeps the refusal: only the
requests whose plan a fact about the machine stopped are marked (`stopped`,
the driver's record). -/
public def markUnplanned (stopped : Array Image.Request) (s : Image.Store) : Image.Store :=
  { entries := s.entries.map (markStopped stopped) }

/-- **Every stopped include has a reason** (`_covers`). -/
public theorem markUnplanned_covers (stopped : Array Image.Request) (s : Image.Store) :
    ∀ en ∈ (markUnplanned stopped s).entries, stopped.contains en.toRequest = true →
      en.info.isNone = true → en.webError.isSome = true := by
  intro en hen hreq hinfo
  simp only [markUnplanned, Array.mem_map] at hen
  obtain ⟨e, -, rfl⟩ := hen
  unfold markStopped at hreq hinfo ⊢
  cases hu : unplanned stopped e with
  | true => simp
  | false =>
    simp only [hu, Bool.false_eq_true, ↓reduceIte] at hreq hinfo ⊢
    cases hw : e.webError with
    | some _ => rfl
    | none =>
      simp [unplanned, hinfo, hw] at hu
      exact absurd (by simpa using hreq) hu

/-- **Only the HTML face's reason changes** (`_exact`): with `webError`
erased, the marked store is the store, so the layout and the PDF writer read
what they read before. -/
public theorem markUnplanned_info_exact (stopped : Array Image.Request) (s : Image.Store) :
    (markUnplanned stopped s).entries.map (fun en => { en with webError := none }) =
      s.entries.map (fun en => { en with webError := none }) := by
  simp only [markUnplanned, Array.map_map]
  congr 1
  funext en
  simp only [Function.comp, markStopped]
  split <;> rfl

/-- **An entry no stopped plan left is unchanged** (`_exact`). -/
public theorem markUnplanned_kept_exact (stopped : Array Image.Request) (s : Image.Store)
    (k : Nat) (en : Image.Loaded) (h : s.get? k = some en)
    (hkept : unplanned stopped en = false) :
    (markUnplanned stopped s).get? k = some en := by
  simp only [Image.Store.get?, markUnplanned, Array.getElem?_map] at h ⊢
  simp [h, markStopped, hkept]

end LeanTex.Cli.Boundary
