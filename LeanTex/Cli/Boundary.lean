module

public import LeanTex.Core.Diag
public import LeanTex.Core.Ir
public import LeanTex.Core.Gfx
public import LeanTex.Core.FigureLoss
public import LeanTex.Cli.PicCache
public import LeanTex.Cli.World
import LeanTex.Cli.DriverDiag
import LeanTex.Cli.ImageAssets
import LeanTex.Cli.PictureAssets

/-! The boundary's decisions once a tool's answers are in: an earlier render or a named
placeholder when nothing ran, the rendered subset's drawing for a refused picture it draws
in part, and the faceless mark for the HTML page. -/

namespace LeanTex.Cli.Boundary

open LeanTex.Core

/-- With no tool, a complete checked drawing of the same request serves; otherwise W0379
names the missing drawing at its span, with `why`. -/
public def coldPicture (picDir : System.FilePath) (tool key : String)
    (span : Option Span := none) (why : String := "") : IO (Except Diag ByteArray) := do
  match ← PictureAssets.previous picDir key with
  | some bytes => return .ok bytes
  | none => return .error (DriverDiag.boundaryToolUnavailable tool span why)

/-- Where a request's input spelled `cand` is read: against the document's
directory `dir`, unless absolute. -/
public def inputPath (dir cand : String) : String :=
  if cand.startsWith "/" then cand else World.ToolPath.join dir cand

/-- The first of a path's graphicx candidates that stands, read once, by the
path it spells, against the document's directory `dir` unless absolute;
none standing leaves `out` as it was, for the tool to name. -/
public def firstInput (dir : String) (out : Array (String × ByteArray)) :
    List String → World.Prog (Array (String × ByteArray))
  | [] => .pure out
  | cand :: rest =>
    let path := inputPath dir cand
    .ask (.stat path) fun
      | .ok _ => .ask (.readFile path) fun
        | .ok bytes => .pure (out.push (cand, bytes))
        | .error _ => .pure out
      | .error _ => firstInput dir out rest

/-- The files a boundary request reads, resolved as the document's images are (graphicx
extensions, `\graphicspath`) and read once, keyed by their bytes. -/
public def requestInputs (dir : String) (paths : Array String) (wrapped : String) :
    World.Prog (Array (String × ByteArray)) :=
  (Ir.pictureInputs wrapped).foldlM (init := #[]) fun out p =>
    firstInput dir out (Image.searchCandidates paths p)

/-- The document's own request, asked only after the tool refused the one set in the
page's faces, and only when it differs from it. -/
public def ownRequest? (wrapped own : String) : PicCache.Outcome → Option String
  | .refused _ => if own == wrapped then none else some own
  | .drawn | .inconclusive _ => none

public theorem ownRequest?_exact (wrapped own r : String) (o : PicCache.Outcome) :
    ownRequest? wrapped own o = some r ↔ (∃ why, o = .refused why) ∧ own ≠ wrapped ∧ r = own := by
  cases o with
  | refused why =>
    by_cases h : own = wrapped
    · subst h
      simp [ownRequest?]
    · have hb : (own == wrapped) = false := by simpa using h
      simp only [ownRequest?, hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      exact ⟨fun e => ⟨⟨why, rfl⟩, h, e.symm⟩, fun ⟨_, _, e⟩ => e.symm⟩
  | drawn => simp [ownRequest?]
  | inconclusive _ => simp [ownRequest?]

/-- What the boundary's refusals leave once the rendered subset stands in: the withdrawn
picture ids, the refusals that still stand, and why each withdrawn request came back
undrawn. -/
public structure Withdrawal where
  ids : Array String := #[]
  standing : Array (String × Diag) := #[]
  said : Array (String × Option String) := #[]
  deriving Repr

/-- How a boundary request came back with no drawing: answered (no tool looked, or the
tool said no), or unfinished. -/
public inductive Undrawn where
  | answered (why : Diag) (said : Option String)
  | unfinished (why : Diag)
  deriving Repr

/-- The refusal an undrawn request stands on when nothing withdraws it. -/
def Undrawn.why : Undrawn → Diag
  | .answered d _ => d
  | .unfinished d => d

/-- One attempt's ending as the withdrawal reads it: a drawing is nothing to withdraw, a
refusal is an answer, and an unfinished attempt none. -/
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

public theorem withdrawStep_unfinished_exact (fallbacks : Array String) (w : Withdrawal)
    (src : String) (d : Diag) :
    withdrawStep fallbacks w (src, .unfinished d) =
      { w with standing := w.standing.push (src, d) } := by
  unfold withdrawStep
  cases fallbacks.find? (Ir.picSrcPrefix ++ · == src) <;> rfl

/-- Withdraw each answered request whose picture the rendered subset draws in part, so the
subset's drawing ships with one W0419; every other refusal stands. -/
public def withdraw (fallbacks : Array String) (undrawn : Array (String × Undrawn)) :
    Withdrawal :=
  undrawn.foldl (withdrawStep fallbacks) {}

/-- Whether `d` is one of withdrawn picture `id`'s losses, read by its structured subject;
a note stands as it is. -/
public def fragmentOf (id : String) (d : Diag) : Bool :=
  d.subject.any (·.startsWith (Ir.picFragmentKey id "")) && d.kind.floor != .inert

/-- Is `d` the line that names withdrawn picture `id` where it stands in a
line of text, which the rendered subset never draws (`Ir.picInlineKey`)? -/
public def inlineOf (id : String) (d : Diag) : Bool :=
  d.subject == some (Ir.picInlineKey id)

/-- The fragments the fold takes; a loss the document's `\allow` accepts stays the
elaborator's line. -/
private def taken (accepted : String → Bool) (id : String) (d : Diag) : Bool :=
  fragmentOf id d && !accepted d.code

/-- Why the boundary drew none of a picture, for its line in a paragraph of its own
(`block`) and in a line of text (`inline`). -/
public structure LineHelp where
  block : String
  inline : Option String := none
  deriving Repr, BEq

/-- A withdrawn picture's: the tool's own last words where it ran, or that
no tool looked (`DriverDiag.withdrawnHelp`). -/
public def withdrawnLine (tool : String) (said : Option String) : LineHelp :=
  { block := DriverDiag.withdrawnHelp tool said
    inline := some (DriverDiag.withdrawnInlineHelp tool said) }

/-- A declined picture's, one the document's `\pictures{ tool = none }` leaves to the
rendered subset. -/
public def declinedLine : LineHelp := { block := DriverDiag.declinedHelp }

/-- The pictures whose refusals the driver folds, each with what its line
says: the withdrawn ones (`Withdrawal.said`) and the declined ones. -/
public def linesOf (tool : String) (w : Withdrawal) (declined : Array String) :
    Array (String × LineHelp) :=
  w.said.map (fun p => (p.1, withdrawnLine tool p.2)) ++ declined.map (·, declinedLine)

/-- One site of a picture as the line that names it: every loss the subset states there,
as clauses, in the record of the site's first fragment, with `help`. -/
public def lineOf (accepted : String → Bool) (help id : String) (ds : Array Diag)
    (first : Diag) : Diag :=
  let here := ((ds.filter fun e => taken accepted id e && e.span == first.span).map
    (·.message)).foldl (fun acc m => if acc.contains m then acc else acc.push m) #[]
  { first with
    kind := .W0419
    message := Diag.say .W0419 .picture
    detail := match here.toList with
      | [] => first.detail
      | one :: [] => first.detail.orElse fun _ => some one
      | many => some (" · ".intercalate many)
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

private def foldOne (accepted : String → Bool) (ds : Array Diag) (p : String × LineHelp) :
    Array Diag :=
  (ds.foldl (placeLine accepted p ds) (#[], #[])).1

/-- Name a picture the rendered subset draws in part once at each place it stands: its
unaccepted fragments fold into one W0419 line per site, and every other diagnostic
stays. -/
public def foldLines (allow : Array String) (allowAll : Bool) (lines : Array (String × LineHelp))
    (ds : Array Diag) : Array Diag :=
  -- premise: pictureRouteChecks — folded refusals are clauses of the picture's line
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
  | cons x _ ih =>
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

/-- The pictures withdrawn from the HTML face alone: those the subset draws in part whose
image source has no converted SVG. -/
public def htmlWithdraw (fallbacks unconverted : Array String) : Array String :=
  fallbacks.filter fun id => unconverted.contains (Ir.picSrcPrefix ++ id)

/-- The reason a faceless boundary picture's HTML entry records; its loss was named where
it happened. -/
public def facelessReason : String :=
  "the boundary picture has no browser face"

/-- A boundary-picture entry the HTML page holds neither a face nor a
reason for: its image would keep the request key as its `src`, which no
resource answers. -/
public def faceless (en : Image.Loaded) : Bool :=
  en.src.startsWith Ir.picSrcPrefix && en.webSvg.isNone && en.webError.isNone

private def markOne (en : Image.Loaded) : Image.Loaded :=
  -- premise: machineLossChecks — the faceless picture's loss is already named
  if faceless en then { en with webError := some facelessReason } else en

/-- Mark every faceless boundary-picture entry with `facelessReason`, so the page shows
its labelled placeholder instead of refusing. -/
public def markFaceless (s : Image.Store) : Image.Store :=
  { s with entries := s.entries.map markOne }

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

public theorem markFaceless_info_exact (s : Image.Store) :
    (markFaceless s).entries.map (fun en => { en with webError := none }) =
      s.entries.map (fun en => { en with webError := none }) := by
  simp only [markFaceless, Array.map_map]
  congr 1
  funext en
  simp only [Function.comp, markOne]
  split <;> rfl

public theorem markFaceless_face_exact (s : Image.Store) (k : Nat) (en : Image.Loaded)
    (h : s.get? k = some en) (hface : faceless en = false) :
    (markFaceless s).get? k = some en := by
  simp only [Image.Store.get?, markFaceless, Array.getElem?_map] at h ⊢
  simp [h, markOne, hface]

/-- What an importer answered for a figure: exact, lossy with each unmet construct named,
or refused with why. -/
public inductive Verdict where
  | exact
  | lossy (losses : Array Gfx.Loss)
  | refused (why : String)
  deriving Repr

/-- What the external converter did for a figure: not asked, drew it, or
left it undrawn — missing, refused by the document, or failed. -/
public inductive ToolState where
  | notAsked
  | drew
  | failed (why : String)
  deriving Repr

/-- A converter's attempt that drew nothing, as the reason the engine's drawing ships: its
own refusal, or a run that did not finish. -/
public def undrawn : PicCache.Outcome → FigureLoss.Unconverted
  | .refused w => .failed w
  | .inconclusive w => .unfinished w
  | .drawn => .unfinished "the converter answered with no drawing"

/-- The words an attempt that drew nothing left. -/
public def undrawnWords : PicCache.Outcome → String
  | .refused w | .inconclusive w => w
  | .drawn => "the converter answered with no drawing"

/-- Whether the document refuses the converter for its figures. -/
public inductive Refusal where
  | none
  | declared
  deriving Repr, BEq

/-- Where a figure's web face comes from: the model's drawing, exact; the
converter's drawing; the model's lossy drawing with every loss named; or
nothing, a placeholder. -/
public inductive Route where
  | native
  | tool
  | nativeWithLoss
  | refused
  deriving Repr, BEq, DecidableEq

/-- Whether a verdict asks the converter at all, under the document's
declaration: an exact import never does, and neither does a document that
refused it. -/
public def Verdict.asksTool (v : Verdict) (decl : Refusal) : Bool :=
  match v, decl with
  | .exact, _ => false
  | _, .declared => false
  | _, .none => true

/-- The one decision a figure's web face is: native where the import is exact; the
converter's drawing where it drew a lossy figure; else the lossy native drawing with its
losses named; a placeholder only where nothing drew. -/
-- premise: figureRouteChecks — tool presence never changes a lossless figure's face
public def route (v : Verdict) (t : ToolState) (decl : Refusal) : Route :=
  match v with
  | .exact => .native
  | .lossy _ =>
    match decl, t with
    | .none, .drew => .tool
    | _, _ => .nativeWithLoss
  | .refused _ =>
    match decl, t with
    | .none, .drew => .tool
    | _, _ => .refused

public theorem route_exact (t : ToolState) (decl : Refusal) : route .exact t decl = .native := by
  unfold route
  rfl

public theorem route_lossy_exact (ls : Array Gfx.Loss) (t : ToolState) (decl : Refusal) :
    route (.lossy ls) t decl = .tool ∨ route (.lossy ls) t decl = .nativeWithLoss := by
  unfold route
  cases decl <;> cases t <;> simp

public theorem route_tool_exact (ls : Array Gfx.Loss) (t : ToolState) (decl : Refusal)
    (h : route (.lossy ls) t decl = .tool) : t = .drew ∧ decl = .none := by
  unfold route at h
  cases decl <;> cases t <;> simp_all

public theorem asksTool_lossless_exact (decl : Refusal) : Verdict.exact.asksTool decl = false := by
  cases decl <;> rfl

public theorem asksTool_declared_exact (v : Verdict) : v.asksTool .declared = false := by
  cases v <;> simp [Verdict.asksTool]

/-- What an SVG figure's route owes, each under its loss's subject: nothing for the
engine's whole drawing, an N0024 note per loss for the converter's, a W0609 per loss for
the engine's lossy drawing. -/
@[expose] public def svgRouteDiags (moving : Bool) (src : String) (why : FigureLoss.Unconverted)
    (losses : Array Gfx.Loss) : Route → Array Diag
  | .native => #[]
  | .tool => FigureLoss.diags (FigureLoss.svgConvertedDiag moving src) losses
  | .nativeWithLoss | .refused => FigureLoss.diags (FigureLoss.svgLostDiag moving src why) losses

public theorem svgRouteDiags_named (moving : Bool) (src : String) (why : FigureLoss.Unconverted)
    (losses : Array Gfx.Loss) (r : Route) (hr : r ≠ .native) (l : Gfx.Loss) (h : l ∈ losses) :
    ∃ d ∈ svgRouteDiags moving src why losses r, d.subject = some (FigureLoss.subject "svg" l) := by
  cases r with
  | native => exact absurd rfl hr
  | tool => exact FigureLoss.svgDiags_named moving src why true losses l h
  | nativeWithLoss | refused => exact FigureLoss.svgDiags_named moving src why false losses l h

public theorem route_losses_exact (losses : Array Gfx.Loss) (t : ToolState) (decl : Refusal) :
    route (if losses.isEmpty then .exact else .lossy losses) t decl = .native ↔
      losses.isEmpty = true := by
  cases h : losses.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, iff_false]
    rcases route_lossy_exact losses t decl with e | e <;> simp [e]
  · simp [route_exact]

end LeanTex.Cli.Boundary
