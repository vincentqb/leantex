module

public import LeanTex.Core.Ir
public import LeanTex.Core.CodeColor
import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab

/-!
Shared listing paint, downstream of the IR and upstream of both backends.
Classification is already in `ListingSpec`; this module never lexes source.
A token paints in its code role (`Kind.role`): the role's weights, and the
colour `CodeColor.resolve` gives the role on the listing's ground. A colour
the document declares or the listing's style states ships as stated, the
contrast report naming a pairing that falls short (`Contrast.docDiags`);
every colour the rule derives adapts to the actual ground.
-/
namespace LeanTex.Core.Listing

open Ir ListingHighlight PygmentsStyle CodeColor

/-- The colour of a token of type `k` on `ground`: its role's. -/
public def paint (pal : Palette) (ground : Color) (style : Option ListingStyle) (k : Kind) :
    Option CodeColor.Paint :=
  (resolve pal ground style).get k.role

/-- **Two types of one role paint alike**, under every palette, ground and
style: a proof hole and a raised not-implemented error, both `error`, ship
one colour by construction. -/
public theorem paint_role_exact (pal : Palette) (ground : Color) (style : Option ListingStyle)
    (k k' : Kind) (h : k.role = k'.role) : paint pal ground style k = paint pal ground style k' := by
  simp only [paint, h]

/-- **A colour a token ships as declared is one the palette declares**, under
the key it ships under. -/
public theorem paint_declared_mem (pal : Palette) (ground : Color) (style : Option ListingStyle)
    (k : Kind) (p : CodeColor.Paint) (h : paint pal ground style k = some p)
    (hd : p.declared = true) :
    ∃ key, p.role = some key ∧ Design.declared? pal key = some p.color :=
  resolve_declared_mem pal ground style k.role p h hd

/-- **Every other colour a token ships is under its role's own key.** -/
public theorem paint_derived_exact (pal : Palette) (ground : Color) (style : Option ListingStyle)
    (k : Kind) (p : CodeColor.Paint) (h : paint pal ground style k = some p)
    (hd : p.declared = false) : p.role = some (Ir.Role.ofCode k.role) :=
  resolve_derived_exact pal ground style k.role p h hd

/-- A colour the rule derives keeps its value where it is legible. On
another ground, the first whole-percent sRGB tint or shade that clears WCAG
AA: the least change on that path, never applied to a colour the document
declares or the listing's style states. The endpoints and percentage scale
are xcolor's `Color.mix`, not new palette constants. -/
public def defaultInk (ground seed : Color) : Color := Id.run do
  if Contrast.contrastMilli seed ground ≥ Contrast.aaText then return seed
  let pole := if Contrast.contrastMilli Color.black ground >
      Contrast.contrastMilli Color.white ground then Color.black else Color.white
  for step in [1:101] do
    let c := seed.mix (100 - step) pole
    if Contrast.contrastMilli c ground ≥ Contrast.aaText then return c
  return pole

/-- The colour a listing's plain text sets in on a ground the listing
declares for itself (minted's `bgcolor`): the code ink the document declares
(`codeink`), as declared; else the text colour around the listing, fitted to
that ground — a pairing the document never stated, the engine's to make
legible, as every colour it derives for the code is. -/
public def groundInk (pal : Palette) (ground inherited : Color) : Color :=
  match Design.declared? pal .codeInk with
  | some c => c
  | none => defaultInk ground inherited

/-- **A declared code ink ships as declared** on the listing's own ground:
the engine fits only the colour it chose. -/
public theorem groundInk_declared_exact (pal : Palette) (ground inherited c : Color)
    (h : Design.declared? pal .codeInk = some c) : groundInk pal ground inherited = c := by
  simp [groundInk, h]

/-- A paint's colour on the actual ground: a colour the document or the
listing's style states as stated, the contrast report naming a pairing that
falls short; a colour the rule derives fitted here once, identically for
PDF, screen and print. -/
private def shipped (bg : Color) (p : CodeColor.Paint) : Color :=
  if p.declared || p.styled then p.color else defaultInk bg p.color

/-- One type's colour on the actual ground. -/
public def ink (pal : Palette) (ground : Option Color) (kind : Kind)
    (style : Option ListingStyle := none) : Option Color :=
  let bg := ground.getD (Design.printPage pal)
  (paint pal bg style kind).map (shipped bg)

/-- A role's weights around a token's text, nested as `\PYG@do` nests
them: underline outside italic outside bold. Text and source punctuation
still convey the language when colours are unavailable (WCAG SC 1.4.1). -/
private def weighted (look : Look) (text : String) : Inline :=
  let body : Inline := .text text
  let body := if look.bold then .styled .bold #[body] else body
  let body := if look.italic then .styled .italic #[body] else body
  if look.underline then .decorated .underline #[body] else body

private theorem weighted_text (look : Look) (text : String) :
    plainTextOne (weighted look text) = text := by
  unfold weighted
  split <;> split <;> split <;> simp [plainTextOne, plainTextList]

/-- What every token of one role ships as: its weights, and its ink and key
on the listing's ground under its overlay. Covering acts on the role's own
colour; an outer colour alone would be overridden by the token's inner
colour during flattening. -/
public structure Brush where
  look : Look
  ink : Option Color
  role : Option ColorRef
  deriving Repr, BEq

/-- A role's brush, from its resolved paint. -/
private def roleBrush (d : Design) (bg : Color) (covered : Option Color)
    (r : ListingHighlight.Role) (p : Option CodeColor.Paint) : Brush :=
  let look : Look := { bold := r.weights.1, italic := r.weights.2 }
  match p with
  | some p =>
    let c := shipped bg p
    let c := if covered.isSome then ({ d with bg := bg }).cover.of c else c
    -- Like `Ir.dimInline`, covered ink is literal: a CSS role would replace
    -- the per-token mixture with the one declared `covered` colour.
    { look, ink := some c, role := if covered.isSome then none else p.role.map .role }
  | none => { look, ink := covered, role := none }

/-- Every role's brush on one ground, each resolved once. -/
public def roleBrushes (pal : Palette) (ground covered : Option Color) (style : Option ListingStyle) :
    RoleTable Brush :=
  let d := Design.ofPalette pal
  let bg := ground.getD d.bg
  let paints := resolve pal bg style
  RoleTable.ofFn fun r => roleBrush d bg covered r (paints.get r)

public def brush (pal : Palette) (ground covered : Option Color) (style : Option ListingStyle)
    (k : Kind) : Brush :=
  (roleBrushes pal ground covered style).get k.role

/-- **Two types of one role ship one brush**, the value both backends paint
from (`brushes`, `paintLine`): one set of weights, one ink, one key. -/
public theorem brush_role_exact (pal : Palette) (ground covered : Option Color)
    (style : Option ListingStyle) (k k' : Kind) (h : k.role = k'.role) :
    brush pal ground covered style k = brush pal ground covered style k' := by
  simp only [brush, h]

/-- A scalar that lays down no ink: white space, the no-break space a
listing's display spelling sets where its spaces must not break included. -/
public def blank (c : Char) : Bool := c.isWhitespace || c == '\u00a0'

/-- Text that lays down no ink in `b`'s weights: blank, not underlined. -/
public def Brush.inkFree (b : Brush) (text : String) : Bool :=
  !b.look.underline && text.all blank

/-- A token's text in its brush. Text that lays down no ink takes no
colour: it paints nothing, and its colour would only cost the artifact a
span or a colour change. -/
public def Brush.inline (b : Brush) (text : String) : Inline :=
  match b.ink with
  | some c => if b.inkFree text then weighted b.look text else .colored c b.role #[weighted b.look text]
  | none => weighted b.look text

/-- A classified source token as ordinary typed inlines. Both backends consume
this projection. -/
public def tokenInline (pal : Palette) (ground covered : Option Color) (t : Token)
    (style : Option ListingStyle := none) : Inline :=
  (brush pal ground covered style t.kind).inline t.text

/-- Painting a classified token conserves its exact scalar sequence, under
every palette, ground, overlay and style. Together with
`Ir.listing_source_exact`, this is the source-preservation premise both
artifact projections consume. -/
public theorem token_inline_source_exact (pal : Palette) (ground covered : Option Color)
    (t : Token) (style : Option ListingStyle := none) :
    plainTextOne (tokenInline pal ground covered t (style := style)) = t.text := by
  unfold tokenInline Brush.inline
  split
  · split
    · exact weighted_text _ _
    · simp [plainTextOne, plainTextList, weighted_text]
  · exact weighted_text _ _

/-- One brush per type the lines hold, for a listing painted on one ground:
each role's resolved once, every type of the role drawing its role's. -/
public def brushes (pal : Palette) (ground covered : Option Color) (style : Option ListingStyle)
    (lines : Array (Array Token)) : Array (Kind × Brush) :=
  let roles := roleBrushes pal ground covered style
  let kinds := lines.foldl (fun acc line => line.foldl (fun acc t =>
    if acc.contains t.kind then acc else acc.push t.kind) acc) #[]
  kinds.map fun k => (k, roles.get k.role)

/-- The weights a brush sets: what decides glyph shapes and advances. -/
public def Brush.weights (b : Brush) : Bool × Bool × Bool :=
  (b.look.bold, b.look.italic, b.look.underline)

/-- The ink `b` ships `text` in: none for text that lays down none. -/
public def Brush.shipsInk (b : Brush) (text : String) : Option (Color × Option ColorRef) :=
  if b.inkFree text then none else b.ink.map (·, b.role)

/-- The brush a type has in `table`, or its own where the table has none. -/
public def brushIn (pal : Palette) (ground covered : Option Color) (style : Option ListingStyle)
    (table : Array (Kind × Brush)) (k : Kind) : Brush :=
  match table.find? (fun e => decide (e.1 = k)) with
  | some (_, b) => b
  | none => brush pal ground covered style k

/-- A brush drawn from the table is the type's own brush, for any lines the
table was drawn from. -/
public theorem brushIn_exact (pal : Palette) (ground covered : Option Color)
    (style : Option ListingStyle) (lines : Array (Array Token)) (k : Kind) :
    brushIn pal ground covered style (brushes pal ground covered style lines) k =
      brush pal ground covered style k := by
  unfold brushIn
  split
  · rename_i k' b found
    have hk : k' = k := by simpa using Array.find?_some found
    obtain ⟨k'', _, he⟩ := Array.mem_map.mp (Array.mem_of_find?_eq_some found)
    cases he
    subst hk
    rfl
  · rfl

/-- Adjacent tokens of one listing line that ship alike: one set of weights
and one ink. White space that lays down no ink shows no ink, so it joins
the run beside it whose weights are its own. -/
public structure Run where
  brush : Brush
  /-- Whether a token that lays down ink stands in the run. Until one does,
  the run ships no colour, as its tokens alone would. -/
  inked : Bool
  tokens : Array Token

/-- The ink a run ships its text in. -/
public def Run.ink (r : Run) : Option (Color × Option ColorRef) :=
  if r.inked then r.brush.ink.map (·, r.brush.role) else none

public def Run.text (r : Run) : String := lineText r.tokens

private def Run.start (b : Brush) (t : Token) : Run :=
  { brush := b, inked := !b.inkFree t.text, tokens := #[t] }

/-- `r` with `t`, painted by `b`, joined, when every scalar then shows as it
would painted alone: one set of weights, and either text that lays down no
ink, a run that has laid none down yet, or no colour on either side. -/
private def Run.join? (r : Run) (b : Brush) (t : Token) : Option Run :=
  if r.brush.weights ≠ b.weights then none
  else if b.inkFree t.text then some { r with tokens := r.tokens.push t }
  else if !r.inked then some { brush := b, inked := true, tokens := r.tokens.push t }
  else if r.brush.ink.isNone && b.ink.isNone then some { r with tokens := r.tokens.push t }
  else none

/-- `Run.join?`'s decision alone: the joined run's brush and inked flag.
Deciding before the run is built leaves `r` unread when its tokens grow,
so they grow in place; building the joined run beside the run that might
not join copied its tokens at every join. -/
private def Run.joins? (r : Run) (b : Brush) (t : Token) : Option (Brush × Bool) :=
  if r.brush.weights ≠ b.weights then none
  else if b.inkFree t.text then some (r.brush, r.inked)
  else if !r.inked then some (b, true)
  else if r.brush.ink.isNone && b.ink.isNone then some (r.brush, r.inked)
  else none

private theorem joins?_join? (r : Run) (b : Brush) (t : Token) :
    (r.joins? b t).map (fun bi => ({ brush := bi.1, inked := bi.2, tokens := r.tokens.push t } : Run)) =
      r.join? b t := by
  unfold Run.joins? Run.join?
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl

private def runsGo (brushOf : Kind → Brush) : List Token → Option Run → Array Run → Array Run
  | [], none, acc => acc
  | [], some r, acc => acc.push r
  | t :: ts, none, acc => runsGo brushOf ts (some (Run.start (brushOf t.kind) t)) acc
  | t :: ts, some r, acc =>
    match r.joins? (brushOf t.kind) t with
    | some (brush, inked) => runsGo brushOf ts (some { brush, inked, tokens := r.tokens.push t }) acc
    | none => runsGo brushOf ts (some (Run.start (brushOf t.kind) t)) (acc.push r)

/-- A listing line as runs of tokens that ship alike, painted from `table`. -/
public def paintLine (pal : Palette) (ground covered : Option Color) (style : Option ListingStyle)
    (table : Array (Kind × Brush)) (line : Array Token) : Array Run :=
  runsGo (brushIn pal ground covered style table) line.toList none #[]

/-- What one scalar shows: its weights, its ink — which a blank scalar that
is not underlined does not show — and the scalar. -/
public def seen (w : Bool × Bool × Bool) (ink : Option (Color × Option ColorRef)) (c : Char) :
    (Bool × Bool × Bool) × Option (Color × Option ColorRef) × Char :=
  (w, if !w.2.2 && blank c then none else ink, c)

/-- What a token painted alone by `b` shows, scalar by scalar. -/
public def tokenShows (b : Brush) (t : Token) :
    List ((Bool × Bool × Bool) × Option (Color × Option ColorRef) × Char) :=
  t.text.toList.map (seen b.weights (b.shipsInk t.text))

/-- What a run shows, scalar by scalar. -/
public def Run.shows (r : Run) :
    List ((Bool × Bool × Bool) × Option (Color × Option ColorRef) × Char) :=
  r.tokens.toList.flatMap fun t => t.text.toList.map (seen r.brush.weights r.ink)

private theorem runsGo_tokens (B : Kind → Brush) (ts : List Token) :
    ∀ (cur : Option Run) (acc : Array Run),
      (runsGo B ts cur acc).toList.flatMap (·.tokens.toList) =
        acc.toList.flatMap (·.tokens.toList) ++ ((cur.map (·.tokens.toList)).getD []) ++ ts := by
  induction ts with
  | nil =>
    intro cur acc
    cases cur <;> simp [runsGo]
  | cons t ts ih =>
    intro cur acc
    cases cur with
    | none => simp [runsGo, ih, Run.start]
    | some r =>
      simp only [runsGo]
      split
      · rw [ih]
        simp
      · rw [ih]
        simp [Run.start]

/-- The runs of a line hold its tokens, in order, each once. -/
public theorem paintLine_tokens_exact (pal : Palette) (ground covered : Option Color)
    (style : Option ListingStyle) (table : Array (Kind × Brush)) (line : Array Token) :
    (paintLine pal ground covered style table line).toList.flatMap (·.tokens.toList) =
      line.toList := by
  simp [paintLine, runsGo_tokens]

/-- A run every token of which shows painted in it as painted alone. -/
private def Run.Good (B : Kind → Brush) (r : Run) : Prop :=
  ∀ t ∈ r.tokens.toList, (B t.kind).weights = r.brush.weights ∧
    t.text.toList.map (seen r.brush.weights r.ink) = tokenShows (B t.kind) t ∧
    (r.inked = false → (B t.kind).inkFree t.text = true)

private theorem inkFree_seen {b : Brush} {t : Token} (h : b.inkFree t.text = true)
    (w : Bool × Bool × Bool) (hw : w.2.2 = b.look.underline)
    (x y : Option (Color × Option ColorRef)) :
    t.text.toList.map (seen w x) = t.text.toList.map (seen w y) := by
  unfold Brush.inkFree at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  apply List.map_congr_left
  intro c hc
  have hws : blank c = true := by
    have := h.2
    rw [String.all_bool_eq] at this
    exact List.all_eq_true.mp this c hc
  simp [seen, hw, h.1, hws]

private theorem start_good (B : Kind → Brush) (t : Token) :
    (Run.start (B t.kind) t).Good B := by
  intro t' ht'
  simp only [Run.start, List.mem_singleton] at ht'
  subst ht'
  refine ⟨rfl, ?_, ?_⟩
  · unfold tokenShows Run.ink Brush.shipsInk
    cases h : (B t'.kind).inkFree t'.text <;> simp [Run.start, h]
  · simp [Run.start]

private theorem join_good (B : Kind → Brush) {r r' : Run} {t : Token} (hr : r.Good B)
    (hj : r.join? (B t.kind) t = some r') : r'.Good B := by
  unfold Run.join? at hj
  split at hj
  · cases hj
  · rename_i hw
    have hw : r.brush.weights = (B t.kind).weights := Classical.not_not.mp hw
    split at hj
    · rename_i hfree
      cases hj
      intro t' ht'
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht'
      rcases ht' with ht' | ht'
      · exact hr t' ht'
      · subst ht'
        refine ⟨hw.symm, ?_, fun _ => hfree⟩
        unfold tokenShows Brush.shipsInk
        rw [hfree, ← hw]
        exact inkFree_seen hfree _ (by simp [Brush.weights] at hw ⊢; exact hw.2.2) _ _
    · rename_i hink
      split at hj
      · rename_i hfresh
        cases hj
        intro t' ht'
        simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht'
        rcases ht' with ht' | ht'
        · obtain ⟨hw', hs, hf⟩ := hr t' ht'
          have hfree : (B t'.kind).inkFree t'.text = true := hf (by simpa using hfresh)
          have hu : r.brush.weights.2.2 = (B t'.kind).look.underline := by
            simp only [Brush.weights, Prod.mk.injEq] at hw' ⊢
            exact hw'.2.2.symm
          refine ⟨by simp [hw', hw], ?_, fun h => by simp at h⟩
          rw [← hs, ← hw]
          exact inkFree_seen hfree _ hu _ _
        · subst ht'
          refine ⟨rfl, ?_, fun h => by simp at h⟩
          unfold tokenShows Brush.shipsInk Run.ink
          simp [hink]
      · rename_i hinked
        split at hj
        · rename_i hnone
          cases hj
          intro t' ht'
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ht'
          rcases ht' with ht' | ht'
          · exact hr t' ht'
          · subst ht'
            have hi : r.inked = true := by simpa using hinked
            simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hnone
            refine ⟨hw.symm, ?_, fun h => by simp [hi] at h⟩
            unfold tokenShows Brush.shipsInk Run.ink
            simp [hink, hi, hnone.1, hnone.2, ← hw]
        · cases hj

private theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun x hx => h x (by simp [hx])]

private theorem good_shows {B : Kind → Brush} {r : Run} (h : r.Good B) :
    r.shows = r.tokens.toList.flatMap (fun t => tokenShows (B t.kind) t) := by
  unfold Run.shows
  exact flatMap_congr fun t ht => (h t ht).2.1

private theorem runsGo_good (B : Kind → Brush) (ts : List Token) :
    ∀ (cur : Option Run) (acc : Array Run), (∀ r ∈ acc.toList, r.Good B) →
      (∀ r, cur = some r → r.Good B) → ∀ r ∈ (runsGo B ts cur acc).toList, r.Good B := by
  induction ts with
  | nil =>
    intro cur acc hacc hcur
    cases cur with
    | none => simpa [runsGo] using hacc
    | some r =>
      simp only [runsGo, Array.toList_push, List.mem_append, List.mem_singleton]
      intro r' hr'
      rcases hr' with hr' | hr'
      · exact hacc r' hr'
      · subst hr'; exact hcur r' rfl
  | cons t ts ih =>
    intro cur acc hacc hcur
    cases cur with
    | none =>
      simp only [runsGo]
      exact ih _ _ hacc fun r hr => by cases hr; exact start_good B t
    | some r =>
      simp only [runsGo]
      split
      · rename_i brush inked hj
        have hj' : r.join? (B t.kind) t = some { brush, inked, tokens := r.tokens.push t } := by
          rw [← joins?_join?, hj]; rfl
        exact ih _ _ hacc fun r'' hr'' => by cases hr''; exact join_good B (hcur r rfl) hj'
      · refine ih _ _ ?_ fun r'' hr'' => by cases hr''; exact start_good B t
        simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        intro r'' hr''
        rcases hr'' with hr'' | hr''
        · exact hacc r'' hr''
        · subst hr''; exact hcur r'' rfl

/-- **A listing line painted as runs shows, scalar by scalar, exactly what
its tokens painted one by one show**: the same scalars in the same order,
each in its type's weights and, wherever it lays down ink, its type's ink.
Only white space that is not underlined may change ink, which it does not
show. -/
public theorem paintLine_shows_exact (pal : Palette) (ground covered : Option Color)
    (style : Option ListingStyle) (lines : Array (Array Token)) (line : Array Token) :
    (paintLine pal ground covered style (brushes pal ground covered style lines) line).toList.flatMap
        Run.shows =
      line.toList.flatMap fun t => tokenShows (brush pal ground covered style t.kind) t := by
  have hgood := runsGo_good (brushIn pal ground covered style (brushes pal ground covered style lines))
    line.toList none #[] (by simp) (by simp)
  have hrw : (paintLine pal ground covered style (brushes pal ground covered style lines) line).toList.flatMap
        Run.shows =
      (paintLine pal ground covered style (brushes pal ground covered style lines) line).toList.flatMap
        fun r => r.tokens.toList.flatMap fun t =>
          tokenShows (brushIn pal ground covered style (brushes pal ground covered style lines) t.kind) t :=
    flatMap_congr fun r hr => good_shows (hgood r hr)
  rw [hrw, ← List.flatMap_assoc, paintLine_tokens_exact]
  simp only [brushIn_exact]

/-- A run's body in its weights and, once inked, its ink, nested as
`\PYG@do` nests them: colour outside underline outside italic outside bold. -/
public def paintRun (r : Run) (body : Array Inline) : Array Inline :=
  let look := r.brush.look
  let body := if look.bold then #[.styled .bold body] else body
  let body := if look.italic then #[.styled .italic body] else body
  let body := if look.underline then #[.decorated .underline body] else body
  match r.ink with
  | some (c, role) => #[.colored c role body]
  | none => body

/-- Painting a run adds no scalar and drops none. -/
public theorem paintRun_text (r : Run) : Conserves plainText (paintRun r) := fun body => by
  simp only [paintRun]
  split <;> split <;> split <;> split <;> simp [plainText, plainTextOne, plainTextList]

/-- Inline code as typed inlines, its tokens painted in runs as a listing
line's are (`paintLine`, `paintRun`) on the ground it stands on. The
elaborator sets them in the mono family and nothing else, so the size,
weight, slant and colour around the code stand: a run with no ink of its
own takes the colour around it, and a role's bold adds to the weight
around it. -/
public def inlineCode (pal : Palette) (ground : Option Color) (style : Option ListingStyle)
    (tokens : Array Token) : Array Inline :=
  (paintLine pal ground none style (brushes pal ground none style #[tokens]) tokens).foldl
    (fun acc r => acc ++ paintRun r #[.text r.text]) #[]

private theorem plainTextList_append (a b : List Inline) :
    plainTextList (a ++ b) = plainTextList a ++ plainTextList b := by
  induction a with
  | nil => simp [plainTextList]
  | cons x rest ih => simp [plainTextList, ih, String.append_assoc]

private theorem textFold_append (s : String) (ts : List Token) :
    ts.foldl (fun acc t => acc ++ t.text) s = s ++ ts.foldl (fun acc t => acc ++ t.text) "" := by
  induction ts generalizing s with
  | nil => simp
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [ih (s ++ t.text), ih ("" ++ t.text)]
    simp [String.append_assoc]

private theorem inlineFold_text (rs : List Run) (acc : Array Inline) :
    plainText (rs.foldl (fun acc r => acc ++ paintRun r #[.text r.text]) acc) =
      (rs.flatMap (·.tokens.toList)).foldl (fun s t => s ++ t.text) (plainText acc) := by
  induction rs generalizing acc with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append]
    rw [ih]
    congr 1
    have hrun := paintRun_text r #[.text r.text]
    simp only [plainText, Array.toList_append, plainTextList_append] at hrun ⊢
    rw [hrun, textFold_append]
    simp [plainTextList, plainTextOne, Run.text, lineText, Array.foldl_toList]

/-- **Inline code ships its source, scalar for scalar**, under every palette,
ground and style: painting adds no scalar and drops none. -/
public theorem inlineCode_source_exact (pal : Palette) (ground : Option Color)
    (style : Option ListingStyle) (tokens : Array Token) :
    plainText (inlineCode pal ground style tokens) = lineText tokens := by
  unfold inlineCode
  rw [← Array.foldl_toList, inlineFold_text, paintLine_tokens_exact]
  simp [plainText, plainTextList, lineText, Array.foldl_toList]

/-- Every colour a listing ships on a ground and the palette does not declare
is text AA there, even where the surrounding frame uses the lower large-text
threshold: every role's, as it ships — what the rule fits, and what the
listing's style states. A colour the palette declares — the document's own, or
a bundle's installed under it — ships as declared and is judged by the contrast
report at its medium's need, a deck's stage asking 3:1. -/
public def contract (pal : Palette) (ground : Option Color) (style : Option ListingStyle := none) :
    Bool :=
  let bg := ground.getD (Design.printPage pal)
  let paints := resolve pal bg style
  ListingHighlight.Role.all.all fun r => match paints.get r with
    | some p => p.declared || decide (Contrast.aaText ≤ Contrast.contrastMilli (shipped bg p) bg)
    | none => true

end LeanTex.Core.Listing
