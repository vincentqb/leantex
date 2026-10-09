module

public import LeanTex.Core.Ir
public import LeanTex.Core.PygmentsStyle
import LeanTex.Core.ContrastRatio
import LeanTex.Core.Oklab

/-!
Shared listing paint, downstream of the IR and upstream of both backends.
Classification is already in `ListingSpec`; this module never lexes source.
A token's look is its style's (`PygmentsStyle.Look`, what a lualatex build
with minted ships), with a colour the palette declares (`Design.listing`)
read as that type's declaration. Style colours adapt to the actual ground;
declared ones follow the document contrast realizer.
-/
namespace LeanTex.Core.Listing

open Ir ListingHighlight PygmentsStyle

/-- The resolved table of a shipped style. -/
public def table : ListingStyle → Table
  | .default => defaultTable
  | .friendly => friendlyTable

/-- A token colour and where it comes from: `role` names the palette role
of the type whose declaration set it (the HTML custom property a host page
may override, and the contrast judge's key), `declared` whether the palette
declared it rather than the style. -/
public structure Paint where
  color : Color
  role : Option String
  declared : Bool
  deriving Repr, BEq

private def roleOf (t : Kind) : Option String := (listingRoles.find? (·.2 == t)).map (·.1)

/-- Up from a token's type, the style's colour `source` set at the type
named beside it. -/
private def walkPaint (d : Design) (source : Option (Color × Kind)) : List Kind → Option Paint
  | [] => none
  | t :: up =>
    match d.listing.find? (·.kind == t) with
    | some r => some { color := r.color, role := some r.role, declared := true }
    | none =>
      match source with
      | some (c, from_) =>
        if from_ == t then some { color := c, role := roleOf t, declared := false }
        else walkPaint d source up
      | none => walkPaint d source up

/-- The colour of a token of type `k`. Walking up from `k` to the type
whose declaration set the style's colour, the first type the palette
declares a colour for wins: a declaration on a type is inherited by every
descendant that declares no colour of its own, as in the style itself. -/
public def paint (d : Design) (style : ListingStyle) (k : Kind) : Option Paint :=
  walkPaint d ((table style).lookOf k).color k.chain.reverse

private theorem walkPaint_declared_mem (d : Design) (source : Option (Color × Kind))
    (ks : List Kind) (p : Paint) (h : walkPaint d source ks = some p) (hd : p.declared = true) :
    ∃ r ∈ d.listing, r.color = p.color ∧ some r.role = p.role := by
  induction ks with
  | nil => simp [walkPaint] at h
  | cons t up ih =>
    unfold walkPaint at h
    split at h
    · rename_i r hr
      cases h
      exact ⟨r, Array.mem_of_find?_eq_some hr, rfl, rfl⟩
    · split at h
      · split at h
        · cases h; simp at hd
        · exact ih h
      · exact ih h

private theorem walkPaint_style_exact (d : Design) (source : Option (Color × Kind))
    (ks : List Kind) (p : Paint) (h : walkPaint d source ks = some p) (hd : p.declared = false) :
    source.map (·.1) = some p.color := by
  induction ks with
  | nil => simp [walkPaint] at h
  | cons t up ih =>
    unfold walkPaint at h
    split at h
    · cases h; simp at hd
    · split at h
      · split at h
        · cases h; simp
        · exact ih h
      · exact ih h

/-- **A colour the palette declares is the only colour a declared paint
carries**: no listing colour is invented between the palette and the page. -/
public theorem paint_declared_mem (d : Design) (style : ListingStyle) (k : Kind) (p : Paint)
    (h : paint d style k = some p) (hd : p.declared = true) :
    ∃ r ∈ d.listing, r.color = p.color ∧ some r.role = p.role :=
  walkPaint_declared_mem d _ _ p h hd

/-- **Every other paint is the style's own colour for the type**, exactly
as the style table composes it. -/
public theorem paint_style_exact (d : Design) (style : ListingStyle) (k : Kind) (p : Paint)
    (h : paint d style k = some p) (hd : p.declared = false) :
    ((table style).lookOf k).color.map (·.1) = some p.color :=
  walkPaint_style_exact d _ _ p h hd

/-- Style colours keep their value when it is legible. On other grounds,
choose the first whole-percent sRGB tint/shade that clears WCAG AA: the
least change on that path, never applied to a colour the document declared.
The endpoints and percentage scale are xcolor's `Color.mix`, not new
palette constants. -/
public def defaultInk (ground seed : Color) : Color := Id.run do
  if Contrast.contrastMilli seed ground ≥ Contrast.aaText then return seed
  let pole := if Contrast.contrastMilli Color.black ground >
      Contrast.contrastMilli Color.white ground then Color.black else Color.white
  for step in [1:101] do
    let c := seed.mix (100 - step) pole
    if Contrast.contrastMilli c ground ≥ Contrast.aaText then return c
  return pole

/-- One type's colour on the actual ground. A recorded realization on a local
ground takes precedence over the palette's page colour. Style colours are
adapted here once, identically for PDF, screen and print. -/
public def ink (pal : Palette) (ground : Option Color) (kind : Kind)
    (style : ListingStyle := .default) : Option Color := do
  let d := Design.ofPalette pal
  let p ← paint d style kind
  let bg := ground.getD d.bg
  if p.declared then
    return ((d.inks.find? fun e =>
      some e.role == p.role && e.declared == p.color && e.ground == bg).map (·.ink)).getD p.color
  else return defaultInk bg p.color

/-- The style's weights around a token's text, nested as `\PYG@do` nests
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

/-- A classified source token as ordinary typed inlines. Both backends consume
this projection. Covering acts on each token's own colour; an outer colour
alone would be overridden by the token's inner colour during flattening. -/
public def tokenInline (pal : Palette) (ground covered : Option Color) (t : Token)
    (style : ListingStyle := .default) : Inline :=
  let body := weighted ((table style).lookOf t.kind) t.text
  match ink pal ground t.kind (style := style) with
  | some c =>
    let c := if covered.isSome then
        ({ Design.ofPalette pal with bg := ground.getD (Design.ofPalette pal).bg }).cover.of c
      else c
    let role := (paint (Design.ofPalette pal) style t.kind).bind (·.role)
    -- Like `Ir.dimInline`, covered ink is literal: a CSS role would replace
    -- the per-token mixture with the one declared `covered` colour.
    .colored c (if covered.isSome then none else role) #[body]
  | none =>
    match covered with
    | some c => .colored c none #[body]
    | none => body

/-- Painting a classified token conserves its exact scalar sequence, under
every palette, ground, overlay and style. Together with
`Ir.listing_source_exact`, this is the source-preservation premise both
artifact projections consume. -/
public theorem token_inline_source_exact (pal : Palette) (ground covered : Option Color)
    (t : Token) (style : ListingStyle := .default) :
    plainTextOne (tokenInline pal ground covered t (style := style)) = t.text := by
  unfold tokenInline
  split
  · simp [plainTextOne, plainTextList, weighted_text]
  · split
    · simp [plainTextOne, plainTextList, weighted_text]
    · exact weighted_text _ _

/-- The box the style draws around a token of type `k`, which the typed
inlines cannot carry: the elaborator names it (W0397). -/
public def box? (style : ListingStyle) (k : Kind) : Option Box :=
  ((table style).lookOf k).box

/-- Every colour a listing can draw is held to text AA, even if the
surrounding frame uses the lower large-text threshold: every type the style
resolves and every type a palette role declares. -/
public def contract (pal : Palette) (ground : Option Color) (style : ListingStyle := .default) :
    Bool :=
  ((table style).kinds ++ listingRoles.map (·.2)).all fun k =>
    match ink pal ground k (style := style) with
    | some c => Contrast.contrastMilli c (ground.getD (Design.ofPalette pal).bg) ≥
        Contrast.aaText
    | none => true

end LeanTex.Core.Listing
