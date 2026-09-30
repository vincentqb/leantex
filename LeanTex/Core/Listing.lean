import LeanTex.Core.ContrastRatio

/-!
Shared listing paint, downstream of the IR and upstream of both backends.
Classification is already in `ListingSpec`; this module never lexes source.
Colours resolve through `Design.ofPalette`. Native defaults adapt to the
actual ground, while authored roles follow the document contrast realizer.
-/
namespace LeanTex.Core.Listing

open Ir ListingHighlight

/-- The palette role corresponding to a lexical class. -/
def role : Kind → Option String
  | .plain => none
  | .keyword => some "codekeyword"
  | .string => some "codestring"
  | .number => some "codenumber"
  | .comment => some "codecomment"
  | .builtin => some "codebuiltin"
  | .name => some "codename"
  | .operator => some "codeoperator"

/-- Projection of the one resolved palette; ordinary text inherits its ink. -/
def color (d : Design) : Kind → Option Color
  | .plain => none
  | .keyword => some d.listing.keyword
  | .string => some d.listing.string
  | .number => some d.listing.number
  | .comment => some d.listing.comment
  | .builtin => some d.listing.builtin
  | .name => some d.listing.name
  | .operator => some d.listing.operator

/-- Native defaults keep the sourced colour when it is legible. On other
grounds, choose the first whole-percent sRGB tint/shade that clears WCAG AA.
This chooses an undeclared default; it never changes an authored colour.
The endpoints and percentage scale are xcolor's `Color.mix`, not new
palette constants. -/
def defaultInk (ground seed : Color) : Color := Id.run do
  if Contrast.contrastMilli seed ground ≥ Contrast.aaText then return seed
  let pole := if Contrast.contrastMilli Color.black ground >
      Contrast.contrastMilli Color.white ground then Color.black else Color.white
  for step in [1:101] do
    let c := seed.mix (100 - step) pole
    if Contrast.contrastMilli c ground ≥ Contrast.aaText then return c
  return pole

/-- One class's colour on the actual ground. A recorded realization on a local
ground takes precedence over the palette's page colour. Undeclared defaults
are selected here once, identically for PDF, screen and print. -/
def ink (pal : Palette) (ground : Option Color) (kind : Kind)
    (style : ListingStyle := .default) : Option Color := do
  let d := Design.ofPalette pal (style := style)
  let seed ← color d kind
  let name ← role kind
  let bg := ground.getD d.bg
  if (pal.find? name).isSome then
    return ((d.inks.find? fun e =>
      e.role == name && e.declared == seed && e.ground == bg).map (·.ink)).getD seed
  else return defaultInk bg seed

/-- Pygments' DefaultStyle and FriendlyStyle agree on font distinctions for
these native classes: keywords bold, comments italic, other classes regular.
Text and source punctuation still convey the language when colours are
unavailable (WCAG SC 1.4.1). -/
private def fontStyle (kind : Kind) (body : Array Inline) : Array Inline :=
  match kind with
  | .keyword => #[.styled .bold body]
  | .comment => #[.styled .italic body]
  | .plain | .string | .number | .builtin | .name | .operator => body

/-- A classified source token as ordinary typed inlines. Both backends consume
this projection. Covering acts on each token's own colour; an outer colour
alone would be overridden by the token's inner colour during flattening. -/
def tokenInline (pal : Palette) (ground covered : Option Color) (t : Token)
    (style : ListingStyle := .default) : Inline :=
  let body := fontStyle t.kind #[.text t.text]
  match ink pal ground t.kind (style := style) with
  | some c =>
    let c := if covered.isSome then
        ({ Design.ofPalette pal with bg := ground.getD (Design.ofPalette pal).bg }).cover.of c
      else c
    -- Like `Ir.dimInline`, covered ink is literal: a CSS role would replace
    -- the per-token mixture with the one declared `covered` colour.
    .colored c (if covered.isSome then none else role t.kind) body
  | none =>
    match covered with
    | some c => .colored c none body
    | none => .text t.text

/-- Painting a classified token conserves its exact scalar sequence, under
every palette, ground and overlay. Together with `Ir.listing_source_exact`,
this is the source-preservation premise both artifact projections consume. -/
theorem token_inline_source_exact (pal : Palette) (ground covered : Option Color)
    (t : Token) (style : ListingStyle := .default) :
    plainTextOne (tokenInline pal ground covered t (style := style)) = t.text := by
  unfold tokenInline
  split
  · cases t.kind <;> simp [fontStyle, plainTextOne, plainTextList]
  · split
    · cases t.kind <;> simp [fontStyle, plainTextOne, plainTextList]
    · rfl

/-- Every lexical colour a listing can draw is held to text AA, even if the
surrounding frame uses the lower large-text threshold. -/
def contract (pal : Palette) (ground : Option Color) (style : ListingStyle := .default) :
    Bool :=
  ([.keyword, .string, .number, .comment, .builtin, .name, .operator] : List Kind).all
    fun k => match ink pal ground k (style := style) with
      | some c => Contrast.contrastMilli c (ground.getD (Design.ofPalette pal).bg) ≥
          Contrast.aaText
      | none => false

end LeanTex.Core.Listing
