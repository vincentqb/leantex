module

public import LeanTex.Core.Html
public import LeanTex.Core.Blank
public import LeanTex.Core.HtmlResource
public import LeanTex.Core.MathMl
public import LeanTex.Core.Ir
public import LeanTex.Core.Dim
public import LeanTex.Core.Contrast
public import LeanTex.Core.Font
public import LeanTex.Core.GfxSvg
public import LeanTex.Core.GfxPicture
public import LeanTex.Core.FigureSvg
import LeanTex.Core.Listing
import LeanTex.Core.ContrastSolve
import LeanTex.Core.TitleTemplate
import LeanTex.Core.ListMark
import Std.Http.Data.URI.Encoding

namespace LeanTex.Core.HtmlDoc

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Dim LeanTex.Core.Html

/-- How much CSS to emit, and whose class names to use. -/
public inductive CssMode where
  /-- The engine's token-driven stylesheet, inlined. -/
  | own
  /-- Bulma's class vocabulary with the tokens bound to `--bulma-*`, styled by the document's
  declared framework stylesheet. -/
  | bulma
  /-- Semantic markup only, styled by the document's declared stylesheet and its own rules. -/
  | none
  deriving Repr, BEq

/-- The unit a table length is spelled in on screen: the deck's stage height or the class size. -/
public inductive LengthBasis where
  | stage (height : Sp)
  | classSize (size : Sp)
  deriving Repr, BEq, Inhabited

/-- Each code role's colour, and the palette role it reads, in each shipped scheme. -/
public abbrev CodeRoot := List (Ir.Scheme × List (Ir.Role × Option (Ir.Color × Option Ir.Role)))

public structure Config where
  css : CssMode := .own
  /-- The document's main locale, in which generated furniture is worded. -/
  locale : Locale := Locale.en
  /-- The script of the client-side math renderer the run declares, shipped inline. -/
  mathRenderer : Option String := none
  styles : Styles := {}
  /-- The document's loaded images, whose intrinsic sizes `<img>` carries. -/
  imgs : Image.Store := {}
  /-- The markdown twin's relative URL, linked from the head as the alternate representation. -/
  mdHref : Option String := none
  /-- The palette in force at this point of the block walk. -/
  pal : Ir.Palette := {}
  /-- The document's own palette, the one epoch 0 paints. -/
  docPal : Ir.Palette := {}
  /-- The colour schemes the page ships, each with its frame; empty outside the engine's
  stylesheet. -/
  frames : List Ir.SchemeFrame := []
  /-- The palette in force as each shipped scheme ships it, in `frames`' order. -/
  views : List Ir.Palette := []
  /-- Every palette the page holds, beside its view in each shipped scheme. -/
  paletteViews : List (Ir.Palette × List Ir.Palette) := []
  /-- The screen scheme the page's `:root` holds. -/
  floor : Ir.Scheme := .light
  /-- The code roles' colours the page's `:root` states for a listing on the page's code ground. -/
  codeRoot : CodeRoot := []
  /-- Ground, text and code-role colours per shipped scheme for a listing that declares nothing. -/
  codePaints : List (Ir.Scheme × Ir.Color × Ir.Color ×
    List (Ir.Role × Option (Ir.Color × Option Ir.Role))) := []
  /-- The page, ink and code ground per shipped scheme, as the palette in force resolves them. -/
  boxTexts : List (Ir.Role × List (Ir.Scheme × Option String)) := []
  /-- A listing's local ground, the one the PDF paints. -/
  listingGround : Option Ir.Color := none
  listingFg : Option Ir.Color := none
  /-- The roles the page's stylesheet declares. -/
  cssRoles : List Ir.Role := []
  /-- Whether the page can declare each role's property, by constructor index. -/
  declarable : Array Bool := #[]
  /-- A painted body's ground, kept across palette declarations. -/
  bodyGround : Option Ir.Color := none
  bodyInk : Option (Ir.ColorRef × Ir.Color) := none
  tokens : Ir.Tokens := {}
  /-- Whether the page is the paged deck, whose frames realize their vertical distribution. -/
  deck : Bool := false
  chromeAllowed : Bool := false
  /-- The deck's frame-alignment keys, which set the glue its spacers grow by. -/
  frameKeys : Ir.FrameKeys := .beamer
  /-- Whether a fill here grows nothing on the deck's stage. -/
  fillsInert : Bool := false
  /-- The frame's overlay step count, which bounds its union selectors. -/
  overlaySteps : Nat := 1
  /-- The document's page geometry, which deck image sizes are shares of. -/
  page : Ir.PageSpec := {}
  lengthBasis : LengthBasis := .classSize Ir.baseFontSize
  /-- The step a narrowing table sets at and whether it overhangs, by the page's decision. -/
  tableFit : Sp → Array Ir.ColSpec → Bool → Bool → Array (Array (Array Inline)) →
    Array Ir.ColSpan → Option String × Bool := fun _ _ _ _ _ _ => (none, false)
  /-- The document's list lineage, which list and quotation levels indent by. -/
  lists : Ir.ListLineage := .sizeFile
  /-- The list and quotation levels around this content. -/
  listDepth : Nat := 0
  inset : Sp := 0
  /-- The local measurement context; `none` reads the document's text area. -/
  measures : Option MeasureValues := none
  /-- Custom-property redefinitions the following siblings carry on their style attribute. -/
  epochStyle : String := ""
  /-- Concrete paint for ordinary flow after a palette declaration. -/
  epochPaint : String := ""
  /-- Whether the accumulated palette diff changes the page ground. -/
  epochGround : Bool := false
  /-- The document's faces, when the artifact ships them as `@font-face` data URLs. -/
  fonts : Option Font.FontSet := none
  /-- The declared stylesheet's spelling and captured text. -/
  stylesheet : Option (String × String) := none
  /-- Captured icon bytes, keyed by the document's exact favicon spelling. -/
  favicon : Option (String × HtmlResource.Embedded) := none
  /-- Inside a declared title slot, whose font template already wraps the title. -/
  slotTitle : Bool := false
  /-- How a picture label's content measures, as layout places labels. -/
  labelMetric : Ir.Pic.LabelMetric := fun _ _ => {}
  /-- The footline band's box on frame `n`, as the page sets it. -/
  footBox : Nat → Array Ir.BandSlot → Option (Sp × Sp) := fun _ _ => none
  /-- Where a rule reaching by a block title's lines stands in its header. -/
  blockTitleRule : Ir.TitledKind → Ir.BlockReach → Option Ir.BlockTitlePlace := fun _ _ => none
  /-- The depth below the baseline of the line box a block's last line stands in. -/
  blockLastBelow : Option Ir.Block → Option Int := fun _ => none
  /-- Measured cancellation in the surrounding text style. -/
  cancelMetric : MeasureValues → Array Ir.Style → Math.MathStyle → Math.CancelSpec →
    Math.MList → Math.MList → Option Math.CancelMetric := fun _ _ _ _ _ _ => none
  /-- The same run's font unit for explicitly sized math lengths. -/
  mathEm : MeasureValues → Array Ir.Style → Math.MathStyle → Option Int := fun _ _ _ => none
  /-- The ambient text em that text-sourced math alphabets keep. -/
  mathTextEm : MeasureValues → Array Ir.Style → Math.MathStyle → Option Int := fun _ _ _ => none
  /-- The ordered style history the native resolver folds. -/
  mathStyles : Array Ir.Style := #[]
  /-- Inside a fill row's group, where a text-width fraction is a fraction of the row. -/
  inFillRow : Bool := false

/-- The current text area: the local context, else the page's. -/
public def Config.measureValues (cfg : Config) : MeasureValues :=
  cfg.measures.getD (MeasureValues.horizontal
    (cfg.page.width - 2 * cfg.page.hmargin) (cfg.page.height - 2 * cfg.page.vmargin))

/-- One list or quotation level deeper: the lineage's left margin, else the page's own 1.5 em
(`Layout.listIndentFor`), off the measure's start, and for a quotation off its end; a declared
`\leftmargin⟨n⟩` is not read. -/
public def Config.deeper (cfg : Config) (both : Bool) : Config :=
  let lv := cfg.listDepth + 1
  let lm := (Ir.leftMargin cfg.lists cfg.page.fontSize lv).getD (cfg.page.fontSize * 3 / 2)
  { cfg with listDepth := lv, inset := cfg.inset + (if both then 2 * lm else lm) }

/-- Enter a box of the given width, at list depth zero. -/
public def Config.atMeasure (cfg : Config) (width : Sp) : Config :=
  { cfg with measures := some (MeasureValues.horizontal width cfg.measureValues.textHeight)
             listDepth := 0, inset := 0 }

@[expose] public def cssColor (c : Color) : String := c.css

public def roleClass (n : String) : String := "u-" ++ n

private theorem roleClass_toList (n : String) :
    (roleClass n).toList = 'u' :: '-' :: n.toList := by
  have h : "u-".toList = ['u', '-'] := by decide
  simp [roleClass, String.toList_append, h]

public theorem roleClass_inj (a b : String) (h : roleClass a = roleClass b) : a = b := by
  have hl := congrArg String.toList h
  rw [roleClass_toList, roleClass_toList] at hl
  simp only [List.cons.injEq, true_and] at hl
  exact String.ext hl

public def raggedClass : Ir.FlushSide → String
  | .left => "ragged"
  | .right => "ragged-right"

/-- The margins a block-level box takes on its scope's side. -/
public def boxMargins : Ir.HAlign → String × String
  | .left => ("0", "auto")
  | .center => ("auto", "auto")
  | .right => ("auto", "0")

/-- The track placement a lone box's grid row takes on its scope's side. -/
public def boxJustify : Ir.HAlign → String
  | .left => "start"
  | .center => "center"
  | .right => "end"

public theorem box_margins_agree (h : Ir.HAlign) :
    ((boxMargins h).1 = "auto" ↔ 0 < h.slackHalves) ∧
      ((boxMargins h).2 = "auto" ↔ h.slackHalves < 2) := by
  cases h <;> decide

/-- An alignment scope's rule: its `text-align` and box placement, both inherited. -/
private def alignScopeRule (cls : String) (h : Ir.HAlign) : String :=
  "." ++ cls ++ " { text-align: " ++ h.align ++ "; --ltx-box-left: " ++ (boxMargins h).1 ++
    "; --ltx-box-right: " ++ (boxMargins h).2 ++ "; --ltx-box-justify: " ++ boxJustify h ++
    "; }\n"

public def raggedRule (s : Ir.FlushSide) : String := alignScopeRule (raggedClass s) s.halign

private theorem raggedRule_projects (s : Ir.FlushSide) :
    raggedRule s = alignScopeRule (raggedClass s) s.halign ∧ s.halign.align = s.align := by
  cases s <;> exact ⟨rfl, rfl⟩

/-- Every class token the engine itself puts on an element. -/
public def engineClasses : List String :=
  ["abstract", "b", "i", "mono", "sc", "em", "sans", "normal", "rm", "md", "up", "see-through",
   "section-number", "display", "equation", "eqnum",
   "band-left", "band-right", "booktabs", "bt-center", "bt-cmid", "bt-heavy-above", "bt-left",
   "bt-light-above", "bt-nowrap", "bt-overhang", "bt-right", "cell-measure", "centered", "ragged", "ragged-right", "column", "columns", "content",
   "deck-progress", "entry",
   "entry-pair", "entry-row", "entry-rows", "fill", "float", "frame-body-end",
   "frame-body-start", "group", "icon",
   "math", "math-display", "nopadl", "nopadr", "note", "picture", "progress",
   "reveal-scroll", "ruled", "section-page", "separator", "slide",
   "slide-foot", "slide-logo", "slide-track", "slides", "snap", "spaced",
   "standout", "step", "table-float", "tcolorbox", "tcolorbox-body", "titlebar", "verbatim-list", "vskip",
   "alt-pair", "alt-alike", "frame-body-tail", "frame-flow-end", "frame-flow-start",
   "fill-before", "squeeze",
   "tok", "tok-long"] ++
  Ir.sizeScale.map (fun p => "size-" ++ p.1) ++ Ir.sizeScale.map (fun p => "lead-" ++ p.1)

private theorem engineClasses_no_u_prefix :
    (engineClasses.all fun c => decide (c.toList.take 2 ≠ ['u', '-'])) = true := by
  decide

public theorem roleClass_engine_disjoint (n c : String) (hc : c ∈ engineClasses) :
    roleClass n ≠ c := by
  intro h
  have hall := List.all_eq_true.mp engineClasses_no_u_prefix c hc
  simp only [decide_eq_true_eq] at hall
  apply hall
  rw [← h, roleClass_toList]
  rfl

public theorem roleClass_single_token (n : String)
    (hn : (n.toList.all fun c => c.isAlpha || c == '@') = true) :
    ((roleClass n).toList.all fun c =>
      !(c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '"' || c == '\'')) = true := by
  rw [roleClass_toList]
  simp only [List.all_cons, Bool.and_eq_true, List.all_eq_true] at hn ⊢
  refine ⟨by decide, by decide, fun c hc => ?_⟩
  have h := hn c hc
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨fun h' => ?_, fun h' => ?_⟩, fun h' => ?_⟩, fun h' => ?_⟩,
    fun h' => ?_⟩, fun h' => ?_⟩ <;> (subst h'; exact absurd h (by decide))

/-- Thousandths as a decimal numeral. -/
private def decMilli (n : Int) : String :=
  let sign := if n < 0 then "-" else ""
  let a := n.natAbs
  let frac := toString (a % 1000)
  let frac := "".pushn '0' (3 - frac.length) ++ frac
  let frac := String.ofList (frac.toList.reverse.dropWhile (· == '0')).reverse
  s!"{sign}{a / 1000}" ++ (if frac.isEmpty then "" else "." ++ frac)

/-- A length in CSS: its absolute part spelled by `absolute`, its `em` and `ex` kept as CSS units,
and zero as `0pt` so it composes in `calc()`. -/
public def cssLengthIn (absolute : Sp → String) (l : Length) : String :=
  let parts :=
    (if l.sp != 0 then [absolute l.sp] else []) ++
    (if l.em != 0 then [s!"{decMilli l.em}em"] else []) ++
    (if l.ex != 0 then [s!"{decMilli l.ex}ex"] else [])
  match parts with
  | [] => "0pt"
  | [one] => one
  | many => "calc(" ++ String.intercalate " + " many ++ ")"

/-- A length in CSS, its absolute part in points. -/
public def cssLength (l : Length) : String :=
  cssLengthIn (fun sp => s!"{sp.toPtString}pt") l

public theorem cssLength_zero_exact : cssLength ({} : Length) = "0pt" := by
  simp [cssLength, cssLengthIn]

/-- A length's share of the deck stage, in thousandths of a percent. -/
public def deckStageMilli (x stage : Int) : Int :=
  x * 100000 / stage

/-- A length on a deck's stage: its absolute part as a share of the stage height, in `vh`. -/
public def stageLengthCss (stage : Sp) (l : Length) : String :=
  cssLengthIn (fun sp => s!"{decMilli (deckStageMilli sp stage)}vh") l

/-- A length's share of the class size, in thousandths. -/
public def classShareMilli (x size : Int) : Int :=
  x * 1000 / size

/-- A length on a page whose body text is 1 rem: its absolute part as a share of the class size. -/
public def classLengthCss (size : Sp) (l : Length) : String :=
  if size ≤ 0 then cssLength l
  else cssLengthIn (fun sp => s!"{decMilli (classShareMilli sp size)}rem") l

/-- The `:root` property naming a colour's text in each shipped scheme, behind the `--ltx--`
prefix. -/
public def schemeVar (texts : List (Ir.Scheme × Option String)) : String :=
  let parts := texts.map fun (_, x) => match x with
    | some t => (t.drop 1).toString
    | none => "none"
  "--ltx--" ++ "-".intercalate (parts.zipIdx.map fun (p, i) =>
    match (parts.take i).idxOf? p with
    | some j => if j < 10 then toString j else p
    | none => p)

/-- The texts a `schemeVar` name spells, in the page's scheme order. -/
public def schemeVarTexts (schemes : List Ir.Scheme) (name : String) :
    Option (List (Ir.Scheme × Option String)) := do
  guard (name.startsWith "--ltx--")
  let parts := ((name.drop 7).toString).splitOn "-"
  guard (parts.length == schemes.length)
  let texts ← parts.foldlM (fun (acc : Array (Option String)) p =>
    if p == "none" then some (acc.push none)
    else if p.length == 1 && p.all Char.isDigit then acc[p.toNat!]?.map acc.push
    else if p.length == 6 && p.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
      some (acc.push (some ("#" ++ p)))
    else none) #[]
  return schemes.zip texts.toList

/-- A colour's texts across the shipped schemes as one declaration states them. -/
public def schemeValue (texts colours : List (Ir.Scheme × Option String)) (floor : Ir.Scheme) :
    String :=
  let f := (texts.lookup floor).join
  if texts.all (·.2 == f) then f.getD "initial"
  else if colours.all (·.2.all (·.startsWith "#")) then s!"var({schemeVar colours})"
  else f.getD "initial"

/-- A literal colour as the page ships it in every shipped scheme. -/
public def Config.literal (cfg : Config) (c : Ir.Color) : String :=
  if cfg.frames.isEmpty then cssColor c else
  let texts := cfg.frames.map fun f => (f.scheme, some (cssColor (Ir.Design.literalIn f c)))
  schemeValue texts texts cfg.floor

/-- The math face's cancel-mark metrics in thousandths of an em, or TeX's defaults without faces. -/
public def mathMarks (cfg : Config) : MathMl.Marks :=
  let marks : MathMl.Marks := {
    alignSep := if cfg.deck then stageLengthCss cfg.page.height (Dim.Length.ofSp Math.minAlignSep)
      else classLengthCss cfg.page.fontSize (Dim.Length.ofSp Math.minAlignSep)
    metric := cfg.cancelMetric cfg.measureValues cfg.mathStyles
    em := cfg.mathEm cfg.measureValues cfg.mathStyles
    textEm := cfg.mathTextEm cfg.measureValues cfg.mathStyles
    literal := cfg.literal }
  match cfg.fonts.bind fun fs => fs.math.bind (fs.fonts[·]?) with
  | some f =>
    match f.math with
    | some mc =>
      let per (v : Int) : Nat := (v * 1000 / (max 1 f.unitsPerEm : Int)).toNat
      { marks with rule := per mc.overbarRuleThickness, gap := per mc.overbarVerticalGap
                   scales := mc.scales }
    | none => marks
  | none => marks

public def lengthBasisOf (doc : Doc) : LengthBasis :=
  if doc.docClass.record.model == .frame then .stage doc.page.height
  else .classSize doc.page.fontSize

public def tableLengthCss : LengthBasis → Length → String
  | .stage h, l => stageLengthCss h l
  | .classSize size, l => classLengthCss size l

public def tokenCss (basis : LengthBasis) (name : String) (l : Length) : String :=
  if (Ir.tableLengths.lookup name).isSome then tableLengthCss basis l else cssLength l

/-- A table length's fallback: the default the page sets an undeclared table by. -/
@[expose] public def tableLengthFallback (doc : Doc) (name : String) : String :=
  tableLengthCss (lengthBasisOf doc)
    (Length.ofSp (doc.preambleFace.resolve (Ir.tableLengthDefault name)))

public def cellSideClass (h : Ir.HAlign) : String := "bt-" ++ h.align

/-- A side class's `text-align` rule, at a table cell's own specificity. -/
public def cellSideRule (h : Ir.HAlign) : String :=
  "table.booktabs td." ++ cellSideClass h ++ ", table.booktabs th." ++ cellSideClass h ++
    " { text-align: " ++ h.align ++ "; }\n"

/-- A token's custom property, when its name needs no CSS escape. -/
public def tokenVar? (n : String) : Option String :=
  if !n.isEmpty && n.all (fun c => c.isAlphanum || c == '-' || c == '_') then some ("--" ++ n)
  else none

/-- A sourced length in CSS: its declared custom property with the resolved length as fallback,
or the length alone where it has none. -/
public def cssSourced (g : Ir.Sourced SymGlue) : String :=
  match g.token.bind tokenVar? with
  | some v => s!"var({v}, {cssLength g.value.width})"
  | none => cssLength g.value.width

public theorem cssSourced_projects (g : Ir.Sourced SymGlue) (n : String)
    (h : g.token = some n) (hn : tokenVar? n = some ("--" ++ n)) :
    cssSourced g = s!"var(--{n}, {cssLength g.value.width})" := by
  simp only [cssSourced, h, Option.bind_some, hn]
  simp only [toString, String.append_assoc]
  rfl

public theorem cssSourced_bare (g : SymGlue) :
    cssSourced (Ir.Sourced.bare g) = cssLength g.width := by
  simp [cssSourced, Ir.Sourced.bare]

/-- The content measure: text width over the base font size, in `em`. -/
public def measureEm (page : PageSpec) : String :=
  let textWidth := page.width - 2 * page.hmargin
  s!"{decMilli (textWidth * 1000 / page.fontSize)}em"

/-- Removes the selector's transition under `prefers-reduced-motion: reduce`. -/
public def reducedMotionGuard (sel : String) : String :=
  s!"@media (prefers-reduced-motion: reduce) \{ {sel} \{ transition: none; } }\n"

/-- A declared motion's transition, followed by its own reduced-motion guard. -/
public def motionCss (sel : String) (ms : Nat) : String :=
  s!"{sel} \{ transition: color {ms}ms, outline-color {ms}ms; }\n" ++
    reducedMotionGuard sel

public theorem motionCss_guarded (sel : String) (ms : Nat) :
    ∃ rule, motionCss sel ms = rule ++ reducedMotionGuard sel :=
  ⟨_, rfl⟩

/-- The reveal's reduced-motion guard, which leaves the element visible. -/
public def revealMotionGuard : String :=
  "@media (prefers-reduced-motion: reduce) \
{ .reveal-scroll { animation: none; } }\n"

/-- The scroll-driven reveal; without scroll-driven animations the element stays visible. -/
public def revealCss : String :=
  "@keyframes ltx-reveal { from { opacity: 0; visibility: hidden } \
to { opacity: 1; visibility: visible } }\n" ++
  "@supports (animation-timeline: scroll()) { .reveal-scroll { \
animation: ltx-reveal linear both; animation-timeline: scroll(); \
animation-range: 0 var(--reveal-range, 100vh); } }\n" ++
  revealMotionGuard

public theorem revealCss_guarded : ∃ rule, revealCss = rule ++ revealMotionGuard :=
  ⟨_, rfl⟩


/-- A declared marker as a `::marker` rule: its text and its declarations. -/
public structure MarkerCss where
  text : String
  decls : Array String := #[]
  deriving Repr, BEq

/-- Font declarations for a style, shared by markers and listings: bold is 600, the level-2 list
dash's weight, and an unknown size gives none. -/
private def fontStyleDecls (scale : List (String × Nat)) (st : Style)
    (lengthCss : Affine Measure → String := Ir.Track.contextCss) :
    Option (Array String) :=
  match st with
  | .bold => some #["font-weight: 600;"]
  | .italic => some #["font-style: italic;"]
  | .emph => some #["font-style: italic;"]
  | .mono => some #["font-family: var(--font-mono);"]
  | .sans => some #["font-family: var(--font-sans);"]
  | .smallcaps => some #["font-variant-caps: all-small-caps;"]
  | .roman => some #["font-family: var(--font-body);"]
  | .medium => some #["font-weight: 400;"]
  | .series w => some #[s!"font-weight: {w.css};"]
  | .upright => some #["font-style: normal;", "font-variant-caps: normal;"]
  | .family s => some #[s!"font-family: var(--font-{s});"]
  | .normal => some #[]
  | .size name => (scale.lookup name).map fun k =>
      #[s!"font-size: {decMilli k}em;"]
  | .fontSize size leading => some #[
      s!"font-size: {lengthCss size};",
      s!"line-height: {lengthCss leading};"]
  | .lang _ => some #[]

private def markerColorDecl (c : Ir.Color) (name : Option Ir.ColorRef) : String :=
  match name with
  | some n => s!"color: var({n.property}, {cssColor c});"
  | none => s!"color: {cssColor c};"

/-- The colour a `color: #rrggbb;` declaration spells. -/
private def literalColorDecl? (d : String) : Option Ir.Color := do
  guard (d.startsWith "color: #" && d.endsWith ";" && d.length == 15)
  let hex := ((d.drop 8).take 6).toString.toList
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let ds ← hex.mapM digit
  let byte (i : Nat) : UInt8 := (16 * ds.getD i 0 + ds.getD (i + 1) 0).toUInt8
  return Ir.Color.ofHtml (byte 0) (byte 2) (byte 4)

mutual

/-- The plain text of a marker whose every element is text; unlike the text census it stops at a
semantic wrapper. -/
private def markerTextOne (acc : String) : Inline → Option String
  | .text s => some (acc ++ s)
  | .math _ _ => none
  | .formula _ _ _ => none
  | .styled _ _ => none
  | .colored _ _ _ => none
  | .located _ body => markerTextInto acc body.toList
  | .role _ _ => none
  | .link _ _ => none
  | .decorated _ _ => none
  | .fill => none
  | .hspace _ _ => none
  | .rule _ _ _ => none
  | .strut _ => none
  | .italicCorr _ => some acc
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .onSteps _ _ => none
  | .altSteps _ _ _ => none
  | .image _ _ _ => none
  -- a `content` string cannot carry an icon's accessible name
  | .icon _ _ => none
  | .label _ => none
  | .ref _ _ _ _ => none
  | .cite _ _ => none
  | .footnote _ _ => none

private def markerTextInto (acc : String) : List Inline → Option String
  | [] => some acc
  | x :: rest =>
    (markerTextOne acc x).bind fun next => markerTextInto next rest

end

mutual

/-- One marker element as `::marker` CSS: a style wrapper over the whole content, or plain text;
`none` when inexpressible. -/
private def markerCssOne (scale : List (String × Nat)) (decls : Array String) :
    Inline → Option MarkerCss
  | .text s => some { text := s, decls := decls }
  | .styled st body =>
    match fontStyleDecls scale st with
    | some ds => markerCssList scale (decls ++ ds) body.toList
    | _ => none
  | .colored c name body =>
    markerCssList scale (decls.push (markerColorDecl c name)) body.toList
  | .located _ body => markerCssList scale decls body.toList
  | .role _ body => markerCssList scale decls body.toList
  | .math _ _ => none
  | .formula _ _ _ => none
  | .link _ _ => none
  | .decorated _ _ => none
  | .fill => none
  | .hspace _ _ => none
  | .rule _ _ _ => none
  | .strut _ => none
  | .italicCorr _ => none
  | .pageNumber => none
  | .pageCount => none
  | .linebreak _ => none
  | .onSteps _ _ => none
  | .altSteps _ _ _ => none
  | .image _ _ _ => none
  | .icon _ _ => none
  | .label _ => none
  | .ref _ _ _ _ => none
  | .cite _ _ => none
  | .footnote _ _ => none

private def markerCorr : Inline → Bool
  | .italicCorr _ => true
  | _ => false

private def markerCssList (scale : List (String × Nat)) (decls : Array String) :
    List Inline → Option MarkerCss
  | [] => some { text := "", decls := decls }
  | x :: rest =>
    if markerCorr x then markerCssList scale decls rest
    else if rest.all markerCorr then markerCssOne scale decls x
    else (markerTextInto "" (x :: rest)).map fun t => { text := t, decls := decls }

end

public def markerCss? (m : Array Inline)
    (scale : List (String × Nat) := Ir.sizeScale) : Option MarkerCss :=
  markerCssList scale #[] (Ir.eraseLocationInlines m).toList

mutual

private theorem markerTextOne_text (x : Inline) (acc t : String)
    (h : markerTextOne acc x = some t) : t = acc ++ Ir.plainTextOne x := by
  match x with
  | .text _ | .italicCorr _ =>
    simp [markerTextOne] at h
    simp [← h, Ir.plainTextOne]
  | .located _ body => exact markerTextInto_text body.toList acc t h
  | .math _ _ | .formula _ _ _ | .styled _ _
  | .colored _ _ _ | .role _ _ | .link _ _
  | .decorated _ _ | .fill | .hspace _ _ | .rule _ _ _
  | .strut _ | .pageNumber | .pageCount | .linebreak _
  | .onSteps _ _ | .altSteps _ _ _ | .image _ _ _ | .icon _ _
  | .label _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _ =>
    simp [markerTextOne] at h

private theorem markerTextInto_text (xs : List Inline) (acc t : String)
    (h : markerTextInto acc xs = some t) : t = acc ++ Ir.plainTextList xs := by
  match xs with
  | [] =>
    simp [markerTextInto] at h
    simp [← h, Ir.plainTextList]
  | x :: rest =>
    simp only [markerTextInto, Option.bind_eq_some_iff] at h
    obtain ⟨next, hb, hr⟩ := h
    rw [markerTextInto_text rest next t hr, markerTextOne_text x acc next hb]
    simp [Ir.plainTextList, String.append_assoc]

end

private theorem markerCorrOne_text (x : Inline) (h : markerCorr x = true) :
    Ir.plainTextOne x = "" := by
  cases x <;> simp [markerCorr, Ir.plainTextOne] at h ⊢

private theorem markerCorr_text (xs : List Inline)
    (h : ∀ x ∈ xs, markerCorr x = true) : Ir.plainTextList xs = "" := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : markerCorr x = true := h x (by simp)
    have hxs : ∀ y ∈ xs, markerCorr y = true := by
      intro y hy
      exact h y (by simp [hy])
    simp [Ir.plainTextList, markerCorrOne_text x hx, ih hxs]

mutual

private theorem markerCssOne_text (scale : List (String × Nat)) (decls : Array String)
    (x : Inline) (r : MarkerCss)
    (h : markerCssOne scale decls x = some r) : r.text = Ir.plainTextOne x := by
  match x with
  | .text s =>
    simp [markerCssOne] at h
    simp [← h, Ir.plainTextOne]
  | .styled st body =>
    rw [markerCssOne] at h
    split at h
    · rw [Ir.plainTextOne]
      exact markerCssList_text scale _ body.toList r h
    · exact absurd h (by simp)
  | .colored c name body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .role n body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .located _ body =>
    rw [markerCssOne] at h
    rw [Ir.plainTextOne]
    exact markerCssList_text scale _ body.toList r h
  | .math _ _ | .formula _ _ _ | .link _ _ | .decorated _ _ | .fill
  | .hspace _ _ | .rule _ _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .linebreak _ | .onSteps _ _ | .image _ _ _ | .icon _ _ | .label _ | .ref _ _ _ _
  | .cite _ _ | .footnote _ _ =>
    simp [markerCssOne] at h
  | .altSteps _ _ _ => simp [markerCssOne] at h

private theorem markerCssList_text (scale : List (String × Nat)) (decls : Array String)
    (xs : List Inline)
    (r : MarkerCss) (h : markerCssList scale decls xs = some r) :
    r.text = Ir.plainTextList xs := by
  match xs with
  | [] =>
    simp [markerCssList] at h
    simp [← h, Ir.plainTextList]
  | x :: rest =>
    rw [markerCssList] at h
    split at h
    · rename_i hx
      rw [markerCssList_text scale decls rest r h]
      simp [Ir.plainTextList, markerCorrOne_text x hx]
    · split at h
      · rename_i hc
        have hrest : ∀ y ∈ rest, markerCorr y = true := by
          simpa only [List.all_eq_true] using hc
        rw [markerCssOne_text scale decls x r h]
        simp [Ir.plainTextList, markerCorr_text rest hrest]
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨t, ht, hr⟩ := h
        rw [← hr]
        simpa using markerTextInto_text (x :: rest) "" t ht

end

public theorem markerCss?_text (m : Array Inline) (r : MarkerCss)
    (scale : List (String × Nat) := Ir.sizeScale)
    (h : markerCss? m scale = some r) : r.text = Ir.plainText m := by
  calc
    r.text = Ir.plainText (Ir.eraseLocationInlines m) :=
      markerCssList_text scale #[] (Ir.eraseLocationInlines m).toList r h
    _ = Ir.plainText m := Ir.eraseLocationInlines_text m

public def cssString (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\""

/-- `\style` declarations as CSS rules, with a diagnostic for each marker `::marker` cannot
express. -/
public def styleRules (doc : Doc) (lit : Ir.Color → String := cssColor) : String × Array Diag :=
  let sel : String → Option String
    | "titlepage" => some "h1:not(.body-heading)"
    | "heading1" => some "h1.body-heading"
    | "section" => some "h2" | "subsection" => some "h3" | "subsubsection" => some "h4"
    | "heading5" => some "h5" | "heading6" => some "h6"
    | "itemize" => some "ul" | "enumerate" => some "ol"
    | "itemize2" => some "ul ul" | "itemize3" => some "ul ul ul"
    | "itemize4" => some "ul ul ul ul"
    | "enumerate2" => some "ol ol" | "enumerate3" => some "ol ol ol"
    | "enumerate4" => some "ol ol ol ol"
    | "nav" => some "nav"
    -- a defined role is addressed by its class; other engine elements have no selector
    | e => if Ir.styleableElements.contains e then none else some ("." ++ roleClass e)
  let markerSel : String → String
    | "ul" => "ul > li::marker, ul ul > li::marker, ul ul ul > li::marker, " ++
      "ul ul ul ul > li::marker"
    | "ol" => "ol > li::marker, ol ol > li::marker, ol ol ol > li::marker, " ++
      "ol ol ol ol > li::marker"
    | tag => s!"{tag} > li::marker"
  Id.run do
  let mut css := ""
  let mut diags : Array Diag := #[]
  for (element, st) in doc.styles.entries do
    let some tag := sel element | continue
    -- the title block's `after` is a skip of its own, not the heading's margin
    let st := if element == "titlepage" then { Ir.titleHeadingStyle st with after := none }
      else st
    let decls :=
      (st.before.map fun g => s!"margin-top: {cssLength g.width};").toList ++
      (st.after.map fun g => s!"margin-bottom: {cssLength g.width};").toList ++
      (st.indent.map fun g => s!"padding-left: {cssLength g.width};").toList ++
      (st.rule.map fun (c, n) =>
        let color := match n with
          | some name => s!"var({name.property}, {cssColor c})"
          | none => lit c
        -- the rule lifts itself half the heading's ex, as the PDF raises it
        s!"display: flex; align-items: baseline; gap: 0.5em; --rule-color: {color};").toList
    let mut liDecls :=
      (st.gap.map fun g => s!"{tag} > li \{ margin-top: {cssLength g.width}; }\n").toList
    if let some m := st.marker then
      match markerCss? m doc.page.scale with
      | some r =>
        let decls := r.decls.map fun d => match literalColorDecl? d with
          | some c => s!"color: {lit c};"
          | none => d
        let body := String.join (decls.toList.map (" " ++ ·))
        liDecls := liDecls ++
          [s!"{markerSel tag} \{ content: \"{cssString r.text}  \";{body} }\n"]
      | none =>
        diags := diags.push (Diag.of .W0331
          s!"the declared '{element}' marker is not expressible in HTML; \
the level default marks these items"
          (span := Ir.inlineSource m)
          (help := some "marker = {...} reaches HTML as text with colour \
and font styling (CSS Pseudo-Elements 4 §4.1); a link, an image, math, or \
an overlay step does not"))
    -- interaction states apply to the element's links
    let iSel := s!"{tag} a"
    let tokenColor (c : Ir.Color) (n : Option Ir.ColorRef) : String := match n with
      | some name => s!"var({name.property}, {cssColor c})"
      | none => lit c
    let interDecls :=
      (st.hover.map fun (c, n) =>
        s!"{iSel}:hover \{ color: {tokenColor c n}; }\n").toList ++
      (st.focus.map fun (c, n) =>
        s!"{iSel}:focus-visible \{ outline-color: {tokenColor c n}; }\n").toList ++
      (st.motion.map fun ms => motionCss iSel ms).toList
    -- a baseline rule drops the x-height lift; a declared thickness is the border weight
    let ruleDecls : List String := if st.rule.isNone then [] else
      (match st.rulePosition with
        | some .baseline => ["transform: none;"]
        | some .xHeight | none => []) ++
      (st.ruleThickness.map fun g => s!"border-top-width: {cssLength g.width};").toList
    let ruleCss := if ruleDecls.isEmpty then "" else
      s!"{tag}.ruled::after \{ {String.intercalate " " ruleDecls} }\n"
    let own := if decls.isEmpty then "" else s!"{tag} \{ {String.intercalate " " decls} }\n"
    let liCss := String.join liDecls
    let interCss := String.join interDecls
    css := css ++ own ++ ruleCss ++ liCss ++ interCss
  return (css, diags)

/-- A per-mille factor as CSS text: 1440 → `1.440`. -/
private def milliFactor (k : Nat) : String :=
  let pad (n : Nat) : String :=
    let s := toString n
    "".pushn '0' (3 - min 3 s.length) ++ s
  s!"{k / 1000}.{pad (k % 1000)}"

/-- Screen prose leading, per-mille: the top of Butterick's 120–145% band for body text. -/
public def bodyLeadingMilli : Nat := 1450

public theorem body_leading_in_band :
    Ir.leadingMilli ≤ bodyLeadingMilli ∧
    1200 ≤ bodyLeadingMilli ∧ bodyLeadingMilli ≤ 1450 := by decide

/-- The print leading as a CSS `line-height` factor, per-mille, for lines a strut paces. -/
public def printLeadingMilli (page : Ir.PageSpec) : Nat :=
  Ir.leadingMilli * page.leading / 1000

public theorem printLeading_exact (page : Ir.PageSpec) (size : Int) (h : page.leading = 1000) :
    size * (printLeadingMilli page : Int) / 1000 = Ir.leadingFor size page.leading := by
  simp only [printLeadingMilli, Ir.leadingFor, Ir.leadingMilli, h]
  omega

/-- A vertical gap of `k` screen rhythm quanta, in rem. -/
public def quantaRem (k : Nat) : String := milliFactor (k * bodyLeadingMilli / 2) ++ "rem"

private def gapK (kind : String) : Nat := (Ir.rhythmGapQuanta.lookup kind).getD 0

/-- A print length as screen milli-rem: its multiple of the print quantum, in the screen's. -/
public def screenMilli (size v : Int) : Nat :=
  if Ir.rhythmQuantum size ≤ 0 then 0
  else (v * ((bodyLeadingMilli / 2 : Nat) : Int) / Ir.rhythmQuantum size).toNat

private def milliRem (m : Nat) : String := milliFactor m ++ "rem"

public theorem screenMilli_between (size v : Int) (hq : 0 < Ir.rhythmQuantum size) (hv : 0 ≤ v) :
    (screenMilli size v : Int) * Ir.rhythmQuantum size ≤ v * ((bodyLeadingMilli / 2 : Nat) : Int) ∧
      v * ((bodyLeadingMilli / 2 : Nat) : Int) <
        ((screenMilli size v : Int) + 1) * Ir.rhythmQuantum size := by
  have hh : (0 : Int) ≤ ((bodyLeadingMilli / 2 : Nat) : Int) := by decide
  unfold screenMilli
  generalize (Ir.rhythmQuantum size : Int) = q at *
  generalize ((bodyLeadingMilli / 2 : Nat) : Int) = h at *
  have hnq : ¬ q ≤ 0 := Int.not_le.mpr hq
  have hnn : 0 ≤ v * h / q := Int.ediv_nonneg (Int.mul_nonneg hv hh) (Int.le_of_lt hq)
  simp only [hnq, ↓reduceIte, Int.toNat_of_nonneg hnn]
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hq), Int.lt_ediv_add_one_mul_self _ hq⟩

/-- The block elements the backend emits into flow, with the kind of gap each opens. -/
public def blockGapKinds : List (String × String) :=
  [("p", "peer"), ("ul", "peer"), ("ol", "peer"), ("dl", "peer"), ("pre", "peer"),
   ("table.booktabs", "peer"), ("details", "peer"),
   ("h1", "heading"), ("h2", "heading"), ("h3", "heading"), ("h4", "heading"),
   ("h5", "heading"), ("h6", "heading")]

public theorem single_owner_gap_exact (g : Int) (h : 0 ≤ g) :
    max 0 g = g ∧ 0 + g = g := by
  omega

private theorem blockGap_kinds_covers :
    (blockGapKinds.all fun e => 0 < gapK e.2) = true ∧ 0 < gapK "float" ∧
    0 < gapK "caption" ∧ 0 < gapK "trivlist" ∧
    0 < screenMilli Ir.baseFontSize (Ir.displaySkipDefault Ir.baseFontSize).width.sp := by
  rw [Ir.displaySkipDefault_base_exact]
  decide

/-- One rule of the block-boundary sheet, rendered inside `:where()`. -/
public inductive GapRule where
  | reset (sel margin : String)
  | boundary (sel value : String)
  | parskip (sel value : String)
  deriving Repr, DecidableEq

public def GapRule.render : GapRule → String
  | .reset sel m => s!":where({sel}) \{ margin: {m}; }\n"
  | .boundary sel v => s!":where({sel}) \{ margin-top: {v}; }\n"
  | .parskip sel v => s!":where({sel}) \{ --parskip: {v}; }\n"

public def GapRule.isReset : GapRule → Bool
  | .reset _ _ => true
  | .boundary _ _ => false
  | .parskip _ _ => false

/-- The peer gap: the declared `\parskip`, else the table's peer row. -/
private def peerGap : String := s!"var(--parskip, {quantaRem (gapK "peer")})"

/-- A trivlist's own space, its `\topsep`. -/
private def trivlistOwn : String :=
  s!"var(--{Ir.trivlistSkipName}, {quantaRem (gapK "trivlist" - gapK "peer")})"

private def trivlistGap : String := s!"calc({trivlistOwn} + {peerGap})"

/-- The class of fancyvrb's `\list` around a listing's code. -/
public def verbatimListClass : String := "verbatim-list"

/-- The class of a code unit a line may not break inside. -/
public def codeTokClass : String := "tok"

/-- The class of a held code unit longer than `codeShortColumns`. -/
public def codeLongTokClass : String := "tok-long"

/-- The most columns a held code unit takes and stays held in every box: an operator's, as `->`,
`:=` or `...`. -/
public def codeShortColumns : Nat := 3

/-- The box width below which held code units are released: the page column at a 320 px viewport. -/
public def codeReleaseWidth : String := "17.5em"

public def skipClass : String := "vskip"

private theorem skipClass_engine : skipClass ∈ engineClasses := by decide

/-- An overlay step's carrier whose first child is a skip box, owning the box's boundaries. -/
public def skipCarrier : String := s!":is(.step, .step-set):has(> .{skipClass}:first-child)"

/-- An element's space below it, as the boundaries it owns before a paragraph and a skip box. -/
private def ownsBelow (sels : List String) (peer own : String) (after : Option String := none) :
    List GapRule :=
  let follow (tail : String) := ", ".intercalate (sels.map (· ++ tail))
  [.boundary (follow " + *") peer,
   .boundary (follow s!" + :is(.{skipClass}, {skipCarrier}, .fill, section.block-shaped)") own] ++
  (after.map fun v =>
    [.boundary (follow s!" + .{skipClass} + p" ++ ", " ++ follow s!" + .{skipClass} + .{skipClass} + p") v]).getD []

/-- A document skip as a box of its own, carrying the skip's natural width as `--skip`. -/
private def skipNode (size : Int) (g : Ir.Sourced SymGlue) (grow : Option Nat := none) : Node :=
  let v := g.value.width.resolve size (size / 2)
  let rem := milliRem (screenMilli size v.natAbs)
  let len := if v < 0 then s!"-{rem}" else rem
  let len := match g.token.bind tokenVar? with
    | some v => s!"var({v}, {len})"
    | none => len
  let extent := if v < 0 then s!"margin-bottom: {len}" else s!"height: {len}"
  let decls := (if v == 0 then [] else [s!"--skip: {len}", extent]) ++
    (grow.map fun n => [s!"flex-grow: {n}"]).getD []
  let style := if decls.isEmpty then #[] else #[("style", "; ".intercalate decls)]
  Html.elem "div" #[] (#[("class", skipClass)] ++ style)

/-- The elements a list level spaces: lists, quotations and fancyvrb's code list. -/
private def listElems : List String :=
  ["ul:not(.bibliography)", "ol:not(.algorithm):not(.algorithm *)", "blockquote", "dl",
   "." ++ verbatimListClass]

/-- A list block's item, and not a reference-list entry, an algorithm's
line or an endnote. -/
private def itemSubject : String :=
  "li:not(.bibliography *):not(.algorithm *):not([role=doc-endnotes] *)"

/-- An enclosing list's item, as `\@listdepth` counts the levels. -/
private def itemAncestor : String := ":is(li, dd, blockquote) "

/-- A list's own space at a boundary: the level's length over the paragraph gap in force. -/
private def listSpace (m : Nat) : String := s!"calc({milliRem m} + var(--parskip, 0rem))"

/-- The `\parskip` term a list's space folds in, alone. -/
private def texParskip : Option String := some "var(--parskip, 0rem)"

/-- One list level's `\topsep`, `\itemsep` and `\parsep`, in screen milli-rem. -/
public def listLevelGaps (size : Int) (sk : Ir.ListSkips) : Nat × Nat × Nat :=
  (screenMilli size sk.topsep.width.sp, screenMilli size sk.itemsep.width.sp,
   screenMilli size sk.parsep.width.sp)

/-- A list level's `\@topsepadd` where the list opens a paragraph, in screen milli-rem. -/
public def listOpenGap (size : Int) (sk : Ir.ListSkips) (partopsep : SymGlue) : Nat :=
  screenMilli size (sk.topsep.width.sp + partopsep.width.sp)

/-- One list level's rules, `pre` reaching the level through an item ancestor per enclosing list. -/
private def listLevelRules (pre : String) (g : Nat × Nat × Nat) (opened : Nat)
    (nested : Nat × Nat) (disc : String := "details[open]") : List GapRule :=
  let inPar := roleClass Ir.inParagraphRole
  -- an item may end on a disclosure whose body ends on the list
  let after (sel : String) (m : Nat) : GapRule :=
    let ends := s!":is({", ".intercalate listElems}){sel}:last-child"
    let last := s!":has(> {ends}, > {disc}:last-child > {ends})"
    .boundary s!"{pre}li{last} + {itemSubject}, {pre}dd{last} + dt" (listSpace m)
  [.parskip s!"{pre}{itemSubject}, {pre}blockquote > *, {pre}dl > *" (milliRem g.2.2),
   .boundary (", ".intercalate (listElems.map fun e => s!"{pre}* + {e}")) (listSpace opened)] ++
  ownsBelow (listElems.map (pre ++ ·)) (listSpace opened) (milliRem opened) texParskip ++
  [.boundary s!"{pre}li + {itemSubject}, {pre}dd + dt" (listSpace g.2.1)] ++
  (if opened == g.1 then [] else
    .boundary s!"{pre}* + .{inPar}" (listSpace g.1) ::
      ownsBelow [s!"{pre}.{inPar}"] (listSpace g.1) (milliRem g.1) texParskip) ++
  (if nested.1 ≤ g.2.1 then [] else [after "" nested.1]) ++
  (if nested.2 ≤ max g.2.1 nested.1 then [] else [after s!":not(.{inPar})" nested.2])

/-- The list rules a page's class owes, `\@list⟨n⟩` for levels one to three; the web lineage
owes none. -/
public def listRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (disc : String := "details[open]") : List GapRule :=
  let spaces (n : Nat) : Nat × Nat := match Ir.listSkips l size n with
    | some sk => ((listLevelGaps size sk).1, listOpenGap size sk (Ir.partopsepFor l size n tokens))
    | none => (0, 0)
  [1, 2, 3].flatMap fun n => match Ir.listSkips l size n with
    | some sk => listLevelRules (String.join (List.replicate (n - 1) itemAncestor))
        (listLevelGaps size sk) (spaces n).2 (spaces (n + 1)) disc
    | none => []

/-- A squeezed frame's list rules: the class's levels with beamer's `\itemsep0pt`. -/
public def squeezeListRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (disc : String := "details[open]") : List GapRule :=
  let squeezed (n : Nat) : Option Ir.ListSkips :=
    (Ir.listSkips l size n).map fun sk => { sk with itemsep := {} }
  let spaces (n : Nat) : Nat × Nat := match squeezed n with
    | some sk => ((listLevelGaps size sk).1, listOpenGap size sk (Ir.partopsepFor l size n tokens))
    | none => (0, 0)
  [1, 2, 3].flatMap fun n => match squeezed n with
    | some sk =>
      listLevelRules ("section.slide.squeeze " ++ String.join (List.replicate (n - 1) itemAncestor))
        (listLevelGaps size sk) (spaces n).2 (spaces (n + 1)) disc
    | none => []

/-- A lineage's list indents as CSS for the kernel's six levels, under the custom property of
their length. -/
public def listIndentCss (l : Ir.ListLineage) : String :=
  String.join ((List.range 6).map fun k =>
    let pre := String.join (List.replicate k itemAncestor)
    let v := s!"var(--{Ir.leftMarginName (k + 1)}, " ++ (match Ir.leftMarginMilli l (k + 1) with
      | some m => s!"{decMilli m}em"
      | none => "1.35rem") ++ ")"
    s!"{pre}ul, {pre}ol, {pre}dd \{ padding-left: {v}; }\n{pre}blockquote \{ padding: 0 {v}; }\n")

/-- The space rules of theorem-like blocks, on the element their role's class marks. -/
public def thmRules (l : Ir.ListLineage) (size : Int) : List GapRule :=
  Ir.ThmSpace.all.flatMap fun k =>
    let c := "." ++ roleClass (Ir.thmSpaceRole k)
    match Ir.thmSkips l size 1 {} k false with
    | some sk =>
      let above := screenMilli size sk.above.width.sp
      let below := screenMilli size sk.below.width.sp
      .boundary s!"* + {c}" (if sk.parskipAbove then listSpace above else milliRem above) ::
        ownsBelow [c] (listSpace below) (milliRem below) texParskip
    | none => .boundary s!"* + {c}" trivlistGap :: ownsBelow [c] trivlistGap trivlistOwn

/-- The resets: every block element's own vertical margins. -/
private def gapResets : List GapRule :=
  [.reset "p, ul, ol, li, dl, dd, pre, blockquote, hr" "0",
   .reset "h1, h2, h3, h4, h5, h6" s!"0 0 {quantaRem (gapK "peer")}",
   -- a title over a title bar's skip has no band of its own
   .reset s!"h1:not(.body-heading):has(+ .{skipClass} + hr.separator)" "0",
   .reset "section.slide > header h2" "0",
   .reset "figure.float" "0 auto",
   -- a negative skip is the skip box's bottom margin
   .reset s!".{skipClass}" "0 0 min(0rem, var(--skip, 0rem))"]

private def gapBeforeLists : List GapRule :=
  (blockGapKinds.filter (·.2 != "heading")).map (fun (sel, _) =>
    .boundary s!"* + {sel}" peerGap) ++
  [.boundary ".bibliography > li + li" peerGap,
   .boundary s!"* + .{roleClass Ir.trivlistRole}, * + blockquote" trivlistGap] ++
  ownsBelow [s!".{roleClass Ir.trivlistRole}", "blockquote"] trivlistGap trivlistOwn

/-- The display's space, TeX's `\abovedisplayskip`, in the screen's quanta. -/
private def displayGapRem : String :=
  milliRem (screenMilli Ir.baseFontSize (Ir.displaySkipDefault Ir.baseFontSize).width.sp)

/-- The follower past a skip box after a heading or at a container's opening pays nothing. -/
private def skipFollowerRule : GapRule :=
  let box := s!".{skipClass}"
  let past (place : String) (edge : String) : List String :=
    [s!"{place}{box}{edge} + *", s!"{place}{box}{edge} + {box} + *",
     s!"{place}{skipCarrier}{edge} > {box}:first-child + *"]
  .boundary (", ".intercalate (past ":is(h1, h2, h3, h4, h5, h6) + " "" ++
    past ":not(section.slide, .step, .step-set) > " ":first-child")) "0"

private def gapAfterLists : List GapRule :=
  let float := s!"var(--floatsep, {quantaRem (gapK "float")})"
  let display := s!"var(--{Ir.displaySkipBelow}, {displayGapRem})"
  (blockGapKinds.filter (·.2 == "heading")).map (fun (sel, kind) =>
    .boundary s!"* + {sel}" (quantaRem (gapK kind))) ++
  [.boundary s!"* + section[id] > h{Ir.headingRank 1}:first-child" (quantaRem (gapK "heading")),
   .boundary "* + figure.float" float,
   -- a title under a title bar stands on the bar's skip alone
   .boundary "hr.separator + .vskip + h1:not(.body-heading)" "0"] ++
  ownsBelow ["figure.float"] float float ++
  [.boundary "* + .display" s!"var(--{Ir.displaySkipAbove}, {displayGapRem})"] ++
  ownsBelow [".display"] display display (some "0rem") ++
  [ -- the caption's margin-bottom is the float's one seam
    .boundary "figure.float > figcaption:first-child + *" "0",
    -- a skip opening a frame pays beamer's `\vskip-\parskip`, which the paragraph past it cancels
    .boundary (s!"section.slide > :is(.{skipClass}, {skipCarrier}):first-child, " ++
      s!"section.slide > .fill:first-child + :is(.{skipClass}, {skipCarrier})")
      "calc(0rem - var(--parskip, 0rem))",
    -- the first body element owns the frame opening, which a fil spacer cannot pay
    .boundary "section.slide > .frame-body-start"
      ("calc(var(--frame-body-skip) + var(--frame-title-below, 0pt) + " ++
        "var(--frame-body-before, 0pt) + var(--frame-body-open, 0pt))"),
    -- An overlay carrier opening the frame gives the opening to the block
    -- its flow opens on in each group (`markFlowStart`): the one a snap
    -- shows opens the frame, as its page opens it.
    .boundary "section.slide > .frame-body-start:has(.frame-flow-start)" "0",
    .boundary "section.slide .frame-flow-start"
      ("calc(var(--frame-body-skip) + var(--frame-title-below, 0pt) + " ++
        "var(--frame-body-before, 0pt) + var(--frame-body-open, 0pt))")]

/-- The heading's follower takes no gap: the band below is the heading's own. -/
private def headingFollowerRule : GapRule := .boundary ":is(h1, h2, h3, h4, h5, h6) + *" "0"

/-- A skip register in force, as a print length; an `ex` part stands at zero. -/
private def skipSp (size : Int) (tokens : Ir.Tokens) (name : String) : Int :=
  (Ir.skipAmount tokens name).width.resolve size 0

/-- A block's own space above it, `\medskipamount` and `\lineskip` (beamerinnerthemedefault.sty),
in screen milli-rem. -/
private def blockAboveMilli (size : Int) (tokens : Ir.Tokens) : Nat :=
  screenMilli size (skipSp size tokens "medskipamount" + Ir.inkClearance)

/-- What stands for a block at a frame's opening: the block, or the overlay step carrier it
opens. -/
private def blockAt (edge : String) : String :=
  s!":is(section.block, :is(.step, .step-set):has(> section.block:{edge}), " ++
    s!":is(.step, .step-set):has(> .step-end > section.block:{edge}))"

/-- A block's boundaries: its space above, and `\smallskipamount` below its body box. -/
private def blockRules (size : Int) (tokens : Ir.Tokens) (shaped : Bool) : List GapRule :=
  let above := blockAboveMilli size tokens
  let below := screenMilli size (skipSp size tokens "smallskipamount")
  -- tcolorbox's `beforeafter skip balanced=0.5\baselineskip`
  let balanced := milliRem (screenMilli size (Ir.rhythmQuantum size))
  let shapedRules : List GapRule := if !shaped then [] else
    .boundary "* + section.block-shaped" "0rem" ::
      ownsBelow ["section.block-shaped"] s!"calc(0rem + {peerGap})" "0rem" ++
    [.boundary s!".{roleClass Ir.trivlistRole} + section.block-shaped, blockquote + section.block-shaped"
       trivlistOwn,
     .boundary "section.block + section.block-shaped" (milliRem below),
     .boundary "section.block-shaped + section.block" (milliRem above),
     .boundary "section.block-shaped + section.block-shaped" "0rem",
     .parskip "section.block-shaped > *" "inherit"]
  .boundary "* + section.block" (milliRem above) ::
    ownsBelow ["section.block"] s!"calc({milliRem below} + {peerGap})" (milliRem below) ++
  [.boundary "section.block + section.block" (milliRem (below + above)),
   .parskip "section.block > *" "0rem"] ++ shapedRules ++
  [.boundary "* + section.tcolorbox" balanced] ++
  ownsBelow ["section.tcolorbox"] balanced s!"calc({balanced} - {peerGap})" ++
  [.parskip "section.tcolorbox > *" "0rem"]

/-- The boundaries beamer sets by adding where `\addvspace` would take the larger. -/
private def beamerPairRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) :
    List GapRule :=
  match l, Ir.listSkips l size 1 with
  | .beamer, some sk =>
    let opened := milliRem (listOpenGap size sk (Ir.partopsepFor l size 1 tokens))
    let below := milliRem (screenMilli size (skipSp size tokens "smallskipamount"))
    let above := milliRem (blockAboveMilli size tokens)
    let display := s!"var(--{Ir.displaySkipBelow}, {displayGapRem})"
    let triv := "." ++ roleClass Ir.trivlistRole
    let top := ":not(li, dd, blockquote) > "
    let lists := s!":is({", ".intercalate (listElems.filter (· != "blockquote"))})"
    let beamerLists := ":is(ul:not(.bibliography), ol:not(.algorithm):not(.algorithm *), dl)"
    let plainBlock := "section.block:not(.block-shaped)"
    let uppers : List (String × String × Bool) :=
      [(plainBlock, below, true), (lists, opened, false), (triv, trivlistOwn, false),
       (".display", display, false)]
    uppers.flatMap fun (u, own, block) =>
      [.boundary s!"{top}{u} + {beamerLists}" s!"calc({own} + {opened} + var(--parskip, 0rem))",
       .boundary s!"{top}{u} + .{verbatimListClass}"
         s!"calc(max({own}, {opened}) + var(--parskip, 0rem))"] ++
      (if block then [] else
        [.boundary s!"{top}{u} + {plainBlock}" s!"calc({own} + {above})"]) ++
      (if u == triv then [] else
        [.boundary s!"{top}{u} + {triv}" s!"calc(max({own}, {trivlistOwn}) + var(--parskip, 0rem))"])
  | _, _ => []

/-- The block-boundary sheet, the one emitter of every vertical margin a block element carries. -/
public def blockGapRules (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (shaped : Bool := false) (squeezed : Bool := false) (disc : String := "details[open]") :
    List GapRule :=
  gapResets ++ gapBeforeLists ++ blockRules size tokens shaped ++ thmRules l size ++
    listRules l size tokens disc ++ (if squeezed then squeezeListRules l size tokens disc else []) ++
    gapAfterLists ++ beamerPairRules l size tokens ++
    [skipFollowerRule, headingFollowerRule]

/-! ## Overlay carriers -/

private def classHas (v c : String) : Bool := (v.splitOn " ").contains c

private def attrsClass (attrs : Array (String × String)) : String :=
  ((attrs.find? (·.1 == "class")).map (·.2)).getD ""

private def classOfNode : Node → String
  | .elem _ attrs _ => attrsClass attrs
  | .text _ | .style _ | .script _ _ => ""

/-- A carrier one element of a chain: an overlay's step, set or end, an alternation's group, or a
backend group. -/
private def isLinkCarrier : Node → Bool
  | .elem "div" attrs _ =>
    attrs.any (·.1 == "data-backend") ||
      ["step", "step-set", "step-end", "alt"].any (classHas (attrsClass attrs) ·)
  | .elem .. | .text _ | .style _ | .script _ _ => false

private def isAltPair : Node → Bool
  | .elem "div" attrs _ => classHas (attrsClass attrs) "alt-pair"
  | .elem .. | .text _ | .style _ | .script _ _ => false

private def isCarrierNode (n : Node) : Bool := isLinkCarrier n || isAltPair n

/-- A disclosure, which a boundary reads through upward only. -/
private def isDisclosureNode : Node → Bool
  | .elem "details" _ _ => true
  | .elem .. | .text _ | .style _ | .script _ _ => false

private def isUpCarrierNode (n : Node) : Bool := isCarrierNode n || isDisclosureNode n

/-- An element the page hides with no snap state. -/
private def hiddenNode : Node → Bool
  | .elem _ attrs _ => attrs.any (·.1 == "hidden")
  | .text _ | .style _ | .script _ _ => false

mutual

/-- The tag and class a carrier ends on, down its last children. -/
private def carrierEndKey : Node → Option (String × String)
  | .elem _ _ kids => endKeyList none kids.toList
  | .text _ | .style _ | .script _ _ => none

-- conserves: none — the list face of `carrierEndKey`
private def endKeyList (acc : Option (String × String)) : List Node → Option (String × String)
  | [] => acc
  | x :: rest =>
    match x with
    | .elem tag attrs _ =>
      endKeyList (if isLinkCarrier x then carrierEndKey x
        else if isAltPair x then
          (if classHas (attrsClass attrs) "alt-alike" then carrierEndKey x else floorEndKey x)
        else some (tag, attrsClass attrs)) rest
    | .text _ => endKeyList acc rest
    | .style _ | .script _ _ => endKeyList none rest

/-- The end of an alternation's group the page shows with no snap state. -/
private def floorEndKey : Node → Option (String × String)
  | .elem _ _ kids => floorEndKeyList kids.toList
  | .text _ | .style _ | .script _ _ => none

-- conserves: none — the list face of `floorEndKey`
private def floorEndKeyList : List Node → Option (String × String)
  | [] => none
  | x :: rest =>
    if classHas (classOfNode x) "alt" && !hiddenNode x then carrierEndKey x
    else floorEndKeyList rest

end

/-- Both groups of an alternation end on the same element. -/
private def altEndsAlike (first other : Array Node) : Bool :=
  match endKeyList none first.toList, endKeyList none other.toList with
  | some a, some b => a == b
  | _, _ => false

mutual

/-- The carrier depths at which the chains of first children `n` opens end on an element. -/
private def downDepths : Node → List Nat
  | .elem _ attrs kids =>
    if classHas (attrsClass attrs) "alt-pair" then groupDownDepths [] kids.toList
    else firstDepths kids.toList
  | .text _ | .style _ | .script _ _ => []

-- conserves: none — the list face of `downDepths`
private def firstDepths : List Node → List Nat
  | [] => []
  | x :: rest =>
    match x with
    | .elem .. => if isCarrierNode x then (downDepths x).map (· + 1) else [1]
    | .text _ => firstDepths rest
    | .style _ | .script _ _ => [1]

-- conserves: none — an alternation's groups for `downDepths`
private def groupDownDepths (acc : List Nat) : List Node → List Nat
  | [] => acc
  | x :: rest =>
    groupDownDepths (if classHas (classOfNode x) "alt"
      then acc ++ (downDepths x).map (· + 1) else acc) rest

end

mutual

/-- The carrier depths of the chains of last children `n` closes. -/
private def upDepths : Node → List Nat
  | .elem _ attrs kids =>
    if classHas (attrsClass attrs) "alt-pair" then
      groupUpDepths (classHas (attrsClass attrs) "alt-alike") [] kids.toList
    else lastDepths [] kids.toList
  | .text _ | .style _ | .script _ _ => []

-- conserves: none — the list face of `upDepths`
private def lastDepths (acc : List Nat) : List Node → List Nat
  | [] => acc
  | x :: rest =>
    match x with
    | .elem .. => lastDepths (if isUpCarrierNode x then (upDepths x).map (· + 1) else [1]) rest
    | .text _ => lastDepths acc rest
    | .style _ | .script _ _ => lastDepths [1] rest

-- conserves: none — an alternation's groups for `upDepths`
private def groupUpDepths (alike : Bool) (acc : List Nat) : List Node → List Nat
  | [] => acc
  | x :: rest =>
    groupUpDepths alike (if classHas (classOfNode x) "alt" && (alike || !hiddenNode x)
      then acc ++ (upDepths x).map (· + 1) else acc) rest

end

/-- A slide's furniture after its body: spacer, footer, logo and notes. -/
private def frameFurniture : Node → Bool
  | .elem tag attrs _ =>
    tag == "footer" || tag == "aside" ||
      ["fill", "frame-body-tail", "slide-logo", "snap"].any (classHas (attrsClass attrs) ·)
  | .text _ | .style _ | .script _ _ => false

/-- The boundary shapes two adjacent siblings stand between. -/
private def pairDepths (p y : Node) : List (Nat × Nat) :=
  let js := 0 :: (if isUpCarrierNode p && !frameFurniture y then upDepths p else [])
  let ks := 0 :: (if isCarrierNode y then downDepths y else [])
  js.flatMap fun j => ks.filterMap fun k => if j == 0 && k == 0 then none else some (j, k)

/-- One element's children, pair by adjacent pair, text between them aside. -/
private def siblingPairs (acc : List (Nat × Nat)) (prev : Option Node) :
    List Node → List (Nat × Nat)
  | [] => acc
  | x :: rest =>
    match x with
    | .text _ => siblingPairs acc prev rest
    | .elem .. | .style _ | .script _ _ =>
      siblingPairs (match prev with
        | some p => (pairDepths p x).foldl (fun a q => if a.contains q then a else q :: a) acc
        | none => acc) (some x) rest

mutual

private def treePairsOne (acc : List (Nat × Nat)) : Node → List (Nat × Nat)
  | .elem _ _ kids => treePairsList (siblingPairs acc none kids.toList) kids.toList
  | .text _ | .style _ | .script _ _ => acc

-- conserves: none — every element's children for `carrierPairs`
private def treePairsList (acc : List (Nat × Nat)) : List Node → List (Nat × Nat)
  | [] => acc
  | x :: rest => treePairsList (treePairsOne acc x) rest

end

/-- The sorted boundary shapes of an emitted tree, which its sheet's boundaries read through. -/
public def carrierPairs (nodes : Array Node) : List (Nat × Nat) :=
  (treePairsList (siblingPairs [] none nodes.toList) nodes.toList).mergeSort
    fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The carriers a boundary reads down from. -/
private def carrierTop : String := "div:is(.step, .step-set, .alt-pair, [data-backend])"



/-- A carrier one element further down a chain of first children. -/
private def carrierFirstLink : String :=
  ":is(div:is(.step, .step-set, .step-end, .alt-pair, [data-backend]):first-child, div.alt)"

/-- `carrierFirstLink` down a chain of last children, through the disclosures `disc` shows. -/
private def carrierLastLink (disc : String) : String :=
  ":is(div:is(.step, .step-set, .step-end, .alt-pair, [data-backend]):last-child, " ++
    s!"{disc}:last-child, .alt-alike > div.alt, div.alt:not([hidden]))"

/-- The carriers a boundary reads up from: `carrierTop` and the disclosures `disc` shows. -/
private def carrierTopUp (disc : String) : String :=
  s!":is(div:is(.step, .step-set, .alt-pair, [data-backend]), {disc})"

/-- `sel`'s parts at the separators `sep` no parenthesis encloses. -/
private def splitTop (sep : Char) (sel : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth : Nat := 0
  for c in sel.toList do
    if c == sep && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else
      if c == '(' then depth := depth + 1
      if c == ')' then depth := depth - 1
      cur := cur.push c
  return (out.push cur.trimAscii.toString).toList

/-- A boundary member `X + Y` as its descendant prefix and its two compounds. -/
private def siblingMember? (m : String) : Option (String × String × String) :=
  let comb (w : String) : Bool := w == "+" || w == ">" || w == "~"
  let item (w : String) : Bool := w.startsWith "li" || w.startsWith "dd" || w.startsWith "dt"
  match ((splitTop ' ' m).filter (!·.isEmpty)).reverse with
  | y :: "+" :: x :: pre =>
    if comb y || comb x || item x || item y || pre.any comb then none
    else some (String.join (pre.reverse.map (· ++ " ")), x, y)
  | _ => none

/-- A boundary member `X + Y` and its variants through the boundary shapes `pairs`. -/
private def throughMembers (pairs : List (Nat × Nat)) (disc : String) (m : String) :
    List String :=
  match siblingMember? m with
  | none => [m]
  | some (pre, x, y) =>
    if pairs.isEmpty then [m] else
    let y := if y == "*" then s!"*:not({carrierTop})" else y
    let down (k : Nat) : String :=
      carrierTop ++ ":not(.frame-body-start)" ++
        String.join (List.replicate (k - 1) (" > " ++ carrierFirstLink)) ++
        " > " ++ y ++ ":first-child"
    let up (j : Nat) : String :=
      carrierTopUp disc ++ ":has(> " ++
        String.join (List.replicate (j - 1) (carrierLastLink disc ++ " > ")) ++ x ++ ":last-child)"
    let upOk := !(x == "*" || (x.splitOn ":has(").length > 1)
    -- a carrier opening on a skip box owns the box's boundary
    let downOk := (y.splitOn ("." ++ skipClass)).length == 1
    let frameEnd := if upOk && pre.isEmpty && y == s!"*:not({carrierTop})" then
        [s!"section.slide:has({x}.frame-flow-end) > .frame-body-tail"]
      else []
    (pre ++ x ++ " + " ++ y) :: (frameEnd ++ pairs.filterMap fun (j, k) =>
      if j == 0 then (if k == 0 || !downOk then none else some (pre ++ x ++ " + " ++ down k))
      else if !upOk then none
      else if k == 0 then some (pre ++ up j ++ " + " ++ y)
      else if !downOk then none
      else some (pre ++ up j ++ " + " ++ down k))

/-- A boundary rule read through the boundary shapes `pairs`; resets and parskip rules stay. -/
public def GapRule.throughCarriers (pairs : List (Nat × Nat)) (disc : String := "details[open]") :
    GapRule → GapRule
  | .boundary sel v =>
    if pairs.isEmpty then .boundary sel v
    else .boundary (", ".intercalate ((splitTop ',' sel).flatMap (throughMembers pairs disc))) v
  | .reset sel m => .reset sel m
  | .parskip sel v => .parskip sel v

public theorem GapRule.throughCarriers_isReset (pairs : List (Nat × Nat)) (r : GapRule) :
    (r.throughCarriers pairs).isReset = r.isReset := by
  cases r with
  | boundary sel v =>
    simp only [GapRule.throughCarriers]
    split <;> rfl
  | reset _ _ => rfl
  | parskip _ _ => rfl

/-- The block-boundary sheet read through a tree's boundary shapes. -/
public def blockGapCss (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (pairs : List (Nat × Nat) := []) (shaped : Bool := false) (squeezed : Bool := false) :
    String :=
  String.join ((blockGapRules l size tokens shaped squeezed).map fun r =>
    (r.throughCarriers pairs).render)

/-- The boundaries paper reads through a closed disclosure, whose body it sets. -/
public def disclosurePrintGapCss (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (pairs : List (Nat × Nat) := []) (shaped : Bool := false) (squeezed : Bool := false) :
    String :=
  let reads (m : String) : Bool := (m.splitOn "details").length > 1
  String.join ((blockGapRules l size tokens shaped squeezed "details").filterMap fun r =>
    match r.throughCarriers pairs "details" with
    | .boundary sel v =>
      let kept := (splitTop ',' sel).filter reads
      if kept.isEmpty then none else some ("  " ++ (GapRule.boundary (", ".intercalate kept) v).render)
    | _ => none)

private theorem dropWhile_append_all {α : Type} (p : α → Bool) (xs ys : List α)
    (h : xs.all p = true) : (xs ++ ys).dropWhile p = ys.dropWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [h.1, ih h.2]

private theorem dropWhile_none {α : Type} (p : α → Bool) (ys : List α)
    (h : ys.all (fun y => !p y) = true) : ys.dropWhile p = ys := by
  cases ys with
  | nil => rfl
  | cons y ys =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [h.1]

private theorem listLevelRules_noReset (pre : String) (g : Nat × Nat × Nat) (o : Nat)
    (n : Nat × Nat) : (listLevelRules pre g o n).all (fun r => !r.isReset) = true := by
  unfold listLevelRules
  split <;> split <;> split <;> rfl

private theorem listRules_noReset (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) :
    (listRules l size tokens).all (fun r => !r.isReset) = true := by
  simp only [listRules, List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> first | rfl | exact listLevelRules_noReset _ _ _ _

private theorem beamerPairRules_noReset (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens) :
    (beamerPairRules l size tokens).all (fun r => !r.isReset) = true := by
  unfold beamerPairRules
  split
  · simp only [List.all_flatMap, List.all_eq_true]
    intro u _
    split <;> split <;> simp [GapRule.isReset]
  · rfl

private theorem squeezeListRules_noReset (l : Ir.ListLineage) (size : Int)
    (tokens : Ir.Tokens) : (squeezeListRules l size tokens).all (fun r => !r.isReset) = true := by
  simp only [squeezeListRules, List.all_flatMap, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true]
  refine ⟨?_, ?_, ?_⟩ <;> split <;> first | rfl | exact listLevelRules_noReset _ _ _ _

private theorem thmRules_noReset (l : Ir.ListLineage) (size : Int) :
    (thmRules l size).all (fun r => !r.isReset) = true := by
  simp only [thmRules, List.all_flatMap, List.all_eq_true]
  intro k _
  split <;> simp [ownsBelow, GapRule.isReset, texParskip]

public theorem blockGap_owner_contract (l : Ir.ListLineage) (size : Int) (tokens : Ir.Tokens)
    (shaped : Bool) (squeezed : Bool := false) :
    ((blockGapRules l size tokens shaped squeezed).dropWhile GapRule.isReset).all
        (fun r => !r.isReset) = true ∧
    (blockGapRules l size tokens shaped squeezed).getLast? =
      some (.boundary ":is(h1, h2, h3, h4, h5, h6) + *" "0") := by
  have hbefore : gapBeforeLists.all (fun r => !r.isReset) = true := by decide
  have hafter : gapAfterLists.all (fun r => !r.isReset) = true := by decide
  have htail : [skipFollowerRule, headingFollowerRule].all (fun r => !r.isReset) = true := by
    decide
  have hblock : (blockRules size tokens shaped).all (fun r => !r.isReset) = true := by
    cases shaped <;> simp [blockRules, ownsBelow, GapRule.isReset]
  have hsq : (if squeezed then squeezeListRules l size tokens else []).all
      (fun r => !r.isReset) = true := by
    cases squeezed
    · rfl
    · exact squeezeListRules_noReset l size tokens
  have hall : (gapBeforeLists ++ blockRules size tokens shaped ++ thmRules l size ++
      listRules l size tokens ++ (if squeezed then squeezeListRules l size tokens else []) ++
      gapAfterLists ++ beamerPairRules l size tokens ++
      [skipFollowerRule, headingFollowerRule]).all (fun r => !r.isReset) = true := by
    simp only [List.all_append, hbefore, hafter, htail, hblock, thmRules_noReset,
      listRules_noReset, beamerPairRules_noReset, hsq, Bool.and_self]
  refine ⟨?_, ?_⟩
  · simp only [blockGapRules, List.append_assoc] at hall ⊢
    rw [dropWhile_append_all _ _ _ (by decide), dropWhile_none _ _ hall]
    exact hall
  · simp [blockGapRules, headingFollowerRule]

public theorem blockGapThrough_owner_contract (l : Ir.ListLineage) (size : Int)
    (tokens : Ir.Tokens) (d : List (Nat × Nat)) (shaped : Bool) (squeezed : Bool := false) :
    (((blockGapRules l size tokens shaped squeezed).map (GapRule.throughCarriers d)).dropWhile
        GapRule.isReset).all (fun r => !r.isReset) = true ∧
      ((blockGapRules l size tokens shaped squeezed).map (GapRule.throughCarriers d)).getLast? =
        some ((GapRule.boundary ":is(h1, h2, h3, h4, h5, h6) + *" "0").throughCarriers d) := by
  have hc := blockGap_owner_contract l size tokens shaped squeezed
  have hp : (GapRule.isReset ∘ GapRule.throughCarriers d) = GapRule.isReset := by
    funext r
    exact GapRule.throughCarriers_isReset d r
  have hn : ((fun r => !r.isReset) ∘ GapRule.throughCarriers d) = (fun r => !r.isReset) := by
    funext r
    simp [GapRule.throughCarriers_isReset]
  refine ⟨?_, ?_⟩
  · rw [List.dropWhile_map, hp, List.all_map, hn]
    exact hc.1
  · rw [List.getLast?_map, hc.2]
    rfl

public theorem listGaps_agree (size : Int) (sk : Ir.ListSkips) (pt : SymGlue)
    (hq : 0 < Ir.rhythmQuantum size)
    (h0 : 0 ≤ sk.topsep.width.sp ∧ 0 ≤ sk.itemsep.width.sp ∧ 0 ≤ sk.parsep.width.sp)
    (hp : 0 ≤ sk.topsep.width.sp + pt.width.sp) :
    let h : Int := ((bodyLeadingMilli / 2 : Nat) : Int)
    let q := Ir.rhythmQuantum size
    let g := listLevelGaps size sk
    let o := listOpenGap size sk pt
    ((g.1 : Int) * q ≤ sk.topsep.width.sp * h ∧ sk.topsep.width.sp * h < ((g.1 : Int) + 1) * q) ∧
    ((g.2.1 : Int) * q ≤ sk.itemsep.width.sp * h ∧
      sk.itemsep.width.sp * h < ((g.2.1 : Int) + 1) * q) ∧
    ((g.2.2 : Int) * q ≤ sk.parsep.width.sp * h ∧
      sk.parsep.width.sp * h < ((g.2.2 : Int) + 1) * q) ∧
    ((o : Int) * q ≤ (sk.topsep.width.sp + pt.width.sp) * h ∧
      (sk.topsep.width.sp + pt.width.sp) * h < ((o : Int) + 1) * q) :=
  ⟨screenMilli_between size _ hq h0.1, screenMilli_between size _ hq h0.2.1,
   screenMilli_between size _ hq h0.2.2, screenMilli_between size _ hq hp⟩

public theorem listRules_web_exact (size : Int) (tokens : Ir.Tokens) :
    listRules .web size tokens = [] := by
  simp only [listRules, Ir.listSkips_web_exact]
  rfl

/-- A declared `\parskip`'s natural width in sp, at the body size it was set under. -/
public def parskipSp (page : Ir.PageSpec) (g : SymGlue) : Dim.Sp :=
  g.width.resolve page.fontSize (page.fontSize / 2)

/-- The document's declared `\parskip` as the screen peer gap, written only where the page
declares one. -/
public def parskipVar (page : Ir.PageSpec) : String :=
  match page.parskip with
  | none => ""
  | some g => s!"    --parskip: {milliRem (screenMilli page.fontSize (parskipSp page g))};\n"

/-- The PDF backend's default gap at a boundary kind; an unknown kind is zero. -/
public def pdfGapSp : String → Dim.Sp
  | "peer" => (Ir.parskipDefault Ir.baseFontSize).width.sp
  | "heading" => 2 * (Ir.parskipDefault Ir.baseFontSize).width.sp
  | "caption" => (Ir.captionSepDefault Ir.baseFontSize).width.sp
  | "float" => (Ir.floatSepDefault Ir.baseFontSize).width.sp
  | "trivlist" => (Ir.parskipDefault Ir.baseFontSize).width.sp
      + (Ir.trivlistSkipDefault Ir.baseFontSize).width.sp
  | _ => 0

/-- The screen backend's default gap at a boundary kind, in milli-rem. -/
public def htmlGapMilliRem (kind : String) : Nat :=
  gapK kind * bodyLeadingMilli / 2

public theorem backend_gaps_agree :
    (Ir.rhythmGapQuanta.all fun e1 =>
      Ir.rhythmGapQuanta.all fun e2 =>
        pdfGapSp e1.1 * (htmlGapMilliRem e2.1 : Int)
          == pdfGapSp e2.1 * (htmlGapMilliRem e1.1 : Int)) = true := by decide

/-- The slide box's inner padding, which the frame-title bar's bleed negates. -/
private def slidePadV : String := "1.4rem"
private def slidePadH : String := "1.8rem"
private def slideRadiusPx : Nat := 8
private def slideBorderPx : Nat := 1

/-- The deck's safe area, 6vmin by default: the middle of the 5–7% Keynote's themes keep clear. -/
private def safeareaVar : String := "var(--safearea, 6vmin)"

/-- A named size step as a CSS factor, read through `Ir.scaleStep`. -/
private def stepFactor (name : String) : String :=
  milliFactor (Ir.scaleStep (1000 : Dim.Sp) name).toNat

/-- A standout frame's size step, `\Large`. -/
private def standoutStep : String := "Large"

/-- The tallest type a footline band's slots set, per mille of the band's own step. -/
private def footCapDecl (scale : List (String × Nat)) (band : Array Ir.BandSlot) :
    List String :=
  let step := (Ir.scaleStepIn scale 1000 Ir.footline.step).toNat
  let sizeOf (m : Nat) (x : Inline) : Nat := match x with
    | .styled (.size n) _ => max m (Ir.scaleStepIn scale 1000 n).toNat
    | _ => m
  let tallest := band.foldl (fun m s => Ir.foldInlines sizeOf m s.content) step
  if tallest ≤ step then [] else [s!"--foot-cap: {milliFactor (tallest * 1000 / max step 1)};"]

@[expose] public def titledBodyPaint (pal : Ir.Palette) (kind : Ir.TitledKind)
    (parent : Ir.ColorPair) : Ir.ColorPair :=
  (Ir.Design.ofPalette pal).titledBodyPaint kind parent

public theorem titledBodyPaint_projects (pal : Ir.Palette) (kind : Ir.TitledKind)
    (parent : Ir.ColorPair) :
    titledBodyPaint pal kind parent = (Ir.Design.ofPalette pal).titledBodyPaint kind parent := by
  rfl

@[expose] public def titledPadding : Length := Ir.titledPadding

/-- A painted block colour box as CSS: `titledPadding` on every side, reaching beyond the
measure. -/
public def titledBoxPaint : String :=
  s!"padding: {cssLength titledPadding}; margin-inline: -{cssLength titledPadding};"

public def titledBodyBoxPaint : String :=
  s!"padding: 0 {cssLength titledPadding} {cssLength titledPadding}; " ++
    s!"margin-inline: -{cssLength titledPadding};"

/-- The title page's slots, pinned on the deck's stage at the points the page places them. -/
public def titleSlotCss (doc : Doc) : String :=
  let slots := ((doc.styles.find? "titlepage").getD {}).slots
  if slots.isEmpty || doc.docClass != .slides then "" else
  let body := max doc.page.fontSize 1
  let emOf (l : Dim.Length) : String :=
    let e := if l.ex != 0 then s!" + {decMilli l.ex}ex" else ""
    s!"{decMilli (l.em + l.sp * 1000 / body)}em{e}"
  let zero : Dim.Length := {}
  let rules := slots.zipIdx.toList.filterMap fun (sl, i) =>
    let (slotWidth, place) := sl.box
    place.map fun pl =>
      let sel := s!"section.slide.title-page > .{roleClass (Ir.titleSlotRole i)}"
      let outer := Dim.Length.ofSp Ir.pgfOuterSep
      let anchorOffset (s : Nat × Nat) : Dim.Length :=
        outer.scale ((s.2 : Int) - (s.1 : Int)) (s.1 + s.2)
      let dx := ((pl.xshift.map (·.width)).getD zero).add
        (anchorOffset pl.anchor.hshares)
      let dy := (pl.yshift.map (·.width)).getD zero
      -- TikZ's `yshift` is up; the stage's `top` grows down
      let up0 : Dim.Length := { sp := -dy.sp, em := -dy.em, ex := -dy.ex }
      let up := up0.add (anchorOffset pl.anchor.vshares)
      let sep := (pl.innerSep.map (·.width)).getD
        (Dim.Length.ofSp (Ir.pgfInnerSep doc.page.fontSize))
      let width := match slotWidth with
        | some w => s!" width: {emOf w.width};"
        | none => ""
      s!"{sel} \{ position: absolute; margin: 0;\n" ++
      s!"  left: calc({decMilli (Ir.shareOf pl.pagePoint.hshares 100000)}% + {emOf dx});\n" ++
      s!"  top: calc({decMilli (Ir.shareOf pl.pagePoint.vshares 100000)}% + {emOf up});\n" ++
      s!"  transform: translate(-{decMilli (Ir.shareOf pl.anchor.hshares 100000)}%, \
-{decMilli (Ir.shareOf pl.anchor.vshares 100000)}%);\n" ++
      s!"  padding: {emOf sep};{width} }\n"
  "@media screen, print { section.slide.title-page { position: relative; }\n" ++
  String.join rules ++
  "section.slide.title-page > [class^=\"u-titlepage-slot-\"] h1 {\n" ++
  "  font-size: 1em; font-weight: inherit; margin: 0; }\n" ++
  "section.slide.title-page > [class^=\"u-titlepage-slot-\"] p { margin: 0; } }\n"

/-- A block template's length in the page's own unit, its `em` and `ex` parts kept. -/
public def shapeLengthCss (deck : Bool) (page : Ir.PageSpec) (g : SymGlue) : String :=
  let l := g.width
  let sp : String := if deck then s!"{decMilli (deckStageMilli l.sp page.height)}vh"
    else milliRem (screenMilli page.fontSize l.sp)
  let parts := (if l.sp != 0 then [sp] else []) ++
    (if l.em != 0 then [s!"{decMilli l.em}em"] else []) ++
    (if l.ex != 0 then [s!"{decMilli l.ex}ex"] else [])
  match parts with
  | [] => "0rem"
  | [one] => one
  | many => "calc(" ++ String.intercalate " + " many ++ ")"

public def blockShapeLength (doc : Doc) (g : SymGlue) : String :=
  shapeLengthCss (doc.docClass.record.model == .frame) doc.page g

/-- Each block kind's template boxes, rules and skips, as the stylesheet sets them. -/
public def blockShapeCss (doc : Doc)
    (titleRule : Ir.TitledKind → Ir.BlockReach → Option Ir.BlockTitlePlace := fun _ _ => none)
    (lit : Ir.Color → String := cssColor) : String :=
  let shapes := [Ir.TitledKind.block, .alert, .example].filterMap fun k =>
    (Ir.blockShapeOf doc.styles k).map (k, ·)
  if shapes.isEmpty then "" else
  let len := blockShapeLength doc
  let skips (sk : Array Ir.BlockSkip) : String := len (Ir.blockSkipSum doc.tokens sk)
  let measures := Dim.MeasureValues.horizontal (doc.page.width - 2 * doc.page.hmargin)
    (doc.page.height - 2 * doc.page.vmargin)
  let paint (e : Ir.BlockEdge) : String := match e.name with
    | some n => s!"var({n.property}, {cssColor e.color})"
    | none => lit e.color
  let rule (pseudo : String) (sel : String) (e : Ir.BlockEdge) (pad top bottom : String) : String :=
    let place := if e.side == .left then "left" else "right"
    s!"{sel}::{pseudo} \{ content: \"\"; position: absolute; top: {top}; bottom: {bottom}; \
{place}: calc({pad} - {len e.sep} - {len e.width}); width: {len e.width}; background: {paint e}; }\n"
  let rules := shapes.map fun (k, sh) =>
    let sel := s!"section.block-shaped.block-{k.name}"
    -- the `\parskip` a title spends inside the box it opens
    let inner := if sh.title.parskip && (sh.title.boxed || sh.whole.isSome) then peerGap else "0rem"
    let before := skips sh.before
    let after := skips sh.after
    let between := skips sh.between
    let edges (span : Ir.BlockSpan) := sh.edges.filter fun e =>
      e.span == span && (span == .title || !e.besideTitle)
    let boxRules (span : Ir.BlockSpan) (box : String) (place : Ir.BlockEdge → String × String) :
        String :=
      let es := edges span
      let padL := len (sh.inset span .left)
      let padR := len (sh.inset span .right)
      let left := (es.find? (·.side == .left)).map fun e =>
        rule "before" box e padL (place e).1 (place e).2
      let right := (es.find? (·.side == .right)).map fun e =>
        rule "after" box e padR (place e).1 (place e).2
      (if es.isEmpty then "" else
        s!"{box} \{ position: relative; padding-inline: {padL} {padR}; }\n") ++
      left.getD "" ++ right.getD ""
    let places := (sh.edges.filter (·.besideTitle)).toList.filterMap fun e => titleRule k e.reach
    let room := (places.map (·.room)).foldl max 0
    let below := if room == 0 then between else s!"calc({between} + {len { width := .ofSp room }})"
    let rise := (places.map (·.rise)).foldl max 0
    let riseMany := (places.map (·.riseMany)).foldl max 0
    let raised (base : String) (r : Int) : String :=
      if r == 0 then base else s!"calc({base} + {len { width := .ofSp r }})"
    let boxTop := raised inner rise
    let titlePlace (r : Int) (e : Ir.BlockEdge) : String × String := match e.reach with
      | .box => (raised peerGap r, below)
      | .lines .. =>
        let p := (titleRule k e.reach).getD default
        (s!"calc({peerGap} + {raised inner r} + {len { width := .ofSp p.top }})",
         s!"calc({below} + {len { width := .ofSp p.bottom }})")
    let broken := s!"{sel} > header:has(br)"
    let titleRules := boxRules .title s!"{sel} > header" (titlePlace rise) ++
      (if riseMany == rise then "" else
        s!"{broken} \{ padding-top: calc({peerGap} + {raised inner riseMany}); }\n" ++
        String.join ([Ir.FlushSide.left, .right].filterMap fun side =>
          ((edges .title).find? (·.side == side)).map fun e =>
            let pseudo := if side == .left then "before" else "after"
            s!"{broken}::{pseudo} \{ top: {(titlePlace riseMany e).1}; }\n"))
    let wholeRules := boxRules .whole sel fun _ => (s!"calc({before} + {peerGap})", after)
    let wholeLines := sh.edges.filter fun e => e.span == .whole && e.besideTitle
    let lineRules := String.join (wholeLines.toList.map fun e =>
      let pseudo := if e.side == .left then "before" else "after"
      let p := (titleRule k e.reach).getD default
      let pad := len (sh.inset .title (if e.side == .left then .left else .right))
      let top (r : Int) : String :=
        s!"calc({before} + {peerGap} + {raised inner r} + {len { width := .ofSp p.top }})"
      let bottom := s!"calc({after} + var(--block-last-below, {len { width := .ofSp p.bodyBelow }}) - \
{len { width := .ofSp p.depth }})"
      rule pseudo sel e pad (top rise) bottom ++
        (if riseMany == rise then "" else
          s!"{sel}:has(> header br)::{pseudo} \{ top: {top riseMany}; }\n") ++
        s!"{sel}:not(:has(> header))::{pseudo} \{ content: none; }\n")
    let lineBox := if wholeLines.isEmpty then "" else s!"{sel} \{ position: relative; }\n"
    -- an untitled block whose template leaves the title out
    let bare := match sh.bare with
      | some b =>
        let inside := if sh.whole.isSome then
            s!" + {skips b.between}" ++ (if sh.whole == some true then s!" + {peerGap}" else "")
          else ""
        s!"{sel}:not(:has(> header)) \{ padding-top: calc({skips b.before} + {peerGap}{inside}); }\n" ++
        (if (edges .whole).isEmpty then "" else
          String.join ((edges .whole).toList.map fun e =>
            let pseudo := if e.side == .left then "before" else "after"
            s!"{sel}:not(:has(> header))::{pseudo} \{ top: calc({skips b.before} + {peerGap}); }\n"))
      | none =>
        let hd := s!"{sel} > header:empty"
        let leading := Ir.blockTitleLeading doc.page.scale doc.page.fontSize doc.page.leading
          measures (Ir.blockTitleFont doc.styles k)
        let strut := len { width := leading }
        let (height, top) :=
          if sh.title.strut then
            (strut, if sh.title.boxed then s!"calc({peerGap} + {boxTop})" else peerGap)
          else if sh.title.boxed then ("1lh", peerGap) else ("0rem", "0rem")
        s!"{hd} \{ box-sizing: content-box; min-height: {height}; padding-top: {top}; }\n" ++
          (if sh.title.strut || (edges .title).isEmpty then "" else
            s!"{hd}::before \{ content: none; }\n{hd}::after \{ content: none; }\n")
    s!"{sel} \{ padding-top: {before}; padding-bottom: {after}; }\n" ++
      s!"{sel} > header \{ padding-top: calc({peerGap} + {boxTop}); padding-bottom: {below}; }\n" ++
      titleRules ++ wholeRules ++ lineBox ++ lineRules ++ bare
  String.join rules

/-- A tcolorbox length, in TeX millimetres, as CSS at the body size. -/
private def tcbLength (v : Int) : String := milliRem (screenMilli Ir.baseFontSize v)

/-! ## Colour roles -/

@[expose] public def roleVar (r : Ir.Role) : String := "--" ++ (Ir.CssName.role r).ident

@[expose] public def roleRef (r : Ir.Role) : String := "var(" ++ roleVar r ++ ")"

private def roleRefOr (r : Ir.Role) (fallback : String) : String :=
  "var(" ++ roleVar r ++ ", " ++ fallback ++ ")"

@[expose] public def Config.declares (cfg : Config) (r : Ir.Role) : Bool :=
  cfg.declarable[r.ctorIdx]?.getD true

/-- A named colour as an element's style reads it: its custom property with the literal as
fallback, or the literal alone for a role the page cannot declare. -/
@[expose] public def colorRead (cfg : Config) (name : Option Ir.ColorRef) (c : Ir.Color) :
    String :=
  match name with
  | some (.role r) => if cfg.declares r then s!"var({roleVar r}, {cssColor c})" else cfg.literal c
  | some n => s!"var({n.property}, {cssColor c})"
  | none => cfg.literal c

public theorem colorRead_names (cfg : Config) (n : Ir.ColorRef) (c : Ir.Color)
    (h : ∀ r, n = .role r → cfg.declares r = true) :
    colorRead cfg (some n) c = s!"var({n.property}, {cssColor c})" := by
  cases n with
  | role r => simp only [colorRead, h r rfl, ite_true]; rfl
  | color m => rfl

public def Config.paint (cfg : Config) (name : Option Ir.ColorRef) (c : Ir.Color) : String :=
  match name with
  | some _ => colorRead cfg name c
  | none => cfg.literal c

@[expose] public def cssDeclValue : Ir.CssDecl → String
  | .value c => cssColor c
  | .alias r => roleRef r

/-- The screen scheme a page's `:root` holds: its own screen, else that screen's more contrast,
else the first shipped screen, else light. -/
public def floorScheme (frames : List Ir.SchemeFrame) (home : Ir.Scheme) : Ir.Scheme :=
  let homeMore := if home.onDark then Ir.Scheme.darkMore else .lightMore
  if frames.any (·.scheme == home) then home
  else if frames.any (·.scheme == homeMore) then homeMore
  else ((frames.find? (·.scheme != .print)).map (·.scheme)).getD .light

/-- The palette in force as each shipped scheme ships it; the light screen alone outside the
engine's stylesheet. -/
public def Config.tables (cfg : Config) : List (Ir.Scheme × Ir.Palette) :=
  if cfg.frames.isEmpty then [(.light, cfg.pal)]
  else cfg.frames.zip cfg.views |>.map fun (f, v) => (f.scheme, v)

public def Config.floorPal (cfg : Config) : Ir.Palette :=
  ((cfg.tables.find? (·.1 == cfg.floor)).map (·.2)).getD cfg.pal

public def Config.ships (cfg : Config) (s : Ir.Scheme) : Bool :=
  cfg.frames.any (·.scheme == s)

/-- A role's text in one scheme's view, as the page's `:root` states it. -/
public def rootText (codeRoot : CodeRoot)
    (v : Ir.Palette) (s : Ir.Scheme) (r : Ir.Role) : Option String :=
  match r.code?, codeRoot.lookup s with
  | some _, some rs => ((rs.lookup r).join).map fun (c, key) => match key with
    | some k => roleRef k
    | none => cssColor c
  | _, _ => (Ir.Design.cssDecl v s r).map cssDeclValue

/-- The custom properties a page declares for its colours, with their texts in one scheme's view. -/
public def schemeProps (v : Ir.Palette) (s : Ir.Scheme) (roles : List Ir.Role)
    (codeRoot : CodeRoot := []) :
    List (String × Option String) :=
  roles.map (fun r => (roleVar r, rootText codeRoot v s r)) ++
    v.entries.toList.filterMap fun (n, c) => match n with
      | .color _ => some (n.property, some (cssColor c))
      | .role _ => none

/-- What each shipped scheme restates over the page's floor, in `@supports` and media blocks. -/
public def schemeBlocksOf (props : Ir.Scheme → Option (List (String × Option String)))
    (floor : Ir.Scheme) (scheme : Bool := true) (printDark : Bool := false) : String :=
  let floorT := (props floor).getD []
  let names := floorT.map (·.1)
  let textIn (t : List (String × Option String)) (p : String) : Option String := (t.lookup p).join
  let decl (ind p : String) (t : Option String) := s!"{ind}{p}: {t.getD "initial"};\n"
  -- the properties a block restates: those it changes, and those `forced`
  let pairs (ind : String) (l d lb db : List (String × Option String)) (forced : List String) :
      List String × String :=
    let rows := names.filterMap fun p =>
      let (a, b) := (textIn l p, textIn d p)
      if (a, b) == (textIn lb p, textIn db p) && !forced.contains p then none else
      match a, b with
      | some a, some b => some (p, if a == b then s!"{ind}{p}: {a};\n"
          else s!"{ind}{p}: light-dark({a}, {b});\n")
      | _, _ => some (p, decl ind p (if floor.onDark then b else a))
    (rows.map (·.1), String.join (rows.map (·.2)))
  let plain (ind : String) (t : List (String × Option String)) (forced : List String) :
      List String × String :=
    let rows := names.filterMap fun p =>
      let x := textIn t p
      if x == textIn floorT p && !forced.contains p then none else some (p, decl ind p x)
    (rows.map (·.1), String.join (rows.map (·.2)))
  -- a polarity with no plain screen reads the floor when the floor has that polarity
  let lightT := (props .light).orElse fun _ => if floor.onDark then none else some floorT
  let darkT := (props .dark).orElse fun _ => if floor.onDark then some floorT else none
  let (ldNames, lightDark) := match lightT, darkT with
    | some l, some d =>
      let (ns, body) := pairs "    " l d floorT floorT []
      (ns, if !scheme && body.isEmpty then "" else
        "@supports (color: light-dark(#000, #fff)) {\n  :root {\n" ++
          (if scheme then "    color-scheme: light dark;\n" else "") ++ body ++ "  }\n}\n")
    | _, _ => ([], "")
  -- under more contrast: the floor polarity's more scheme plainly, then each polarity's as pairs
  let floorMore := if floor.onDark then Ir.Scheme.darkMore else .lightMore
  let otherMore := if floor.onDark then Ir.Scheme.lightMore else .darkMore
  let (plainNames, morePlain) := ((props floorMore).map (plain "    " · [])).getD ([], "")
  let screens := lightT.isSome && darkT.isSome
  let baseL := if screens then lightT.getD floorT else floorT
  let baseD := if screens then darkT.getD floorT else floorT
  -- the other polarity's more scheme opens the block even without its plain screen
  let opens := !screens && (props otherMore).isSome
  let (moreNames, moreLd) :=
    if !(screens || opens) || ((props .lightMore).isNone && (props .darkMore).isNone) then ([], "")
    else
      let moreL := (props .lightMore).getD baseL
      let moreD := (props .darkMore).getD baseD
      let (ns, body) := pairs "      " moreL moreD baseL baseD plainNames
      (ns, if body.isEmpty && !opens then "" else
        (if opens && scheme then "      color-scheme: light dark;\n" else "") ++ body)
  let more := if morePlain.isEmpty && moreLd.isEmpty then "" else
    "@media (prefers-contrast: more) {\n" ++
      (if morePlain.isEmpty then "" else "  :root {\n" ++ morePlain ++ "  }\n") ++
      (if moreLd.isEmpty then "" else
        "  @supports (color: light-dark(#000, #fff)) {\n    :root {\n" ++ moreLd ++ "    }\n  }\n") ++
      "}\n"
  -- print restates what other blocks move, since they stay in force when printing
  let touched := ldNames ++ plainNames ++ moreNames
  let print := match props .print with
    | some pr =>
      let (_, body) := plain "    " pr touched
      if !scheme && body.isEmpty then "" else
      "@media print {\n  :root {\n" ++
        (if scheme then s!"    color-scheme: {if printDark then "dark" else "light"};\n" else "") ++
        body ++ "  }\n}\n"
    | none => ""
  lightDark ++ more ++ print

public def schemeBlocks (tables : List (Ir.Scheme × Ir.Palette)) (floor : Ir.Scheme)
    (roles : List Ir.Role) (codeRoot : CodeRoot := []) :
    String :=
  schemeBlocksOf (fun s => (tables.find? (·.1 == s)).map fun (_, v) =>
      schemeProps v s roles codeRoot) floor
    (printDark := (tables.lookup .print).any (·.darkPage))

public def propText (v : Ir.Palette) (s : Ir.Scheme) (prop : Ir.ColorRef) : Option String :=
  match prop with
  | .role r => (Ir.Design.cssDecl v s r).map cssDeclValue
  | .color _ => (v.lookup prop).map cssColor

private def bytesAt (b pat : ByteArray) (i : Nat) : Bool := Id.run do
  if b.size < i + pat.size then return false
  for k in [0:pat.size] do
    if (b[i + k]?.getD 0) != (pat[k]?.getD 0) then return false
  return true

/-- A byte a custom property's name holds: an ASCII letter or digit, `-` or `_`. -/
private def nameByte (c : UInt8) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 45 || c == 95

/-- Where `pat` (non-empty) stands in `b`, every byte offset in order. -/
private def bytePositions (b pat : ByteArray) : Array Nat := Id.run do
  let mut out := #[]
  let first := (pat[0]?.getD 0)
  for i in [0:b.size] do
    if (b[i]?.getD 0) == first && bytesAt b pat i then out := out.push i
  return out

/-- The end of the name a custom property's spelling starts at `j`. -/
private def nameEnd (b : ByteArray) (j : Nat) : Nat := Id.run do
  let mut k := j
  for _ in [j:b.size] do
    if k < b.size && nameByte (b[k]?.getD 0) then k := k + 1 else break
  return k

/-- Every custom property a CSS text reads with `var(--<name>`, in order. -/
public def varReads (css : String) : Array String := Id.run do
  let mut out : Array String := #[]
  if !css.contains "var(" then return out
  let b := css.toUTF8
  let mut from_ := 0
  for i in bytePositions b "var(".toUTF8 do
    if from_ ≤ i then
      let mut j := i + 4
      for _ in [j:b.size] do
        if j < b.size && (b[j]?.getD 0) == 32 then j := j + 1 else break
      if j + 1 < b.size && (b[j]?.getD 0) == 45 && (b[j + 1]?.getD 0) == 45 then
        let k := nameEnd b j
        out := out.push (String.Pos.Raw.extract css ⟨j⟩ ⟨k⟩)
        from_ := k
  return out

private def roleVars : Std.HashMap String Ir.Role :=
  Ir.Role.all.foldl (fun m r => m.insert (roleVar r) r) {}

public def roleOfVar? (name : String) : Option Ir.Role := roleVars[name]?

/-- The roles a stylesheet's rules read, in registry order. -/
public def rolesRead (css : String) : List Ir.Role :=
  let reads := (varReads css).toList.filterMap roleOfVar?
  Ir.Role.all.filter reads.contains

/-- The roles a table must declare for a set of reads: the reads and every role their aliases
reach. -/
@[expose] public def cssRoles (pal : Ir.Palette) (schemes : List Ir.Scheme)
    (seed : List Ir.Role) : List Ir.Role :=
  Ir.Role.all.filter fun r => seed.any fun q => (Ir.Design.reach pal schemes q).contains r

public theorem cssRoles_closed (pal : Ir.Palette) (schemes : List Ir.Scheme)
    (seed : List Ir.Role) (s : Ir.Scheme) (hs : s ∈ schemes) :
    ∀ r ∈ cssRoles pal schemes seed, ∀ p,
      Ir.Design.cssDecl pal s r = some (.alias p) → p ∈ cssRoles pal schemes seed := by
  intro r hr p hp
  simp only [cssRoles, List.mem_filter, List.any_eq_true, List.contains_iff_mem] at hr ⊢
  obtain ⟨_, q, hq, hrq⟩ := hr
  exact ⟨List.contains_iff_mem.mp (Ir.Role.all_complete p),
    q, hq, Ir.Design.reach_covers pal schemes q r p s hs hrq hp⟩

public theorem role_css_projects (pal : Ir.Palette) (schemes : List Ir.Scheme)
    (seed : List Ir.Role) (s : Ir.Scheme) (hs : s ∈ schemes) (r : Ir.Role)
    (hr : r ∈ cssRoles pal schemes seed) :
    Ir.Design.chase (Ir.Design.restrict (Ir.Design.cssDecl pal s) (cssRoles pal schemes seed)) r =
      Ir.Design.at pal s r := by
  rw [Ir.Design.chase_restrict_exact _ _ (cssRoles_closed pal schemes seed s hs) r hr]
  exact Ir.Design.cssDecl_chase_exact pal s r

public theorem html_print_agree (doc pal : Ir.Palette) (stage : Bool) (schemes : List Ir.Scheme)
    (seed : List Ir.Role) (hs : Ir.Scheme.print ∈ schemes) (r : Ir.Role)
    (hr : r ∈ cssRoles (pal.view (doc.frame .print stage)).1 schemes seed) :
    Ir.Design.chase (Ir.Design.restrict (Ir.Design.cssDecl (pal.view (doc.frame .print stage)).1 .print)
        (cssRoles (pal.view (doc.frame .print stage)).1 schemes seed)) r =
      Ir.Design.at pal .print r := by
  rw [Ir.Palette.view_home pal _ (Ir.Palette.frame_print_home doc stage)] at hr ⊢
  exact role_css_projects pal schemes seed .print hs r hr

public theorem marker_css_agree (pal : Ir.Palette) (schemes : List Ir.Scheme)
    (seed : List Ir.Role) (hs : Ir.Scheme.light ∈ schemes)
    (hr : Ir.Role.marker ∈ cssRoles pal schemes seed) :
    Ir.Design.chase (Ir.Design.restrict (Ir.Design.cssDecl pal .light)
        (cssRoles pal schemes seed)) .marker =
      Ir.Design.at pal .print .marker := by
  rw [role_css_projects pal schemes seed .light hs .marker hr,
    Ir.Design.marker_print_light_exact]

/-- The declarations a page's stylesheet carries, in one scheme, for the roles the palette leaves
undeclared. -/
public def roleDefaultVars (pal : Ir.Palette) (s : Ir.Scheme) (roles : List Ir.Role)
    (codeRoot : CodeRoot := []) : List String :=
  roles.filterMap fun r =>
    if (Ir.Design.declared? pal r).isSome then none
    else (rootText codeRoot pal s r).map fun t => s!"    {roleVar r}: {t};"

/-! ## Page roles -/

/-- A style attribute's references: what its declarations read, and each custom property it
declares with what that reads. -/
private def styleRefs (style : String) : Array String × Array (String × Array String) :=
  if !style.contains "--" then (#[], #[]) else
  (style.splitOn ";").foldl (fun (acc : Array String × Array (String × Array String)) piece =>
    let t := piece.trimAscii.toString
    if t.startsWith "--" then
      match t.splitOn ":" with
      | name :: rest => (acc.1, acc.2.push (name.trimAscii.toString, varReads (":".intercalate rest)))
      | [] => acc
    else ((varReads t).foldl Array.push acc.1, acc.2)) (#[], #[])

mutual

/-- The custom properties an emitted tree reads, and the declarations its style attributes carry. -/
private def nodeRefsOne (acc : Array String × Array (String × Array String)) :
    Node → Array String × Array (String × Array String)
  | .elem _ attrs kids =>
    let acc := match attrs.find? (·.1 == "style") with
      | some (_, st) =>
        let (r, e) := styleRefs st
        (r.foldl Array.push acc.1, e.foldl Array.push acc.2)
      | none => acc
    nodeRefsList acc kids.toList
  | .style css => ((varReads css).foldl Array.push acc.1, acc.2)
  | .text _ | .script _ _ => acc

private def nodeRefsList (acc : Array String × Array (String × Array String)) :
    List Node → Array String × Array (String × Array String)
  | [] => acc
  | n :: ns => nodeRefsList (nodeRefsOne acc n) ns

end

/-- Whether some table gives a role a value in a shipped scheme. -/
private def roleDeclarable (tables : List (Ir.Scheme × Ir.Palette)) (r : Ir.Role) : Bool :=
  tables.any fun (s, p) => (Ir.Design.declared? p r).isSome || (Ir.Design.cssDecl p s r).isSome

/-- The roles a page declares: what it reads, closed under aliases, less those no table gives a
value. -/
public def pageRoleSet (tables : List (Ir.Scheme × Ir.Palette))
    (roots : List Ir.Role) (edges : Array (Ir.Role × List Ir.Role))
    (extra : Ir.Role → Bool := fun _ => false) : List Ir.Role := Id.run do
  let rows : List (Ir.Role × Ir.Role) := tables.flatMap fun (s, p) =>
    Ir.Role.all.filterMap fun r => match Ir.Design.cssDecl p s r with
      | some (.alias q) => some (r, q)
      | _ => none
  let mut set := roots
  for _ in [0:Ir.Role.all.length + 1] do
    let viaRows := (rows.filter fun (src, _) => set.contains src).map (·.2)
    let viaEdges := (edges.filter fun (src, _) => set.contains src).toList.flatMap (·.2)
    let next := Ir.Role.all.filter fun r => set.contains r || viaRows.contains r || viaEdges.contains r
    if next.length == set.length then break
    set := next
  return Ir.Role.all.filter fun r => set.contains r && (roleDeclarable tables r || extra r)

/-- One pass of `resolveRoleVars`, with whether it replaced anything. -/
private def resolveRoleVarsPass (keep : Ir.Role → Bool) (s : String) : String × Bool := Id.run do
  let b := s.toUTF8
  let mut out := ""
  let mut copied := 0
  let mut from_ := 0
  let mut changed := false
  for i in bytePositions b "var(--ltx-".toUTF8 do
    if from_ ≤ i then
      let j := nameEnd b (i + 4)
      let mut depth := 1
      let mut k := j
      let mut comma : Option Nat := none
      for _ in [j:b.size] do
        if b.size ≤ k then break
        let c := (b[k]?.getD 0)
        if c == 40 then depth := depth + 1
        else if c == 41 then
          depth := depth - 1
          if depth == 0 then break
        else if c == 44 && depth == 1 && comma.isNone then comma := some k
        k := k + 1
      if let some r := roleOfVar? (String.Pos.Raw.extract s ⟨i + 4⟩ ⟨j⟩) then
        if !keep r then
          changed := true
          let fallback := match comma with
            | some c0 => (String.Pos.Raw.extract s ⟨c0 + 1⟩ ⟨k⟩).trimAscii.toString
            | none => "initial"
          out := out ++ String.Pos.Raw.extract s ⟨copied⟩ ⟨i⟩ ++ fallback
          copied := k + 1
      from_ := k + 1
  if !changed then return (s, false)
  return (out ++ String.Pos.Raw.extract s ⟨copied⟩ ⟨b.size⟩, true)

/-- How many role reads a text spells, which bounds the passes `resolveRoleVars` needs. -/
private def roleReadCount (s : String) : Nat :=
  (bytePositions s.toUTF8 "var(--ltx-".toUTF8).size

/-- A CSS text with every read of a role outside `keep` replaced by its fallback, or `initial`. -/
public def resolveRoleVars (keep : Ir.Role → Bool) (s : String) : String := Id.run do
  if !s.contains "var(--ltx-" then return s
  let mut text := s
  for _ in [0:roleReadCount s] do
    let (t, changed) := resolveRoleVarsPass keep text
    if !changed then break
    text := t
  return text

/-- A style attribute with declarations of roles outside `keep` dropped and their reads resolved. -/
private def keepRoleStyle (keep : Ir.Role → Bool) (style : String) : String :=
  if !style.contains "--ltx-" then style else
  let pieces := (style.splitOn ";").filter fun piece =>
    let t := piece.trimAscii.toString
    match (t.splitOn ":").head? with
    | some name => match roleOfVar? name.trimAscii.toString with
      | some r => !t.startsWith "--" || keep r
      | none => true
    | none => true
  resolveRoleVars keep (";".intercalate pieces)

mutual

/-- An emitted tree with every style attribute kept to the page's roles. -/
private def keepRolesOne (keep : Ir.Role → Bool) : Node → Node
  | .elem tag attrs kids =>
    .elem tag (attrs.map fun (k, v) => if k == "style" then (k, keepRoleStyle keep v) else (k, v))
      (keepRolesList keep #[] kids.toList)
  | .style css => .style (resolveRoleVars keep css)
  | n@(.text _) => n
  | n@(.script _ _) => n

private def keepRolesList (keep : Ir.Role → Bool) (acc : Array Node) : List Node → Array Node
  | [] => acc
  | n :: ns => keepRolesList keep (acc.push (keepRolesOne keep n)) ns

end

/-- Read-only aliases of the roles under the engine's reader names, and each author colour's own
name. -/
private def readerAliases (pal : Ir.Palette) (roles : List Ir.Role) (taken : List String := []) :
    List String :=
  let roleNames : List (String × Ir.Role) :=
    [("fg", .ink), ("bg", .page), ("muted", .muted), ("ink", .ink), ("surface", .page),
     ("accent", .accent), ("tint", .codeSurface), ("rule", .rule)]
  let authored (n : String) := pal.colors.any (·.1 == n)
  -- an author colour's name is skipped where the engine reads that property itself
  let free (n : String) := !taken.contains ("--" ++ n) && !n.startsWith "ltx-"
  (roleNames.filter fun (n, r) => roles.contains r && !authored n && free n).map
      (fun (n, r) => s!"    --{n}: {roleRef r};") ++
    (pal.colors.toList.filter fun (n, _) => free n && (tokenVar? n).isSome).map
      fun (n, _) => s!"    --{n}: var({(Ir.ColorRef.color n).property});"

/-- A stage length as its share of the stage's height, in `vh`. -/
private def stageVh (page : PageSpec) (x : Sp) : String :=
  s!"{decMilli (deckStageMilli x page.height)}vh"

/-- A length a class's lineage fixes, in the page's own unit. -/
private def lineageLength (doc : Doc) (x : Sp) : String :=
  if doc.docClass.record.model == .frame then stageVh doc.page x
  else milliRem (screenMilli doc.page.fontSize x)

/-- The trivlist's and the float's spaces at a list depth in beamer's lineage, in the page's
unit. -/
private def lineageSkipDecls (doc : Doc) (depth : Nat) (squeezed : Bool := false) : String :=
  let size := doc.page.fontSize
  let t := (Ir.trivlistSkipFor .beamer doc.tokens size depth).width.resolve size 0
  let float := match Ir.floatSpaceFor .beamer doc.tokens size depth with
    | (_, true) => if squeezed then s!"calc({lineageLength doc t} + var(--parskip, 0rem))"
      else s!"calc(var(--{Ir.trivlistSkipName}) + var(--parskip, 0rem))"
    | (g, false) => lineageLength doc (g.width.resolve size 0)
  -- a squeezed frame keeps beamer's `\topsep0.5pt`; its floats keep their own space
  let topsep := if squeezed then Ir.squeezedTopsep.width.resolve size 0 else t
  s!"--{Ir.trivlistSkipName}: {lineageLength doc topsep}; --floatsep: {float};"

private def anySqueezed (doc : Doc) : Bool :=
  Ir.foldBlocks (fun acc b => acc || match b with
      | .frame _ _ _ _ fbody => Ir.frameSqueeze fbody != .none
      | _ => false)
    (fun acc _ => acc) false doc.body

/-- In beamer's lineage, the top level's trivlist and float spaces on the root. -/
private def lineageSkipVars (doc : Doc) : String :=
  match doc.docClass.record.lists with
  | .beamer => s!"    {lineageSkipDecls doc 0}\n"
  | .sizeFile | .web => ""

/-- Each list level's spaces in beamer's lineage. -/
private def lineageLevelRules (doc : Doc) : String :=
  match doc.docClass.record.lists with
  | .beamer =>
    let within := ["li", "dd", "blockquote"]
    let deep := within.flatMap fun o => within.map (o ++ " " ++ ·)
    let sq (sels : List String) := sels.map ("section.slide.squeeze " ++ ·)
    s!"{", ".intercalate within} \{ {lineageSkipDecls doc 1} }\n" ++
    s!"{", ".intercalate deep} \{ {lineageSkipDecls doc 2} }\n" ++
    (if anySqueezed doc then
      s!"{", ".intercalate (sq within)} \{ {lineageSkipDecls doc 1 true} }\n" ++
      s!"{", ".intercalate (sq deep)} \{ {lineageSkipDecls doc 2 true} }\n"
    else "")
  | .sizeFile | .web => ""

/-- The footline band's box as the stage lengths `footlineCss` reads. -/
private def footBoxDecls (page : PageSpec) : Option (Sp × Sp) → List String
  | some (h, d) => [s!"--foot-h: {stageVh page h};", s!"--foot-d: {stageVh page d};"]
  | none => []

/-- The frame title's size step: the `frametitle` font template's, else Large. -/
private def frameTitleStep (doc : Doc) : String :=
  match (doc.styles.find? "frametitle").bind (·.font) with
  | some tpl => milliFactor (Ir.templateSize (1000 : Dim.Sp) tpl).toNat
  | none => stepFactor "Large"

/-- moloch's frame-title box on the stage, as the PDF builds it. -/
private def frameTitleStrutCss (hdr : String := "section.slide > header") : String :=
  let pad := s!"var(--frametitlepadding, {cssLength Ir.frameTitlePadding.width})"
  s!"{hdr} h2::before \{ content: \"\"; display: inline-block;\n" ++
  s!"  height: calc({pad} + {decMilli (Ir.frameTitleStrut 1000)}em); }\n" ++
  s!"{hdr} h2::after \{ content: \"\"; display: inline-block;\n" ++
  s!"  vertical-align: calc(-1 * {pad}); }\n"

/-- moloch's footline (beamerouterthememoloch.sty), standing on the stage's bottom edge. -/
private def footlineCss (page : PageSpec) : String :=
  let raise := stageVh page Ir.footline.raise
  let step := milliFactor (Ir.scaleStepIn page.scale 1000 Ir.footline.step).toNat
  "section.slide > footer.slide-foot { position: relative; order: 1;\n" ++
  s!"  margin: 0 calc(-1 * {safeareaVar}); line-height: 0;\n" ++
  "  font-weight: var(--ltx-body-weight, normal);\n" ++
  s!"  color: {roleRef .footInk}; background: {roleRefOr .footBand "transparent"}; }\n" ++
  s!"section.slide.standout > footer.slide-foot \{ font-size: calc({step}em / \
{stepFactor standoutStep}); }\n" ++
  "footer.slide-foot::before { content: \"\"; display: inline-block;\n" ++
  s!"  height: calc(var(--foot-h, var(--foot-cap, 1) * 1cap) + var(--foot-d, 0px) + {raise}); }\n" ++
  s!"footer.slide-foot > .band-left \{ position: absolute; left: {stageVh page Ir.footline.left};\n" ++
  "  bottom: 0; white-space: nowrap; }\n" ++
  s!"footer.slide-foot > .band-right \{ position: absolute; right: {stageVh page Ir.footline.right};\n" ++
  "  bottom: 0; white-space: nowrap; }\n" ++
  "footer.slide-foot > :is(.band-left, .band-right)::before { content: \"\";\n" ++
  s!"  display: inline-block; height: calc(1cap + {raise} + var(--foot-d, 0px));\n" ++
  s!"  vertical-align: calc(-1 * ({raise} + var(--foot-d, 0px))); }\n" ++
  -- on screen the band stays on the stage's edge however far the content runs
  "@media screen { section.slide > footer.slide-foot { position: sticky; bottom: 0; } }\n"

/-- The furniture rules the semantic palette keys turn on, shared by every theme. -/
public def themeCss (doc : Doc)
    (titleRule : Ir.TitledKind → Ir.BlockReach → Option Ir.BlockTitlePlace := fun _ _ => none)
    (lit : Ir.Color → String := cssColor) : String :=
  let d := Design.ofDoc doc
  let sectionMeasure :=
    s!"min({stageVh doc.page (Ir.sectionPageMeasure (doc.page.width - 2 * doc.page.hmargin))}, 100%)"
  let declares (r : Ir.Role) : Bool :=
    (Ir.Design.declared? doc.palette r).isSome ||
      Ir.foldBlocks (fun a b => a || match b with
        | .setPalette p => (Ir.Design.declared? p r).isSome
        | _ => false) (fun a _ => a) false doc.body
  let barRules (hdr : String) : String :=
    s!"{hdr} \{ background: {roleRef .frameTitleBar};\n" ++
    s!"  color: {roleRef .frameTitleInk};\n" ++
    -- the bar sets at the title's step, so `frametitlepadding` resolves at the title's size
    s!"  font-size: {stepFactor "Large"}rem;\n" ++
    s!"  margin: -{slidePadV} -{slidePadH} 0;\n" ++
    s!"  padding: var(--frametitlepadding, {quantaRem 1}) {slidePadH};\n" ++
    s!"  border-radius: {slideRadiusPx - slideBorderPx}px {slideRadiusPx - slideBorderPx}px 0 0; }\n" ++
    s!"{hdr} h2 \{ color: inherit; font-size: 1em; }\n" ++
    -- the paged deck's slide is cornerless; the bar bleeds through the safe area
    (if doc.docClass == .slides then
      s!"@media screen, print \{ {hdr} \{ border-radius: 0;\n" ++
      -- the deck sets type in `vh`, so the bar retakes the title step in `em`
      s!"  font-size: {frameTitleStep doc}em;\n" ++
      (if doc.chromeAllowed then s!"  margin: 0 calc(-1 * {safeareaVar}) 0;\n"
       else s!"  margin: calc(-1 * {safeareaVar}) calc(-1 * {safeareaVar}) 0;\n") ++
      (if (doc.tokens.find? "frametitlepadding").isSome then
        -- moloch's bar spans the paper, its title inset by `Ir.frameTitleInset`
        s!"  padding: 0 {decMilli (Ir.frameTitleInset 1000)}em; line-height: \
{decMilli (Ir.leadingFor 1000)}; } }\n" ++
        frameTitleStrutCss hdr
       else s!"  padding: var(--frametitlepadding, {quantaRem 1}) {safeareaVar}; } }\n")
     else "")
  -- paint comes from each block's palette epoch
  "section.block > header { font-weight: bold; }\n" ++
  -- a colour box is a flow root: no margin collapses through its edge
  "section.block, section.block > .block-body { display: flow-root; }\n" ++
  -- tcolorbox's box: its rules, `boxsep` and insets as `Ir.tcb…` states them
  "section.tcolorbox, section.tcolorbox > .tcolorbox-body { display: flow-root; }\n" ++
  s!"section.tcolorbox > header \{ padding: {tcbLength (Ir.tcbRule + Ir.tcbBoxsep)} {tcbLength Ir.tcbInset}; }\n" ++
  s!"section.tcolorbox > .tcolorbox-body \{ padding: {tcbLength (Ir.tcbBoxsep + Ir.tcbTop)} {tcbLength Ir.tcbInset} {tcbLength (Ir.tcbBottom + Ir.tcbBoxsep + Ir.tcbRule)}; }\n" ++
  s!"section.tcolorbox > .tcolorbox-body:first-child \{ padding-top: {tcbLength (Ir.tcbRule + Ir.tcbBoxsep + Ir.tcbTop)}; }\n" ++
  s!"{blockAt "first-child"} \{ --frame-body-before: calc({milliFactor (blockAboveMilli doc.page.fontSize doc.tokens)}rem - var(--parskip, 0rem)); }\n" ++
  (if d.frametitle.isSome then barRules "section.slide > header" else
    -- an undeclared title ink inherits, as every heading's does
    (if declares .frameTitleInk then
      s!"section.slide > header \{ color: {roleRef .frameTitleInk}; }\n" else "") ++
    "section.slide > header h2 { color: inherit; }\n" ++
    -- with no bar the title is the page's first line, at the slides' top margin
    (if doc.chromeAllowed then
      "@media screen, print { section.slide:not(.title-page) > header {\n" ++
      s!"  padding-top: {stageVh doc.page doc.page.vmargin}; } }\n"
     else "") ++
    -- beamer's default frametitle box ends 1ex above the title strut's depth
    (if doc.docClass.record.model == .frame then
      "section.slide:not(.title-page):not(.titlebar) > header h2 \
{ text-box: trim-end text alphabetic; }\n" ++
      s!"section.slide:not(.title-page):not(.titlebar):has(> header) \{ --frame-title-below: \
calc({stepFactor Ir.plainFrameTitleStep} * \
({decMilli (Ir.defaultFrameTitleBelow 1000 doc.page.leading 0)}em - 1ex)); }\n"
     else "") ++
    (if declares .frameTitleBar then barRules "section.slide.titlebar > header" else "")) ++
  -- the poster's headline band: title matter between two equal tracks, logos in the corners
  (match doc.headline with
   | some _ =>
     let side : Ir.HAlign := ((doc.styles.find? "titlepage").bind (·.align)).getD .center
     let pad := s!"gap: {quantaRem 2}; padding: {quantaRem 2} {quantaRem 3}; }\n"
     (if side == .center then
       "body > header.headline { display: grid; grid-template-columns: 1fr auto 1fr;\n" ++
       "  align-items: center; " ++ pad ++
       "body > header.headline > .headline-matter { grid-area: 1 / 2; text-align: center; }\n" ++
       "body > header.headline > .headline-logo:first-child { grid-area: 1 / 1;\n" ++
       "  justify-self: start; }\n" ++
       "body > header.headline > .headline-matter ~ .headline-logo { grid-area: 1 / 3;\n" ++
       "  justify-self: end; }\n"
      else
       "body > header.headline { display: flex; align-items: center;\n  " ++ pad ++
       s!"body > header.headline .headline-matter \{ flex: 1; text-align: {side.align}; }\n") ++
     "body > header.headline h1 { margin: 0; }
" ++
     (if d.frametitle.isSome then
       s!"body > header.headline \{ background: {roleRef .frameTitleBar};
" ++
       s!"  color: {roleRef .frameTitleInk}; }
" ++
       "body > header.headline h1 { color: inherit; }
"
      else "")
   | none => "") ++
  -- the title page's ground, only where the design declares it
  (match d.titlepage with
   | some _ =>
     s!"section.slide.title-page \{ background: {roleRef .titlePageGround};\n" ++
     s!"  color: {roleRef .titlePageInk}; }\n" ++
     "section.slide.title-page h1 { color: inherit; }\n"
   | none => "") ++
  titleSlotCss doc ++
  blockShapeCss doc titleRule lit ++
  -- emitted for every frame deck, since later palette epochs may use it
  (if doc.docClass.record.model == .frame then
    s!"section.section-page \{ text-align: center; padding: {quantaRem 3} 0;\n" ++
    "  break-inside: avoid; }\n" ++
    -- title and bar share moloch's centred measure, as the PDF's
    "section.section-page h2 { display: inline-block; text-align: left;\n" ++
    s!"  width: {sectionMeasure}; margin: 0; color: {roleRef .sectionTitleInk}; }\n" ++
    -- `progressheight`, with moloch's own 1pt fallback
    s!".progress \{ background: {roleRef .sectionProgressTrack};\n" ++
    "  height: var(--progressheight, 1pt);\n" ++
    s!"  width: {sectionMeasure}; margin: {quantaRem 1} auto 0; }\n" ++
    s!".progress > div \{ background: {roleRefOr .sectionProgressFill "transparent"}; height: 100%; }\n" ++
    -- moloch's section page closes on the subsection title's strut below its bar
    (if doc.chromeAllowed then
      s!"section.section-page::after \{ content: \"\"; flex: none; \
height: calc({decMilli (Ir.sectionPageStrut 1000 doc.page.leading)}em - var(--progressheight, 1pt)); }\n"
     else "") ++
    -- the deck's progress hairline, scroll-driven where supported, screen only
    (if doc.docClass == .slides && d.progress.isSome then
      "@media screen { @supports (animation-timeline: scroll()) {\n" ++
      ".deck-progress { position: fixed; top: 0; left: 0; width: 100%;\n" ++
      s!"  height: var(--progressheight, 1pt); background: {roleRef .progressFill};\n" ++
      "  transform-origin: 0 50%;\n" ++
      "  animation: ltx-deck-progress linear both;\n" ++
      "  animation-timeline: scroll(root x); }\n" ++
      "@keyframes ltx-deck-progress { from { transform: scaleX(0) } \
to { transform: scaleX(1) } }\n" ++
      "} }\n" ++
      "@media print { .deck-progress { display: none; } }\n"
     else "") else "") ++
  -- the chrome footer: each slot pinned to its declared edge, collisions ranked by `z-index`
  (if doc.chromeAllowed &&
      (doc.chrome.hasFooter || doc.body.any fun b => match b with
        | .framefoot xs => !xs.isEmpty
        | _ => false) then
    footlineCss doc.page ++
    -- a named size inside a slot is the body's step, as TeX's size commands are absolute
    (let step := (Ir.scaleStepIn doc.page.scale 1000 Ir.footline.step).toNat
     String.join (doc.page.scale.map fun (name, k) =>
       s!"footer.slide-foot .size-{name} \{ font-size: \
{milliFactor (k * 1000 / max step 1)}em; }\n")) else "")

/-- One palette entry as the custom-property declaration `:root` carries. -/
private def paletteVar (n : Ir.ColorRef) (c : Ir.Color) : String :=
  "    " ++ n.property ++ ": " ++ cssColor c ++ ";"

public def paletteVars (p : Ir.Palette) : List String :=
  p.entries.toList.map fun (n, c) => paletteVar n c

private theorem hexDigit_inj :
    ∀ i < 16, ∀ j < 16,
      "0123456789abcdef".toList.getD i '0' = "0123456789abcdef".toList.getD j '0' →
        i = j := by
  decide

private theorem hexByte_inj (a b : UInt8)
    (h : Color.hexByte a false = Color.hexByte b false) : a = b := by
  have hl := congrArg String.toList h
  simp only [Color.hexByte, Bool.false_eq_true, ite_false, String.toList_ofList,
    List.cons.injEq, and_true] at hl
  have ha : a.toNat < 256 := a.toNat_lt
  have hb : b.toNat < 256 := b.toNat_lt
  have hdiv := hexDigit_inj (a.toNat / 16) (by omega) (b.toNat / 16) (by omega) hl.1
  have hmod := hexDigit_inj (a.toNat % 16) (by omega) (b.toNat % 16) (by omega) hl.2
  have : a.toNat = b.toNat := by omega
  exact UInt8.toNat_inj.mp this

public theorem cssColor_inj (a b : Ir.Color) (h : cssColor a = cssColor b) :
    a.r = b.r ∧ a.g = b.g ∧ a.b = b.b := by
  have hl := congrArg String.toList h
  simp only [cssColor, Color.css, Color.hexByte, Bool.false_eq_true, ite_false,
    String.toList_append, String.toList_ofList,
    List.cons_append, List.nil_append, List.append_assoc] at hl
  have hl6 := List.append_cancel_left hl
  simp only [List.cons.injEq, and_true] at hl6
  obtain ⟨hr1, hr2, hg1, hg2, hb1, hb2⟩ := hl6
  have har : a.r.toNat < 256 := a.r.toNat_lt
  have hag : a.g.toNat < 256 := a.g.toNat_lt
  have hab : a.b.toNat < 256 := a.b.toNat_lt
  have hbr : b.r.toNat < 256 := b.r.toNat_lt
  have hbg : b.g.toNat < 256 := b.g.toNat_lt
  have hbb : b.b.toNat < 256 := b.b.toNat_lt
  have er1 := hexDigit_inj _ (by omega) _ (by omega) hr1
  have er2 := hexDigit_inj _ (by omega) _ (by omega) hr2
  have eg1 := hexDigit_inj _ (by omega) _ (by omega) hg1
  have eg2 := hexDigit_inj _ (by omega) _ (by omega) hg2
  have eb1 := hexDigit_inj _ (by omega) _ (by omega) hb1
  have eb2 := hexDigit_inj _ (by omega) _ (by omega) hb2
  exact ⟨UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
    UInt8.toNat_inj.mp (by omega)⟩

public theorem role_use_is_palette_dependent (p : Ir.Palette) (r : Ir.ColorRef)
    (c₁ c₂ : Ir.Color) (hne : (c₁.r, c₁.g, c₁.b) ≠ (c₂.r, c₂.g, c₂.b)) :
    paletteVars (p.declare r c₁) ≠ paletteVars (p.declare r c₂) := by
  simp only [paletteVars, Ir.Palette.declare, Array.toList_push, List.map_append,
    List.map_cons, List.map_nil]
  intro h
  have hlast := List.append_cancel_left h
  simp only [List.cons.injEq, and_true] at hlast
  have hl := congrArg String.toList hlast
  simp only [paletteVar, String.toList_append, List.append_assoc] at hl
  have h1 := List.append_cancel_left hl
  have h2 := List.append_cancel_left h1
  have h3 := List.append_cancel_left h2
  have hrgb := cssColor_inj c₁ c₂ (String.ext (List.append_cancel_right h3))
  exact hne (by simp [hrgb.1, hrgb.2.1, hrgb.2.2])

/-- A slot's synthetic family name, never the face's own, so no installed font can substitute. -/
private def slotName : Nat → String
  | 0 => "body"
  | 1 => "sans"
  | 2 => "mono"
  | n => toString n

/-- The synthetic families face `i` serves: each slot resolving to it, and `ltx-math` for the
math face. -/
private def namedFamiliesOf (fs : Font.FontSet) (i : Nat) : List String :=
  let slots := fs.index.foldl (fun n e => max n (e.1.1 + 1)) 3
  ((List.range slots).filterMap fun s =>
    if fs.index.any (fun e => e.1.1 == s && e.2 == i) then
      some s!"ltx-{slotName s}"
    else none) ++
  (if fs.math == some i then ["ltx-math"] else [])

/-- The families face `i` ships under: its slots', or a fallback family of its own. -/
public def familiesOf (fs : Font.FontSet) (i : Nat) : List String :=
  if (namedFamiliesOf fs i).isEmpty then [s!"ltx-fb{i}"] else namedFamiliesOf fs i

public theorem familiesOf_ne_nil (fs : Font.FontSet) (i : Nat) : familiesOf fs i ≠ [] := by
  unfold familiesOf
  split
  · simp
  · next h => exact fun hn => h (by simp [hn])

/-- A slot's font stack: its own family, every other family in face order, then the generic. -/
private def stackFor (fs : Font.FontSet) (own generic : String) : String :=
  let rest := (((List.range fs.fonts.size).flatMap fun i =>
    familiesOf fs i).eraseDups.filter (· != own)).map fun f => s!"\"{f}\""
  String.intercalate ", " ([s!"\"{own}\""] ++ rest ++ [generic])

/-- The face's file name: its index and its PostScript name's safe characters. -/
private def fontFileName (i : Nat) (f : Font.Font) : String :=
  let safe := f.psName.toList.filter fun c =>
    c.isAlphanum || c == '-' || c == '_' || c == '.'
  s!"f{i}-{String.ofList safe}." ++ (if f.isCff then "otf" else "ttf")

public def fontResource (f : Font.Font) : HtmlResource.Embedded :=
  { media := if f.isCff then .otf else .ttf, bytes := f.data }

public def fontResources (fs : Font.FontSet) : Array HtmlResource.Embedded :=
  (Array.range fs.fonts.size).map fun i => fontResource (fs.get i)

/-- One `@font-face` the page ships: a face under one synthetic family, with the face's own
weight and italic flag. -/
public structure FontFace where
  index : Nat
  family : String
  weight : Nat
  italic : Bool
  file : String
  format : String
  deriving Repr, BEq

/-- The `@font-face` list: every face of the resolved set, under every synthetic family it
serves. -/
public def shipFaces (fs : Font.FontSet) : Array FontFace :=
  (Array.range fs.fonts.size).flatMap fun i =>
    (familiesOf fs i).toArray.map fun fam =>
      { index := i
        family := fam
        weight := (fs.get i).weight
        italic := (fs.get i).isItalic
        file := fontFileName i (fs.get i)
        format := if (fs.get i).isCff then "opentype" else "truetype" }

public theorem shipFaces_covers (fs : Font.FontSet) {k : Nat} (hk : k < fs.fonts.size) :
    ∃ ff ∈ shipFaces fs, ff.index = k := by
  obtain ⟨fam, rest, heq⟩ : ∃ a l, familiesOf fs k = a :: l := by
    cases h : familiesOf fs k with
    | nil => exact absurd h (familiesOf_ne_nil fs k)
    | cons a l => exact ⟨a, l, rfl⟩
  refine ⟨{ index := k, family := fam, weight := (fs.get k).weight
            italic := (fs.get k).isItalic, file := fontFileName k (fs.get k)
            format := if (fs.get k).isCff then "opentype" else "truetype" }, ?_, rfl⟩
  simp only [shipFaces, Array.mem_flatMap]
  refine ⟨k, by simpa using hk, ?_⟩
  simp only [Array.mem_map, List.mem_toArray]
  exact ⟨fam, by simp [heq], rfl⟩

/-- What this emitter realizes of the output contract. -/
public def profile : Ir.Realization :=
  { alternatives := .attribute
    color := .srgbByDefinition
    fonts := .ships
    scripting := .constantGated
    math := .mathmlCore }

public theorem html_default_contract_exact : ({} : Ir.OutputContract).unmet profile = #[] :=
  Ir.OutputContract.unmet_default_exact profile

/-- Artifact-specific. -/
public theorem shipFaces_src_shipped (fs : Font.FontSet) :
    ∀ ff ∈ shipFaces fs, fontResource (fs.get ff.index) ∈ fontResources fs := by
  intro ff hff
  simp only [shipFaces, Array.mem_flatMap] at hff
  obtain ⟨i, hi, hmem⟩ := hff
  simp only [Array.mem_map, List.mem_toArray] at hmem
  obtain ⟨fam, _, rfl⟩ := hmem
  exact Array.mem_map.mpr ⟨i, hi, rfl⟩

/-! ## Image resources -/

/-- A captured image's staging identity for report readers. -/
public structure ImageAsset where
  file : String
  srcIndex : Nat
  poster : Bool := false
  deriving Repr, BEq

private def basename (p : String) : String := (p.splitOn "/").getLastD p

/-- The path the driver resolved for an entry, else its spelling. -/
public def resolvedSrc (en : Image.Loaded) : String :=
  if en.href.isEmpty then en.src else en.href

/-- Whether an entry supplies a browser resource: a loaded image with a browser face, boundary
pictures aside. -/
public def imageShips (en : Image.Loaded) : Bool :=
  -- premise: Tests.svgAssetChecks — a failed conversion publishes no source bytes.
  -- premise: Tests.svgRasterFigureChecks — a drawn figure's raster ships in the figure's file.
  !en.src.startsWith Ir.picSrcPrefix && en.webError.isNone && en.rasterOf.isNone &&
  match en.info with
  | some i => i.form.isNone || Image.isSvg (resolvedSrc en) || en.webSvg.isSome
  | none => false

/-- A converted browser face's source: the source's basename with an SVG extension. -/
private def browserAssetSrc (en : Image.Loaded) : String :=
  if en.webSvg.isSome then ((System.FilePath.mk (resolvedSrc en)).withExtension "svg").toString
  else resolvedSrc en

private def imageFileName (kind : String) (k : Nat) (href : String)
    (data : Option ByteArray) : String :=
  let assetPrefix := kind ++ ListMark.arabicN k ++ "-" ++
    (data.map (fun bytes => Flate.contentKey bytes ++ "-")).getD ""
  -- Linux NAME_MAX is 255 bytes
  let budget := 255 - assetPrefix.utf8ByteSize
  let base := basename href
  let suffix := if base.utf8ByteSize ≤ budget then base else
    (base.toList.foldr (fun c (used, tail) =>
      let used := used + (String.singleton c).utf8ByteSize
      (used, if used ≤ budget then String.singleton c ++ tail else tail)) (0, "")).2
  assetPrefix ++ suffix

/-- An image's asset name: its store index, its content key and its basename. -/
public def imageAssetName (k : Nat) (href : String) (data : Option ByteArray := none) : String :=
  imageFileName "i" k href data

/-- The static face's asset name, in a namespace of its own. -/
private def imagePosterName (k : Nat) (en : Image.Loaded) : String :=
  imageFileName "p" k ((System.FilePath.mk (resolvedSrc en)).withExtension "svg").toString
    en.posterSvg

/-- The page's image assets: primary faces in store order, then static faces. -/
public def imageAssets (imgs : Image.Store) : Array ImageAsset :=
  ((Array.range imgs.entries.size).filterMap fun k =>
    (imgs.get? k).bind fun en =>
      if imageShips en then
        some { file := imageAssetName k (browserAssetSrc en) en.browserBytes, srcIndex := k }
      else none) ++
  ((Array.range imgs.entries.size).filterMap fun k =>
    (imgs.get? k).bind fun en =>
      if imageShips en && en.posterSvg.isSome then
        some { file := imagePosterName k en, srcIndex := k, poster := true }
      else none)

/-- An asset's URL, percent-encoded so a `srcset` candidate never splits. -/
public def imageAssetHref (assetsDir file : String) : String :=
  toString (Std.Http.URI.EncodedString.encode
    (r := fun c => Std.Http.Internal.Char.isUnreserved c || c == '/'.toUInt8)
    (assetsDir ++ "/" ++ file))

/-- An entry's browser face, from its captured bytes. -/
public def imageResource? (en : Image.Loaded) : Option HtmlResource.Embedded := do
  if en.webError.isSome || !(imageShips en ||
      (en.src.startsWith Ir.picSrcPrefix && en.webSvg.isSome)) then none else do
    let bytes ← en.browserBytes
    let media := if en.webSvg.isSome || Image.isSvg (resolvedSrc en) then .svg
      else if bytes.extract 0 8 == ⟨#[137, 80, 78, 71, 13, 10, 26, 10]⟩ then .png else .jpeg
    some { media, bytes }

public def imagePosterResource? (en : Image.Loaded) : Option HtmlResource.Embedded := do
  let _ ← imageResource? en
  let bytes ← en.posterSvg
  some { media := .svg, bytes }

public def imageResources (imgs : Image.Store) : Array HtmlResource.Embedded :=
  imgs.entries.filterMap imageResource? ++ imgs.entries.filterMap imagePosterResource?

/-- The embedded URL of a request's browser face; a missing capture stays unresolved. -/
public def imageRequestHref (imgs : Image.Store) (req : Image.Request) : String :=
  match imgs.findRequest? req |>.bind imgs.get? with
  | some en => (imageResource? en |>.map (·.uri)).getD (resolvedSrc en)
  | none => req.src

public def imageHref (imgs : Image.Store) (src : String) : String :=
  imageRequestHref imgs { src }

/-- The embedded URL of a request's static face. -/
public def imagePosterHref (imgs : Image.Store) (req : Image.Request) :
    Option String := do
  let k ← imgs.findRequest? req
  let en ← imgs.get? k
  let r ← imagePosterResource? en
  some r.uri

/-- A length in whole CSS pixels, to nearest, at 1in = 72pt = 96px. -/
public def cssPxOfSp (l : Int) : Nat := ((4 * l + 3 * spPerPt / 2) / (3 * spPerPt)).toNat

public theorem cssPxOfSp_between (l : Int) (h : 0 ≤ l) :
    3 * spPerPt * (cssPxOfSp l : Int) ≤ 4 * l + 3 * spPerPt / 2 ∧
      4 * l + 3 * spPerPt / 2 < 3 * spPerPt * ((cssPxOfSp l : Int) + 1) := by
  unfold cssPxOfSp
  simp only [spPerPt]
  omega

/-- The size an `<img>` declares, in CSS pixels: a raster's grid, or a PDF page's box. -/
public def intrinsicPx (p : Image.Plan) : Nat × Nat :=
  match p.form with
  | some f => (cssPxOfSp f.val.w, cssPxOfSp f.val.h)
  | none => (p.pxW, p.pxH)

/-- Whether an entry is a PDF page with no browser face, boundary pictures aside. -/
public def pdfPageImg (en : Image.Loaded) : Bool :=
  -- premise: Tests.svgAssetChecks — the SVG face is linked and published.
  !en.src.startsWith Ir.picSrcPrefix && !imageShips en &&
  match en.info with
  | some p => p.form.isSome
  | none => false

/-- The emitted PDF-page image requests with no browser face, each once, in page order. -/
public def undecodableIndices (imgs : Image.Store) (uses : Array String) : Array Nat :=
  ((uses.filterMap String.toNat?).foldl (fun acc k =>
    if acc.contains k then acc else acc.push k) #[]).filter fun k =>
      (imgs.get? k).any pdfPageImg

/-- W0605, an image with no browser face, its subject keyed by store index. -/
public def undecodableDiag (src : String) (reason : Option String := none)
    (index : Option Nat := none) : Diag :=
  Diag.of .W0605
    (match reason with
      | some _ => s!"image '{src}' could not produce its browser face; the web page shows a \
labelled placeholder instead"
      | none => s!"image '{src}' is a PDF page no browser decodes; the web page shows a \
placeholder box instead")
    (detail := reason)
    (subject := some (match index with
      | some k => s!"img:{k}:{src}"
      | none => s!"img:{src}"))
    (help := some "for the web page, \\includegraphics a PNG export inside \
\\begin{ifbackend}{html}, and move this include inside \\begin{ifbackend}{pdf}")

private theorem arabicN_no_dash (k : Nat) : ∀ c ∈ (ListMark.arabicN k).toList, c ≠ '-' := by
  intro c hc heq
  simp only [ListMark.arabicN, String.toList_ofList, List.mem_reverse] at hc
  have := ListMark.digitsRev_digits hc
  subst heq
  simp at this

private theorem dash_split (a a' r r' : List Char)
    (ha : ∀ c ∈ a, c ≠ '-') (ha' : ∀ c ∈ a', c ≠ '-')
    (h : a ++ '-' :: r = a' ++ '-' :: r') : a = a' := by
  induction a generalizing a' with
  | nil =>
    cases a' with
    | nil => rfl
    | cons c cs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm (ha' c (List.mem_cons_self ..))
  | cons c cs ih =>
    cases a' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      exact absurd h.1 (ha c (List.mem_cons_self ..))
    | cons c' cs' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have := ih cs' (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun x hx => ha' x (List.mem_cons_of_mem _ hx)) h.2
      rw [h.1, this]

public theorem imageAssetName_inj {k k' : Nat} {h h' : String} {data data' : Option ByteArray}
    (e : imageAssetName k h data = imageAssetName k' h' data') : k = k' := by
  have hl := congrArg String.toList e
  have hi : "i".toList = ['i'] := rfl
  have hd : "-".toList = ['-'] := rfl
  simp only [imageAssetName, imageFileName, String.toList_append, List.append_assoc, hi, hd,
    List.singleton_append] at hl
  exact ListMark.arabicN_inj (String.ext
    (dash_split _ _ _ _ (arabicN_no_dash k) (arabicN_no_dash k') (List.cons.inj hl).2))

public theorem imageAssets_covers (imgs : Image.Store) {k : Nat} {en : Image.Loaded}
    (hen : imgs.get? k = some en) (hr : imageShips en = true) :
    ∃ a ∈ imageAssets imgs, a.srcIndex = k := by
  refine ⟨{ file := imageAssetName k (browserAssetSrc en) en.browserBytes, srcIndex := k },
    ?_, rfl⟩
  apply Array.mem_append.mpr
  left
  simp only [Array.mem_filterMap]
  refine ⟨k, Array.mem_range.mpr ?_, ?_⟩
  · exact (Array.getElem?_eq_some_iff.mp hen).1
  · simp [hen, hr]

public theorem img_request_src_shipped (imgs : Image.Store) (req : Image.Request)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.findRequest? req = some k) (hen : imgs.get? k = some en)
    (hr : imageResource? en = some r) :
    r ∈ imageResources imgs ∧ imageRequestHref imgs req = r.uri := by
  refine ⟨Array.mem_append.mpr (.inl (Array.mem_filterMap.mpr ⟨en, ?_, hr⟩)), ?_⟩
  · exact Array.mem_of_getElem? hen
  · simp [imageRequestHref, hk, hen, hr]

public theorem img_src_shipped (imgs : Image.Store) (src : String)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.find? src = some k) (hen : imgs.get? k = some en)
    (hr : imageResource? en = some r) :
    r ∈ imageResources imgs ∧ imageHref imgs src = r.uri :=
  img_request_src_shipped imgs { src } hk hen hr

public theorem imagePosterHref_covers (imgs : Image.Store) (req : Image.Request)
    {k : Nat} {en : Image.Loaded} {r : HtmlResource.Embedded}
    (hk : imgs.findRequest? req = some k) (hen : imgs.get? k = some en)
    (hr : imagePosterResource? en = some r) :
    r ∈ imageResources imgs ∧ imagePosterHref imgs req = some r.uri := by
  refine ⟨Array.mem_append.mpr (.inr (Array.mem_filterMap.mpr ⟨en, ?_, hr⟩)), ?_⟩
  · exact Array.mem_of_getElem? hen
  · simp [imagePosterHref, hk, hen, hr]

private def fontFaceRule (fs : Font.FontSet) (ff : FontFace) : String :=
  s!"@font-face \{ font-family: \"{ff.family}\"; font-weight: {ff.weight}; " ++
  s!"font-style: {if ff.italic then "italic" else "normal"}; " ++
  s!"src: url(\"{(fontResource (fs.get ff.index)).uri}\") format(\"{ff.format}\"); }\n"

private def fontFaceCss (fs : Font.FontSet) : String :=
  String.join ((shipFaces fs).toList.map (fontFaceRule fs))

/-- The `@font-face` rules, the body weight the document resolved, and small caps as the only
synthesis. -/
private def fontCss (fs : Font.FontSet) : String :=
  let w := (fs.get (fs.lookup 0 400 false)).weight
  fontFaceCss fs ++
  s!"body \{ font-weight: {w}; --ltx-body-weight: {w}; " ++
  "font-synthesis: small-caps; }\n"

/-- The generic family closing a slot's stack: monospace by `post` isFixedPitch, else by OS/2
sFamilyClass (8 sans serif, 1–7 serif; OpenType OS/2 table), else the declared kind. -/
public def genericFor (fs : Font.FontSet) (slot : Nat) (declared : String) : String :=
  let f := fs.get (fs.lookup slot 400 false)
  if f.isFixedPitch then "monospace"
  else if f.familyClass == 8 then "sans-serif"
  else if 1 ≤ f.familyClass && f.familyClass ≤ 7 then "serif"
  else declared

/-- Design tokens as CSS custom properties. -/
private def tokenVars (cfg : Config) (doc : Doc) (roles : List Ir.Role)
    (taken : List String := []) : String :=
  let pal := cfg.floorPal
  let aliases := readerAliases pal roles taken
  let palette := (pal.entries.toList.filterMap fun (n, c) => match n with
      | .role r => if roles.contains r then some (paletteVar n c) else none
      | .color _ => some (paletteVar n c)) ++ aliases
  -- beamer's lineage states these in the page's unit (`lineageSkipVars`)
  let stated (n : String) : Bool :=
    doc.docClass.record.lists == .beamer && (n == Ir.trivlistSkipName || n == "floatsep")
  let tokens := (doc.tokens.entries.toList.filter (!stated ·.1)).filterMap fun (n, g) =>
    (tokenVar? n).map fun v => s!"    {v}: {tokenCss (lengthBasisOf doc) n g.width};"
  let fonts := match cfg.fonts with
    | some fs =>
      -- the slides class fills the text slot from the sans declaration, beamer's default
      let bodyDeclared :=
        if doc.docClass == DocClass.slides && doc.fonts.sans.isSome then "sans-serif"
        else "serif"
      let slot (s : Nat) (declared : String) : String :=
        stackFor fs s!"ltx-{slotName s}" (genericFor fs s declared)
      [s!"    --font-body: {slot 0 bodyDeclared};",
       s!"    --font-sans: {slot 1 "sans-serif"};",
       s!"    --font-mono: {slot 2 "monospace"};"] ++
      (doc.fonts.families.toList.zipIdx.map fun (_, i) =>
        let s := Ir.familySlotBase + i
        s!"    --font-{s}: {slot s bodyDeclared};") ++
      (if fs.math.isSome then
        [s!"    --font-math: {stackFor fs "ltx-math" "math"};"]
       else [])
    | none =>
      (match doc.fonts.body with
       | some f => [s!"    --font-body: \"{f}\", Georgia, serif;"]
       | none => []) ++
      (match doc.fonts.sans with
       | some f => [s!"    --font-sans: \"{f}\", system-ui, sans-serif;"]
       | none => []) ++
      (match doc.fonts.mono with
       | some f => [s!"    --font-mono: \"{f}\", ui-monospace, monospace;"]
       | none => [])
  String.intercalate "\n" (palette ++ tokens ++ fonts)

/-- One scale step as a CSS size, from `Ir.sizeScale`. -/
private def scaleSize (name : String) (unit : String) : String :=
  milliFactor ((Ir.sizeScale.lookup name).getD 1000) ++ unit

/-- The leading a named size step sets, as a unitless CSS line height in milli. -/
@[expose] public def stepLineHeightMilli (skips : List (String × Nat)) (factor : Nat)
    (body : Dim.Sp) (step : String) (k : Nat) : Nat :=
  let size := max 1 (body * (k : Int) / 1000)
  ((Ir.stepSkip (Ir.stepLead skips step body) body factor * 1000 + size / 2) / size).toNat

public theorem stepLineHeight_between (skips : List (String × Nat)) (factor : Nat)
    (body : Int) (step : String) (k : Nat) (hs : 0 < body * (k : Int) / 1000)
    (hl : 0 ≤ Ir.stepSkip (Ir.stepLead skips step body) body factor) :
    (stepLineHeightMilli skips factor body step k : Int) * (body * (k : Int) / 1000) ≤
        Ir.stepSkip (Ir.stepLead skips step body) body factor * 1000 +
          body * (k : Int) / 1000 / 2 ∧
      Ir.stepSkip (Ir.stepLead skips step body) body factor * 1000 +
          body * (k : Int) / 1000 / 2 <
        ((stepLineHeightMilli skips factor body step k : Int) + 1) *
          (body * (k : Int) / 1000) := by
  unfold stepLineHeightMilli
  generalize body * (k : Int) / 1000 = sz at hs ⊢
  have hm : max 1 sz = sz := by omega
  have hq : 0 ≤ (Ir.stepSkip (Ir.stepLead skips step body) body factor * 1000 + sz / 2) / sz :=
    Int.ediv_nonneg (Int.add_nonneg (Int.mul_nonneg hl (by decide))
      (Int.ediv_nonneg (Int.le_of_lt hs) (by decide))) (Int.le_of_lt hs)
  simp only [hm, Int.toNat_of_nonneg hq]
  exact ⟨Int.ediv_mul_le _ (Int.ne_of_gt hs), Int.lt_ediv_add_one_mul_self _ hs⟩

/-- Size rules from the document's ladder, and on a deck each step's leading class. -/
private def sizeRules (scale : List (String × Nat))
    (deck : Option (List (String × Nat) × Nat × Dim.Sp) := none) : String :=
  String.join (scale.map fun (name, k) =>
    match deck with
    | some (skips, factor, body) =>
      s!".size-{name} \{ font-size: {milliFactor k}em; }\n" ++
      -- no element carries the body's own step (`stepNode`, `withLead`)
      (if name == "normalsize" then "" else
        s!":is(h1, h2, h3, h4, h5, h6).lead-{name} \{ line-height: 0; }\n" ++
        s!".lead-{name} .size-{name}, .size-{name}.lead-{name} \{ line-height: " ++
          s!"{milliFactor (stepLineHeightMilli skips factor body name k)}; }\n")
    | none => s!".size-{name} \{ font-size: {milliFactor k}em; }\n")

/-! ## Deck stylesheet -/

/-- A browser feature the deck's stylesheet gates on. -/
public inductive Feature where
  /-- View progress timelines, `animation-timeline: view()`. -/
  | viewTimeline
  /-- Scroll-state container queries, `container-type: scroll-state`. -/
  | scrollState
  /-- The relational selector `:has()`. -/
  | has
  deriving Repr, DecidableEq

/-- The `@supports` condition that detects the feature. -/
public def Feature.test : Feature → String
  | .viewTimeline => "(animation-timeline: view())"
  | .scrollState => "(container-type: scroll-state)"
  | .has => "selector(:has(a))"

/-- The sourced support note: engines and versions, from caniuse and MDN. -/
public def Feature.support : Feature → String
  | .viewTimeline =>
    "Chromium 115+ (Jul 2023), Safari 26; Firefox release unsupported \
(preview builds only; ESR 140 reports the feature false) — caniuse \
mdn-css_properties_animation-timeline_view, read 2026-09-21"
  | .scrollState =>
    "Chromium 133+ (Feb 2025), no Firefox, no Safari — MDN scroll-state \
container queries / caniuse, read 2026-09-20"
  | .has =>
    "Chromium 105+ (Aug 2022), Firefox 121+ (Dec 2023), Safari 15.4+ \
(Mar 2022) — caniuse css-has, read 2026-09-20"

/-- The property names whose meaning depends on the feature. -/
public def Feature.dependsOnProps : Feature → List String
  | .viewTimeline => ["animation-timeline", "view-timeline", "animation-range"]
  | .scrollState => []
  | .has => []

/-- The digit-free selector fragments whose meaning depends on the feature. -/
public def Feature.dependsOnSel : Feature → List String
  | .viewTimeline => []
  | .scrollState => ["scroll-state("]
  | .has => [":has("]

/-- Every feature, in emission order for the `@supports` blocks. -/
public def Feature.all : List Feature := [.viewTimeline, .scrollState, .has]

public theorem Feature.all_complete : ∀ f : Feature, f ∈ Feature.all := by
  intro f; cases f <;> simp [Feature.all]

public theorem Feature.all_nodup : Feature.all.Nodup := by decide

private def hasFragAux (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | l@(_ :: t) => pat.isPrefixOf l || hasFragAux pat t

public def hasFrag (s frag : String) : Bool := hasFragAux frag.toList s.toList

/-- One chunk of a deck selector: literal syntax, an interpolated ordinal, or step alternatives. -/
public inductive SelChunk where
  | lit (s : String)
  | num (n : Nat)
  /-- The uncovered-step alternatives, one `.step[data-step]` compound per step. -/
  | stepAlts (js : List Nat)
  /-- One compound per declared attribute value on a class. -/
  | attrAlts (cls attr : String) (js : List Nat)
  deriving Repr, DecidableEq

/-- The literal syntax a chunk renders, ordinals excluded. -/
public def SelChunk.lits : SelChunk → List String
  | .lit s => [s]
  | .num _ => []
  | .stepAlts _ => [".step[data-step=\"", "\"], "]
  | .attrAlts cls attr _ => [".", cls, "[", attr, "=\"", "\"], "]

public def SelChunk.render : SelChunk → String
  | .lit s => s
  | .num n => toString n
  | .stepAlts js =>
    String.intercalate ", " (js.map fun j => s!".step[data-step=\"{j}\"]")
  | .attrAlts cls attr js =>
    String.intercalate ", " (js.map fun j => s!".{cls}[{attr}=\"{j}\"]")

private def renderSel (sel : List SelChunk) : String :=
  String.join (sel.map SelChunk.render)

/-- Where a rule stands in the feature partition: the base, a feature's `@supports` block, or
its `@supports not` block. -/
public inductive Gate where
  | base
  | supported (f : Feature)
  | unsupported (f : Feature)
  deriving Repr, DecidableEq

/-- The media partition a rule is emitted into: screen, reduced motion, print, or the stage in
both media. -/
public inductive Part where
  | screen
  | reduce
  | print
  | stage
  deriving Repr, DecidableEq

public structure DeckRule where
  selector : List SelChunk
  decls : List (String × String)
  requires : Gate := .base
  part : Part := .screen
  deriving Repr, DecidableEq

/-- Whether the rule's property names or selector literals depend on `f`. -/
public def DeckRule.uses (r : DeckRule) (f : Feature) : Bool :=
  r.decls.any (fun d => f.dependsOnProps.contains d.1) ||
    f.dependsOnSel.any fun frag =>
      (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s frag

/-- One rule's CSS text, closing every block its selector opens. -/
public def DeckRule.render (r : DeckRule) : String :=
  let sel := renderSel r.selector
  sel ++ " { " ++
    String.join (r.decls.map fun d => d.1 ++ ": " ++ d.2 ++ "; ") ++
    "}" ++ String.join (List.replicate
      (sel.toList.count '{' - sel.toList.count '}') " }") ++ "\n"

/-- One partition's rules grouped by gate: the base, then `@supports`, then `@supports not`. -/
private def emitGates (rules : List DeckRule) : String :=
  let group (g : Gate) := rules.filter (fun r => r.requires == g)
  let block (test : String) (rs : List DeckRule) : String :=
    if rs.isEmpty then "" else
      "@supports " ++ test ++ " {\n" ++
        String.join (rs.map DeckRule.render) ++ "}\n"
  String.join ((group .base).map DeckRule.render) ++
    String.join (Feature.all.map fun f => block f.test (group (.supported f))) ++
    String.join (Feature.all.map fun f =>
      block ("not " ++ f.test) (group (.unsupported f)))

/-- The deck stylesheet from its typed rules: stage, screen, reduced motion after the blocks it
reverts, then print. -/
public def emitDeckRules (rules : List DeckRule) : String :=
  let part (p : Part) := rules.filter (fun r => r.part == p)
  "@media screen, print {\n" ++ emitGates (part .stage) ++ "}\n" ++
  "@media screen {\n" ++
    emitGates (part .screen) ++
    "@media (prefers-reduced-motion: reduce) {\n" ++
      emitGates (part .reduce) ++ "}\n" ++
    "}\n" ++
  "@media print {\n" ++ emitGates (part .print) ++ "}\n"

private def deckGlideRule : DeckRule :=
  { selector := [.lit "html"], decls := [("scroll-behavior", "smooth")] }

/-- The one rule declaring snap alignment, on every `[data-snap]` area. -/
private def deckSnapDoor : DeckRule :=
  { selector := [.lit "[data-snap]"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")] }

/-- The frame's logo strip across the stage's safe area, pinned to its bottom. -/
private def deckLogoRule : DeckRule :=
  { selector := [.lit ".slide-logo"]
    decls := [("position", "absolute"), ("bottom", safeareaVar),
      ("left", safeareaVar), ("right", safeareaVar), ("display", "flex")]
    part := .stage }

public def stageGround : String := roleRef .page

public def stageInk : String := roleRef .ink

/-- Every frame fills the viewport as one opaque stage, its spill reachable by its own scroll. -/
private def deckStageRule : DeckRule :=
  { selector := [.lit "section.slide, section.section-page"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw"),
      ("height", "100dvh"), ("overflow-y", "auto"),
      ("background", stageGround), ("color", stageInk), ("display", "flex"),
      ("flex-direction", "column"), ("padding", safeareaVar),
      ("position", "relative")]
    part := .stage }

/-- The deck's stage typography: body and root sizes as shares of the stage height, and the
body's line height. -/
public structure DeckType where
  body : String
  root : String
  leading : String

/-- The deck's base screen rules, which no feature gates. -/
private def deckBase (ty : DeckType) : List DeckRule :=
  [ { selector := [.lit "html"]
      decls := [("scroll-snap-type", "x mandatory"), ("overflow-y", "clip")] },
    deckGlideRule,
    { selector := [.lit "body"], decls := [("padding", "0")], part := .stage },
    { selector := [.lit "main"]
      decls := [("max-width", "none"), ("margin", "0"), ("font-size", ty.body),
        ("line-height", ty.leading)]
      part := .stage },
    { selector := [.lit "main"]
      decls := [("display", "flex"), ("align-items", "flex-start")] },
    deckStageRule,
    deckSnapDoor,
    deckLogoRule,
    { selector := [.lit "section.section-page"]
      decls := [("justify-content", "center"), ("align-items", "center")]
      part := .stage },
    { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")]
      part := .stage },
    { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")]
      part := .stage },
    { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")]
      part := .stage },
    -- the band keeps its title and padding even when the body overflows
    { selector := [.lit "section.slide > header"]
      decls := [("flex-shrink", "0")], part := .stage },
    { selector := [.lit "section.slide > header h2"]
      decls := [("font-size", scaleSize "Large" "em")], part := .stage },
    -- the root size the sheet's rem gaps read: the stage's rhythm unit
    { selector := [.lit "html"], decls := [("font-size", ty.root)], part := .stage },
    -- a listing on the stage takes no padding or ground of its own, as on the page
    { selector := [.lit "pre"], decls := [("padding", "0"), ("background", "none")],
      part := .stage } ]

/-- `deckGlideRule`'s reduced-motion counterpart. -/
private def deckGlideGuard : DeckRule :=
  { selector := [.lit "html"], decls := [("scroll-behavior", "auto")]
    part := .reduce }

private def deckReduce : List DeckRule := [deckGlideGuard]

/-- The stepped track, gated on `view()` timelines: one sticky stage over a snap spacer per step. -/
private def stepTrackRule : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("display", "flex"), ("align-items", "flex-start"),
      ("width", "calc(var(--steps) * 100vw)"),
      ("flex", "0 0 calc(var(--steps) * 100vw)"),
      ("view-timeline", "--frame x")]
    requires := .supported .viewTimeline }

/-- The stage rides its track sticky at the scrollport's left edge, over its spacers. -/
private def stepStageRule : DeckRule :=
  { selector := [.lit ".slide-track > section.slide"]
    decls := [("position", "sticky"), ("left", "0"),
      ("margin-right", "-100vw")]
    requires := .supported .viewTimeline }

/-- Each spacer is one scrollport wide and one stage tall. -/
private def stepSnapSize : DeckRule :=
  { selector := [.lit ".snap"]
    decls := [("flex", "0 0 100vw"), ("height", "100dvh")]
    requires := .supported .viewTimeline }

/-- The uncover's keyframes: a covered step dimmed and offset, the `to` frame fully restored. -/
private def stepKeyframes (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "@keyframes ltx-uncover \
{ to { opacity: 100%; transform: none } from"]
    decls := [("opacity", s!"{coveredPct}%"),
      ("transform", "translateX(var(--motiondistance, 1rem))")]
    requires := .supported .viewTimeline }

/-- The steps' uncover: each step fades in during the scroll to its snap. -/
private def stepUncoverRule : DeckRule :=
  { selector := [.lit ".step:not([data-step=\"1\"])"]
    decls := [("animation", "ltx-uncover linear both"),
      ("animation-timeline", "--frame"),
      ("animation-range",
        "contain calc((var(--step) - 2) / (var(--steps) - 1) * 100%) \
contain calc((var(--step) - 1) / (var(--steps) - 1) * 100%)")]
    requires := .supported .viewTimeline }

/-- Without `view()` timelines the spacers hide, and the stepped frame is one page. -/
private def stepSnapHide : DeckRule :=
  { selector := [.lit ".snap"], decls := [("display", "none")]
    requires := .unsupported .viewTimeline }

/-- With spacers hidden, the track is the frame's snap box. -/
private def stepTrackFloorSnap : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")]
    requires := .unsupported .viewTimeline }

/-- On the floor, steps start covered only under the deck script's marker. -/
private def stepFloorCovered (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] .step:not([data-step=\"1\"])"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .unsupported .viewTimeline }

/-- The steps a floor snap `k` uncovers: `2..k`. -/
public def uncoveredBy (k : Nat) : List Nat := (List.range (k - 1)).map (· + 2)

/-- The floor's uncover for snap `k`: every step up to `k` of the frame the script marks. -/
private def stepSnappedRule (k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k,
      .lit "\"] :is(", .stepAlts (uncoveredBy k), .lit ")"]
    decls := [("opacity", "100%")]
    requires := .unsupported .viewTimeline }

private def stepSnapped (maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).map fun i => stepSnappedRule (i + 2)

/-! ## Overlay range ends -/

/-- The recover's keyframes: full colour at the range's end, the covered fraction past it. -/
private def stepRecoverKeyframes (coveredPct : Nat) : DeckRule :=
  { selector := [.lit "@keyframes ltx-recover { from { opacity: 100% } to"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .supported .viewTimeline }

/-- A declared end's carrier dims over the snap interval after the range's last step. -/
private def stepRecoverRule : DeckRule :=
  { selector := [.lit ".step-end"]
    decls := [("animation", "ltx-recover linear both"),
      ("animation-timeline", "--frame"),
      ("animation-range",
        "contain calc((var(--step-last) - 1) / (var(--steps) - 1) * 100%) \
contain calc(var(--step-last) / (var(--steps) - 1) * 100%)")]
    requires := .supported .viewTimeline }

/-- The `data-step-last` values snap `k` stands past, read off `Ir.stepPending`. -/
public def endedBy (maxSteps k : Nat) : List Nat :=
  ((List.range maxSteps).map (· + 1)).filter fun u => Ir.stepPending 1 (some u) k

/-- The floor's recover for snap `k`: every declared end below `k` dims its carrier again. -/
private def stepRecoverFloorRule (coveredPct maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] .slide-track[data-snapped=\"", .num k,
      .lit "\"] :is(", .attrAlts "step-end" "data-step-last" (endedBy maxSteps k),
      .lit ")"]
    decls := [("opacity", s!"{coveredPct}%")]
    requires := .unsupported .viewTimeline }

private def stepRecovered (coveredPct maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).map fun i => stepRecoverFloorRule coveredPct maxSteps (i + 2)

/-- The end carrier's reduced-motion guard: no animation, full colour. -/
private def stepRecoverGuard : DeckRule :=
  { selector := [.lit ".step-end"]
    decls := [("opacity", "100%"), ("animation", "none")]
    part := .reduce }

/-- The floor recover's reduced-motion counterpart, at its own specificity. -/
private def stepRecoverFloorGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] .slide-track[data-snapped] \
:is(.step-end[data-step-last])"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- Whether the emitted rules leave step `(n, last)` covered at snap `k`. -/
public def htmlStepPendingAt (maxSteps n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  (!(n == 1) && !((uncoveredBy k).contains n)) ||
    (match last with
     | some u => (endedBy maxSteps k).contains u
     | none => false)

public theorem html_step_pending_agree (maxSteps n k : Nat) (last : Option Nat)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlast : ∀ u, last = some u → 1 ≤ u ∧ u ≤ maxSteps) :
    htmlStepPendingAt maxSteps n last k = Ir.stepPending n last k := by
  have hstart : ∀ m, m ∈ uncoveredBy k ↔ (2 ≤ m ∧ m ≤ k) := by
    intro m
    simp only [uncoveredBy, List.mem_map, List.mem_range]
    exact ⟨fun ⟨i, hi, hm⟩ => by omega, fun h => ⟨m - 2, by omega, by omega⟩⟩
  have hend : ∀ u, u ∈ endedBy maxSteps k ↔ (1 ≤ u ∧ u ≤ maxSteps ∧ u < k) := by
    intro u
    simp only [endedBy, List.mem_filter, List.mem_map, List.mem_range,
      Ir.stepPending, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨⟨i, hi, hu⟩, hp⟩ => by omega,
      fun h => ⟨⟨u - 1, by omega, by omega⟩, by omega⟩⟩
  rw [Bool.eq_iff_iff]
  cases last with
  | none =>
    simp only [htmlStepPendingAt, Ir.stepPending, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, List.contains_eq_mem,
      decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, hstart,
      Bool.false_eq_true, or_false]
    omega
  | some u =>
    have hu := hlast u rfl
    simp only [htmlStepPendingAt, Ir.stepPending, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_true_eq, List.contains_eq_mem,
      decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq, hstart, hend]
    omega

/-- The steps' reduced-motion guard: no step animates, and every step stands at full colour. -/
private def stepGuard : DeckRule :=
  { selector := [.lit ".step"]
    decls := [("opacity", "100%"), ("animation", "none")]
    part := .reduce }

/-- The covered default's reduced-motion counterpart, at its exact selector. -/
private def stepCoveredGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] .step:not([data-step=\"1\"])"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- The track's reduced-motion reverts: one page per stepped frame. -/
private def stepTrackWidthReduce : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("width", "100vw"), ("flex", "0 0 100vw")]
    part := .reduce }

private def stepSnapReduceHide : DeckRule :=
  { selector := [.lit ".snap"], decls := [("display", "none")]
    part := .reduce }

private def stepTrackSnapReduce : DeckRule :=
  { selector := [.lit ".slide-track"]
    decls := [("scroll-snap-align", "start"), ("scroll-snap-stop", "always")]
    part := .reduce }

/-! ## Alternation -/

/-- The `data-step` values snap `k` has reached, read off `Ir.stepPending`. -/
public def startedBy (maxSteps k : Nat) : List Nat :=
  ((List.range maxSteps).map (· + 1)).filter fun n => !Ir.stepPending n none k

/-- Snap `k` shows the crisp side of every alternation whose start it has reached. -/
private def altStartCrispRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-crisp" "data-step" (startedBy maxSteps k), .lit ")"]
    decls := [("display", "contents")] }

/-- Snap `k` hides the pending side of those alternations. -/
private def altStartPendingRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit ".slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-pending" "data-step" (startedBy maxSteps k), .lit ")"]
    decls := [("display", "none")] }

/-- Past a declared end the sides swap back, outranking the start rules. -/
private def altEndCrispRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-crisp" "data-step-last" (endedBy maxSteps k), .lit ")"]
    decls := [("display", "none")] }

private def altEndPendingRule (maxSteps k : Nat) : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped=\"", .num k, .lit "\"] :is(",
      .attrAlts "alt-pending" "data-step-last" (endedBy maxSteps k), .lit ")"]
    decls := [("display", "contents")] }

/-- The four rules one snap needs: the start reached, then the end passed. -/
private def altSnapRules (maxSteps k : Nat) : List DeckRule :=
  [altStartCrispRule maxSteps k, altStartPendingRule maxSteps k,
   altEndCrispRule maxSteps k, altEndPendingRule maxSteps k]

private def altSnapped (maxSteps : Nat) : List DeckRule :=
  (List.range (maxSteps - 1)).flatMap fun i => altSnapRules maxSteps (i + 2)

/-- Under reduce, alternations show step 1's reading. -/
private def altReduceHiddenRule : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped] .alt[hidden]"]
    decls := [("display", "none")]
    part := .reduce }

private def altReduceShownRule : DeckRule :=
  { selector := [.lit "html .slide-track[data-snapped] .alt:not([hidden])"]
    decls := [("display", "contents")]
    part := .reduce }

private def altReduceFixed : List DeckRule := [altReduceHiddenRule, altReduceShownRule]

private def altRules (maxSteps : Nat) : List DeckRule :=
  let snapped := altSnapped maxSteps
  altReduceFixed ++ snapped

/-- Which group the emitted rules select at snap `k`. -/
public def altShownFirstAt (maxSteps n : Nat) (last : Option Nat) (k : Nat) : Bool :=
  htmlStepPendingAt maxSteps n last k == Ir.altFirstWhenPending n last

public theorem alt_backend_agree (maxSteps n k : Nat) (last : Option Nat)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlast : ∀ u, last = some u → 1 ≤ u ∧ u ≤ maxSteps) :
    altShownFirstAt maxSteps n last k = Ir.altShowsFirst n last k := by
  rw [altShownFirstAt, html_step_pending_agree maxSteps n k last hn hk hlast,
    Ir.altShowsFirst_side]

/-- The step rules whose spelling reads no parameter. -/
private def stepFixed : List DeckRule :=
  [stepTrackRule, stepStageRule, stepSnapSize, stepUncoverRule,
   stepRecoverRule, stepSnapHide, stepTrackFloorSnap, stepGuard,
   stepRecoverGuard, stepCoveredGuard, stepRecoverFloorGuard,
   stepTrackWidthReduce, stepSnapReduceHide, stepTrackSnapReduce]

private def stepRules (coveredPct maxSteps : Nat) : List DeckRule :=
  stepKeyframes coveredPct :: stepRecoverKeyframes coveredPct ::
    stepFloorCovered coveredPct ::
    (stepFixed ++ stepSnapped maxSteps ++ stepRecovered coveredPct maxSteps)

/-- The printed deck's page: the stage's size, with no margin. -/
private def deckPageRule (size : String) : DeckRule :=
  { selector := [.lit "@page"], decls := [("size", size), ("margin", "0")]
    part := .print }

/-- The page size `deckPageRule` declares: the PDF's MediaBox, in `pt`. -/
public def deckPageSize (page : PageSpec) : String :=
  s!"{page.width.toPtString}pt {page.height.toPtString}pt"

/-- A stage on paper opens its sheet and grows with its content instead of clipping it. -/
private def printStageRule : DeckRule :=
  { selector := [.lit "section.slide, section.section-page"]
    decls := [("break-after", "page"), ("break-before", "page"), ("height", "auto"),
      ("min-height", "100dvh"), ("overflow-y", "visible"),
      ("box-decoration-break", "clone"), ("print-color-adjust", "exact")]
    part := .print }

/-- Every sheet shows the stage's ground. -/
private def printSheetGround : DeckRule :=
  { selector := [.lit "html"]
    decls := [("background", stageGround), ("print-color-adjust", "exact")]
    part := .print }

/-- How far ahead of the declared vertical distribution a frame's end spacer claims the leftover. -/
public def printEndGrow : Nat := 100000000

public theorem printEndGrow_outranks_contract :
    ∀ (keys : Ir.FrameKeys) (v : Ir.VAlign) (breakable : Bool) (fills : Nat), fills ≤ 100 →
      100 * ((v.shares keys breakable).1 + (v.shares keys breakable).2 + Ir.fillUnit * fills) ≤
        printEndGrow := by
  intro keys v breakable fills h
  have hf : Ir.fillUnit * fills ≤ 100000 := by simp only [Ir.fillUnit]; omega
  have hs : (v.shares keys breakable).1 + (v.shares keys breakable).2 ≤ 5618 := by
    cases keys <;> cases v <;> cases breakable <;> decide
  simp only [printEndGrow]
  omega

/-- On paper a frame keeps its bottom safe area as a trailing spacer that gives the room back. -/
private def printFrameEnd : List DeckRule :=
  [ { selector := [.lit "section.slide"], decls := [("padding-bottom", "0")]
      part := .print },
    { selector := [.lit "section.slide::after"]
      decls := [("content", "\"\""), ("flex", s!"{printEndGrow} 0 0"),
        ("max-height", safeareaVar)]
      part := .print } ]

/-- The fill a `\block[before = fill]` opens its content with, as the box's `::before`. -/
private def fillBeforeCss : String :=
  s!"section.slide .spaced.fill-before::before \{ content: \"\"; flex-grow: {Ir.fillUnit}; }\n"

/-- beamer's text area on the stage: the frame opens at the top edge and ends `\footheight`
above the bottom. -/
private def deckAreaCss (doc : Doc) : String :=
  if doc.chromeAllowed then
    "section.slide:not(.title-page) { padding-top: 0; padding-bottom: 0; }\n" ++
    "section.slide:not(.title-page)::after { content: \"\";\n" ++
    s!"  flex: {printEndGrow} 0 0; max-height: {stageVh doc.page Ir.footline.sep}; }\n" ++
    "@media print { section.slide > :is(.fill, footer.slide-foot), section.slide::after {\n" ++
    "  break-before: avoid; } }\n"
  else ""

/-- A frame's content as TeX opens it below its `\vbox{}` (beamerbaseframe.sty): the first
baseline one `\baselineskip` down, the last line trimmed to its baseline. -/
private def frameOpeningCss (doc : Doc) : String :=
  let l := doc.docClass.record.lists
  let size := doc.page.fontSize
  -- One set of rules per edge: the frame's opening element, the stage's
  -- child (`frame-body-start`), and the block an opening carrier's flow
  -- opens on in each group (`frame-flow-start`, `markFlowStart`).
  let rules (pre cls : String) : String :=
    let item := s!"{pre}:is(ul, ol:not(.algorithm)){cls} > li:first-child"
    let triv := s!"{pre}.{roleClass Ir.trivlistRole}{cls}"
    let float := s!"{pre}figure.float{cls}"
    (match Ir.listSkips l size 1 with
     | some sk =>
       let opened := sk.topsep.width.sp + (Ir.partopsepFor l size 1 doc.tokens).width.sp
       s!"{pre}:is({", ".intercalate listElems}){cls} \{ \
--frame-body-open: {stageVh doc.page opened}; }\n"
     | none => "") ++
    s!"{triv} \{ --frame-body-open: {stageVh doc.page ((Ir.trivlistSkipFor l doc.tokens size 0).width.resolve size 0)}; }\n" ++
    s!"{float} \{ --frame-body-open: {stageVh doc.page ((Ir.floatSpaceFor l doc.tokens size 0).1.width.resolve size 0)}; }\n" ++
    s!"{pre}p{cls}::before,\n" ++
    s!"{triv} > p:first-child::before, {float} > :is(p, figcaption):first-child::before,\n" ++
    s!"{pre}dl{cls} > dt:first-child::before,\n" ++
    s!"{item}:not(:has(> :is(p, div, ul, ol, dl, pre, table, figure, blockquote)))::before,\n" ++
    s!"{item} > p:first-child::before \{ content: \"\"; display: inline-block;\n" ++
    s!"  height: {decMilli (Ir.leadingFor 1000 doc.page.leading)}em; }\n"
  rules "section.slide > " ".frame-body-start" ++ rules "section.slide " ".frame-flow-start" ++
  "section.slide > :is(p, ul, ol, dl, blockquote, .centered, .ragged, .ragged-right)\
.frame-body-end,\nsection.slide :is(p, ul, ol, dl, blockquote, .centered, .ragged, \
.ragged-right).frame-flow-end { text-box: trim-end text alphabetic; }\n"

/-- The print rules every deck carries, steps aside. -/
private def printPaged : List DeckRule := [printStageRule, printSheetGround] ++ printFrameEnd

/-- The print partition: the stages paged, snap spacers hidden, every step at full colour. -/
private def deckPrint (maxSteps : Nat) : List DeckRule :=
  printPaged ++
    (if 2 ≤ maxSteps then
      [ { selector := [.lit ".snap"], decls := [("display", "none")]
          part := .print },
        { selector := [.lit ".step"], decls := [("opacity", "100%")]
          part := .print } ]
     else [])

/-- A numbered union dims outside its emitted membership set. -/
private def stepSetPendingRule (cp k : Nat) : DeckRule :=
  { selector := [.lit "html[data-deck-script] [data-snapped=\"", .num k,
      .lit "\"] .step-set:not([data-steps~=\"", .num k, .lit "\"])"]
    decls := [("opacity", s!"{cp}%")] }

private def altSetShownRule (k : Nat) : DeckRule :=
  { selector := [.lit "[data-snapped=\"", .num k,
      .lit "\"] .alt-set[data-steps~=\"", .num k, .lit "\"]"]
    decls := [("display", "contents")] }

private def altSetHiddenRule (k : Nat) : DeckRule :=
  { selector := [.lit "[data-snapped=\"", .num k,
      .lit "\"] .alt-set:not([data-steps~=\"", .num k, .lit "\"])"]
    decls := [("display", "none")] }

/-- `stepSetPendingRule`'s reduced-motion counterpart. -/
private def stepSetGuard : DeckRule :=
  { selector := [.lit "html[data-deck-script] [data-snapped] .step-set[data-steps]"]
    decls := [("opacity", "100%")]
    part := .reduce }

/-- Under a pending ancestor a descendant's own cover stops, so opacities never multiply. -/
private def nestedCoverRule (k : Nat) : DeckRule :=
  let parent := [.lit "html[data-deck-script] [data-snapped=\"", .num k,
    .lit "\"] :is(.step, .step-set):not([data-steps~=\"", .num k, .lit "\"])"]
  { selector := parent ++ [.lit " :is(.step, .step-set), "] ++ parent ++
      [.lit " :is(.step, .step-set) > .step-end"]
    decls := [("opacity", "100%"), ("animation", "none")] }

/-- Without the deck script every cover stands at full colour. -/
private def coverStaticFloor : DeckRule :=
  { selector := [.lit "html:not([data-deck-script]) :is(.step, .step-end, .step-set)"]
    decls := [("opacity", "100%"), ("animation", "none")] }

private def setRules (cp ms : Nat) : List DeckRule :=
  stepSetGuard :: coverStaticFloor :: (List.range ms).flatMap fun i =>
    [stepSetPendingRule cp (i + 1), altSetShownRule (i + 1), altSetHiddenRule (i + 1),
      nestedCoverRule (i + 1)]

private theorem setRules_cases {P : DeckRule → Prop} {cp ms : Nat}
    (hg : P stepSetGuard) (hf : P coverStaticFloor)
    (hp : ∀ k, P (stepSetPendingRule cp k))
    (hs : ∀ k, P (altSetShownRule k)) (hh : ∀ k, P (altSetHiddenRule k))
    (hn : ∀ k, P (nestedCoverRule k)) :
    ∀ r ∈ setRules cp ms, P r := by
  intro r hr
  simp only [setRules, List.mem_cons, List.mem_flatMap, List.mem_range,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | ⟨i, _, rfl | rfl | rfl | rfl⟩
  · exact hg
  · exact hf
  · exact hp _
  · exact hs _
  · exact hh _
  · exact hn _

/-- Every rule of the deck's stylesheet, in emission order. -/
public def deckRules (ty : DeckType) (pageSize : String) (coveredPct maxSteps : Nat) :
    List DeckRule :=
  deckBase ty ++ deckReduce ++
    ((if 2 ≤ maxSteps then stepRules coveredPct maxSteps ++ altRules maxSteps else []) ++
      setRules coveredPct maxSteps) ++
    deckPageRule pageSize :: deckPrint maxSteps

private theorem deckRules_forall {P : DeckRule → Prop} {v : DeckType} {pg : String} {cp ms : Nat}
    (hbase : ∀ r ∈ deckBase v, P r)
    (hreduce : ∀ r ∈ deckReduce, P r)
    (hkey : 2 ≤ ms → P (stepKeyframes cp))
    (hrkey : 2 ≤ ms → P (stepRecoverKeyframes cp))
    (hcov : 2 ≤ ms → P (stepFloorCovered cp))
    (hfix : 2 ≤ ms → ∀ r ∈ stepFixed, P r)
    (hsnapped : 2 ≤ ms → ∀ k, P (stepSnappedRule k))
    (hrecovered : 2 ≤ ms → ∀ k, P (stepRecoverFloorRule cp ms k))
    (haltfix : 2 ≤ ms → ∀ r ∈ altReduceFixed, P r)
    (haltsnap : 2 ≤ ms → ∀ k, ∀ r ∈ altSnapRules ms k, P r)
    (hsets : ∀ r ∈ setRules cp ms, P r)
    (hpage : ∀ s, P (deckPageRule s))
    (hprint : ∀ r ∈ deckPrint ms, P r) :
    ∀ r ∈ deckRules v pg cp ms, P r := by
  intro r hr
  simp only [deckRules, List.mem_append, List.mem_cons] at hr
  rcases hr with ((h | h) | (h | h)) | (rfl | h)
  · exact hbase r h
  · exact hreduce r h
  · split at h
    case isTrue hms =>
      simp only [stepRules, stepSnapped, stepRecovered, altRules, altSnapped,
        List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
        List.mem_range] at h
      rcases h with (rfl | rfl | rfl | ((h | ⟨i, -, rfl⟩) | ⟨i, -, rfl⟩)) |
        (h | ⟨i, -, h⟩)
      · exact hkey hms
      · exact hrkey hms
      · exact hcov hms
      · exact hfix hms r h
      · exact hsnapped hms _
      · exact hrecovered hms _
      · exact haltfix hms r h
      · exact haltsnap hms _ r h
    case isFalse => cases h
  · exact hsets r h
  · exact hpage pg
  · exact hprint r h

private theorem altReduceFixed_cases {P : DeckRule → Prop}
    (h1 : P altReduceHiddenRule) (h2 : P altReduceShownRule) :
    ∀ r ∈ altReduceFixed, P r := by
  intro r hr
  simp only [altReduceFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h2

private theorem altSnapRules_cases {P : DeckRule → Prop} {ms k : Nat}
    (h1 : P (altStartCrispRule ms k)) (h2 : P (altStartPendingRule ms k))
    (h3 : P (altEndCrispRule ms k)) (h4 : P (altEndPendingRule ms k)) :
    ∀ r ∈ altSnapRules ms k, P r := by
  intro r hr
  simp only [altSnapRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

private theorem mem_deckRules_base {r : DeckRule} {v : DeckType} {pg : String} {cp ms : Nat}
    (h : r ∈ deckBase v) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

private theorem mem_deckRules_reduce {r : DeckRule} {v : DeckType} {pg : String} {cp ms : Nat}
    (h : r ∈ deckReduce) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

private theorem mem_deckRules_step {r : DeckRule} {v : DeckType} {pg : String} {cp ms : Nat}
    (hms : 2 ≤ ms) (h : r ∈ stepRules cp ms) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append]
  refine Or.inl (Or.inr (Or.inl ?_))
  simpa only [ite_eq_left hms, List.mem_append] using
    (Or.inl h : r ∈ stepRules cp ms ∨ r ∈ altRules ms)

private theorem mem_stepRules_fixed {r : DeckRule} {cp ms : Nat}
    (h : r ∈ stepFixed) : r ∈ stepRules cp ms := by
  simp only [stepRules, List.mem_cons, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))

private theorem deckPrint_subset {ms : Nat} : ∀ r ∈ deckPrint ms, r ∈ deckPrint 2 := by
  intro r hr
  simp only [deckPrint, List.mem_append] at hr ⊢
  rcases hr with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    split at h
    · simpa using h
    · cases h

private theorem deckRules_check {p : DeckRule → Bool} (v : DeckType) (pg : String) (cp ms : Nat)
    (hbase : ∀ r ∈ deckBase v, p r = true)
    (hreduce : ∀ r ∈ deckReduce, p r = true)
    (hkey : p (stepKeyframes cp) = true)
    (hrkey : p (stepRecoverKeyframes cp) = true)
    (hcov : p (stepFloorCovered cp) = true)
    (hfix : ∀ r ∈ stepFixed, p r = true)
    (hsnapped : ∀ k, p (stepSnappedRule k) = true)
    (hrecovered : ∀ k, p (stepRecoverFloorRule cp ms k) = true)
    (haltfix : ∀ r ∈ altReduceFixed, p r = true)
    (haltsnap : ∀ k, ∀ r ∈ altSnapRules ms k, p r = true)
    (hsets : ∀ r ∈ setRules cp ms, p r = true)
    (hpage : ∀ s, p (deckPageRule s) = true)
    (hprint : ∀ r ∈ deckPrint 2, p r = true) :
    ∀ r ∈ deckRules v pg cp ms, p r = true :=
  deckRules_forall hbase hreduce (fun _ => hkey) (fun _ => hrkey) (fun _ => hcov)
    (fun _ => hfix) (fun _ _ => hsnapped _) (fun _ _ => hrecovered _)
    (fun _ => haltfix) (fun _ k => haltsnap k) hsets hpage
    (fun r hr => hprint r (deckPrint_subset r hr))

private theorem deckBase_cases {P : DeckRule → Prop} {v : DeckType}
    (h1 : P { selector := [.lit "html"]
              decls := [("scroll-snap-type", "x mandatory"), ("overflow-y", "clip")] })
    (h2 : P deckGlideRule)
    (h3 : P { selector := [.lit "body"], decls := [("padding", "0")], part := .stage })
    (h4 : P { selector := [.lit "main"]
              decls := [("max-width", "none"), ("margin", "0"), ("font-size", v.body),
                ("line-height", v.leading)]
              part := .stage })
    (h4a : P { selector := [.lit "main"]
               decls := [("display", "flex"), ("align-items", "flex-start")] })
    (h5 : P deckStageRule)
    (h6 : P deckSnapDoor)
    (h6a : P deckLogoRule)
    (h7 : P { selector := [.lit "section.section-page"]
              decls := [("justify-content", "center"), ("align-items", "center")]
              part := .stage })
    (h8 : P { selector := [.lit "h1"], decls := [("font-size", scaleSize "LARGE" "em")]
              part := .stage })
    (h9 : P { selector := [.lit "h2"], decls := [("font-size", scaleSize "Large" "em")]
              part := .stage })
    (h10 : P { selector := [.lit "h3"], decls := [("font-size", scaleSize "large" "em")]
               part := .stage })
    (h11 : P { selector := [.lit "section.slide > header"]
               decls := [("flex-shrink", "0")], part := .stage })
    (h12 : P { selector := [.lit "section.slide > header h2"]
               decls := [("font-size", scaleSize "Large" "em")], part := .stage })
    (h13 : P { selector := [.lit "html"], decls := [("font-size", v.root)], part := .stage })
    (h14 : P { selector := [.lit "pre"], decls := [("padding", "0"), ("background", "none")],
               part := .stage }) :
    ∀ r ∈ deckBase v, P r := by
  intro r hr
  simp only [deckBase, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;>
    assumption

/-- Whether a rule whose syntax depends on a feature is gated on that feature's support. -/
public def gateRespects (r : DeckRule) : Bool :=
  Feature.all.all fun f => r.requires == Gate.supported f || !(r.uses f)

public theorem deck_css_partition (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, gateRespects r = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The property names the floor may use, each universal across current engines per caniuse. -/
public def baselineProps : List String :=
  ["scroll-snap-type", "scroll-snap-align", "scroll-snap-stop",
   "scroll-behavior", "padding", "padding-bottom", "margin", "margin-top", "max-width",
   "width", "flex", "flex-shrink", "background", "overflow-y",
   "min-height", "max-height", "height", "font-size", "line-height", "color",
   "text-align", "opacity", "transform", "display", "flex-direction",
   "justify-content", "align-items", "position", "content",
   "animation", "border", "border-radius", "break-inside", "break-after",
   "break-before", "size", "print-color-adjust", "box-decoration-break",
   "bottom", "left", "right"]

/-- Whether a rule is part of the floor: the base and every `@supports not` block. -/
public def onFloor (r : DeckRule) : Bool :=
  match r.requires with
  | .base => true
  | .unsupported _ => true
  | .supported _ => false

public theorem floor_is_baseline (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(onFloor r) || r.decls.all fun d => baselineProps.contains d.1) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The selector fragments that address what the deck shows: frame stages and steps. -/
public def contentFrags : List String :=
  ["section.slide", "section.section-page", ".step[", ".step:"]

public def targetsContent (r : DeckRule) : Bool :=
  contentFrags.any fun frag =>
    (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s frag

public theorem floor_hides_nothing (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(targetsContent r) ||
        (!(r.decls.contains ("display", "none")) &&
         !(r.decls.contains ("visibility", "hidden")))) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

public def opacityValues (r : DeckRule) : List String :=
  r.decls.filterMap fun d => if d.1 == "opacity" then some d.2 else none

public theorem floor_opacity_mem (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, ∀ o ∈ opacityValues r,
      o = "100%" ∨ o = s!"{cp}%" := by
  refine deckRules_forall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact deckBase_cases (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho)
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    exact fun o ho => nomatch ho
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · exact fun _ o ho => Or.inr (List.mem_singleton.mp ho)
  · intro _ r hr
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;>
      first
        | exact fun o ho => Or.inl (List.mem_singleton.mp ho)
        | exact fun o ho => nomatch ho
  · exact fun _ k o ho => Or.inl (List.mem_singleton.mp ho)
  · exact fun _ k o ho => Or.inr (List.mem_singleton.mp ho)
  · intro _ r hr
    simp only [altReduceFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact fun o ho => nomatch ho
  · exact fun _ k => altSnapRules_cases (fun o ho => nomatch ho)
      (fun o ho => nomatch ho) (fun o ho => nomatch ho) (fun o ho => nomatch ho)
  · exact setRules_cases
      (fun o ho => Or.inl (List.mem_singleton.mp ho))
      (fun o ho => Or.inl (List.mem_singleton.mp ho))
      (fun _ o ho => Or.inr (List.mem_singleton.mp ho))
      (fun _ o ho => nomatch ho) (fun _ o ho => nomatch ho)
      (fun _ o ho => Or.inl (List.mem_singleton.mp ho))
  · exact fun _ o ho => nomatch ho
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · have hnone : ∀ q ∈ printPaged, opacityValues q = [] := by decide
      intro o ho
      rw [hnone r h1] at ho
      exact nomatch ho
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact fun o ho => nomatch ho
        · exact fun o ho => Or.inl (List.mem_singleton.mp ho)
      · cases h2

/-- Whether the rule's selector carries the deck script's own `[data-deck-script]` marker. -/
public def scriptGated (r : DeckRule) : Bool :=
  (r.selector.flatMap SelChunk.lits).any fun s => hasFrag s "[data-deck-script]"

public theorem floor_covered_script_gated (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (!(onFloor r) || scriptGated r ||
        r.decls.all fun d => d.1 != "opacity" || d.2 == "100%") = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

/-- The motion properties the reduced-motion contract covers. -/
public def motionProps : List String := ["animation", "transition", "scroll-behavior"]

/-- The static value a guard must set a motion property back to. -/
public def motionOff : String → String
  | "scroll-behavior" => "auto"
  | _ => "none"

/-- Whether reduce-partition rule `g` covers `r`'s selector. -/
public def guardCovers (g r : DeckRule) : Bool :=
  g.part == Part.reduce &&
    (renderSel g.selector == renderSel r.selector ||
      (renderSel g.selector ++ ":").toList.isPrefixOf
        (renderSel r.selector).toList)

/-- Whether every active motion property of `r` is guarded by the set's reduce partition; reduce
and print rules are exempt. -/
public def motionGuarded (rules : List DeckRule) (r : DeckRule) : Bool :=
  (r.part == Part.reduce || r.part == Part.print) ||
    r.decls.all fun d =>
      !(motionProps.contains d.1) || d.2 == motionOff d.1 ||
        rules.any fun g => guardCovers g r && g.decls.contains (d.1, motionOff d.1)

private theorem motionGuarded_of_guard {rules : List DeckRule} {r g : DeckRule}
    (hg : g ∈ rules)
    (hchk : ∀ d ∈ r.decls, motionProps.contains d.1 = true →
      (guardCovers g r && g.decls.contains (d.1, motionOff d.1)) = true) :
    motionGuarded rules r = true := by
  unfold motionGuarded
  cases hpart : (r.part == Part.reduce || r.part == Part.print)
  · rw [Bool.false_or, List.all_eq_true]
    intro d hd
    cases hmp : motionProps.contains d.1
    · rw [Bool.not_false, Bool.true_or, Bool.true_or]
    · rw [Bool.not_true, Bool.false_or]
      rw [List.any_eq_true.mpr ⟨g, hg, hchk d hd hmp⟩, Bool.or_true]
  · rw [Bool.true_or]

public theorem guards_by_construction (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, motionGuarded (deckRules v pg cp ms) r = true := by
  refine deckRules_forall ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => altReduceFixed_cases rfl rfl)
    (fun _ k => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl))
    (fun _ => rfl) ?_
  · exact deckBase_cases rfl
      (motionGuarded_of_guard (g := deckGlideGuard)
        (mem_deckRules_reduce (by decide)) (by
          simp only [guardCovers, renderSel, deckGlideGuard, deckGlideRule,
            List.map_cons, List.map_nil, SelChunk.render, String.join_cons,
            String.join_nil, String.append_empty, String.toList_append]
          decide))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    rfl
  · intro hms r hr
    have hstep : stepGuard ∈ deckRules v pg cp ms :=
      mem_deckRules_step hms (mem_stepRules_fixed (by decide))
    have hend : stepRecoverGuard ∈ deckRules v pg cp ms :=
      mem_deckRules_step hms (mem_stepRules_fixed (by decide))
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    case inr.inr.inr.inl =>
      exact motionGuarded_of_guard hstep (by
        simp only [guardCovers, renderSel, stepGuard, stepUncoverRule,
          List.map_cons, List.map_nil, SelChunk.render, String.join_cons,
          String.join_nil, String.append_empty, String.toList_append]
        decide)
    case inr.inr.inr.inr.inl =>
      exact motionGuarded_of_guard hend (by
        simp only [guardCovers, renderSel, stepRecoverGuard, stepRecoverRule,
          List.map_cons, List.map_nil, SelChunk.render, String.join_cons,
          String.join_nil, String.append_empty, String.toList_append]
        decide)
    all_goals rfl
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · simp only [printPaged, printFrameEnd, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h1
      rcases h1 with (rfl | rfl) | (rfl | rfl) <;> rfl
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl <;> rfl
      · cases h2

/-- The declarations that bound a stage on screen, each with the value that lifts it in print. -/
public def stageBounds : List (String × String) := [("height", "auto"), ("overflow-y", "visible")]

/-- Whether ungated print rule `g` lifts every bound stage rule `r` declares, at `r`'s own
selector. -/
public def liftsOnPaper (g r : DeckRule) : Bool :=
  g.part == Part.print && g.requires == Gate.base &&
    renderSel g.selector == renderSel r.selector &&
    r.decls.all fun d => match List.lookup d.1 stageBounds with
      | none => true
      | some lift => g.decls.contains (d.1, lift)

/-- Whether a bounded content rule of the stage partition is lifted on paper by the set. -/
public def printLifts (rules : List DeckRule) (r : DeckRule) : Bool :=
  !(r.part == Part.stage && targetsContent r &&
      r.decls.any fun d => (List.lookup d.1 stageBounds).isSome) ||
    rules.any fun g => liftsOnPaper g r

private theorem printLifts_of_lift {rules : List DeckRule} {r g : DeckRule}
    (hg : g ∈ rules) (hl : liftsOnPaper g r = true) : printLifts rules r = true := by
  unfold printLifts
  rw [List.any_eq_true.mpr ⟨g, hg, hl⟩, Bool.or_true]

private theorem mem_deckRules_print {r : DeckRule} {v : DeckType} {pg : String} {cp ms : Nat}
    (h : r ∈ deckPrint ms) : r ∈ deckRules v pg cp ms := by
  simp only [deckRules, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr h)

public theorem print_lifts_stage_bounds_covers (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms, printLifts (deckRules v pg cp ms) r = true := by
  refine deckRules_forall ?_ ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => altReduceFixed_cases rfl rfl)
    (fun _ k => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl))
    (fun _ => rfl) ?_
  · exact deckBase_cases rfl rfl rfl rfl rfl
      (printLifts_of_lift (g := printStageRule)
        (mem_deckRules_print (List.mem_append_left _ (by decide))) (by
          simp only [liftsOnPaper, renderSel, printStageRule, deckStageRule,
            List.map_cons, List.map_nil, SelChunk.render, String.join_cons,
            String.join_nil, String.append_empty]
          decide))
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · intro r hr
    simp only [deckReduce, deckGlideGuard, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl
    rfl
  · intro _ r hr
    simp only [stepFixed, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> rfl
  · intro r hr
    have hr2 := deckPrint_subset r hr
    simp only [deckPrint, List.mem_append] at hr2
    rcases hr2 with h1 | h2
    · simp only [printPaged, printFrameEnd, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at h1
      rcases h1 with (rfl | rfl) | (rfl | rfl) <;> rfl
    · split at h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl <;> rfl
      · cases h2

public theorem snapped_uncovers_every_step (v : DeckType) (pg : String) (cp ms n : Nat)
    (h2 : 2 ≤ n) (hn : n ≤ ms) :
    ∃ k r, n ≤ k ∧ r ∈ deckRules v pg cp ms ∧
      r.selector = [.lit ".slide-track[data-snapped=\"", .num k,
        .lit "\"] :is(", .stepAlts (uncoveredBy k), .lit ")"] ∧
      r.requires = .unsupported .viewTimeline ∧
      ("opacity", "100%") ∈ r.decls ∧ n ∈ uncoveredBy k := by
  refine ⟨n, stepSnappedRule n, Nat.le_refl n, ?_, rfl, rfl, by simp [stepSnappedRule], ?_⟩
  · refine mem_deckRules_step (Nat.le_trans h2 hn) ?_
    simp only [stepRules, stepSnapped, List.mem_cons, List.mem_append,
      List.mem_map, List.mem_range]
    refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨n - 2, by omega, ?_⟩))))
    rw [Nat.sub_add_cancel h2]
  · simp only [uncoveredBy, List.mem_map, List.mem_range]
    exact ⟨n - 2, by omega, by omega⟩

public theorem snap_pages_partition_frames (v : DeckType) (pg : String) (cp ms : Nat) (hms : 2 ≤ ms) :
    (∃ r ∈ deckRules v pg cp ms, r.requires = .base ∧
      r.selector = [.lit "[data-snap]"] ∧
      ("scroll-snap-align", "start") ∈ r.decls) ∧
    (∃ r ∈ deckRules v pg cp ms,
      r.requires = .unsupported .viewTimeline ∧
      r.selector = [.lit ".snap"] ∧ ("display", "none") ∈ r.decls) ∧
    (∃ r ∈ deckRules v pg cp ms,
      r.requires = .unsupported .viewTimeline ∧
      r.selector = [.lit ".slide-track"] ∧
      ("scroll-snap-align", "start") ∈ r.decls) := by
  exact
    ⟨⟨deckSnapDoor, mem_deckRules_base (by simp [deckBase]), rfl, rfl, by decide⟩,
     ⟨stepSnapHide, mem_deckRules_step hms (mem_stepRules_fixed (by decide)),
       rfl, rfl, by decide⟩,
     ⟨stepTrackFloorSnap, mem_deckRules_step hms (mem_stepRules_fixed (by decide)),
       rfl, rfl, by decide⟩⟩

public theorem deck_text_path_free (v : DeckType) (pg : String) (cp ms : Nat) :
    ∀ r ∈ deckRules v pg cp ms,
      (r.decls.all fun d =>
        d.1 != "content" || (d.2 == "\"\"" || d.2 == "none")) = true :=
  deckRules_check v pg cp ms
    (deckBase_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    (by decide) rfl rfl rfl (by decide) (fun _ => rfl) (fun _ => rfl)
    (by decide) (fun _ => altSnapRules_cases rfl rfl rfl rfl)
    (setRules_cases rfl rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl)) (fun _ => rfl) (by decide)

public theorem deckStageMilli_share (x stage : Int) (hs : 0 < stage) :
    deckStageMilli x stage * stage ≤ x * 100000 ∧
    x * 100000 < deckStageMilli x stage * stage + stage := by
  have hne : stage ≠ 0 := by omega
  have hmod := Int.emod_nonneg (x * 100000) hne
  have hlt := Int.emod_lt_of_pos (x * 100000) hs
  have heq := Int.mul_ediv_add_emod (x * 100000) stage
  unfold deckStageMilli
  rw [Int.mul_comm (x * 100000 / stage) stage]
  generalize hr : x * 100000 % stage = r at hmod hlt heq
  generalize hp : stage * (x * 100000 / stage) = p at heq ⊢
  generalize ha : x * 100000 = a at heq ⊢
  omega

/-- The shared frame opening, as a share of the stage. -/
public def frameBodySkipMilli (hasTitle : Bool) (valign : VAlign)
    (size height : Sp) : Int :=
  deckStageMilli ((Ir.frameBodySkip hasTitle valign).resolve size 0) height

public theorem frameBodySkip_projects (hasTitle : Bool) (valign : VAlign)
    (size height : Sp) (hh : 0 < height) :
    frameBodySkipMilli hasTitle valign size height * height ≤
        (Ir.frameBodySkip hasTitle valign).resolve size 0 * 100000 ∧
      (Ir.frameBodySkip hasTitle valign).resolve size 0 * 100000 <
        frameBodySkipMilli hasTitle valign size height * height + height := by
  simpa only [frameBodySkipMilli] using
    deckStageMilli_share ((Ir.frameBodySkip hasTitle valign).resolve size 0) height hh

public theorem deck_type_is_stage_ratio (fontSize height : Int) (hh : 0 < height) :
    deckStageMilli fontSize height * height ≤ fontSize * 100000 ∧
    fontSize * 100000 < deckStageMilli fontSize height * height + height :=
  deckStageMilli_share fontSize height hh

/-- The deck's root size as a share of the stage: the body size scaled by the print leading over
the screen's. -/
public def deckRootMilli (fontSize height : Int) : Int :=
  deckStageMilli (fontSize * (Ir.leadingMilli : Int) / (bodyLeadingMilli : Int)) height

public theorem deck_root_between (fontSize height : Int) (hh : 0 < height) :
    deckRootMilli fontSize height * height ≤
        fontSize * (Ir.leadingMilli : Int) / (bodyLeadingMilli : Int) * 100000 ∧
      fontSize * (Ir.leadingMilli : Int) / (bodyLeadingMilli : Int) * 100000 <
        deckRootMilli fontSize height * height + height :=
  deckStageMilli_share _ height hh

/-- A length on the deck's stage: its absolute part as a share of the stage height. -/
public def deckLengthCss (stage : Sp) (l : Length) : String :=
  let parts :=
    (if l.sp != 0 then [s!"{decMilli (deckStageMilli l.sp stage)}vh"] else []) ++
    (if l.em != 0 then [s!"{decMilli l.em}em"] else []) ++
    (if l.ex != 0 then [s!"{decMilli l.ex}ex"] else [])
  match parts with
  | [] => "0pt"
  | [one] => one
  | many => "calc(" ++ String.intercalate " + " many ++ ")"

/-- `cssSourced` on the deck's stage. -/
public def deckSourced (stage : Sp) (g : Ir.Sourced SymGlue) : String :=
  match g.token.bind tokenVar? with
  | some v => s!"var({v}, {deckLengthCss stage g.value.width})"
  | none => deckLengthCss stage g.value.width

private def deckType (page : PageSpec) : DeckType :=
  { body := s!"{milliFactor (deckStageMilli page.fontSize page.height).toNat}vh"
    root := s!"{milliFactor (deckRootMilli page.fontSize page.height).toNat}vh"
    leading := milliFactor
      (stepLineHeightMilli page.skipScale page.leading page.fontSize "normalsize" 1000) }

public theorem image_share_agrees (l : Image.Len) (iW iH textW textH stage : Int)
    (hs : 0 < stage) :
    (Image.resolveSize { width := some l } iW iH textW textH).1
        = l.resolve textW textH ∧
    deckStageMilli (l.resolve textW textH) stage * stage
        ≤ (Image.resolveSize { width := some l } iW iH textW textH).1 * 100000 ∧
    (Image.resolveSize { width := some l } iW iH textW textH).1 * 100000
        < deckStageMilli (l.resolve textW textH) stage * stage + stage :=
  ⟨rfl, deckStageMilli_share (l.resolve textW textH) stage hs⟩

/-! ## Deck script -/

/-- The deck's constant script: arrow, page, space, Home and End keys page between `[data-snap]`
points, and the floor's step state follows the current snap. -/
public def deckScript : String :=
  "(() => {
  document.documentElement.dataset.deckScript = \"\";
  const snaps = Array.from(document.querySelectorAll(\"[data-snap]\"));
  if (snaps.length === 0) return;
  const reduce = matchMedia(\"(prefers-reduced-motion: reduce)\");
  const stageOf = (el) => el.closest(\".slide-track\") || el;
  const links = snaps.map(s => s.dataset.slideLabel);
  const routes = new Map(links.map((key, i) => [key, i]));
  links.forEach((key, i) => {
    if (key.endsWith(\".1\")) routes.set(key.slice(0, -2), i);
  });
  const box = (el) => {
    const r = el.getBoundingClientRect();
    const stage = stageOf(el);
    return r.width > 0 ? r : (stage.querySelector(\"section.slide\") || stage).getBoundingClientRect();
  };
  let cur = 0;
  let destination = null;
  let seenHash = location.hash;
  if (\"scrollRestoration\" in history) history.scrollRestoration = \"manual\";
  const mark = () => {
    const track = snaps[cur].closest(\".slide-track\");
    if (!track) return;
    let k = 0;
    for (const s of snaps) {
      if (s.closest(\".slide-track\") === track) k += 1;
      if (s === snaps[cur]) break;
    }
    track.dataset.snapped = String(k);
  };
  const writeHash = (mode) => {
    const hash = \"#\" + encodeURIComponent(links[cur]);
    if (location.hash !== hash)
      history[mode === \"push\" ? \"pushState\" : \"replaceState\"](history.state, \"\", hash);
    seenHash = location.hash;
  };
  const go = (i, mode, instant = false) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    destination = cur;
    mark();
    if (mode) writeHash(mode);
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : stageOf(snaps[cur]);
    el.scrollIntoView({ behavior: instant || reduce.matches ? \"instant\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
    if (Math.abs(box(snaps[cur]).left) < 1) destination = null;
  };
  const sync = () => {
    if (location.hash !== seenHash) return;
    if (destination !== null) {
      if (Math.abs(box(snaps[destination]).left) >= 1) return;
      destination = null;
    }
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) {
      cur = best;
      mark();
      writeHash(\"replace\");
    }
  };
  const readHash = () => {
    seenHash = location.hash;
    let key;
    try { key = decodeURIComponent(location.hash.slice(1)); } catch (_) { return; }
    if (!key) { go(0, null, true); return; }
    let i = routes.get(key);
    if (i === undefined) {
      const target = document.getElementById(key);
      if (!target) return;
      i = snaps.indexOf(target);
      if (i < 0) i = snaps.findIndex(s => stageOf(s).contains(target));
    }
    if (i >= 0) go(i, null, true);
  };
  addEventListener(\"scroll\", sync, { passive: true });
  addEventListener(\"hashchange\", readHash);
  for (const event of [\"wheel\", \"touchstart\", \"pointerdown\"])
    addEventListener(event, () => { destination = null; }, { passive: true });
  readHash();
  if (!location.hash) { sync(); writeHash(\"replace\"); }
  const skip = (i, dir) => {
    if (!reduce.matches) return i;
    while (snaps[i] && stageOf(snaps[i]) === stageOf(snaps[cur])) i += dir;
    if (!snaps[i]) return cur;
    while (i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName) ||
          (t.tagName === \"SUMMARY\" && (e.key === \" \" || e.key === \"Enter\")))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") {
      i = snaps.length - 1;
      while (reduce.matches && i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    }
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i, \"push\");
  });
})();"

public theorem deck_script_constant : deckScript =
  "(() => {
  document.documentElement.dataset.deckScript = \"\";
  const snaps = Array.from(document.querySelectorAll(\"[data-snap]\"));
  if (snaps.length === 0) return;
  const reduce = matchMedia(\"(prefers-reduced-motion: reduce)\");
  const stageOf = (el) => el.closest(\".slide-track\") || el;
  const links = snaps.map(s => s.dataset.slideLabel);
  const routes = new Map(links.map((key, i) => [key, i]));
  links.forEach((key, i) => {
    if (key.endsWith(\".1\")) routes.set(key.slice(0, -2), i);
  });
  const box = (el) => {
    const r = el.getBoundingClientRect();
    const stage = stageOf(el);
    return r.width > 0 ? r : (stage.querySelector(\"section.slide\") || stage).getBoundingClientRect();
  };
  let cur = 0;
  let destination = null;
  let seenHash = location.hash;
  if (\"scrollRestoration\" in history) history.scrollRestoration = \"manual\";
  const mark = () => {
    const track = snaps[cur].closest(\".slide-track\");
    if (!track) return;
    let k = 0;
    for (const s of snaps) {
      if (s.closest(\".slide-track\") === track) k += 1;
      if (s === snaps[cur]) break;
    }
    track.dataset.snapped = String(k);
  };
  const writeHash = (mode) => {
    const hash = \"#\" + encodeURIComponent(links[cur]);
    if (location.hash !== hash)
      history[mode === \"push\" ? \"pushState\" : \"replaceState\"](history.state, \"\", hash);
    seenHash = location.hash;
  };
  const go = (i, mode, instant = false) => {
    cur = Math.min(Math.max(i, 0), snaps.length - 1);
    destination = cur;
    mark();
    if (mode) writeHash(mode);
    const el = snaps[cur].getBoundingClientRect().width > 0
      ? snaps[cur] : stageOf(snaps[cur]);
    el.scrollIntoView({ behavior: instant || reduce.matches ? \"instant\" : \"smooth\",
      inline: \"start\", block: \"nearest\" });
    if (Math.abs(box(snaps[cur]).left) < 1) destination = null;
  };
  const sync = () => {
    if (location.hash !== seenHash) return;
    if (destination !== null) {
      if (Math.abs(box(snaps[destination]).left) >= 1) return;
      destination = null;
    }
    let best = cur;
    for (let i = 0; i < snaps.length; i += 1)
      if (Math.abs(box(snaps[i]).left) < Math.abs(box(snaps[best]).left)) best = i;
    if (box(snaps[best]).left !== box(snaps[cur]).left) {
      cur = best;
      mark();
      writeHash(\"replace\");
    }
  };
  const readHash = () => {
    seenHash = location.hash;
    let key;
    try { key = decodeURIComponent(location.hash.slice(1)); } catch (_) { return; }
    if (!key) { go(0, null, true); return; }
    let i = routes.get(key);
    if (i === undefined) {
      const target = document.getElementById(key);
      if (!target) return;
      i = snaps.indexOf(target);
      if (i < 0) i = snaps.findIndex(s => stageOf(s).contains(target));
    }
    if (i >= 0) go(i, null, true);
  };
  addEventListener(\"scroll\", sync, { passive: true });
  addEventListener(\"hashchange\", readHash);
  for (const event of [\"wheel\", \"touchstart\", \"pointerdown\"])
    addEventListener(event, () => { destination = null; }, { passive: true });
  readHash();
  if (!location.hash) { sync(); writeHash(\"replace\"); }
  const skip = (i, dir) => {
    if (!reduce.matches) return i;
    while (snaps[i] && stageOf(snaps[i]) === stageOf(snaps[cur])) i += dir;
    if (!snaps[i]) return cur;
    while (i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    return i;
  };
  addEventListener(\"keydown\", (e) => {
    if (e.ctrlKey || e.altKey || e.metaKey || e.defaultPrevented) return;
    const t = e.target;
    if (t instanceof Element &&
        (t.isContentEditable || /^(input|textarea|select|button)$/i.test(t.tagName) ||
          (t.tagName === \"SUMMARY\" && (e.key === \" \" || e.key === \"Enter\")))) return;
    let i = null;
    if (e.key === \"Home\") i = 0;
    else if (e.key === \"End\") {
      i = snaps.length - 1;
      while (reduce.matches && i > 0 && stageOf(snaps[i - 1]) === stageOf(snaps[i])) i -= 1;
    }
    else if ((e.key === \" \" && e.shiftKey) || e.key === \"ArrowLeft\" ||
        e.key === \"ArrowUp\" || e.key === \"PageUp\") i = skip(cur - 1, -1);
    else if ((e.key === \" \" && !e.shiftKey) || e.key === \"ArrowRight\" ||
        e.key === \"ArrowDown\" || e.key === \"PageDown\") i = skip(cur + 1, 1);
    if (i === null) return;
    e.preventDefault();
    go(i, \"push\");
  });
})();" := by rfl

/-- The script's one emission site, for the deck alone. -/
public def deckScriptNodes (deck : Bool) : Array Node :=
  if deck then #[Node.script #[] deckScript] else #[]

public theorem deck_script_gated (b : Bool) :
    deckScriptNodes b = if b then #[Node.script #[] deckScript] else #[] := by rfl

/-! ## Math renderer -/

/-- The renderer's one emission site: its captured text as a script node, when the run declares
one. -/
public def mathBoundaryNodes (renderer : Option String) : Array Node :=
  match renderer with
  | some text => #[Node.script #[("data-math-boundary", "")] text]
  | none => #[]

/-- Artifact-specific. -/
public theorem math_boundary_contract (renderer : Option String) :
    mathBoundaryNodes renderer =
      (renderer.map fun text => Node.script #[("data-math-boundary", "")] text).toArray := by
  cases renderer <;> rfl

/-- The slide sections' stylesheet: the paged deck for the slides class, the card for every
other. -/
private def slideCss (doc : Doc) : String :=
  -- the handout card, every non-deck class's only rendering
  let handout :=
    s!"section.slide \{ border: {slideBorderPx}px solid {roleRef .rule}; border-radius: {slideRadiusPx}px;\n" ++
    s!"  padding: {slidePadV} {slidePadH}; margin: 0; break-inside: avoid; }\n" ++
    s!"* + section.slide \{ margin-top: {slidePadV}; }\n"
  -- inside this split, so the deck's screen override stands after it
  let headerH2 :=
    s!"section.slide > header h2 \{ font-size: {scaleSize "Large" "rem"}; }\n"
  if doc.docClass == .slides then
    let maxSteps := doc.body.foldl (fun n b => max n (Ir.frameSteps b)) 1
    -- the covered shade is the PDF cover's own fraction (`Ir.Design.cover`)
    headerH2 ++
      emitDeckRules (deckRules (deckType doc.page)
        (deckPageSize doc.page) (Design.ofDoc doc).coveredFraction maxSteps)
  else handout ++ headerH2

/-- Whether the document carries a listing with a caption or line numbers, gating the listing
CSS. -/
private def docHasListing (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || match bl with
      | .verbatim _ _ spec => spec.caption.isSome || spec.numbers
      | _ => false)
    (fun b _ => b) false doc.body

/-- The class a token wears: its Pygments type's, behind `tok-`. -/
public def tokenClass (k : ListingHighlight.Kind) : String := "tok-" ++ k.cssClass

/-- The token classes a document's highlighted listings use, ink-role ones aside, each with its
code role, in first-use order. -/
public def docTokenClasses (doc : Doc) : Array (String × ListingHighlight.Role) :=
  let kinds : Array ListingHighlight.Kind := Ir.foldBlocks (fun acc bl => match bl with
      | .verbatim _ _ spec => spec.highlight.foldl (fun acc line => line.foldl (fun acc t =>
          if acc.contains t.kind then acc else acc.push t.kind) acc) acc
      | _ => acc)
    (fun acc _ => acc) #[] doc.body
  kinds.foldl (fun acc k =>
    let c := tokenClass k
    if k.role == .ink || acc.any (·.1 == c) then acc else acc.push (c, k.role)) #[]

/-- The rules that colour a document's tokens, one per code role its listings use. -/
public def tokenRules (doc : Doc) : String :=
  let classes := docTokenClasses doc
  String.join (ListingHighlight.Role.all.filterMap fun r =>
    let cs := (classes.filter (·.2 == r)).map (·.1)
    if cs.isEmpty then none else
      some s!":is({", ".intercalate (cs.toList.map ("." ++ ·))}) \{ color: {roleRef (Ir.Role.ofCode r)}; }\n")

/-- Whether the document carries a table whose columns narrow, gating its print rule. -/
private def docHasNarrowingTable (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || match bl with
      | .table cols .. => cols.any (·.narrows)
      | _ => false)
    (fun b _ => b) false doc.body

/-- Whether the document carries a disclosure, gating its summary and print rules. -/
private def docHasDisclosure (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || bl matches .disclosure ..) (fun b _ => b) false doc.body

private def disclosureCss : String :=
  s!"summary \{ {" ".intercalate ((fontStyleDecls [] Ir.disclosureSummaryStyle).getD #[]).toList} }\n"

/-- On paper a disclosure prints its body, and its summary without the toggle marker. -/
private def disclosurePrintCss : String :=
  "  details::details-content { content-visibility: visible; }\n" ++
  "  summary { list-style: none; }\n" ++
  "  summary::-webkit-details-marker { display: none; }\n"

/-- Whether the document carries a reference list, gating its rules. -/
private def docHasBibliography (doc : Doc) : Bool :=
  Ir.foldBlocks (fun b bl => b || bl matches .bibliography ..) (fun b _ => b) false doc.body

/-- The reference list as the page sets it: hanging author-year entries, or a label column with
`\labelsep` (.5em, article.cls) before the text. -/
private def bibCss (doc : Doc) : String :=
  let hang := s!"var(--{Ir.bibHangName}, {cssLength (Ir.bibHang {}).width})"
  let size := doc.page.fontSize
  let sepMilli := (Ir.bibSepDefault size).width.sp * 1000 / (max size 1)
  let sep := s!"var(--{Ir.bibSepName}, {decMilli sepMilli}em)"
  let flush := Ir.foldBlocks (fun b bl => b || match bl with
    | .bibliography _ _ items => items.any (·.labelFlush)
    | _ => false) (fun b _ => b) false doc.body
  s!"ul.bibliography \{ display: grid; row-gap: {sep}; padding: 0; list-style: none; }\n" ++
  s!"ul.bibliography.unmarked > li \{ padding-left: {hang}; text-indent: calc(-1 * {hang}); }\n" ++
  "ul.bibliography:not(.unmarked) { grid-template-columns: max-content minmax(0, 1fr);\n" ++
  "  column-gap: 0.5em; }\n" ++
  "ul.bibliography:not(.unmarked) > li { display: grid; grid-column: 1 / -1;\n" ++
  "  grid-template-columns: subgrid; }\n" ++
  ".bib-marker { text-align: right; }\n" ++
  (if flush then ".bib-marker.flush { text-align: left; }\n" else "")

/-- The HTML projection of an OpenType feature record. -/
public def kernCssFor (features : Ir.Features) : String :=
  if features.kern then "  font-kerning: normal;\n" else ""

public def kernCss : String := kernCssFor Ir.features

/-- Whether a declared style paints a colour of its own outside the inline regions the document
walk reads. -/
public def styleColored (st : ElementStyle) : Bool :=
  st.rule.isSome || st.separator.isSome || st.hover.isSome || st.focus.isSome ||
    st.color.isSome ||
    ((st.authorFont.getD #[]) :: st.slots.toList.flatMap (fun s =>
      s.parts.toList.flatMap fun p => [p.content, p.font.getD #[]])).any
      (Ir.foldInlines (fun a i => a || i matches .colored _ _ _) false)

/-- Whether a loaded image can paint on the page's own ground. -/
public def imageSeeThrough (en : Image.Loaded) : Bool :=
  imageShips en && match en.info with
    | some p => p.alpha != .opaque || Image.isSvg (resolvedSrc en) || en.webSvg.isSome
    | none => false

/-- The class a float kind's `<figure>` carries. -/
private def floatKindClass : Ir.FloatKind → String
  | .figure => "float"
  | .table => "table-float"
  | .sub => "subfloat"
  | .algorithm => "algorithm-float"

/-- Each float kind's caption tokens, placed by its declared caption position. -/
private def captionScopeCss (doc : Doc) : String :=
  let pos := doc.captionPos
  let chain (s : Ir.CaptionSkip) (k : Ir.FloatKind) : String :=
    let dflt := match doc.docClass.record.lists, s with
      | .beamer, _ =>
        lineageLength doc (Ir.CaptionSkip.defaultFor .beamer s doc.page.fontSize).width.sp
      | _, .above => quantaRem (gapK "caption")
      | _, .below => "0px"
    (s.keys k).foldr (fun key acc => s!"var(--{key}, {acc})") dflt
  String.join ([Ir.FloatKind.figure, .table, .sub, .algorithm].map fun k =>
    let p := Ir.captionPosFor doc.docClass.record.lists pos k
    let (obj, far) := Ir.captionSides p false
    let (objTop, farTop) := Ir.captionSides p true
    let s := k.captionScope
    s!"figure.{floatKindClass k} \{ --ltx-capsep: {chain obj k}; --ltx-capfar: {chain far k};\n" ++
    s!"  --ltx-capsep-top: {chain objTop k}; --ltx-capfar-top: {chain farTop k};\n" ++
    s!"  --ltx-capmargin: var(--{s}captionmargin, var(--captionmargin, 0px)); }\n")

/-- Whether the page's paragraphs hyphenate: a justified page that does not turn hyphenation off. -/
public def autoHyphens (page : PageSpec) : Bool :=
  page.justify != some false && page.hyphenate != some false

/-- The line-through rule thickness, from the token the PDF path also reads. -/
public def lineThroughThicknessCss : String := s!"{Ir.lineThroughThickness.toPtString}pt"

@[simp] public theorem lineThroughThicknessCss_agree :
    lineThroughThicknessCss = s!"{Ir.lineThroughThickness.toPtString}pt" := by rfl

public def figureWordsClass : String := "figure-words"

/-- A figure's words as the page carries them, out of sight and out of the accessibility tree. -/
public def figureWordsNode (words : String) : Node :=
  Html.elem "span" #[Html.text words] #[("class", figureWordsClass), ("aria-hidden", "true")]

/-- Out of flow and clipped to nothing: WCAG technique C7's visually hidden pattern. -/
public def figureWordsRule : String :=
  s!".{figureWordsClass} \{ position: absolute; width: 1px; height: 1px; overflow: hidden; \
clip-path: inset(50%); white-space: nowrap; }\n"

/-- The base stylesheet's rules, after its custom properties. -/
public def baseRules (doc : Doc) (pairs : List (Nat × Nat) := []) (figureWords : Bool := false) :
    String :=
  let tl := tableLengthFallback doc
  "*, *::before, *::after { box-sizing: border-box; }\n" ++
  "body {\n" ++
  "  margin: 0;\n" ++
  s!"  padding: {quantaRem 3} 1.25rem {quantaRem 6};\n" ++
  s!"  background: {roleRef .page};\n" ++
  s!"  color: {roleRef .ink};\n" ++
  "  font-family: var(--font-body);\n" ++
  -- the reader's own declared size
  "  font-size: 1rem;\n" ++
  s!"  line-height: {milliFactor bodyLeadingMilli};\n" ++
  "  text-rendering: optimizeLegibility;\n" ++
  kernCss ++
  "  -webkit-font-smoothing: antialiased;\n" ++
  "}\n" ++
  "main { max-width: var(--measure); margin: 0 auto; }\n" ++
  -- headings from the IR's own scale; margins belong to `blockGapRules` alone
  "h1, h2, h3, h4, h5, h6 {\n" ++
  "  font-family: var(--font-sans);\n" ++
  "  font-weight: 600;\n" ++
  s!"  line-height: {milliFactor Ir.leadingMilli};\n" ++
  "  text-wrap: balance;\n" ++
  "}\n" ++
  s!"h1 \{ font-size: {scaleSize "LARGE" "rem"}; }\n" ++
  s!"h2 \{ font-size: {scaleSize "Large" "rem"}; }\n" ++
  s!"h3 \{ font-size: {scaleSize "large" "rem"}; }\n" ++
  -- the deeper ranks share the body size, in `em` to follow the local scale
  s!"h4, h5, h6 \{ font-size: {scaleSize "normalsize" "em"}; }\n" ++
  -- hyphenation follows the declared language; a ragged or unhyphenated page hyphenates nothing
  s!"p \{ hyphens: {if autoHyphens doc.page then "auto" else "manual"}; }\n" ++
  -- markdown inline code may break rather than overflow its line, as its page breaks it
  (if doc.surface == .markdown then
    ":where(:not(pre) > code) { overflow-wrap: break-word; }\n" else "") ++
  listIndentCss doc.docClass.record.lists ++
  (if figureWords then figureWordsRule else "") ++
  s!"li::marker \{ color: {roleRef .marker}; }\n" ++
  -- the class-default list marks per nesting level, as classes.dtx sets them
  "ul { list-style-type: disc; }\n" ++
  "ul ul > li::marker { content: \"\u2013  \"; font-weight: 600; }\n" ++
  "ul ul ul > li::marker { content: \"\u2217  \"; }\n" ++
  "ul ul ul ul > li::marker { content: \"\u00b7  \"; }\n" ++
  "ol { list-style-type: decimal; }\n" ++
  "ol ol { list-style-type: lower-alpha; }\n" ++
  "ol ol > li::marker { content: \"(\" counter(list-item, lower-alpha) \")  \"; }\n" ++
  "ol ol ol { list-style-type: lower-roman; }\n" ++
  "ol ol ol > li::marker { content: counter(list-item, lower-roman) \".  \"; }\n" ++
  "ol ol ol ol { list-style-type: upper-alpha; }\n" ++
  "ol ol ol ol > li::marker { content: counter(list-item, upper-alpha) \".  \"; }\n" ++
  -- a link inherits its colour; the underline band is the font's own (`from-font`)
  "a { color: inherit; text-decoration-thickness: from-font;\n" ++
  "    text-underline-position: from-font; text-decoration-skip-ink: auto; }\n" ++
  "u { text-decoration: underline; text-decoration-skip-ink: auto;\n" ++
  "    text-decoration-thickness: from-font; text-underline-position: from-font; }\n" ++
  s!"s \{ text-decoration-line: line-through; text-decoration-thickness: {lineThroughThicknessCss};\n" ++
  "    text-decoration-skip-ink: none; }\n" ++
  s!"a:focus-visible \{ outline: 2px solid {roleRef .focus}; outline-offset: 2px; }\n" ++
  "code, pre { font-family: var(--font-mono); }\n" ++
  -- a code unit never breaks, save in a box too narrow to hold it
  s!"pre .{codeTokClass} \{ white-space: nowrap; }\n" ++
  s!"@container (width < {codeReleaseWidth}) \{ pre .{codeLongTokClass} \{ white-space: inherit; } }\n" ++
  -- a scroll container has no automatic flex minimum (Flexbox 1 §4.5), so code never shrinks
  (if (Design.at doc.palette .light .codeSurface).isSome then
    s!"pre \{ background: {roleRef .codeSurface}; padding: {quantaRem 1} 1rem; overflow-x: auto;\n" ++
    "      border-radius: 4px; flex-shrink: 0; }\n"
   else "pre { background: none; padding: 0; overflow-x: auto; flex-shrink: 0; }\n") ++
  -- a listing's caption stands above (listings' default); line numbers are a CSS counter
  (if docHasListing doc then
    "figure.listing { margin: 0; }\n" ++
    s!"figure.listing > figcaption \{ text-align: center; margin-bottom: {quantaRem 1}; }\n" ++
    "pre.numbered { counter-reset: listing-line; }\n" ++
    "pre.numbered .line::before { counter-increment: listing-line;\n" ++
    "  content: counter(listing-line); display: inline-block; width: 2.25em;\n" ++
    s!"  padding-right: 1em; text-align: right; color: {roleRef .marker};\n" ++
    "  user-select: none; }\n"
   else "") ++
  (if docHasBibliography doc then bibCss doc else "") ++
  alignScopeRule "centered" .center ++
  raggedRule .left ++ raggedRule .right ++
  -- a box's content starts from no side of its own (`\@parboxrestore`)
  alignScopeRule "column" .left ++
  -- outside any alignment scope a table stands flush left
  "table { margin-left: var(--ltx-box-left, 0); margin-right: var(--ltx-box-right, auto); }\n" ++
  ".fill { flex: 1 1 auto; }\n" ++
  -- a skip box: a positive skip is its height; opening a frame it pays `\vskip-\parskip`
  s!".{skipClass} \{ display: flow-root; flex: none; height: max(0rem, var(--skip, 0rem));\n" ++
    "  --frame-body-before: calc(0rem - var(--parskip, 0rem)); }\n" ++
  s!"{skipCarrier} \{ --frame-body-before: calc(0rem - var(--parskip, 0rem)); }\n" ++
  -- an exact pair is a grid reserving the right column before the left wraps
  ".entry, .entry-row { display: flex; flex-wrap: wrap; column-gap: 0.4rem;\n" ++
  "  align-items: baseline; }\n" ++
  ".entry > .group + .group, .entry-row > .group + .group { margin-left: auto; }\n" ++
  -- a fill spans its line whatever the paragraph's alignment
  ".entry > .group:first-child, .entry-row > .group:first-child { text-align: left; }\n" ++
  ".entry > .group:last-child, .entry-row > .group:last-child { text-align: right; }\n" ++
  ".entry-pair { display: grid;\n" ++
  "  grid-template-columns: minmax(0, 1fr) max-content; }\n" ++
  ".entry-rows { display: flex; flex-direction: column; }\n" ++
  ".sans { font-family: var(--font-sans); }\n" ++
  -- each font-axis class resets exactly its axis
  ".rm { font-family: var(--font-body); }\n" ++
  ".md { font-weight: 400; }\n" ++
  ".up { font-style: normal; font-variant-caps: normal; }\n" ++
  (if docHasDisclosure doc then disclosureCss else "") ++
  ".ruled::after { content: \"\"; flex: 1; border-top: 1px solid var(--rule-color);\n" ++
  -- half the heading's x-height above the baseline, where the PDF draws the rule
  "  transform: translateY(-0.5ex); }\n" ++
  -- `all-small-caps`: mixed-case source sets at one height
  ".sc { font-variant-caps: all-small-caps; }\n" ++
  -- booktabs' lengths come from `tableLengthFallback`; rows stand at the print leading
  s!"table.booktabs \{ border-collapse: collapse; line-height: {decMilli (printLeadingMilli doc.page)}; }\n" ++
  s!"table.booktabs td, table.booktabs th \{ padding: 0 var(--tabcolsep, {tl "tabcolsep"});\n" ++
  "  vertical-align: top; }\n" ++
  "table.booktabs th { font-weight: inherit; }\n" ++
  cellSideRule .left ++ cellSideRule .center ++ cellSideRule .right ++
  "table.booktabs.nopadl tr > td:first-child,\n" ++
  "table.booktabs.nopadl tr > th:first-child { padding-left: 0; }\n" ++
  "table.booktabs.nopadr tr > td:last-child,\n" ++
  "table.booktabs.nopadr tr > th:last-child { padding-right: 0; }\n" ++
  s!"tr.bt-heavy-above > td, tr.bt-heavy-above > th \{ border-top: var(--heavyrulewidth, {tl "heavyrulewidth"}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {tl "belowrulesep"}); }\n" ++
  s!"tr.bt-light-above > td, tr.bt-light-above > th \{ border-top: var(--lightrulewidth, {tl "lightrulewidth"}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {tl "belowrulesep"}); }\n" ++
  s!"tr.bt-heavy-below > td, tr.bt-heavy-below > th \{ border-bottom: var(--heavyrulewidth, {tl "heavyrulewidth"}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {tl "aboverulesep"}); }\n" ++
  s!"tr.bt-light-below > td, tr.bt-light-below > th \{ border-bottom: var(--lightrulewidth, {tl "lightrulewidth"}) solid;\n" ++
  s!"  padding-bottom: var(--aboverulesep, {tl "aboverulesep"}); }\n" ++
  s!"tr.bt-pre > td, tr.bt-pre > th \{ padding-bottom: var(--aboverulesep, {tl "aboverulesep"}); }\n" ++
  s!"td.bt-cmid, th.bt-cmid \{ border-top: var(--cmidrulewidth, {tl "cmidrulewidth"}) solid;\n" ++
  s!"  padding-top: var(--belowrulesep, {tl "belowrulesep"}); }\n" ++
  -- `white-space` has no effect on a `<col>`, so a natural column's nowrap sits on its cells
  ":where(table.booktabs td.bt-nowrap, table.booktabs th.bt-nowrap)" ++
  " { white-space: nowrap; }\n" ++
  -- `--algindent` defaults to algorithm2e's \SetInd{0.5em}{1em} + 0.4pt, ≈1.5em
  "ol.algorithm { list-style: none; padding-left: 0; counter-reset: algline; }\n" ++
  "ol.algorithm ol { list-style: none; padding-left: var(--algindent, 1.5em); }\n" ++
  -- pseudocode lists are not enumerates, so their marker content resets
  "ol.algorithm li::marker, ol.algorithm ol > li::marker,\n" ++
  "ol.algorithm ol ol > li::marker, ol.algorithm ol ol ol > li::marker {\n" ++
  "  content: none; }\n" ++
  "ol.algorithm.numbered { padding-left: var(--algnumindent, 2em); position: relative; }\n" ++
  "ol.algorithm.numbered li { counter-increment: algline; }\n" ++
  -- one number column inside the block (algorithm2e's own inset), whatever the line's depth
  "ol.algorithm.numbered li::before { content: counter(algline);\n" ++
  s!"  color: {roleRef .marker}; font-size: 0.8em; width: 1.5em;\n" ++
  "  position: absolute; left: 0; text-align: right; }\n" ++
  "figure.float > table { margin-left: auto; margin-right: auto; }\n" ++
  "figure.float > img { display: block; margin: 0 auto; }\n" ++
  captionScopeCss doc ++
  "figure.float > figcaption { margin-top: var(--ltx-capsep);\n" ++
  "  padding: 0 var(--ltx-capmargin) var(--ltx-capfar);\n" ++
  "  text-align: center; text-wrap: balance; }\n" ++
  -- the text-side skip is padding, since a margin would collapse into the float's separation
  "figure.float > figcaption:first-child { margin-top: 0;\n" ++
  "  padding-top: var(--ltx-capfar-top); padding-bottom: 0;\n" ++
  "  margin-bottom: var(--ltx-capsep-top); }\n" ++
  blockGapCss doc.docClass.record.lists doc.page.fontSize doc.tokens pairs
    (shaped := [Ir.TitledKind.block, .alert, .example].any fun k => (Ir.blockShapeOf doc.styles k).isSome)
    (squeezed := anySqueezed doc) ++
  slideCss doc ++
  -- a standout frame inverts, at the scale's Large step for the whole frame
  s!"section.slide.standout \{ background: {roleRef .standoutGround};\n" ++
  s!"  color: {roleRef .standoutInk}; text-align: center;\n" ++
  s!"  font-size: {scaleSize standoutStep "em"}; font-weight: 600;\n" ++
  "  display: flex; flex-direction: column; justify-content: center; }\n" ++
  deckAreaCss doc ++
  (if doc.docClass == .slides then frameOpeningCss doc ++ fillBeforeCss else "") ++
  -- a deck's steps set their own leading; a reading page keeps one line height
  sizeRules doc.page.scale
    (if doc.docClass == .slides then
      some (doc.page.skipScale, doc.page.leading, doc.page.fontSize) else none) ++
  -- the resolved math face; the stack behind it serves a page with no shipped face
  "math, .math { font-family: var(--font-math, \"Latin Modern Math\", \"STIX Two Math\", math); }\n" ++
  -- a display's skips are the block boundary's, never the formula's margin
  ".display { text-align: center; }\n" ++
  -- a numbered display: the tag on the right edge, centred on the formula (amsmath)
  ".equation { display: flex; align-items: center; }\n" ++
  ".equation > .math { flex: 1 1 auto; text-align: center; }\n" ++
  "@media print {\n" ++
  -- paper and ink are the page's roles, printed exactly
  s!"  html, body \{ print-color-adjust: exact; }\n" ++
  s!"  body \{ background: {roleRef .page}; color: {roleRef .ink}; padding: 0; }\n" ++
  -- paper has no scroll, so a code line wider than its box wraps inside it
  "  pre { overflow-x: visible; white-space: pre-wrap; overflow-wrap: anywhere; }\n" ++
  (if docHasDisclosure doc then
    disclosurePrintCss ++
      disclosurePrintGapCss doc.docClass.record.lists doc.page.fontSize doc.tokens pairs
        (shaped := [Ir.TitledKind.block, .alert, .example].any fun k =>
          (Ir.blockShapeOf doc.styles k).isSome)
        (squeezed := anySqueezed doc)
  else "") ++
  -- an overhanging markdown table stands centred over both margins, as its page sets it
  (if docHasNarrowingTable doc then
    "  table.booktabs.bt-overhang { position: relative; left: 50%; transform: translateX(-50%); }\n"
  else "") ++
  "}\n" ++
  "@media (prefers-reduced-motion: reduce) {\n" ++
  "  * { animation: none !important; transition: none !important; }\n" ++
  "}\n" ++
  "@media (max-width: 30rem) {\n" ++
  "  .entry-pair { grid-template-columns: minmax(0, 1fr); }\n" ++
  "}"

/-- The roles the reader aliases read. -/
public def readerRoles : List Ir.Role := [.page, .ink, .muted, .accent, .codeSurface, .rule]

/-- The roles a set of scheme tables must declare for a set of reads, aliases included. -/
public def cssRolesIn (tables : List (Ir.Scheme × Ir.Palette)) (seed : List Ir.Role) :
    List Ir.Role :=
  Ir.Role.all.filter fun r => seed.any fun q =>
    tables.any fun (s, v) => (Ir.Design.reach v [s] q).contains r

/-- The roles a page's own stylesheet declares. -/
public def pageRoles (cfg : Config) (doc : Doc) : List Ir.Role :=
  cssRolesIn cfg.tables (rolesRead (baseRules doc ++ themeCss doc) ++ readerRoles)


/-- The base stylesheet; its unsourced paddings, margins, radii and breakpoints are the engine's
own screen furniture, each overridable. -/
public def baseCss (cfg : Config) (doc : Doc) (pairs : List (Nat × Nat) := [])
    (roles : Option (List Ir.Role) := none) (taken : List String := [])
    (rules : Option String := none) (epochVars : String := "") : String :=
  let parskip := parskipVar doc.page
  let roles := roles.getD (pageRoles cfg doc)
  -- role defaults come from the registry, never literals here
  let floorPal := cfg.floorPal
  ":root {\n" ++
  s!"    color-scheme: {if cfg.floor.onDark then "dark" else "light"};\n" ++
  s!"    --measure: {measureEm doc.page};\n" ++
  parskip ++
  lineageSkipVars doc ++
  String.join ((roleDefaultVars floorPal cfg.floor roles cfg.codeRoot).map (· ++ "\n")) ++
  "    --font-body: Georgia, \"Times New Roman\", serif;\n" ++
  "    --font-sans: system-ui, -apple-system, \"Segoe UI\", sans-serif;\n" ++
  "    --font-mono: ui-monospace, SFMono-Regular, Menlo, monospace;\n" ++
  "}\n" ++
  -- at equal `:root` specificity, source order alone decides between these blocks
  (let tv := tokenVars cfg doc roles taken
   if tv.isEmpty then "" else ":root {\n" ++ tv ++ "\n}\n") ++
  schemeBlocks cfg.tables cfg.floor roles cfg.codeRoot ++ epochVars ++
  lineageLevelRules doc ++
  rules.getD (baseRules doc pairs (cfg.imgs.entries.any (!·.webWords.isEmpty)))

private def styleClass : Style → String
  | .bold => "b"
  | .italic => "i"
  | .mono => "mono"
  | .smallcaps => "sc"
  | .emph => "em"
  | .sans => "sans"
  | .normal => "normal"
  | .roman => "rm"
  | .medium => "md"
  -- unused: `.series` ships as a numeric `font-weight`
  | .series w => s!"w{w.css}"
  | .upright => "up"
  -- unused: `.family` ships as its stack's custom property
  | .family s => s!"family-{s}"
  | .size n => "size-" ++ n
  -- unused: `.fontSize` ships as one inline declaration
  | .fontSize _ _ => "fontsize"
  -- unused: `.lang` ships as a `lang` attribute
  | .lang tag => "lang-" ++ tag

/-- The shares of a slide's leftover vertical space above and below its content. -/
@[expose] public def vdistShares (keys : Ir.FrameKeys) (v : Ir.VAlign) (breakable : Bool := false) :
    Nat × Nat :=
  Ir.VAlign.shares keys v breakable

/-- The grows a frame's two spacers take: its declared shares, or none where its glue yields to a
`\vfill`. -/
@[expose] public def deckSpacerShares (keys : Ir.FrameKeys) (breakable : Bool) (valign : Ir.VAlign)
    (fills : Nat) : Nat × Nat :=
  if (Ir.frameGlue keys breakable valign).joins || fills == 0 then vdistShares keys valign breakable
  else (0, 0)

/-- The overlay attributes a step's wrapper carries. -/
public def stepAttrs (n : Nat) (last : Option Nat) : Array (String × String) :=
  (#[("class", "step"), ("data-step", toString n)] ++
    (match last with
     | some u => #[("data-step-last", toString u)]
     | none => #[])) ++
    #[("style", s!"--step: {n}")]

/-- The declared end's own carrier, nested inside the step's wrapper when the range has one. -/
public def stepEndNodes (tag : String) (last : Option Nat) (kids : Array Node) : Array Node :=
  match last with
  | none => kids
  | some u =>
    #[Html.elem tag kids
      #[("class", "step-end"), ("data-step-last", toString u),
        ("style", s!"--step-last: {u}")]]

/-- One alternation group in its own wrapper; the group step 1 does not ink carries `hidden`. -/
public def altGroupNode (tag : String) (n : Nat) (last : Option Nat) (first : Bool)
    (kids : Array Node) : Node :=
  let pendingSide := Ir.altFirstWhenPending n last == first
  Html.elem tag kids
    ((#[("class", if pendingSide then "alt alt-pending" else "alt alt-crisp"),
        ("data-step", toString n)] ++
      (match last with
       | some u => #[("data-step-last", toString u)]
       | none => #[])) ++
      (if first then #[] else #[("hidden", "hidden")]))

/-- The selector's finite projection, as whitespace-separated step tokens. -/
public def overlayStepTokens (spec : Ir.OverlaySpec) (steps : Nat) : String :=
  String.intercalate " " ((spec.selectedSteps steps).map toString)

/-- Whether a selector uses range animation: one positive range, ordered and within the frame's
steps, on a multi-reveal track. -/
public def overlayUsesRange (steps : Nat) (spec : Ir.OverlaySpec) : Bool :=
  (2 ≤ steps) && spec.more.isEmpty && (1 ≤ spec.first) &&
    match spec.last with
    | none => true
    | some u => spec.first ≤ u && u ≤ steps

public theorem overlayUsesRange_contract (steps : Nat) (spec : Ir.OverlaySpec)
    (h : overlayUsesRange steps spec = true) :
    2 ≤ steps ∧ spec.more = [] ∧ 1 ≤ spec.first ∧
      ∀ u, spec.last = some u → spec.first ≤ u ∧ u ≤ steps := by
  cases spec with
  | mk n last more =>
    cases more <;> cases last <;> simp_all [overlayUsesRange]

/-- One body carrier for an exact selector. -/
public def overlayNode (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (kids : Array Node) : Node :=
  if overlayUsesRange steps spec then
    Html.elem tag (stepEndNodes tag spec.last kids)
      ((stepAttrs spec.first spec.last).push ("data-steps", overlayStepTokens spec steps))
  else
    Html.elem tag kids #[("class", "step-set"),
      ("data-steps", overlayStepTokens spec steps)]

/-- Both alternatives, declared once each in page order. -/
public def overlayAltNode (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first : Bool) (kids : Array Node) : Node :=
  if overlayUsesRange steps spec then altGroupNode tag spec.first spec.last first kids
  else
    Html.elem tag kids (#[("class", "alt alt-set"),
      ("data-steps", String.intercalate " " ((spec.pageSteps steps first).map toString))] ++
      if first then #[] else #[("hidden", "hidden")])

/-- Does a group show nothing: no element, and no text but white space? -/
public def nodesBlank (xs : Array Node) : Bool :=
  xs.all fun n => match n with
    | .text t => !holdsText t
    | .elem .. | .style _ | .script .. => false

/-- One group of an alternation in its finite membership set, `hidden` where
asked: the representation every snap selects by its own number. -/
public def overlayAltSetNode (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first hidden : Bool) (kids : Array Node) : Node :=
  Html.elem tag kids (#[("class", "alt alt-set"),
    ("data-steps", String.intercalate " " ((spec.pageSteps steps first).map toString))] ++
    if hidden then #[("hidden", "hidden")] else #[])

/-- An alternation's two groups, in page order. Where one shows nothing —
`\only`'s, absent off its steps — both stand in their membership sets and
the blank one carries `hidden`, so a rendering with no snap state shows the
other: the floor with scripting off, the print sheet and the reduced page
hide nothing the document says, while every snap still shows the group its
step selects (`overlay_set_alternation_agree`). Otherwise the group stored
first is the floor's (`overlayAltNode`). -/
public def altPairNodes (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first other : Array Node) : Array Node :=
  if nodesBlank first != nodesBlank other then
    #[overlayAltSetNode tag steps spec true (nodesBlank first) first,
      overlayAltSetNode tag steps spec false (nodesBlank other) other]
  else #[overlayAltNode tag steps spec true first, overlayAltNode tag steps spec false other]

/-- **No floor shows a blank alternative over one with content**
(`_contract`): where exactly one group is blank, the pair is its two
membership-set nodes, the blank one alone `hidden`. -/
public theorem altPairNodes_floor_contract (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first other : Array Node) (h : nodesBlank first != nodesBlank other) :
    altPairNodes tag steps spec first other =
      #[overlayAltSetNode tag steps spec true (nodesBlank first) first,
        overlayAltSetNode tag steps spec false (!nodesBlank first) other] := by
  unfold altPairNodes
  cases hf : nodesBlank first <;> cases ho : nodesBlank other <;> simp_all

mutual

private def anchorIdsOne (acc : Array String) : Node → Array String
  | .elem _ attrs kids =>
    -- a figure's own definitions are no anchors
    let ids := attrs.filterMap fun (key, value) =>
      if key == "id" && (GfxSvg.parseId value).isNone then some value else none
    anchorIdsList (acc ++ ids) kids.toList
  | .text _ | .style _ | .script _ _ => acc

private def anchorIdsList (acc : Array String) : List Node → Array String
  | [] => acc
  | x :: xs => anchorIdsList (anchorIdsOne acc x) xs

end

mutual

/-- Strip the `id`s listed in `ids`, leaving every other node as it was. -/
private def unanchorOne (ids : Array String) : Node → Node
  | .elem tag attrs kids => .elem tag
      (attrs.filter fun (key, value) => !(key == "id" && ids.contains value))
      (unanchorList ids #[] kids.toList)
  | .text s => .text s
  | .style css => .style css
  | .script attrs js => .script attrs js

private def unanchorList (ids : Array String) (acc : Array Node) : List Node → Array Node
  | [] => acc
  | x :: xs => unanchorList ids (acc.push (unanchorOne ids x)) xs

end

/-- Exclusive alternatives, their shared anchors moved to one target outside both carriers. -/
public def overlayAlternatives (tag : String) (steps : Nat) (spec : Ir.OverlaySpec)
    (first other : Array Node) : Array Node :=
  let otherIds := anchorIdsList #[] other.toList
  let shared := ((anchorIdsList #[] first.toList).filter otherIds.contains).toList.eraseDups.toArray
  let anchors := shared.map fun id =>
    Html.elem "span" #[] #[("id", id), ("data-alt-anchor", "")]
  anchors ++ altPairNodes tag steps spec (unanchorList shared #[] first.toList)
    (unanchorList shared #[] other.toList)

/-- Artifact-specific. -/
public theorem overlay_membership_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    (spec.selectedSteps steps).contains k = spec.selects k := by
  apply Bool.eq_iff_iff.mpr
  simp [Ir.OverlaySpec.selectedSteps_mem, hk, hsteps]

/-- Covering as read from the representation `overlayNode` emits. -/
public def overlayPendingAt (steps : Nat) (spec : Ir.OverlaySpec) (k : Nat) : Bool :=
  if overlayUsesRange steps spec then htmlStepPendingAt steps spec.first spec.last k
  else !(spec.selectedSteps steps).contains k

public theorem overlay_pending_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    overlayPendingAt steps spec k = spec.pending k := by
  by_cases h : overlayUsesRange steps spec = true
  · obtain ⟨_, hmore, hn, hlast⟩ := overlayUsesRange_contract steps spec h
    have he : ∀ u, spec.last = some u → 1 ≤ u ∧ u ≤ steps := by
      intro u hu
      have hh := hlast u hu
      exact ⟨by omega, hh.2⟩
    simpa [overlayPendingAt, h, Ir.OverlaySpec.pending, Ir.OverlaySpec.selects,
      Ir.OverlaySpec.ranges, hmore] using
      html_step_pending_agree steps spec.first k spec.last hn hk he
  · unfold overlayPendingAt
    rw [ite_eq_right h, overlay_membership_agree spec steps k hk hsteps]
    rfl

/-- Page-order alternation as read from the representation `overlayAltNode` emits. -/
public def overlayFirstAt (steps : Nat) (spec : Ir.OverlaySpec) (k : Nat) : Bool :=
  if overlayUsesRange steps spec then altShownFirstAt steps spec.first spec.last k
  else (spec.pageSteps steps true).contains k

/-- The membership-set representation selects at every snap of the frame
the group the PDF page inks: the snap shows the first group exactly where
the IR's step does. -/
public theorem overlay_set_alternation_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    (spec.pageSteps steps true).contains k = spec.showsFirst k := by
  apply Bool.eq_iff_iff.mpr
  simp [Ir.OverlaySpec.pageSteps_mem, hk, hsteps]

public theorem overlay_alternation_agree (spec : Ir.OverlaySpec) (steps k : Nat)
    (hk : 1 ≤ k) (hsteps : k ≤ steps) :
    overlayFirstAt steps spec k = spec.showsFirst k := by
  by_cases h : overlayUsesRange steps spec = true
  · obtain ⟨_, hmore, hn, hlast⟩ := overlayUsesRange_contract steps spec h
    have he : ∀ u, spec.last = some u → 1 ≤ u ∧ u ≤ steps := by
      intro u hu
      have hh := hlast u hu
      exact ⟨by omega, hh.2⟩
    simpa [overlayFirstAt, h, Ir.altShowsFirst, Ir.OverlaySpec.showsFirst,
      Ir.OverlaySpec.pending, Ir.OverlaySpec.selects, Ir.OverlaySpec.ranges, hmore] using
      alt_backend_agree steps spec.first k spec.last hn hk he
  · apply Bool.eq_iff_iff.mpr
    simp [overlayFirstAt, h, Ir.OverlaySpec.pageSteps_mem, hk, hsteps]

/-- Whether a string carries a character that shows something. -/
@[expose] public def nonBlank (s : String) : Bool := holdsText s

/-- The first of two strings that carries anything to read. -/
public def firstNonBlank (a b : String) : String := if nonBlank a then a else b

public theorem firstNonBlank_contract (a b : String) (hb : nonBlank b = true) :
    nonBlank (firstNonBlank a b) = true := by
  unfold firstNonBlank
  split
  · assumption
  · exact hb

/-- The locale's figure word, else English. -/
public def figureWord (loc : Locale) : String := firstNonBlank loc.figure "figure"

public theorem figureWord_contract (loc : Locale) : nonBlank (figureWord loc) = true :=
  firstNonBlank_contract _ _ (by decide)

public def attrOf? (attrs : Array (String × String)) (k : String) : Option String :=
  (attrs.find? (·.1 == k)).map (·.2)

/-- An `<img>`'s alternative attributes, from its one `Alt`. -/
public def imgAltAttrs : Ir.Alt → Array (String × String)
  | .described t => #[("alt", t)]
  | .decorative => #[("alt", ""), ("role", "presentation")]
  | .undeclared => #[("alt", "")]

/-- A picture's role and name, from its one `Alt`. -/
public def pictureAltAttrs (floor : String) : Ir.Alt → Array (String × String)
  | .described t => #[("role", "img"), ("aria-label", firstNonBlank t floor)]
  | .decorative => #[("aria-hidden", "true")]
  | .undeclared => #[("role", "img"), ("aria-label", floor)]

/-- A listing's line height over its own font size: the pitch its source lines stand at on the
page. -/
private def listingLineHeight (page : PageSpec) (spec : Ir.ListingSpec) (step : String) :
    String :=
  let k := (page.scale.lookup step).getD 1000
  let size := page.fontSize * (k : Int) / 1000
  let pitch := Ir.stepSkip (Ir.stepLead page.skipScale step page.fontSize) page.fontSize
    page.leading - spec.lineOverlap
  decMilli (pitch * 1000 / max size 1)

/-- A length of the page's own: on a deck the stage's share, elsewhere screen rem. -/
private def stageLength (cfg : Config) (v : Int) : String :=
  if cfg.deck then s!"{decMilli (deckStageMilli v cfg.page.height)}vh"
  else milliRem (screenMilli cfg.page.fontSize v)

/-- A block that sets no line box in its section's flow. -/
private def shipsNoLine : Block → Bool
  | .note .. | .nav .. | .logo .. | .pagebreak | .framefoot .. | .setPalette .. | .setTokens .. => true
  | .para .. | .section .. | .list .. | .center .. | .ragged .. | .spaced .. | .role .. | .link ..
  | .quote .. | .abstract .. | .titled .. | .disclosure .. | .equation .. | .verbatim ..
  | .algorithm .. | .columns .. | .onSteps .. | .altSteps .. | .only .. | .frame .. | .rule ..
  | .picture .. | .table .. | .float .. | .bibliography .. => false

mutual

-- conserves: none — follows the last block alone, which no fold over every block can say
/-- How far a body's end stands below its last baseline, with the skips of the shaped blocks it
ends inside. -/
private def endBelowList (cfg : Config) (para : String) : List Block → String
  | [] => para
  | [b] => endBelowOne cfg para b
  | b :: rest => if rest.all shipsNoLine then endBelowOne cfg para b else endBelowList cfg para rest

private def endBelowItems (cfg : Config) (para : String) : List (Array Block) → String
  | [] => para
  | [item] => endBelowList cfg para item.toList
  | _ :: rest => endBelowItems cfg para rest

private def endBelowOne (cfg : Config) (para : String) : Block → String
  | .titled kind _ body =>
    let inner := endBelowList cfg para body.toList
    match Ir.blockShapeOf cfg.styles kind with
    | some sh =>
      s!"calc({shapeLengthCss cfg.deck cfg.page (Ir.blockSkipSum cfg.tokens sh.after)} + {inner})"
    | none => inner
  | .disclosure _ expanded body => if expanded then endBelowList cfg para body.toList else para
  | .list _ items => endBelowItems cfg para items.toList
  | .center body | .ragged _ body | .spaced _ body | .role _ body | .link _ body
  | .quote body | .abstract body | .onSteps _ body | .only _ body =>
    endBelowList cfg para body.toList
  | .verbatim covered content spec =>
    match cfg.blockLastBelow (some (.verbatim covered content spec)) with
    | some v =>
      if cfg.deck then stageLength cfg v else s!"calc({stageLength cfg v} + {quantaRem 1})"
    | none => para
  | .para .. | .section .. | .equation .. | .algorithm .. | .rule .. | .picture ..
  | .table .. | .bibliography .. | .columns .. | .altSteps .. | .note .. | .nav ..
  | .logo .. | .pagebreak | .frame .. | .framefoot .. | .setPalette .. | .setTokens ..
  | .float .. => para

end
/-- An image's element: an inline drawn figure as its own SVG, else the `<img>`. -/
public def imageElement (cfg : Config) (index? : Option Nat) (req : Image.Request) (alt : Ir.Alt)
    (dims : Array (String × String)) (img : Node) : Node :=
  match index?.bind (FigureSvg.inlineFigure? cfg.imgs) with
  -- the `picture` class keeps a figure on the page's own plate in every scheme
  | some fig => FigureSvg.inlineSvg fig
      (pictureAltAttrs (figureWord cfg.locale) alt ++ #[("class", "picture")] ++ dims)
  | none =>
    match imagePosterHref cfg.imgs req with
    | some poster => Html.elem "picture" #[
        Html.elem "source" #[] #[("media", "print, (prefers-reduced-motion: reduce)"),
          ("srcset", poster)], img]
    | none => img

/-- A font length in CSS: on a deck an absolute length as its stage share, else its CSS form. -/
private def fontLengthCss (cfg : Config) (e : Affine Measure) : String :=
  if cfg.deck && e.rigidAbsolute && !(e.anyRef fun _ => true) then
    let length := (e.eval fun _ => {}).width.sp
    s!"{decMilli (deckStageMilli length cfg.page.height)}vh"
  else Ir.Track.contextCss e

mutual

/-- Inline content, pushed onto `acc`. -/
private def inlineNodeInto (cfg : Config) (acc : Array Node) (x : Inline) : Array Node :=
  match x with
  | .text s => acc.push (Html.text s)
  | .image src size alt =>
    -- the intrinsic size rides as width/height; on a deck a stage length is a stage share
    let index? := cfg.imgs.findRequest? (size.request src)
    let loaded? := index?.bind cfg.imgs.get?
    let info? := loaded?.bind (·.info)
    let canvas? := loaded?.bind (·.canvasSize)
    let pixels? : Option (Nat × Nat) := info?.map fun inf =>
      match canvas? with
      | some (w, h) => (cssPxOfSp w, cssPxOfSp h)
      | none => intrinsicPx inf
    -- a boundary picture with no face draws nothing, so its alternative is never decorative
    let alt := if src.startsWith Ir.picSrcPrefix && info?.isNone then
        (match alt with
          | .undeclared => .described (figureWord cfg.locale)
          | .decorative => .decorative
          | .described t => .described t) else alt
    -- an unresolved request keeps its source spelling, so publication can name the loss
    let href := imageRequestHref cfg.imgs (size.request src)
    let horizontal (l : Image.Len) : Bool :=
      l.value.anyRef fun m => m != .textHeight
    let vertical (l : Image.Len) : Bool :=
      l.value.anyRef (· == .textHeight)
    let cssDim (l : Image.Len) (isVertical : Bool) : Option String :=
      if vertical l then none
      else if isVertical then some (Ir.Track.contextCss l.value)
      else some (Ir.Track.css (.affine l.value))
    let deckDim (l : Image.Len) (isVertical : Bool) : Option String :=
      if horizontal l && !vertical l then
        some (if isVertical then Ir.Track.contextCss l.value
          else Ir.Track.css (.affine l.value))
      else if !horizontal l then
        let (stage, unit) :=
          if isVertical then (cfg.page.height, "dvh") else (cfg.page.width, "vw")
        let textW := cfg.page.width - 2 * cfg.page.hmargin
        let textH := cfg.page.height - 2 * cfg.page.vmargin
        some (decMilli (deckStageMilli (l.resolve textW textH) stage) ++ unit)
      else none
    let dim (l : Image.Len) (vertical : Bool) : Option String :=
      if cfg.deck then deckDim l vertical else cssDim l vertical
    let wCss := size.width.bind (dim · false)
    let hCss := size.height.bind (dim · true)
    -- in a fill row a text-width fraction is the row's, in `cqi`
    let wRow := size.width.bind fun l =>
      if cfg.inFillRow && horizontal l && !vertical l then
        some (Ir.Track.contextCss l.value)
      else none
    let width (w : String) : String := match wRow with
      | some r => s!"width: {w}; width: {r}"
      | none => s!"width: {w}"
    let style : Option String :=
      match wCss, hCss with
      | some w, some h =>
        -- `keepaspectratio` scales by the smaller ratio, as graphicx does
        match size.keepAspect, pixels? with
        | true, some (pw, ph) =>
          let (rw, rh) := canvas?.getD (Int.ofNat pw, Int.ofNat ph)
          let floor := if wRow.isSome then s!"width: {w}; " else ""
          some (s!"{floor}width: min({wRow.getD w}, calc({h} * {rw} / {rh})); " ++
            "height: auto")
        | true, none => some s!"{width w}; height: {h}; object-fit: contain"
        | false, _ => some s!"{width w}; height: {h}"
      | some w, none => some s!"{width w}; height: auto"
      | none, some h => some s!"height: {h}; width: auto"
      | none, none =>
        if size.width.isNone && size.height.isNone &&
            (size.scaleNum != 1 || size.scaleDen != 1) then
          (loaded?.bind (·.size?)).map fun (iw, _) =>
            let scaled := iw * size.scaleNum / size.scaleDen
            if cfg.deck then
              s!"width: {decMilli (deckStageMilli scaled cfg.page.width)}vw; height: auto"
            else
              s!"width: {Dim.Sp.toPtString scaled}pt; height: auto"
        else none
    -- animate §6.1 fixes the canvas to frame one
    let style := match canvas? with
      | some (w, h) =>
        let ar := s!"aspect-ratio: {w} / {h}; object-fit: fill"
        some (match style with | some s => s ++ "; " ++ ar | none => ar)
      | none => style
    let requestAttrs := match index? with
      | some k => if loaded?.any pdfPageImg then #[("data-image-index", toString k)] else #[]
      | none => #[]
    if loaded?.any (·.webError.isSome) then
      let attrs := pictureAltAttrs (figureWord cfg.locale) alt
      let label := (attrOf? attrs "aria-label").getD ""
      -- a failed conversion still reserves the intrinsic pixel box
      let dims := match pixels? with
        | some (pw, ph) => [s!"width: {pw}px", s!"height: {ph}px"]
        | none => []
      let styleText := String.intercalate "; "
        (["display: inline-block"] ++ dims ++ (style.map (fun s => [s])).getD [])
      acc.push (Html.elem "span" #[Html.text label]
        (attrs ++ requestAttrs ++ #[("data-image-src", href),
          ("style", styleText)]))
    else
    let dims := (match pixels? with
       | some (pw, ph) =>
         #[("width", toString pw), ("height", toString ph)]
       | none => #[]) ++
      (match style with
       | some st => #[("style", st)]
       | none => #[])
    let seeThrough := if loaded?.any imageSeeThrough then #[("class", "see-through")] else #[]
    let img := Html.elem "img" #[] (#[("src", href)] ++ requestAttrs ++ imgAltAttrs alt ++ seeThrough ++ dims)
    let acc := acc.push (imageElement cfg index? (size.request src) alt dims img)
    match loaded? with
    | some en => if en.webWords.isEmpty then acc else acc.push (figureWordsNode en.webWords)
    | none => acc
  | .math display src =>
    -- unmodelled math ships its floor text, the source in a data attribute
    let tag := if display then "div" else "span"
    acc.push (Html.elem tag #[Html.text (Ir.mathFloor src)]
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)])
  | .formula display src body =>
    -- native MathML Core from the parsed atoms; the TeX source rides in `data-tex`
    acc.push (MathMl.formula display
      #[("class", if display then "math math-display" else "math"),
        ("data-tex", src)] body (mathMarks cfg))
  | .styled st body =>
    let kids := inlineNodesInto { cfg with mathStyles := cfg.mathStyles.push st } #[] body.toList
    match st with
    | .bold => acc.push (Html.elem "strong" kids)
    | .italic => acc.push (Html.elem "em" kids)
    | .emph => acc.push (Html.elem "em" kids)
    | .mono => acc.push (Html.elem "code" kids)
    | .normal => acc ++ kids
    -- a series is the run's numeric weight, matched against the shipped faces
    | .series w =>
      acc.push (Html.elem "span" kids #[("style", s!"font-weight: {w.css}")])
    | .fontSize size leading =>
      acc.push (Html.elem "span" kids #[
        ("style", s!"font-size:{fontLengthCss cfg size};line-height:{fontLengthCss cfg leading}")])
    -- a run's language is a `lang` attribute, which hyphenation and assistive technology read
    | .lang tag => acc.push (Html.elem "span" kids #[("lang", tag)])
    | .family s => acc.push (Html.elem "span" kids #[("style", s!"font-family: var(--font-{s})")])
    | other => acc.push (Html.elem "span" kids #[("class", styleClass other)])
  | .role n body =>
    -- a title-part role also states its size and baseline skip; other roles carry only their class
    let part := Ir.titlePartOf ((cfg.styles.find? "titlepage").getD {}).slots n
    let style := part.bind fun p =>
      let decls :=
        (p.size.map fun z => s!"font-size:{fontLengthCss cfg (.lit z)};").toList ++
        (p.leading.map fun z => s!"line-height:{fontLengthCss cfg (.lit z)};").toList
      if decls.isEmpty then none else some (String.join decls)
    let attrs := #[some ("class", roleClass n), style.map ("style", ·)].filterMap id
    let inner := match part with
      | some p =>
        match p.size with
        | some size =>
          let st := Ir.Style.fontSize (.lit size) (.lit (p.leading.getD size))
          { cfg with mathStyles := cfg.mathStyles.push st }
        | none => cfg
      | none => cfg
    acc.push (Html.elem "span" (inlineNodesInto inner #[] body.toList) attrs)
  | .colored c name body =>
    acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
      #[("style", "color: " ++ cfg.paint name c)])
  | .located _ body => inlineNodesInto cfg acc body.toList
  | .link url body =>
    acc.push (Html.elem "a" (inlineNodesInto cfg #[] body.toList)
      #[("href", url), ("style", "color: inherit")])
  | .label key =>
    acc.push (Html.elem "span" #[] #[("id", Ir.labelAnchor key)])
  -- an unresolved reference shows LaTeX's `??`, already diagnosed
  | .ref _ _ text target =>
    match target with
    | some a =>
      acc.push (Html.elem "a" #[Html.text text]
        #[("href", "#" ++ a), ("style", "color: inherit")])
    | none => acc.push (Html.text text)
  | .decorated kind body =>
    let tag := match kind with
      | .underline => "u"
      | .lineThrough => "s"
    acc.push (Html.elem tag (inlineNodesInto cfg #[] body.toList))
  | .onSteps spec body =>
    acc.push (overlayNode "span" cfg.overlaySteps spec (inlineNodesInto cfg #[] body.toList))
  | .altSteps spec firstPage otherPage =>
    acc ++ overlayAlternatives "span" cfg.overlaySteps spec
      (inlineNodesInto cfg #[] firstPage.toList) (inlineNodesInto cfg #[] otherPage.toList)
  | .icon c label =>
    -- the PUA glyph is hidden from assistive technology; the `img` wrapper carries its name
    acc.push (Html.elem "span"
      #[Html.elem "span" #[Html.text (String.ofList [c])] #[("aria-hidden", "true")]]
      #[("class", "icon"), ("role", "img"), ("aria-label", label)])
  | .fill => acc.push (Html.elem "span" #[] #[("class", "fill")])
  -- infinite stretch keeps the fill carrier; a finite part stays an inline offset
  | .hspace e _ =>
    let finite := e.withoutFil
    let room := Ir.Track.css (.affine finite)
    let node := Html.elem "span" #[] #[("style", s!"margin-inline-start:{room}")]
    if e.hasFil then
      (acc.push node).push (Html.elem "span" #[] #[("class", "fill")])
    else acc.push node
  | .rule width height raise =>
    let w := Ir.Track.css (.affine width)
    let h := Ir.Track.contextCss height
    let r := Ir.Track.contextCss raise
    acc.push (Html.elem "span" #[] #[
      ("style", s!"display:inline-block;inline-size:{w};block-size:{h};vertical-align:{r};background:currentColor")])
  -- a strut adds no box: the page reads at its own line height
  | .strut _ => acc
  -- an italic correction is TeX's kern; a browser sets its own italics
  | .italicCorr _ => acc
  -- an unresolved citation shows its marks, already diagnosed
  | .cite _ keys => acc.push (Html.text (Ir.citeMarks keys))
  -- the mark links to the note's endnote entry (DPUB-ARIA `doc-noteref`)
  | .footnote num _ =>
    let n := num.getD 0
    acc.push (Html.elem "sup"
      #[Html.elem "a" #[Html.text (toString n)]
        #[("href", s!"#fn{n}"), ("id", s!"fnref{n}"),
          ("role", "doc-noteref"), ("style", "color: inherit")]])
  -- page furniture has no meaning in a continuous document
  | .pageNumber => acc
  | .pageCount => acc
  | .linebreak extra =>
    -- extra space after a break is a sized block, not a second `<br>`
    if extra == ({} : SymGlue) then acc.push (Html.elem "br" #[])
    else (acc.push (Html.elem "br" #[])).push
      (Html.elem "span" #[]
        #[("style", s!"display:block;height:{cssLength extra.width}")])

private def inlineNodesInto (cfg : Config) (acc : Array Node) : List Inline → Array Node
  | [] => acc
  | x :: rest => inlineNodesInto cfg (inlineNodeInto cfg acc x) rest

end

private def inlines (cfg : Config) (xs : Array Inline) : Array Node :=
  inlineNodesInto cfg #[] xs.toList

public def tableCellTag (headerRows i : Nat) : String :=
  if i < headerRows then "th" else "td"

public theorem tableCellTag_th_iff (headerRows i : Nat) :
    tableCellTag headerRows i = "th" ↔ i < headerRows := by
  unfold tableCellTag
  split
  · simp_all
  · simp_all

private def readsInlineMeasure (e : Affine Measure) : Bool :=
  e.anyRef (· != .textHeight)

/-- Whether an emitted inline property reads `cqi`. -/
private def contextUnitLeaf (found : Bool) : Inline → Bool
  | .styled st _ => found || match st with
    | .fontSize size leading => readsInlineMeasure size || readsInlineMeasure leading
    | .bold | .italic | .mono | .smallcaps | .emph | .sans | .normal | .roman
    | .medium | .series _ | .upright | .family _ | .size _ | .lang _ => false
  | .rule _ height raise =>
    found || readsInlineMeasure height || readsInlineMeasure raise
  | .image _ size _ => found || size.height.any fun l =>
    readsInlineMeasure l.value && !l.value.anyRef (· == .textHeight)
  | .text _ | .math _ _ | .formula _ _ _ | .colored _ _ _ | .located _ _ | .role _ _
  | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .fill
  | .hspace _ _ | .strut _ | .italicCorr _ | .pageNumber | .pageCount
  | .icon _ _ | .label _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _
  | .linebreak _ => found

private def usesContextUnit (xs : Array Inline) : Bool :=
  Ir.foldInlines contextUnitLeaf false xs

/-- A cell's side class, from its spec's side, on every cell. -/
@[expose] public def cellSideClassOf (cols : Array Ir.ColSpec) (spans : Array Ir.ColSpan)
    (i j : Nat) : String :=
  cellSideClass (Ir.cellSpec cols spans i j).align

/-- A cell's classes, its side first, then `bt-cmid` and `bt-nowrap` where they apply. -/
@[expose] public def cellClasses (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (spans : Array Ir.ColSpan) (i j : Nat) : List String :=
  let spec := Ir.cellSpec cols spans i j
  cellSideClassOf cols spans i j ::
    ((if cmids.any (fun (a, b) => a ≤ j + 1 && j + 1 ≤ b) then ["bt-cmid"] else []) ++
      (if (spec.width matches .natural) && !spec.narrows then ["bt-nowrap"] else []))

/-- The classes of a block set wholly in step `n`: its size, and on a deck its leading. -/
public def stepClasses (deck : Bool) (n : String) : List String :=
  ("size-" ++ n) :: (if deck then ["lead-" ++ n] else [])

/-- The step classes of a cell set under one named size declared over it. -/
public def cellStepClasses (deck : Bool) (cell : Array Inline) : List String :=
  match Ir.paraStep? cell with
  | some "normalsize" | none => []
  | some n => stepClasses deck n

/-- One table cell: its classes, `scope=col` on a header cell, and `colspan` for a spanning head. -/
public def tableCellNode (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (spans : Array Ir.ColSpan) (headerRows i j : Nat) (cell : Array Inline) : Node :=
  let spec := Ir.cellSpec cols spans i j
  let span : Array (String × String) := match Ir.cellSpan? spans i j with
    | some s => if 2 ≤ s.n then #[("colspan", toString s.n)] else #[]
    | none => #[]
  let scope : Array (String × String) := if i < headerRows then #[("scope", "col")] else #[]
  let attrs := #[("class", " ".intercalate (cellClasses cols cmids spans i j ++
    cellStepClasses cfg.deck cell))] ++ (span ++ scope)
  let child := match spec.width with
    | .sized e => cfg.atMeasure
      (e.resolveWidth (MeasureValues.horizontal cfg.measureValues.lineWidth 0))
    | .natural | .flex _ => cfg
  -- the cell's class states its step, so the scope is lifted out of the content
  let cell := if (Ir.paraStep? cell).isSome then Ir.liftParaStep cell else cell
  let content := inlines child cell
  -- Chromium resolves no query units against a table cell, so a block inside it is the container
  let content := if usesContextUnit cell then
      #[Html.elem "div" content
        #[("class", "cell-measure"), ("style", "container-type: inline-size")]]
    else content
  Html.elem (tableCellTag headerRows i) content attrs

/-- Whether cell `(i, j)` is covered by a `\multicolumn` head to its left. -/
private def coveredBySpan (spans : Array Ir.ColSpan) (i j : Nat) : Bool :=
  spans.any fun s => s.row == i && s.col < j && j < s.col + s.n

/-- The cells of row `i`, in column order, the span-covered ones left out. -/
public def tableRowCells (cfg : Config) (cols : Array Ir.ColSpec) (cmids : Array (Nat × Nat))
    (spans : Array Ir.ColSpan) (headerRows i : Nat) (row : Array (Array Inline)) :
    Array Node :=
  (Array.range row.size).filterMap fun j =>
    if coveredBySpan spans i j then none
    else some (tableCellNode cfg cols cmids spans headerRows i j (row[j]?.getD #[]))

public theorem th_iff_header_row (cfg : Config) (cols : Array Ir.ColSpec)
    (cmids : Array (Nat × Nat)) (spans : Array Ir.ColSpan) (headerRows i : Nat)
    (row : Array (Array Inline)) (nd : Node)
    (h : nd ∈ tableRowCells cfg cols cmids spans headerRows i row) :
    nd.tag? = some "th" ↔ i < headerRows := by
  simp only [tableRowCells, Array.mem_filterMap] at h
  obtain ⟨j, _, hj⟩ := h
  split at hj
  · exact absurd hj (by simp)
  · simp only [Option.some.injEq] at hj
    subst hj
    simp only [tableCellNode, Html.elem, Html.Node.tag?, Option.some.injEq]
    exact tableCellTag_th_iff headerRows i

public theorem tableCellNode_align_projects (cfg : Config) (cols : Array Ir.ColSpec)
    (cmids : Array (Nat × Nat)) (spans : Array Ir.ColSpan) (headerRows i j : Nat)
    (cell : Array Inline) :
    ∃ attrs kids, tableCellNode cfg cols cmids spans headerRows i j cell =
      .elem (tableCellTag headerRows i) attrs kids ∧
      attrs[0]? = some ("class", " ".intercalate (cellClasses cols cmids spans i j ++
        cellStepClasses cfg.deck cell)) ∧
      (cellClasses cols cmids spans i j).head? = some (cellSideClassOf cols spans i j) :=
  ⟨_, _, rfl, by rw [Array.getElem?_append_left (by simp)]; rfl, rfl⟩

/-- One column node: a relative track hint, else the declared width, else natural sizing. -/
public def colElOf (shares : Array (Option Nat)) (j : Nat) (c : Ir.ColSpec) : Node :=
  match shares[j]? with
  | some (some p) => Html.elem "col" #[] #[("style", s!"width: {Ir.percentCss p}")]
  | _ => match c.width with
    | .sized e => Html.elem "col" #[] #[("style", s!"width: {Ir.Track.css (.affine e)}")]
    | .flex _ | .natural => Html.elem "col" #[] #[]

/-- One column node per typed column, in order. -/
public def tableColEls (cols : Array Ir.ColSpec) (target : Option Ir.TableTarget) : Array Node :=
  let shares : Array (Option Nat) := match target with
    | some t => Ir.tableColShares cols t
    | none => cols.map fun _ => none
  cols.mapIdx (colElOf shares)

public theorem tableColEls_share_projects (shares : Array (Option Nat)) (j : Nat)
    (c : Ir.ColSpec) (p : Nat) (h : shares[j]? = some (some p)) :
    colElOf shares j c = Html.elem "col" #[] #[("style", s!"width: {Ir.percentCss p}")] := by
  simp [colElOf, h]

public theorem tableColEls_natural_projects (shares : Array (Option Nat)) (j : Nat)
    (c : Ir.ColSpec) (hc : c.width = .natural) (h : shares[j]? = some none) :
    colElOf shares j c = Html.elem "col" #[] #[] := by
  simp [colElOf, h, hc]

/-- booktabs' formal table: rules as border classes on the rows they precede, head rows under
`<thead>`. -/
private def tableNode (cfg : Config) (cols : Array Ir.ColSpec) (padL padR : Bool)
    (rows : Array (Array (Array Inline))) (rules : Array (Nat × Ir.TableRule))
    (spans : Array Ir.ColSpan) : Node :=
  let headerRows := Ir.tableHeaderRows rows rules
  let ruleAt (i : Nat) : Array Ir.TableRule :=
    rules.foldl (fun out (k, r) => if k == i then out.push r else out) #[]
  let drawn (r : Ir.TableRule) : Bool := match r with
    | .gap _ => false
    | .top | .mid | .bottom | .cmid .. => true
  let target := cols.findSome? fun c => match c.width with
    | .flex t => some t
    | .natural | .sized _ => none
  let colEls := tableColEls cols target
  let rowEls := rows.mapIdx fun i row =>
    let cls := Id.run do
      let mut cls : Array String := #[]
      for r in ruleAt i do
        match r with
        | .top | .bottom => cls := cls.push "bt-heavy-above"
        | .mid => cls := cls.push "bt-light-above"
        | .cmid .. | .gap _ => pure ()
      if i + 1 == rows.size then
        for r in ruleAt rows.size do
          match r with
          | .top | .bottom => cls := cls.push "bt-heavy-below"
          | .mid => cls := cls.push "bt-light-below"
          | .cmid .. | .gap _ => pure ()
      else if (ruleAt (i + 1)).any drawn then
        cls := cls.push "bt-pre"
      return String.intercalate " " cls.toList
    let cmids := (ruleAt i).foldl (fun out r => match r with
      | .cmid a b _ _ => out.push (a, b)
      | .top | .mid | .bottom | .gap _ => out) (#[] : Array (Nat × Nat))
    Html.elem "tr" (tableRowCells cfg cols cmids spans headerRows i row)
      (if cls.isEmpty then #[] else #[("class", cls)])
  -- a markdown table too wide sets at the page's step, and overhangs on paper if still too wide
  let (step, overhang) :=
    cfg.tableFit (cfg.measureValues.lineWidth - cfg.inset) cols padL padR rows spans
  let cls := "booktabs" ++ (if padL then "" else " nopadl")
    ++ (if padR then "" else " nopadr") ++ (if overhang then " bt-overhang" else "")
  let kids := Id.run do
    let mut kids := #[Html.elem "colgroup" colEls]
    if 0 < headerRows then
      kids := kids.push (Html.elem "thead" (rowEls.extract 0 headerRows))
    if headerRows < rows.size then
      kids := kids.push (Html.elem "tbody" (rowEls.extract headerRows rowEls.size))
    return kids
  let decls : List String :=
    (match target with
      | some t => ["width: " ++ t.css]
      | none => []) ++
    (match step with
      | some st => ((fontStyleDecls cfg.page.scale (.size st)).getD #[]).toList
      | none => [])
  let attrs := if decls.isEmpty then #[("class", cls)]
    else #[("class", cls), ("style", " ".intercalate decls)]
  Html.elem "table" kids attrs

private theorem role_use_names_its_token (cfg : Config) (acc : Array Node)
    (c : Ir.Color) (n : Ir.ColorRef) (body : Array Inline)
    (h : ∀ r, n = .role r → cfg.declares r = true) :
    inlineNodeInto cfg acc (.colored c (some n) body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("style", "color: " ++ s!"var({n.property}, {cssColor c})")]) := by
  rw [← colorRead_names cfg n c h]
  simp [inlineNodeInto, Config.paint]

private theorem role_use_undeclarable_value (cfg : Config) (acc : Array Node)
    (c : Ir.Color) (r : Ir.Role) (body : Array Inline) (h : cfg.declares r = false) :
    inlineNodeInto cfg acc (.colored c (some (.role r)) body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("style", "color: " ++ cfg.literal c)]) := by
  have hv : colorRead cfg (some (.role r)) c = cfg.literal c := by simp [colorRead, h]
  rw [← hv]
  simp [inlineNodeInto, Config.paint]

private theorem role_class_reaches_artifact (cfg : Config) (acc : Array Node)
    (n : String) (body : Array Inline)
    (h : Ir.titlePartOf ((cfg.styles.find? "titlepage").getD {}).slots n = none) :
    inlineNodeInto cfg acc (.role n body) =
      acc.push (Html.elem "span" (inlineNodesInto cfg #[] body.toList)
        #[("class", roleClass n)]) := by
  simp [inlineNodeInto, h]

private theorem link_url_enters_attribute_position (cfg : Config) (acc : Array Node)
    (url : String) (body : Array Inline) :
    inlineNodeInto cfg acc (.link url body) =
      acc.push (Html.elem "a" (inlineNodesInto cfg #[] body.toList)
        #[("href", url), ("style", "color: inherit")]) := by
  simp [inlineNodeInto]

private theorem linkLeafAfford_projects (cfg : Config) (acc : Array Node)
    (s : Ir.Styles) (kind : String) (x : Inline) (h : x.bearsLinkText = true) :
    inlineNodeInto cfg acc (s.linkLeafAfford kind x)
      = (match (s.find? kind).bind (·.color) with
         | some (c, n) =>
             acc.push (Html.elem "span"
               #[Html.elem "u" (inlineNodesInto cfg #[] [x])]
               #[("style", "color: " ++ cfg.paint n c)])
         | none => acc.push (Html.elem "u" (inlineNodesInto cfg #[] [x]))) := by
  rw [Ir.Styles.linkLeafAfford_afford s kind x h]
  cases hc : (s.find? kind).bind (·.color) with
  | none => simp [inlineNodeInto, inlineNodesInto]
  | some p => obtain ⟨c, n⟩ := p; simp [inlineNodeInto, inlineNodesInto]

/-- Whether a paragraph uses `\hfill`, which makes it a flex row. -/
private def hasFill (xs : Array Inline) : Bool :=
  xs.any fun x => match x with
    | .fill => true
    | .hspace e _ => e.hasFil
    | _ => false

/-- Split inline content at each `\\`, one flex row per break. -/
private def splitAtBreaks (xs : Array Inline) : Array (Array Inline) := Id.run do
  let mut out : Array (Array Inline) := #[]
  let mut cur : Array Inline := #[]
  for x in xs do
    match x with
    | .linebreak _ =>
      out := out.push cur
      cur := #[]
    | other => cur := cur.push other
  return out.push cur

/-- Split one row at each `\hfill`. -/
private def splitAtFills (xs : Array Inline) : Array (Array Inline) := Id.run do
  let mut out : Array (Array Inline) := #[]
  let mut cur : Array Inline := #[]
  for x in xs do
    match x with
    | .fill =>
      out := out.push cur
      cur := #[]
    | .hspace e keep =>
      if e.hasFil then
        let finite := e.withoutFil
        let zero := MeasureValues.horizontal 0 0
        unless !finite.anyRef (fun _ => true) && finite.eval zero.find == {} do
          cur := cur.push (.hspace finite keep)
        out := out.push cur
        cur := #[]
      else cur := cur.push x
    | other => cur := cur.push other
  return out.push cur

@[expose] public def headingTag (level : Ir.HeadingLevel) : String :=
  s!"h{Ir.headingRank level}"

private def fillRow (cfg : Config) (tag baseClass : String) (xs : Array Inline) : Node :=
  let groups := splitAtFills xs
  let rowClass := if groups.size == 2 then baseClass ++ " entry-pair" else baseClass
  -- a row holding an image sized by a text-width fraction is its container
  let sized := Ir.foldInlines (fun acc x => acc || match x with
    | .image _ size _ => size.width.any fun l =>
        l.value.anyRef (· != .textHeight) && !l.value.anyRef (· == .textHeight)
    | _ => false) false xs
  let cfg := { cfg with inFillRow := true }
  Html.elem tag (groups.map fun group =>
    Html.elem "span" (inlines cfg group) #[("class", "group")])
    (#[("class", rowClass)] ++
      (if sized then #[("style", "container-type: inline-size")] else #[]))

/-- Grid tracks from the declared widths: a percentage, a length, or an `fr` share of the
leftover. -/
private def gridTracks (cols : Array (BoxWidth × Array Block)) : String :=
  String.intercalate " " (cols.toList.map fun (w, _) => Ir.Track.css w.trackOf)

/-- Children start their own sibling walk; the parent's epoch style already inherits into them. -/
public def Config.into (cfg : Config) : Config :=
  { cfg with epochStyle := "", epochPaint := "", epochGround := false }

/-- The frame's numbered extent, for every part of its HTML frame. -/
public def Config.inFrame (cfg : Config) (frame : Block) : Config :=
  { cfg with overlaySteps := Ir.frameSteps frame }

public theorem Config.inFrame_membership_agree (cfg : Config) (frame : Block)
    (spec : Ir.OverlaySpec) (k : Nat) (hk : 1 ≤ k) (hsteps : k ≤ Ir.frameSteps frame) :
    (spec.selectedSteps (cfg.inFrame frame).overlaySteps).contains k = spec.selects k :=
  overlay_membership_agree spec (Ir.frameSteps frame) k hk hsteps

private def joinStyles (a b : String) : String :=
  if a.isEmpty then b else if b.isEmpty then a else a ++ "; " ++ b

/-- An epoch's accumulated declarations, with each property's last value kept. -/
private def compactStyle (style : String) : String :=
  let decls := (style.splitOn ";").filterMap fun d =>
    let d := d.trimAscii.toString
    if d.isEmpty then none else some (((d.splitOn ":").headD "").trimAscii.toString, d)
  let kept := decls.foldr (fun (k, d) acc => if acc.any (·.1 == k) then acc else (k, d) :: acc) []
  String.intercalate "; " (kept.map (·.2))

/-- A body palette epoch as semantic changes; `none` removes a property. -/
public structure PaletteDiff where
  entries : Array (Ir.ColorRef × Option Ir.Color)
  /-- The page's roles the epoch re-declares by default. -/
  defaults : Array (Ir.Role × Option Ir.CssDecl) := #[]

public def PaletteDiff.groundChanged (diff : PaletteDiff) : Bool :=
  diff.entries.any (·.1 == .role .page)

/-- The palette changes as custom-property declarations. -/
public def PaletteDiff.style (diff : PaletteDiff) : String :=
  let restated := diff.defaults.map (·.1)
  String.intercalate "; " ((diff.entries.toList.filterMap fun
    | (n, some c) => some s!"{n.property}: {cssColor c}"
    | (.role r, none) => if restated.contains r then none else some s!"{roleVar r}: initial"
    | (n, none) => some s!"{n.property}: initial") ++
    diff.defaults.toList.map fun
      | (r, some d) => s!"{roleVar r}: {cssDeclValue d}"
      | (r, none) => s!"{roleVar r}: initial")

/-- The custom-property redefinitions a body `\palette` makes against the palette before it. -/
public def epochPaletteDiff (roles : List Ir.Role) (before after : Ir.Palette) : PaletteDiff :=
  let changed := (after.entries.filter fun (n, c) =>
    (before.lookup n).map cssColor != some (cssColor c)).map fun (n, c) => (n, some c)
  let removed := (before.entries.filter fun (n, _) =>
    (after.lookup n).isNone).map fun (n, _) => (n, none)
  let entries := changed ++ removed
  let screen (d : Option Ir.CssDecl) : Option String := d.map cssDeclValue
  let undeclared := roles.filter fun r => (Ir.Design.declared? after r).isNone
  let moved := entries.toList.filterMap fun
    | (.role r, _) => some r
    | (.color _, _) => none
  let base := undeclared.filter fun r =>
    screen (Ir.Design.cssDecl after .light r) != screen (Ir.Design.cssDecl before .light r)
  let restated := Id.run do
    let mut set := base
    for _ in [0:Ir.Role.all.foldl (fun m r => max m r.depth) 0 + 1] do
      let named := undeclared.filter fun r =>
        !set.contains r && match Ir.Design.cssDecl after .light r with
          | some (.alias p) => set.contains p || moved.contains p
          | _ => false
      set := set ++ named
    return set
  { entries
    defaults := ((undeclared.filter restated.contains).map fun r =>
      (r, Ir.Design.cssDecl after .light r)).toArray }

/-- The redefinitions a body `\tokens` makes, same diff. -/
public def epochTokenStyle (basis : LengthBasis) (before after : Ir.Tokens) : String :=
  String.intercalate "; " ((after.entries.filter fun (n, g) =>
    before.find? n != some g).toList.filterMap fun (n, g) =>
      (tokenVar? n).map fun v => s!"{v}: {tokenCss basis n g.width}")

/-- The colours a listing's box may name by role, page, ink and code ground, per shipped scheme. -/
public def boxRoleTexts (frames : List Ir.SchemeFrame) (views : List Ir.Palette) :
    List (Ir.Role × List (Ir.Scheme × Option String)) :=
  [Ir.Role.page, .ink, .codeSurface].map fun r =>
    (r, (frames.zip views).map fun (f, v) => (f.scheme, (Ir.Design.at v f.scheme r).map cssColor))

/-- A palette's views in the schemes the page ships. -/
public def Config.viewsOf (cfg : Config) (p : Ir.Palette) : List Ir.Palette :=
  match cfg.paletteViews.find? (·.1 == p) with
  | some (_, vs) => vs
  | none => cfg.frames.map fun f => (p.view f).1

/-- What an epoch restates in every scheme the page ships, as one inline style. -/
public def Config.epochStyleFor (cfg : Config) (floorDiff : PaletteDiff)
    (before after : List Ir.Palette) : String :=
  if cfg.frames.all (·.scheme == cfg.floor) then floorDiff.style else
  let tabs := (cfg.frames.map (·.scheme)).zip (before.zip after)
  let add (out : Array Ir.ColorRef) (d : PaletteDiff) : Array Ir.ColorRef :=
    let out := d.entries.foldl (fun o (n, _) => if o.contains n then o else o.push n) out
    d.defaults.foldl (fun o (r, _) => if o.contains (.role r) then o else o.push (.role r)) out
  -- a scheme shipping the palette as declared moves what the floor's diff moves
  let floorHome := cfg.frames.any fun f => f.scheme == cfg.floor && f.home
  let props : Array Ir.ColorRef := (cfg.frames.zip (before.zip after)).foldl
    (fun out (f, vb, va) => if floorHome && f.home then out
      else add out (epochPaletteDiff cfg.cssRoles vb va)) (add #[] floorDiff)
  -- a removed role restates its default, since the flow's ink reads it
  String.intercalate "; " (props.toList.map fun n =>
    let texts := tabs.map fun (sc, _, va) => (sc, propText va sc n)
    let colours := tabs.map fun (sc, _, va) => (sc, (match n with
      | .role r => Ir.Design.at va sc r
      | .color _ => va.lookup n).map cssColor)
    s!"{n.property}: {schemeValue texts colours cfg.floor}")

/-- The `:root` properties the page's elements read their colours through, of those in `used`. -/
public def Config.epochVars (cfg : Config) (used : List String) :
    List (String × List (Ir.Scheme × Option String)) :=
  let ss := cfg.frames.map (·.scheme)
  (used.eraseDups.filterMap fun v => (schemeVarTexts ss v).map (v, ·))

/-- The epochs' `:root` properties the page reads, at the floor and in each scheme's block. -/
public def Config.epochVarBlocks (cfg : Config) (used : List String) : String :=
  let evs := cfg.epochVars used
  if evs.isEmpty then "" else
  ":root {\n" ++ String.join (evs.map fun (v, texts) =>
      s!"    {v}: {((texts.lookup cfg.floor).join).getD "initial"};\n") ++ "}\n" ++
    schemeBlocksOf (fun sc => if cfg.ships sc then
        some (evs.map fun (v, texts) => (v, (texts.lookup sc).join)) else none)
      cfg.floor (scheme := false)

/-- Advance the palette tokens and the flow's default ink, keeping a painted body's surface. -/
public def Config.advancePalette (cfg : Config) (p : Ir.Palette) : Config :=
  let views := cfg.viewsOf p
  let boxTexts := boxRoleTexts cfg.frames views
  let diff := epochPaletteDiff cfg.cssRoles cfg.floorPal
    (((cfg.frames.map (·.scheme)).zip views).lookup cfg.floor |>.getD p)
  let fg := Design.printInk p
  let home := cfg.bodyGround.isNone && p.sameAs cfg.docPal
  { cfg with pal := p
             views, boxTexts
             listingGround := cfg.bodyGround.or (Ir.Design.declared? p .page)
             listingFg := if home then none else some fg, bodyInk := none
             epochStyle := compactStyle (joinStyles cfg.epochStyle (cfg.epochStyleFor diff cfg.views views))
             epochPaint := if home then "" else s!"color: {roleRef .ink};"
             epochGround := cfg.bodyGround.isNone && (cfg.epochGround || diff.groundChanged) }

public theorem Config.advancePalette_ink_projects (cfg : Config) (p : Ir.Palette) :
    (cfg.advancePalette p).listingFg =
      if cfg.bodyGround.isNone && p.sameAs cfg.docPal then none
      else some (Design.ofPalette p).fg := by
  rfl

public theorem Config.advancePalette_home_exact (cfg : Config) (p : Ir.Palette)
    (hhome : (cfg.bodyGround.isNone && p.sameAs cfg.docPal) = true) :
    (cfg.advancePalette p).epochPaint = "" ∧ (cfg.advancePalette p).listingFg = none := by
  simp only [Config.advancePalette, hhome, ↓reduceIte, and_self]

/-- Advance the token state; a table length is spelled against the document's basis. -/
private def Config.advanceTokens (cfg : Config) (tk : Ir.Tokens) : Config :=
  { cfg with tokens := tk
             epochStyle := compactStyle (joinStyles cfg.epochStyle
               (epochTokenStyle cfg.lengthBasis cfg.tokens tk)) }

/-- How declarations flow past a block: through ordinary containers, never out of columns, notes
or navigation. -/
private def declarationFlow : Ir.CtxFold Bool Config where
  openBlock := fun visible cfg b => match b with
    | .columns _ | .note _ | .nav _ _ => (cfg, false)
    | .role name _ => (cfg, visible && !Ir.pageMarkerRole name)
    | .setPalette p => (if visible then cfg.advancePalette p else cfg, visible)
    | .setTokens tk => (if visible then cfg.advanceTokens tk else cfg, visible)
    | _ => (cfg, visible)
  closeBlock := fun _ cfg _ => cfg
  openInline := fun visible cfg _ => (cfg, visible)
  closeInline := fun _ cfg _ => cfg

private def Config.afterBlock (cfg : Config) : Block → Config
  | .columns _ | .note _ | .nav _ _ => cfg
  | b => Ir.foldCtxBlock declarationFlow true cfg b

private def Config.afterBlocks (cfg : Config) (body : Array Block) : Config :=
  Ir.foldCtxBlocks declarationFlow true cfg body

private theorem Config.afterBlock_columns_exact (cfg : Config)
    (cols : Array (BoxWidth × Array Block)) :
    cfg.afterBlock (.columns cols) = cfg := rfl

private theorem Config.afterBlock_palette_projects (cfg : Config) (p : Ir.Palette) :
    cfg.afterBlock (.setPalette p) = cfg.advancePalette p := rfl

/-- A ground-changing epoch's style, painting each following flow box in that ground. -/
private def epochSurfaceStyle (style : String) (groundChanged : Bool) : String :=
  if groundChanged then
    joinStyles style ("background: " ++ stageGround)
  else style

/-- An ordinary sibling's epoch style: its tokens and its concrete flow ink. -/
private def Config.flowEpochStyle (cfg : Config) : String :=
  joinStyles cfg.epochStyle cfg.epochPaint

/-- The epoch's redefinitions onto one emitted sibling, before the element's own style. -/
public def withEpoch (style : String) (groundChanged : Bool) : Node → Node
  | .elem t attrs kids =>
    let style := epochSurfaceStyle style groundChanged
    if style.isEmpty then .elem t attrs kids
    else if attrs.any (·.1 == "style") then
      .elem t (attrs.map fun kv =>
        if kv.1 == "style" then (kv.1, style ++ "; " ++ kv.2) else kv) kids
    else .elem t (attrs.push ("style", style)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

/-- Apply the epoch to a node: tokens alone on a stage or its track, flow ink as well elsewhere. -/
private def Config.applyEpoch (cfg : Config) (node : Node) : Node :=
  let stage := match node with
    | .elem tag attrs _ =>
      let classes := ((attrOf? attrs "class").getD "").splitOn " "
      (tag == "section" && (classes.contains "slide" || classes.contains "section-page")) ||
        (tag == "div" && classes.contains "slide-track")
    | .text _ | .style _ | .script .. => false
  if stage then withEpoch cfg.epochStyle false node
  else withEpoch cfg.flowEpochStyle cfg.epochGround node

public def withClass (c : String) : Node → Node
  | .elem t attrs kids =>
    if attrs.any (·.1 == "class") then
      .elem t (attrs.map fun kv => if kv.1 == "class" then (kv.1, kv.2 ++ " " ++ c) else kv) kids
    else .elem t (attrs.push ("class", c)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

public def withStyle (decls : String) : Node → Node
  | .elem t attrs kids =>
    if attrs.any (·.1 == "style") then
      .elem t (attrs.map fun kv => if kv.1 == "style" then (kv.1, kv.2 ++ "; " ++ decls) else kv) kids
    else .elem t (attrs.push ("style", decls)) kids
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

/-- A container holding `n` of its frame's fills on a deck's stage, growing by their weight. -/
public def fillCarrier (cfg : Config) (n : Nat) (node : Node) (item : Bool := false) : Node :=
  if !cfg.deck || cfg.fillsInert || n == 0 then node
  else if item then withStyle s!"flex-grow: {Ir.fillUnit * n}" node
  else withStyle s!"flex-grow: {Ir.fillUnit * n}; display: flex; flex-direction: column" node

/-- A generated leading margin as the authored addend of the frame boundary. -/
private def frameBodyBefore (style : String) : String :=
  String.intercalate ";" ((style.splitOn ";").map fun decl =>
    match decl.splitOn ":" with
    | [key, value] =>
      if key.trimAscii.toString == "margin-top" then
        s!"--frame-body-before: {value.trimAscii.toString}"
      else decl
    | _ => decl)

/-- An element's generated leading margin as the frame boundary's addend
(`frameBodyBefore`). -/
private def openingStyle : Node → Node
  | .elem tag attrs body =>
    .elem tag (attrs.map fun (key, value) =>
      (key, if key == "style" then frameBodyBefore value else value)) body
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

mutual

/-- The element a carrier's flow opens on, marked `frame-flow-start` down its
first children — in every group of an alternation, each the opening of the
snaps that show it — carrying the frame's opening there, where the page
opens it: on the block, never on the carrier around it. -/
private def markFlowStart : Node → Node
  | .elem tag attrs kids =>
    if isAltPair (.elem tag attrs kids) then .elem tag attrs (markGroupsStart kids.toList).toArray
    else if isLinkCarrier (.elem tag attrs kids) then
      .elem tag attrs (markFirstList kids.toList).toArray
    else withClass "frame-flow-start" (openingStyle (.elem tag attrs kids))
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

-- conserves: none — the first element of a carrier for `markFlowStart`; it marks one class.
private def markFirstList : List Node → List Node
  | [] => []
  | x :: rest =>
    match x with
    | .elem .. => markFlowStart x :: rest
    | .text _ | .style _ | .script _ _ => x :: markFirstList rest

-- conserves: none — an alternation's groups for `markFlowStart`; it marks one class.
private def markGroupsStart : List Node → List Node
  | [] => []
  | x :: rest => markFlowStart x :: markGroupsStart rest

end

/-- Put the frame boundary on its first participating body element. State,
text and hidden speaker notes do not take it. A generated leading margin
joins the fixed opening at its one owner; the element tree is unchanged.
Where that element is an overlay's carrier, the block its flow opens on
takes the opening (`markFlowStart`). -/
private def frameBodyStart (kids : Array Node) : Array Node :=
  match kids.findIdx? (fun node => match node with
    | .elem _ attrs _ => !(attrs.any (·.1 == "hidden"))
    | .text _ | .style _ | .script .. => false) with
  | some i => kids.modify i fun node =>
    let node := withClass "frame-body-start" (openingStyle node)
    if isCarrierNode node then markFlowStart node else node
  | none => kids

mutual

/-- Mark the element a carrier's flow ends on `frame-flow-end`, down its last children. -/
private def markFlowEnd : Node → Node
  | .elem tag attrs kids =>
    if isLinkCarrier (.elem tag attrs kids) then .elem tag attrs (markLastList kids.toList).toArray
    else if classHas (attrsClass attrs) "alt-pair" then
      .elem tag attrs (markGroupsList (classHas (attrsClass attrs) "alt-alike") kids.toList).toArray
    else withClass "frame-flow-end" (.elem tag attrs kids)
  | .text s => .text s
  | .style css => .style css
  | .script attrs code => .script attrs code

-- conserves: none — the last element of a carrier for `markFlowEnd`
private def markLastList : List Node → List Node
  | [] => []
  | x :: rest =>
    if rest.any (· matches .elem ..) then x :: markLastList rest
    else (match x with
      | .elem .. => markFlowEnd x
      | .text _ | .style _ | .script _ _ => x) :: rest

-- conserves: none — an alternation's groups for `markFlowEnd`
private def markGroupsList (alike : Bool) : List Node → List Node
  | [] => []
  | x :: rest =>
    (if classHas (classOfNode x) "alt" && (alike || !hiddenNode x) then markFlowEnd x else x) ::
      markGroupsList alike rest

end

/-- Where a frame's body ends on a carrier or before speaker notes, mark the block its flow ends
on. -/
private def frameFlowEnd (kids : Array Node) : Array Node × Bool :=
  match (kids.toList.zipIdx.reverse.find? fun (node, _) => match node with
    | .elem _ attrs _ => !(attrs.any (·.1 == "hidden"))
    | .text _ | .style _ | .script .. => false) with
  | some (node, i) =>
    let notesAfter := (kids.extract (i + 1) kids.size).any (· matches .elem ..)
    if isCarrierNode node || notesAfter then (kids.modify i markFlowEnd, true) else (kids, false)
  | none => (kids, false)

/-- Mark a frame's last participating body element. -/
private def frameBodyEnd (kids : Array Node) : Array Node :=
  let ends (node : Node) : Bool := match node with
    | .elem _ attrs _ => !(attrs.any (·.1 == "hidden"))
    | .text _ | .style _ | .script .. => false
  match (List.range kids.size).reverse.find? (fun i => (kids[i]?.map ends).getD false) with
  | some i => kids.modify i (withClass "frame-body-end")
  | none => kids

/-- Whether a frame's first body element owns the frame opening. -/
public def frameOpensBody (chromeAllowed hasTitle : Bool) (valign : VAlign) : Bool :=
  hasTitle || Ir.frameInTextArea chromeAllowed valign

public theorem frameOpensBody_projects (chromeAllowed : Bool) (valign : VAlign) :
    frameOpensBody chromeAllowed false valign = Ir.frameInTextArea chromeAllowed valign := by
  simp only [frameOpensBody, Bool.false_or]

/-- One reference-list entry: its marker, its content and its anchor. -/
private def bibItemNode (cfg : Config) (item : Ir.BibItem) : Node :=
  let kids : Array Node := match item.marker with
    | some m => #[Html.elem "span" #[Html.text s!"[{m}]"]
          #[("class", if item.labelFlush then "bib-marker flush" else "bib-marker")],
        Html.text " ", Html.elem "span" (inlines cfg item.content) #[("class", "bib-entry")]]
    | none => inlines cfg item.content
  Html.elem "li" kids #[("id", Ir.bibAnchor item.key)]

private theorem bibItemNode_key_enters_attribute_position (cfg : Config)
    (item : Ir.BibItem) :
    ∃ kids, bibItemNode cfg item =
      Html.elem "li" kids #[("id", Ir.bibAnchor item.key)] :=
  ⟨_, rfl⟩

/-- One algorithm line's place in the nesting its declared depths imply. -/
private inductive AlgTree where
  | node (line : Option Ir.AlgLine) (kids : Array AlgTree)

mutual

/-- The lines one nesting node carries, in document order. -/
private def algLinesOne (acc : Array Ir.AlgLine) : AlgTree → Array Ir.AlgLine
  | .node none kids => algLinesList acc kids.toList
  | .node (some l) kids => algLinesList (acc.push l) kids.toList

private def algLinesList (acc : Array Ir.AlgLine) : List AlgTree → Array Ir.AlgLine
  | [] => acc
  | t :: rest => algLinesList (algLinesOne acc t) rest

end

/-- One finished level attached to the node it stood under. -/
private def algAttach (inner top : Array AlgTree) : Array AlgTree :=
  match top.back? with
  | some (.node l kids) => top.pop.push (.node l (kids ++ inner))
  | none => top.push (.node none inner)

/-- Close the innermost open level into the one beneath it. -/
private def algClose : List (Array AlgTree) → List (Array AlgTree)
  | inner :: top :: rest => algAttach inner top :: rest
  | [lvl] => [lvl]
  | [] => []

private def algCloseN : Nat → List (Array AlgTree) → List (Array AlgTree)
  | 0, s => s
  | n + 1, s => algCloseN n (algClose s)

/-- Open `n` levels under the current one. -/
private def algOpenN : Nat → List (Array AlgTree) → List (Array AlgTree)
  | 0, s => s
  | n + 1, s => algOpenN n (#[] :: s)

/-- One line onto the stack, at the depth it declares. -/
private def algStep (s : List (Array AlgTree)) (l : Ir.AlgLine) : List (Array AlgTree) :=
  let closed := algCloseN (s.length - (l.depth + 1)) s
  let opened := algOpenN (l.depth + 1 - closed.length) closed
  (opened.headD #[]).push (.node (some l) #[]) :: opened.tail

/-- The nesting an algorithm's lines declare, as a forest. -/
private def algNest (lines : Array Ir.AlgLine) : Array AlgTree :=
  let s := lines.foldl algStep [#[]]
  (algCloseN (s.length - 1) s).headD #[]

/-- Every line the stack holds, bottom level first. -/
private def algStackLines (s : List (Array AlgTree)) : Array Ir.AlgLine :=
  s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) #[]

mutual

private theorem algLinesOne_acc (acc : Array Ir.AlgLine) (t : AlgTree) :
    algLinesOne acc t = acc ++ algLinesOne #[] t := by
  match t with
  | .node none kids =>
    rw [algLinesOne, algLinesOne, algLinesList_acc acc kids.toList]
  | .node (some l) kids =>
    rw [algLinesOne, algLinesOne, algLinesList_acc (acc.push l) kids.toList,
      algLinesList_acc ((#[] : Array Ir.AlgLine).push l) kids.toList,
      Array.push_eq_append, Array.push_eq_append, Array.empty_append,
      Array.append_assoc]

private theorem algLinesList_acc (acc : Array Ir.AlgLine) (xs : List AlgTree) :
    algLinesList acc xs = acc ++ algLinesList #[] xs := by
  match xs with
  | [] => rw [algLinesList, algLinesList, Array.append_empty]
  | t :: rest =>
    rw [algLinesList, algLinesList, algLinesList_acc (algLinesOne acc t) rest,
      algLinesList_acc (algLinesOne #[] t) rest, algLinesOne_acc acc t,
      Array.append_assoc]

end

private theorem algLinesList_append (xs ys : List AlgTree) :
    algLinesList #[] (xs ++ ys)
      = algLinesList #[] xs ++ algLinesList #[] ys := by
  induction xs with
  | nil => rw [List.nil_append, algLinesList, Array.empty_append]
  | cons t rest ih =>
    rw [List.cons_append, algLinesList, algLinesList,
      algLinesList_acc (algLinesOne #[] t) (rest ++ ys), ih,
      algLinesList_acc (algLinesOne #[] t) rest, Array.append_assoc]

private theorem algLinesList_acc_append (acc : Array Ir.AlgLine)
    (xs ys : List AlgTree) :
    algLinesList acc (xs ++ ys)
      = acc ++ algLinesList #[] xs ++ algLinesList #[] ys := by
  rw [algLinesList_acc, algLinesList_append, Array.append_assoc]

private theorem algLinesList_push (xs : Array AlgTree) (t : AlgTree) :
    algLinesList #[] (xs.push t).toList
      = algLinesList #[] xs.toList ++ algLinesOne #[] t := by
  rw [Array.toList_push, algLinesList_append, algLinesList, algLinesList]

private theorem algAttach_lines (inner top : Array AlgTree) :
    algLinesList #[] (algAttach inner top).toList
      = algLinesList #[] top.toList ++ algLinesList #[] inner.toList := by
  rw [algAttach]
  split
  · next l kids h =>
    obtain ⟨ys, hy⟩ := Array.back?_eq_some_iff.1 h
    subst hy
    rw [Array.pop_push, algLinesList_push, algLinesList_push]
    cases l with
    | none =>
      rw [algLinesOne, algLinesOne, Array.toList_append,
        algLinesList_acc_append, Array.empty_append, Array.append_assoc]
    | some l =>
      rw [algLinesOne, algLinesOne, Array.toList_append,
        algLinesList_acc_append,
        algLinesList_acc ((#[] : Array Ir.AlgLine).push l) kids.toList]
      simp [Array.append_assoc]
  · next h =>
    rw [Array.back?_eq_none_iff.1 h, algLinesList_push, algLinesOne,
      algLinesList, algLinesList_acc #[] inner.toList, Array.empty_append,
      Array.empty_append]

private theorem algLevelsFoldl (s : List (Array AlgTree))
    (acc : Array Ir.AlgLine) :
    s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) acc
      = s.foldl (fun acc lvl => algLinesList #[] lvl.toList ++ acc) #[] ++ acc := by
  induction s generalizing acc with
  | nil => rw [List.foldl_nil, List.foldl_nil, Array.empty_append]
  | cons b bs ih =>
    rw [List.foldl_cons, List.foldl_cons, ih,
      ih (algLinesList #[] b.toList ++ #[]), Array.append_empty,
      Array.append_assoc]

private theorem algStackLines_cons (a : Array AlgTree)
    (rest : List (Array AlgTree)) :
    algStackLines (a :: rest)
      = algStackLines rest ++ algLinesList #[] a.toList := by
  unfold algStackLines
  rw [List.foldl_cons, algLevelsFoldl, Array.append_empty]

private theorem algStackLines_nil :
    algStackLines [] = (#[] : Array Ir.AlgLine) := rfl

private theorem algClose_lines (s : List (Array AlgTree)) :
    algStackLines (algClose s) = algStackLines s := by
  match s with
  | [] => rfl
  | [_] => rfl
  | inner :: top :: rest =>
    rw [algClose, algStackLines_cons, algStackLines_cons, algStackLines_cons,
      algAttach_lines, Array.append_assoc]

private theorem algCloseN_lines (n : Nat) (s : List (Array AlgTree)) :
    algStackLines (algCloseN n s) = algStackLines s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [algCloseN, ih, algClose_lines]

private theorem algOpenN_lines (n : Nat) (s : List (Array AlgTree)) :
    algStackLines (algOpenN n s) = algStackLines s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [algOpenN, ih, algStackLines_cons, Array.toList_empty, algLinesList,
      Array.append_empty]

private theorem algStackLines_headD (t : List (Array AlgTree)) :
    algStackLines t.tail ++ algLinesList #[] (t.headD #[]).toList
      = algStackLines t := by
  match t with
  | [] =>
    rw [List.tail_nil, algStackLines_nil, List.headD_nil, Array.toList_empty,
      algLinesList, Array.append_empty]
  | _ :: _ => rw [algStackLines_cons]; rfl

private theorem algStep_lines (s : List (Array AlgTree)) (l : Ir.AlgLine) :
    algStackLines (algStep s l) = algStackLines s ++ #[l] := by
  rw [algStep, algStackLines_cons, algLinesList_push, algLinesOne,
    Array.toList_empty, algLinesList, Array.push_eq_append, Array.empty_append,
    ← Array.append_assoc, algStackLines_headD, algOpenN_lines, algCloseN_lines]

private theorem algStep_ne_nil (s : List (Array AlgTree)) (l : Ir.AlgLine) :
    algStep s l ≠ [] := by rw [algStep]; exact List.cons_ne_nil _ _

private theorem algFold_lines (xs : List Ir.AlgLine)
    (init : List (Array AlgTree)) :
    algStackLines (xs.foldl algStep init)
      = algStackLines init ++ xs.toArray := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons, ih, algStep_lines, Array.append_assoc]
    congr 1
    apply Array.toList_inj.1
    simp

private theorem algFold_ne_nil (xs : List Ir.AlgLine)
    (init : List (Array AlgTree)) (h : init ≠ []) :
    xs.foldl algStep init ≠ [] := by
  induction xs generalizing init with
  | nil => rwa [List.foldl_nil]
  | cons x rest ih =>
    rw [List.foldl_cons]
    exact ih (algStep init x) (algStep_ne_nil init x)

private theorem algCloseN_length (n : Nat) (s : List (Array AlgTree))
    (h : s.length = n + 1) : (algCloseN n s).length = 1 := by
  induction n generalizing s with
  | zero => rw [algCloseN]; omega
  | succ n ih =>
    rw [algCloseN]
    refine ih (algClose s) ?_
    match s with
    | [] => simp at h
    | [_] => simp at h
    | _ :: _ :: rest =>
      rw [algClose, List.length_cons]
      simp only [List.length_cons] at h
      omega

private theorem algorithm_lines_agree (lines : Array Ir.AlgLine) :
    algLinesList #[] (algNest lines).toList = lines := by
  rw [algNest]
  have hne : lines.foldl algStep [#[]] ≠ [] := by
    rw [← Array.foldl_toList]
    exact algFold_ne_nil lines.toList [#[]] (List.cons_ne_nil _ _)
  have hlen : (lines.foldl algStep [#[]]).length
      = ((lines.foldl algStep [#[]]).length - 1) + 1 := by
    have := List.length_pos_iff.2 hne; omega
  have h1 := algCloseN_length _ _ hlen
  have hfold : algStackLines (lines.foldl algStep [#[]]) = lines := by
    rw [← Array.foldl_toList, algFold_lines, algStackLines_cons,
      algStackLines_nil, Array.toList_empty, algLinesList, Array.empty_append,
      Array.empty_append]
  have hpres := algCloseN_lines ((lines.foldl algStep [#[]]).length - 1)
    (lines.foldl algStep [#[]])
  rw [hfold] at hpres
  match hm : algCloseN ((lines.foldl algStep [#[]]).length - 1)
      (lines.foldl algStep [#[]]) with
  | [] => rw [hm] at h1; simp at h1
  | _ :: _ :: _ => rw [hm] at h1; simp at h1
  | [a] =>
    rw [hm] at hpres
    rw [List.headD_cons, ← hpres, algStackLines_cons, algStackLines_nil,
      Array.empty_append]

mutual

/-- One nesting node as a list item: its line's inlines, then its kids' nested list. -/
private def algRenderOne (payload : Ir.AlgLine → Array Node) : AlgTree → Node
  | .node l kids =>
    let pay := match l with
      | some l => payload l
      | none => #[]
    Html.elem "li" (if kids.isEmpty then pay
      else pay.push (Html.elem "ol" (algRenderList payload #[] kids.toList) #[])) #[]

private def algRenderList (payload : Ir.AlgLine → Array Node) (acc : Array Node) :
    List AlgTree → Array Node
  | [] => acc
  | t :: rest => algRenderList payload (acc.push (algRenderOne payload t)) rest

end

private def labelPiece : Inline → String
  | .math _ src => Ir.mathFloor src
  | .formula _ _ body => Ir.formulaFloor body
  | inl => Ir.plainTextOne inl

/-- The face a picture label's run is set in, on the axes the PDF resolves. -/
public structure LabelFace where
  weight : Ir.Weight := .m
  italic : Bool := false
  slot : Nat := 0
  smallcaps : Bool := false
  size : Option String := none
  lang : Option String := none
  deriving BEq, Inhabited

/-- One style's step on a label's face, as the PDF takes it. -/
public def LabelFace.step (f : LabelFace) (s : Style) : LabelFace :=
  let f := { f with weight := (s.weight?).getD f.weight }
  match s with
  | .italic => { f with italic := true }
  | .emph => { f with italic := !f.italic }
  | .upright => { f with italic := false, smallcaps := false }
  | .smallcaps => { f with smallcaps := true }
  | .mono => { f with slot := 2 }
  | .sans => { f with slot := 1 }
  | .roman => { f with slot := 0 }
  | .family s => { f with slot := s }
  | .normal => {}
  | .lang tag => { f with lang := some tag }
  | .size n => { f with size := some n }
  | .fontSize _ _ => f
  | .bold | .medium | .series _ => f

/-- A face as the attributes of its `<tspan>`, relative to the label's regular, upright `<text>`. -/
public def LabelFace.attrs (f : LabelFace) : Array (String × String) :=
  let weight : Array (String × String) :=
    if f.weight == .m then #[]
    else if f.weight == .b then #[("font-weight", "bolder")]
    else #[("font-weight", toString f.weight.css)]
  let slant : Array (String × String) := if f.italic then #[("font-style", "italic")] else #[]
  let classes := (if f.slot == 1 then [styleClass .sans] else []) ++
    (if f.smallcaps then [styleClass .smallcaps] else []) ++
    (match f.size with
     | some n => [styleClass (.size n)]
     | none => [])
  let cls : Array (String × String) :=
    if classes.isEmpty then #[] else #[("class", " ".intercalate classes)]
  let family : Array (String × String) :=
    if f.slot == 2 then #[("style", "font-family: var(--font-mono)")]
    else if Ir.familySlotBase ≤ f.slot then #[("style", s!"font-family: var(--font-{f.slot})")]
    else #[]
  let lang : Array (String × String) := match f.lang with
    | some tag => #[("lang", tag)]
    | none => #[]
  weight ++ slant ++ cls ++ family ++ lang

/-- One run of text in a face: SVG character data or a `<tspan>`, or an `mtext` beside native
math. -/
public def LabelFace.run (f : LabelFace) (s : String) (nativeMath : Bool := false) : Node :=
  let a := f.attrs
  if nativeMath then
    let css := a.toList.filterMap fun (k, v) =>
      if k == "style" then some v
      else if k == "font-weight" || k == "font-style" then some s!"{k}: {v}"
      else none
    Html.elem "mtext" #[Html.text s]
      ((a.filter fun (k, _) => k != "style" && k != "font-weight" && k != "font-style").push
        ("style", "; ".intercalate ("white-space: pre" :: css)))
  else if a.isEmpty then Html.text s else Html.elem "tspan" #[Html.text s] a

mutual

/-- One inline of a picture label as SVG `<text>` children, each run carrying its full face. -/
public def labelNodesOne (f : LabelFace) (acc : Array Node) (x : Inline)
    (mathCfg : Option Config := none) : Array Node :=
  let native := mathCfg.isSome
  match x with
  | .text s => acc.push (f.run s native)
  | .formula display src body =>
    match mathCfg with
    | some cfg => acc.push (MathMl.formulaRow display #[("class", "math"), ("data-tex", src)]
        body (mathMarks cfg))
    | none => acc.push (Html.elem "tspan" #[Html.text (labelPiece x)] #[("font-style", "italic")])
  | .math _ _ => acc.push (({ italic := true } : LabelFace).run (labelPiece x) native)
  | .styled st body => labelNodesList (f.step st) acc body.toList
      (mathCfg.map fun cfg => { cfg with mathStyles := cfg.mathStyles.push st })
  | .colored c name body =>
    let paint := match name with
      | some n => ("style", s!"{if native then "color" else "fill"}: var({n.property}, {cssColor c})")
      | none => if native then ("style", s!"color: {cssColor c}") else ("fill", cssColor c)
    acc.push (Html.elem (if native then "mrow" else "tspan")
      (labelNodesList f #[] body.toList mathCfg) #[paint])
  | .role n body =>
    acc.push (Html.elem (if native then "mrow" else "tspan")
      (labelNodesList f #[] body.toList mathCfg) #[("class", roleClass n)])
  | .located _ body => labelNodesList f acc body.toList mathCfg
  | .italicCorr _ => acc
  | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .fill | .hspace _ _ | .rule _ _ _ | .strut _
  | .pageNumber | .pageCount | .linebreak _ | .image _ _ _ | .icon _ _ | .label _
  | .ref _ _ _ _ | .cite _ _ | .footnote _ _ => acc.push (f.run (labelPiece x) native)

public def labelNodesList (f : LabelFace) (acc : Array Node) (xs : List Inline)
    (mathCfg : Option Config := none) : Array Node :=
  match xs with
  | [] => acc
  | x :: rest => labelNodesList f (labelNodesOne f acc x mathCfg) rest mathCfg

end

public theorem labelFormula_glyphs_agree (f : LabelFace) (cfg : Config)
    (display : Bool) (src : String) (body : Math.MList) :
    MathMl.nodeListChars #[]
      (labelNodesOne f #[] (.formula display src body) (some cfg)).toList =
        MathMl.listChars #[] body := by
  simpa only [labelNodesOne, Array.toList_push, List.nil_append,
    Array.toList_empty, MathMl.nodeListChars_cons, MathMl.nodeListChars_nil] using
      MathMl.formulaRow_glyphs_agree display _ body (mathMarks cfg)

private theorem labelRun_mathFree (f : LabelFace) (s : String) (native : Bool) :
    MathMl.tagFree (· == "math") (f.run s native) = true := by
  unfold LabelFace.run
  cases native with
  | true => simp [Html.elem, Html.text, MathMl.tagFree, MathMl.tagFreeList]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    split <;> simp [Html.elem, Html.text, MathMl.tagFree, MathMl.tagFreeList]

mutual

/-- Artifact-specific. -/
public theorem labelNodesOne_mathFree_contract (f : LabelFace) (acc : Array Node) (x : Inline)
    (mathCfg : Option Config)
    (ha : MathMl.tagFreeList (· == "math") acc.toList = true) :
    MathMl.tagFreeList (· == "math") (labelNodesOne f acc x mathCfg).toList = true := by
  match x with
  | .text s =>
    simp only [labelNodesOne, MathMl.tagFreeList_push, ha, labelRun_mathFree, Bool.and_self]
  | .formula display src body =>
    cases mathCfg with
    | some cfg =>
      simp only [labelNodesOne, MathMl.tagFreeList_push, ha,
        MathMl.formulaRow_mathFree_contract, Bool.and_self]
    | none =>
      simp [labelNodesOne, MathMl.tagFreeList_append, ha, Html.elem, Html.text,
        MathMl.tagFree, MathMl.tagFreeList]
  | .math _ _ =>
    simp only [labelNodesOne, MathMl.tagFreeList_push, ha, labelRun_mathFree, Bool.and_self]
  | .styled st body =>
    simp only [labelNodesOne]
    exact labelNodesList_mathFree_contract _ acc body.toList _ ha
  | .colored c name body =>
    have hk := labelNodesList_mathFree_contract f #[] body.toList mathCfg rfl
    cases mathCfg <;> cases name <;>
      simp [labelNodesOne, MathMl.tagFreeList_append, MathMl.tagFreeList, ha, Html.elem,
        MathMl.tagFree, hk]
  | .role n body =>
    have hk := labelNodesList_mathFree_contract f #[] body.toList mathCfg rfl
    cases mathCfg <;>
      simp [labelNodesOne, MathMl.tagFreeList_append, MathMl.tagFreeList, ha, Html.elem,
        MathMl.tagFree, hk]
  | .located _ body =>
    simp only [labelNodesOne]
    exact labelNodesList_mathFree_contract f acc body.toList mathCfg ha
  | .italicCorr _ => simpa only [labelNodesOne] using ha
  | .link _ _ | .decorated _ _ | .onSteps _ _ | .altSteps _ _ _ | .fill | .hspace _ _
  | .rule _ _ _ | .strut _ | .pageNumber | .pageCount | .linebreak _ | .image _ _ _
  | .icon _ _ | .label _ | .ref _ _ _ _ | .cite _ _ | .footnote _ _ =>
    simp only [labelNodesOne, MathMl.tagFreeList_push, ha, labelRun_mathFree, Bool.and_self]

/-- Artifact-specific. -/
public theorem labelNodesList_mathFree_contract (f : LabelFace) (acc : Array Node)
    (xs : List Inline) (mathCfg : Option Config)
    (ha : MathMl.tagFreeList (· == "math") acc.toList = true) :
    MathMl.tagFreeList (· == "math") (labelNodesList f acc xs mathCfg).toList = true := by
  match xs with
  | [] => simpa only [labelNodesList] using ha
  | x :: rest =>
    simp only [labelNodesList]
    exact labelNodesList_mathFree_contract f _ rest mathCfg
      (labelNodesOne_mathFree_contract f acc x mathCfg ha)

end

/-- A picture label as SVG `<text>` runs or one MathML carrier, at the IR's measured baseline. -/
public def pictureLabelNode (metric : Ir.Pic.LabelMetric) (cfg : Config) (fr : GfxSvg.SFrame)
    (l : Gfx.LabelSpec) : Node :=
  let anchor := match l.align with
    | .center | .south | .north => "middle"
    | .west => "start"
    | .east => "end"
  let baseline := Ir.Pic.labelBaseline l.y l.align (metric l.content l.scale)
  let size := (Ir.baseFontSize * (l.scale : Int) / 1000).toPtString
  let (px, py) : Dim.Sp × Dim.Sp := match fr.iso with
    | some t => t.apply (l.x, baseline)
    | none => (l.x, -baseline)
  let placed := #[
    ("x", px.toPtString),
    ("y", py.toPtString),
    ("dominant-baseline", "alphabetic")]
  let node :=
    if Ir.anyInline (fun x => match x with | .formula _ _ _ => true | _ => false) l.content then
      let shift := match l.align with
        | .center | .south | .north => "-50%"
        | .west => "0%"
        | .east => "-100%"
      let nodes := labelNodesList {} #[] l.content.toList (some { cfg with mathStyles := #[] })
      -- SVG 2 §12.5: a foreignObject paints only with a positive viewport, hence the 1×1 box
      Html.elem "foreignObject" #[
        Html.elem "div" #[
          Html.elem "math" #[
            Html.elem "mpadded"
              #[Html.elem "mrow" nodes #[("style", s!"font-size: {size}px")]]
              #[("height", "0px"), ("depth", "0px")]]
            #[("style", "font-size: 0; font-family: inherit")]]
          #[("xmlns", "http://www.w3.org/1999/xhtml"),
            ("style", s!"font-size: 0; line-height: 0; width: max-content; \
transform: translateX({shift}); color: {cssColor l.color}")]]
        (placed ++ #[("width", "1"), ("height", "1"), ("overflow", "visible")])
    else
      Html.elem "text" (labelNodesList {} #[] l.content.toList)
        (placed ++ #[("fill", cssColor l.color), ("font-size", size), ("text-anchor", anchor)])
  match fr.iso with
  | some _ => node
  | none => Html.elem "g" #[node] #[GfxSvg.transformAttr ⟨1, 0, 0, -1, 0, 0⟩]

/-- The isometry from picture coordinates, y up, into the SVG's frame, y down. -/
@[expose] public def pictureIso (box : Ir.Pic.Box) : Gfx.Iso :=
  { flipY := true, dx := -box.1.1, dy := box.2.2 }

/-- A picture's typed SVG tree in its box: the lowered figure and its labels. -/
public def pictureTree (pic : Ir.Pic.Picture) (box : Ir.Pic.Box)
    (metric : Ir.Pic.LabelMetric := fun _ _ => {}) (cfg : Config := {}) : Array GfxSvg.El :=
  GfxSvg.tree (pictureLabelNode metric cfg) #[] (pictureIso box) (Gfx.ofPictureIn box pic)

/-- A picture's shapes as SVG children, in the box the viewBox declares. -/
public def pictureKids (pic : Ir.Pic.Picture) (box : Ir.Pic.Box)
    (metric : Ir.Pic.LabelMetric := fun _ _ => {}) (cfg : Config := {}) : Array Node :=
  GfxSvg.spell 0 (pictureTree pic box metric cfg)

private theorem pictureLabelNode_baseline (box : Ir.Pic.Box) (metric : Ir.Pic.LabelMetric)
    (cfg : Config) (l : Gfx.LabelSpec) :
    (match pictureLabelNode metric cfg { iso := some (pictureIso box) } l with
      | .elem _ attrs _ => (attrOf? attrs "y", attrOf? attrs "dominant-baseline")
      | _ => (none, none)) =
      (some (box.2.2 - Ir.Pic.labelBaseline l.y l.align (metric l.content l.scale)).toPtString,
        some "alphabetic") := by
  by_cases hm : Ir.anyInline
      (fun x => match x with | .formula _ _ _ => true | _ => false) l.content = true <;>
    simp only [pictureLabelNode, hm, ite_true, pictureIso, Gfx.Iso.apply] <;>
    rfl

mutual

private theorem treeOne_lift_rawsAll {L : Type} (lab : GfxSvg.SFrame → L → Node)
    (q : Node → Bool) :
    ∀ (fr : GfxSvg.SFrame) (acc : Array GfxSvg.El) (n : Gfx.Node Empty),
      GfxSvg.El.rawsAllList q (GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.Node.lift n)).toList =
        GfxSvg.El.rawsAllList q acc.toList
  | fr, acc, .draw g fl st => by
    simp [Gfx.Node.lift, GfxSvg.treeOne, GfxSvg.El.rawsAllList_append, GfxSvg.El.rawsAll,
      GfxSvg.El.rawsAllList]
  | fr, acc, .group xf clips alpha kids => by
    have hk : GfxSvg.El.rawsAllList q (GfxSvg.treeList lab #[] #[] #[]
        (fr.enter (GfxSvg.groupXf fr xf)) #[] (Gfx.Node.liftList #[] kids.toList).toList).toList =
        true := by
      rw [Gfx.Node.liftList_map]
      simp only [Array.empty_append, List.toList_toArray]
      rw [treeList_lift_rawsAll lab q _ #[] kids.toList]
      rfl
    simp only [Gfx.Node.lift, GfxSvg.treeOne, Array.toList_push, GfxSvg.El.rawsAllList_append,
      GfxSvg.El.rawsAllList, GfxSvg.El.rawsAll, GfxSvg.El.rawsAllList_nestClips, hk, Bool.and_true]
  | fr, acc, .use k xf => by simp [Gfx.Node.lift, GfxSvg.treeOne]
  | fr, acc, .stamp o xf fl st => by
    simp [Gfx.Node.lift, GfxSvg.treeOne, GfxSvg.El.rawsAllList_append, GfxSvg.El.rawsAll,
      GfxSvg.El.rawsAllList]
  | fr, acc, .image k xf => by
    simp [Gfx.Node.lift, GfxSvg.treeOne, GfxSvg.El.rawsAllList_append, GfxSvg.El.rawsAll,
      GfxSvg.El.rawsAllList]
  | _, _, .label l => nomatch l
  | fr, acc, .words w => by simp [Gfx.Node.lift, GfxSvg.treeOne]

private theorem treeList_lift_rawsAll {L : Type} (lab : GfxSvg.SFrame → L → Node)
    (q : Node → Bool) :
    ∀ (fr : GfxSvg.SFrame) (acc : Array GfxSvg.El) (xs : List (Gfx.Node Empty)),
      GfxSvg.El.rawsAllList q (GfxSvg.treeList lab #[] #[] #[] fr acc (xs.map Gfx.Node.lift)).toList =
        GfxSvg.El.rawsAllList q acc.toList
  | fr, acc, [] => rfl
  | fr, acc, n :: rest => by
    simp only [List.map_cons, GfxSvg.treeList]
    rw [treeList_lift_rawsAll lab q fr _ rest, treeOne_lift_rawsAll lab q fr acc n]

end

private theorem treeOne_lift_one {L : Type} (lab : GfxSvg.SFrame → L → Node)
    (fr : GfxSvg.SFrame) (acc : Array GfxSvg.El) (n : Gfx.Node Empty)
    (h : Gfx.shapeOneEl (.ink n) = true) :
    ∃ e, GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.Node.lift n) = acc.push e := by
  cases n with
  | draw g fl st => exact ⟨_, rfl⟩
  | group xf clips alpha kids => exact ⟨_, rfl⟩
  | use k xf => simp [Gfx.shapeOneEl] at h
  | stamp o xf fl st => exact ⟨_, rfl⟩
  | image k xf => exact ⟨_, rfl⟩
  | label l => exact nomatch l
  | words w => simp [Gfx.shapeOneEl] at h

private theorem treeOne_lift_none {L : Type} (lab : GfxSvg.SFrame → L → Node)
    (fr : GfxSvg.SFrame) (acc : Array GfxSvg.El) (n : Gfx.Node Empty)
    (h : Gfx.shapeOneEl (.ink n) = false) :
    GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.Node.lift n) = acc := by
  cases n with
  | draw g fl st => simp [Gfx.shapeOneEl] at h
  | group xf clips alpha kids => simp [Gfx.shapeOneEl] at h
  | use k xf => simp [Gfx.Node.lift, GfxSvg.treeOne]
  | stamp o xf fl st => simp [Gfx.shapeOneEl] at h
  | image k xf => simp [Gfx.shapeOneEl] at h
  | label l => exact nomatch l
  | words w => simp [Gfx.Node.lift, GfxSvg.treeOne]

private theorem pictureShapes_tree (metric : Ir.Pic.LabelMetric) (cfg : Config) (box : Ir.Pic.Box) :
    ∀ (acc : Array GfxSvg.El) (ss : List Ir.Pic.Shape),
      let lab := pictureLabelNode metric cfg
      let fr : GfxSvg.SFrame := { iso := some (pictureIso box) }
      let t := GfxSvg.treeList lab #[] #[] #[] fr acc (ss.map Gfx.ofShape)
      (∀ q : Node → Bool, (∀ l, q (lab fr l) = true) →
          GfxSvg.El.rawsAllList q t.toList = GfxSvg.El.rawsAllList q acc.toList) ∧
        (∃ es : Array GfxSvg.El, t = acc ++ es ∧
            ∀ (i : Nat) (l : Gfx.LabelSpec), (ss[i]?.bind Gfx.labelOf?) = some l →
              es[(ss.take i).countP Gfx.shapeOneEl]? = some (GfxSvg.El.raw (lab fr l)))
  | acc, [] => ⟨fun _ _ => rfl, ⟨#[], by simp [GfxSvg.treeList], fun i l hl => by simp at hl⟩⟩
  | acc, s :: rest => by
    intro lab fr t
    have hcons : t = GfxSvg.treeList lab #[] #[] #[] fr
        (GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.ofShape s)) (rest.map Gfx.ofShape) := rfl
    obtain ⟨ih1, es, hes, hidx⟩ := pictureShapes_tree metric cfg box
      (GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.ofShape s)) rest
    refine ⟨fun q hq => ?_, ?_⟩
    · rw [hcons, ih1 q hq]
      cases s with
      | label x y content color scale align =>
        simp [Gfx.ofShape, GfxSvg.treeOne, GfxSvg.El.rawsAllList_append, GfxSvg.El.rawsAll,
          GfxSvg.El.rawsAllList, hq]
      | ink n => exact treeOne_lift_rawsAll lab q fr acc n
    · cases hso : Gfx.shapeOneEl s with
      | true =>
        have hone : ∃ e, GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.ofShape s) = acc.push e ∧
            ∀ l, Gfx.labelOf? s = some l → e = GfxSvg.El.raw (lab fr l) := by
          cases s with
          | label x y content color scale align =>
            exact ⟨_, rfl, fun l hl => by
              simp only [Gfx.labelOf?, Option.some.injEq] at hl
              subst hl
              rfl⟩
          | ink n =>
            obtain ⟨e, he⟩ := treeOne_lift_one lab fr acc n hso
            exact ⟨e, he, fun l hl => by simp [Gfx.labelOf?] at hl⟩
        obtain ⟨e, he, hel⟩ := hone
        refine ⟨#[e] ++ es, ?_, fun i l hl => ?_⟩
        · rw [hcons, hes, he]
          simp
        · cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.bind_some] at hl
            rw [hel l hl, List.take_zero, List.countP_nil, Array.getElem?_append_left (by simp)]
            rfl
          | succ i =>
            simp only [List.getElem?_cons_succ] at hl
            simp only [List.take_succ_cons, List.countP_cons, hso, ↓reduceIte]
            rw [Array.getElem?_append_right (by simp)]
            simpa using hidx i l hl
      | false =>
        cases s with
        | label x y content color scale align => simp [Gfx.shapeOneEl] at hso
        | ink n =>
          have hnone : GfxSvg.treeOne lab #[] #[] #[] fr acc (Gfx.ofShape (.ink n)) = acc :=
            treeOne_lift_none lab fr acc n hso
          refine ⟨es, ?_, fun i l hl => ?_⟩
          · rw [hcons, hes, hnone]
          · cases i with
            | zero => simp [Gfx.labelOf?] at hl
            | succ i =>
              simp only [List.getElem?_cons_succ] at hl
              simp only [List.take_succ_cons, List.countP_cons, hso]
              simpa using hidx i l hl

private theorem pictureTree_shapes (pic : Ir.Pic.Picture) (box : Ir.Pic.Box)
    (metric : Ir.Pic.LabelMetric) (cfg : Config) :
    pictureTree pic box metric cfg = GfxSvg.treeList (pictureLabelNode metric cfg) #[] #[] #[]
      { iso := some (pictureIso box) } #[] (pic.shapes.toList.map Gfx.ofShape) := by
  simp [pictureTree, GfxSvg.tree, Gfx.ofPictureIn, GfxSvg.bodyEls, Gfx.Figure.bodies]

private theorem pictureLabelNode_unnested (metric : Ir.Pic.LabelMetric) (cfg : Config)
    (fr : GfxSvg.SFrame) (l : Gfx.LabelSpec) :
    MathMl.unnested (pictureLabelNode metric cfg fr l) = true := by
  have hm := labelNodesList_mathFree_contract {} #[] l.content.toList
    (some { cfg with mathStyles := #[] }) rfl
  have ht := labelNodesList_mathFree_contract {} #[] l.content.toList none rfl
  obtain ⟨iso⟩ := fr
  cases iso <;> simp only [pictureLabelNode] <;> split <;>
    simp [Html.elem, MathMl.unnested, MathMl.unnestedList, MathMl.tagFree, MathMl.tagFreeList,
      hm, ht, MathMl.unnestedList_of_mathFree]

private theorem unnested_spellClosed : GfxSvg.SpellClosed MathMl.unnested := by
  intro t ht attrs kids hk
  have hne : (t == "math") = false := by
    simp only [GfxSvg.spellTags, GfxSvg.plainTags, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have hl : ∀ ns : List Node, (∀ k ∈ ns, MathMl.unnested k = true) → MathMl.unnestedList ns = true := by
    intro ns
    induction ns with
    | nil => intro _; rfl
    | cons n rest ih =>
      intro h
      simp only [MathMl.unnestedList, h n (List.mem_cons_self ..), Bool.true_and]
      exact ih fun k hk => h k (List.mem_cons_of_mem _ hk)
  simp only [Html.elem, MathMl.unnested, hne, Bool.false_eq_true, ↓reduceIte]
  exact hl kids.toList fun k hk' => hk k (Array.mem_toList_iff.mp hk')

/-- Artifact-specific. -/
public theorem pictureKids_unnested_contract (pic : Ir.Pic.Picture) (box : Ir.Pic.Box)
    (metric : Ir.Pic.LabelMetric) (cfg : Config) :
    ∀ n ∈ pictureKids pic box metric cfg, MathMl.unnested n = true := by
  obtain ⟨hr, _⟩ := pictureShapes_tree metric cfg box #[] pic.shapes.toList
  unfold pictureKids
  rw [pictureTree_shapes]
  refine GfxSvg.spell_contract MathMl.unnested unnested_spellClosed 0 _ ?_
  rw [hr _ fun l => pictureLabelNode_unnested metric cfg _ l]
  rfl

public theorem pictureLabelBaseline_projects (pic : Ir.Pic.Picture) (box : Ir.Pic.Box)
    (metric : Ir.Pic.LabelMetric) (i : Nat) (x y : Dim.Sp)
    (content : Array Inline) (color : Ir.Color) (scale : Nat) (align : Ir.Pic.LabelAlign)
    (h : pic.shapes[i]? = some (.label x y content color scale align)) (cfg : Config := {}) :
    (match (pictureKids pic box metric cfg)[(pic.shapes.toList.take i).countP Gfx.shapeOneEl]? with
      | some (.elem _ attrs _) => (attrOf? attrs "y", attrOf? attrs "dominant-baseline")
      | _ => (none, none)) =
      (some (box.2.2 - Ir.Pic.labelBaseline y align (metric content scale)).toPtString,
        some "alphabetic") := by
  obtain ⟨_, es, hes, hidx⟩ := pictureShapes_tree metric cfg box #[] pic.shapes.toList
  let l : Gfx.LabelSpec :=
    { x := x, y := y, content := content, color := color, scale := scale, align := align }
  have hl : pic.shapes.toList[i]?.bind Gfx.labelOf? = some l := by
    simp only [Array.getElem?_toList, h, Option.bind_some, Gfx.labelOf?]
    rfl
  have hk : (pictureKids pic box metric cfg)[(pic.shapes.toList.take i).countP Gfx.shapeOneEl]? =
      some (pictureLabelNode metric cfg { iso := some (pictureIso box) } l) := by
    unfold pictureKids
    rw [pictureTree_shapes]
    refine GfxSvg.spell_raw_exact 0 _ _ _ ?_
    rw [hes, Array.empty_append]
    exact hidx i l hl
  rw [hk]
  have hb := pictureLabelNode_baseline box metric cfg l
  revert hb
  generalize pictureLabelNode metric cfg { iso := some (pictureIso box) } l = n
  intro hb
  cases n with
  | elem tag attrs kids => simpa using hb
  | text _ => simp at hb
  | style _ => simp at hb
  | script _ _ => simp at hb

/-- The picture's box as the element's own size: pt in flow classes, a stage share on a deck. -/
public def pictureBox (cfg : Config) (w h : Dim.Sp) (rise : Dim.Sp := 0) : Array (String × String) :=
  #[("viewBox", s!"0 0 {w.toPtString} {h.toPtString}")] ++
    (if cfg.deck then
      #[("style", s!"width: {decMilli (deckStageMilli w cfg.page.width)}vw; \
height: {decMilli (deckStageMilli h cfg.page.height)}dvh" ++
        (if rise == 0 then "" else
          s!"; vertical-align: -{decMilli (deckStageMilli rise cfg.page.height)}dvh"))]
     else
      #[("width", s!"{w.toPtString}pt"), ("height", s!"{h.toPtString}pt")] ++
        (if rise == 0 then #[] else #[("style", s!"vertical-align: -{rise.toPtString}pt")]))

public def pictureSaid (pic : Ir.Pic.Picture) : String := pic.said

/-- What a picture says to a reader: its alternative, else the figure word. -/
public def pictureName (loc : Locale) (pic : Ir.Pic.Picture) : String :=
  firstNonBlank pic.alternative.text (figureWord loc)

public theorem pictureName_contract (loc : Locale) (pic : Ir.Pic.Picture) :
    nonBlank (pictureName loc pic) = true :=
  firstNonBlank_contract _ _ (figureWord_contract loc)

/-- A string's words, one space apart. -/
public def squashSpace (s : String) : String :=
  String.intercalate " "
    (((s.map fun c => if c.isWhitespace then ' ' else c).splitOn " ").filter (!·.isEmpty))

mutual

/-- The words a subtree shows a sighted reader, hidden subtrees, styles and scripts left out. -/
public def shownWordsOne (acc : String) : Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ attrs kids =>
    if attrs.any (fun kv => kv.1 == "hidden" || (kv.1 == "aria-hidden" && kv.2 == "true"))
    then acc
    else shownWordsList acc kids.toList ++ " "

public def shownWordsList (acc : String) : List Node → String
  | [] => acc
  | k :: rest => shownWordsList (shownWordsOne acc k) rest

end

/-- A deck stage's name: its title as its first page shows it, else the words it shows, else
`slide`. -/
public def frameName (title : Array Inline) (kids : Array Node) : String :=
  firstNonBlank (squashSpace (Ir.firstPageText title))
    (firstNonBlank (squashSpace (shownWordsList "" kids.toList)) "slide")

public theorem frameName_contract (title : Array Inline) (kids : Array Node) :
    nonBlank (frameName title kids) = true :=
  firstNonBlank_contract _ _ (firstNonBlank_contract _ _ (by decide))

public def sectionPageName (title : Array Inline) : String :=
  firstNonBlank (squashSpace (Ir.firstPageText title)) "section"

public theorem sectionPageName_contract (title : Array Inline) :
    nonBlank (sectionPageName title) = true :=
  firstNonBlank_contract _ _ (by decide)

/-- A deck stage's keyboard door: a tab stop and a name, so a reader can scroll what spills. -/
public def stageAttrs (deck : Bool) (name : String) : Array (String × String) :=
  if deck then #[("tabindex", "0"), ("aria-label", name)] else #[]

public def pictureRole (loc : Locale) (pic : Ir.Pic.Picture) : Array (String × String) :=
  pictureAltAttrs (figureWord loc) pic.alternative ++ #[("class", "picture")]

public theorem html_picture_name_projects (loc : Locale) (pic : Ir.Pic.Picture) :
    pictureRole loc pic =
      pictureAltAttrs (figureWord loc) pic.alternative ++ #[("class", "picture")] := by rfl

/-- The box a picture's SVG declares: the IR's box under the driver's label measurement. -/
public def pictureBoxOf (cfg : Config) (pic : Ir.Pic.Picture) : Ir.Pic.Box :=
  pic.box cfg.labelMetric

/-- The picture as inline SVG, its declared box a size and never a clip. -/
public def pictureSvg (cfg : Config) (pic : Ir.Pic.Picture) : Node :=
  let ((px0, py0), (px1, py1)) := pictureBoxOf cfg pic
  Html.elem "svg" (pictureKids pic ((px0, py0), (px1, py1)) cfg.labelMetric cfg)
    (pictureBox cfg (px1 - px0) (py1 - py0) (pic.rise cfg.labelMetric) ++
      pictureRole cfg.locale pic ++ #[("overflow", "visible")])

/-- A picture as a standalone SVG document. -/
public def pictureDocument (cfg : Config) (pic : Ir.Pic.Picture) : String :=
  let box := pictureBoxOf cfg pic
  "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++
    Html.render (GfxSvg.documentRoot box false
      (GfxSvg.spell 0 (pictureTree pic box cfg.labelMetric cfg))) 0

public theorem pictureSvg_overflow_contract (cfg : Config) (pic : Ir.Pic.Picture) :
    (Gfx.ofPicture cfg.labelMetric pic).clipToBox = false ∧
    (match pictureSvg cfg pic with
      | .elem _ attrs _ => attrOf? attrs "overflow"
      | _ => none) = some "visible" := by
  refine ⟨rfl, ?_⟩
  rcases h : pic.box cfg.labelMetric with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  rcases ha : pic.alternative with _ | _ | t <;>
    simp [pictureSvg, pictureBoxOf, h, ha, Html.elem, pictureBox, pictureRole, pictureAltAttrs,
      attrOf?] <;>
    split <;> (try split) <;> simp

public theorem pictureViewBox_projects (cfg : Config) (pic : Ir.Pic.Picture) :
    (match pictureSvg cfg pic with
      | .elem _ attrs _ => attrOf? attrs "viewBox"
      | _ => none) =
      (let b := (Gfx.ofPicture cfg.labelMetric pic).box
       some s!"0 0 {(b.2.1 - b.1.1).toPtString} {(b.2.2 - b.1.2).toPtString}") := by
  simp only [Gfx.ofPicture_box_exact]
  rcases h : pic.box cfg.labelMetric with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  simp [pictureSvg, pictureBoxOf, h, Html.elem, pictureBox, attrOf?]

/-- The abstract region's classes: the engine's hook and its body's size step. -/
public def abstractClass (styles : Ir.Styles) : String :=
  let step := Ir.abstractBodySize styles
  "abstract size-" ++ step

/-- The most columns a code line holds whole: a continuation line at WCAG's 320 px reflow width. -/
public def codeHoldColumns : Nat := 23

/-- How many columns a code character takes: two for a wide character or an emoji, else one. -/
private def codeColumns (c : Char) : Nat :=
  let n := c.toNat
  if (Listing.wrapsBetweenChars c && !Listing.wrapsAtWords c &&
      !(0xFF61 ≤ n && n ≤ 0xFFDC) && !(0xFFE8 ≤ n && n ≤ 0xFFEE)) ||
      (0x1F300 ≤ n && n ≤ 0x1F64F) || (0x1F680 ≤ n && n ≤ 0x1F6FF) ||
      (0x1F900 ≤ n && n ≤ 0x1F9FF) || (0x1FA70 ≤ n && n ≤ 0x1FAFF) then 2
  else 1

mutual

/-- `acc` and a node with its text `hole` filled by `fill`. -/
private def fillHoleOne (hole : String) (fill : Array Node) (acc : Array Node) : Node → Array Node
  | .elem tag attrs kids => acc.push (.elem tag attrs (fillHoleList hole fill #[] kids.toList))
  | .text s => if s == hole then acc ++ fill else acc.push (.text s)
  | .style css => acc.push (.style css)
  | .script attrs js => acc.push (.script attrs js)

-- conserves: none — a run's paint around its atoms, every node once
private def fillHoleList (hole : String) (fill : Array Node) (acc : Array Node) :
    List Node → Array Node
  | [] => acc
  | k :: rest => fillHoleList hole fill (fillHoleOne hole fill acc k) rest

end

/-- `nodes` with a text node `t` after them, joined to a text node they end on. -/
private def pushCodeText (nodes : Array Node) (t : String) : Array Node :=
  match nodes.back? with
  | some (.text u) => nodes.pop.push (.text (u ++ t))
  | _ => nodes.push (.text t)

/-- Pieces of code, each a run's characters, after `ps`, a piece of the run
`ps` ends on joined to it. -/
private def joinPieces (ps qs : Array (Nat × String)) : Array (Nat × String) :=
  qs.foldl (fun acc q => match acc.back? with
    | some (ri, t) => if ri == q.1 then acc.pop.push (ri, t ++ q.2) else acc.push q
    | none => acc.push q) ps

/-- A code line's nodes: its highlighter runs painted, and what the line may not break inside
held in `tok` spans. -/
private def codeLineNodes (cfg : Config) (wrap : Ir.ListingWrap) (runs : Array Listing.Run)
    (line : Array ListingHighlight.Token) (classes : Array (Option String) := #[]) :
    Array Node := Id.run do
  let marks := Listing.codeMarks wrap line
  let atomOf (m : Listing.CodeMark) : Nat := match wrap with
    | .units => m.lex
    | .whitespaceFirst => m.fb
  -- the line's atoms in order: their pieces by run, and whether each is white space
  let mut atoms : Array (Nat × Bool × Array (Nat × String)) := #[]
  let mut i := 0
  for (r, ri) in runs.zipIdx do
    for c in r.text.toList do
      let m := marks[i]?.getD { c := c, token := 0, lex := 0, fb := 0, space := false }
      i := i + 1
      let a := atomOf m
      match atoms.back? with
      | some (a', sp, ps) =>
        if a' == a then atoms := atoms.pop.push (a', sp, joinPieces ps #[(ri, String.singleton c)])
        else atoms := atoms.push (a, m.space, #[(ri, String.singleton c)])
      | none => atoms := atoms.push (a, m.space, #[(ri, String.singleton c)])
  let columns (ps : Array (Nat × String)) : Nat :=
    ps.foldl (fun n p => p.2.foldl (fun k c => k + codeColumns c) n) 0
  let fits (ps : Array (Nat × String)) : Bool :=
    2 ≤ ps.foldl (fun n p => n + p.2.length) 0 && columns ps ≤ codeHoldColumns
  -- the units the line emits, in order: white space, and what it holds
  let mut units : Array (Bool × Bool × Array (Nat × String)) := #[]
  match wrap with
  | .units =>
    for (_, sp, ps) in atoms do units := units.push (sp, !sp && fits ps, ps)
  | .whitespaceFirst =>
    let mut stretch : Array (Array (Nat × String)) := #[]
    for (_, sp, ps) in atoms.push (0, true, #[]) do
      if sp then
        let whole := stretch.foldl joinPieces #[]
        if fits whole then units := units.push (false, true, whole)
        else for qs in stretch do units := units.push (false, fits qs, qs)
        stretch := #[]
        unless ps.isEmpty do units := units.push (true, false, ps)
      else stretch := stretch.push ps
  -- a run's paint, once, around what it holds
  let hole := "\uE000\uE001\uE002"
  let paint (ri : Nat) (content : Array Node) : Array Node :=
    match runs[ri]? with
    | some r =>
      let filled := fillHoleList hole content #[] (inlines cfg (Listing.paintRun r #[.text hole])).toList
      match classes[ri]?.join with
      | some cls => #[Html.elem "span" filled #[("class", cls)]]
      | none => filled
    | none => content
  let classesOf (ps : Array (Nat × String)) : String :=
    if columns ps ≤ codeShortColumns then codeTokClass else codeTokClass ++ " " ++ codeLongTokClass
  let held (ps : Array (Nat × String)) (kids : Array Node) : Node :=
    Html.elem "span" kids #[("class", classesOf ps)]
  -- a run that is one held unit takes the classes on its own element
  let flush (ri : Nat) (content : Array Node) : Array Node :=
    match content with
    | #[.elem "span" #[("class", k)] #[.text t]] =>
      if (k.splitOn " ").contains codeTokClass && (runs[ri]?.map (·.text)) == some t then
        match paint ri #[.text t] with
        | #[.elem tag attrs kids] =>
          #[(k.splitOn " ").foldl (fun n c => withClass c n) (.elem tag attrs kids)]
        | _ => paint ri content
      else paint ri content
    | _ => paint ri content
  let mut out : Array Node := #[]
  -- the run being filled, and what it holds so far
  let mut cur : Option (Nat × Array Node) := none
  let mut prevSpace : Option Bool := none
  let mut prevLast : Option Char := none
  for (sp, hold, ps) in units do
    let first := ps[0]?.bind fun (_, t) => t.toList.head?
    let between := (prevLast.any Listing.wrapsBetweenChars) && (first.any Listing.wrapsBetweenChars)
    prevLast := (ps.back?.bind fun (_, t) => t.toList.getLast?).orElse fun _ => prevLast
    let gap := wrap matches .units && prevSpace == some false && !sp && !between
    match ps with
    | #[(ri, t)] =>
      -- inside one run: in that run's paint
      let content := match cur with
        | some (ri', c) => if ri' == ri then c else #[]
        | none => #[]
      if let some (ri', c) := cur then
        if ri' != ri then out := out ++ flush ri' c
      let content := if gap then content.push (Html.elem "wbr" #[] #[]) else content
      let content := if hold then content.push (held ps #[.text t]) else pushCodeText content t
      cur := some (ri, content)
    | _ =>
      -- across runs: each piece in its own run's paint, the unit around them
      if let some (ri', c) := cur then out := out ++ flush ri' c
      cur := none
      if gap then out := out.push (Html.elem "wbr" #[] #[])
      let pieces := ps.foldl (fun acc (ri, t) => acc ++ paint ri #[.text t]) #[]
      out := if hold then out.push (held ps pieces) else out ++ pieces
    prevSpace := some sp
  if let some (ri, c) := cur then out := out ++ flush ri c
  return out

/-- A block set wholly in one named size carries the step's class on its own element. -/
private def stepNode (cfg : Config) (tag : String) (content : Array Inline) : Node :=
  match Ir.paraStep? content with
  | some "normalsize" => Html.elem tag (inlines cfg (Ir.liftParaStep content))
  | some n => Html.elem tag (inlines cfg (Ir.liftParaStep content))
      #[("class", " ".intercalate (stepClasses cfg.deck n))]
  | none => Html.elem tag (inlines cfg content)

/-- A deck's heading or title set in one named size takes that step's leading. -/
private def withLead (cfg : Config) (content : Array Inline) (node : Node)
    (inserted : Bool := false) : Node :=
  if !cfg.deck then node else
  match (if inserted then Ir.insertedStep? cfg.page.scale content else Ir.paraStep? content) with
  | some "normalsize" | none => node
  | some n => withClass ("lead-" ++ n) node

private def paragraphNode (cfg : Config) (content : Array Inline) : Node :=
  -- label anchors alone must not open a blank paragraph
  if !content.isEmpty && content.all (fun x => x matches .label _) then
    Html.elem "span" (inlines cfg content)
  else
  if hasFill content then
    let rows := splitAtBreaks content
    if rows.size == 1 then
      fillRow cfg "p" "entry" content
    else
      Html.elem "p" (rows.map fun row => fillRow cfg "span" "entry-row" row)
        #[("class", "entry-rows")]
  else
    stepNode cfg "p" content

/-- What a listing stands on and sets its plain text in where it declares no ground, in one
scheme. -/
private def listingAround (cfg : Config) (f : Ir.SchemeFrame) (v : Ir.Palette) :
    Option Ir.Color × Ir.Color :=
  let s := f.scheme
  let around := if cfg.listingGround == Ir.Design.declared? cfg.pal .page then
      Ir.Design.declared? v .page
    else if f.home then cfg.listingGround else cfg.listingGround.map f.ground
  let ground := around.getD ((Ir.Design.at v s .page).getD Ir.Color.white)
  let req := Contrast.requiredIn s (Ir.Need.text.atStage f.stage)
  let ink := match cfg.listingFg with
    | some c =>
      if c == Ir.Design.printInk cfg.pal then (Ir.Design.at v s .ink).getD c
      else if f.home then c
      else (Ir.Design.carryInk f.flip req f.homePage f.page ground c).getD (Listing.fitInk req ground c)
    | none => (Ir.Design.at v s .ink).getD Ir.Color.black
  (around, ink)

/-- A listing as one shipped scheme ships it: its ground, its plain text's colour and each code
role's. -/
private def listingPaintIn (cfg : Config) (spec : Ir.ListingSpec) (f : Ir.SchemeFrame)
    (v : Ir.Palette)
    (known : Option (Ir.Color × List (Ir.Role × Option (Ir.Color × Option Ir.Role))) := none) :
    Ir.Color × Ir.Color × List (Ir.Role × Option (Ir.Color × Option Ir.Role)) :=
  let s := f.scheme
  let (around, inherited) := listingAround cfg f v
  let own : Option Ir.Color := if f.home then (spec.groundIn v s).map (·.1)
    else (spec.ground.map fun (g, _) => f.ground g).or (Ir.Design.at v s .codeSurface)
  let page := (Ir.Design.at v s .page).getD Ir.Color.white
  let ground : Ir.Color := (own.or around).getD page
  let req := Contrast.requiredIn s (Ir.Need.text.atStage f.stage)
  let carry (c : Ir.Color) : Ir.Color :=
    (Ir.Design.carryInk f.flip req f.homePage f.page ground c).getD (Listing.fitInk req ground c)
  let fit := if f.home then Listing.defaultInk ground else Listing.fitInk req ground
  -- schemes shipping the palette as declared share one resolution per ground
  let reuse := known.bind fun (g, rs) => if f.home && g == ground then some rs else none
  let roles := match reuse with
    | some rs => rs
    | none =>
    let paints := CodeColor.resolve v ground spec.style
    -- more contrast never lowers a derived colour that already meets the gate
    let homePaints := if f.flip || f.home then none
      else some (CodeColor.resolve cfg.pal ground spec.style)
    let derived (r : ListingHighlight.Role) (c : Ir.Color) : Ir.Color :=
      let again := fit c
      match homePaints.bind (·.get r) with
      | some hp =>
        let h := Listing.defaultInk ground hp.color
        if req ≤ Contrast.contrastMilli h ground &&
            Contrast.contrastMilli again ground ≤ Contrast.contrastMilli h ground then h else again
      | none => again
    ListingHighlight.Role.all.map fun r =>
      (Ir.Role.ofCode r, (paints.get r).map fun p =>
        let c := if !(p.declared || p.styled) then derived r p.color
          else if f.home then p.color
          else if p.styled then carry p.color
          else carry ((p.role.bind (Ir.Design.declared? cfg.pal ·)).getD p.color)
        (c, if p.declared && p.role != some (Ir.Role.ofCode r) then p.role else none))
  let ink := match Ir.Design.declared? cfg.pal .codeInk with
    | some c => if f.home then c else carry c
    | none => if own.isSome then fit inherited else inherited
  (ground, ink, roles)

/-- A listing in every scheme the page ships. -/
private def Config.listingPaints (cfg : Config) (spec : Ir.ListingSpec) :
    List (Ir.Scheme × Ir.Color × Ir.Color × List (Ir.Role × Option (Ir.Color × Option Ir.Role))) :=
  if !cfg.codePaints.isEmpty && spec.ground.isNone && spec.style.isNone &&
      cfg.pal.sameAs cfg.docPal && cfg.listingGround == Ir.Design.declared? cfg.pal .page &&
      cfg.listingFg.all (· == Ir.Design.printInk cfg.pal) then
    cfg.codePaints
  else
    let (out, _) := (cfg.frames.zip cfg.views).foldl (fun (acc :
        Array (Ir.Scheme × Ir.Color × Ir.Color × List (Ir.Role × Option (Ir.Color × Option Ir.Role))) ×
          Option (Ir.Color × List (Ir.Role × Option (Ir.Color × Option Ir.Role)))) (f, v) =>
      let (g, ink, rs) := listingPaintIn cfg spec f v acc.2
      (acc.1.push (f.scheme, g, ink, rs), if f.home && acc.2.isNone then some (g, rs) else acc.2))
      (#[], none)
    out.toList

/-- A listing line's runs, cut where their tokens' classes change, each beside its class. -/
private def tokenRuns (classes : Array (ListingHighlight.Kind × Option String))
    (runs : Array Listing.Run) : Array Listing.Run × Array (Option String) :=
  runs.foldl (fun (out : Array Listing.Run × Array (Option String)) r =>
    let classOf (t : ListingHighlight.Token) : Option String :=
      if r.brush.inkFree t.text then none
      else ((classes.find? (·.1 == t.kind)).bind (·.2))
    let segs := r.tokens.foldl (fun (segs : Array (Option String × Array ListingHighlight.Token)) t =>
      let c := classOf t
      match segs.back? with
      | some (c', ts) =>
        if c == c' || (c.isNone && r.brush.inkFree t.text) then segs.pop.push (c', ts.push t)
        else segs.push (c, #[t])
      | none => segs.push (c, #[t])) #[]
    segs.foldl (fun (out : Array Listing.Run × Array (Option String)) (c, ts) =>
      (out.1.push { brush := { r.brush with ink := none }, inked := false, tokens := ts },
       out.2.push c)) out) (#[], #[])

/-- The colours a listing's box states in every scheme the page ships, where they differ from what
surrounds it. -/
private def Config.listingStyle (cfg : Config) (spec : Ir.ListingSpec)
    (paints : List (Ir.Scheme × Ir.Color × Ir.Color ×
      List (Ir.Role × Option (Ir.Color × Option Ir.Role)))) : String :=
  let roleTexts (r : Ir.Role) : List (Ir.Scheme × Option String) :=
    (cfg.boxTexts.lookup r).getD []
  let value (t : List (Ir.Scheme × Option String)) (rs : List Ir.Role) : String :=
    match rs.find? (fun r => roleTexts r == t) with
    | some r => roleRef r
    | none => schemeValue t t cfg.floor
  let ground := paints.map fun (sc, g, _, _) => (sc, some (cssColor g))
  let ink := paints.map fun (sc, _, i, _) => (sc, some (cssColor i))
  let classGround := (Ir.Design.at cfg.docPal .light .codeSurface).isSome
  let inked := (Ir.Design.declared? cfg.pal .codeInk).isSome
  let decls : List String :=
    if spec.highlight.isEmpty then
      match spec.ground with
      | some _ => [s!"background: {value ground []};", s!"color: {value ink []};"]
      | none =>
        let epochGround := !classGround && (spec.groundIn cfg.pal .light).isSome
        (if epochGround then [s!"background: {roleRef .codeSurface};"] else []) ++
          (if inked then [s!"color: {value ink [.ink]};"] else [])
    else
      let bg := if spec.ground.isNone && classGround && ground == roleTexts .codeSurface then []
        else [s!"background: {value ground [.page, .codeSurface]};"]
      let used := (spec.highlight.foldl (fun acc line => line.foldl (fun acc t =>
        if acc.contains t.kind then acc else acc.push t.kind) acc) #[]).map (·.role)
      -- the code roles are `:root`'s only outside an epoch and a painted body
      let atRoot := cfg.bodyGround.isNone && cfg.pal.sameAs cfg.docPal
      let roles := ListingHighlight.Role.all.filterMap fun r =>
        let key := Ir.Role.ofCode r
        if r == .ink || !used.contains r then none else
        let t := paints.map fun (sc, _, _, rs) => (sc, ((rs.lookup key).join).map (cssColor ·.1))
        let root := paints.map fun (sc, _) =>
          (sc, ((((cfg.codeRoot.lookup sc).getD []).lookup key).join).map (cssColor ·.1))
        if atRoot && t == root then none else some s!"{roleVar key}: {schemeValue t t cfg.floor};"
      bg ++ [s!"color: {value ink [.ink]};"] ++ roles
  " ".intercalate decls

mutual

public def blockNode (cfg : Config) (b : Block) : Node :=
  let cfg := match b.listScope cfg.lists cfg.styles with
    | .onList => cfg
    | .box | .aside => { cfg with fillsInert := true }
  match b with
  | .para content => paragraphNode cfg content
  | .section level _ num title =>
    let element := level.element
    let tag := headingTag level
    let st := (cfg.styles.find? element).getD {}
    let st := if level == 0 then Ir.titleHeadingStyle st else st
    let title := match st.font, cfg.slotTitle && level == 0 with
      | some tpl, false => fillTemplate tpl title
      | _, _ => title
    -- the number is its own span, so the anchor slug reads the title alone
    let kids := inlines cfg title
    let kids := match num with
      | some n => #[Html.elem "span" #[Html.text n]
          #[("class", "section-number")], Html.text "\u2003"] ++ kids
      | none => kids
    let attrs := if st.rule.isSome then #[("class", "ruled")] else #[]
    -- a deck's section heading outside a frame takes the section title's ink where declared
    let attrs := if cfg.deck && level == 1 &&
        ((Ir.Design.declared? cfg.pal .sectionTitleInk).isSome ||
          (Ir.Design.declared? cfg.pal .ink).isSome) then
      attrs.push ("style", s!"color: {roleRef .sectionTitleInk}") else attrs
    let node := withLead cfg title (Html.elem tag kids attrs)
    if level == .h1 then withClass "body-heading" node else node
  | .list ordered items =>
    let desc := Ir.listIsDesc ordered items
    let n := Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b
    if desc then
      fillCarrier cfg n (Html.elem "dl" (descItemsInto (cfg.deeper false).into #[] items.toList))
    else
    let tag := if ordered then "ol" else "ul"
    fillCarrier cfg n (Html.elem tag (listItemsInto (cfg.deeper false).into #[] items.toList))
  | .center body =>
    match Ir.displayContent? body with
    | some content => Html.elem "p" (inlines cfg content) #[("class", "display")]
    | none =>
      fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
        (Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", "centered")])
  -- flush left is still a class, so it survives a centred ancestor
  | .ragged flush body =>
    fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
      (Html.elem "div" (blockNodesInto cfg.into #[] body.toList) #[("class", raggedClass flush)])
  -- spacing-only roles are a class on the environment's own element, never an element of their own
  | .role n body =>
    if let some (anchors, pic) := Ir.displayPicture? (.role n body) then
      Html.elem "p" ((inlines cfg anchors).push (pictureSvg cfg pic))
        #[("class", "display")]
    else
    -- a title slot's content sets under the slot's template alone
    let cfg := if (Ir.titleSlotOf ((cfg.styles.find? "titlepage").getD {}).slots n).isSome
      then { cfg with slotTitle := true } else cfg
    let kids := blockNodesInto cfg.into #[] body.toList
    -- a page-model mark has no meaning in a continuous medium
    if Ir.pageMarkerRole n then Html.text "" else
    match n == Ir.trivlistRole || n == Ir.inParagraphRole || (Ir.thmSpaceOf? n).isSome,
        kids.toList with
    | true, [k] => withClass (roleClass n) k
    | false, [k] =>
      if (Ir.DisplayCtx.ofRole? n).isSome then k
      else fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
        (Html.elem "div" kids #[("class", roleClass n)])
    | _, _ =>
      fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
        (Html.elem "div" kids #[("class", roleClass n)])
  -- an anchor's content model is transparent; elaboration refuses nested anchors
  | .link target body =>
    fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
      (Html.elem "a" (blockNodesInto cfg.into #[] body.toList)
        #[("href", target), ("style", "display: block")])
  | .quote body =>
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "blockquote" (blockNodesInto (cfg.deeper true).into #[] body.toList))
  | .disclosure summary expanded body =>
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "details"
        (#[Html.elem "summary" (inlines cfg summary)] ++ blockNodesInto cfg.into #[] body.toList)
        (if expanded then #[("open", "")] else #[]))
  -- an untitled block keeps its empty header, as beamer keeps the box
  | .titled kind title body =>
    let d := Design.ofPalette cfg.pal
    let look := d.titledBody kind
    let inherited := cfg.bodyInk.getD (.role .ink, cfg.listingFg.getD d.fg)
    let parent : Ir.ColorPair :=
      { fg := inherited.2, bg := cfg.listingGround.getD d.bg }
    let paint := titledBodyPaint cfg.pal kind parent
    let role := if look.fg.isSome then .role (Ir.Role.bodyInk kind) else inherited.1
    let titleLook := Ir.titledLook cfg.pal kind
    let read (r : Ir.Role) (c : Ir.Color) : String := colorRead cfg (some (.role r)) c
    let barStyle := (titleLook.bar.map fun c =>
      s!"background: {read (Ir.Role.titleBar kind) c}; {titledBoxPaint}").getD ""
    let titleStyle := s!"color: {read (Ir.Role.titleInk kind) titleLook.fg};" ++ barStyle
    let shown := match Ir.blockTitleFont cfg.styles kind with
      | some tpl => Ir.fillTemplate tpl title
      | none => title
    let head : Array Html.Node :=
      if title.isEmpty then
        #[Html.elem "header" #[] #[("style", if barStyle.isEmpty then "min-height: 1lh;" else barStyle)]]
      else #[Html.elem "header" (inlines cfg shown) #[("style", titleStyle)]]
    let bodyCfg := { cfg.into with
      listingFg := some paint.fg, listingGround := look.bg.or cfg.listingGround
      bodyGround := look.bg.or cfg.bodyGround
      bodyInk := some (role, (look.resolve parent).fg) }
    let kids := blockNodesInto bodyCfg #[] body.toList
    let bodyStyle := s!"color: {colorRead cfg (some role) paint.fg};"
    if kind == .box then
      let barStyle := (titleLook.bar.map fun c =>
        s!"background: {read (Ir.Role.titleBar kind) c};").getD ""
      let head : Array Html.Node := if title.isEmpty then #[] else
        #[Html.elem "header" (inlines cfg title)
          #[("style", s!"color: {read (Ir.Role.titleInk kind) titleLook.fg};" ++ barStyle)]]
      let bodyPaint := (look.bg.map fun bg =>
        s!"background: {read (Ir.Role.bodyGround kind) bg};").getD ""
      Html.elem "section" (head.push (Html.elem "div" kids
          #[("class", "tcolorbox-body"), ("style", bodyStyle ++ bodyPaint)]))
        #[("class", "tcolorbox")]
    else
    match Ir.blockShapeOf cfg.styles kind with
    | some shape =>
      let showTitle := shape.showsTitle (!title.isEmpty)
      let titleInk := titleLook.fg
      let head : Array Html.Node :=
        if !showTitle then #[]
        else if title.isEmpty then #[Html.elem "header" #[] #[]]
        else #[Html.elem "header" (inlines cfg shown)
          #[("style", s!"color: {read (Ir.Role.titleInk kind) titleInk};")]]
      let ink := look.fg.getD inherited.2
      let shapedCfg := { cfg.into with
        listingFg := some ink, bodyInk := some (role, look.fg.getD inherited.2) }
      -- each section states its own body's end, so none reads an enclosing section's
      let lastBelow : String :=
        match shape.edges.find? fun e => e.span == .whole && e.besideTitle with
        | none => ""
        | some e =>
          let para := ((cfg.blockTitleRule kind e.reach).map fun p => stageLength cfg p.bodyBelow).getD
            "0rem"
          s!" --block-last-below: {endBelowList cfg para body.toList};"
      fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
        (Html.elem "section" (head ++ blockNodesInto shapedCfg #[] body.toList)
          #[("class", s!"block block-{kind.name} block-shaped"),
            ("style", s!"color: {cfg.literal ink};" ++ lastBelow)])
    | none =>
    let kids := match look.bg with
      | some bg => #[Html.elem "div" kids #[("class", "block-body"), ("style",
          bodyStyle ++ s!"background: {read (Ir.Role.bodyGround kind) bg}; {titledBodyBoxPaint}")]]
      | none => kids
    let attrs := #[("class", s!"block block-{kind.name}")]
    let attrs := if look.bg.isNone && look.fg.isSome then attrs.push ("style", bodyStyle) else attrs
    Html.elem "section" (head ++ kids) attrs
  | .equation num content =>
    let kids := inlines cfg content
    Html.elem "div"
      (kids.push (Html.elem "span" (inlines cfg num) #[("class", "eqnum")]))
      #[("class", "equation display")]
  | .abstract body =>
    -- an `<h2>`, so a declared `\style{section}` reaches the abstract's heading
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "section"
        (#[Html.elem "h2" #[Html.text cfg.locale.abstract] #[("style", "text-align: center")]] ++
          blockNodesInto cfg.into #[] body.toList)
        #[("class", abstractClass cfg.styles)])
  | .columns cols =>
    let justify := if cols.size == 1 then "var(--ltx-box-justify, start)" else "space-between"
    let total := cfg.measureValues.lineWidth
    let declared := cols.foldl (fun s c => s + (c.1.resolve total).getD 0) 0
    let unspecified := cols.foldl (fun n c => if c.1.declared then n else n + 1) 0
    let share := if unspecified > 0 then max 0 (total - declared) / unspecified else 0
    Html.elem "div" (columnNodesInto cfg.into total share #[] cols.toList)
      #[("class", "columns"),
        ("style", s!"display: grid; grid-template-columns: {gridTracks cols}; " ++
          s!"justify-content: {justify}")]
  | .onSteps spec body =>
    fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
      (overlayNode "div" cfg.overlaySteps spec (blockNodesInto cfg.into #[] body.toList))
  | .altSteps spec firstPage otherPage =>
    -- a group's fills grow nothing: the stage's flex column is shared by every step
    let first := blockNodesInto { cfg.into with fillsInert := true } #[] firstPage.toList
    let other := blockNodesInto { cfg.into with fillsInert := true } #[] otherPage.toList
    Html.elem "div" (overlayAlternatives "div" cfg.overlaySteps spec first other)
      #[("class", if altEndsAlike first other then "alt-pair alt-alike" else "alt-pair")]
  | .note body =>
    -- hidden: for a speaker view, invisible in the deck and in print
    Html.elem "aside" (blockNodesInto cfg.into #[] body.toList)
      #[("class", "note"), ("hidden", "hidden")]
  | .pagebreak =>
    Html.text ""
  | .spaced before body =>
    let grows := cfg.deck && !cfg.fillsInert && before.value.fil
    if body.isEmpty then
      skipNode cfg.page.fontSize before (if grows then some Ir.fillUnit else none)
    else
    let style := s!"margin-top: {if cfg.deck then deckSourced cfg.page.height before
      else cssSourced before}"
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
        #[("class", if grows then "spaced fill-before" else "spaced"), ("style", style)])
  | .verbatim covered s spec =>
    let lines := spec.tokenLines s
    let own := spec.groundIn cfg.pal .light
    let ground := (own.map (·.1)).or cfg.listingGround
    let brushes := Listing.brushes cfg.pal ground covered spec.style lines
    let paints := if cfg.frames.isEmpty || covered.isSome then [] else cfg.listingPaints spec
    let colored (r : ListingHighlight.Role) : Bool :=
      paints.any fun (_, _, _, rs) => ((rs.lookup (Ir.Role.ofCode r)).join).isSome
    let classes := brushes.map fun (k, _) =>
      (k, if k.role != .ink && colored k.role then some (tokenClass k) else none)
    let codeAttrs : Array (String × String) := match spec.htmlClass with
      | some c => #[("class", c)]
      | none => #[]
    let codeKids := Id.run do
      let mut kids := #[]
      for i in [:lines.size] do
        if i > 0 then kids := kids.push (Html.text "\n")
        let runs := Listing.paintLine cfg.pal ground covered spec.style brushes lines[i]!
        let line := if paints.isEmpty then codeLineNodes cfg spec.wrapAt runs lines[i]!
          else
            let (parts, partClasses) := tokenRuns classes runs
            codeLineNodes cfg spec.wrapAt parts lines[i]! partClasses
        kids := if spec.numbers then
          kids.push (Html.elem "span" line #[("class", "line")])
          else kids ++ line
      return kids
    let code := Html.elem "code" codeKids codeAttrs
    let design := Ir.Design.ofPalette cfg.pal
    let paint := if !paints.isEmpty then cfg.listingStyle spec paints else
      match spec.ground, own with
      | some (g, ref), _ =>
        s!"background: {colorRead cfg ref g}; " ++
        s!"color: {cssColor (covered.getD
          (Listing.groundInk cfg.pal g (cfg.listingFg.getD design.fg)))};"
      | none, some (g, _) =>
        -- plain verbatim reads the code ground's role; a highlighted listing states its ground
        if spec.highlight.isEmpty then
          let ground := if (Design.at cfg.docPal .light .codeSurface).isSome then none
            else some s!"background: {roleRef .codeSurface};"
          " ".intercalate (ground.toList ++ (covered.map fun c => s!"color: {cssColor c};").toList)
        else
          s!"background: {cssColor g}; " ++
          s!"color: {cssColor (covered.getD
            (Listing.groundInk cfg.pal g (cfg.listingFg.getD design.fg)))};"
      | none, none =>
        if spec.highlight.isEmpty then
          (covered.map fun c => s!"color: {cssColor c};").getD ""
        else
          s!"background: {cssColor (cfg.listingGround.getD design.bg)}; " ++
          s!"color: {cssColor (covered.getD (cfg.listingFg.getD design.fg))};"
    let style := String.intercalate " "
      (((fontStyleDecls cfg.page.scale spec.fontSize (fontLengthCss cfg)).getD #[]).toList) ++
      (match spec.fontSize with
        | .fontSize .. => ""
        | .size n => s!" line-height: {listingLineHeight cfg.page spec n};"
        | _ => s!" line-height: {decMilli (printLeadingMilli cfg.page)};") ++
      s!" tab-size: {spec.tabSize};" ++
      (if spec.breakLines then " white-space: pre-wrap; overflow-wrap: break-word;" else "") ++
      -- a wrapped line's continuation hangs `breakIndent` in (`hanging each-line`)
      (match spec.breakIndent with
        | some w =>
          if spec.breakLines then s!" text-indent: {cssLength (.ofSp w)} hanging each-line;"
          else ""
        | none => "") ++
      (if paint.isEmpty then "" else " " ++ paint)
    let pre := Html.elem "pre" #[code]
      ((if spec.numbers then #[("class", "numbered")] else #[]) ++
       #[("style", style)] ++
       -- a code block scrolls sideways, so it is a tab stop (WCAG 2.2 SC 2.1.1)
       #[("tabindex", "0")])
    let node := match spec.caption with
      | some (n, cap) =>
        Html.elem "figure"
          #[Html.elem "figcaption" (inlines cfg (Ir.listingCaption cfg.locale n cap)),
            pre]
          #[("class", "listing")]
      | none => pre
    match spec.frame with
    | .trivlist => withClass (roleClass Ir.trivlistRole) node
    | .list => withClass verbatimListClass node
    | .none => node
  | .algorithm numbered semis lines =>
    let words := Ir.algWords cfg.locale.tag
    let muted := Ir.mutedOf cfg.pal
    Html.elem "ol"
      (algRenderList (fun l => inlines cfg (Ir.AlgLine.rendered words semis muted l))
        #[] (algNest lines).toList)
      #[("class", if numbered then "algorithm numbered" else "algorithm")]
  | .rule color name thickness =>
    let c := colorRead cfg name color
    Html.elem "hr" #[] #[("class", "separator"),
      ("style", s!"border: none; height: {cssSourced thickness}; background: {c}")]
  | .frame title standout valign breakable body =>
    let cfg := cfg.inFrame b
    let header := if title.isEmpty then #[]
      else #[Html.elem "header" #[withLead cfg title (Html.elem "h2" (inlines cfg title))
        (inserted := true)]]
    let design := Ir.Design.ofPalette cfg.pal
    let cls := if standout then "slide standout"
      else if valign matches .golden then "slide title-page"
      else if design.frametitle.isSome && !title.isEmpty then "slide titlebar" else "slide"
    let cls := if Ir.frameSqueeze body != .none then cls ++ " squeeze" else cls
    let listingFg := if standout then some design.standout.fg
      else if valign matches .golden then design.titlepage.map (·.fg) else none
    let bodyCfg := { cfg.into with
      listingGround := Ir.frameGroundOf cfg.pal standout valign, listingFg }
    let kids := blockNodesInto bodyCfg #[] body.toList
    let hasTitle := !standout && !title.isEmpty
    let opening := frameOpensBody cfg.chromeAllowed hasTitle valign
    let kids := if opening then frameBodyStart kids else kids
    let (kids, endsOnCarrier) := if cfg.deck && !(valign matches .golden)
      then frameFlowEnd (frameBodyEnd kids) else (kids, false)
    let openingAttrs := if opening then
        let length := if cfg.deck then
            s!"{decMilli (frameBodySkipMilli hasTitle valign cfg.page.fontSize cfg.page.height)}vh"
          else cssLength (Length.ofSp ((Ir.frameBodySkip hasTitle valign).resolve cfg.page.fontSize 0))
        #[("style", s!"--frame-body-skip: {length}")]
      else #[]
    let kids := if cfg.deck then
        let (above, below) :=
          deckSpacerShares (Ir.frameKeysOf cfg.frameKeys standout) breakable valign
            (Ir.frameFills cfg.lists cfg.styles .deck body)
        let spacer (n : Nat) (cls : String) : Array Html.Node :=
          if n == 0 then #[] else
            #[Html.elem "div" #[] #[("class", cls), ("style", s!"flex-grow: {n}")]]
        let up := spacer above "fill"
        let down := spacer below (if endsOnCarrier then "fill frame-body-tail" else "fill")
        up ++ kids ++ down
      else kids
    Html.elem "section" (header ++ kids)
      (#[("class", cls)] ++ stageAttrs cfg.deck (frameName title kids) ++ openingAttrs)
  | .framefoot _ =>
    -- a state change, not content
    Html.text ""
  | .setPalette _ =>
    -- a state change the sibling walks replay
    Html.text ""
  | .setTokens _ =>
    Html.text ""
  | .only targets body =>
    -- `emit` already kept this node for HTML, so it is a transparent group
    fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck body)
      (Html.elem "div" (blockNodesInto cfg.into #[] body.toList)
        #[("data-backend", String.intercalate "," targets.toList)])
  | .nav spec body =>
    let labelAttrs : Array (String × String) :=
      match spec.label with
      | some l => #[("aria-label", l)]
      | none => #[]
    let pinAttrs : Array (String × String) :=
      match spec.pin with
      | some pin =>
        let v := if pin.top then "top" else "bottom"
        let h := if pin.left then "left" else "right"
        let off := cssLength pin.offset.width
        let style := s!"position: fixed; {v}: {off}; {h}: {off}" ++
          (match pin.revealBy with
           | some g => s!"; --reveal-range: {cssLength g.width}"
           | none => "")
        (if pin.reveal then #[("class", "reveal-scroll")] else #[]).push
          ("style", style)
      | none => #[]
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "nav" (blockNodesInto cfg.into #[] body.toList) (labelAttrs ++ pinAttrs))
  | .logo _ =>
    -- a state change the deck's top-level walk reads
    Html.text ""
  | .picture pic => pictureSvg cfg pic
  | .table cols padL padR rows rules spans => tableNode cfg cols padL padR rows rules spans
  | .float kind num capAbove body caption =>
    let capNode : Array Node :=
      if caption.isEmpty then #[]
      else #[Html.elem "figcaption"
        (inlines cfg (Ir.numberedCaption cfg.locale kind num caption))]
    let kids := blockNodesInto cfg.into #[] body.toList
    let kindCls := floatKindClass kind
    let cls := if kind == .figure then "float" else "float " ++ kindCls
    fillCarrier cfg (Ir.frameFillsOne cfg.lists cfg.styles .deck 0 b)
      (Html.elem "figure" (if capAbove then capNode ++ kids else kids ++ capNode)
        #[("class", cls)])
  | .bibliography _ _ items =>
    let marked := items.any (·.marker.isSome)
    -- WebKit drops list semantics from a list styled without markers, hence the explicit role
    Html.elem "ul" (items.map (bibItemNode cfg))
      #[("class", if marked then "bibliography" else "bibliography unmarked"),
        ("role", "list")]

/-- Blocks, pushed onto `acc`, each sibling carrying the epoch in force. -/
private def blockNodesInto (cfg : Config) (acc : Array Node) : List Block → Array Node
  | [] => acc
  | .logo _ :: rest => blockNodesInto cfg acc rest
  | .setPalette p :: rest =>
    blockNodesInto (cfg.advancePalette p) acc rest
  | .setTokens tk :: rest =>
    blockNodesInto (cfg.advanceTokens tk) acc rest
  | b :: rest =>
    if Ir.pageMarkerBlock b then blockNodesInto cfg acc rest
    else blockNodesInto (cfg.afterBlock b)
      (acc.push (cfg.applyEpoch (blockNode cfg b))) rest

private def columnNodesInto (cfg : Config) (total share : Sp) (acc : Array Node) :
    List (BoxWidth × Array Block) → Array Node
  | [] => acc
  | (w, body) :: rest =>
    let align := match w.pos with
      | .top => ""
      | .first => "align-self: baseline"
      | .center => "align-self: center"
      | .last => "align-self: last baseline"
    -- every box is the query container its content's `cqi` reads
    let style := if align.isEmpty then "container-type: inline-size"
      else "container-type: inline-size; " ++ align
    let child := cfg.atMeasure ((w.resolve total).getD share)
    columnNodesInto cfg total share
      (acc.push (Html.elem "div" (blockNodesInto child #[] body.toList)
        #[("class", "column"), ("style", style)])) rest

private def listItemsInto (cfg : Config) (acc : Array Node) : List (Array Block) → Array Node
  | [] => acc
  | item :: rest =>
    listItemsInto (cfg.afterBlocks item)
      (acc.push (fillCarrier cfg (Ir.itemTrailingFills item)
        (listItem { cfg with fillsInert := true } "li" item.toList) (item := true)))
      rest

/-- A description list's items: each label a `<dt>`, the text after it and further blocks a
`<dd>`. -/
private def descItemsInto (cfg : Config) (acc : Array Node) : List (Array Block) → Array Node
  | [] => acc
  | ⟨Block.para c :: bs⟩ :: rest =>
    let (label, after) := (Ir.descLabel? c).getD (#[], c)
    let body := if bs.isEmpty then inlines cfg after
      else blockNodesInto cfg.into #[paragraphNode cfg.into after] bs
    descItemsInto (cfg.afterBlocks bs.toArray)
      ((acc.push (cfg.applyEpoch (Html.elem "dt" (inlines cfg label)))).push
        (cfg.applyEpoch (fillCarrier cfg
          (Ir.frameFillsList cfg.lists cfg.styles .deck 0 bs) (Html.elem "dd" body)))) rest
  | item :: rest =>
    descItemsInto (cfg.afterBlocks item)
      ((acc.push (Html.elem "dt" #[])).push
        (fillCarrier cfg (Ir.frameFills cfg.lists cfg.styles .deck item)
          (listItem cfg "dd" item.toList)))
      rest

-- a one-paragraph item keeps its epoch on the `li` or `dd` it elides the `p` into
private def listItem (cfg : Config) (tag : String) : List Block → Node
  | [.para content] => cfg.applyEpoch (stepNode cfg tag content)
  | [] => cfg.applyEpoch (Html.elem tag #[])
  | .logo _ :: rest => listItem cfg tag rest
  | .setPalette p :: rest =>
    listItem (cfg.advancePalette p) tag rest
  | .setTokens tk :: rest =>
    listItem (cfg.advanceTokens tk) tag rest
  | b :: rest =>
    if Ir.pageMarkerBlock b then listItem cfg tag rest
    else
      let child := cfg.into
      cfg.applyEpoch (Html.elem tag
        (blockNodesInto (child.afterBlock b)
          #[child.applyEpoch (blockNode child b)] rest))

end

private theorem pageOpening_projects (cfg : Config) (acc : Array Node)
    (n : String) (opening : Ir.PageOpening) (rest : List Block)
    (h : Ir.pageOpeningOfRole? n = some opening) :
    blockNodesInto cfg acc (.role n #[] :: rest) = blockNodesInto cfg acc rest := by
  simp only [blockNodesInto, Ir.pageMarkerBlock, Array.isEmpty_empty,
    Ir.pageOpening_marker_exact n opening h, Bool.true_and, ite_true]

/-- Facts of the emitted tree the landmark and anchor checks judge, collected in one walk. -/
private structure PageFacts where
  /-- DOM anchors with the canonical snap that contains them, when any. -/
  ids : Array (String × Option String) := #[]
  fragmentRefs : Array String := #[]
  /-- Canonical labels read by the deck's script, in snap order. -/
  slideLabels : Array String := #[]
  deck : Bool := false
  /-- Unlabeled `<nav>` landmarks, which count toward W0325. -/
  navs : Nat := 0
  /-- Elements carrying the `reveal-scroll` class. -/
  reveals : Nat := 0

mutual

private def pageFactsOne (stage : Option String) (acc : PageFacts) : Node → PageFacts
  | .text _ => acc
  | .style _ => acc
  | .script _ text => { acc with deck := acc.deck || text == deckScript }
  | .elem tag attrs kids =>
    let stage := (attrOf? attrs "data-slide-label").orElse (fun _ => stage)
    let acc := if attrs.any (·.1 == "data-snap") then
        { acc with slideLabels := acc.slideLabels ++ stage.toArray } else acc
    let acc := if tag == "nav" && attrs.all (·.1 != "aria-label") then
        { acc with navs := acc.navs + 1 } else acc
    let acc := if attrs.any (fun kv => kv.1 == "class" && kv.2 == "reveal-scroll") then
        { acc with reveals := acc.reveals + 1 } else acc
    let acc := attrs.foldl (init := acc) fun a kv =>
      if kv.1 == "id" then { a with ids := a.ids.push (kv.2, stage) }
      else if kv.1 == "href" && kv.2.startsWith "#" then
        { a with fragmentRefs := a.fragmentRefs.push kv.2 }
      else a
    pageFactsList stage acc kids.toList

private def pageFactsList (stage : Option String) (acc : PageFacts) : List Node → PageFacts
  | [] => acc
  | k :: rest => pageFactsList stage (pageFactsOne stage acc k) rest

end

/-- Whether an `svg`'s children close with a figure's definitions. -/
private def definesFigure (kids : Array Node) : Bool :=
  match (kids.back? : Option Node) with
  | some (Node.elem tag _ _) => tag == "defs"
  | some (Node.text _) => false
  | some (Node.style _) => false
  | some (Node.script _ _) => false
  | none => false

mutual

-- conserves: none — a renaming of figure ids
/-- Every figure that names an id numbered apart, in document order. -/
private def numberFiguresOne (n : Nat) : Node → Node × Nat
  | .elem tag attrs kids =>
    if tag == "svg" && definesFigure kids then
      (.elem tag attrs (GfxSvg.renumberList n #[] kids.toList), n + 1)
    else
      let r := numberFiguresList n #[] kids.toList
      (.elem tag attrs r.1, r.2)
  | .text s => (.text s, n)
  | .style s => (.style s, n)
  | .script a s => (.script a s, n)

private def numberFiguresList (n : Nat) (acc : Array Node) : List Node → Array Node × Nat
  | [] => (acc, n)
  | x :: rest =>
    let r := numberFiguresOne n x
    numberFiguresList r.2 (acc.push r.1) rest

end

/-- A page's figures numbered apart, so no two share an id. -/
public def numberFigures (body : Array Node) : Array Node := (numberFiguresList 0 #[] body.toList).1

/-- The first free anchor among `taken` (`base`, `base-2`, …), and the holder's title when a
different title collides. -/
private def claimId (taken : Std.HashMap String String) (base text : String) :
    String × Option String := Id.run do
  let mut id := base
  let mut clash : Option String := none
  for n in [2 : taken.size + 3] do
    match taken[id]? with
    | some holder =>
      if holder != text && clash.isNone then
        clash := some holder
      id := s!"{base}-{n}"
    | none => break
  return (id, clash)

/-- The first stage name no earlier stage carries: `name`, then `name (2)`, `name (3)`, and so
on. -/
private def claimName (taken : Std.HashSet String) (name : String) : String := Id.run do
  let mut out := name
  for n in [2 : taken.size + 3] do
    if taken.contains out then out := s!"{name} ({n})" else break
  return out

/-- A stage with its accessible name claimed against the earlier stages' names. -/
private def claimStageName (taken : Std.HashSet String) : Node → Node × Std.HashSet String
  | .elem tag attrs kids =>
    match attrOf? attrs "aria-label" with
    | some name =>
      let got := claimName taken name
      (.elem tag (attrs.map fun kv => if kv.1 == "aria-label" then (kv.1, got) else kv) kids,
        taken.insert got)
    | none => (.elem tag attrs kids, taken)
  | .text s => (.text s, taken)
  | .style s => (.style s, taken)
  | .script attrs s => (.script attrs s, taken)

/-- The snap spacers of a stepped frame's track, one per overlay step, each claiming its aliases. -/
private def snapWalk (id text label : String) (kids : Array Node)
    (taken : Std.HashMap String String) (diags : Array Diag) :
    List Nat → Array Node × Std.HashMap String String × Array Diag
  | [] => (kids, taken, diags)
  | k :: rest =>
    let (sid, sclash) := claimId taken s!"{id}-{k}" text
    let diags := match sclash with
      | some holder => diags.push (Diag.of .W0327
          s!"frames share the step anchor '{id}-{k}'; each after the first takes a \
numbered anchor"
          (help := some s!"an in-page link '#{id}-{k}' reaches only the first; \
retitle the frames apart, or link to the numbered anchor")
          (detail := some s!"{text.quote} takes '{sid}', after {holder.quote}"))
      | none => diags
    snapWalk id text label
      (kids.push (Html.elem "div" #[]
        #[("class", "snap"), ("id", sid), ("data-snap", ""),
          ("data-slide-label", s!"{label}.{k}")]))
      (taken.insert sid text) diags rest

private def stepList (steps : Nat) : List Nat :=
  (List.range steps).map (· + 1)

@[simp] private theorem stepList_length (steps : Nat) :
    (stepList steps).length = steps := by
  simp [stepList]

private theorem snapWalk_count (id text label : String) :
    ∀ (ks : List Nat) (kids : Array Node) (taken : Std.HashMap String String)
      (diags : Array Diag),
      (snapWalk id text label kids taken diags ks).1.size = kids.size + ks.length
  | [], _, _, _ => rfl
  | k :: rest, kids, taken, diags => by
    unfold snapWalk
    rw [snapWalk_count id text label rest]
    simp only [Array.size_push, List.length_cons]
    omega

private theorem track_snaps_exact (id text label : String)
    (taken : Std.HashMap String String) (diags : Array Diag)
    (frame : Ir.Block) :
    (snapWalk id text label #[] taken diags
        (stepList (Ir.frameSteps frame))).1.size
      = Ir.frameSteps frame := by
  rw [snapWalk_count, stepList_length]
  simp

/-- An article's top-level sections as `<section id>` containers; colliding slugs are named
W0327. -/
private def sectionize (cfg : Config) (blocks : Array Block) :
    Array Node × Array Diag := Id.run do
  let close (out cur : Array Node) : Option String → Array Node
    | some id => out.push (Html.elem "section" cur #[("id", id)])
    | none => out ++ cur
  let mut out : Array Node := #[]
  let mut cur : Array Node := #[]
  let mut openId : Option String := none
  -- each assigned id with the plain text of the title that holds it
  let mut taken : Std.HashMap String String := {}
  let mut diags : Array Diag := #[]
  let mut cfg := cfg
  for b in blocks do
    match b with
    | .setPalette p =>
      cfg := cfg.advancePalette p
    | .setTokens tk =>
      cfg := cfg.advanceTokens tk
    | .section 1 _ _ title =>
      out := close out cur openId
      let text := Ir.firstPageText title
      let base := slug title
      let base := if base.isEmpty then "section" else base
      let (id, clash) := claimId taken base text
      if let some holder := clash then
        diags := diags.push (Diag.of .W0327
          s!"sections share the anchor '{base}'; each after the first takes a numbered anchor"
          (help := some s!"an in-page link '#{base}' reaches only the first; \
retitle the sections apart, or link to the numbered anchor")
          (detail := some s!"{text.quote} takes '{id}', after {holder.quote}"))
      taken := taken.insert id text
      openId := some id
      cur := #[cfg.applyEpoch (blockNode cfg b)]
    | _ =>
      unless Ir.pageMarkerBlock b do cur := cur.push (cfg.applyEpoch (blockNode cfg b))
      cfg := cfg.afterBlock b
  return (close out cur openId, diags)

/-- Whether an element is a sequential-navigation tab stop (HTML §6.6.3). -/
public def tabbable (tag : String) (attrs : Array (String × String)) : Bool :=
  match (attrOf? attrs "tabindex").bind String.toInt? with
  | some i => decide (0 ≤ i)
  | none =>
    ((tag == "a" || tag == "area") && (attrOf? attrs "href").isSome) ||
    (["button", "input", "select", "textarea"].contains tag &&
      (attrOf? attrs "disabled").isNone && attrOf? attrs "type" != some "hidden") ||
    tag == "iframe" || tag == "summary" ||
    ((tag == "audio" || tag == "video") && (attrOf? attrs "controls").isSome)

mutual

/-- Whether a subtree holds a tab stop outside a `hidden` subtree. -/
public def tabbableOne : Node → Bool
  | .elem tag attrs kids =>
    (attrOf? attrs "hidden").isNone && (tabbable tag attrs || tabbableList kids.toList)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

public def tabbableList : List Node → Bool
  | [] => false
  | k :: rest => tabbableOne k || tabbableList rest

end

/-- Whether an element stands `aria-hidden` over a tab stop, itself or below. -/
public def hidesTabStop : Node → Bool
  | .elem tag attrs kids =>
    attrOf? attrs "aria-hidden" == some "true" && tabbableOne (.elem tag attrs kids)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- A logo's content as decoration: every image's `alt` blank. -/
private def logoDecoration (content : Array Inline) : Array Inline :=
  Ir.mapInlines (fun x => match x with
    | .image src size _ => .image src size .undeclared
    | x => x) content

/-- A logo's box: decorative and hidden from assistive technology, unless it holds a tab stop. -/
public def logoBox (cls : String) (style : Option String) (deco authored : Array Node) : Node :=
  let styled := match style with
    | some s => #[("style", s)]
    | none => #[]
  if tabbableList deco.toList then
    Html.elem "div" authored (#[("class", cls)] ++ styled)
  else
    Html.elem "div" deco
      (#[("class", cls), ("role", "presentation"), ("aria-hidden", "true")] ++ styled)

/-- Artifact-specific. -/
public theorem logoBox_hidden_contract (cls : String) (style : Option String)
    (deco authored : Array Node) :
    hidesTabStop (logoBox cls style deco authored) = false := by
  cases style <;> simp only [logoBox] <;> split <;>
    simp_all [hidesTabStop, tabbableOne, tabbable, attrOf?, Html.elem]

/-- A frame's logo in force, attached as the section's own furniture. -/
private def attachLogo (cfg : Config) (node : Node)
    (logo : Option (Array Inline)) : Node :=
  match logo with
  | none => node
  | some content =>
    if content.isEmpty then node else
    match node with
    | .elem tag attrs kids =>
      let justify := match Ir.logoAlign cfg.styles with
        | .left => "flex-start"
        | .center => "center"
        | .right => "flex-end"
      Node.elem tag attrs (kids.push (logoBox "slide-logo"
        (some s!"justify-content: {justify}")
        (inlines cfg (logoDecoration content)) (inlines cfg content)))
    | .text s => .text s
    | .style s => .style s
    | .script attrs s => .script attrs s

mutual

/-- An image-use attribute in tree order, hidden uses included. -/
private def imageAttrsOne (name : Option String) (acc : Array String) : Node → Array String
  | .elem tag attrs kids =>
    let acc :=
        match attrOf? attrs (name.getD (if tag == "img" then "src" else "data-image-src")) with
        | some s => acc.push s
        | none => acc
    imageAttrsList name acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

private def imageAttrsList (name : Option String) (acc : Array String) : List Node → Array String
  | [] => acc
  | k :: rest => imageAttrsList name (imageAttrsOne name acc k) rest

end

/-- Every image source a node carries, failed-conversion placeholders included. -/
public def imgSrcsOne (acc : Array String) (node : Node) : Array String :=
  imageAttrsOne none acc node

/-- Every image source a tree carries, hidden or not, in page order. -/
public def imgSrcsList (acc : Array String) (nodes : List Node) : Array String :=
  imageAttrsList none acc nodes

/-- What the page owes its schemes beyond colours: forced-colours band borders, and a plate under
see-through images. -/
public def schemeRules (cfg : Config) : String :=
  "@media (forced-colors: active) {\n" ++
  "  section.slide > header, body > header.headline, section.slide.standout,\n" ++
  "  section.block > header, section.tcolorbox > header { border: 1px solid CanvasText; }\n}\n" ++
  -- the plate is the printed page's colour as a literal, since every role reads the other screen's
  (let page := Ir.Design.printPage cfg.docPal
   let dark := cfg.docPal.darkPage
   if dark && (cfg.ships .light || cfg.ships .lightMore) then
     "@supports (color: light-dark(#000, #fff)) {\n" ++
     s!"  img.see-through, svg.picture \{ background: light-dark({cssColor page}, transparent); }\n" ++
     "}\n"
   else if !dark && (cfg.ships .dark || cfg.ships .darkMore) then
     "@supports (color: light-dark(#000, #fff)) {\n" ++
     s!"  img.see-through, svg.picture \{ background: light-dark(transparent, {cssColor page}); }\n" ++
     "}\n"
   else "")

/-- A document as its typed tree, head and body, with the backend's own diagnostics. -/
private def emitTreeCore (cfg : Config) (doc : Doc)
    (styles : (Ir.Color → String) → String × Array Diag) :
    Array Node × Array Node × Array Diag := Id.run do
  -- backend conditionals resolve here, so every walk below sees only this page's content
  let doc := { doc with body := Ir.keepFor "html" doc.body }
  let cfg := { cfg with locale := doc.info.locale }
  let judge := if cfg.css == .own then Contrast.schemeJudge doc else {}
  let cfg := { cfg with pal := doc.palette, docPal := doc.palette, frames := judge.frames
                        views := (judge.views.head?.map (·.2)).getD []
                        boxTexts := boxRoleTexts judge.frames ((judge.views.head?.map (·.2)).getD [])
                        paletteViews := judge.views
                        floor := floorScheme judge.frames doc.palette.homeScreen }
  let cfg := if cfg.frames.isEmpty || (docTokenClasses doc).isEmpty then cfg else
    let paints := cfg.listingPaints {}
    { cfg with codeRoot := paints.map fun (sc, _, _, rs) => (sc, rs), codePaints := paints }
  let allTables : List (Ir.Scheme × Ir.Palette) :=
    if cfg.frames.isEmpty then (Contrast.docPalettes doc).map (.light, ·)
    else judge.views.flatMap fun (_, vs) => (cfg.frames.zip vs).map fun (f, v) => (f.scheme, v)
  let mut diags : Array Diag := judge.diags
  if doc.head.isSome || doc.foot.isSome then
    diags := diags.push (Diag.of .W0007
      "running head/foot is paged-media furniture; omitted from HTML"
      (help := "body content reaches both backends: move the masthead there"))
  -- outside the frame model a logo is paged-media furniture, and its drop is named
  if doc.docClass.record.model != .frame &&
      (doc.logo.isSome || doc.body.any (fun b => match b with
        | .logo c => !c.isEmpty
        | _ => false)) then
    diags := diags.push (Diag.of .W0007
      "the \\logo is paged-media furniture; omitted from HTML"
      (help := "body content reaches both backends: move the image there"))
  let title := doc.info.title.getD "Untitled"
  let mut head : Array Node := #[
    Html.elem "meta" #[] #[("charset", "utf-8")],
    Html.elem "meta" #[] #[("name", "viewport"),
      ("content", "width=device-width, initial-scale=1")],
    Html.elem "title" #[Html.text title]
  ]
  for (name, value) in [("author", doc.info.author), ("description", doc.info.subject),
      ("keywords", doc.info.keywords)] do
    if let some v := value then
      head := head.push (Html.elem "meta" #[] #[("name", name), ("content", v)])
  -- the declared web identity: canonical URL, icon, and Open Graph from facts declared once
  if let some url := doc.info.url then
    head := head.push (Html.elem "link" #[] #[("rel", "canonical"), ("href", url)])
  if let some icon := doc.info.favicon then
    let href := match cfg.favicon with
      | some (source, r) => if source == icon then r.uri else icon
      | none => icon
    head := head.push (Html.elem "link" #[] #[("rel", "icon"), ("href", href)])
  if let some md := cfg.mdHref then
    head := head.push (Html.elem "link" #[]
      #[("rel", "alternate"), ("type", "text/markdown"), ("href", md)])
  if doc.info.url.isSome || doc.info.image.isSome then
    let og (p v : String) : Node :=
      Html.elem "meta" #[] #[("property", p), ("content", v)]
    if let some t := doc.info.title then
      head := head.push (og "og:title" t)
    if let some s := doc.info.subject then
      head := head.push (og "og:description" s)
    if let some u := doc.info.url then
      head := head.push (og "og:url" u)
    if let some i := doc.info.image then
      head := head.push (og "og:image" i)
    head := head.push (og "og:type" "website")
    head := head.push (Html.elem "meta" #[]
      #[("name", "twitter:card"), ("content", "summary")])
  -- JSON-LD as a data block: schema.org's WebPage, every value through `Html.escapeJson`
  if doc.info.url.isSome then
    let jstr (s : String) : String := "\"" ++ Html.escapeJson s ++ "\""
    let field (k : String) : Option String → List String
      | some v => [s!"  {jstr k}: {jstr v}"]
      | none => []
    let author := match doc.info.author with
      | some a =>
        [s!"  {jstr "author"}: \{{jstr "@type"}: {jstr "Person"}, {jstr "name"}: {jstr a}}"]
      | none => []
    let fields :=
      [s!"  {jstr "@context"}: {jstr "https://schema.org"}",
       s!"  {jstr "@type"}: {jstr "WebPage"}"] ++
      field "name" doc.info.title ++ field "description" doc.info.subject ++
      field "url" doc.info.url ++ field "image" doc.info.image ++ author
    head := head.push (Node.script #[("type", "application/ld+json")]
      ("{\n" ++ String.intercalate ",\n" fields ++ "\n}"))
  head := head.push (Html.elem "meta" #[] #[("name", "generator"), ("content", "leantex")])
  let (styled, styleDiags) := styles cfg.literal
  diags := diags ++ styleDiags
  let faceRules := match cfg.fonts with
    | some fs => fontCss fs
    | none => ""
  -- the base sheet's slot is held here, filled once the body's boundary shapes are known
  let cssCfg := cfg
  let styleAt := head.size
  match cfg.css with
  | .own => head := head.push (Node.style "")
  | .bulma =>
    -- the tokens bound onto Bulma's custom properties, before the declared sheet
    let primary := "var(--primary, " ++ roleRef .accent ++ ")"
    let accentDecl := String.join ((roleDefaultVars doc.palette .light [.accent]).map (· ++ "\n"))
    head := head.push (Node.style (faceRules ++ ":root {\n" ++ tokenVars cfg doc [.accent] ++ "\n" ++
      accentDecl ++
      s!"    --bulma-primary: {primary};\n" ++
      "    --bulma-body-family: var(--font-body, inherit);\n" ++
      "}\n" ++ styled))
  | .none => unless styled.isEmpty do head := head.push (Node.style styled)
  -- the declared sheet comes last, so it wins at equal specificity
  if let some href := doc.output.stylesheet then
    head := head.push (match cfg.stylesheet with
      | some (source, css) => if source == href then Node.style css else
          Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)]
      | none => Html.elem "link" #[] #[("rel", "stylesheet"), ("href", href)])
  let bodyClass := match cfg.css with
    | .bulma => "content"
    | _ => ""
  let cfg := { cfg with styles := doc.styles
                        cssRoles := match cfg.css with
                          | .own => Ir.Role.all
                          | _ => []
                        declarable := match cfg.css with
                          | .own => (Ir.Role.all.map
                              (roleDeclarable allTables)).toArray
                          | _ => #[]
                        pal := doc.palette
                        docPal := doc.palette
                        tokens := doc.tokens
                        deck := doc.docClass.record.model == .frame
                        chromeAllowed := doc.chromeAllowed
                        frameKeys := doc.frameKeys
                        page := doc.page
                        lengthBasis := lengthBasisOf doc
                        lists := doc.docClass.record.lists }
  let hasFrameFoot := doc.body.any fun b => match b with
    | .framefoot xs => !xs.isEmpty
    | _ => false
  let chromeFoot := doc.chromeAllowed && (doc.chrome.hasFooter || hasFrameFoot)
  let (inner, sectionDiags) := if doc.docClass.record.model == .flow then
      sectionize cfg doc.body
    else if doc.docClass.record.model != .frame then
      (blockNodesInto cfg #[] doc.body.toList, #[])
    else Id.run do
      -- frame numbers come only from `Ir.frameNumbers`, the PDF's own
      let nums := doc.frameNumbers
      let mut total := doc.frameCount
      let mut done := 0
      let labels := doc.frameLabels
      let mut sectionPages := 0
      let mut curSection : Array Inline := #[]
      let mut frameFoot : Option (Array Inline) := none
      let mut logoSpans : Array (Nat × Array Inline) := #[]
      let mut acc : Array Node := #[]
      let mut walkDiags : Array Diag := #[]
      -- each assigned frame id with the plain title that holds it
      let mut taken : Std.HashMap String String := {}
      let mut named : Std.HashSet String := {}
      let mut cfg := cfg
      for h : i in [0:doc.body.size] do
        let b := doc.body[i]
        total := doc.frameCountAt i
        if doc.frameRestart == some i then done := 0
        match b with
        | .setPalette p =>
          cfg := cfg.advancePalette p
        | .setTokens tk =>
          cfg := cfg.advanceTokens tk
        | .logo c =>
          -- the frames from here on carry `c`; an empty `c` clears
          logoSpans := logoSpans.push (i, c)
        | .framefoot xs =>
          frameFoot := if xs.isEmpty then none else some xs
          -- a continuous page has no physical page number, so the drop is named
          if Ir.hasPhysicalPage xs && walkDiags.isEmpty then
            walkDiags := walkDiags.push (Diag.of .W0007
              "\\pagenumber in a \\framefoot is paged-media furniture; \
omitted from HTML"
              (help := some "the deck has no physical pages; \\framenumber \
via \\chrome is the sequence both backends share"))
        | .frame title standout _ _ fbody =>
          let frameCfg := cfg.inFrame b
          let num := nums[i]?.getD none
          let numberAttrs := num.toArray.map fun n => ("data-frame-number", toString n)
          let label := (labels[i]?.getD none).getD "slide"
          done := num.getD done
          -- a fill the stage cannot grow is named once per frame
          let lists := doc.docClass.record.lists
          if Ir.frameFills lists doc.styles .deck fbody <
              Ir.frameFills lists doc.styles .every fbody then
            walkDiags := walkDiags.push (Diag.of .W0399 (subject := some label)
              "a \\vfill before more of its list item, or inside \\alt, spaces nothing \
on the web slide"
              (help := some "end the item at the \\vfill, or move it outside the \\alt")
              (detail := some s!"in frame {label}"))
          let (node, named2) := claimStageName named (blockNode frameCfg b)
          named := named2
          -- a stepped frame's anchor rides its track: a pinned stage reads as already in view
          let text := Ir.firstPageText title
          let base := slug title
          let base := if base.isEmpty then "slide" else base
          let (id, clash) := claimId taken base text
          if let some holder := clash then
            walkDiags := walkDiags.push (Diag.of .W0327
              s!"frames share the anchor '{base}'; each after the first takes a numbered anchor"
              (help := some s!"an in-page link '#{base}' reaches only the first; \
retitle the frames apart, or link to the numbered anchor")
              (detail := some s!"{text.quote} takes '{id}', after {holder.quote}"))
          taken := taken.insert id text
          let steps := frameCfg.overlaySteps
          let (spacers, taken2, diags2) :=
            if steps > 1 then
              snapWalk id text label #[] taken walkDiags (stepList steps)
            else
              (#[], taken, walkDiags)
          taken := taken2
          walkDiags := diags2
          let node := if chromeFoot then
              match doc.chrome.frameFootBand frameFoot curSection num total standout, node with
              | some band, .elem tag attrs kids =>
                let design := Design.ofPalette cfg.pal
                let look := design.frameFootLook standout
                let paint := if standout then
                    [s!"color: {colorRead frameCfg (some (.role .standoutInk)) look.fg};",
                     s!"background: {colorRead frameCfg (some (.role .standoutGround)) design.standout.bg};"]
                  else []
                Node.elem tag attrs (kids.push (Html.elem "footer"
                  (band.map fun s => Html.elem "span" (inlines frameCfg s.content)
                    #[("class", match s.side with
                        | .left => "band-left"
                        | .right => "band-right"),
                      ("style", s!"z-index: {s.rank}")])
                  #[("class", "slide-foot size-" ++ Ir.footline.step),
                    ("style", String.intercalate " "
                      (paint ++ footCapDecl doc.page.scale band ++
                        footBoxDecls doc.page (cfg.footBox (num.getD 0) band)))]))
              | _, other => other
            else node
          let node := attachLogo frameCfg node (Ir.logoInForce doc.logo logoSpans i)
          let node := if steps > 1 then
              Html.elem "div" (#[node] ++ spacers)
                (#[("class", "slide-track"), ("style", s!"--steps: {steps}"),
                  ("id", id), ("data-slide-label", s!"{label}.1")] ++ numberAttrs)
            else match node with
              | .elem tag attrs kids =>
                Node.elem tag (attrs ++ #[("id", id), ("data-snap", ""), ("data-snapped", "1"),
                  ("data-slide-label", label)] ++ numberAttrs) kids
              | .text s => Node.text s
              | .style s => Node.style s
              | .script attrs s => Node.script attrs s
          acc := acc.push (cfg.applyEpoch node)
          cfg := cfg.afterBlock b
        | .section 1 starred num title =>
          curSection := title
          if (Design.ofPalette cfg.pal).sectionProgress.isSome then
            -- no clamp, as on the PDF path
            let kids := #[Html.elem "h2" (inlines cfg title)]
            let kids := if total == 0 then kids else
              kids.push (Html.elem "div"
                #[Html.elem "div" #[] #[("style", s!"width: {done * 100 / total}%")]]
                #[("class", "progress")])
            let name := claimName named (sectionPageName title)
            named := named.insert name
            acc := acc.push (cfg.applyEpoch
              (attachLogo cfg
                (Html.elem "section" kids
                  (#[("class", "section-page")] ++
                    stageAttrs cfg.deck name ++ #[("data-snap", ""),
                      ("data-slide-label", s!"section-{sectionPages}")]))
                (Ir.logoInForce doc.logo logoSpans i)))
            sectionPages := sectionPages + 1
          else
            acc := acc.push (cfg.applyEpoch
              (blockNode cfg (.section 1 starred num title)))
        | _ =>
          unless Ir.pageMarkerBlock b do acc := acc.push (cfg.applyEpoch (blockNode cfg b))
          cfg := cfg.afterBlock b
      return (acc, walkDiags)
  diags := diags ++ sectionDiags
  -- the endnotes: one `doc-endnotes` section, each note back-linked to its mark
  let notes := Ir.footnotesOf doc.body
  let inner := if notes.isEmpty then inner else
    inner.push (Html.elem "section"
      #[Html.elem "ol" (notes.map fun (num, content) =>
          let n := num.getD 0
          Html.elem "li"
            ((inlineNodesInto cfg #[] content.toList).push (Html.text " ")
              |>.push (Html.elem "a" #[Html.text "\u21a9"]
                #[("href", s!"#fnref{n}"), ("role", "doc-backlink"),
                  ("aria-label", "back to the text"), ("style", "color: inherit")]))
            #[("id", s!"fn{n}")]) #[]]
      #[("role", "doc-endnotes")])
  let mainAttrs := (if bodyClass.isEmpty then #[] else #[("class", bodyClass)]) ++
    #[("style", "container-type: inline-size")]
  let main := Html.elem "main" inner mainAttrs
  -- the poster's headline band is the page's banner `<header>`
  let headerNode : Array Node := match doc.headline with
    | some hl =>
      let slot (c : Option (Array Ir.Inline)) : Array Html.Node :=
        match c with
        | some xs =>
          #[logoBox "headline-logo" none (inlines cfg (logoDecoration xs)) (inlines cfg xs)]
        | none => #[]
      let line (cls : String) (xs : Array Ir.Inline) : Array Html.Node :=
        if xs.isEmpty then #[] else
          #[Html.elem "p" (inlineNodesInto cfg #[] xs.toList) #[("class", cls)]]
      let matter := #[Html.elem "h1" (inlineNodesInto cfg #[] hl.title.toList)] ++
        line "headline-author" hl.author ++
        line "headline-institute" hl.institute
      #[Html.elem "header"
        (slot doc.logoLeft ++
          #[Html.elem "div" matter #[("class", "headline-matter")]] ++
          slot doc.logoRight)
        #[("class", "headline")]]
    | none => #[]
  let mut body : Array Node := headerNode ++ #[main]
  -- the progress hairline reads the base bar, never a section-only override
  if doc.docClass == .slides && (Design.ofDoc doc).progress.isSome then
    body := body.push (Html.elem "div" #[]
      #[("class", "deck-progress"), ("aria-hidden", "true")])
  body := body ++ deckScriptNodes (doc.docClass == .slides)
  -- figures numbered apart before the anchors are judged
  body := numberFigures body
  let facts := pageFactsList none {} body.toList
  -- premise: slideLabelChecks — these routes ship with the constant script
  let routes := if facts.deck then
      facts.slideLabels.foldl (init := ({} : Std.HashMap String String)) fun a label =>
        let a := a.insert label label
        if label.endsWith ".1" then a.insert (label.dropEnd 2).toString label else a
    else {}
  for (id, stage) in facts.ids do
    if let some target := routes[id]? then
      if stage != some target then
        diags := diags.push (Diag.of .W0327
          s!"fragment '#{id}' names both a slide and an element anchor; \
slide navigation uses '#{target}'"
          (subject := some id)
          (help := some (match stage with
            | some label => s!"use '#{label}' to reach the slide holding that anchor"
            | none => "rename the anchor so it differs from a slide label")))
  if facts.navs > 1 then
    -- ARIA asks each repeated landmark role for a unique label
    diags := diags.push (Diag.of .W0325
      "unlabeled <nav> landmarks repeat on one page, indistinguishable to assistive technology"
      (help := some "repeated landmarks need unique labels (ARIA Landmark \
Regions): give each one a name, \\begin{nav}[label = Site]")
      (detail := some s!"{facts.navs} on one page"))
  if facts.reveals > 0 then
    head := head.push (Node.style revealCss)
  -- every in-page link resolves or is named; `#` and `top` in any ASCII case always resolve
  let mut checked : Array String := #[]
  for fref in facts.fragmentRefs do
    let frag := (fref.drop 1).toString
    let isTop := frag.isEmpty || frag.map Char.toLower == "top"
    unless isTop || facts.ids.any (·.1 == frag) || routes.contains frag ||
        checked.contains fref do
      checked := checked.push fref
      diags := diags.push (Diag.of .W0326
        s!"in-page link '{fref}' has no target anchor on this page"
        (help := some (if facts.ids.isEmpty then
            "this page has no anchors: a level-1 \\section title becomes \
one in the article class"
          else s!"anchors on this page: \
{String.intercalate ", " (facts.ids.toList.map (fun kv => "#" ++ kv.1))}")))
  for k in undecodableIndices cfg.imgs
      (imageAttrsList (some "data-image-index") #[] body.toList) do
    if let some en := cfg.imgs.get? k then
      diags := diags.push (undecodableDiag (resolvedSrc en) en.webError (some k))
  let mut shipped := body
  if cssCfg.css == .own then
    let pairs := carrierPairs body
    let theme := themeCss doc cssCfg.blockTitleRule cssCfg.literal
    let tokens := tokenRules doc
    let base := baseRules doc pairs (cssCfg.imgs.entries.any (!·.webWords.isEmpty)) ++
      schemeRules cssCfg ++ tokens
    let rules := base ++ "\n" ++ theme ++ styled
    let (bodyReads, bodyDecls) := nodeRefsList (#[], #[]) body.toList
    let sheetReads := varReads rules
    let roots := (sheetReads ++ bodyReads).toList.filterMap roleOfVar? ++ readerRoles
    let edges := bodyDecls.filterMap fun (name, reads) =>
      (roleOfVar? name).map (·, reads.toList.filterMap roleOfVar?)
    let coded (r : Ir.Role) : Bool := r.code?.isSome &&
      (cssCfg.codeRoot.any (fun (_, rs) => ((rs.lookup r).join).isSome) ||
        bodyDecls.any (·.1 == roleVar r))
    -- a code role the root states as a palette role's colour reads that role
    let codeEdges := cssCfg.codeRoot.toArray.flatMap fun (_, rs) => rs.toArray.filterMap
      fun (r, p) => p.bind fun (_, key) => key.map fun k => (r, [k])
    let roles := pageRoleSet allTables roots (edges ++ codeEdges) coded
    let outside (name : String) : Bool := (roleOfVar? name).any (!roles.contains ·)
    let mut used := sheetReads.toList ++ bodyReads.toList ++
      bodyDecls.toList.flatMap (fun (d : String × Array String) => d.2.toList)
    if bodyReads.any outside || bodyDecls.any (outside ·.1) then
      shipped := keepRolesList roles.contains #[] body.toList
      -- what a dropped declaration read is no longer read
      let (r, d) := nodeRefsList (#[], #[]) shipped.toList
      used := sheetReads.toList ++ r.toList ++
        d.toList.flatMap (fun (d : String × Array String) => d.2.toList)
    head := head.modify styleAt fun _ => Node.style (faceRules ++ resolveRoleVars roles.contains
      (baseCss cssCfg doc pairs (roles := some roles) (taken := sheetReads.toList)
        (rules := some base)
        (epochVars := { cssCfg with cssRoles := roles }.epochVarBlocks
          (used.filter (·.startsWith "--ltx--"))) ++ "\n" ++ theme ++ styled))
  return (head, shipped, diags)

/-- The document's typed tree, head and body, with its diagnostics, from the normalized IR. -/
public def emitTree (cfg : Config) (doc : Doc) :
    Array Node × Array Node × Array Diag :=
  let coverage := cfg.fonts.map (·.mathAlphabets) |>.getD {}
  let family := cfg.fonts.bind (fun fs => fs.math.bind (fs.fonts[·]?))
    |>.map (·.family) |>.getD "math face"
  let resolved := Ir.resolveMathAlphas coverage family doc
  -- locations erased, so they hide nothing from the structural classifiers
  let tree := emitTreeCore { cfg with mathRenderer := none } (Ir.eraseLocations resolved.1)
    (fun lit => styleRules resolved.1 lit)
  -- projections, not a destructuring `let`, keep `emitTree_resolve_agree` cheap to check
  (tree.1, tree.2.1 ++ mathBoundaryNodes cfg.mathRenderer, resolved.2 ++ tree.2.2)

-- a bound below the default, holding the kernel check's cost
set_option maxHeartbeats 2000 in
public theorem emitTree_resolve_agree (cfg : Config) (doc : Doc) :
    let coverage := cfg.fonts.map (·.mathAlphabets) |>.getD {}
    let family := cfg.fonts.bind (fun fs => fs.math.bind (fs.fonts[·]?))
      |>.map (·.family) |>.getD "math face"
    let resolved := (Ir.resolveMathAlphas coverage family doc).1
    (emitTree cfg resolved).1 = (emitTree cfg doc).1 ∧
      (emitTree cfg resolved).2.1 = (emitTree cfg doc).2.1 := by
  simp only [emitTree, Ir.resolveMathAlphas_fixed_point, and_self]

-- a bound below the default, as above
set_option maxHeartbeats 2000 in
/-- Artifact-specific. -/
public theorem math_boundary_floor_exact (cfg : Config) (doc : Doc) :
    (emitTree cfg doc).1 = (emitTree { cfg with mathRenderer := none } doc).1 ∧
      (emitTree cfg doc).2.1 =
        (emitTree { cfg with mathRenderer := none } doc).2.1 ++ mathBoundaryNodes cfg.mathRenderer ∧
      (emitTree cfg doc).2.2 = (emitTree { cfg with mathRenderer := none } doc).2.2 := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [emitTree, mathBoundaryNodes, Array.append_empty]

/-- Emit a document: the file, and the diagnostics the backend itself raises. -/
public def emit (cfg : Config) (doc : Doc) : String × Array Diag :=
  let (head, body, diags) := emitTree cfg doc
  -- `<html lang>` is the document's declared tag, shipped as declared
  (Html.document (doc.info.language.getD "en") head body, diags)

/-- The captured resources this artifact may embed. -/
public def resources (cfg : Config) : Array HtmlResource.Embedded :=
  (cfg.fonts.map fontResources).getD #[] ++ imageResources cfg.imgs ++
    (cfg.favicon.map fun (_, r) => #[r]).getD #[]

/-- The scripts a page may carry: the deck's constant and the declared math renderer. -/
public def admittedScripts (renderer : Option String) : Array String :=
  #[deckScript] ++ renderer.toArray

/-- A checked page whose only scripts are the deck's constant and the declared renderer; a link's
URL scheme is outside the gate. -/
public abbrev ClosedPage (renderer : Option String) :=
  HtmlResource.ClosedPage (admittedScripts renderer)

/-- The publication entry: the emitted tree, closed against its captured resources. -/
public def emitClosed (cfg : Config) (doc : Doc) (svgChecked : Array ByteArray) :
    Except String (ClosedPage cfg.mathRenderer) × Array Diag :=
  let (head, body, diags) := emitTree cfg doc
  -- premise: Tests.htmlContainedChecks — Bulma requires a captured framework stylesheet.
  let page := if cfg.css == .bulma && doc.output.stylesheet.isNone then
      .error "'css = bulma' declares the framework's class names, and no 'stylesheet = ...' \
declares the framework's sheet"
    else HtmlResource.close (resources cfg) svgChecked (admittedScripts cfg.mathRenderer)
      (doc.info.language.getD "en") head body
  (page, diags)

/-- Artifact-specific. -/
public theorem emitClosed_covers (cfg : Config) (doc : Doc) (svgChecked : Array ByteArray)
    {page : ClosedPage cfg.mathRenderer} (h : (emitClosed cfg doc svgChecked).1 = .ok page) :
    page.render = (emit cfg doc).1 ∧
      ∀ r ∈ HtmlResource.requests (emitTree cfg doc).1 (emitTree cfg doc).2.1,
        HtmlResource.resolves (resources cfg) svgChecked (admittedScripts cfg.mathRenderer) r = true := by
  dsimp only [emitClosed] at h
  split at h
  · contradiction
  · exact HtmlResource.close_covers (resources cfg) svgChecked (admittedScripts cfg.mathRenderer)
      (doc.info.language.getD "en") _ _ h

public theorem emit_lang_declared (cfg : Config) (doc : Doc) :
    ∃ head body,
      (emit cfg doc).1 = Html.document (doc.info.language.getD "en") head body := by
  rcases h : emitTree cfg doc with ⟨head, body, ds⟩
  exact ⟨head, body, by simp [emit, h]⟩

/-! ## Accessibility facts -/

/-- Whether an element carries an accessible name in its own markup. -/
public def carriesName : Node → Bool
  | .elem _ attrs kids =>
    attrs.any (fun kv => (kv.1 == "aria-label" || kv.1 == "aria-labelledby") &&
        nonBlank kv.2) ||
      kids.any fun k => match k with
        | .elem "title" _ ts => ts.any fun t => match t with
          | .text s => nonBlank s
          | _ => false
        | _ => false
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- The page facts assistive technology depends on, as counts over the emitted tree. -/
public structure A11yFacts where
  h1s : Nat := 0
  /-- Tab stops under `aria-hidden`, outside a `hidden` subtree. -/
  hiddenTabStops : Nat := 0
  imgs : Nat := 0
  /-- `<img>` with no non-blank `alt` and no decorative role, or an unnamed non-SVG `img` role. -/
  imgsUnnamed : Nat := 0
  svgs : Nat := 0
  svgsUnnamed : Nat := 0
  /-- Elements the engine's own stylesheet makes scroll containers. -/
  scrolls : Nat := 0
  /-- Scroll containers a keyboard cannot reach, and deck stages with no name. -/
  scrollsUnreachable : Nat := 0
  summaries : Nat := 0
  /-- Summaries with no text and no name of their own. -/
  summariesUnnamed : Nat := 0
  deriving Repr, BEq, Inhabited

mutual

/-- Whether a subtree holds non-blank text outside a `hidden` subtree. -/
public def holdsTextOne : Node → Bool
  | .elem _ attrs kids => (attrOf? attrs "hidden").isNone && holdsTextList kids.toList
  | .text s => nonBlank s
  | .style _ => false
  | .script _ _ => false

public def holdsTextList : List Node → Bool
  | [] => false
  | k :: rest => holdsTextOne k || holdsTextList rest

end

public def classTokens (attrs : Array (String × String)) : List String :=
  ((attrOf? attrs "class").getD "").splitOn " " |>.filter (!·.isEmpty)

/-- Whether the engine's own stylesheet makes an element a scroll container. -/
public def declaresScroll (own deck : Bool) (tag : String) (attrs : Array (String × String)) :
    Bool :=
  own && (tag == "pre" ||
    (deck && tag == "section" &&
      (classTokens attrs).any (fun c => c == "slide" || c == "section-page")))

/-- Whether a scroll container is a tab stop with a name; a code block takes no name. -/
public def scrollReachable : Node → Bool
  | n@(.elem tag attrs _) =>
    attrOf? attrs "tabindex" == some "0" && (tag == "pre" || carriesName n)
  | .text _ => false
  | .style _ => false
  | .script _ _ => false

/-- One element's own contribution to the facts, its children aside. -/
private def a11yElem (own deck : Bool) (tag : String) (attrs : Array (String × String))
    (kids : Array Node) (acc : A11yFacts) : A11yFacts :=
  let decorative := match attrOf? attrs "role" with
    | some "presentation" | some "none" => true
    | _ => false
  let acc := if tag == "h1" then { acc with h1s := acc.h1s + 1 } else acc
  let acc := if tag == "img" || (tag != "svg" && attrOf? attrs "role" == some "img") then
      let named := if tag == "img" then nonBlank ((attrOf? attrs "alt").getD "")
        else carriesName (.elem tag attrs kids)
      { acc with imgs := acc.imgs + 1
                 imgsUnnamed := acc.imgsUnnamed + (if named || decorative then 0 else 1) }
    else acc
  let acc := if tag == "svg" then
      { acc with svgs := acc.svgs + 1
                 svgsUnnamed := acc.svgsUnnamed +
                   (if carriesName (.elem tag attrs kids) then 0 else 1) }
    else acc
  let acc := if tag == "summary" then
      { acc with summaries := acc.summaries + 1
                 summariesUnnamed := acc.summariesUnnamed +
                   (if holdsTextList kids.toList || carriesName (.elem tag attrs kids) then 0
                    else 1) }
    else acc
  if declaresScroll own deck tag attrs then
    { acc with scrolls := acc.scrolls + 1
               scrollsUnreachable := acc.scrollsUnreachable +
                 (if scrollReachable (.elem tag attrs kids) then 0 else 1) }
  else acc

mutual

/-- The facts of one node onto `acc`, under its `aria-hidden` and `hidden` ancestor flags. -/
private def a11yOne (own deck hidden inert : Bool) (acc : A11yFacts) : Node → A11yFacts
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let hid := hidden || attrOf? attrs "aria-hidden" == some "true"
    let inert := inert || (attrOf? attrs "hidden").isSome
    let acc := if !hid then a11yElem own deck tag attrs kids acc
      else if !inert && tabbable tag attrs then
        { acc with hiddenTabStops := acc.hiddenTabStops + 1 }
      else acc
    a11yList own deck hid inert acc kids.toList

private def a11yList (own deck hidden inert : Bool) (acc : A11yFacts) : List Node → A11yFacts
  | [] => acc
  | k :: rest => a11yList own deck hidden inert (a11yOne own deck hidden inert acc k) rest

end

/-- The facts of a page body under its stylesheet mode and page model. -/
public def a11yFacts (own deck : Bool) (body : Array Node) : A11yFacts :=
  a11yList own deck false false {} body.toList

/-- The text pairings a page's own stylesheet creates in one scheme, each with the contrast ratio
it owes. -/
public def themePairs (pal : Ir.Palette) (s : Ir.Scheme) (stage : Bool := false) :
    List (String × Ir.Color × Ir.Color × Nat) :=
  let look (r : Ir.Role) := (Ir.Design.at pal s r).getD Ir.Color.black
  let text := Contrast.requiredIn s (Ir.Need.text.atStage stage)
  [("text", look .ink, look .page, text),
   ("muted", look .muted, look .page, text),
   ("marker", look .marker, look .page, text),
   -- a listing a class paints no ground under stands on the page
   ("code", look .codeInk, (Ir.Design.at pal s .codeSurface).getD (look .page), text),
   ("accent", look .focus, look .page, Contrast.requiredIn s .nonText)]

/-- The pairings a page fails in each screen scheme it ships; none under a stylesheet the engine
does not own. -/
public def schemeFailures (own : Bool) (doc : Doc) : List (String × String) :=
  if !own then [] else
    let j := Contrast.schemeJudge doc
    let stage := Contrast.stageOf doc
    (j.frames.zip ((j.views.head?.map (·.2)).getD [])).flatMap fun (f, v) =>
      if f.scheme == .print then [] else
      ((themePairs v f.scheme stage).filter fun p =>
          Contrast.contrastMilli p.2.1 p.2.2.1 < p.2.2.2).map fun p => (f.scheme.name, p.1)

public theorem picture_svg_named_contract (cfg : Config) (pic : Ir.Pic.Picture) :
    (blockNode cfg (.picture pic)).tag? = some "svg" ∧
      (pic.alternative ≠ .decorative → carriesName (blockNode cfg (.picture pic)) = true) := by
  rcases h : pictureBoxOf cfg pic with ⟨⟨x0, y0⟩, ⟨x1, y1⟩⟩
  refine ⟨by simp [blockNode, Ir.Block.listScope, pictureSvg, h, Html.elem, Node.tag?],
    fun hd => ?_⟩
  cases ha : pic.alternative with
  | decorative => exact absurd ha hd
  | described t =>
    simp [blockNode, Ir.Block.listScope, pictureSvg, h, Html.elem, carriesName, pictureRole,
      pictureAltAttrs, ha, firstNonBlank_contract _ _ (figureWord_contract cfg.locale)]
  | undeclared =>
    simp [blockNode, Ir.Block.listScope, pictureSvg, h, Html.elem, carriesName, pictureRole,
      pictureAltAttrs, ha, figureWord_contract]

/-- Artifact-specific. -/
public theorem frame_stage_reachable_contract (cfg : Config) (hd : cfg.deck = true)
    (title : Array Inline) (standout : Bool) (valign : VAlign) (br : Bool)
    (body : Array Block) :
    scrollReachable (blockNode cfg (.frame title standout valign br body)) = true := by
  simp [blockNode, Ir.Block.listScope, Config.inFrame, hd, Html.elem, scrollReachable,
    carriesName, attrOf?, stageAttrs, frameName_contract]

end LeanTex.Core.HtmlDoc
