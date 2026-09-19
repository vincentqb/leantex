import LeanTex.Core.Ir

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- The four declaration surfaces a `\theme` installs onto: what the
document has declared at the theme site, and what its later declarations
keep overriding. Values in, values out — the install is `apply` below, a
function of these alone. A `Theme` extends this record: a bundle is the
same four surfaces plus a name.

`theme_fixes_no_page`, by construction: a class fixes the page model and
nothing a theme may override. This structure is `apply`'s whole domain and
codomain, and it carries no page, no class, and no assertion, so a bundle
*cannot* reach the geometry or the class's implied contract
(`Ir.DocClass.record`) — the compiler enforces the rule at the type, the
same way `DocClass` closes the class set; `theme_layer_contract` is the
checkable half over the shipped bundles. Keep it that way: a bundle wanting
geometry is a genre or class question, never a theme field (the
value-vs-consumer layering rule; audit-layer's `Theme.apply`/W0348 fixed
the value-vs-value face, and W0355 names the consumer face at install). -/
structure Decls where
  palette : Palette := {}
  tokens : Tokens := {}
  styles : Styles := {}
  /-- The slide footer's slots, declared data (`\chrome`), not colour: no
  theorem ranges over it. -/
  chrome : Chrome := {}
  deriving Repr, BEq

/-- A theme is data: palette, tokens, element styles, and chrome as the
*values* the engine runs on, installed at the `\theme` site through the same
replace-on-redeclare path a document's own declarations use. A document's
later declarations override, so a theme is a default, never a lock — and a
new theme is a new table here, values only, no code. Values rather than
surface strings so a theorem about a bundle ranges over what `\theme`
installs (`Contrast.builtin_palettes_contract` closes by `decide` over
these entries, for every bundle in `builtin` at once);
colour arithmetic a bundle wants (xcolor's `!` mixes) is evaluated right
here, at definition time, with the same `Color.mix` step
`Ir.Palette.resolve` folds at document use sites. The semantic palette keys
are the whole contract with the backends: `fg`/`bg` colour text and page,
declaring `frametitlebg` turns the frame title into a colour bar,
`progressfg`/`bg` draw the section-page progress bar (`progressheight`
sizes it), `standoutfg`/`bg` invert a `[standout]` frame, and `muted`
quiets secondary furniture — the chrome footer draws in it. -/
structure Theme extends Decls where
  name : String

/-- `{\large\bfseries}` (`{\Large\bfseries}` for `large := "Large"`) as the
elaborator reads a `\style` font value: nested wrappers with an empty body
where the element's own content goes. -/
private def boldFont (size : String) : ElementStyle :=
  { font := some #[.styled (.size size) #[.styled .bold #[]]] }

private def pt1 : Dim.SymGlue := { width := Length.ofSp (Dim.pt 1) }

/-- The Metropolis lineage as a token bundle: an inverted frame-title bar,
one warm accent, a near-white page. Values map the moloch beamer theme's
light preset onto the semantic keys, mixes evaluated (the original xcolor
spelling rides in the comment beside each). -/
def moloch : Theme :=
  let fg : Color := { r := 0x23, g := 0x37, b := 0x3B }
  let bg := Color.black.mix 2 Color.white                     -- black!2
  -- moloch's own alert is #EB811B, which reads at 2.61:1 on this page —
  -- under the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text. The same orange at
  -- 70% over black clears it at 4.94:1, so the lineage keeps its hue and
  -- the bundle keeps the engine's contract (Core/Contrast.lean).
  let alert : Color := { r := 0xA5, g := 0x5A, b := 0x13 }
  let progressfg := alert
  let progressbg := (progressfg.mix 50 .black).mix 30 .white  -- progressfg!50!black!30
  { name := "moloch"
    palette := {
      entries := #[
        ("fg", fg), ("bg", bg), ("alert", alert), ("example", { r := 0x00, g := 0x80, b := 0x80 }),
        -- The muted step: the theme's own ink mixed 70:30 into its page, the
        -- strongest quieting that still clears the 4.5:1 WCAG 2.2 SC 1.4.3
        -- asks of the small footer text (4.79:1 here;
        -- Contrast.builtin_palettes_contract is the kernel check, and
        -- 60:40 already fails at 3.65:1).
        ("muted", fg.mix 70 bg),                              -- fg!70!bg
        ("frametitlefg", bg), ("frametitlebg", fg),
        ("progressfg", progressfg), ("progressbg", progressbg),
        ("separator", progressfg),
        ("standoutfg", bg), ("standoutbg", fg)]
      -- Covered overlay content keeps each colour at 31% of itself over
      -- the page, mixed in Oklab (Core/Oklab.lean). Material's
      -- disabled-state opacity is 38% (m2.material.io/design/interaction/
      -- states.html#disabled), but at 38% this bundle's alert and example
      -- read at 2.89:1 and 2.75:1 against their active forms — under the
      -- 3:1 WCAG 2.2 SC 1.4.11 asks of state-identifying information; 31%
      -- is the largest fraction where every text role clears it
      -- (Contrast.builtin_designs_covered is the kernel check).
      coveredFraction := some 31 }
    -- The title page's inter-part spacing, from the moloch source
    -- (beamerinnerthememoloch.dtx): 0.3em above the subtitle, 0.8em below
    -- the separator (its default linewidth is 0.5pt), 0.5em below the
    -- author, 1em below the institute.
    -- progressheight is moloch's `progressbar linewidth=1pt` default
    -- (beamerouterthememoloch.dtx, \moloch@outer@setdefaults).
    tokens := { entries := #[
      ("progressheight", pt1),
      ("separatorheight", { width := Length.ofSp (Dim.pt 1 / 2) }),  -- 0.5pt
      ("subtitlegap", { width := { em := 300 } }),                   -- 0.3em
      ("separatorgap", { width := { em := 800 } }),                  -- 0.8em
      ("authorgap", { width := { em := 500 } }),                     -- 0.5em
      ("institutegap", { width := { em := 1000 } })] }               -- 1em
    styles := { entries := #[
      ("frametitle", boldFont "large"),
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large"),
      -- moloch's `title page` template sets the title matter ragged left
      -- and draws a separator rule between the title block and the author
      -- block, in the palette's separator colour (resolved here, exactly
      -- what `separator = separator` resolved to at install time).
      ("titlepage", { align := some "left"
                      separator := some (progressfg, some "separator") })] }
    -- The footline of the lineage read as data: metropolis puts the frame
    -- number in the footline and a `frame footer` template beside it; here
    -- the section title keeps the reader placed and the frame number says
    -- how far along (beamerouterthememoloch.dtx, footline template).
    chrome := { footerLeft := some .sectionTitle
                footerRight := some .frameNumber } }

/-- A quieter default: near-black ink on white, one restrained accent, no
title bar — frame titles set as plain bold headings because the bar key is
simply absent. A third theme costs exactly one more table like this. -/
def plain : Theme :=
  let fg : Color := { r := 0x1B, g := 0x1B, b := 0x1F }
  let bg : Color := { r := 0xFF, g := 0xFF, b := 0xFF }
  { name := "plain"
    palette := {
      entries := #[
        ("fg", fg), ("bg", bg), ("alert", { r := 0xB3, g := 0x26, b := 0x1E }),
        ("example", { r := 0x20, g := 0x5E, b := 0x3B }),
        -- Same muted rule as moloch: ink 70:30 into the page (6.36:1 here).
        ("muted", fg.mix 70 bg),                              -- fg!70!bg
        ("progressfg", fg.mix 60 .white),                     -- fg!60
        ("progressbg", fg.mix 15 .white),                     -- fg!15
        ("separator", fg.mix 40 .white),                      -- fg!40
        ("standoutfg", bg), ("standoutbg", fg)]
      -- Covered keeps each colour at 38% of itself over the page — the
      -- Material disabled-state opacity, per colour in Oklab; this
      -- bundle's roles all clear the 3:1 state change at 38%
      -- (Contrast.builtin_designs_covered is the kernel check).
      coveredFraction := some 38 }
    tokens := { entries := #[("progressheight", pt1)] }
    styles := { entries := #[
      ("sectionpage", boldFont "Large"),
      ("standout", boldFont "Large")] }
    chrome := { footerLeft := some .sectionTitle
                footerRight := some .frameNumber } }

def builtin : List Theme := [moloch, plain]

/-- A role resolves at one site: `Palette.find?` is the single reader of
the entries, and `Palette.resolve` — the evaluator `\textcolor` and every
declaration value go through — agrees with it on every entry name of every
shipped bundle. `black` and `white` are `resolve`'s only own atoms and they
yield to a declared entry of the same name, so the two spellings of a role
use cannot diverge; a bundle declaring an entry named `black` would fail
this contract's proof only if the yield rule broke. Adding a bundle is
entering the contract. -/
theorem role_resolves_at_one_site :
    (builtin.all fun t => t.palette.entries.toList.all fun e =>
      t.palette.resolve e.1 == t.palette.find? e.1) = true := by decide

/-- Arch-design I2, the value half: every shipped bundle that styles the
title page declares its alignment and its separator — moloch's title
matter is ragged left with a rule by declaration
(beamerinnerthememoloch.dtx's `title page` template is `\raggedright`
with a separator rule), never by a backend constant. The stronger
reading — that the declaration survives `\theme` through the elaborator —
is the staged `titlepage_align_declared_engine`. -/
theorem titlepage_align_declared :
    ∀ t ∈ builtin,
      ((t.styles.find? "titlepage").all fun st =>
        st.align.isSome && st.separator.isSome) = true := by decide

def find? (name : String) : Option Theme :=
  builtin.find? (·.name == name)

def names : List String := builtin.map (·.name)

/-- Key-wise onto the element's existing entry: the theme's key wins where
both declare it (the positional last-writer rule every palette entry
follows), and the document's survives where the theme is silent — over
every `Option` field of `ElementStyle`, the same merge a later `\style`
block performs against the running entry. -/
def styleMerge (top base : ElementStyle) : ElementStyle :=
  { font := top.font <|> base.font
    before := top.before <|> base.before
    after := top.after <|> base.after
    rule := top.rule <|> base.rule
    marker := top.marker <|> base.marker
    indent := top.indent <|> base.indent
    gap := top.gap <|> base.gap
    align := top.align <|> base.align
    separator := top.separator <|> base.separator
    ruleAbove := top.ruleAbove <|> base.ruleAbove
    ruleAboveSkip := top.ruleAboveSkip <|> base.ruleAboveSkip
    ruleAboveGap := top.ruleAboveGap <|> base.ruleAboveGap
    ruleBelow := top.ruleBelow <|> base.ruleBelow
    ruleBelowGap := top.ruleBelowGap <|> base.ruleBelowGap
    ruleBelowSkip := top.ruleBelowSkip <|> base.ruleBelowSkip
    authorFont := top.authorFont <|> base.authorFont
    authorStrut := top.authorStrut <|> base.authorStrut
    hover := top.hover <|> base.hover
    focus := top.focus <|> base.focus
    motion := top.motion <|> base.motion }

private def installPalette (p : Palette) : List (String × Color) → Palette
  | [] => p
  | (k, c) :: es => installPalette (p.declare k c) es

private def installTokens (t : Tokens) : List (String × Dim.SymGlue) → Tokens
  | [] => t
  | (k, g) :: es => installTokens (t.declare k g) es

private def installStyles (s : Styles) : List (String × ElementStyle) → Styles
  | [] => s
  | (k, st) :: es =>
    installStyles (s.declare k (styleMerge st ((s.find? k).getD {}))) es

/-- The bundle-palette install: entries fold through `Palette.declare`, and
the bundle's covered fraction rides with them (`<|>`: a document's earlier
`covered = <n>\%` yields, its later one overrides). Its own function so the
layering statements below take it whole. -/
private def paletteApply (bp p : Palette) : Palette :=
  let pal := installPalette p bp.entries.toList
  { pal with coveredFraction := bp.coveredFraction <|> pal.coveredFraction }

/-- The bundle-chrome install: per slot, the same shape as every palette
entry — the bundle's slot wins where it declares one, the document's
survives where it is silent. -/
private def chromeApply (bc c : Chrome) : Chrome :=
  { footerLeft := bc.footerLeft <|> c.footerLeft
    footerRight := bc.footerRight <|> c.footerRight }

/-- The `\theme` install as a value: the bundle's entries fold onto the
document's declarations through the same replace-on-redeclare doors the
document's own blocks use (`Palette.declare`, `Tokens.declare`,
`Styles.declare`), the bundle's covered fraction rides with its palette,
styles merge key-wise onto any entry already declared, and the bundle's
chrome merges per slot — a slot the bundle declares wins, as any later
declaration does, and a slot it leaves silent keeps the document's,
instead of the band replacing wholesale. Values in, values out, no
elaborator state — effects as data: `Elab` calls exactly this function at
the `\theme` site, so a statement about layering ranges over the install
the engine runs. -/
def apply (th : Theme) (s : Decls) : Decls :=
  { palette := paletteApply th.palette s.palette
    tokens := installTokens s.tokens th.tokens.entries.toList
    styles := installStyles s.styles th.styles.entries.toList
    chrome := chromeApply th.chrome s.chrome }

/-- Every `(declaration, key)` the bundle installs — `("palette", "alert")`,
`("chrome", "footer.left")` — whatever stood there before: the keys whose
standing value is the theme's after `apply`. -/
def declares (th : Theme) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for (k, _) in th.palette.entries do
    out := out.push ("palette", k)
  if th.palette.coveredFraction.isSome then
    out := out.push ("palette", "covered")
  for (k, _) in th.tokens.entries do
    out := out.push ("tokens", k)
  for (element, _) in th.styles.entries do
    out := out.push ("style", element)
  if th.chrome.footerLeft.isSome then
    out := out.push ("chrome", "footer.left")
  if th.chrome.footerRight.isSome then
    out := out.push ("chrome", "footer.right")
  return out

/-- The `(declaration, key)` pairs `apply` would overwrite with a
*different* value, computed against the same state `apply` consumes: the
positional last-writer rule says the theme wins them, and W0348's site
says so out loud when the loser was the document's own declaration. A key
the theme re-declares at the standing value replaces nothing and is not
listed. Install order: palette entries, `covered`, tokens, styles,
chrome. -/
def replaces (th : Theme) (s : Decls) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for (k, c) in th.palette.entries do
    if let some c0 := s.palette.find? k then
      if c0 != c then
        out := out.push ("palette", k)
  if let some n := th.palette.coveredFraction then
    if let some m := s.palette.coveredFraction then
      if n != m then
        out := out.push ("palette", "covered")
  for (k, g) in th.tokens.entries do
    if let some g0 := s.tokens.find? k then
      if g0 != g then
        out := out.push ("tokens", k)
  for (element, st) in th.styles.entries do
    if let some cur := s.styles.find? element then
      if styleMerge st cur != cur then
        out := out.push ("style", element)
  if let some d := th.chrome.footerLeft then
    if let some d0 := s.chrome.footerLeft then
      if d0 != d then
        out := out.push ("chrome", "footer.left")
  if let some d := th.chrome.footerRight then
    if let some d0 := s.chrome.footerRight then
      if d0 != d then
        out := out.push ("chrome", "footer.right")
  return out

/-- The class layer under the theme layer: a class fixes the page model
and its implied contract, and a theme may override neither. The type
carries most of it — `Ir.DocClass.record` reads the class alone, and
`apply`'s whole domain and codomain is `Decls`, which has no class, page,
or assertion field, so applying any theme leaves the class's page model
and assertions unchanged by construction. The checkable residue is this
contract: every key a shipped bundle installs lives on one of the four
visual surfaces. Quantified over `builtin` — adding a bundle is entering
the contract. -/
theorem theme_layer_contract :
    (builtin.all fun t => (declares t).toList.all fun e =>
      ["palette", "tokens", "style", "chrome"].contains e.1) = true := by decide

/-! ## The layering contract over the install

T1 (`Palette.declare_last_wins`, `Palette.declare_keeps_others` and the
`Tokens` twins beside them in `Ir`) states the per-key contract of one
declaration. The statements below are its bundle-side companions, in the
same terms, over the install the engine runs (`apply`):

* T2, the keeps side — a bundle changes only the keys it declares:
  `apply_palette_keeps_others` and its per-surface siblings. The positional
  reading (a bundle *wins* the keys it does declare, wherever it stands) is
  the beamer lineage's `\usetheme` semantics — a `\setbeamercolor` before
  `\usetheme` loses the same way — and per entry it is exactly
  `Palette.declare_last_wins`.
* Idempotence — applying a theme twice is applying it once:
  `apply_fixed_point`. A bundle declares a state, it does not perform an
  action, so `apply th s` is a fixed point of `apply th`.
-/

/-- No key declared twice. Every shipped bundle satisfies it
(`builtin_styles_nodup`), and it is what pins the style fold's read-back
to the pre-install state in `apply_fixed_point`. -/
def nodupKeys {α : Type} : List (String × α) → Bool
  | [] => true
  | e :: es => !(es.any (·.1 == e.1)) && nodupKeys es

/-- Entering the contract: every shipped bundle declares each style element
once, so `apply_fixed_point` covers it. Quantified over `builtin` — adding
a bundle re-runs this check. -/
theorem builtin_styles_nodup :
    (builtin.all fun th => nodupKeys th.styles.entries.toList) = true := by decide

private theorem orElse_absorb {α : Type} (a b : Option α) :
    (a <|> (a <|> b)) = (a <|> b) := by
  cases a <;> rfl

private theorem or_absorb {α : Type} (a b : Option α) : a.or (a.or b) = a.or b := by
  cases a <;> rfl

private theorem styleMerge_absorb (a b : ElementStyle) :
    styleMerge a (styleMerge a b) = styleMerge a b := by
  simp [styleMerge, or_absorb]

/-- The keyed store, as every declare door writes it: filter the key out,
push the entry. `Palette.declare`, `Tokens.declare`, and `Styles.declare`
all reduce to iterating this step, so the fold lemmas below serve all
three surfaces. -/
private def installEntries {α : Type} (xs : Array (String × α)) :
    List (String × α) → Array (String × α)
  | [] => xs
  | (k, v) :: es => installEntries ((xs.filter (·.1 != k)).push (k, v)) es

private theorem step_find_eq {α : Type} (xs : Array (String × α)) (k : String) (v : α) :
    ((xs.filter (·.1 != k)).push (k, v)).find? (·.1 == k) = some (k, v) := by
  have hnone : (xs.filter (·.1 != k)).find? (·.1 == k) = none := by
    rw [Array.find?_eq_none]
    intro x hx
    have hne := (Array.mem_filter.mp hx).2
    simpa using hne
  rw [Array.find?_push, hnone]
  simp

private theorem step_find_ne {α : Type} (xs : Array (String × α)) (k k' : String) (v : α)
    (h : k' ≠ k) :
    ((xs.filter (·.1 != k)).push (k, v)).find? (·.1 == k') = xs.find? (·.1 == k') := by
  rw [Array.find?_push, Array.find?_filter]
  have hpred : (fun a : String × α => decide ((a.fst != k) = true ∧ (a.fst == k') = true))
      = (fun a : String × α => a.fst == k') := by
    funext x
    by_cases hx : (x.1 == k') = true
    · have hxe : x.1 = k' := by simpa using hx
      simp [hxe, h]
    · simp [hx]
  rw [hpred]
  have hkk : (k == k') = false := by
    simpa using fun hk => h hk.symm
  simp [hkk]

private theorem installEntries_keeps {α : Type} (es : List (String × α))
    (xs : Array (String × α)) (k : String) (h : ∀ e ∈ es, e.1 ≠ k) :
    (installEntries xs es).find? (·.1 == k) = xs.find? (·.1 == k) := by
  induction es generalizing xs with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k0, v0⟩ := e
    have hk : k0 ≠ k := h (k0, v0) (List.mem_cons_self ..)
    simp only [installEntries]
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      step_find_ne _ _ _ _ (fun hh => hk hh.symm)]

private theorem installEntries_residue {α : Type} (es : List (String × α))
    (xs : Array (String × α)) :
    installEntries xs es =
      xs.filter (fun x => !(es.any (fun e => x.1 == e.1))) ++ installEntries #[] es := by
  induction es generalizing xs with
  | nil =>
    simp only [installEntries, List.any_nil, Bool.not_false]
    rw [Array.filter_eq_self.mpr (fun a _ => rfl)]
    simp
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [installEntries]
    rw [ih ((xs.filter (·.1 != k)).push (k, v)),
      ih (((#[] : Array (String × α)).filter (·.1 != k)).push (k, v))]
    rw [Array.filter_push, Array.filter_push, Array.filter_filter]
    have hpred : (fun x : String × α => (!(es.any fun e => x.1 == e.1)) && (x.1 != k))
        = (fun x : String × α => !(((k, v) :: es).any fun e => x.1 == e.1)) := by
      funext x
      simp only [List.any_cons, Bool.not_or]
      rw [Bool.and_comm]
      rfl
    rw [hpred]
    have hempty : ((#[] : Array (String × α)).filter (·.1 != k)) = #[] := rfl
    rw [hempty]
    cases _hP : (!(es.any fun e => ((k, v) : String × α).1 == e.1)) with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [show (Array.filter (fun x => !es.any fun e => x.fst == e.fst)
        (#[] : Array (String × α))) = #[] from rfl]
      simp
    | true =>
      simp only [ite_true]
      rw [show (Array.filter (fun x => !es.any fun e => x.fst == e.fst)
        (#[] : Array (String × α))) = #[] from rfl]
      rw [Array.push_eq_append, Array.push_eq_append]
      simp

private theorem installEntries_mem {α : Type} (es : List (String × α))
    (xs : Array (String × α)) (x : String × α) (hx : x ∈ installEntries xs es) :
    x ∈ xs ∨ (es.any (fun e => x.1 == e.1)) = true := by
  induction es generalizing xs with
  | nil => exact .inl hx
  | cons e es ih =>
    obtain ⟨k, v⟩ := e
    simp only [installEntries] at hx
    rcases ih _ hx with hmem | hany
    · rcases Array.mem_push.mp hmem with hf | heq
      · exact .inl (Array.mem_filter.mp hf).1
      · right
        simp [heq, List.any_cons]
    · right
      simp [List.any_cons, hany]

private theorem installEntries_idem {α : Type} (es : List (String × α))
    (xs : Array (String × α)) :
    installEntries (installEntries xs es) es = installEntries xs es := by
  have hself : ((installEntries (#[] : Array (String × α)) es).filter
      (fun x => !(es.any (fun e => x.1 == e.1)))) = #[] := by
    rw [Array.filter_eq_empty_iff]
    intro x hx
    rcases installEntries_mem es #[] x hx with hmem | hany
    · simp at hmem
    · simp [hany]
  rw [installEntries_residue es (installEntries xs es), installEntries_residue es xs]
  rw [Array.filter_append (by simp), Array.filter_filter]
  have hidem : (fun x : String × α => (!(es.any fun e => x.1 == e.1)) &&
      !(es.any fun e => x.1 == e.1)) = (fun x : String × α => !(es.any fun e => x.1 == e.1)) := by
    funext x
    exact Bool.and_self _
  rw [hidem, hself]
  simp

private theorem find?_none_keys {α : Type} (xs : Array (String × α)) (k : String)
    (h : xs.find? (·.1 == k) = none) : ∀ e ∈ xs.toList, e.1 ≠ k := by
  intro e he hk
  rw [Array.find?_eq_none] at h
  have := h e (by simpa using he)
  simp [hk] at this

private theorem installPalette_entries (p : Palette) (es : List (String × Color)) :
    (installPalette p es).entries = installEntries p.entries es := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette, installEntries]
    rw [ih]
    rfl

private theorem installPalette_covered (p : Palette) (es : List (String × Color)) :
    (installPalette p es).coveredFraction = p.coveredFraction := by
  induction es generalizing p with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    rfl

private theorem installPalette_decorative (p : Palette) (es : List (String × Color)) :
    (installPalette p es).decorative =
      p.decorative.filter (fun x => !(es.any (fun e => x == e.1))) := by
  induction es generalizing p with
  | nil =>
    simp only [installPalette, List.any_nil, Bool.not_false]
    exact (Array.filter_eq_self.mpr (fun a _ => rfl)).symm
  | cons e es ih =>
    obtain ⟨k, c⟩ := e
    simp only [installPalette]
    rw [ih]
    show (p.decorative.filter (· != k)).filter _ = _
    rw [Array.filter_filter]
    congr 1
    funext x
    simp only [List.any_cons, Bool.not_or]
    rw [Bool.and_comm]
    rfl

private theorem installTokens_entries (t : Tokens) (es : List (String × Dim.SymGlue)) :
    (installTokens t es).entries = installEntries t.entries es := by
  induction es generalizing t with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, g⟩ := e
    simp only [installTokens, installEntries]
    rw [ih]
    rfl

/-- The style fold's writes, read against one base: nodup keys are what
make the running fold's reads equal these (each key is written once, so no
read sees an earlier write). -/
private def styleWrites (s : Styles) :
    List (String × ElementStyle) → List (String × ElementStyle)
  | [] => []
  | (k, st) :: es => (k, styleMerge st ((s.find? k).getD {})) :: styleWrites s es

private theorem styles_declare_find_ne (s : Styles) (k k' : String) (st : ElementStyle)
    (h : k' ≠ k) : (s.declare k st).find? k' = s.find? k' := by
  show (((s.entries.filter (·.1 != k)).push (k, st)).find? (·.1 == k')).map (·.2)
      = (s.entries.find? (·.1 == k')).map (·.2)
  rw [step_find_ne _ _ _ _ h]

private theorem styleWrites_congr (s₁ s₂ : Styles) (es : List (String × ElementStyle))
    (h : ∀ e ∈ es, styleMerge e.2 ((s₁.find? e.1).getD {})
      = styleMerge e.2 ((s₂.find? e.1).getD {})) :
    styleWrites s₁ es = styleWrites s₂ es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, st⟩ := e
    simp only [styleWrites]
    rw [h (k, st) (List.mem_cons_self ..), ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]

private theorem nodup_head {α : Type} (k : String) (v : α) (es : List (String × α))
    (h : nodupKeys ((k, v) :: es) = true) :
    (∀ e ∈ es, e.1 ≠ k) ∧ nodupKeys es = true := by
  simp only [nodupKeys, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun e he hk => ?_, h.2⟩
  have hall := List.any_eq_false.mp h.1 e he
  simp [hk] at hall

private theorem installStyles_entries (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) :
    (installStyles s es).entries = installEntries s.entries (styleWrites s es) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, st⟩ := e
    obtain ⟨hne, hnd⟩ := nodup_head k st es h
    simp only [installStyles, styleWrites, installEntries]
    rw [ih _ hnd]
    have hw : styleWrites (s.declare k (styleMerge st ((s.find? k).getD {}))) es
        = styleWrites s es := by
      apply styleWrites_congr
      intro e' he'
      rw [styles_declare_find_ne _ _ _ _ (hne e' he')]
    rw [hw]
    rfl

private theorem installStyles_keeps (s : Styles) (es : List (String × ElementStyle))
    (k : String) (h : ∀ e ∈ es, e.1 ≠ k) :
    (installStyles s es).find? k = s.find? k := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k0, st0⟩ := e
    simp only [installStyles]
    rw [ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')),
      styles_declare_find_ne _ _ _ _ (fun hh => (h (k0, st0) (List.mem_cons_self ..)) hh.symm)]

private theorem installStyles_find_mem (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) (k : String) (st : ElementStyle) (hmem : (k, st) ∈ es) :
    (installStyles s es).find? k = some (styleMerge st ((s.find? k).getD {})) := by
  induction es generalizing s with
  | nil => cases hmem
  | cons e es ih =>
    obtain ⟨k0, st0⟩ := e
    obtain ⟨hne, hnd⟩ := nodup_head k0 st0 es h
    cases hmem with
    | head =>
      simp only [installStyles]
      rw [installStyles_keeps _ _ _ hne]
      show ((((s.entries.filter (·.1 != k)).push
          (k, styleMerge st ((s.find? k).getD {}))).find? (·.1 == k)).map (·.2)) = _
      rw [step_find_eq]
      rfl
    | tail _ hmem' =>
      have hkne : k ≠ k0 := by
        intro hk
        exact (hne (k, st) hmem') (by rw [hk])
      simp only [installStyles]
      rw [ih _ hnd hmem', styles_declare_find_ne _ _ _ _ hkne]

private theorem styles_ext {a b : Styles} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  simpa using h

private theorem tokens_ext {a b : Tokens} (h : a.entries = b.entries) : a = b := by
  cases a
  cases b
  simpa using h

private theorem palette_ext {a b : Palette} (he : a.entries = b.entries)
    (hc : a.coveredFraction = b.coveredFraction) (hd : a.decorative = b.decorative) :
    a = b := by
  cases a
  cases b
  simp_all

private theorem installStyles_idem (s : Styles) (es : List (String × ElementStyle))
    (h : nodupKeys es = true) :
    installStyles (installStyles s es) es = installStyles s es := by
  apply styles_ext
  have hw : styleWrites (installStyles s es) es = styleWrites s es := by
    apply styleWrites_congr
    intro e he
    obtain ⟨k, st⟩ := e
    rw [installStyles_find_mem s es h k st he]
    show styleMerge st (styleMerge st ((s.find? k).getD {})) = _
    rw [styleMerge_absorb]
  rw [installStyles_entries _ _ h, hw, installStyles_entries s es h, installEntries_idem]

private theorem installTokens_idem (t : Tokens) (es : List (String × Dim.SymGlue)) :
    installTokens (installTokens t es) es = installTokens t es := by
  apply tokens_ext
  rw [installTokens_entries, installTokens_entries]
  exact installEntries_idem ..

private theorem paletteApply_entries (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).entries = installEntries q.entries bp.entries.toList := by
  intro q
  show (installPalette q bp.entries.toList).entries = _
  exact installPalette_entries ..

private theorem paletteApply_covered (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).coveredFraction
      = (bp.coveredFraction <|> q.coveredFraction) := by
  intro q
  show (bp.coveredFraction <|>
      (installPalette q bp.entries.toList).coveredFraction) = _
  rw [installPalette_covered]

private theorem paletteApply_decorative (bp : Palette) : ∀ q : Palette,
    (paletteApply bp q).decorative
      = q.decorative.filter
          (fun x => !(bp.entries.toList.any (fun e => x == e.1))) := by
  intro q
  show (installPalette q bp.entries.toList).decorative = _
  exact installPalette_decorative ..

private theorem paletteApply_idem (bp p : Palette) :
    paletteApply bp (paletteApply bp p) = paletteApply bp p := by
  apply palette_ext
  · simp only [paletteApply_entries]
    exact installEntries_idem ..
  · simp only [paletteApply_covered]
    exact orElse_absorb ..
  · simp only [paletteApply_decorative]
    rw [Array.filter_filter]
    congr 1
    funext x
    exact Bool.and_self _

private theorem chromeApply_idem (bc c : Chrome) :
    chromeApply bc (chromeApply bc c) = chromeApply bc c := by
  simp only [chromeApply]
  rw [orElse_absorb, orElse_absorb]

/-- T2, the palette half, in `Palette.declare_keeps_others`'s terms: a
bundle changes only the keys it declares — a key the theme does not name
resolves after `\theme` exactly as before it. -/
theorem apply_palette_keeps_others (th : Theme) (s : Decls) (k : String)
    (h : th.palette.find? k = none) :
    (apply th s).palette.find? k = s.palette.find? k := by
  have hall : ∀ e ∈ th.palette.entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Palette.find?, Option.map_eq_none_iff] at h
    exact h
  show ((installPalette s.palette th.palette.entries.toList).entries.find?
      (·.1 == k)).map (·.2) = _
  rw [installPalette_entries, installEntries_keeps _ _ _ hall]
  rfl

/-- The covered fraction is part of the same contract: a bundle that
declares no `covered` leaves the document's standing. -/
theorem apply_keeps_covered (th : Theme) (s : Decls)
    (h : th.palette.coveredFraction = none) :
    (apply th s).palette.coveredFraction = s.palette.coveredFraction := by
  show (th.palette.coveredFraction <|>
      (installPalette s.palette th.palette.entries.toList).coveredFraction) = _
  rw [h, installPalette_covered]
  rfl

/-- The decorative exemption is per key and rides with declarations
(`declare_decorative_rides`); a bundle that does not declare a key never
touches its exemption. -/
theorem apply_palette_keeps_decorative (th : Theme) (s : Decls) (k : String)
    (h : th.palette.find? k = none) :
    (k ∈ (apply th s).palette.decorative) ↔ k ∈ s.palette.decorative := by
  have hall : ∀ e ∈ th.palette.entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Palette.find?, Option.map_eq_none_iff] at h
    exact h
  show k ∈ (installPalette s.palette th.palette.entries.toList).decorative ↔ _
  rw [installPalette_decorative]
  constructor
  · intro hm
    exact (Array.mem_filter.mp hm).1
  · intro hm
    refine Array.mem_filter.mpr ⟨hm, ?_⟩
    simp only [Bool.not_eq_true']
    rw [List.any_eq_false]
    intro e he
    simpa using fun hk => (hall e he) hk.symm

/-- T2, the tokens half: `Tokens.declare_keeps_others` lifted over the
bundle fold. -/
theorem apply_tokens_keeps_others (th : Theme) (s : Decls) (k : String)
    (h : th.tokens.find? k = none) :
    (apply th s).tokens.find? k = s.tokens.find? k := by
  have hall : ∀ e ∈ th.tokens.entries.toList, e.1 ≠ k := by
    apply find?_none_keys
    simp only [Tokens.find?, Option.map_eq_none_iff] at h
    exact h
  show ((installTokens s.tokens th.tokens.entries.toList).entries.find?
      (·.1 == k)).map (·.2) = _
  rw [installTokens_entries, installEntries_keeps _ _ _ hall]
  rfl

/-- T2, the styles half: an element the bundle does not style keeps the
document's whole entry. -/
theorem apply_styles_keeps_others (th : Theme) (s : Decls) (element : String)
    (h : th.styles.find? element = none) :
    (apply th s).styles.find? element = s.styles.find? element := by
  have hall : ∀ e ∈ th.styles.entries.toList, e.1 ≠ element := by
    apply find?_none_keys
    simp only [Styles.find?, Option.map_eq_none_iff] at h
    exact h
  exact installStyles_keeps _ _ _ hall

/-- T2, the chrome half: a slot the bundle leaves silent keeps the
document's datum — the statement whose absence let the install replace the
band wholesale. -/
theorem apply_chrome_keeps_left (th : Theme) (s : Decls)
    (h : th.chrome.footerLeft = none) :
    (apply th s).chrome.footerLeft = s.chrome.footerLeft := by
  show (th.chrome.footerLeft <|> s.chrome.footerLeft) = _
  rw [h]
  rfl

theorem apply_chrome_keeps_right (th : Theme) (s : Decls)
    (h : th.chrome.footerRight = none) :
    (apply th s).chrome.footerRight = s.chrome.footerRight := by
  show (th.chrome.footerRight <|> s.chrome.footerRight) = _
  rw [h]
  rfl

/-- Idempotence: applying a theme twice is applying it once — `apply th s`
is a fixed point of `apply th`. A bundle declares a state rather than
performing an action, so a repeated `\theme{name}` cannot drift the
document. The one hypothesis — the bundle declares each style element
once — holds for every shipped bundle (`builtin_styles_nodup`) and is what
pins the style fold's read-back to the pre-install state. -/
theorem apply_fixed_point (th : Theme) (s : Decls)
    (h : nodupKeys th.styles.entries.toList = true) :
    apply th (apply th s) = apply th s := by
  simp only [apply]
  rw [paletteApply_idem, installTokens_idem, installStyles_idem _ _ h, chromeApply_idem]

end LeanTex.Core.Theme
