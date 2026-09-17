import LeanTex.Core.Layout
import LeanTex.Core.Contrast
import LeanTex.Core.Theme
import LeanTex.Core.Elab

/-!
# The owed theorems: obligations stated, proofs open

Every declaration here is a statement about the engine's *own* functions —
never a spec copy — whose proof is still a hole. A statement with a hole is
honest and useful: it says exactly what the engine does not yet guarantee,
in the engine's own language, and it cannot rot silently because the
compiler type-checks it even while the proof is missing.

This module is a queue, not a home. It is its own lake target
(`lake build Obligations`), outside the default build and outside
`lake test`; nothing in `LeanTex/` may import it (the pre-commit hook and
`scripts/owed.lean` both check, mechanically). A discharged obligation
moves into the module that owns it, with a real proof, and its hole
disappears from here.

Each obligation carries a record the ratchet reads — five consecutive
comment lines, `owed` (the name, registered in PLAN.md or the commit
fails), `owner` (where the proved theorem will live), `source` (which
advisory or audit asked for it), `blocker` (what stops the proof today),
and `goldens` (whether discharging it moves goldens).

`lake env lean --run scripts/owed.lean` prints the queue and enforces the
ratchet: one hole per record, every record named in PLAN.md, no import
from the gated library. The definitions below are measures the statements
need (counting functions over public engine types); they specify inputs
and outputs, they do not duplicate any engine definition.
-/

namespace Obligations

open LeanTex.Core
open LeanTex.Core.Ir
open LeanTex.Core.Layout

/-- Ink characters: what conservation counts. Whitespace becomes glue, the
no-break space a fixed kern's glyph, and the soft hyphen a discretionary —
none of them stable on both sides of layout — so all are outside the
measure. -/
def inkChars (s : String) : List Char :=
  s.toList.filter fun c =>
    !(c.isWhitespace || c == ' ' || c == '\u00a0' || c == '\u00ad')

/-- The fragment of the IR the weak conservation statement ranges over:
a paragraph of plain text runs. -/
def plainPara : Ir.Block → Prop
  | .para xs => ∀ x ∈ xs, ∃ s, x = Ir.Inline.text s
  | _ => False

/-- The ink a document's paragraphs declare, in order. -/
def docInk (doc : Ir.Doc) : List Char :=
  doc.body.toList.flatMap fun b =>
    match b with
    | .para xs => inkChars (Ir.plainText xs)
    | _ => []

/-- The ink a shipped segment carries. -/
def segInk : Seg → List Char
  | .run _ _ _ _ glyphs _ _ _ => inkChars (String.ofList (glyphs.toList.map (·.2)))
  | _ => []

def lineInk (l : LineOut) : List Char := l.segs.toList.flatMap segInk

def pageInk (p : PageOut) : List Char := p.lines.toList.flatMap lineInk

/-- The ink an entire layout run ships, in page order. -/
def outInk (o : Out) : List Char := o.pages.toList.flatMap pageInk

/-- The diagnostics that name a legal drop: a glyph no face covers. A run
that emitted none of them dropped nothing it did not report. -/
def dropped (o : Out) : Bool :=
  o.diags.any fun d => d.code == "E0405" || d.code == "W0009"

-- owed: emission_conservation_paras
-- owner: LeanTex.Core.Layout
-- source: arch-provable I4 (the theorem whose absence let six user-visible defects ship); arch-faithful refactor 3
-- blocker: this is the weak public form. The strong form — #(renderable leaves of a block) = #(Op.para emitted by collectBlock) — is unstatable outside Layout.lean: `Acc`, `Op`, `collectBlock` are private, and `Acc` is one 14-field record (arch-provable R3 splits it). Proving even this form needs `itemsOfInlines` refactored into folds returning (items, dropped) with dropped fully reported (arch-faithful R3) and `B`'s writers narrowed to commit/pushSibling/finishPage.
-- goldens: no
/-- Emission conservation, weak public form: a document of plain text
paragraphs (no head, no foot, no hyphenation) ships exactly the ink it
declares, in order, unless a diagnostic named the dropped glyph. -/
theorem emission_conservation_paras
    (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc)
    (hplain : ∀ b ∈ doc.body, plainPara b)
    (hhead : doc.head = none) (hfoot : doc.foot = none)
    (hclean : dropped (Layout.run geom fs none doc) = false) :
    outInk (Layout.run geom fs none doc) = docInk doc := by
  sorry

-- owed: page_background_survives
-- owner: LeanTex.Core.Layout
-- source: arch-provable I5 (page conservation; the fill-vanishing bug — B.commit rebuilt the page with only its lines, PLAN 2026-09-16 themed entry — is its counterexample)
-- blocker: this is the weak observable form. The strong form — lines+fills committed to `B` equal lines+fills in `B.pages` after the final finishPage — is unstatable outside Layout.lean: `B` is private and 18+ fields wide, with `pageShrink` maintained half in placeLine and half in commit. Provable once `B`'s writers are the named trio.
-- goldens: no
/-- Every page of a document that declares a `bg` palette entry ships a
full-page fill: what the walk attaches to a page survives to that page's
output, observed at the page background. -/
theorem page_background_survives
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (hbg : (doc.palette.find? "bg").isSome = true) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages,
      ∃ f ∈ p.fills.toList,
        f.x = 0 ∧ f.y = 0 ∧ f.w = geom.pageW ∧ f.h = geom.pageH := by
  sorry

/-- The handout pages one block owes: one per overlay step of a frame,
none for anything else. The measure of the numbering statements. -/
def frameSteps : Ir.Block → Nat
  | .frame _ _ _ body => max 1 (Ir.maxStepBlocks body)
  | _ => 0

/-- A deck whose top level is only countable frames in audit-numbering's
sense: non-standout, not the golden-valign title page, visibly titled.
What the numbering statements range over. -/
def framedDeck (doc : Ir.Doc) : Prop :=
  doc.body ≠ #[] ∧ ∀ b ∈ doc.body, ∃ title valign body,
    b = Ir.Block.frame title false valign body ∧ valign ≠ Ir.VAlign.golden ∧
      Ir.plainText title ≠ ""

-- owed: pages_count_frame_steps
-- owner: LeanTex.Core.Layout
-- source: audit-numbering, whose refactor 1 has since LANDED (its model: a frame yields ≥1 pages — steps, spills; this is the page-count face of it); arch-provable I4's page side
-- blocker: partly cleared under us. `framesSeen`/`framesTotal` are gone and `Ir.frameNumbers`/`Ir.frameCount` are public, so the counting side is statable directly and audit-numbering's T2–T4 are proved there. What this weak form still owes is the page side — that the page count equals the summed overlay steps — which needs the collect walk's induction, i.e. the Acc split (arch-provable R3). Restate over frameNumbers when discharging.
-- goldens: no
/-- Numbered pages are exactly the countable ones, weak form: a deck of
titled countable frames ships one page per overlay step, `frameSteps` many
in total, when no diagnostic reported a dropped glyph. -/
theorem pages_count_frame_steps
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (hclass : doc.docClass = "slides")
    (hframes : framedDeck doc)
    (hclean : dropped (Layout.run geom fs pats doc) = false) :
    (Layout.run geom fs pats doc).pages.size
      = doc.body.foldl (fun n b => n + frameSteps b) 0 := by
  sorry

-- owed: frame_pages_footed
-- owner: LeanTex.Core.Layout
-- source: audit-numbering T2's page face, whose refactor 1 has since LANDED: its countable predicate (non-standout, non-golden) is why framedDeck excludes the title page — a golden frame's pages bear no footer, and this statement stays true across that landing; the chrome-footer slice (PLAN 2026-09-17)
-- blocker: the density half is discharged elsewhere — `frameNumbers_gapless` and `frameNumbers_last_is_count` are theorems now, and footer presence is `frameNum.isSome`, so a non-countable frame provably has no number to show. What remains is page-to-frame attribution, which `Out` still does not carry: publicly statable only as “every page of a footed countable-frame deck is footed”.
-- goldens: no
/-- One numbering, weak form: in a deck with a chrome footer and no
`\runningfoot` override, every shipped page of a titled non-standout frame
carries a chrome foot. -/
theorem frame_pages_footed
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (hclass : doc.docClass = "slides")
    (hfoot : doc.foot = none) (hchrome : doc.chrome.hasFooter = true)
    (hframes : framedDeck doc)
    (hclean : dropped (Layout.run geom fs pats doc) = false) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages, p.foot.isSome = true := by
  sorry

/-- The document the engine itself elaborates from a minimal deck that
installs the named theme: the real pipeline (lex → parse → compat → elab),
so every statement over it ranges over what `\theme` actually installs —
never a transcription. -/
def themedDoc (name : String) : Ir.Doc :=
  (Elab.run "owed.tex"
    ("\\documentclass{beamer}\n\\theme{" ++ name ++ "}\n" ++
     "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}\n")).1

-- owed: builtin_palette_contract_engine
-- owner: LeanTex.Core.Contrast
-- source: arch-provable I2 (theme contract over engine values; Contrast.molochResolved/plainResolved are the spec copies this deletes)
-- blocker: half discharged under us. Typed theme values landed (arch-provable R2): the bundle constants are now real values, the transcriptions are deleted, and `builtin_designs_legible` proves the contract over `bundlePalette` by `decide`. What is still owed is the stronger reading stated here — the contract over what `\theme` installs *through the elaborator* — and that remains blocked for the original reason: `decide` cannot evaluate `Elab.run`. Discharging it needs the installed palette to be reachable without running the elaborator in the kernel, not another refactor of Theme.
-- goldens: no
/-- The contrast contract holds for what `\theme` installs, for every
shipped bundle — over the engine's values, not a transcription of them. -/
theorem builtin_palette_contract_engine :
    ∀ t ∈ Theme.builtin,
      Contrast.paletteContract (themedDoc t.name).palette = true ∧
      Contrast.coveredContract (themedDoc t.name).palette = true := by
  sorry

-- owed: titlepage_align_declared_engine
-- owner: LeanTex.Core.Theme
-- source: arch-design I2 (furniture alignment is declared, never a constant; consumes the once-unread `separator`)
-- blocker: same as builtin_palette_contract_engine — bundle styles are surface strings, so the statement must go through the elaborator, which `decide` cannot evaluate. Unblocked by arch-provable R2 (typed theme values).
-- goldens: no
/-- Every shipped bundle that styles the title page declares its alignment
and its separator — the moloch title matter is ragged left with a rule by
declaration, not by a backend constant. -/
theorem titlepage_align_declared_engine :
    ∀ t ∈ Theme.builtin,
      match (themedDoc t.name).styles.find? "titlepage" with
      | some st => st.align.isSome ∧ st.separator.isSome
      | none => True := by
  sorry

-- owed: heading_hierarchy
-- owner: LeanTex.Core.Layout
-- source: arch-design I3 (hierarchy from the scale, visible at every base size)
-- blocker: false as the code stands — `sectionSize` is three loose constants (pt 14 / pt 12 / fontSize), so at a 12 pt base the subsection equals its body and past a 14 pt base a section sets smaller than its body. Unblocked by arch-design R3: sectionSize via `Ir.sizeScale` lookups (Large/large/normalsize, article.cls's own mapping); then this follows from `sizeScale_monotone`.
-- goldens: yes — headings shift ~0.4 pt (Large is 14.4, the constant is 14)
/-- Heading hierarchy: at every positive base size a section sets strictly
larger than a subsection, and no heading sets smaller than its body. -/
theorem heading_hierarchy (g : Geom) (hfs : 0 < g.fontSize) :
    sectionSize g 1 > sectionSize g 2 ∧ sectionSize g 2 ≥ g.fontSize := by
  sorry

-- owed: unwrap_item_steps_text
-- owner: LeanTex.Core.Ir
-- source: arch-faithful I1 (dim/shade conservation is proved in Ir.lean; this is the one remaining public IR-to-IR walk without its conservation theorem)
-- blocker: none structural — the same accumulator-lemma-then-mutual-induction pattern as `dimBlocks_text`; the chain lemmas (`plainTextList_append`, `blockTextList_chain`) are private to Ir.lean, so the proof lands there, not here.
-- goldens: no
/-- Unwrapping item steps loses no text: the marker pre-pass flattens a
leading `\item<2->` wrapper, it never drops the item's content. -/
theorem unwrap_item_steps_text (xs : Array Ir.Block) :
    Ir.blocksText (Ir.unwrapItemSteps xs) = Ir.blocksText xs := by
  sorry

-- owed: ordered_marker_shows_order
-- owner: LeanTex.Core.ListMark
-- source: arch-faithful I4 (the census's marker-with-kind fact, as a theorem; `enumLabel_inj` already proves two indices never share a label — this adds that the marker content IS the label)
-- blocker: none — expected dischargeable by unfolding; stated so the census fact is owed as a theorem, not held only by fixture tests.
-- goldens: no
/-- An ordered list's marker shows its order: the marker content of item
`n` is exactly the level's numbering label. -/
theorem ordered_marker_shows_order (level n : Nat) (covered : Char → Bool) :
    Ir.plainText (ListMark.marker true level n covered)
      = ListMark.enumLabel level n := by
  sorry

-- owed: take_args_consumes_forward
-- owner: LeanTex.Core.Elab
-- source: arch-provable I6; PLAN's phase-split design (the measure: definition-time expansion limit, then suffix length)
-- blocker: `takeArgs` is one of the elaborator's three tracked non-total functions — opaque to the checker, so nothing about it is provable as written. This is the progress half of its termination measure (the returned index never rewinds), stated now so the phase split (arch-provable R5) has its contract; the split restates it over the total Phase-A definitions and discharges it structurally.
-- goldens: no
/-- Argument consumption only moves forward: the index `takeArgs` returns
is never before the one it was given — the suffix-length half of the
elaborator's termination measure. -/
theorem take_args_consumes_forward
    (ctx : Elab.Ctx) (params : Array Elab.Param) (name : String)
    (raws : Array Parse.Raw) (start : Nat) (pos : Pos) (st : Elab.ESt) :
    start ≤ ((Elab.takeArgs ctx params name raws start pos).run st).1.2 := by
  sorry

end Obligations
