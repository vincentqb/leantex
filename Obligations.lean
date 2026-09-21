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
  | .run _ _ _ _ glyphs _ _ _ _ => inkChars (String.ofList (glyphs.toList.map (·.2)))
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
-- blocker: this is the weak public form. The strong form — #(renderable leaves of a block) = #(Op.para emitted by collectBlock) — is unstatable outside Layout.lean: `Acc`, `Op`, `collectBlock` are private, and `Acc` has grown to a 24-field record since this was written (arch-provable R3 splits it into reader/writer/state). Proving even this form needs `itemsOfInlines` refactored into folds returning (items, dropped) with dropped fully reported (arch-faithful R3) and `B`'s writers narrowed to commit/pushSibling/finishPage — then the collect-walk induction over roughly a dozen mutually threading collect* functions.
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

/-- A deck whose top level is only countable frames in audit-numbering's
sense: non-standout, not the golden-valign title page, visibly titled.
What the numbering statements range over. -/
def framedDeck (doc : Ir.Doc) : Prop :=
  doc.body ≠ #[] ∧ ∀ b ∈ doc.body, ∃ title valign body,
    b = Ir.Block.frame title false valign body ∧ valign ≠ Ir.VAlign.golden ∧
      Ir.plainText title ≠ ""

-- owed: pages_partition_frames
-- owner: LeanTex.Core.Layout
-- source: audit-numbering's model, restated as a partition over `PageOut.frame` when refactor 1 (the frame id on `PageOut`, written at `finishPage`) landed — supersedes pages_count_frame_steps, whose count is this statement summed over the frames; arch-provable I4's page side
-- blocker: the page side needs the collect walk's induction — the `Acc` split (arch-provable R3); the counting side is already proved on the IR (`frameNumbers_gapless`, `frameNumbers_last_is_count`), and the attribution now travels with the footer through the one `.foot` op.
-- goldens: no
/-- Numbered pages partition by frame: in a deck of titled countable
frames, every shipped page is attributed to a frame (the `_covers` half),
and frame k's pages number exactly its overlay steps — the page count of
the superseded weak form is this statement summed over the body. -/
theorem pages_partition_frames
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (hclass : doc.docClass = .slides)
    (hframes : framedDeck doc)
    (hclean : dropped (Layout.run geom fs pats doc) = false) :
    (∀ p ∈ (Layout.run geom fs pats doc).pages, p.frame.isSome = true) ∧
    (∀ i, (h : i < doc.body.size) →
      ((Layout.run geom fs pats doc).pages.filter
          (fun p => p.frame == some (i + 1))).size
        = frameSteps doc.body[i]) := by
  sorry

-- owed: frame_pages_footed
-- owner: LeanTex.Core.Layout
-- source: audit-numbering T2's page face; the chrome-footer slice (PLAN 2026-09-17); restated as a per-page fold over `PageOut.frame` when refactor 1 landed
-- blocker: `PageOut.frame` and `PageOut.foot` are written together at `finishPage` from the one `.foot` op a frame's opening pushes (content is some exactly when the frame bears a number, given the chrome), so the implication is definitional at the write site; what remains is the collect-walk induction connecting `doc.chrome` to the op stream — the `Acc` split (arch-provable R3).
-- goldens: no
/-- One numbering, per page: in a deck with a chrome footer and no
`\runningfoot` override, every page attributed to a countable frame
carries a chrome foot — a fold over the shipped pages, reading the
attribution `finishPage` writes beside the footer it judges. -/
theorem frame_pages_footed
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) (hclass : doc.docClass = .slides)
    (hfoot : doc.foot = none) (hchrome : doc.chrome.hasFooter = true) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages,
      p.frame.isSome = true → p.foot.isSome = true := by
  sorry

/-- The document the engine itself elaborates from a minimal deck that
installs the named theme: the real pipeline (lex → parse → compat → elab),
so every statement over it ranges over what `\theme` actually installs —
never a transcription. -/
def themedDoc (name : String) : Ir.Doc :=
  (Elab.run "owed.tex"
    ("\\documentclass{beamer}\n\\theme{" ++ name ++ "}\n" ++
     "\\begin{document}\n\\begin{frame}{T}\nx\n\\end{frame}\n\\end{document}\n")).1

-- owed: elab_inlines_option_run_dropped
-- owner: LeanTex.Core.Elab
-- source: recover-content (Tests/Layout.lean recoveryChecks, the test that wanted to be this theorem); the de-partial slices, whose point was making it statable
-- blocker: retried 2026-09-19 with elabBlocks total; the wall stands and budget is not the fix: proved in-module (private equations visible) via simp [elabInlines, elabInlinesFrom], the tactic still fails at maxHeartbeats 16000000 with maxRecDepth 4096 — the WF equation lemmas rewrite into their own results on the symbolic .word w token, so raising limits diverges rather than converges. Needs a staged per-arm rw script over one-step equation lemmas stated once in Elab.lean (public, so this file can drive them), normalizing the ground prefix before the symbolic tail — or the inline spine restated as a small-step function whose one-step equations are cheap.
-- goldens: no
/-- The W0341 arm's content claim, as a commutation: an unknown command's
leading `[...]` option run is not content, so elaboration with the run and
with the run deleted return the same inlines — no character of the run
reaches the elaborated output, whatever the run's text. The shipped-page
witness is `recoveryChecks` in Tests/Layout.lean. -/
theorem elab_inlines_option_run_dropped (w kept : String) (st : Elab.ESt) :
    ((Elab.elabInlines { file := "d" }
        #[.ctrl "zzz" ⟨1, 1⟩, .sym '[' ⟨1, 5⟩, .word w ⟨1, 6⟩, .sym ']' ⟨1, 7⟩,
          .group #[.word kept ⟨1, 9⟩] ⟨1, 8⟩]).run st).1
    = ((Elab.elabInlines { file := "d" }
        #[.ctrl "zzz" ⟨1, 1⟩, .group #[.word kept ⟨1, 9⟩] ⟨1, 8⟩]).run st).1 := by
  sorry

/-- Every (colour, ground) pair a page's glyph runs ship, the ground the
one the resolving site declared onto the run (`Seg.run`'s `ground`,
refactor 2: the palette epoch's `bg`, the frame-title bar, the standout
inversion) — field equality where this stood as geometric recovery (a
`groundUnder` scan of the fills below each baseline midpoint, deleted
with the refactor). `none` is the undeclared page, read as the judge's
effective surface — the convention `Contrast.effectivePair` applies. -/
def runPairs (defaultBg : Ir.Color) (p : PageOut) :
    Array (Ir.Color × Ir.Color) := Id.run do
  let mut out : Array (Ir.Color × Ir.Color) := #[]
  for l in p.lines do
    for s in l.segs do
      match s with
      | .run _ color _ _ glyphs _ _ _ ground =>
        unless glyphs.isEmpty do
          out := out.push (color, ground.getD defaultBg)
      | _ => pure ()
  return out

-- owed: contrast_judged_complete
-- owner: LeanTex.Core.Contrast
-- source: the a11y-contract slice (the user's ask: weak accessibility in any document is proven, never suspected) — the completeness half of the W0315/W0345 judge, whose per-bundle contracts are already theorems; restated over the declared ground when refactor 2 (`ground` on `Seg.run`, written at the resolving sites) landed
-- blocker: the geometric-recovery half is gone — the shipped pair is the declared pair, so this is `judged_pair_is_shipped`'s converse, statable at last: every pair the pages ship is a pair the judge weighed. What remains is the collect-walk induction relating the walk's ground writes to `judgedPairs`' enumeration — the `Acc` split (arch-provable R3), the same blocker as emission_conservation_paras.
-- goldens: no
/-- The contrast judge is complete over the shipped pages —
`judged_pair_is_shipped`'s converse: every glyph run `Layout.run` ships,
paired with the ground its resolving site declared onto it, is a pair
`Contrast.judgedPairs` enumerates. A colour pairing the reader sees that
the judge never weighed then does not exist, and weak contrast anywhere
is a warning, never a discovery. -/
theorem contrast_judged_complete
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages,
      ∀ pr ∈ runPairs (Contrast.effectivePair doc).bg p,
        (Contrast.judgedPairs doc).contains pr = true := by
  sorry

end Obligations
