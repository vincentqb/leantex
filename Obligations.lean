import LeanTex.Core.Layout
import LeanTex.Core.Loop
import LeanTex.Core.Contrast
import LeanTex.Core.Theme
import LeanTex.Core.Elab
import LeanTex.Core.Pdf
import LeanTex.Core.PdfCensus

/-!
# The owed theorems: obligations stated, proofs open

Every declaration here is an unproved proposal about the engine's own
functions. Type checking keeps its names and types current; it does not
establish that the proposal is true. Some have recorded counterexamples
and need corrected specifications before a proof is possible.

This module is a queue, not a home. It is its own lake target
(`lake build Obligations`), outside the default build and outside
`lake test`; nothing in `LeanTex/` may import it (the pre-commit hook and
`scripts/owed.lean` both check, mechanically). A discharged obligation
moves into the module that owns it, with a real proof, and its hole
disappears from here.

Each obligation carries a record the ratchet reads — five consecutive
comment lines, `owed` (a unique, nonempty name),
`owner` (where the proved theorem will live), `source` (which
advisory or audit asked for it), `blocker` (what stops the proof today),
and `goldens` (whether discharging it moves goldens).

`lake env lean --run scripts/owed.lean` prints the queue and enforces the
ratchet: one hole per named record, no duplicate names, no import
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
  | .run _ _ _ _ glyphs _ _ _ _ _ _ => inkChars (String.ofList (glyphs.toList.map (·.2.1)))
  | _ => []

def lineInk (l : LineOut) : List Char := l.segs.toList.flatMap segInk

def pageInk (p : PageOut) : List Char := p.lines.toList.flatMap lineInk

/-- The ink an entire layout run ships, in page order. -/
def outInk (o : Out) : List Char := o.pages.toList.flatMap pageInk

/-- The diagnostics that name a legal drop: a glyph no face covers. A run
that emitted none of them dropped nothing it did not report. -/
def dropped (o : Out) : Bool :=
  o.diags.any fun d => d.code == "E0405" || d.code == "W0009"

/-- The ink the lines attributed to structure leaf `k` ship, in page order
(`LineOut.leaf`, the attribution channel). -/
def attributedInk (o : Out) (k : Nat) : List Char :=
  o.pages.toList.flatMap fun p =>
    (p.lines.toList.filter (·.leaf == some k)).flatMap lineInk

/-- The ink of the top-level block whose first leaf is `k`: every leaf of
the root child opening at `k`, as `Struct.leavesOne` enumerates them;
empty when no block opens there. -/
def blockLeafInk (t : Struct.Tree) (k : Nat) : List Char :=
  (t.children.toList.filterMap fun n =>
    let ls := Struct.leavesOne #[] n
    match ls[0]? with
    | some (id, _) =>
      if id == k then some (ls.toList.flatMap fun (_, l) => inkChars l.census) else none
    | none => none).flatten

-- owed: lines_attributed_covers
-- owner: LeanTex.Core.Layout
-- source: pdf-tagging audit "theorems (owed)"; SYNTHESIS §e W2.8 (the attribution channel indexes the structure tree's leaf array); PLAN 2026-09-21 modern-output entry, wave 2's named owed statements
-- blocker: Layout.lines_attributed_projects now preserves the actual shipment's attributed lines, ink, geometry and page order through both postlude passes. Collection and placement still need an invariant connecting every non-furniture ink line to a valid Struct leaf, stated inside Layout over their own state; postlude preservation cannot supply a missing attribution.
-- goldens: no
/-- Attribution covers the ink, weak public form: in a document of plain
text paragraphs, every line that is not furniture and ships ink names a
structure leaf, and the leaf is an index into the tree of the document
the pages set (`Struct.leaves (Struct.ofDoc (Layout.pdfView doc))`, the
array `structTree_leaves_id` numbers). The unrestricted form is false:
generated ink the tree does not census (the abstract heading, the
headline band, an `\item` with no text) ships lines with no leaf. -/
theorem lines_attributed_covers
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns) (doc : Ir.Doc)
    (hplain : ∀ b ∈ doc.body, plainPara b) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages, ∀ l ∈ p.lines,
      l.furniture = false → lineInk l ≠ [] →
        ∃ k, l.leaf = some k ∧
          k < (Struct.ofDoc (Layout.pdfView doc)).leaves.size := by
  sorry

-- owed: lines_attributed_text
-- owner: LeanTex.Core.Layout
-- source: pdf-tagging audit "theorems (owed)"; SYNTHESIS §e W2.8; PLAN 2026-09-21 modern-output entry, wave 2's named owed statements
-- blocker: Layout.lines_attributed_projects preserves attributed lines exactly through the actual public run. The remaining proof is the progress-indexed body census through collection and placement, with per-paragraph conservation as in emission_conservation_paras and the Struct leaf order. No copy of either loop is needed.
-- goldens: no
/-- Attribution is a census, weak public form: in a document of plain text
paragraphs, set without hyphenation and dropping no glyph, the ink of the
lines attributed to leaf `k`, in page order, is exactly the ink of the
leaves of the block that opens at `k` — and nothing is attributed to a leaf
no block opens at. -/
theorem lines_attributed_text
    (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc)
    (hplain : ∀ b ∈ doc.body, plainPara b)
    (hclean : dropped (Layout.run geom fs none doc) = false) :
    ∀ k, attributedInk (Layout.run geom fs none doc) k
      = blockLeafInk (Struct.ofDoc (Layout.pdfView doc)) k := by
  sorry

-- owed: emission_conservation_paras
-- owner: LeanTex.Core.Layout
-- source: arch-provable I4 (the theorem whose absence let six user-visible defects ship); arch-faithful refactor 3
-- blocker: The statement is false as written: outInk includes the automatic page number even when head and foot are absent (LayoutContracts.counterexamples). Conservation must count body ink separately from furniture. The actual collection and placement loops still need progress-indexed body-census invariants; the loop contracts alone do not supply them.
-- goldens: no
/-- Staged body-conservation claim. This measure also counts automatic
page numbers, so the statement is false even without a declared header or
footer. The replacement must separate body ink from furniture. -/
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
  doc.body ≠ #[] ∧ ∀ b ∈ doc.body, ∃ title valign br body,
    b = Ir.Block.frame title false valign br body ∧ valign ≠ Ir.VAlign.golden ∧
      Ir.plainText title ≠ ""

-- owed: pages_partition_frames
-- owner: LeanTex.Core.Layout
-- source: audit-numbering's model, restated as a partition over `PageOut.frame` when refactor 1 (the frame id on `PageOut`, written at `finishPage`) landed — supersedes pages_count_frame_steps, whose count is this statement summed over the frames; arch-provable I4's page side
-- blocker: The statement is false as written: a frame can spill beyond its overlay count, and frameRestart can give distinct source frames the same displayed number (LayoutContracts.counterexamples). Partition by source identity and actual spill count, then relate the driver and placement loops to that measure. Displayed numbering is not a source identifier.
-- goldens: no
/-- Staged frame-partition claim. Overlay count excludes spill pages, and
displayed frame numbers can restart. A correct partition needs source
frame identity and the actual number of pages it ships. -/
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
-- blocker: The statement is false for numbered standout pages, which deliberately select no chrome footer (LayoutContracts.counterexamples). The replacement premise must use the shared footer decision, not frame.isSome. Placement now preserves the selected page metadata; connecting every collected frame opening to that selection remains owed.
-- goldens: no
/-- Staged footer claim. Numbered standout pages deliberately omit chrome;
the premise must use the shared footer selection, not numbering alone. -/
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
      | .run _ color _ _ glyphs _ _ _ _ ground _ =>
        unless glyphs.isEmpty do
          out := out.push (color, ground.getD defaultBg)
      | _ => pure ()
  return out

-- owed: contrast_judged_complete
-- owner: LeanTex.Core.Contrast
-- source: the a11y-contract slice (the user's ask: weak accessibility in any document is proven, never suspected) — the completeness half of the W0315/W0345 judge, whose per-bundle contracts are already theorems; restated over the declared ground when refactor 2 (`ground` on `Seg.run`, written at the resolving sites) landed
-- blocker: The document plan omits computed covered colours and picture paint, so this statement is false (contrastContractChecks). Contrast.shippedPaints_exact and Contrast.layoutAudit_covers now enumerate every actual nonempty glyph run with its address, preserving repeated paint. A complete accessibility judge still needs effective local grounds and covered/decorative provenance; a missing recorded ground does not mean no fill is behind the run.
-- goldens: no
/-- Staged completeness claim for the document contrast plan. Computed
covered colours and picture paint falsify it. The placed-run audit now
covers those runs, but effective local grounds and policy still need a
complete contract. -/
theorem contrast_judged_complete
    (geom : Geom) (fs : Font.FontSet) (pats : Option Hyphen.Patterns)
    (doc : Ir.Doc) :
    ∀ p ∈ (Layout.run geom fs pats doc).pages,
      ∀ pr ∈ runPairs (Contrast.effectivePair doc).bg p,
        (Contrast.judgedPairs doc).contains pr = true := by
  sorry

-- Flate.inflate_deflate_id proves the complete public zlib round trip.
-- Flate.inflate_deflate_bounded_id permits any sufficient output capacity;
-- both compose the actual encoder and decoder without external premises.

-- owed: write_fonts_embedded
-- owner: LeanTex.Core.Pdf
-- source: the pdf-census slice (modern output, wave 1 S2; pdf-objects T3/T4): `fonts.all_embedded` now reads the census of the bytes, so the claim that the writer's own output passes that census is the writer's to prove — today it is the executable witness "written pdf census: fonts embedded" in Tests/Backends and the pdffonts oracle over the corpus.
-- blocker: the unrestricted statement is false: 65,536 synthetic outline entries overflow a compressed object's 16-bit index; the writer's root/count still read, but object recovery fails and the font census returns an error. The representable domain must bound direct offsets and object-stream ids to 32 bits, compressed indices to 16 bits, and decoded structural streams to `PdfRead.maxDecoded`. `Pdf.fontObjects_links_exact` proves the actual writer's dictionary references for both font formats; `Pdf.fontObjects_census_contract` proves the census from recovered font dictionaries and descriptors. `PdfRead.parseVal_render_id` now proves full-consumption inversion under the independent recursive `Obj.Representable` domain. Reader recovery still needs the writer's dictionaries in that domain, `inflate_deflate_id`, Adler verification and object-stream lookup composition. Those internal facts are obligations, not external hypotheses that construction proves.
-- goldens: no
/-- Staged writer/census contract for image-free output. Its unrestricted
input domain is too wide: a compressed object index can exceed the field
the file declares. A representable-size domain and proof of reader
recovery are still owed. The component font-reference laws do not close
this claim about the bytes. -/
theorem write_fonts_embedded (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array PageOut) (info : Ir.Meta) (outline : Array OutlineEntry) :
    (PdfCensus.census (Pdf.write geom fs pages info {} outline)).map (·.fontsEmbedded)
      = .ok true := by
  sorry

-- owed: write_readXref_exact
-- owner: LeanTex.Core.Pdf
-- source: the pdf-conformance-gate slice (modern output, wave 1 S3; pdf-validation F/gap 1–2, S3 red 1–2): the engine's own reader accepts every file the engine writes — today the executable witness is the reference walk over every corpus PDF in Tests/PdfConformance (`walkPdf`) and the six mutants it refuses by name.
-- blocker: `Pdf.serialize_row_exact` now locates every emitted row's bytes, and `Pdf.Xref.row_fields_exact` proves all declared [1,4,2] fields read back under their width bounds. `PdfRead.parseVal_render_id` now proves full-consumption object inversion under `Obj.Representable`. These components do not yet prove `PdfRead.readXref`: the writer's trailer must satisfy that domain, and startxref discovery, stream decompression with Adler verification, and the xref row loop still need composition, including `inflate_deflate_id` and the reader's decoded-size limits. The current conclusion checks root/count only; it does not certify the locations or object-stream indices, which can overflow while that conclusion still holds.
-- goldens: no
/-- The writer and the engine's reader agree on the cross-reference
(`_exact`, artifact-specific: a fact of the file's own bookkeeping, with
no IR statement behind it): `readXref` follows `startxref` in every file
`Pdf.write` emits, finds the catalog at object 1, and the trailer's
`/Size` is exactly the listed objects plus the free object 0 — the count
`write` computed for its `/Index [0 size]`, read back from the bytes. -/
theorem write_readXref_exact (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array PageOut) (info : Ir.Meta) (imgs : Image.Store)
    (outline : Array OutlineEntry) (streams : Array (ByteArray × Option ByteArray)) :
    ∃ x, PdfRead.readXref (Pdf.write geom fs pages info imgs outline streams) = .ok x ∧
      x.root = some 1 ∧
      (x.trailer.bind (·.get? "Size")).bind PdfRead.Obj.int? = some (x.locs.size + 1) := by
  sorry

-- PdfRead.parseVal_render_id proves full-consumption inversion over
-- recursively representable objects. The rejected primitive, descendant
-- and dictionary-key spellings remain checked in the runtime suite.

-- The former arbitrary-statement order claim was false: two writes to the
-- same node name resolve differently when reversed (PictureContracts.checks).
-- Picture.NodePlan.place_order_agree proves commutation at evalNode's actual
-- resolving operations under independent reads and writes. This is not a
-- theorem about permutations of evalFixed's whole source/fixed-point walk.

-- Picture.nodeLabel_mem proves character provenance through the actual
-- salvage: literals, selected substitutions, elaborated math, or a named
-- generated floor. Literal punctuation is content, not a forbidden alphabet.

/-- The flow's own lines that carry ink: furniture stands in the margin by
design and the note apparatus belongs to the page, so neither is a line the
document's paragraphs declared. -/
def inkLines (o : Out) : List LineOut :=
  o.pages.toList.flatMap fun p =>
    p.lines.toList.filter fun l => !l.furniture && !l.note && lineInk l ≠ []

-- Layout.reflow_named proves that every split before an authored segment
-- end retains its paragraph-keyed diagnostic through the actual public run.
-- LayoutContracts.reflowChecks covers floats, columns, repeated paragraphs,
-- restarted frame counters, and the final-segment counterexample.

-- The former node-border claim used an arbitrary metric and identified a
-- label's owner by coordinates alone; neither premise is sound. The actual
-- producer contract, Picture.nodeExtent_covers, covers emitted labels with
-- the picture hull under cx.metric, absent an explicit bounding box.
-- Negative padding and authored text dimensions can put ink outside a node
-- border. PictureContracts.checks preserves those distinctions.

-- PictureContract.pictureKeys_named proves complete accounting over the
-- settings retained by Elab.prepare, including accumulated style definitions.
-- FrontendPictureContracts retains the counterexample to the raw-source
-- premise: compatibility preparation can discard a setting before drawing.

-- Body duplication does not double preamble diagnostics. The old source
-- doubling claim is refuted by elabWarningContractChecks. The proved
-- Elab.warnOnce_sites_exact counts one actual reporting call, keyed by code,
-- output and subject; it does not prove that every source loss reaches one.

/-- The ink baselines the flow ships, in page and line order: the measure a
vertical-monotonicity statement compares two runs by. -/
def inkBaselines (o : Out) : List Dim.Sp := (inkLines o).map (·.y)

-- owed: elementSpace_monotone
-- owner: LeanTex.Core.Layout
-- source: the paragraph-skip slice (PLAN 2026-09-24, the vertical-skip composition entry): inserting positive vertical glue between two paragraphs narrowed their separation, because the declared glue stood *in place of* the parskip it displaced rather than beside it. `Layout.skip_monotone` closes the half where the glue is a bare declared skip — `\vspace`, `\smallskip`, `Ir.gapBlock` — which is the half the defect was measured on and the half LaTeX's own `\vskip` semantics pin. The other half is still live and measured: an element's own space, the `\addvspace` path, still replaces the peer default, so `\style{itemize}{ before = 1pt }` after a paragraph ships a 13 pt separation where the undeclared peer gap is 18 pt — a positive declaration narrowing a gap by 5 pt. Correcting it is not the same one-line change: the engine's furniture rhythm constants (`Ir.titleBarGap`, the caption gaps, `Ir.headingBeforeDefault` and its parskip-growth arm) were tuned against the replacing behaviour, and `default_rhythm_multiples`/`caption_gaps_rhythm` pin those multiples, so the fix is a re-derivation of the furniture rhythm against a parskip that always adds, not a swap of one composition operator.
-- blocker: The statement is false across pagination: positive glue can move the last line onto a new page, lowering its page-local y coordinate (LayoutContracts.counterexamples). The replacement needs physical-page coordinates or a same-page premise, a fixed preceding layout, and a nonnegative resolved length rather than only its sp component. The actual addvspace composition and body placement still need their corresponding local monotonicity proof.
-- goldens: no
/-- Staged spacing monotonicity. Page-local baselines can decrease when
positive glue causes a page break, and a nonnegative `sp` component does
not constrain the whole resolved length. A local contract needs a fixed
preceding layout and either physical coordinates or a same-page premise. -/
theorem elementSpace_monotone
    (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc)
    (a b : Array Ir.Inline) (g : Ir.Sourced Dim.SymGlue)
    (hpos : (0 : Int) ≤ g.value.width.sp) :
    ((inkBaselines (Layout.run geom fs none
        { doc with body := #[.para a, .para b] })).getLast?.getD 0 : Int)
      ≤ (inkBaselines (Layout.run geom fs none
          { doc with body := #[.para a, .spaced g #[.para b]] })).getLast?.getD 0 := by
  sorry

/-- How far the glyphs of a label's text reach above their baseline, read
from the face's own outlines rather than from any declared metric: the
measure the containment claim below is about, and exactly what
`Layout.labelVExtent` declines to consult. Font units scaled to the label's
size — the arithmetic only, no engine decision restated. The body face,
because that is the face a plain label sets in; a label switching face
mid-line is the same claim over more runs. -/
def labelInkReach (geom : Geom) (fs : Font.FontSet) (content : Array Ir.Inline)
    (scale : Nat) : Dim.Sp :=
  let font := fs.body
  let size := geom.fontSize * (scale : Int) / 1000
  (Ir.plainText content).toList.foldl (fun acc ch =>
    match font.gid ch with
    | some g =>
      match font.yExtent g with
      | some (_, hi) => max acc (hi * size / (font.unitsPerEm : Int))
      | none => acc
    | none => acc) 0

-- owed: ink_covered_or_named
-- owner: LeanTex.Core.Layout
-- source: the label-centring slice (PLAN 2026-09-24, the what-cannot-move-a-baseline entry). A label's band is the face's declared cap height up and hhea descent down (`Layout.labelVStep`), and that band is read for two different jobs: it *places* the baseline, where being glyph-blind is the whole point (`Layout.label_centre_glyph_free`, the wobble's absence), and it is also the box a picture reserves space by (`Ir.Pic.labelInkBox` into `Ir.Pic.Picture.inkBbox`), where being glyph-blind means the box can be smaller than the ink. Measured on the three shipped faces at 10 pt: a diacritic inks 2.07–2.25 pt above the declared cap height (É in Source Serif Pro and Open Sans, Î in Fira Sans), and plain lowercase ascenders do too — six of `bdfhklt` in every face, by 0.51–0.79 pt — as do round capitals by their overshoot (0.10–0.14 pt) and, in two faces of three, every fence (`(` by 1.56 pt in Fira Sans). The descent side is sound: no descender of `gjpqy` reaches below the declared descent in any of the three. So the overflow is one-sided and it is the common case, not the exception, which is what makes this owed rather than fixed: the two consumers want different bands, and the placement band must stay where it is. The design being protected is the one the report named — an extent-derived box exists so diacritics and descenders cannot clip or collide (CSS 2.1 §10.6.1, css-inline-3 §5.2) — so the honest resolution is a second, wider *declared* band for containment (hhea ascent, which is the room a face reserves for exactly this and which all three faces' worst glyph fits inside) with the residue named, never a crop and never a diagnostic on every label carrying a `b`. The in-suite witness is the third group of `labelBaselineChecks`, which pins the overflow above the cap and the clearance under the descent as the numbers they are.
-- blocker: Layout.labelInk_projects now measures the segments returned by the actual producer, and Layout.labelLine_covers bounds every produced glyph in the separate reserved glyph box after page placement, without treating a cap-height band as containment. This older statement still uses labelInkBox and plain text measured in the body face. It needs the real per-run glyph measure and reserved box, plus a contract connecting each source label to the producer result or a named refusal through the picture walk.
-- goldens: yes
/-- Staged source-label coverage claim. The producer now separates the
font band used for placement from measured glyph bounds used for space
reservation. This statement still measures plain text in one face against
the placement box; its replacement must follow the actual producer's
segments and reserved glyph box through the picture walk. -/
theorem ink_covered_or_named
    (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc) (pic : Ir.Pic.Picture)
    (x y : Dim.Sp) (content : Array Ir.Inline) (c : Ir.Color) (scale : Nat)
    (al : Ir.Pic.LabelAlign)
    (hpic : Ir.Block.picture pic ∈ doc.body)
    (hs : Ir.Pic.Shape.label x y content c scale al ∈ pic.shapes) :
    Ir.Pic.labelBaseline y al (Layout.labelMetric geom fs {} content scale)
          + labelInkReach geom fs content scale
        ≤ (Ir.Pic.labelInkBox x y al
            (Layout.labelMetric geom fs {} content scale)).2.2
      ∨ (Layout.run geom fs none doc).diags.any
          (fun d => d.subject == some (Ir.plainText content)) := by
  sorry

/-- A synthetic document that uses one control-plane command with its
declared number of keyword groups, standing between two words of invented
prose. The keyword is a word no prose would carry, so its presence in the
elaborated body is exactly the leak. -/
def ctrlProbe (name : String) (groups : Nat) : String :=
  "\\documentclass{article}\n\\begin{document}\nalpha\n\\" ++ name ++
    String.join (List.replicate groups "{zzkeyword}") ++
    "\nomega\n\\end{document}\n"

/-- The ink the elaborated body declares, as the engine's own walk reads it
(`Ir.blocksText`) — the measure a page's text is a rearrangement of. -/
def elabInk (src : String) : String :=
  Ir.blocksText (Elab.run "probe.tex" src).1.body

/-- `hay` carries `needle`, the repo's own substring reading. -/
def carries (hay needle : String) : Bool := (hay.splitOn needle).length ≥ 2

-- owed: ctrl_groups_never_ink
-- owner: LeanTex.Core.Compat
-- source: a probe paper gained the word "fullpage" as body ink. The engine's floor for a construct it cannot render is that construct's *content*, never its spelling (PLAN 2026-09-24, the diagnostic-recovery entry) — and for `\emph{text}` the content is prose, so the floor is right. For a control-plane command the argument is a keyword, and the same floor puts a stray word on the page: measured synthetically, `\setlayout{fullpage}` ships "fullpage" in both backends (pdftotext over the PDF and the HTML body agree), named only by a W0301 a reader may not look at. The recognised half of that surface is the first two conjuncts; the unrecognised half is the third and fourth, statable since `Ir.Doc.salvage` marked recovered ink (PLAN 2026-09-24, the salvage-census entry).
-- blocker: CompatContract.ctrl_groups_consumed_contract proves exact consumption by the actual dispatcher for all meaningFree/configSkip rows and preserves the unknown-control probe. Elab.elabInlines_option_run_exact proves the real inline recovery entry under independent resolver-miss premises. The full lex/parse/compat/elab probe and its salvage-to-diagnostic accounting still need composition; the old absence of inline equations is no longer the blocker.
-- goldens: no
/-- A recognised control-plane command's argument groups contribute no
character to the document's ink: the engine knows the command, so its
keywords are consumed, never recovered as prose. The probe stands the
command between two invented words, so the elaborated body is exactly those
two words — the keyword nowhere in it.

This is the invariant whose absence let `\PackageWarning{pkg}{msg}` ship its
package name and message as body text, and it binds every row of both
consuming tables rather than the six spellings that exposed it. The
complementary half — that an *unrecognised* command still keeps its groups,
so this is a named exception and not a licence to swallow content — is the
third conjunct.

The fourth is what the salvage census made statable, and it is the clause
that makes the third safe to want: the kept groups are *attributed*. Ink the
document did not declare is recorded as recovery under the command that
produced it, so the stray keyword on the page is separable from the author's
prose by a reader of the IR rather than only by a reader of the log. Without
it "the groups are kept" and "a control keyword leaked" are the same
observation. -/
theorem ctrl_groups_never_ink :
    (∀ row ∈ Compat.meaningFree,
      carries (elabInk (ctrlProbe row.1 row.2.1)) "zzkeyword" = false) ∧
    (∀ row ∈ Compat.configSkip,
      carries (elabInk (ctrlProbe row.1 row.2.1)) "zzkeyword" = false) ∧
    carries (elabInk (ctrlProbe "zzNotAControl" 1)) "zzkeyword" = true ∧
    (∀ s ∈ (Elab.run "probe.tex" (ctrlProbe "zzNotAControl" 1)).1.salvage,
      ((Elab.run "probe.tex" (ctrlProbe "zzNotAControl" 1)).2).any
        (·.subject == some s.subject) = true) := by
  sorry

-- The old raw-source content premise was false even after successful
-- parsing: invisible delimiters and layout parameters carry source
-- punctuation/digits but declare no glyphs (Tests.formulaFloorChecks).
-- Ir.formulaFloor_covers instead bounds the structural reading against the
-- independent parsed glyph census; source-to-parser conservation remains
-- outside that contract. Ir.formulaFloor_separates proves the former
-- fraction separator obligation without its nonempty-operand hypotheses.

-- The prefix LaTeX puts before a refused name on its way to a filename now
-- lives with the scan that reads it (`Compat.nameRefusalAsk`), where it is
-- closed against the code list rather than kept here by hand: a refusal
-- carries its name on `Diag.refused`, every code owes a firing witness, so
-- the codes that refuse names are enumerable from the registry of codes
-- itself (`nameRefusalRegistryChecks`). This file states the claim over that
-- registry and keeps no copy of it.

-- owed: nameRefusals_asked
-- owner: LeanTex.Core.Compat
-- source: theme-loading audit 2026-09-24, the generalised invariant: the defect was not about themes but about a refusal that never asked, and `\usefonttheme`/`\useinnertheme`/`\useoutertheme` sat one keystroke from the same bug
-- blocker: This per-diagnostic claim is false: native theme refusals require no file, package-option refusals can name supported packages, and expansion can introduce calls absent from the original raws. CompatContract.nameRefusals_asked now proves the actual loading-call contract for arbitrary positions, option groups, nonempty external package names and every themeAsking row. Connecting expanded requests, file results and final refusals still needs provenance through the driver.
-- goldens: no
/-- Staged name-refusal accounting. A diagnostic code alone cannot identify
a file-loading request: native themes and package-option refusals share
these codes, and expansion can introduce loading calls. The replacement
must follow the actual loading call and its request provenance. -/
theorem nameRefusals_asked (file : String) (raws : Array Parse.Raw) :
    ∀ d ∈ (Elab.runRaws file raws).2,
      ∀ p ∈ Compat.nameRefusalAsk,
        d.kind = p.1 →
          ∀ nm, d.refused = some nm →
            (Compat.localStyCandidates raws).contains (p.2 ++ nm) = true := by
  sorry

-- `Elab.titleStyle_spelling_agree` proves alias equivalence through the
-- production preamble and complete frontend at the selected declarative
-- body boundary. Global source equivalence is false: executable source
-- can inspect a spelling, as `elabTitleBoundaryChecks` demonstrates.

end Obligations
