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

-- Layout.pages_partition_frames partitions actual shipped pages by source
-- identity, including overlays and spill pages across counter restarts.
-- Layout.frame_pages_footed connects every frame page to its actual opening
-- and selected footer; a numbered standout may correctly select none.
-- LayoutContracts retains the counterexamples to the former statements.

-- The source-plan completeness claim was false for computed overlay ink
-- and picture labels; contrastContractChecks retains those counterexamples.
-- Contrast.contrast_judged_complete covers every actual placed run.
-- Check.pdfA11ySummary_clear_contract connects the PDF assertion to actual
-- size, weight and supported ground; unresolved grounds fail explicitly.

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

-- Pdf.write_readXref_exact proves readback of the actual producer bytes on
-- its representable-size domain. Pdf.writeChecked_readXref_exact discharges
-- those bounds for every successful checked write. The proof includes
-- startxref discovery, compression, checksum verification and row decoding.

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

-- Layout.Spacing.elementSpace_monotone proves ordering in the actual public
-- run from common preparation, resolved default compensation and numeric
-- line-fit conditions. Layout.Spacing.twoParagraphIncreasing_contract
-- constructs these premises from arbitrary document inputs on its supported
-- two-paragraph domain; it never assumes the output ordering it proves.
-- ElementSpacing retains counterexamples to the old unconditional claim:
-- replacing a larger default, signed relative lengths and page breaks.

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
