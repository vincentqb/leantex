import LeanTex.Core.Layout
import LeanTex.Core.Loop
import LeanTex.Core.Contrast
import LeanTex.Core.Theme
import LeanTex.Core.Elab
import LeanTex.Core.Pdf
import LeanTex.Core.PdfCensus

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
-- blocker: the collect walk's equation lemmas landed (2026-09-24: `collectBlock`'s match split into per-arm functions, eleven non-recursive arms and six non-recursive interiors lifted out; `role_transparent_collect` is the witness that an arm now unfolds at the default budget, where generation previously exhausted whnf whatever the budget). That was necessary and is not sufficient. Two imperative loops still stand between the walk and the pages, and this statement must cross both: `run`'s top-level `for h : i in [0:doc.body.size]` over `doc.body`, which threads `acc` and is where a frame's number and its step pages are decided, and the placement pass over the staged op stream. Neither loop needs restating, though. CORRECTED 2026-09-24 (loop-reading layer): the premise that a `forIn`/`Id.run` loop has no equational theory is no longer true. `LeanTex.Core.Loop` reads one: `forIn_range_inv` carries a state invariant through a loop that may `break` (a `ForInStep.done` is the same channel as a `yield` for a safety property), and `bind_eq_of_inv` peels the loops of a chained `Id.run do` block one at a time. Neither needs the loop restated as a fold, and `Ir.floorMask_id` is the worked example — three loops, no change to the walk. What that layer does NOT reach, and what is therefore the live blocker here: a pure invariant is blind to how much of the input the loop has consumed, so it proves a `_covers`-shaped safety claim and not a census; and the state both loops thread is `Acc`, private to Layout, so the invariant cannot be *spelled* from outside the module. The remaining work is therefore two statements written inside Layout — the driver loop's invariant over `Acc`, and a progress-indexed form (invariant over the prefix consumed) for the counting half — not a refactor of either loop. The placement half stays definitional: `placeLine`'s `mk` closure copies `ParaJob.leaf` onto every line it commits (`placeLine_leaf_exact`), and the count comes from `Struct`'s own walk (`leafCount`), so what remains is that the walk's claims run over the body in `Struct.blocksRaw`'s order — which is the driver loop's order, hence the first of the two loops above
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
-- blocker: as `lines_attributed_covers` (the two loops between the walk and the pages, the collect-walk equation lemmas having landed 2026-09-24; the loops are now readable in place through `LeanTex.Core.Loop`, so what remains is a progress-indexed invariant over `Acc`, spelled inside Layout), plus the per-paragraph half of `emission_conservation_paras`: a paragraph's lines ship exactly its declared ink, which is exactly its node's leaf census (`structTree_text` per block)
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
-- blocker: the named refactors landed (2026-09-20: Rd/Acc reader split, B's writers the commit/pushSibling/finishPage trio, itemsOfInlines a fold of itemsOfTok with a first-class dropped ledger, the driver on placeFrom/runPost with page facts crossing at runPost_pages. 2026-09-24: the collect-walk arm split, so `collectBlock` unfolds one arm at a time — `role_transparent_collect` is the witness, and the equation-lemma wall this row named is down). What remains is not the walk: it is the two imperative loops on either side of it. `run`'s top-level `for h : i in [0:doc.body.size]` threads `acc` over `doc.body` with the frame numbering and the per-step collects inside it, and the placement pass folds the staged op stream into pages; neither needs restating. CORRECTED 2026-09-24 (loop-reading layer): the premise that a `forIn`/`Id.run` loop has no equational theory is no longer true. `LeanTex.Core.Loop` reads one: `forIn_range_inv` carries a state invariant through a loop that may `break` (a `ForInStep.done` is the same channel as a `yield` for a safety property), and `bind_eq_of_inv` peels the loops of a chained `Id.run do` block one at a time. Neither needs the loop restated as a fold, and `Ir.floorMask_id` is the worked example — three loops, no change to the walk. What that layer does NOT reach, and what is therefore the live blocker here is the conservation direction: this row is a census equality, and a pure loop invariant cannot express one (it cannot name the prefix consumed). So what is owed is a progress-indexed invariant — `P (prefix consumed) state`, whose conclusion at a `break` is a prefix rather than the whole body — written inside Layout, where `Acc` can be named. The two loops themselves are now readable as they stand. Note the arm split is not uniform and cannot be: Lean picks one recursive argument group for the mutual block and `collectAlt` recurses into two block arrays, so the recursive arms stay inline; well-founded recursion would trade this cheap wall for the WF-equation wall `elab_inlines_option_run_dropped` records
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
  doc.body ≠ #[] ∧ ∀ b ∈ doc.body, ∃ title valign br body,
    b = Ir.Block.frame title false valign br body ∧ valign ≠ Ir.VAlign.golden ∧
      Ir.plainText title ≠ ""

-- owed: pages_partition_frames
-- owner: LeanTex.Core.Layout
-- source: audit-numbering's model, restated as a partition over `PageOut.frame` when refactor 1 (the frame id on `PageOut`, written at `finishPage`) landed — supersedes pages_count_frame_steps, whose count is this statement summed over the frames; arch-provable I4's page side
-- blocker: the collect walk's equation lemmas landed (2026-09-24: `collectBlock`'s match split into per-arm functions, eleven non-recursive arms and six non-recursive interiors lifted out; `role_transparent_collect` is the witness that an arm now unfolds at the default budget, where generation previously exhausted whnf whatever the budget). That was necessary and is not sufficient. Two imperative loops still stand between the walk and the pages, and this statement must cross both: `run`'s top-level `for h : i in [0:doc.body.size]` over `doc.body`, which threads `acc` and is where a frame's number and its step pages are decided, and the placement pass over the staged op stream. Neither loop needs restating, though. CORRECTED 2026-09-24 (loop-reading layer): the premise that a `forIn`/`Id.run` loop has no equational theory is no longer true. `LeanTex.Core.Loop` reads one: `forIn_range_inv` carries a state invariant through a loop that may `break` (a `ForInStep.done` is the same channel as a `yield` for a safety property), and `bind_eq_of_inv` peels the loops of a chained `Id.run do` block one at a time. Neither needs the loop restated as a fold, and `Ir.floorMask_id` is the worked example — three loops, no change to the walk. What that layer does NOT reach, and what is therefore the live blocker here: a pure invariant is blind to how much of the input the loop has consumed, so it proves a `_covers`-shaped safety claim and not a census; and the state both loops thread is `Acc`, private to Layout, so the invariant cannot be *spelled* from outside the module. The remaining work is therefore two statements written inside Layout — the driver loop's invariant over `Acc`, and a progress-indexed form (invariant over the prefix consumed) for the counting half — not a refactor of either loop. Both halves of this row live in those loops: the frame attribution is decided in the driver loop (it sets `acc.frameNum` per top-level block and re-enters `collectBlock` once per overlay step), and the page side needs a frame-attribution analogue of the BgStep pack over the `.foot`-op stream in the placement loop. The counting side is already proved on the IR (`frameNumbers_gapless`, `frameNumbers_last_is_count`)
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
-- blocker: `PageOut.frame` and `PageOut.foot` are written together at `finishPage` from the one `.foot` op a frame's opening pushes (`collectFrameOpen`, where content is some exactly when the frame bears a number given the chrome), so the implication is definitional at the write site. The collect-walk equation lemmas landed 2026-09-24 and the walk half was attempted: `chromeFoot_isSome` goes through (the chrome fields are set once by `run` and no arm writes them, so `Acc.chromeFoot` answers the same for the whole document), and the op-stream invariant is stateable. It met the zeta-expansion trap instead — `collectFrameOpen` is a `let`-chain, so `unfold` produces a `have`-chain `split` cannot see through, and `simp only` then leaves the membership goal in a shape the case analysis does not match. That is the factorization to do first: `collectFrameOpen` restated so the pushed op is a named value the statement can read, rather than a `let`-bound intermediate. Past it stand the two loops `emission_conservation_paras` names — the driver loop connecting `doc.chrome` to the op stream, and the placement fold carrying `curFoot`/`curFrame` onto each closing page. Both are now readable in place: this row is a per-page implication, not a census, so `Loop.forIn_range_inv` plus `Loop.bind_eq_of_inv` are the right shape, and the invariant ("every page closed so far carries a foot") only needs spelling where `Acc` can be named — inside Layout
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
-- blocker: the geometric-recovery half is gone — the shipped pair is the declared pair, so this is `judged_pair_is_shipped`'s converse. The collect-walk equation lemmas landed 2026-09-24 (the arm split; `role_transparent_collect` is the witness), so the walk's ground writes can now be opened one arm at a time. What remains is relating those writes to `judgedPairs`' enumeration across the two imperative loops `emission_conservation_paras` names: the driver loop, which re-enters the walk per overlay step and so may write a ground more than once per frame, and the placement fold, which is where a run's `ground` reaches a page. Both are readable in place now (`LeanTex.Core.Loop`), and this row is the shape that layer fits best — a membership claim, preserved by every step, so a pure invariant carries it. It is blocked only on being written where `Acc` is nameable: inside Layout, exported as the corollary this file reads. The judge's titled-bar default is no longer among the remainder: both sides resolve through `Contrast.titledGround`, held by `titled_ground_agree` and by the shipped-ground rows in Tests/Themes (titledGroundChecks)
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

-- owed: inflate_deflate_id
-- owner: LeanTex.Core.Flate
-- source: the build-cache slice (2026-09-21 survey wave): the engine grew a real compressor, and it owns both halves of the round trip — deflate emits only symbols inflate's tables decode, so the identity is the engine's to prove, not an interop hope. The executable oracle is scripts/flate-fuzz.lean (adversarial and random inputs, the fixtures' decoded planes, every stream cross-checked against a foreign inflater); the in-suite witnesses are the deflate-roundtrip rows in Tests/Backends.
-- blocker: the component algebra now has proofs: `Flate.bitField_bits_exact` and `Flate.pushU_read_exact` cover bit spelling and reading after a bounded write; `Flate.mkHuff_counts_exact`, `Flate.canonCodes_reverseBits_exact` and `Flate.push_huff_decode_exact` cover code-length counts and canonical symbol encoding; `Flate.tokenize_covers` and `Flate.backref_copy_exact` cover source progress and overlapping copies. The remaining work is composing these contracts through the actual zlib/block headers, code-length prelude, constructed Huffman tables, token emission/decoding, and end-of-block handling. The symbol contract assumes its canonical interval; proving the encoder and decoder construct matching intervals is still owed. The progress-indexed loop contracts expose consumed input, but do not supply this whole-stream inversion.
-- goldens: no
/-- The engine's inflate inverts its deflate on every input: the compressed
streams the PDF writer emits (content, fonts, image planes, metadata, the
object and cross-reference streams) decode back to exactly the bytes the
engine meant, by the engine's own decoder. -/
theorem inflate_deflate_id (b : ByteArray) :
    Flate.inflate (Flate.deflate b) b.size = .ok b := by
  sorry

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

/-- The lines a set of inlines declares: one per `\\`, plus the line the
last segment ends. The measure the re-flow statement compares the shipped
count against, over the public inline type. -/
def declaredBreakLines (xs : Array Ir.Inline) : Nat :=
  1 + xs.foldl (fun n x => match x with | .linebreak _ => n + 1 | _ => n) 0

/-- The flow's own lines that carry ink: furniture stands in the margin by
design and the note apparatus belongs to the page, so neither is a line the
document's paragraphs declared. -/
def inkLines (o : Out) : List LineOut :=
  o.pages.toList.flatMap fun p =>
    p.lines.toList.filter fun l => !l.furniture && !l.note && lineInk l ≠ []

-- owed: reflow_named
-- owner: LeanTex.Core.Layout
-- source: the declared-break slice (PLAN 2026-09-24, the re-flow entry): a deck's title shipped three lines where its author declared two and said nothing, because the engine had no code for "the shape you declared is not the shape shipped". W0386 and its step account (`Layout.warnReflow_accounts`) close the accounting half — the warning is pushed in the same step that reads the two counts — but the step is not the artifact: nothing yet states that the diagnostic survives the placement fold and reaches the `Out` a caller reads, so a future refactor between the two could drop it and leave the account green. The in-suite witness is the "a declared break destroyed by re-flow is named" row of `titleBreakChecks`, which reads `Layout.run`'s own diagnostics off a title whose first declared line does not fit, with three sibling rows pinning the floors (a break that holds is silent, a title declaring no break reports nothing, and W0005 stays silent because no line is overfull).
-- blocker: three factorizations, none of them a tactic. (1) There is no diagnostic-monotonicity notion across placement: `placePara` folds `placeParaLine` through `placeParaTrailer`, `placeLine`, `fitCommit`, `commit`, `finishPage`, `spillPage` and `warnSpill`, and while every one of them only appends, no lemma says so — `PagesExtend` is the shape this wants, a `DiagsExtend` beside it, which is what makes "pushed at the step" mean "present in the `Out`". Note (2026-09-24) that monotonicity *is* exactly the shape `LeanTex.Core.Loop`'s invariant carries — "the diagnostics so far contain d" is preserved by an appending step and survives a `break` — so once `DiagsExtend` is stated over the private state inside Layout, the loop between it and the `Out` is no longer an obstacle. (2) The shipped count is not connected to the breaker's: `breaks.size` is what `warnReflow` reads, and that it equals the ink lines a one-paragraph document ships needs the placement induction (one line committed per break, the same lines re-placed after a spill). (3) The declared count is not connected to the item stream: `declaredLines` counts forced penalties in `Array Item`, and that this is the `.linebreak` count of the inlines is `itemsOfInlines`'s own census — the `Acc`-split work the emission-conservation rows already wait on. The same three hold `warnSpill_accounts` (W0384) one level below its artifact, so discharging them closes both.
-- goldens: no
/-- A declared break is honoured or named, weak public form: for a document
that is one paragraph declaring at least one break and not ending in one,
if the flow ships more ink lines than the paragraph declared, the run's
diagnostics name the loss. The restriction to a single paragraph is what
makes the shipped count readable from `Out` at all — there is no channel
recording which paragraph a line came from, and adding one for this
statement alone would be the spec copy the queue forbids. -/
theorem reflow_named
    (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc) (xs : Array Ir.Inline)
    (hone : doc.body = #[Ir.Block.para xs])
    (hdecl : 2 ≤ declaredBreakLines xs)
    (hlast : ∀ e, xs.back? ≠ some (Ir.Inline.linebreak e))
    (hlost : declaredBreakLines xs < (inkLines (Layout.run geom fs none doc)).length) :
    (Layout.run geom fs none doc).diags.any (·.kind == .W0386) = true := by
  sorry

-- The former node-border claim used an arbitrary metric and identified a
-- label's owner by coordinates alone; neither premise is sound. The actual
-- producer contract, Picture.nodeExtent_covers, covers emitted labels with
-- the picture hull under cx.metric, absent an explicit bounding box.
-- Negative padding and authored text dimensions can put ink outside a node
-- border. PictureContracts.checks preserves those distinctions.

-- owed: pictureKeys_named
-- owner: LeanTex.Core.Elab
-- source: the stale picture-key gate (PLAN 2026-09-24, the unread-picture-key entry): the keys a `\tikzset` line leaves outside the rendered subset were named only under the declared refusal, on the premise that the real TikZ read them at the edge whenever a tool was configured. Native drawing killed that premise — the boundary became the fallback — and the diagnostic went silent for every picture the engine drew itself, an arrow-tip default among the keys dropped without a word on a 41-page deck. The gate now reads `Elab.enginePictures`, the count of `.picture` nodes the body walk produced, which is who drew it rather than which tool was configured. The in-suite witness is `pictureKeyGateChecks`, whose decisive row is a pair of builds differing by one `\pictures{ tool = none }` line: byte-identical PDFs, the same keys named on both sides, which is what separates the drawing from the honesty. Its siblings pin the two floors (a document whose every picture went whole to the boundary claims no loss, a document with no picture has no drawing to have lost them) and the mixed case the previous gate got wrong.
-- blocker: the same diagnostic-monotonicity wall `reflow_named` names, one module over: the naming happens inside `elabDoc`'s `EM` fold and nothing states that a diagnostic pushed there survives to the array `runRaws` returns — every step only appends and no lemma says so. (2026-09-24: "the array so far contains d" is precisely the shape `LeanTex.Core.Loop`'s invariant carries through a loop that may break, so this half is a statement to write inside Elab, not a wall.) Two further factorizations are specific to this statement. The gate's premise reads the elaborated body, so relating it to the source needs `elabBlocks`' own census (which `.picture` nodes a source produces), the `Acc` split again. And the fold over the set lines accumulates the style table, so a statement over more than one `\tikzset` line needs an invariant carried through that fold; the single-line form below avoids it, which is why it is stated weakly rather than generally.
-- goldens: no
/-- The keys a drawing did not read are named, weak public form: for a
document whose whole `\tikzset` census is one line, if the engine drew a
picture of its own then every key of that line the rendered subset does not
read carries a W0334 whose structured subject is the key. The restriction to
one set line is what keeps the unread set readable without re-running the
elaborator's style fold; the restriction to the engine's own drawing is the
statement's content, since a picture that went whole to the boundary is read
by the real TikZ and has no loss to name. -/
theorem pictureKeys_named (file : String) (raws : Array Parse.Raw)
    (pos : Pos) (keys : Array Parse.Raw)
    (hone : Compat.tikzsetKeys raws = #[(pos, keys)])
    (hdrew : 0 < Elab.enginePictures (Elab.runRaws file raws).1.body) :
    ∀ k ∈ Picture.unreadKeys [] (Picture.ofRaws keys),
      (Elab.runRaws file raws).2.any (fun d =>
        d.kind == .W0334 && d.subject == some ("picture:set:" ++ k)) = true := by
  sorry

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
-- blocker: two factorizations. (1) The composition lives in `Acc.gapGlue`, which is private to Layout and reads the owed-glue array and the peer flag together; the statable public form has to go through `Layout.run` and compare two whole runs, and nothing yet says that two documents differing only in one block's declared space ship baselines differing only below that block — the `PagesExtend`-shaped locality lemma the re-flow rows also wait on. (2) `Acc.addvspace` takes a maximum against the owed array's last entry, so the element-space gap is not a monotone function of the declaration alone: it is monotone only against a fixed prefix, and the statement needs the prefix named, which is the same `Acc` split (owed glue as a value with an equational theory, not an array threaded through the walk) that the emission-conservation rows wait on.
-- goldens: no
/-- An element's own declared space never narrows the gap above it: giving a
block a positive declared space cannot move the line that follows it *up*
the page. Stated over `Ir.Block.spaced` carrying a body, which is the
element-space path — a role's, a list's or a `\block[before]{body}`'s own
space — as against the bare declared skip `Layout.skip_monotone` already
holds. Positive glue narrowing a gap is impossible under any convention,
and the engine does not yet earn that here. -/
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
-- blocker: the statement is the honest restatement of what was proposed as "ink outside the band either grows the frame or fires a diagnostic"; that shape presumed the cap band was a containment claim, and the measurement above says it is not and cannot become one without undoing the placement. What is left is two things, neither a tactic. (1) There is no diagnostic for the residual case, so the disjunct below is stated over `Diag.subject` rather than a code: registering one is a `DiagCode` constructor with its declared `Loss`, a `diagWitness` arm and a golden, and it must fire on the genuine residue — ink outside the *ascent* band — not on the ordinary ascender, which means the band swap lands first. (2) Proving the covered disjunct needs the glyph-ink census over the picture walk, which is outline decoding inside a theorem (`Font.yExtent` is a memoized `Thunk` over per-gid outline data, with no equational theory) plus the `Acc` split the emission-conservation rows already wait on; and the containment is in any case not a theorem of the format — hhea ascent is not guaranteed to bound every glyph, `usWinAscent` being OpenType's declared clipping metric and its use for line spacing "strongly discouraged" — which is precisely why the statement is a disjunction and not a `_covers`.
-- goldens: yes
/-- **A label's ink is inside a declared band, or it is named.** The box a
picture reserves for a label is built from the band the label's faces
declare, and the glyphs may reach past it: so either the ink above the
baseline fits under the box's top, or the run carries a diagnostic naming
that label.

Stated as a disjunction rather than a containment because the containment is
not a fact of the font format — no OpenType metric is guaranteed to bound
every outline — and stated over the *reserved* box rather than the placement
band because those are the two jobs one band is doing today, and only the
second may move. This is the report's third constraint as an enforceable
obligation: the reason extent-derived boxes exist is that ink must not clip,
so a rule that places by declared metric owes an account of the ink it
thereby stops measuring. -/
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
-- blocker: one wall, and it is the same one two levels up. The quantifier is over a table, so the proof is a walk over `Compat.meaningFree` and `Compat.configSkip` — decidable per row, but each row's witness runs the whole surface pipeline (lex → parse → compat → elab), and `Elab.run`'s inline spine has no equational theory a per-row `rw` can use: it is the wall `elab_inlines_option_run_dropped` records. A table-quantified executable oracle is available today and is the honest interim — it is what found the leak. The *second* wall this row carried is gone: an unknown command's group could not be judged keyword or prose by any function the engine had, because recovered ink was not marked as recovered, so no statement could separate it from declared prose. `Ir.Doc.salvage` is that mark — the attribution the census reads — and the accounting conjunct below is the `_named` shape it makes statable: ink the document did not declare is paid for by a diagnostic whose `subject` names the command that produced it. `salvageChecks` runs the accounting executably over the corpus and the probes meanwhile.
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
-- blocker: the channel is no longer missing and the statement is no longer vacuous, which turns this row from unstatable into *false for one of its two registry entries* — retained here so the repair lands against its stated counterexample. What the channel fixed: `Diag.subject` is the dedup key, namespaced for some codes and unset for others, and W0103 and W0319 set nothing there at all, so the old spelling read the empty option and the whole quantification was trivially true. `Diag.refused` carries the name structurally (`Diag.of_refused`), `Compat.nameRefusalAsk` is the registry, and `nameRefusalRegistryChecks` closes it against the code list in both directions over the witness registry every code owes — a third name-refusal can no longer arrive invisibly, which is how `\usetheme` escaped. What remains is not a proof wall: W0319 is raised by *two* doors with different answers — the compat spellings, which do ask for `beamerthemeX.sty`, and the native `\theme{X}`, where no file beside the document would define a built-in bundle — so a per-code claim cannot be right for both. The registry needs the door rather than the code, or the native refusal needs a code of its own; that is a user-visible decision and Compat's to make. The wall this row carried behind that is now down to spelling: the quantification runs over `Elab.runRaws`'s whole diagnostic surface, an imperative preamble fold, and `LeanTex.Core.Loop` carries an invariant through a `forIn` that breaks — so what is left there is stating the invariant inside Elab, not factoring the fold
-- goldens: no
/-- **A declaration the engine refuses as unknown has no file beside the
document that would define it.** The pure half, which is the half the engine
owns: whenever a document's elaboration refuses a name, the file that would
have defined it was among the candidates the scan offered, so the driver
looked before the refusal was spoken. The effect half is
`Cli.Input.expandLocalSty`'s — a candidate whose file exists is read and
spliced, and the declaration is then consumed, so no refusal survives a file
that answers it.

Read off `Diag.refused` and quantified over `Compat.nameRefusalAsk`, so the
registry the claim ranges over is the engine's own and the name is a field
rather than a reading of a sentence. -/
theorem nameRefusals_asked (file : String) (raws : Array Parse.Raw) :
    ∀ d ∈ (Elab.runRaws file raws).2,
      ∀ p ∈ Compat.nameRefusalAsk,
        d.kind = p.1 →
          ∀ nm, d.refused = some nm →
            (Compat.localStyCandidates raws).contains (p.2 ++ nm) = true := by
  sorry

-- owed: titleStyle_spelling_agree
-- owner: LeanTex.Core.Elab
-- source: template-family audit 2026-09-24: `\setbeamertemplate{title page}` failed two real decks outright once `\usetheme{X}` began reading `beamerthemeX.sty`, and the read-out that should have salvaged the body knew latex.ltx's `\@title` and not beamer's `\inserttitle` — a refusal that read nothing because it did not recognise the spelling in front of it
-- blocker: not the scan. `Elab.barScan_alias_agree` is proved, and it is the whole of the property *at the scan*: a control word reaches the closed vocabulary only through `barCtrlName`, so two spellings that resolve alike are the same scan step in the same state, which is why the alias table cannot learn one name and miss another. What is open is the lift from that step to the elaborated document, and the wall is the one three other rows here describe: `applyRefusedTitleStyle` runs at the end of an imperative preamble fold, over `PreState` — private to Elab, so the premise cannot be spelled from outside the module at all — and the style it declares reaches `Doc.styles` only after that fold, a `Theme.styleMerge` under anything the document declared, and a diagnostic rewrite that walks `diags` backwards to find the W0361 it must amend. `LeanTex.Core.Loop` reads a `forIn` in place, so the fold needs no restating; what it does not give is a name for `PreState` outside Elab. The remaining work is therefore the statement written *inside* Elab over the fold's own state, exported as the corollary over `runRaws` spelled here — and the second clause ("only what cannot be expressed is named") is the harder half: it is an `_accounts` claim over the refusal's message, and the message is prose, so it needs `Diag` to carry the read structurally before it can be stated at all
-- goldens: no
/-- **A theme's spelling of a declared datum reads as the engine's own, at
the document.** Two preambles differing only in which vocabulary a refused
`\maketitle` body writes its metadata in — beamer's `\inserttitle` and
`\insertauthor`, or latex.ltx's `\@title` and `\@author` — elaborate to the
same title-page style. The scan-level half is proved
(`Elab.barScan_alias_agree`); this is its consequence for the artifact,
which is what a reader of the deck can see, and the property the defect
actually broke: the theme-authored spelling styled nothing.

Stated over the alias table, so the claim is the vocabulary's rather than
one name's, and over `Doc.styles` — the one place a read-out can land. -/
theorem titleStyle_spelling_agree (file : String)
    (pre post : Array Parse.Raw) (p q : Pos) (b l : String)
    (h : Elab.beamerInsertAlias.lookup b = some l) :
    ((Elab.runRaws file (pre ++ #[.ctrl b p] ++ post)).1.styles.find? "titlepage")
      = ((Elab.runRaws file (pre ++ #[.ctrl l q] ++ post)).1.styles.find? "titlepage") := by
  sorry

end Obligations
