import LeanTex.Core.Layout
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
  | .run _ _ _ _ glyphs _ _ _ _ _ => inkChars (String.ofList (glyphs.toList.map (·.2)))
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
-- blocker: the collect-walk induction — the claim sites are `Acc.leafRange` calls inside `collectBlock`'s one giant match, whose equation-lemma generation exhausts whnf whatever the budget (the `emission_conservation_paras` blocker); the per-constructor arm split is the named factorization, and this channel is what it pays for. The placement half is definitional: `placeLine`'s `mk` closure copies `ParaJob.leaf` onto every line it commits (`placeLine_leaf_exact`), and the count comes from `Struct`'s own walk (`leafCount`), so what remains is that the walk's claims run over the body in `Struct.blocksRaw`'s order.
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
-- blocker: as `lines_attributed_covers` (the collect-walk induction behind `collectBlock`'s arm split), plus the per-paragraph half of `emission_conservation_paras`: a paragraph's lines ship exactly its declared ink, which is exactly its node's leaf census (`structTree_text` per block).
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
-- blocker: the named refactors landed (2026-09-20: Rd/Acc reader split, B's writers the commit/pushSibling/finishPage trio, itemsOfInlines a fold of itemsOfTok with a first-class dropped ledger, the driver on placeFrom/runPost with page facts crossing at runPost_pages — page_background_survives discharged over them). What remains is the collect-walk induction, and its wall is not the state any more: equation-lemma generation for collectBlock's one giant match exhausts whnf whatever the budget (the `role_transparent_layout` blocker, confirmed again this session), so no `rw`/`induction` can open the walk. The next factorization: split collectBlock's match into per-constructor arm functions (the placePicture extraction is the shape — stepStaged's case analysis only fit the budget once the picture arm was its own def), so each arm's equation is one cheap unfold.
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
-- blocker: the page side needs the collect walk's induction; the Acc split landed (2026-09-20) and the remaining wall is collectBlock's equation lemmas (see emission_conservation_paras) plus the placement half — a frame-attribution analogue of the BgStep pack over the `.foot`-op stream. The counting side is already proved on the IR (`frameNumbers_gapless`, `frameNumbers_last_is_count`), and the attribution travels with the footer through the one `.foot` op.
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
-- blocker: `PageOut.frame` and `PageOut.foot` are written together at `finishPage` from the one `.foot` op a frame's opening pushes (content is some exactly when the frame bears a number, given the chrome), so the implication is definitional at the write site; what remains is the collect-walk induction connecting `doc.chrome` to the op stream — the Acc split landed (2026-09-20), the wall now collectBlock's equation lemmas (see emission_conservation_paras).
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
      | .run _ color _ _ glyphs _ _ _ ground _ =>
        unless glyphs.isEmpty do
          out := out.push (color, ground.getD defaultBg)
      | _ => pure ()
  return out

-- owed: contrast_judged_complete
-- owner: LeanTex.Core.Contrast
-- source: the a11y-contract slice (the user's ask: weak accessibility in any document is proven, never suspected) — the completeness half of the W0315/W0345 judge, whose per-bundle contracts are already theorems; restated over the declared ground when refactor 2 (`ground` on `Seg.run`, written at the resolving sites) landed
-- blocker: the geometric-recovery half is gone — the shipped pair is the declared pair, so this is `judged_pair_is_shipped`'s converse, statable at last: every pair the pages ship is a pair the judge weighed. What remains is the collect-walk induction relating the walk's ground writes to `judgedPairs`' enumeration — the Acc split landed (2026-09-20), the wall now collectBlock's equation lemmas (see emission_conservation_paras). The proof will also surface the judge's titled-bar default (white in Contrast.judgedPairs where the walk's surfaceOf reads light.surface) — the fix belongs to Contrast.lean's owner.
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
-- blocker: both sides are imperative loops (`Id.run`/`forIn` on the inflate side, fuel-shaped tail recursion on the deflate side) with no equational theory the round-trip induction can use. The factorization it needs: the encoder split into the block-structure functions the proof can walk (header emission, one Huffman-coded token, the code-length prelude), each with an emit/decode commutation lemma, and a bit-reader/bit-writer adjunction (`Br.bits` after `Bw.push`) at the bottom. The deflate-fast rewrite (2026-09-21) did not change the shape — the tokenizer is still fuel-shaped tail recursion — but the writer now carries its invariant explicitly (fewer than eight pending bits between pushes, so `Bw.pushU` is a pure two-case function of `(bits, nbits)`), which is the adjunction's base case.
-- goldens: no
/-- The engine's inflate inverts its deflate on every input: the compressed
streams the PDF writer emits (content, fonts, image planes, metadata, the
object and cross-reference streams) decode back to exactly the bytes the
engine meant, by the engine's own decoder. -/
theorem inflate_deflate_id (b : ByteArray) :
    Flate.inflate (Flate.deflate b) b.size = .ok b := by
  sorry

/-- Every count the cache format spells as a u32 is inside it, and no form
rides: what `Image.decode` produces (the ranges by
`colorKeyRanges_between`). -/
def binBounded (i : Image.Plan) : Prop :=
  i.form = none ∧ i.pxW < 4294967296 ∧ i.pxH < 4294967296 ∧
    i.dpiX < 4294967296 ∧ i.dpiY < 4294967296 ∧ i.bitDepth < 4294967296 ∧
    i.orientation < 4294967296 ∧ i.data.size < 4294967296 ∧ i.losses.size < 4294967296 ∧
    (match i.color with
      | .gray => True
      | .rgb => True
      | .indexed palette => palette.size < 4294967296
      | .iccBased n profile => n < 4294967296 ∧ profile.size < 4294967296) ∧
    (match i.alpha with
      | .opaque => True
      | .colorKey ranges => ranges.size < 4294967296 ∧ ∀ v ∈ ranges, v < 4294967296
      | .soft plane bpc => plane.size < 4294967296 ∧ bpc < 4294967296)

-- owed: decodeBin_encodeBin_id
-- owner: LeanTex.Core.Image
-- source: the build-cache slice (2026-09-21 survey wave): the driver's image cache files `Image.encodeBin`'s bytes under the source's content key and the plan parameters' key, and transparency — a cache hit *is* the recomputation's value, keeping the artifact a function of the document and the font environment — is exactly this inversion. Restated over the typed `Plan` by image-plan-factor (the three sums ride as tag bytes, the ledger as one byte per entry). The in-suite witnesses are the image-cache serialization rows in Tests/Images (a plan per alpha and colour constructor round-trips; foreign, truncated, and older-magic bytes refuse).
-- blocker: the codec is fixed-offset field reads over `ByteArray.push`/`append`/`extract`, and the standard library's equational coverage for those (get-of-append, extract-of-append) is not yet enough to push the eighteen header reads, the key loop, and the tag dispatch through; the statement carries its honest side conditions (`binBounded`: each Nat field and each length under 2³², every colour-key value under 2³², `form = none`) so the per-field lemmas can compose once they exist.
-- goldens: no
/-- The image cache's serialization inverts: reading back `encodeBin`'s
bytes yields the plan itself, field for field, for every raster `Plan` the
cache can hold (`binBounded`). A cache hit therefore equals a
recomputation. -/
theorem decodeBin_encodeBin_id (i : Image.Plan) (hb : binBounded i) :
    Image.decodeBin (Image.encodeBin i) = some i := by
  sorry

-- owed: write_fonts_embedded
-- owner: LeanTex.Core.Pdf
-- source: the pdf-census slice (modern output, wave 1 S2; pdf-objects T3/T4): `fonts.all_embedded` now reads the census of the bytes, so the claim that the writer's own output passes that census is the writer's to prove — today it is the executable witness "written pdf census: fonts embedded" in Tests/Backends and the pdffonts oracle over the corpus.
-- blocker: the statement crosses the string writer and the byte parser: `write` spells its twelve dictionaries as interpolated strings, and no equation connects a spelled `/FontFile2 n 0 R` to the `Obj` `parseVal` returns for it. The factorization: the dictionary sites typed as `PdfRead.Obj`, rendered by one `Obj.render`, with `parseVal_render_id` (`_id`, stated when `render` exists) — then the census over `write`'s output is the census over the values `write` built, and the font arm is a fold over `keepFaces`.
-- goldens: no
/-- The writer embeds every font it names: for an image-free document
(no copied graph can bring a foreign face), the census of the bytes
`Pdf.write` emits says every font is embedded — the internal check
`fonts.all_embedded` reads, holding of the writer's own output by proof
rather than by the corpus sweep. -/
theorem write_fonts_embedded (geom : Layout.Geom) (fs : Font.FontSet)
    (pages : Array PageOut) (info : Ir.Meta) (outline : Array OutlineEntry) :
    (PdfCensus.census (Pdf.write geom fs pages info {} outline)).map (·.fontsEmbedded)
      = .ok true := by
  sorry

-- owed: write_readXref_exact
-- owner: LeanTex.Core.Pdf
-- source: the pdf-conformance-gate slice (modern output, wave 1 S3; pdf-validation F/gap 1–2, S3 red 1–2): the engine's own reader accepts every file the engine writes — today the executable witness is the reference walk over every corpus PDF in Tests/PdfConformance (`walkPdf`) and the six mutants it refuses by name.
-- blocker: `write` is one `Id.run` with a mutable `Wr` and a `locs` table it fills as it goes, so no equation connects the offsets it wrote into the cross-reference stream to the positions `readXref` parses them back from; the size it computed (`xrefId + 1`) is a local of that block, which is why the statement reads the trailer's `/Size` instead. The factorization: the layout/serialize split — an `ObjTable` of typed objects with their ids (M7-12 begins it) and a later `serialize : ObjTable → … → ByteArray × Array Loc` whose offsets are the table's by construction; then `readXref ∘ serialize` is a fold over the rows and `/Size` is the table's length plus one.
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

-- owed: skeleton_leafKids_nodup
-- owner: LeanTex.Core.PdfStruct
-- source: the pdf-tag-skeleton slice (modern output, wave 2 W2.8; pdf-tagging audit "theorems (PDF projection corollaries)"): the structure elements hold each leaf's marked content once — the hypothesis `parentTree_covers` reads, and what makes the leaf tags a function (`leafTags`) rather than a last-writer-wins fold; the executable witness is the per-fixture row "every leaf placeholder is held by exactly one element" in Tests/Backends.
-- blocker: the skeleton walk threads an element accumulator through a mutual recursion (`skelList`/`skelStep`) that also modifies earlier elements in place (`pushElem`, `addKid`), so the census of its `.leaf` placeholders needs the accumulator-generalised statement `leafKids (skelList es …) = leafKids es ++ <the tree's leaf ids outside asides>` proved through `Array.modify`'s equational theory before `structTree_leaves_id` (the ids are `range n`) gives the nodup; the heading census (`pdf_headings_covers`) went the same route and is closed — this row is the leaf half of that induction.
-- goldens: no
/-- The skeleton holds every leaf of a document's structure tree at most
once: no two elements carry the same `.leaf k` placeholder, so a leaf's
marked content lands in one element and the parent tree names it. -/
theorem skeleton_leafKids_nodup (doc : Ir.Doc) :
    (Pdf.leafKids (Pdf.skeleton (Struct.ofDoc doc))).Nodup := by
  sorry

-- owed: parentTree_covers
-- owner: LeanTex.Core.PdfStruct
-- source: the pdf-tag-skeleton slice (modern output, wave 2 W2.8; pdf-tagging audit "theorems (PDF projection corollaries)"): the parent tree entry of every marked-content identifier is the element that lists it — ISO 32000-2 §14.7.5.4's contract, which every reader's structure walk relies on; the executable witness is the per-fixture row "the parent tree maps every identifier back to the element listing it" in Tests/Backends, read back through the engine's reader.
-- blocker: two fold inversions over `Id`-style array folds — `leafPagesOf` (a `(page, mcid)` pair lands in slot `k` exactly when the marks of that page carry `(mcid, k)`) and `leafOwners` (an owner recorded for `k` is the element carrying `.leaf k`, unique under `skeleton_leafKids_nodup`) — plus `numberMarks_mcids_exact` read as "position is identifier" on `pageMarks`; the statement is closed the day those three lemmas are, and its shape is fixed here so they are proved against it.
-- goldens: no
/-- The parent tree covers every marked-content reference: for elements
filled from the pages' marks (`fill` over `leafPagesOf`), if element `i`
lists `(page, mcid)` then the parent tree built from the same marks and
owners (`parentTreeOf`) answers `i` at `[page][mcid]` — given the marks are
positional (identifier = index, `numberMarks_mcids_exact`), the leaf
placeholders are held once (`skeleton_leafKids_nodup`) and lie within the
leaf count. -/
theorem parentTree_covers (es : Array Pdf.StructElem) (n : Nat) (marks : Array (Array (Nat × Nat)))
    (hpos : ∀ p (hp : p < marks.size) i (hi : i < marks[p].size), (marks[p][i]).1 = i)
    (hnodup : (Pdf.leafKids es).Nodup) (hlt : ∀ k ∈ Pdf.leafKids es, k < n) :
    ∀ i (hi : i < (Pdf.fill es (Pdf.leafPagesOf n marks)).size) p m,
      Pdf.StructKid.mcid p m ∈ (Pdf.fill es (Pdf.leafPagesOf n marks))[i].kids →
        ((Pdf.parentTreeOf marks (Pdf.leafOwners es n))[p]?).bind (·[m]?) = some (some i) := by
  sorry

end Obligations
