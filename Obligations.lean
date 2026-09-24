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
  doc.body ≠ #[] ∧ ∀ b ∈ doc.body, ∃ title valign br body,
    b = Ir.Block.frame title false valign br body ∧ valign ≠ Ir.VAlign.golden ∧
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
-- blocker: the geometric-recovery half is gone — the shipped pair is the declared pair, so this is `judged_pair_is_shipped`'s converse, statable at last: every pair the pages ship is a pair the judge weighed. What remains is the collect-walk induction relating the walk's ground writes to `judgedPairs`' enumeration — the Acc split landed (2026-09-20), the wall now collectBlock's equation lemmas (see emission_conservation_paras). The judge's titled-bar default is no longer among the remainder: it read an unbarred title's page as white where the walk read `surfaceOf`, and both now resolve through `Contrast.titledGround`, held there by `titled_ground_agree` and by the shipped-ground rows in Tests/Themes (titledGroundChecks).
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

-- owed: macroDecls_fixed_point
-- owner: LeanTex.Core.Ir
-- source: the boundary-request closure defect (a document's own `\newcommand` that a picture spelled was undefined in the wrapped standalone, so the boundary tool drew nothing, E0382 fired as a dropped loss and no artifact was written at all); PLAN 2026-09-24 boundary-macro-closure entry
-- blocker: the pigeonhole the code rests on, which the statement does not mention. `macroReachNames` runs `macros.size` rounds and stops at the first round that adds nothing; correctness is that the *selected* set — `macros.filter (ns.contains ·.1)` — grows by at least one on every round that is not already the fixed point, and is bounded by `macros.size`, so a reference chain cannot outlast the round budget. The measure is over that selected set, not over `ns`: `macroReachRound` filters new names against `ns` only, so `ns` may hold a name twice and `ns.size` is not a cardinality. The named factorization is to carry the selection itself as the saturation's state (a duplicate-free `Array Nat` of indices, `Nodup` in a subtype) instead of a name set, which makes `size` the cardinality the pigeonhole needs and turns the round bound into `Nat.le_induction` over it. The direct half is proved (`macroDecls_covers`); the transitive half runs as an oracle in `boundaryChecks` ("a macro reached only through another macro's body rides too").
-- goldens: no
/-- The carried definitions are closed under reference: a definition whose
name another carried definition spells is carried too — the transitive half
of `macroDecls_covers`, and the reason a macro written in terms of an
earlier macro reaches the boundary whole. What the saturation computes; what
this statement owes is that `macros.size` rounds always suffice to reach it,
so no picture is ever handed a definition whose own body is undefined. -/
theorem macroDecls_fixed_point (macros : Array (String × String)) (body n d : String)
    (hm : (n, d) ∈ macros)
    (hr : ∃ p ∈ Ir.macroDecls macros body, n ∈ Ir.ctrlNames p.2) :
    (n, d) ∈ Ir.macroDecls macros body := by
  sorry

-- owed: place_order_agree
-- owner: LeanTex.Core.Picture
-- source: the M8b native-node slice (PLAN 2026-09-24, slice 3): a picture whose nodes are placed relative to one another drew nothing at all before it, and every such picture went to the boundary, where one un-drawable picture cost the whole artifact (E0382). The fix makes placement a function of the reference graph rather than of writing order; this is the statement of that, and the in-suite witness is the "a forward reference resolves: the offset is the same either way round" row of `pictureNodePlaceChecks`, read off two shipped pages.
-- blocker: the factorization, not the tactic. `evalFixed` is a `for` loop over `Id.run do` whose body is `evalList` — a mutual recursion whose node table is threaded through `Ev` as one field among five, so no equation names "the table after run k". The refactor the statement needs is a split of `Ev` into the *resolved table* and the *report* (shapes, diags, deferred, readOpts), making `evalList`'s table component a function of the seed alone; with that, order-independence is the statement that the least fixed point of the seeding map does not depend on the order `evalList` visits its statements, which is provable by induction on the statement list because each node's placement reads the table and nothing else. Until the split, the statement would have to quantify over a state the language cannot name — the case AGENTS.md calls a factorization finding.
-- goldens: no
/-- **A node's resolved position is a function of the nodes it references,
not of the order they were written in.** TikZ rejects a forward reference
outright (`No shape named 'x' is known`); the engine resolves it, and the
statement of that is this: the node table `evalFixed` settles on is the
same whichever order two independent node statements stand in, so the page
cannot tell the two documents apart.

Stated over the engine's own walk, on the table rather than the shapes,
because the table is what every relative placement and every edge endpoint
reads — the shapes follow from it. `sts₁` and `sts₂` range over the same
statements in two orders, spelled as one list with two elements
transposed, which is the case a document actually writes and the weakest
form that still names the fact. -/
theorem place_order_agree (cx : Picture.Cx) (pre post : List Picture.Stmt)
    (a b : Picture.Stmt) :
    ∀ nm, (Picture.evalFixed cx (pre ++ a :: b :: post)).nodes.lookup nm
        = (Picture.evalFixed cx (pre ++ b :: a :: post)).nodes.lookup nm := by
  sorry

-- owed: floorChars_id
-- owner: LeanTex.Core.Ir
-- source: the math recovery floor (PLAN 2026-09-24, the floor entries): the lower bound on the salvage a degraded formula inks. `floorChars_mem` is the upper bound — nothing invented, no markup — and it holds for a mask that dropped every character, so on its own it permits a blank page where an equation stood; this is the other side, that a source already free of control sequences and markup salvages to itself. The executable witness is the whole-string rows in `recoveryChecks` ("a plain content run passes through the floor unchanged" and its six siblings), which pin seven shapes exactly and fail under both an all-dropping and an all-keeping mask.
-- blocker: `floorMask` is three imperative index loops over a mutable `Array Bool` with no equational theory, so the statement needs the loop invariant "every index of a markup-free source is still marked kept" carried through the naming-argument scan, the whitespace squeeze and the trailing trim. The shape is fixed here so the invariant is proved against it rather than around it; the same `Acc`-split work the emission-conservation rows wait on is what makes an imperative accumulator statable.
-- goldens: no
/-- A math source with no control sequence, no LaTeX punctuation and no
whitespace salvages to exactly itself: the floor keeps content, it is not
merely free to drop it. -/
theorem floorChars_id (src : String)
    (h : ∀ c ∈ src.toList,
      c ≠ '\\' ∧ c ∉ Ir.markupChars ∧ c.isWhitespace = false) :
    Ir.floorChars src = src.toList := by
  sorry

mutual

/-- The characters a node body's tokens carry, in order: the source side of
the label floor's lower bound. A group is grouping, so its body's
characters are the group's own; a control sequence's *name* is not a
character it carries, and neither is a math span's spelling — the span
elaborates through the math layer, which decides its own content and
carries its own floor. An accumulator rather than an append, so the measure
has the shape the engine's walks do. -/
def bodyChars (env : List (String × Picture.Val)) (acc : Array Char) :
    List Picture.Tok → Array Char
  | [] => acc
  | t :: rest => bodyChars env (tokChars env acc t) rest

/-- One token's own characters (`bodyChars`'s element case). -/
def tokChars (env : List (String × Picture.Val)) (acc : Array Char) :
    Picture.Tok → Array Char
  | .ident w => w.toList.foldl Array.push acc
  | .num m => (Picture.milliString m).toList.foldl Array.push acc
  | .space => acc.push ' '
  | .sym c => acc.push c
  | .ctrl n =>
    match env.lookup n with
    | some v => v.text.toList.foldl Array.push acc
    | none => acc
  | .group g => bodyChars env acc g
  | .math _ _ => acc
  | .other _ => acc

end

mutual

/-- The characters a label's inlines ink, in order. Recurses into a coloured
group, which is the wrapper the node salvage introduced: a statement that
read only top-level `.text` runs would be satisfied by a salvage that put
whatever it liked inside a `.colored`. A math span carries its own floor and
is outside this measure, as it is outside `bodyChars`. -/
def labelChars (acc : Array Char) : List Ir.Inline → Array Char
  | [] => acc
  | x :: rest => labelChars (inlineChars acc x) rest

/-- One inline's own inked characters (`labelChars`'s element case). -/
def inlineChars (acc : Array Char) : Ir.Inline → Array Char
  | .text s => s.toList.foldl Array.push acc
  | .colored _ _ body => labelChars acc body.toList
  | _ => acc

end

-- owed: nodeLabel_mem
-- owner: LeanTex.Core.Picture
-- source: the node-label recovery floor (PLAN 2026-09-24, the node-label floor entry and its review round): the lower bound on what a degraded node label inks. `labelFloor_accounts` is the paid-for side — a label that named a loss ships ink — and it holds for a salvage that kept nothing at all, since the placeholder then pays for it; on its own it permits a diagram of bracketed ellipses where words stood, and it permits markup on the page. This is the other side: every character a salvaged label inks, inside a coloured group as well as at the top level, is a character its body carried or one of the declared placeholder's, and none of them is LaTeX punctuation. It bounds *provenance* and not *selection* — a naming argument's characters are the body's too, so this statement cannot express "dropped the argument it was told to drop", and that half is executable only: the whole-label rows in `pictureNodeFloorChecks` ("a length argument never rides onto the page", "a starred name's star does not stand in for its argument", "every trailing option run goes with the command", "the named key never reaches the page" and their siblings) pin the salvage of sixteen shapes against the shipped page, and each is paired with a positive row over the same input so none passes under an all-dropping salvage.
-- blocker: `salList` is a mode machine (`Picture.SalMode`) threaded through a mutual walk over a token tree, and no equation names "the label after token k" — the pending text run, the closed lines and the mode advance together inside one `Sal`, so the statement needs an invariant carried through five modes and two mutual arms. The named factorization is a `Sal` split into the content built so far and the machine's pending state, which is the same accumulator-statability work `floorChars_id` waits on one module over; until it lands the statement is owed rather than asserted in a docstring.
-- goldens: no
/-- Every character a salvaged node label inks — inside a coloured group as
well as at the top level — is a character its body carried, or one of the
declared placeholder's, and none of them is LaTeX punctuation: the label
keeps what the body says and invents nothing. -/
theorem nodeLabel_mem (cx : Picture.Cx) (env : List (String × Picture.Val))
    (toks : List Picture.Tok) :
    ∀ l ∈ (Picture.nodeLabel cx env toks).1,
      ∀ c ∈ (labelChars #[] l.1.toList).toList,
        (c ∈ (bodyChars env #[] toks).toList ∨ c ∈ Ir.mathFloorPlaceholder) ∧
          c ∉ Ir.markupChars := by
  sorry

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
-- blocker: three factorizations, none of them a tactic. (1) There is no diagnostic-monotonicity notion across placement: `placePara` folds `placeParaLine` through `placeParaTrailer`, `placeLine`, `fitCommit`, `commit`, `finishPage`, `spillPage` and `warnSpill`, and while every one of them only appends, no lemma says so — `PagesExtend` is the shape this wants, a `DiagsExtend` beside it, which is what makes "pushed at the step" mean "present in the `Out`". (2) The shipped count is not connected to the breaker's: `breaks.size` is what `warnReflow` reads, and that it equals the ink lines a one-paragraph document ships needs the placement induction (one line committed per break, the same lines re-placed after a spill). (3) The declared count is not connected to the item stream: `declaredLines` counts forced penalties in `Array Item`, and that this is the `.linebreak` count of the inlines is `itemsOfInlines`'s own census — the `Acc`-split work the emission-conservation rows already wait on. The same three hold `warnSpill_accounts` (W0384) one level below its artifact, so discharging them closes both.
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

-- owed: nodeExtent_covers
-- owner: LeanTex.Core.Picture
-- source: the picture-extent slice (PLAN 2026-09-24, the box-contains-its-ink entry): a node's extent is never measured against its label text, so `right =of` separates node *centres* by one node distance and long labels overlap whatever they say. The border arithmetic is proved and exact (`Picture.placeRight_border_exact` and its three siblings); what is wrong is the input, because the half-extent a node registers is the declared minimum only and a body with no `minimum width` registers zero. On the private reference corpus this collapsed an eight-node graph into roughly a centimetre of ink. The measured box (`Ir.Pic.Picture.inkBbox`, `inkBbox_covers`) closes the half that sent glyphs off the page; this is the half that would space the diagram correctly, and the in-suite witness meanwhile is the overrun row of `pictureInkBoxChecks`, which names a diagram whose measured ink leaves the text area instead of shipping it silently.
-- blocker: the picture walk has no face, and the driver cannot give it one. A node's extent is a font question, and the font set is built *from* the elaborated document (`buildFontSet` reads `doc.fonts`, a preamble declaration), so at the moment `evalNode` resolves a placement there is nothing to measure against — the ordering is circular, and breaking it means a two-pass driver (parse, resolve the font environment from the preamble, then elaborate) which is the elaborator's and the driver's door, not this module's. `Ir.Pic.LabelMetric` is the seam the measurement will arrive through and every box statement is already quantified over it; what this obligation needs is for `Picture.Cx` to carry one, so `evalNode`'s `ownA`/`ownB` are `max` of the declared minimum and the measured half-extent rather than the minimum alone. Until then the statement quantifies over a metric the walk never sees, which is why it is owed rather than proved.
-- goldens: yes
/-- **A node's registered extent covers its label's ink.** The half-extents
a named node registers (`NodeGeom.a`, `NodeGeom.b`) are what every relative
placement measures border to border from, so a label standing at a node's
anchor must fit inside them — otherwise the separation the placement
theorems prove exactly is exact about the wrong box, and two nodes one node
distance apart by their borders overlap by their text.

Stated over the engine's own walk and over an arbitrary measurement, the
same `Ir.Pic.LabelMetric` the box statements range over: whatever face
resolves, the ink of a label at a node's anchor is inside the extent that
node placed against. The anchor hypothesis is how a shape is tied to its
node — the walk emits a label centred on the node's own point, and no
channel records which node emitted which shape. -/
theorem nodeExtent_covers (cx : Picture.Cx) (m : Ir.Pic.LabelMetric)
    (sts : List Picture.Stmt) (nm : String) (g : Picture.NodeGeom)
    (x y : Dim.Sp) (content : Array Ir.Inline) (c : Ir.Color) (sc : Nat)
    (al : Ir.Pic.LabelAlign)
    (hg : (Picture.evalFixed cx sts).nodes.lookup nm = some g)
    (hs : Ir.Pic.Shape.label x y content c sc al ∈ (Picture.evalFixed cx sts).shapes)
    (hanchor : x = g.x ∧ y = g.y) :
    Ir.Pic.Box.le (Ir.Pic.labelInkBox x y al (m content sc))
      ((g.x - g.a, g.y - g.b), (g.x + g.a, g.y + g.b)) := by
  sorry



-- owed: pictureKeys_named
-- owner: LeanTex.Core.Elab
-- source: the stale picture-key gate (PLAN 2026-09-24, the unread-picture-key entry): the keys a `\tikzset` line leaves outside the rendered subset were named only under the declared refusal, on the premise that the real TikZ read them at the edge whenever a tool was configured. Native drawing killed that premise — the boundary became the fallback — and the diagnostic went silent for every picture the engine drew itself, an arrow-tip default among the keys dropped without a word on a 41-page deck. The gate now reads `Elab.enginePictures`, the count of `.picture` nodes the body walk produced, which is who drew it rather than which tool was configured. The in-suite witness is `pictureKeyGateChecks`, whose decisive row is a pair of builds differing by one `\pictures{ tool = none }` line: byte-identical PDFs, the same keys named on both sides, which is what separates the drawing from the honesty. Its siblings pin the two floors (a document whose every picture went whole to the boundary claims no loss, a document with no picture has no drawing to have lost them) and the mixed case the previous gate got wrong.
-- blocker: the same diagnostic-monotonicity wall `reflow_named` names, one module over: the naming happens inside `elabDoc`'s `EM` fold and nothing states that a diagnostic pushed there survives to the array `runRaws` returns — every step only appends and no lemma says so. Two further factorizations are specific to this statement. The gate's premise reads the elaborated body, so relating it to the source needs `elabBlocks`' own census (which `.picture` nodes a source produces), the `Acc` split again. And the fold over the set lines accumulates the style table, so a statement over more than one `\tikzset` line needs an invariant carried through that fold; the single-line form below avoids it, which is why it is stated weakly rather than generally.
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

/-- How many diagnostics of one run are sites of the same loss as `d`: the
census `Diag.tallySites` counts, read back over the public array so a
statement can compare it with what the source contains. -/
def lossSites (ds : Array Diag) (d : Diag) : Nat :=
  (ds.filter (Diag.sameLoss d ·)).size

-- owed: warnOnce_sites_exact
-- owner: LeanTex.Core.Elab
-- source: the per-construct diagnostic census (PLAN 2026-09-24, the counted-sites entry): `warnOnce` keyed on the construct and dropped every later occurrence, so on one real document ten diagnostics stood for roughly fifty losses and two node labels were dropped with no diagnostic at all, an earlier site having spent the key. Each site now delivers a note beside the named first, and `Diag.tallySites` puts the total on the visible line. The in-log half is proved: `Diag.tallySites_exact` says the number on the line is the number of diagnostics of that loss in the run, and `tallySites_length`/`tallySites_id` say counting adds, drops and rewords nothing. What is owed is the other half — that the number of diagnostics equals the number of *sites in the source*, which is the claim a reader sizing the damage from the log actually relies on. The in-suite witnesses are `diagSiteCountChecks` (three occurrences, three diagnostics, one visible line carrying 3, each note at its own position, the count equal to the diagnostics of that loss, and a single occurrence carrying neither count nor note) and the four fixture goldens whose second site stopped being silent.
-- blocker: the source side has no census to compare against. There is no function from a raw tree to "the occurrences of construct c", and writing one here would be the spec copy the queue forbids — the occurrences are exactly the sites `elabBlocks` reaches, so the honest measure is that walk's own, which is the `Acc` split the emission-conservation rows already wait on. The form below sidesteps it by counting occurrences through repetition instead: appending a block to a document whose loss it already carries must raise that loss's count by exactly its own contribution, which is stateable over `Elab.runRaws` alone. That still needs the diagnostic-monotonicity notion `reflow_named` names (a `DiagsExtend` beside `PagesExtend`) plus the fact that elaborating a concatenation elaborates each part — neither exists, and the second is the compositionality `compose-fuzz.lean` currently stands in for.
-- goldens: no
/-- No site is silent, stated through repetition: elaborating a document's
body twice over names every loss twice as often. The site count a reader
takes from the default line is then the number of occurrences in the source
and not merely the number in the log — which is the whole claim, since a
census that undercounts is exactly the defect this replaced. Restricted to
losses the single copy already names, because a repetition can create a loss
of its own (a second `\maketitle` is refused where a first is not), and
those have no count in the single copy to double. -/
theorem warnOnce_sites_exact (file : String) (pre body : String) :
    ∀ d ∈ (Elab.run file (pre ++ "\\begin{document}" ++ body ++ "\\end{document}")).2,
      d.subject.isSome →
        lossSites (Elab.run file
            (pre ++ "\\begin{document}" ++ body ++ body ++ "\\end{document}")).2 d =
          2 * lossSites (Elab.run file
            (pre ++ "\\begin{document}" ++ body ++ "\\end{document}")).2 d := by
  sorry

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
    (a b : Array Ir.Inline) (g : Dim.SymGlue) (hpos : (0 : Int) ≤ g.width.sp) :
    ((inkBaselines (Layout.run geom fs none
        { doc with body := #[.para a, .para b] })).getLast?.getD 0 : Int)
      ≤ (inkBaselines (Layout.run geom fs none
          { doc with body := #[.para a, .spaced g #[.para b]] })).getLast?.getD 0 := by
  sorry

end Obligations
