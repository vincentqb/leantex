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
-- blocker: the collect walk's equation lemmas landed (2026-09-24: `collectBlock`'s match split into per-arm functions, eleven non-recursive arms and six non-recursive interiors lifted out; `role_transparent_collect` is the witness that an arm now unfolds at the default budget, where generation previously exhausted whnf whatever the budget). That was necessary and is not sufficient. Two imperative loops still stand between the walk and the pages, and this statement must cross both: `run`'s top-level `for h : i in [0:doc.body.size]` over `doc.body`, which threads `acc` and is where a frame's number and its step pages are decided, and the placement pass over the staged op stream. Neither has an equational theory an induction can use — the `Id.run`/`forIn` shape the nine loop-shaped rows name one level down — so the next factorization is those two loops restated as folds over a step function with a named invariant, the `stepStaged`/`PagesExtend` shape already proved for the placement side's page facts. The placement half stays definitional: `placeLine`'s `mk` closure copies `ParaJob.leaf` onto every line it commits (`placeLine_leaf_exact`), and the count comes from `Struct`'s own walk (`leafCount`), so what remains is that the walk's claims run over the body in `Struct.blocksRaw`'s order — which is the driver loop's order, hence the first of the two loops above
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
-- blocker: as `lines_attributed_covers` (the two loops between the walk and the pages, the collect-walk equation lemmas having landed 2026-09-24), plus the per-paragraph half of `emission_conservation_paras`: a paragraph's lines ship exactly its declared ink, which is exactly its node's leaf census (`structTree_text` per block)
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
-- blocker: the named refactors landed (2026-09-20: Rd/Acc reader split, B's writers the commit/pushSibling/finishPage trio, itemsOfInlines a fold of itemsOfTok with a first-class dropped ledger, the driver on placeFrom/runPost with page facts crossing at runPost_pages. 2026-09-24: the collect-walk arm split, so `collectBlock` unfolds one arm at a time — `role_transparent_collect` is the witness, and the equation-lemma wall this row named is down). What remains is not the walk: it is the two imperative loops on either side of it. `run`'s top-level `for h : i in [0:doc.body.size]` threads `acc` over `doc.body` with the frame numbering and the per-step collects inside it, and the placement pass folds the staged op stream into pages; neither is a fold with a named invariant, so no induction reaches from `docInk` to `outInk`. The next factorization is those two, restated as folds over a step function, the shape `stepStaged` and `PagesExtend` already give the placement side's page facts. Note the arm split is not uniform and cannot be: Lean picks one recursive argument group for the mutual block and `collectAlt` recurses into two block arrays, so the recursive arms stay inline; well-founded recursion would trade this cheap wall for the WF-equation wall `elab_inlines_option_run_dropped` records
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
-- blocker: the collect walk's equation lemmas landed (2026-09-24: `collectBlock`'s match split into per-arm functions, eleven non-recursive arms and six non-recursive interiors lifted out; `role_transparent_collect` is the witness that an arm now unfolds at the default budget, where generation previously exhausted whnf whatever the budget). That was necessary and is not sufficient. Two imperative loops still stand between the walk and the pages, and this statement must cross both: `run`'s top-level `for h : i in [0:doc.body.size]` over `doc.body`, which threads `acc` and is where a frame's number and its step pages are decided, and the placement pass over the staged op stream. Neither has an equational theory an induction can use — the `Id.run`/`forIn` shape the nine loop-shaped rows name one level down — so the next factorization is those two loops restated as folds over a step function with a named invariant, the `stepStaged`/`PagesExtend` shape already proved for the placement side's page facts. Both halves of this row live in those loops: the frame attribution is decided in the driver loop (it sets `acc.frameNum` per top-level block and re-enters `collectBlock` once per overlay step), and the page side needs a frame-attribution analogue of the BgStep pack over the `.foot`-op stream in the placement loop. The counting side is already proved on the IR (`frameNumbers_gapless`, `frameNumbers_last_is_count`)
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
-- blocker: `PageOut.frame` and `PageOut.foot` are written together at `finishPage` from the one `.foot` op a frame's opening pushes (`collectFrameOpen`, where content is some exactly when the frame bears a number given the chrome), so the implication is definitional at the write site. The collect-walk equation lemmas landed 2026-09-24 and the walk half was attempted: `chromeFoot_isSome` goes through (the chrome fields are set once by `run` and no arm writes them, so `Acc.chromeFoot` answers the same for the whole document), and the op-stream invariant is stateable. It met the zeta-expansion trap instead — `collectFrameOpen` is a `let`-chain, so `unfold` produces a `have`-chain `split` cannot see through, and `simp only` then leaves the membership goal in a shape the case analysis does not match. That is the factorization to do first: `collectFrameOpen` restated so the pushed op is a named value the statement can read, rather than a `let`-bound intermediate. Past it stand the two loops `emission_conservation_paras` names — the driver loop connecting `doc.chrome` to the op stream, and the placement fold carrying `curFoot`/`curFrame` onto each closing page
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
-- blocker: the geometric-recovery half is gone — the shipped pair is the declared pair, so this is `judged_pair_is_shipped`'s converse. The collect-walk equation lemmas landed 2026-09-24 (the arm split; `role_transparent_collect` is the witness), so the walk's ground writes can now be opened one arm at a time. What remains is relating those writes to `judgedPairs`' enumeration across the two imperative loops `emission_conservation_paras` names: the driver loop, which re-enters the walk per overlay step and so may write a ground more than once per frame, and the placement fold, which is where a run's `ground` reaches a page. The judge's titled-bar default is no longer among the remainder: both sides resolve through `Contrast.titledGround`, held by `titled_ground_agree` and by the shipped-ground rows in Tests/Themes (titledGroundChecks)
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

/-! ## Discharged here, awaiting a move

`floorChars_id` below is proved. Its owner is `LeanTex.Core.Ir`, which
another agent holds in this wave, so it stands here with a real proof
rather than a hole until that file can take it — with its `floorMask_id`
lemma and the `filterMap_eq_map_fst` helper, which move with it. The queue
is not a home: these three lines go into Ir.lean beside `floorChars_mem`,
whose converse this is, in the commit that can touch that file.

The proof is the loop-reading layer (`LeanTex.Core.Loop`) applied three
times, once per loop of `floorMask`, and it needed no change to
`floorMask` itself. -/

/-- A `filterMap` that keeps every element is the projection it keeps.
Moves into `LeanTex.Core.Ir` with `floorChars_id`. -/
private theorem filterMap_eq_map_fst {α β : Type} (l : List (α × β)) (g : α × β → Option α)
    (hg : ∀ p ∈ l, g p = some p.1) : l.filterMap g = l.map Prod.fst := by
  induction l with
  | nil => simp
  | cons p rest ih =>
    rw [List.filterMap_cons, hg p (by simp), List.map_cons,
      ih (fun q hq => hg q (by simp [hq]))]

/-- **The mask of a markup-free source keeps every index.** Each of
`floorMask`'s three loops preserves "the mask is still all-true": the
naming-argument scan because no character is a backslash, so the branch
that drops one is unreachable; the whitespace squeeze and the trailing trim
because no character is whitespace — and the trim's own `survives` test
supplies the bound that makes its character readable, so the invariant
needs nothing about the descending cursor.

Moves into `LeanTex.Core.Ir` with `floorChars_id`. -/
theorem floorMask_id (src : String)
    (h : ∀ c ∈ src.toList, c ≠ '\\' ∧ c ∉ Ir.markupChars ∧ c.isWhitespace = false) :
    Ir.floorMask src = Array.replicate src.toList.length true := by
  have hat : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ∈ src.toList := by
    intro i hi
    rw [List.getElem?_eq_getElem hi]
    simp [List.getElem_mem]
  have hws : ∀ i, i < src.toList.length →
      (src.toList[i]?.getD ' ').isWhitespace = false :=
    fun i hi => (h _ (hat i hi)).2.2
  have hbs : ∀ i, i < src.toList.length → (src.toList[i]?.getD ' ') ≠ '\\' :=
    fun i hi => (h _ (hat i hi)).1
  have hrep : ∀ j, ((Array.replicate src.toList.length true)[j]?).getD false = true →
      j < src.toList.length := by
    intro j hj
    simp only [Array.getElem?_replicate] at hj
    split at hj
    · assumption
    · simp at hj
  simp only [Ir.floorMask, List.size_toArray]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step1) ?rest
  case step1 =>
    intro i _ _ b hb
    split
    · exact hb
    · rename_i hlt
      split
      · exact hb
      · rename_i hne
        exact absurd (by simpa using hne) (hbs b.2 (by omega))
  case rest =>
  intro b hb
  rw [hb]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Bool) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step2) ?rest2
  case step2 =>
    intro i _ hi c hc
    split
    · split
      · rename_i hw; exact absurd hw (by simp [hws i hi])
      · exact hc
    · exact hc
  case rest2 =>
  intro c hc
  rw [hc]
  refine Loop.bind_eq_of_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _
    (Loop.forIn_range_inv (fun (st : Array Bool × Nat) =>
      st.1 = Array.replicate src.toList.length true) _ _ _ _ rfl ?step3) ?rest3
  case step3 =>
    intro i _ _ d hd
    split
    · exact hd
    · split
      · rename_i hsv
        have hlt : d.2 - 1 < src.toList.length := hrep _ (by
          simpa using (Bool.and_eq_true _ _ ▸ hsv : _ ∧ _).1)
        split
        · rename_i hw; exact absurd hw (by simp [hws _ hlt])
        · exact hd
      · exact hd
  case rest3 =>
  intro d hd
  exact hd

/-- A math source with no control sequence, no LaTeX punctuation and no
whitespace salvages to exactly itself: the floor keeps content, it is not
merely free to drop it.

Moves into `LeanTex.Core.Ir` beside `floorChars_mem`, whose converse this
is: that bound permits a mask which dropped everything, and so on its own
permits a blank page where an equation stood. -/
theorem floorChars_id (src : String)
    (h : ∀ c ∈ src.toList,
      c ≠ '\\' ∧ c ∉ Ir.markupChars ∧ c.isWhitespace = false) :
    Ir.floorChars src = src.toList := by
  simp only [Ir.floorChars, floorMask_id src h]
  rw [filterMap_eq_map_fst]
  · exact List.zipIdx_map_fst 0 src.toList
  · intro p hp
    have hmem : p.1 ∈ src.toList := by
      have hm := List.mem_map_of_mem (f := Prod.fst) hp
      rwa [List.zipIdx_map_fst] at hm
    simp [Array.getElem?_replicate, (h _ hmem).2.1]
    split <;> simp

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
-- source: the picture-extent slice (PLAN 2026-09-24, the box-contains-its-ink entry): a node's extent is never measured against its label text, so `right =of` separates node *centres* by one node distance and long labels overlap whatever they say. The border arithmetic is proved and exact (`Picture.placeRight_border_exact` and its three siblings); what is wrong is the input, because the half-extent a node registers is the declared minimum only and a body with no `minimum width` registers zero. On the private reference corpus this collapsed an eight-node graph into roughly a centimetre of ink. The measured box (`Ir.Pic.Picture.inkBbox`, `inkBbox_covers`) closes the half that sent glyphs off the page; this is the half that would space the diagram correctly, and the in-suite witness meanwhile is the overrun row of `pictureInkBoxChecks`, which names a diagram whose measured ink leaves the text area instead of shipping it silently. The site and its two facts landed since (`nodeExtentChecks` pins their arithmetic on numbers, including the defect as the number it was).
-- blocker: the wiring, no longer the ordering (PLAN 2026-09-24, the face-a-node-is-measured-against entry). The arithmetic and the covering are now proved, on the IR and for every measurement: `Ir.Pic.nodeExtent` is the resolving site — the declared minimum, or the label's own reach where the text stands proud of it — `Ir.Pic.nodeExtent_covers` says a label at a node's anchor is inside the extent that node places against, and `Ir.Pic.nodeExtent_separates` says two nodes one separation plus both half-extents apart part their text. What is left is that this walk read that site: `Picture.Cx` carrying an `Ir.Pic.LabelMetric` (a function field beside `Cx.math`, which arrives the same way), `evalNode` reading the node body before it resolves the placement so there is something to measure, and `ownA`/`ownB` plus the registered `NodeGeom` coming from `Ir.Pic.nodeExtent` rather than the minimum alone. The metric's other end exists too and is not this module's: one export of layout's own `labelInk` (a second implementation would place nodes against one face and set them against another) and the driver elaborating twice, gated on `Elab.enginePictures`. Both ends are written and measured — the three-node row's labels part, W0336 falls to nothing on the reference corpus, +6.5% on a picture-heavy deck — and held back only because a signature landed in half leaves the tree red. So the statement below is provable as soon as the walk reads the site; it quantifies over a metric the walk still does not see, which is the whole of what remains.
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

-- owed: formulaFloor_covers
-- owner: LeanTex.Core.Ir
-- source: the recovery-floor policy (PLAN 2026-09-24, the floor-as-a-function-of-the-loss entry): `Ir.FloorHonest` is the one judge every floor is checked against, and `floorInk_covers` discharges it for the filtered salvage — the math source floor — for every registered code. This is the same statement at the engine's other translated salvage: a formula the parser *did* model but the page cannot set (W0003, `degraded`, so `Floor.content`) inks its glyph text, and the paid-for clause says it inks *something* whenever the construct carried content. `carried` is read through `Ir.floorChars` over the formula's own source rather than off the parsed list, deliberately: the scalars are both the floor's output and, read as `carried`, its reference set, so a statement over them is vacuous and would certify a floor that shipped nothing at all. The executable witness is the no-math-face rows of `recoveryChecks` and the `floorPolicyChecks` rows beside them, read off `Layout.Out`; the space-only shapes (`$\,$`, `${}$`, `$\quad$`) are the boundary the statement has to permit, since their source carries no content character either and a placeholder there would invent ink where an author wrote a thin space.
-- blocker: there is no relation between a `.formula`'s `src` and its `body` at the IR, and there cannot be one: `Ir.Inline.formula` carries both as independent fields, so the statement is false for an arbitrary pair and has to be conditioned on the parse — `MathParse.parseMath (rawsOf src) = .ok (body, _)`. That condition is a fold inversion over `parseToks`, which threads a token cursor, a pending grid and a note array through one mutual recursion, so no equation names "the list after token k" and nothing yet says that a content character of the source reaches the atom list. It is the same `Acc`-split, accumulator-statability work `floorChars_id` and `nodeLabel_mem` wait on at the other two floors, which is why all three are queued rather than one being asserted from the others.
-- goldens: no
/-- A formula the page cannot set inks something whenever its source carried
content: the paid-for clause of `Ir.FloorHonest` at the translated salvage,
the side `floorInk_accounts` holds unconditionally at the filtered one. -/
theorem formulaFloor_covers (c : DiagCode) (h : c.floor.ships)
    (raws : Array Parse.Raw) (body : Math.MList) (notes : Array MathParse.Note)
    (hp : MathParse.parseMath raws = .ok (body, notes)) :
    Ir.FloorHonest c.floor .translated
      (Ir.floorChars (Parse.rawSrc raws)) (Ir.formulaFloor body).toList := by
  sorry

-- owed: formulaFloor_separates
-- owner: LeanTex.Core.Ir
-- source: the `\cancelto` corollary (PLAN 2026-09-24, "a floor may be lossy; it may not be false"), carried from the one construct that was fixed by a table row to the family that cannot be. `\cancelto{0}{x}` inked `0x` — a product where the source says `x` cancels to `0` — and `Ir.floorNamedArgs` closed it by dropping the naming argument. A fraction has no naming argument: both operands are content, and the translated floor concatenates them, so `$\frac{1}{2}$` inks `12` and `$\binom{n}{k}$` inks `nk`. That is the identical defect with no table row available, and it is not confined to a faceless host: `Ir.plainTextOne` reads this floor for alt text, running heads, the PDF outline and the tagged structure tree, so a heading carrying `$\frac{1}{2}$` is announced as `12` even where the page sets the fraction correctly. The corpus already ships one: `math.tex`'s `$\sqrt[3]{x + 1}$` reads `3x + 1`. Measured before this record: `Half $\frac{1}{2}$ done` gives the plain-text reading `Half 12 done`. The statement is the general repair — two content operands of one nucleus are separated, so a kept pair can never read as an application of the operator standing between them — and it is false today, which is the point of stating it before the code.
-- blocker: not a proof wall but an unmade design decision, and it is not this file's to make alone. The separator vocabulary is user-visible in four channels at once (page ink, SVG label text, PDF outline, tagged tree) and has no locale-free answer for every nucleus: `/` reads correctly for a fraction but needs parentheses around a compound operand to stay true (`\frac{a+b}{c}` is not `a+b/c`), `√` is a glyph the body face may not carry so the repair would trade a false reading for a missing-glyph diagnostic, and `\binom` has no plain-text spelling that is not invented notation. The engine's own line is also not yet drawn: `^` and `_` are on `Ir.markupChars`, so the filtered floor already ships `x2` for `$x^2$` and the project accepted that as lossy rather than false — a rule that separates fraction operands and not scripts is answering half the question. What the statement fixes is the *shape* of the repair, so the vocabulary decision lands against it rather than around it, and `formulaFloor` grows its own walk over `Math.MList` instead of reusing `Math.MList.scalarsList`, whose job is the coverage census and whose omissions (no radical sign is ever pushed) are correct there and wrong here.
-- goldens: yes
/-- **A floor may be lossy; it may not be false.** The two content operands
of one nucleus never reach the page as their bare juxtaposition, so a reader
cannot read a fraction as a product. Stated as the inequality rather than as
a spelling, because what is owed is the separation and not the separator. -/
theorem formulaFloor_separates (num den : Math.MList)
    (hn : Ir.formulaFloor num ≠ "") (hd : Ir.formulaFloor den ≠ "") :
    Ir.formulaFloor (.cons (.atom .inner (.frac num den) .nil .nil false) .nil)
      ≠ Ir.formulaFloor num ++ Ir.formulaFloor den := by
  sorry

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
-- blocker: the channel is no longer missing and the statement is no longer vacuous, which turns this row from unstatable into *false for one of its two registry entries* — stated anyway, as `formulaFloor_separates` is, so the repair lands against it. What the channel fixed: `Diag.subject` is the dedup key, namespaced for some codes and unset for others, and W0103 and W0319 set nothing there at all, so the old spelling read the empty option and the whole quantification was trivially true. `Diag.refused` carries the name structurally (`Diag.of_refused`), `Compat.nameRefusalAsk` is the registry, and `nameRefusalRegistryChecks` closes it against the code list in both directions over the witness registry every code owes — a third name-refusal can no longer arrive invisibly, which is how `\usetheme` escaped. What remains is not a proof wall: W0319 is raised by *two* doors with different answers — the compat spellings, which do ask for `beamerthemeX.sty`, and the native `\theme{X}`, where no file beside the document would define a built-in bundle — so a per-code claim cannot be right for both. The registry needs the door rather than the code, or the native refusal needs a code of its own; that is a user-visible decision and Compat's to make. Behind it stands the wall this row always had: the quantification runs over `Elab.runRaws`'s whole diagnostic surface, an imperative preamble fold with no equational theory an induction can enter — the same wall the nine loop-shaped rows name
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

end Obligations
