import Obligations
import LeanTex.Core.HtmlDoc

/-!
# The vertical rhythm's contract: three statements the engine does not yet earn

Measured first (`scripts/rhythm.lean`, the `rhythm` tier and its HTML and
private-document reports); stated here once per fact, over the engine's own
functions, quantified over what they govern. Each is owed: two are false on
today's tree, as the measurements named, and one is true on every fixture
and blocked on the same loop reading the attribution rows wait on.
-/

namespace Obligations.Rhythm

open LeanTex.Core LeanTex.Core.Ir LeanTex.Core.Layout Obligations

-- owed: peer_gap_exact
-- owner: LeanTex.Core.Layout
-- source: the rhythm audit (PLAN 2026-09-26, the rhythm-audit entry). `HtmlDoc.backend_gaps_agree` holds the rhythm table's rows to the tokens both backends read, and nothing holds the PDF's shipped page to the table: the peer row is `flushGap_default_exact`'s one `.skip` of the parskip, private to Layout, with no statement that the lines it separates stand the leading plus that skip apart. Measured on every fixture that declares the boundary: 18.000 bp at the article base (12 + 6) and 13.200 bp in the slides class (13.2 + 0), exact to the sp in `tests/rhythm/*.tex` through `rhythm --table`.
-- blocker: the two loops between the block walk and the pages, as `lines_attributed_covers` (the driver loop over `doc.body` threading `Acc`, and the placement pass over the op stream): `LeanTex.Core.Loop` reads them in place, but the invariant the statement needs — the placement pass's pen advances by the leading plus the skips it meets and by nothing else between two plain lines — is over `Acc` and the private `B`, so it must be written inside Layout and exported as the corollary this reads. No goldens move: the statement is today's behaviour.
-- goldens: no
/-- **Two peer paragraphs stand one leading and one parskip apart.** A
document of two plain paragraphs that each set one line on one page ships
their baselines exactly the page's leading plus its declared paragraph skip
apart — the peer row of `Ir.rhythmGapQuanta` realized on the page, not only
in the table (`HtmlDoc.backend_gaps_agree`'s PDF half). Stated for a skip spelled in
sp, so no face's em or ex enters it; whatever class the document is, the
geometry it is laid out in carries the skip. -/
theorem peer_gap_exact (geom : Geom) (fs : Font.FontSet) (doc : Ir.Doc)
    (a b : Array Ir.Inline) (p y₁ y₂ : Dim.Sp)
    (ha : plainPara (.para a)) (hb : plainPara (.para b))
    (hp : geom.parskip.width = { sp := p })
    (hflow : doc.docClass.record.model = .flow)
    (hlines : inkBaselines (Layout.run geom fs none { doc with body := #[.para a, .para b] })
      = [y₁, y₂]) :
    y₂ - y₁ = Ir.leadingFor geom.fontSize geom.leading + p := by
  sorry

/-- A LaTeX glue as its source declares it — natural width, stretch and
shrink in thousandths of TeX's point (1/72.27 in) — with the file and line
that declare it. -/
structure SourcedGlue where
  natural : Int
  stretch : Int
  shrink : Int
  source : String

/-- The display skip each builtin class's LaTeX lineage declares at the size
it loads. `\belowdisplayskip` is `\abovedisplayskip` in every size file (the
line after), so one glue serves both.

- `article`, and the classes whose LaTeX half is an article (`webpage`,
  `card`): size10.clo:49, `\abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@`.
- `resume`: moderncv.cls:62 executes `11pt`, and :66 inputs size11.clo,
  whose line 49 is `\abovedisplayskip 11\p@ \@plus3\p@ \@minus6\p@`.
- `slides`: beamer.cls:155 defaults `\beamer@size` to size11.clo, line 49.
- `poster`: the same size11.clo:49, through beamer.cls:155 —
  beamerposter.sty:244 replaces `\normalsize` with its own `\fontsize` and
  never resets the display skips, so they stay at the 11pt file's values. -/
def displaySource : Ir.DocClass → SourcedGlue
  | .article | .webpage | .card => ⟨10000, 2000, 5000, "size10.clo:49"⟩
  | .resume => ⟨11000, 3000, 6000, "size11.clo:49 via moderncv.cls:62,66"⟩
  | .slides => ⟨11000, 3000, 6000, "size11.clo:49 via beamer.cls:155"⟩
  | .poster => ⟨11000, 3000, 6000, "size11.clo:49 via beamer.cls:155; beamerposter.sty:244"⟩

/-- A length in the engine's sp (65536 to the bp, 1/72 in) as thousandths of
TeX's point: × 72.27/72. The unit is the point of the conversion — a length
compared with a LaTeX source in the engine's own pt is off by 0.375 %. -/
def milliTexPt (v : Dim.Sp) : Int := v * 72270 / (72 * 65536)

/-- The class's body size, as its record declares it. -/
def classBase (c : Ir.DocClass) : Dim.Sp := c.record.fontSize.getD Ir.baseFontSize

-- owed: display_skips_between
-- owner: LeanTex.Core.Ir
-- source: the rhythm audit (PLAN 2026-09-26, the rhythm-audit entry). `Ir.display_between` states the article-base display skip inside `10pt plus 2pt minus 5pt` by comparing the engine's value against `Dim.pt 12`, which is 12 bp, not 12 TeX points: read in the source's own unit, the quantized 12 bp is 12.045 pt, 0.045 pt over size10.clo's ceiling. The same comparison had never been made for any other class. Measured (engine display skip at the class base, against its lineage's range in TeX pt): article, webpage, card 12.045 against 5–12 (over by 0.045); resume 12.045 against 5–14; slides 13.249 against 5–14; poster 29.967 against 5–14 (over by 15.97), because beamerposter scales the body and not the display skips.
-- blocker: false on today's tree for four classes of six, so this is a decision before it is a proof: whether the quantized display skip gives way to the source's range (a default at most 12 TeX pt at the 10pt base, 11.955 bp, which is off the rhythm) or the statement's range is widened by a declared divergence per class — a human gate, since it is a new deliberate divergence from LaTeX either way. Once decided the proof is `decide` over the six classes: every quantity is a closed constant.
-- goldens: yes
/-- **A class's display skip is one its LaTeX lineage could set.** For every
builtin class, the display skip the engine ships by default above and below
a formula, read in TeX points at the class's base size, lies within the glue
its source declares: natural less shrink to natural plus stretch. -/
theorem display_skips_between (c : Ir.DocClass) :
    (displaySource c).natural - (displaySource c).shrink
        ≤ milliTexPt (Ir.displayAbove {} (classBase c)).width.sp ∧
      milliTexPt (Ir.displayAbove {} (classBase c)).width.sp
        ≤ (displaySource c).natural + (displaySource c).stretch ∧
      milliTexPt (Ir.displayBelow {} (classBase c)).width.sp
        = milliTexPt (Ir.displayAbove {} (classBase c)).width.sp := by
  sorry

/-- The base sheet's rules, as `(selector list, declarations)` pairs: the
text between one `}` and the next `{`, and the text inside the braces. A
reader of the emitted stylesheet, not of any engine decision. -/
def cssRules (css : String) : List (List String × String) :=
  (css.splitOn "}").filterMap fun chunk =>
    match chunk.splitOn "{" with
    | [sel, body] =>
      some ((sel.splitOn ",").map (·.trimAscii.toString), body)
    | _ => none

/-- Does some rule whose selector list names `sel` exactly set that element's
top margin? A bare type or type-and-class selector has specificity at least
(0,0,1), which beats every `:where(…)` rule `HtmlDoc.blockGapCss` emits, whatever the
order the sheet states them in. -/
def shadowsGap (css sel : String) : Bool :=
  (cssRules css).any fun (sels, body) =>
    sels.contains sel &&
      ((body.splitOn "margin:").length > 1 || (body.splitOn "margin-top:").length > 1)

-- owed: blockGap_owner_contract
-- owner: LeanTex.Core.HtmlDoc
-- source: the rhythm audit (PLAN 2026-09-26, the rhythm-audit entry). `HtmlDoc.single_owner_gap_exact` proves the realized gap equals the emitted one when a boundary has one emitter, and `backend_gaps_agree` holds the emitted numbers to the PDF's; neither sees the cascade. The base sheet's own element rules — `p { margin: 0; … }`, `ul, ol { margin: 0; … }`, `blockquote { margin: 0; … }`, `h1, h2, h3, h4 { … margin: 0 0 …; }` — outrank every `:where(* + …)` gap rule by specificity, so in Chromium 151.0.7922.34 every one of those boundaries computes `margin-top: 0px`: a paragraph after a paragraph, a list after a paragraph, a heading after a paragraph, and an unnumbered display (a `p.display`) ship no gap at all. Measured: par-par 23.188 px, one line, against the declared 34.8 (2.00 against 3.00 quanta); the numbered equation, a `div`, keeps its 1.45 rem.
-- blocker: false on today's tree; the fix is the sheet's, in HtmlDoc (owned this round by the rhythm-pic branch): state the element rules' zero margins inside `:where()` too, before `blockGapCss`, so the gap rules win at equal specificity by standing later, or drop the margin from the element rules. The heading's own band below (`margin: 0 0 <peer>`) has to move with it. Once the sheet is fixed the proof is `decide` over `blockGapKinds` for a fixed configuration, and the general statement needs `baseCss`'s dependence on `cfg` and `doc` factored so the element rules are one constant.
-- goldens: no
/-- **A declared gap is the gap the page renders.** For every block element
the base sheet emits a gap rule for (`HtmlDoc.blockGapKinds`), no other rule
of the sheet sets that element's top margin at a higher specificity — the
premise `HtmlDoc.single_owner_gap_exact` needs before the emitted value is the
realized one. -/
theorem blockGap_owner_contract (cfg : HtmlDoc.Config) (doc : Ir.Doc) :
    ∀ e ∈ HtmlDoc.blockGapKinds, shadowsGap (HtmlDoc.baseCss cfg doc) e.1 = false := by
  sorry

end Obligations.Rhythm
