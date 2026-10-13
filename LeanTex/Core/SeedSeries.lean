module

public import LeanTex.Core.SeedPalette
public import LeanTex.Core.ContrastSolve

/-!
A chart's categorical series colours, generated from the seeds a palette is
generated from (`SeedPalette`), for the charts a TeX build or a figure
script draws beside the deck: the export writes them with the palette
(`scripts/palette.lean --series N`).

* The first series is the accent as it reads on the paper, the palette's
  `accentText`, so a chart's subject stands in the colour the page's alerts
  do.
* Each next series is, among the candidates — every hue in `hueStep` steps
  from the accent's, at the series chroma (`chroma`, or what the gamut holds
  of it at the tone), at the tone nearest the paper that stands out from it
  as a mark and at the one that reads on it as text — the candidate farthest
  in ΔEOK from every series already taken and from the ink: farthest-point
  sampling (T. F. Gonzalez, "Clustering to minimize the maximum
  intercluster distance", Theoretical Computer Science 38, 1985), which
  keeps every prefix, so a chart of `k` series takes the first `k` whatever
  the count, and a series keeps its colour from one chart to the next.
* Every series stands out from the paper as a mark (SC 1.4.11's 3:1, with
  the generator's margin), the first reads on it as text, and no two stand
  nearer than `minGap` (`Generated.valid`).
-/

namespace LeanTex.Core.SeedSeries

open Ir Oklab Contrast

/-- The candidates' hue step, in millidegrees: 5°. -/
public def hueStep : Nat := 5000

/-- The most series a palette generates. -/
public def maxCount : Nat := 16

/-- The nearest two series may stand, ΔEOK at `labOf`'s scale: two JNDs
(`Oklab.okJnd`), a declared reading of the least difference at which two
marks side by side read as two colours, not a measurement. -/
public def minGap : Int := 2 * okJnd

/-- The candidates' chroma: the accent's own, never below five JNDs — the
code hues' (`CodeColor.codeChroma`) — so a quiet accent's charts still part
their series. -/
public def chroma (accent : Color) : Int := max (5 * okJnd) (SeedPalette.chromaOf accent)

/-- The tone of hue `h` (millidegrees) at chroma `C` nearest the paper that
meets `target` on it: the lightness bisected from the paper's toward the
far end of the axis, each candidate brought into the gamut at its lightness
and hue; `none` where the far end does not meet it either. -/
private def toneAt (paper : Color) (dark : Bool) (target : Nat) (C h : Int) : Option Color :=
  let dir := ofLch 0 C h
  let at_ (L : Int) : Color := (Okl.toGamut { L, a := dir.a, b := dir.b, f := fracOne }).toColor
  let pass (L : Int) : Bool := decide (target ≤ contrastMilli (at_ L) paper)
  let far : Int := if dark then 10 ^ 18 else 0
  if pass far then some (at_ (ContrastSolve.bisect pass 40 (labOf paper).L far)) else none

/-- The candidates, in the order ties are broken in: every hue from the
accent's on in `hueStep` steps, each at the tone that stands out from the
paper as a mark, then at the one that reads on it as text. -/
private def candidates (s : SeedPalette.Seeds) (t : SeedPalette.Targets) : Array (Color × Lab) :=
  let l := labOf s.accent
  let h0 := hueMilli l.a l.b
  let C := chroma s.accent
  (List.range (360000 / hueStep)).foldl (fun acc k =>
    let h := (h0 + (hueStep * k : Nat)) % 360000
    [t.edge, t.text].foldl (fun acc target =>
      match toneAt s.paper s.dark target C h with
      | some c => acc.push (c, labOf c)
      | none => acc) acc) #[]

/-- The least ΔEOK² from a value to any taken one. -/
private def nearestSq (l : Lab) (taken : List Lab) : Int :=
  taken.foldl (fun m x => min m (distSq l x)) (10 ^ 38)

/-- Farthest-point sampling: `n` more series, each the candidate whose
nearest taken value stands farthest, the earliest among equals. -/
private def pick (cands : Array (Color × Lab)) : Nat → List Lab → Array Color → Array Color
  | 0, _, acc => acc
  | n + 1, taken, acc =>
    let best := cands.foldl (fun (best : Option (Color × Lab × Int)) (c, l) =>
      let d := nearestSq l taken
      match best with
      | some (_, _, bd) => if bd < d then some (c, l, d) else best
      | none => some (c, l, d)) none
    match best with
    | some (c, l, _) => pick cands n (l :: taken) (acc.push c)
    | none => acc

/-- **The contract a generated series carries**: every series stands out
from the paper as a mark, the first reads on it as text, and no two stand
nearer than `minGap`. -/
public def contract (paper : Color) (t : SeedPalette.Targets) (series : List Color) : Bool :=
  (series.all fun c => decide (t.edge ≤ contrastMilli c paper)) &&
  (series.head?.all fun c => decide (t.text ≤ contrastMilli c paper)) &&
  decide (series.Pairwise fun c c' => minGap * minGap ≤ ContrastSolve.deltaEOkSq c c')

/-- Generated series: the colours, and the proof they meet the contract. -/
public structure Generated (s : SeedPalette.Seeds) (t : SeedPalette.Targets) where
  series : List Color
  valid : contract s.paper t series = true

/-- **Generate `n` series** from the seeds and the palette they generate: the
palette's accent text first, then farthest-point sampling over the
candidates; a count outside 1 to `maxCount`, or a palette whose series the
contract does not hold for, is refused with the reason. -/
public def generate (s : SeedPalette.Seeds) (t : SeedPalette.Targets)
    (p : SeedPalette.Generated s t) (n : Nat) : Except String (Generated s t) := do
  if n == 0 || maxCount < n then
    throw s!"a series count runs from 1 to {maxCount}, not {n}"
  let first := p.colors.accentText
  let rest := pick (candidates s t) (n - 1) [labOf first, labOf s.ink] #[]
  let series := first :: rest.toList
  if series.length != n then
    throw s!"only {series.length} of {n} series stand out from the paper"
  if h : contract s.paper t series = true then return ⟨series, h⟩
  else throw s!"{n} series cannot stand {minGap / 10 ^ 16}/100 ΔEOK apart and out from the paper"

/-- **Every generated series stands out from the paper as a mark, the first
reads on it as text, and no two stand nearer than `minGap`.** -/
public theorem generated_series_contract {s : SeedPalette.Seeds} {t : SeedPalette.Targets}
    (g : Generated s t) :
    (∀ c ∈ g.series, t.edge ≤ contrastMilli c s.paper) ∧
      (∀ c, g.series.head? = some c → t.text ≤ contrastMilli c s.paper) ∧
      g.series.Pairwise fun c c' => minGap * minGap ≤ ContrastSolve.deltaEOkSq c c' := by
  have h := g.valid
  simp only [contract, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun c hc => ?_, h3⟩
  rw [hc] at h2
  simpa using h2

/-- **The export**: an xcolor colour per series, `<stem>Series<k>` from 1, in
the order generated. -/
public def declarations (stem : String) (series : List Color) : String :=
  String.join (series.zipIdx.map fun (c, i) =>
    "\\definecolor{" ++ stem ++ "Series" ++ toString (i + 1) ++ "}{HTML}{" ++
      Color.hexByte c.r ++ Color.hexByte c.g ++ Color.hexByte c.b ++ "}\n")

end LeanTex.Core.SeedSeries
