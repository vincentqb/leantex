module

public import LeanTex.Core.SeedPalette
import LeanTex.Core.CodeColor
public import LeanTex.Core.ContrastSolve

/-! A chart's categorical series colours generated from a palette's seeds: the accent text first,
then farthest-point sampling in ΔEOK (Gonzalez 1985) over hues at mark and text tones. -/

namespace LeanTex.Core.SeedSeries

open Ir Oklab Contrast

/-- The candidates' hue step in millidegrees, a declared bound on the search's cost. -/
public def hueStep : Nat := 5000

/-- The most series a palette generates, a declared bound (ColorBrewer stops at twelve, Tableau at
twenty). -/
public def maxCount : Nat := 16

/-- The nearest two series may stand, ΔEOK at `labOf`'s scale: two JNDs, a declared reading. -/
public def minGap : Int := 2 * okJnd

/-- `minGap` as the README spells it, in hundredths of a unit of ΔEOK. -/
private def minGapText : String :=
  let c := minGap / 10 ^ 16
  s!"ΔEOK 0.{if c < 10 then "0" else ""}{c}"

/-- The candidates' chroma: the accent's own, never below the code hues'. -/
public def chroma (accent : Color) : Int := max CodeColor.codeChroma (SeedPalette.chromaOf accent)

/-- How far from the grey's lightness a tone's boundary is looked for first: 0.06 of the axis. -/
private def guessSpan : Int := 6 * 10 ^ 16

/-- The tone of hue `h` at chroma `C` nearest the paper that meets `target` on it, or `none`. -/
private def toneAt (paper : Color) (dark : Bool) (target : Nat) (C h : Int) : Option Color :=
  let dir := ofLch 0 C h
  let at_ (L : Int) : Color := (Okl.toGamut { L, a := dir.a, b := dir.b, f := fracOne }).toColor
  let pass (L : Int) : Bool := decide (target ≤ contrastMilli (at_ L) paper)
  let far : Int := if dark then 10 ^ 18 else 0
  let guess := ContrastSolve.greyLightness (ContrastSolve.luminanceAt paper target dark)
  if pass far then some (at_ (ContrastSolve.bisectNear pass 20 (labOf paper).L far guess guessSpan))
  else none

/-- The candidates in tie-breaking order: every hue in `hueStep` steps from the accent's, at the
mark tone then the text tone. -/
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

/-- The candidate whose nearest taken value stands farthest, the earliest
among equals. -/
private def farthest (cands : Array (Color × Lab)) (taken : List Lab) : Option (Color × Lab) :=
  (cands.foldl (fun (best : Option (Color × Lab × Int)) (c, l) =>
    let d := nearestSq l taken
    match best with
    | some (_, _, bd) => if bd < d then some (c, l, d) else best
    | none => some (c, l, d)) none).map fun (c, l, _) => (c, l)

/-- Farthest-point sampling: `n` more series, each the `farthest` candidate
from every value taken so far. -/
private def pick (cands : Array (Color × Lab)) : Nat → List Lab → Array Color → Array Color
  | 0, _, acc => acc
  | n + 1, taken, acc =>
    match farthest cands taken with
    | some (c, l) => pick cands n (l :: taken) (acc.push c)
    | none => acc

private theorem pick_acc (cands : Array (Color × Lab)) :
    ∀ (n : Nat) (taken : List Lab) (acc : Array Color),
      pick cands n taken acc = acc ++ pick cands n taken #[]
  | 0, _, acc => by simp [pick]
  | n + 1, taken, acc => by
    simp only [pick]
    split
    · rw [pick_acc cands n _ (acc.push _), pick_acc cands n _ (#[].push _)]
      simp
    · simp

private theorem pick_take (cands : Array (Color × Lab)) :
    ∀ (m n : Nat) (taken : List Lab),
      (pick cands (m + n) taken #[]).toList.take m = (pick cands m taken #[]).toList
  | 0, _, _ => by simp [pick]
  | m + 1, n, taken => by
    rw [Nat.add_right_comm]
    simp only [pick]
    split
    · rw [pick_acc cands (m + n), pick_acc cands m]
      simp [pick_take cands m n]
    · simp

/-- The `n` series the seeds' palette generates: its accent text, then `n - 1` picks. -/
private def seriesOf (s : SeedPalette.Seeds) (t : SeedPalette.Targets) (p : SeedPalette.Generated s t)
    (n : Nat) : List Color :=
  let cands := if n ≤ 1 then #[] else candidates s t
  p.colors.accentText :: (pick cands (n - 1) [labOf p.colors.accentText, labOf s.ink] #[]).toList

private theorem seriesOf_take (s : SeedPalette.Seeds) (t : SeedPalette.Targets)
    (p : SeedPalette.Generated s t) {k n : Nat} (hk : 1 ≤ k) (hn : k ≤ n) :
    seriesOf s t p k = (seriesOf s t p n).take k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
  unfold seriesOf
  simp only [List.take_succ_cons, Nat.add_sub_cancel, show k + 1 + n - 1 = k + n by omega]
  congr 1
  by_cases h0 : k = 0
  · subst h0
    simp [pick]
  · have h1 : ¬ k + 1 ≤ 1 := by omega
    by_cases h2 : k + 1 + n ≤ 1
    · omega
    · simp only [h1, h2, ite_false]
      exact (pick_take _ k n _).symm

/-- The contract a generated series carries: marks stand out from the paper, the first reads as
text, no two nearer than `minGap`, none after the first near the ink. -/
public def contract (paper ink : Color) (t : SeedPalette.Targets) (series : List Color) : Bool :=
  (series.all fun c => decide (t.edge ≤ contrastMilli c paper)) &&
  (series.head?.all fun c => decide (t.text ≤ contrastMilli c paper)) &&
  decide (series.Pairwise fun c c' => minGap * minGap ≤ ContrastSolve.deltaEOkSq c c') &&
  ((series.drop 1).all fun c => decide (minGap * minGap ≤ ContrastSolve.deltaEOkSq c ink))

/-- Generated series: the colours, and the proof they meet the contract. -/
public structure Generated (s : SeedPalette.Seeds) (t : SeedPalette.Targets) where
  series : List Color
  valid : contract s.paper s.ink t series = true

/-- Generate `n` series from the seeds, refusing a count outside 1 to `maxCount`, too few
candidates, or a failed contract. -/
public def generate (s : SeedPalette.Seeds) (t : SeedPalette.Targets)
    (p : SeedPalette.Generated s t) (n : Nat) : Except String (Generated s t) :=
  if n = 0 ∨ maxCount < n then
    .error s!"a series count runs from 1 to {maxCount}, not {n}"
  else if (seriesOf s t p n).length ≠ n then
    .error s!"the candidates gave {(seriesOf s t p n).length} of {n} series"
  else if h : contract s.paper s.ink t (seriesOf s t p n) = true then .ok ⟨seriesOf s t p n, h⟩
  else .error s!"{n} series do not all stand {minGapText} apart and from the ink"

private theorem generate_ok {s : SeedPalette.Seeds} {t : SeedPalette.Targets}
    {p : SeedPalette.Generated s t} {n : Nat} {g : Generated s t} (h : generate s t p n = .ok g) :
    1 ≤ n ∧ n ≤ maxCount ∧ g.series = seriesOf s t p n ∧ (seriesOf s t p n).length = n := by
  unfold generate at h
  split at h
  · cases h
  · rename_i hn
    split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
        exact ⟨by omega, by omega, rfl, by simpa using hl⟩
      · cases h

public theorem generate_head_exact {s : SeedPalette.Seeds} {t : SeedPalette.Targets}
    {p : SeedPalette.Generated s t} {n : Nat} {g : Generated s t} (h : generate s t p n = .ok g) :
    g.series.head? = some p.colors.accentText := by
  obtain ⟨-, -, hs, -⟩ := generate_ok h
  rw [hs]
  rfl

public theorem generate_take_exact {s : SeedPalette.Seeds} {t : SeedPalette.Targets}
    {p : SeedPalette.Generated s t} {n k : Nat} {g : Generated s t} (h : generate s t p n = .ok g)
    (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∃ g' : Generated s t, generate s t p k = .ok g' ∧ g'.series = g.series.take k := by
  obtain ⟨-, hmax, hs, hlen⟩ := generate_ok h
  have hv := g.valid
  rw [hs] at hv
  have htake := seriesOf_take s t p hk hkn
  have hvk : contract s.paper s.ink t (seriesOf s t p k) = true := by
    rw [htake]
    simp only [contract, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
    refine ⟨⟨⟨fun c hc => h1 c (List.mem_of_mem_take hc), ?_⟩, h3.take⟩,
      fun c hc => h4 c ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      cases hser : seriesOf s t p n with
      | nil => simp
      | cons a as => simpa [hser] using h2
    · rw [List.drop_take] at hc
      exact List.mem_of_mem_take hc
  have hlk : (seriesOf s t p k).length = k := by
    rw [htake, List.length_take, hlen]
    omega
  refine ⟨⟨seriesOf s t p k, hvk⟩, ?_, show seriesOf s t p k = g.series.take k by rw [hs, htake]⟩
  unfold generate
  rw [ite_eq_right (by omega), ite_eq_right (by simpa using hlk), dite_eq_left hvk]

public theorem generated_series_contract {s : SeedPalette.Seeds} {t : SeedPalette.Targets}
    (g : Generated s t) :
    (∀ c ∈ g.series, t.edge ≤ contrastMilli c s.paper) ∧
      (∀ c, g.series.head? = some c → t.text ≤ contrastMilli c s.paper) ∧
      (g.series.Pairwise fun c c' => minGap * minGap ≤ ContrastSolve.deltaEOkSq c c') ∧
      ∀ c ∈ g.series.drop 1, minGap * minGap ≤ ContrastSolve.deltaEOkSq c s.ink := by
  have h := g.valid
  simp only [contract, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun c hc => ?_, h3, h4⟩
  rw [hc] at h2
  simpa using h2

/-- The export: an xcolor colour per series, `<stem>Series<k>` from 1, in generated order. -/
public def declarations (stem : String) (series : List Color) : String :=
  String.join (series.zipIdx.map fun (c, i) =>
    "\\definecolor{" ++ stem ++ "Series" ++ toString (i + 1) ++ "}{HTML}{" ++
      Color.hexByte c.r ++ Color.hexByte c.g ++ Color.hexByte c.b ++ "}\n")

end LeanTex.Core.SeedSeries
