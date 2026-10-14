module

public import LeanTex.Core.SeedPalette
public import LeanTex.Core.ContrastSolve

/-! A chart's categorical series colours generated from a palette's seeds: the accent text first,
then farthest-point sampling (Gonzalez 1985) for the nearest of four simulated readers (Okabe & Ito's
Color Universal Design; Machado, Oliveira & Fernandes 2009). -/

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

/-- A colour as each simulated reader sees it, typical vision first (`Oklab.Vision.all`). -/
public def views (c : Color) : List Lab := Vision.all.map (labIn · c)

/-- The least ΔEOK² between two colours' readings, reader by reader. -/
private def viewSq (v w : List Lab) : Int :=
  (v.zip w).foldl (fun m (x, y) => min m (distSq x y)) (10 ^ 38)

/-- Whether two colours stand `minGap` apart for every simulated reader. -/
public def apart (c c' : Color) : Bool :=
  Vision.all.all fun v => decide (minGap * minGap ≤ distSq (labIn v c) (labIn v c'))

/-- Whether a hue is warm, within a quarter turn of OKLCH 40°, between sRGB red's 29° and Okabe and
Ito's vermilion's 47.5°: magentas through yellow. -/
private def warmHue (h : Int) : Bool :=
  let d := (h - 40000) % 360000
  decide (min d (360000 - d) < 90000)

/-- Whether a colour's hue is warm (`warmHue`). -/
private def warm (c : Color) : Bool :=
  let l := labOf c
  warmHue (hueMilli l.a l.b)

/-- Whether a hue stands within 7.5° of sRGB red's OKLCH 29.2°, which Okabe and Ito replace by
vermilion (https://jfly.uni-koeln.de/color/). -/
private def pureRed (h : Int) : Bool :=
  let d := (h - 29200) % 360000
  decide (min d (360000 - d) < 7500)

/-- Whether a hue is a yellow-green CUD avoids, to OKLCH 150°, from the disliked region's warm edge
on a light page, where a yellow dark enough to stand out is an olive, and from its cool edge on a
dark one. -/
private def yellowGreen (dark : Bool) (h : Int) : Bool :=
  decide ((if dark then ContrastSolve.dislikedHi else ContrastSolve.dislikedLo) ≤ h ∧ h ≤ 150000)

/-- The tones a hue offers, in steps of 0.10 lightness away from the paper from its floor band, so
neighbours of one temperature part by lightness (Okabe & Ito). -/
private def toneSteps : List Int := [0, 1, 2, 3]

/-- A candidate: its colour, its readings (`views`) and whether it is warm. -/
private abbrev Cand := Color × List Lab × Bool

/-- The candidates in tie-breaking order: each hue in `hueStep` steps at its `toneSteps` meeting the
marks' floor, off pure red, the yellow-greens and the disliked region. -/
private def candidates (s : SeedPalette.Seeds) (t : SeedPalette.Targets) : Array Cand :=
  let l := labOf s.accent
  let h0 := hueMilli l.a l.b
  let away : Int := if s.dark then 10 ^ 17 else -(10 ^ 17)
  (List.range (360000 / hueStep)).foldl (fun acc k =>
    let h := (h0 + (hueStep * k : Nat)) % 360000
    if pureRed h || yellowGreen s.dark h then acc
    else
      let L0 := ContrastSolve.bandL t.edge [s.paper] h
      toneSteps.foldl (fun acc j =>
        let c := ContrastSolve.edgeAt h (L0 + j * away)
        if decide (t.edge ≤ contrastMilli c s.paper) && !ContrastSolve.disliked c then
          acc.push (c, views c, warm c)
        else acc) acc) #[]

/-- The least ΔEOK² from a candidate's readings to any taken one's. -/
private def nearestSq (v : List Lab) (taken : List (List Lab)) : Int :=
  taken.foldl (fun m x => min m (viewSq v x)) (10 ^ 38)

/-- The candidate `keep` admits whose nearest taken value stands farthest, the earliest among equals. -/
private def farthestOf (cands : Array Cand) (taken : List (List Lab)) (keep : Cand → Bool) :
    Option (Cand × Int) :=
  cands.foldl (fun (best : Option (Cand × Int)) c =>
    if keep c then
      let d := nearestSq c.2.1 taken
      match best with
      | some (_, bd) => if bd < d then some (c, d) else best
      | none => some (c, d)
    else best) none

/-- The farthest candidate of the other temperature than the last pick where one stands `minGap`
apart, else the farthest of either: Okabe and Ito alternate warm and cool. -/
private def farthest (cands : Array Cand) (taken : List (List Lab)) (lastWarm : Bool) :
    Option Cand :=
  match farthestOf cands taken (fun c => c.2.2 != lastWarm) with
  | some (c, d) => if minGap * minGap ≤ d then some c else (farthestOf cands taken fun _ => true).map (·.1)
  | none => (farthestOf cands taken fun _ => true).map (·.1)

/-- Farthest-point sampling: `n` more series, each the `farthest` candidate
from every value taken so far. -/
private def pick (cands : Array Cand) : Nat → List (List Lab) → Bool → Array Color → Array Color
  | 0, _, _, acc => acc
  | n + 1, taken, w, acc =>
    match farthest cands taken w with
    | some (c, v, w') => pick cands n (v :: taken) w' (acc.push c)
    | none => acc

private theorem pick_acc (cands : Array Cand) :
    ∀ (n : Nat) (taken : List (List Lab)) (w : Bool) (acc : Array Color),
      pick cands n taken w acc = acc ++ pick cands n taken w #[]
  | 0, _, _, acc => by simp [pick]
  | n + 1, taken, w, acc => by
    simp only [pick]
    split
    · rw [pick_acc cands n _ _ (acc.push _), pick_acc cands n _ _ (#[].push _)]
      simp
    · simp

private theorem pick_take (cands : Array Cand) :
    ∀ (m n : Nat) (taken : List (List Lab)) (w : Bool),
      (pick cands (m + n) taken w #[]).toList.take m = (pick cands m taken w #[]).toList
  | 0, _, _, _ => by simp [pick]
  | m + 1, n, taken, w => by
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
  p.colors.accentText ::
    (pick cands (n - 1) [views p.colors.accentText, views s.ink] (warm p.colors.accentText) #[]).toList

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
      exact (pick_take _ k n _ _).symm

/-- The contract a generated series carries: marks stand out from the paper, the first reads as
text, and no two, nor any after the first and the ink, stand within `minGap` for any reader. -/
public def contract (paper ink : Color) (t : SeedPalette.Targets) (series : List Color) : Bool :=
  (series.all fun c => decide (t.edge ≤ contrastMilli c paper)) &&
  (series.head?.all fun c => decide (t.text ≤ contrastMilli c paper)) &&
  decide (series.Pairwise fun c c' => apart c c' = true) &&
  ((series.drop 1).all fun c => apart c ink)

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
  else .error s!"{n} series do not all stand {minGapText} apart and from the ink, for typical \
vision and simulated protanopia, deuteranopia and tritanopia"

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
      (g.series.Pairwise fun c c' => apart c c' = true) ∧
      ∀ c ∈ g.series.drop 1, apart c s.ink = true := by
  have h := g.valid
  simp only [contract, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun c hc => ?_, h3, h4⟩
  rw [hc] at h2
  simpa using h2

public theorem apart_exact {c c' : Color} (h : apart c c' = true) :
    ∀ v ∈ Vision.all, minGap * minGap ≤ distSq (labIn v c) (labIn v c') := by
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp h v hv)

/-- The export: an xcolor colour per series, `<stem>Series<k>` from 1, in generated order. -/
public def declarations (stem : String) (series : List Color) : String :=
  String.join (series.zipIdx.map fun (c, i) =>
    "\\definecolor{" ++ stem ++ "Series" ++ toString (i + 1) ++ "}{HTML}{" ++
      c.hex (hash := false) ++ "}\n")

end LeanTex.Core.SeedSeries
