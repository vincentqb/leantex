module

public import LeanTex.Core.Contrast
import all LeanTex.Core.Contrast
import all LeanTex.Core.Theme
import LeanTex.Core.Ir
import all LeanTex.Core.ContrastRatio
import all LeanTex.Core.Oklab
import all LeanTex.Core.Listing
import all LeanTex.Core.DesignRole
import all LeanTex.Core.SeedPalette
import all LeanTex.Core.PaletteData
import all LeanTex.Core.Color

/-! Kernel-checked contrast contracts for the shipped design constants and built-in themes. -/

namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir LeanTex.Core.Dim

public theorem pdf_default_aa : contrastMilli Color.black Color.white ≥ aaText := by
  decide +kernel

private theorem every_depth (P : Theme → Palette → Bool)
    (hdecks : Theme.builtin.all (fun th => P th (th.realize .decks)) = true)
    (hdocs : Theme.builtin.all (fun th => th.seeds.isNone || P th (th.realize .documents)) = true)
    (hposters : Theme.builtin.all (fun th => th.seeds.isNone || P th (th.realize .posters)) = true) :
    ∀ th ∈ Theme.builtin, ∀ d ∈ GroundDepth.all, P th (th.realize d) = true := by
  intro th hth d hd
  have h1 := List.all_eq_true.mp hdecks th hth
  have h2 := List.all_eq_true.mp hdocs th hth
  have h3 := List.all_eq_true.mp hposters th hth
  simp only [GroundDepth.all, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · cases hs : th.seeds with
    | none => rw [Theme.realize_depth_exact th hs .documents .decks]; exact h1
    | some _ => simpa [hs] using h2
  · exact h1
  · cases hs : th.seeds with
    | none => rw [Theme.realize_depth_exact th hs .posters .decks]; exact h1
    | some _ => simpa [hs] using h3

/-- A contract judged at the medium's size holds at every depth where it holds on a document's
page, a deck's stage, and for seeded bundles a poster's board (`Theme.realize_depth_exact`). -/
private theorem every_medium (P : Theme → Bool → Palette → Bool)
    (hdocs : Theme.builtin.all (fun th => P th false (th.realize .documents)) = true)
    (hdecks : Theme.builtin.all (fun th => P th true (th.realize .decks)) = true)
    (hposters :
      Theme.builtin.all (fun th => th.seeds.isNone || P th false (th.realize .posters)) = true) :
    ∀ th ∈ Theme.builtin, ∀ d ∈ GroundDepth.all, P th d.stage (th.realize d) = true := by
  intro th hth d hd
  have h1 := List.all_eq_true.mp hdocs th hth
  have h2 := List.all_eq_true.mp hdecks th hth
  have h3 := List.all_eq_true.mp hposters th hth
  simp only [GroundDepth.all, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl
  · exact h1
  · exact h2
  · cases hs : th.seeds with
    | none => rw [Theme.realize_depth_exact th hs .posters .documents]; exact h1
    | some _ =>
      have h3' : P th false (th.realize .posters) = true := by simpa [hs] using h3
      exact h3'

public theorem builtin_palettes_contract :
    ∀ th ∈ Theme.builtin, ∀ d ∈ GroundDepth.all,
      paletteContract (th.realize d) th.reported d.stage = true :=
  every_medium (fun th stage pal => paletteContract pal th.reported stage) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

public theorem default_covered : coveredContract {} = true := by decide +kernel

public theorem default_cover_monotone : coverMonotone {} = true := by decide +kernel

public theorem builtin_covers_monotone :
    ∀ th ∈ Theme.builtin, ∀ d ∈ GroundDepth.all, coverMonotone (th.realize d) = true :=
  every_depth (fun _ => coverMonotone) (by decide +kernel) (by decide +kernel) (by decide +kernel)

public theorem builtin_designs_covered :
    ∀ th ∈ Theme.builtin, ∀ d ∈ GroundDepth.all, coveredContract (th.realize d) th.reported = true :=
  every_depth (fun th pal => coveredContract pal th.reported) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

public theorem builtin_palette_contract_engine :
    (Theme.builtin.all fun t =>
      paletteContract (Theme.apply t {}).palette t.reported &&
      coveredContract (Theme.apply t {}).palette t.reported) = true := by
  decide +kernel

public theorem default_sites_contract :
    (Scheme.all.all fun s => (Design.sites {} s).all Site.passes) = true := by decide +kernel

end LeanTex.Core.Contrast
