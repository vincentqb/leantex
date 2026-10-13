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

private theorem both_depths (P : Theme.Theme → Palette → Bool)
    (hdecks : Theme.builtin.all (fun th => P th (th.realize .decks)) = true)
    (hdocs : Theme.builtin.all (fun th => th.seeds.isNone || P th (th.realize .documents)) = true) :
    ∀ th ∈ Theme.builtin, ∀ d ∈ [GroundDepth.documents, .decks], P th (th.realize d) = true := by
  intro th hth d hd
  have h1 := List.all_eq_true.mp hdecks th hth
  have h2 := List.all_eq_true.mp hdocs th hth
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · cases hs : th.seeds with
    | none => rw [Theme.realize_depth_exact th hs .documents .decks]; exact h1
    | some _ => simpa [hs] using h2
  · exact h1

public theorem builtin_palettes_contract :
    ∀ th ∈ Theme.builtin, ∀ d ∈ [GroundDepth.documents, .decks],
      paletteContract (th.realize d) th.reported = true :=
  both_depths (fun th pal => paletteContract pal th.reported) (by decide +kernel)
    (by decide +kernel)

public theorem default_covered : coveredContract {} = true := by decide +kernel

public theorem default_cover_monotone : coverMonotone {} = true := by decide +kernel

public theorem builtin_covers_monotone :
    ∀ th ∈ Theme.builtin, ∀ d ∈ [GroundDepth.documents, .decks],
      coverMonotone (th.realize d) = true :=
  both_depths (fun _ => coverMonotone) (by decide +kernel) (by decide +kernel)

public theorem builtin_designs_covered :
    ∀ th ∈ Theme.builtin, ∀ d ∈ [GroundDepth.documents, .decks],
      coveredContract (th.realize d) th.reported = true :=
  both_depths (fun th pal => coveredContract pal th.reported) (by decide +kernel)
    (by decide +kernel)

public theorem builtin_palette_contract_engine :
    (Theme.builtin.all fun t =>
      paletteContract (Theme.apply t {}).palette t.reported &&
      coveredContract (Theme.apply t {}).palette t.reported) = true := by
  decide +kernel

public theorem default_sites_contract :
    (Scheme.all.all fun s => (Design.sites {} s).all Site.passes) = true := by decide +kernel

end LeanTex.Core.Contrast
