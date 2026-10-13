module

public import LeanTex.Core.Theme
import all LeanTex.Core.Theme
import all LeanTex.Core.Ir
import all LeanTex.Core.SeedPalette
import all LeanTex.Core.PaletteData
import all LeanTex.Core.DesignRole
import all LeanTex.Core.ContrastRatio
import all LeanTex.Core.Oklab
import all LeanTex.Core.Color

/-! Kernel-checked contracts over the shipped bundles, in a leaf module so their evaluations run
beside the build; each quantifies over `Theme.builtin`. -/

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir

public theorem titlepage_align_declared_engine :
    (builtin.all fun t =>
      match (apply t {}).styles.find? "titlepage" with
      | some st => st.align.isSome && st.separator.isSome
      | none => true) = true := by decide

public theorem builtin_styles_nodup :
    (builtin.all fun th => nodupKeys th.styles.entries.toList) = true := by decide

public theorem builtin_names_plain :
    (builtin.all fun th => th.palette.entries.toList.all fun e => plainName e.1.key) = true := by
  decide

/-- Where the contracts judge a shipped bundle installed: a deck's stage and a document's page. -/
@[expose] public def installs : List ClassColors :=
  [{ row := .stage, depth := .decks }, { row := .latex, depth := .documents }]

/-- A shipped bundle's palette where a class installs it. -/
@[expose] public def installedAt (th : Theme) (c : ClassColors) : Palette :=
  { th.realize c.depth with classColors := c }

/-- The schemes a bundle's colours are declared for: the printed page and the light screen. -/
@[expose] public def shipped : List Scheme := [.print, .light]

private theorem sites_at (c : ClassColors) (h : builtin.all (fun th => shipped.all fun s =>
      (Design.sites (installedAt th c) s).all fun site =>
        site.passes || th.reported.contains site.role) = true) :
    ∀ th ∈ builtin, ∀ s ∈ shipped, ∀ site ∈ Design.sites (installedAt th c) s,
      (site.passes || th.reported.contains site.role) = true :=
  fun th hth s hs site hsite =>
    List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h th hth) s hs) site hsite

private theorem sites_stage : builtin.all (fun th => shipped.all fun s =>
    (Design.sites (installedAt th { row := .stage, depth := .decks }) s).all fun site =>
      site.passes || th.reported.contains site.role) = true := by
  decide +kernel

private theorem sites_latex : builtin.all (fun th => shipped.all fun s =>
    (Design.sites (installedAt th { row := .latex, depth := .documents }) s).all fun site =>
      site.passes || th.reported.contains site.role) = true := by
  decide +kernel

public theorem builtin_sites_contract :
    ∀ th ∈ builtin, ∀ c ∈ installs, ∀ s ∈ shipped, ∀ site ∈ Design.sites (installedAt th c) s,
      (site.passes || th.reported.contains site.role) = true := by
  intro th hth c hc
  simp only [installs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact sites_at _ sites_stage th hth
  · exact sites_at _ sites_latex th hth

/-- moloch's lineage colour, `mLightBrown` (beamercolorthememoloch.sty). -/
@[expose] public def molochLineage : Color := Color.ofHtml 0xEB 0x81 0x1B

public theorem moloch_lineage_exact (d : GroundDepth) :
    Design.declared? (moloch.realize d) .alert = some molochLineage ∧
      Design.declared? (moloch.realize d) .progressFill = some molochLineage ∧
      Design.declared? (moloch.realize d) .separator = some molochLineage := by
  rw [realize_depth_exact moloch rfl d .decks]
  exact ⟨rfl, rfl, rfl⟩

public theorem builtin_muted_contract :
    (builtin.all fun th => installs.all fun c => shipped.all fun s =>
        match Design.at (installedAt th c) s .muted, Design.at (installedAt th c) s .page with
        | some m, some p => decide (4600 ≤ Contrast.contrastMilli m p)
        | _, _ => true) &&
      (ClassRow.all.all fun row => [GroundDepth.documents, .decks].all fun d =>
        Scheme.all.all fun s =>
          let pal : Palette := { classColors := { row, depth := d } }
          match Design.at pal s .muted, Design.at pal s .page with
          | some m, some p => decide (4600 ≤ Contrast.contrastMilli m p)
          | _, _ => true) = true := by
  decide +kernel

end LeanTex.Core.Theme
