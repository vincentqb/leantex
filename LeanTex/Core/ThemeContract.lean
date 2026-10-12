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

/-!
Kernel-checked contracts over the shipped bundles, kept in a leaf so the
evaluations run beside the build rather than in series with every module
that imports `Theme`. Each quantifies over `Theme.builtin`: adding a bundle
is entering the contract.
-/

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir

/-- Arch-design I2, the engine half: what `\theme` installs is what the
bundle declares — the install function is `apply`, the very function the
elaborator calls at the `\theme` site, so a bundle's title-page alignment
and separator survive the install onto an undeclared document. The literal
through-`Elab.run` reading stays with the executable oracles: Elab's WF
recursion is kernel-irreducible, and this statement over the install
function is the same fact one definitional step earlier. -/
public theorem titlepage_align_declared_engine :
    (builtin.all fun t =>
      match (apply t {}).styles.find? "titlepage" with
      | some st => st.align.isSome && st.separator.isSome
      | none => true) = true := by decide

/-- Every shipped bundle declares each style element once, so
`apply_fixed_point` covers it. -/
public theorem builtin_styles_nodup :
    (builtin.all fun th => nodupKeys th.styles.entries.toList) = true := by decide

/-- Every name a shipped bundle declares reads as itself in an expression,
so `resolve_find_exact` covers each: `\textcolor{<name>}` and every reader of
the entry agree on it. -/
public theorem builtin_names_plain :
    (builtin.all fun th => th.palette.entries.toList.all fun e => plainName e.1.key) = true := by
  decide

/-- The depths a shipped bundle is realized at: a document's and a deck's. -/
@[expose] public def depths : List GroundDepth := [.documents, .decks]

/-- The schemes a bundle ships in: the printed page and the light screen (a
page declaring its colours ships one scheme, `HtmlDoc.dualScheme`). -/
@[expose] public def shipped : List Scheme := [.print, .light]

private theorem sites_documents_print :
    builtin.all (fun th => (Design.sites (th.realize .documents) .print).all Site.passes) = true := by
  decide +kernel

private theorem sites_documents_light :
    builtin.all (fun th => (Design.sites (th.realize .documents) .light).all Site.passes) = true := by
  decide +kernel

private theorem sites_decks_print :
    builtin.all (fun th => (Design.sites (th.realize .decks) .print).all Site.passes) = true := by
  decide +kernel

private theorem sites_decks_light :
    builtin.all (fun th => (Design.sites (th.realize .decks) .light).all Site.passes) = true := by
  decide +kernel

/-- **Every site a shipped bundle paints reads**: at a document's and a
deck's depth, on the printed page and the light screen, each pair the
bundle's realized palette ships — its generated grounds and inks, its
literal colours, the colour it derives from a lineage, and the defaults the
registry fills in — meets its need (`Site.passes`). The kernel reads the
realized palettes, whose generated and derived values are the literals
`PaletteData` keeps (held to a fresh derivation by `Tests.PaletteData`). -/
public theorem builtin_sites_contract :
    ∀ th ∈ builtin, ∀ d ∈ depths, ∀ s ∈ shipped, ∀ site ∈ Design.sites (th.realize d) s,
      site.passes = true := by
  intro th hth d hd s hs site hsite
  simp only [depths, shipped, List.mem_cons, List.not_mem_nil, or_false] at hd hs
  have pick : ∀ (h : builtin.all (fun th => (Design.sites (th.realize d) s).all Site.passes) = true),
      site.passes = true := fun h =>
    List.all_eq_true.mp (List.all_eq_true.mp h th hth) site hsite
  rcases hd with rfl | rfl <;> rcases hs with rfl | rfl
  · exact pick sites_documents_print
  · exact pick sites_documents_light
  · exact pick sites_decks_print
  · exact pick sites_decks_light

/-- moloch's lineage colour, `mLightBrown` (beamercolorthememoloch.sty). -/
@[expose] public def molochLineage : Color := Color.ofHtml 0xEB 0x81 0x1B

/-- A bundle that generates nothing realizes alike at every depth. -/
public theorem realize_seedless (th : Theme) (h : th.seeds = none) (d d' : GroundDepth) :
    th.realize d = th.realize d' := by
  simp only [Theme.realize, h]

/-- **moloch's progress bar and title separator are its lineage colour**,
exactly, as lualatex draws them, wherever the bundle is installed. -/
public theorem moloch_lineage_exact (d : GroundDepth) :
    Design.declared? (moloch.realize d) .progressFill = some molochLineage ∧
      Design.declared? (moloch.realize d) .separator = some molochLineage := by
  rw [realize_seedless moloch rfl d .decks]
  exact ⟨rfl, rfl⟩

/-- **Every shipped muted reads with a margin**: the secondary ink each
shipped bundle installs, and the one each class's defaults give an
undeclared document, at a document's and a deck's depth, on the printed
page and the light screen, stands at least 4.6:1 on its page — 0.10 over
the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text, the margin a generated ink is
held to. moloch's declared 70:30 mix of its ink into its page holds it at
4.79:1. -/
public theorem builtin_muted_margin :
    ((builtin.map (·.realize)) ++ ClassRow.all.map (fun row d =>
        ({ classColors := { row, depth := d } } : Palette))).all (fun pal =>
      depths.all fun d => shipped.all fun s =>
        match Design.at (pal d) s .muted, Design.at (pal d) s .page with
        | some m, some p => decide (4600 ≤ Contrast.contrastMilli m p)
        | _, _ => true) = true := by
  decide +kernel

end LeanTex.Core.Theme
