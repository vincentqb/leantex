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

/-- Where the contracts judge a shipped bundle installed: on a deck's stage
at a deck's depth, and on a document's LaTeX page at a document's depth, each
row's defaults filling in what the bundle leaves (`Ir.ClassColors`). A web
page's and a card's rows are installs `\theme` reaches too, not judged here:
pending the resolver table that would make each install cheap to judge. -/
@[expose] public def installs : List ClassColors :=
  [{ row := .stage, depth := .decks }, { row := .latex, depth := .documents }]

/-- A shipped bundle's palette where a class installs it. -/
@[expose] public def installedAt (th : Theme) (c : ClassColors) : Palette :=
  { th.realize c.depth with classColors := c }

/-- The schemes a bundle ships in: the printed page and the light screen (a
page declaring its colours ships one scheme, `HtmlDoc.dualScheme`). -/
@[expose] public def shipped : List Scheme := [.print, .light]

/-- Every site a shipped bundle paints where one class installs it, in each
scheme it ships in: one evaluation per install, so the kernel resolves each
installed palette once for both schemes. -/
private theorem sites_at (c : ClassColors) (h : builtin.all (fun th => shipped.all fun s =>
      (Design.sites (installedAt th c) s).all Site.passes) = true) :
    ∀ th ∈ builtin, ∀ s ∈ shipped, ∀ site ∈ Design.sites (installedAt th c) s, site.passes = true :=
  fun th hth s hs site hsite =>
    List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h th hth) s hs) site hsite

private theorem sites_stage : builtin.all (fun th => shipped.all fun s =>
    (Design.sites (installedAt th { row := .stage, depth := .decks }) s).all Site.passes) = true := by
  decide +kernel

private theorem sites_latex : builtin.all (fun th => shipped.all fun s =>
    (Design.sites (installedAt th { row := .latex, depth := .documents }) s).all Site.passes) = true := by
  decide +kernel

/-- **Every site a shipped bundle paints reads**: on a deck's stage and a
document's page, on the printed page and the light screen, each pair the
bundle's realized palette ships there — its generated grounds and inks, its
literal colours, the colour it derives from a lineage, and the defaults the
class's row fills in — meets its need (`Site.passes`). The kernel reads the
realized palettes, whose generated and derived values are the literals
`PaletteData` keeps (held to a fresh derivation by `Tests.PaletteData`); the
two installs cost about 30 s of kernel time, pending a resolver that hands
the kernel its strata as a table. -/
public theorem builtin_sites_contract :
    ∀ th ∈ builtin, ∀ c ∈ installs, ∀ s ∈ shipped, ∀ site ∈ Design.sites (installedAt th c) s,
      site.passes = true := by
  intro th hth c hc
  simp only [installs, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact sites_at _ sites_stage th hth
  · exact sites_at _ sites_latex th hth

/-- moloch's lineage colour, `mLightBrown` (beamercolorthememoloch.sty). -/
@[expose] public def molochLineage : Color := Color.ofHtml 0xEB 0x81 0x1B

/-- **moloch's progress bar and title separator are its lineage colour**,
exactly, as lualatex draws them, wherever the bundle is installed. -/
public theorem moloch_lineage_exact (d : GroundDepth) :
    Design.declared? (moloch.realize d) .progressFill = some molochLineage ∧
      Design.declared? (moloch.realize d) .separator = some molochLineage := by
  rw [realize_depth_exact moloch rfl d .decks]
  exact ⟨rfl, rfl⟩

/-- **Every shipped muted reads with a margin**: the secondary ink each
shipped bundle installs where a class installs it, on the printed page and
the light screen, and the one each class's row gives an undeclared document
at its depth, on the dark screen too, stands at least 4.6:1 on its page —
0.10 over the 4.5:1 WCAG 2.2 SC 1.4.3 asks of text, the margin a generated
ink is held to. moloch's declared 70:30 mix of its ink into its page holds
it at 4.79:1. -/
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
