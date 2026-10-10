module

public import LeanTex.Core.Contrast
import all LeanTex.Core.Contrast
import all LeanTex.Core.Theme
import LeanTex.Core.Ir
import all LeanTex.Core.ContrastRatio
import all LeanTex.Core.Oklab
import all LeanTex.Core.Listing
import all LeanTex.Core.DesignRole

/-!
Kernel-checked contrast contracts for the shipped design constants and
built-in themes. Kept downstream of the colour solver so consumers of its
API need not depend on these finite evaluations.
-/

namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- The PDF default — black ink on the unpainted (white) page — clears the
AA text threshold; 21:1 is the definition's own maximum. (Named `_aa`,
not `_text`: `_text` is the registered census-conservation suffix, and a
registry is only a registry if a suffix has one meaning.) -/
public theorem pdf_default_aa : contrastMilli Color.black Color.white ≥ aaText := by
  decide +kernel

-- The theorems range over the bundles the engine installs: `Theme.builtin`
-- carries each palette as values (mixes evaluated at definition time), so
-- the kernel walks the same entries `\theme` declares — no transcription
-- stands between the statement and the engine. Each contract quantifies
-- over the shipped list itself, so a third bundle enters every contract by
-- being added, not by someone remembering three theorems; only the default
-- surface (`{}` is not in `builtin`) keeps its own statements.

/-- No shipped bundle's pairing is illegible: every built-in palette — the
content colours (`alert`, `example`) and the resolved design's semantic
pairings, defaults applied — clears its WCAG 2.2 threshold. Moloch's alert
is the corrected one: the lineage's own #EB811B read at 2.61:1 on this
page, under SC 1.4.3. -/
public theorem builtin_palettes_contract :
    Theme.builtin.all (fun th => paletteContract th.palette) = true := by decide +kernel

/-- **Every shipped bundle is legible on screen too**: each pair its design
ships in the stylesheet's light column — the column a page declaring
colours ships, since such a page ships one scheme (`HtmlDoc.dualScheme`) —
meets its need, the screen's own code panel and focus ring included. -/
public theorem builtin_palettes_light_contract :
    Theme.builtin.all (fun th => (Design.sites th.palette .light).all Site.passes) = true := by
  decide +kernel

/-- The default surface: black ink, white page, covered at
`coveredFractionDefault` — 38% of the ink over the page, mixed in Oklab
(the Material disabled-state opacity, applied as the opacity it is). `{}`
is not in `Theme.builtin`, so the default keeps its own statement. -/
public theorem default_covered : coveredContract {} = true := by decide +kernel

public theorem default_cover_monotone : coverMonotone {} = true := by decide +kernel

/-- Cover monotonicity, quantified over the shipped list: covering twice
quiets further for every built-in bundle's text roles. -/
public theorem builtin_covers_monotone :
    Theme.builtin.all (fun th => coverMonotone th.palette) = true := by decide +kernel

/-- The covered contract, quantified the same way: every built-in
bundle's palette is visibly covered when dimmed, per colour. -/
public theorem builtin_designs_covered :
    Theme.builtin.all (fun th => coveredContract th.palette) = true := by decide +kernel

/-- Both contracts over what `\theme` installs, for every shipped bundle
(arch-provable I2): stated over `Theme.apply t {}` — the exact function
`Elab` runs at the `\theme` site (values in, values out), on a document
that has declared nothing — never a transcription of the install. The
remaining link, that `\theme` reaches this install through `Elab.run`,
is the per-bundle "`\theme` installs the bundle's own values" pin in
`Tests.lean`: `Elab.run`'s tracked non-total functions keep the
elaborator itself outside the kernel's reach. -/
public theorem builtin_palette_contract_engine :
    (Theme.builtin.all fun t =>
      paletteContract (Theme.apply t {}).palette &&
      coveredContract (Theme.apply t {}).palette) = true := by
  decide +kernel

/-- The registry's own defaults are legible in every scheme: each site an
undeclared design ships — body, muted and marker text on the page, code on
its surface, the focus ring, the frame and block titles, the standout
inversion — meets its need in print and in both screen columns, which are
the stylesheet's own colours. -/
public theorem default_sites_contract :
    (Scheme.all.all fun s => (Design.sites {} s).all Site.passes) = true := by decide +kernel

end LeanTex.Core.Contrast
