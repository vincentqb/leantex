module

public import LeanTex.Core.Contrast
import all LeanTex.Core.Contrast
import all LeanTex.Core.Theme
import all LeanTex.Core.Ir
import all LeanTex.Core.ContrastRatio
import all LeanTex.Core.Oklab
import all LeanTex.Core.Listing

/-!
Kernel-checked contrast contracts for the shipped design constants and
built-in themes. Kept downstream of the colour solver so consumers of its
API need not depend on these finite evaluations.
-/

namespace LeanTex.Core.Contrast

open LeanTex.Core.Ir LeanTex.Core.Dim

/-- No shipped light bundle regresses into an illegible pair. -/
public theorem light_contract : light.contractHolds = true := by decide +kernel

/-- The dark variant is held to the same contract, not assumed from the
light one. -/
public theorem dark_contract : dark.contractHolds = true := by decide +kernel

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

/-- Quantified over the shipped list itself, so a third bundle enters the
contract by being added, not by someone remembering a theorem: every
built-in bundle's resolved design — the values `\theme` installs, with
every default applied — satisfies the contrast contract. -/
public theorem builtin_designs_legible :
    Theme.builtin.all (fun th =>
      designContract (Design.ofDoc { palette := th.palette
                                     tokens := th.tokens
                                     styles := th.styles })) = true := by decide +kernel

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

/-- Every (role, ground) pair a shipped bundle's resolved design creates
realizes to itself: the pairs already meet their WCAG 2.2 requirement, so
realization is the identity on them (`realize_id_of_passing` is the
general statement; this is its kernel check over the shipped values, the
census half of the realization rule). Quantified over `Theme.builtin` and
over the design's own grounds — the page under the content colours and
`muted`, the frame-title bar under its ink, each titled bar under its
title, the standout ground under its ink — so adding a bundle is entering
the contract. The cross-ground pairs a document's own content creates
(a content colour inside a frame title or a standout frame) realize at
their use sites and are pinned executably in Tests.lean
(realizedCrossChecks): the search there is not the identity, and the
kernel does not evaluate it cheaply. -/
public theorem realized_builtin_contract :
    (Theme.builtin.all fun th =>
      let pal := th.palette
      let d := Design.ofDoc { palette := pal }
      let ok (req : Nat) (ground c : Color) : Bool := realize req ground c == some c
      ok aaText d.bg d.fg && ok aaText d.bg d.muted
        && (match pal.find? "alert" with | some c => ok aaText d.bg c | none => true)
        && (match pal.find? "example" with | some c => ok aaText d.bg c | none => true)
        && (match d.frametitle with | some p => ok aaText p.bg p.fg | none => true)
        && ok aaText (d.blockTitle.bar.getD d.bg) d.blockTitle.fg
        && ok aaText (d.alertTitle.bar.getD d.bg) d.alertTitle.fg
        && ok aaText (d.exampleTitle.bar.getD d.bg) d.exampleTitle.fg
        && ok aaLargeText d.standout.bg d.standout.fg) = true := by
  decide +kernel

end LeanTex.Core.Contrast
