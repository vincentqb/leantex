# Title-page layout implementation — resumed run

- Date: 2026-09-30
- Mode: bug fix, nitrogen-implement-v2 AUTOPILOT
- Status: complete
- Branch: `agent/theme-title-layout`
- Starting HEAD: `82613240626aa271176193c2092b953f61d84b40`
- Base / merge-base with `main`: `2bb0d18142843a3e17829c1faae851482b1ed7c0`
- Rebase: already complete at resume; `main` remained an ancestor through delivery
- Task source: direct implementation request; no Taskei or Pippin project
- Build system: Lake with the repository-mandated Lean compiler environment

The prior completion record described the first pass. This resumed pass finished the general title-node geometry and optional-arm work, proved the new checks fail on the pre-fix tree, reran the independent external and private acceptance probes, and published only the feature branch. No private source, text, path, font, palette, or spacing value entered tracked files.

## Invariants and implementation

- One pinned title node is one box. Its anchor is computed from shipped glyph ink plus inner separation and pgf outer anchor clearance, not nominal face ascent/descent.
- A lower title part takes its declared TeX baseline skip; an explicit conditional gap remains separate glue.
- Beamer `size` and `size*` preserve both exact size and leading through one IR value into PDF and typed HTML.
- Empty optional metadata is identical to an absent arm in non-furniture `Layout.Out`, emits no separator, and keeps the same HTML pins.
- Only a final scoped arm that inserts exactly the tested datum with an optional absolute gap is normalized. Relative, unconditional, mismatched, ungrouped, literal, and trailing-content shapes retain the named fallback.

## RED → GREEN evidence

- A target-local archived copy of pre-fix `82613240` ran the current external placement report: all eight baseline comparisons failed; worst residual `6.55 pt`.
- Current code ran the same report: all eight passed; worst residual `0.05 pt` under the `0.25 pt` extractor bound.
- A target-local optional-shape guard passed after the fix and failed six adversarial forms against pre-fix `82613240`.
- The complete reference guard initially exposed five current-tree failures; after the parser and inherited-ink fixes, `lake test` passed.

## Validation

- [x] `lake build` — 141 jobs, passed
- [x] `lake test` — all passed
- [x] Focused title/layout/census runner — all passed
- [x] Title placement report and selftest — passed; worst `0.05 pt`
- [x] Private A/B — both variants produced one page in each engine; sampled grounds equal; baseline residuals at most `0.10 pt`
- [x] HTML browser oracle selftest — passed; refreshed 84 fixtures; two unchanged cross-image target cells remain report residuals
- [x] `htmlreader --check` — 4 items, 0 regressions
- [x] `htmla11y --check` — 504 items, 0 regressions
- [x] `external --check` — 216 items, 0 regressions
- [x] Scoreboard selftest and base-aware aggregate check — all 12 tiers passed
- [x] Owed selftest/check — passed
- [x] Compose fuzz — every swappable pair commuted over synthetic inputs and 85 corpus files
- [x] Whole-document benchmark — reference-list growth `4.1×` for `4×` entries, under `8.0×`
- [x] Fresh read-only review — APPROVED, no blocking findings

## Delivery

Feature commits from the verified base:

1. `c97bd25c9e2f30c7ec136d3d0022ea661df88843` — preserve compound node placement
2. `82613240626aa271176193c2092b953f61d84b40` — record first-pass implementation
3. `934faa6125f7d1272a1209bf10d28374ebf3191e` — match compound node placement

Published behavior update:

```text
To https://github.com/vincentqb/leantex
 + 22c954e7...934faa61 agent/theme-title-layout -> agent/theme-title-layout (forced update)
```

The durable exact handoff is `final-report.md` in this directory.
