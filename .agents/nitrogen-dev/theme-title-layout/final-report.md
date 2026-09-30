# Final handoff — title-page box and baseline parity

## Result

The title-page divergence is fixed on `agent/theme-title-layout`. Compound and split title-node shapes now agree with LuaLaTeX to a worst Ghostscript baseline residual of `0.05 pt`, versus `6.55 pt` before the resumed fix. Both authorized theme variants build one page in LuaLaTeX and leantex with equal sampled grounds. No private source, text, path, font, palette, or spacing value is tracked.

## Root cause and durable fix

The divergence was structural, not theme-specific:

1. A pinned title node was anchored from nominal face ascent/descent instead of the glyph box its lines shipped.
2. The node box included inner separation but omitted pgf's default `0.2 pt` outer anchor clearance.
3. Beamer `size*={size}{baseline skip}` retained `size` but dropped its second argument; named beamer sizes also lost their exact leading.
4. Consecutive differently sized title parts used cross-size half-leading rather than the lower paragraph's TeX baseline skip.
5. The optional-datum reader admitted conditionals without proving the full final scoped-arm shape, and treated unconditional or relative gaps as removable optional glue.

The fix makes `TitlePart` carry exact size and leading, resolves beamer's 11-point named sizes at the title-template boundary, gives both backends one `titlePartOf` lookup, anchors `Layout.B.placeSlot` from `segsInk`, includes inner plus outer separation in `slotShift`, and applies the lower part's leading only to that paragraph's first baseline. `slotShift_exact` and `placeLine_gap_exact` state the geometry. The optional reader now admits only a final scoped arm inserting exactly the tested datum with an optional absolute-unit gap; seven nearby shapes retain `W0363` fallback behavior.

## RED → GREEN

The pre-fix tree was copied from `82613240626aa271176193c2092b953f61d84b40` into ignored target-local scratch; no worktree or ref was changed. Running the current independent report against that binary failed all eight lines. The same report against the committed fix passed all eight.

| shape | line | before delta | after delta |
|---|---|---:|---:|
| compound | title | `-6.55 pt` | `0.00 pt` |
| compound | subtitle | `-4.75 pt` | `+0.05 pt` |
| compound | author | `-3.60 pt` | `-0.05 pt` |
| compound | institute | `-2.95 pt` | `0.00 pt` |
| split | title | `-5.70 pt` | `+0.05 pt` |
| split | subtitle | `-1.10 pt` | `0.00 pt` |
| split | author | `-2.95 pt` | `-0.05 pt` |
| split | institute | `-2.95 pt` | `-0.05 pt` |

The target-local full-shape guard passed on the fix and failed six adversarial forms on `82613240`. The tracked guard compares empty optional arms with absent arms over every non-furniture `Layout.Out` line/run, checks that no separator returns, checks title-page HTML pin identity, compares populated-arm ink with explicit-arm ink, and rejects mismatched, literal, ungrouped, trailing-content, relative-gap, and unconditional-gap forms.

## Independent report and bound

`scripts/title-placement-diff.lean` uses three independent artifact readers: Ghostscript `txtwrite` at 1440 dpi for baselines, Poppler `-bbox` for word boxes, and Poppler rasterization plus ImageMagick for page-ground samples. It builds only invented synthetic inputs and writes under the ignored build tree; it is a report, never a host-TeX `lake test` gate.

The gate bound is `0.25 PDF pt` (five 1440-dpi coordinate quanta). One quantum is `0.05 pt`; differencing two rounded Ghostscript coordinates contributes at most `0.05 pt`. The probe's largest baseline skip is 33 TeX pt, whose conversion to PDF points contributes `0.123 pt` against the engine's declared point unit. A `0.20 pt` threshold leaves less than one coordinate quantum beyond those independent effects; `0.25 pt` is the smallest grid threshold preserving one full quantum of extraction margin. The observed worst residual is `0.05 pt`.

Poppler word-box edges remain evidence rather than an identity gate because the two writers embed different font descriptors; exact Ghostscript baselines and ground samples are the placement oracle.

## Private A/B acceptance

All inputs and outputs stayed in ignored target-local scratch and used invented metadata. The compound variant residuals were `0.00`, `+0.05`, `-0.10`, and `-0.05 pt` for title, subtitle, author, and institute. The split variant rendered its two defined lines at `+0.05` and `0.00 pt`; its absent optional lines remained absent. LuaLaTeX and leantex each produced one page for both variants, and all sampled grounds agreed.

The command run from each ignored A/B variant directory was:

```sh
lualatex -halt-on-error -interaction=batchmode presentation.tex
lualatex -halt-on-error -interaction=batchmode presentation.tex
$REPO/.lake/build/bin/leantex presentation.tex -o leantex.pdf
gs -q -dNOPAUSE -dBATCH -r1440 -sDEVICE=txtwrite -dTextFormat=0 -sOutputFile=lualatex-ghost.xml presentation.pdf
gs -q -dNOPAUSE -dBATCH -r1440 -sDEVICE=txtwrite -dTextFormat=0 -sOutputFile=leantex-ghost.xml leantex.pdf
pdftoppm -f 1 -singlefile -png -r 72 presentation.pdf lualatex-page
pdftoppm -f 1 -singlefile -png -r 72 leantex.pdf leantex-page
```

## Validation commands and results

Every `lake` invocation used the required compiler environment:

```sh
env LEAN_CC=/home/linuxbrew/.linuxbrew/bin/clang \
  LIBRARY_PATH="$(lean --print-prefix)/lib:$(lean --print-prefix)/lib/lean" \
  <lake command>
```

| command | result |
|---|---|
| `lake build` | passed, 141 jobs |
| `lake test` | `tests: all passed` |
| `lake env lean --run .lake/title-census-targeted.lean` | focused title/layout/census checks all passed |
| `lake env lean --run scripts/title-placement-diff.lean --selftest` | all passed |
| `lake env lean --run scripts/title-placement-diff.lean` | 8/8 lines passed; worst `0.05 pt`; grounds exact |
| same report in archived pre-fix copy | 0/8 lines passed; worst `6.55 pt` |
| target-local optional guard on fix / pre-fix | all passed / six adversarial forms failed |
| `lake env lean --run scripts/html-oracle.lean --selftest` | passed |
| `lake env lean --run scripts/html-oracle.lean` | refreshed 84 fixtures; two unchanged cross-image target cells remain report residuals |
| `lake env lean --run scripts/htmlreader.lean --selftest` | passed |
| `lake env lean --run scripts/htmlreader.lean --check` | 4 items, 0 regressions, result `ok` |
| `lake env lean --run scripts/htmla11y.lean --selftest` | passed |
| `lake env lean --run scripts/htmla11y.lean --check` | 504 items, 0 regressions, result `ok` |
| `lake env lean --run scripts/external.lean --selftest` | passed |
| `lake env lean --run scripts/external.lean --check` | 216 items, 0 regressions, result `ok` |
| `lake build scoreboard` | passed |
| `lake exe scoreboard --selftest` | aggregate and all 12 tier selftests passed |
| `lake exe scoreboard --check --base 2bb0d18142843a3e17829c1faae851482b1ed7c0` | every tier and base check `ok` |
| `lake env lean --run scripts/owed.lean --selftest` | passed |
| `lake env lean --run scripts/owed.lean --check` | passed |
| `lake env lean --run scripts/compose-fuzz.lean` | every swappable pair commuted over synthetic inputs and 85 corpus files |
| `lake env lean --run scripts/bench.lean` | all runs passed; 1600/400-entry bibliography growth `4.1×` under `8.0×` |
| fresh read-only diff review | `APPROVED`, no blocking findings |

Benchmark medians were 92/370/570 ms for leantex paragraphs/lorem/underline, 87 ms for themed PDF and HTML, 185/163 ms for paper PDF/HTML, and 24/99 ms for 400/1600-entry bibliography phases. Performance evidence is from `scripts/bench.lean`, not code inspection.

## Commits, base, and delivery

The requested rebase was already complete at resume: starting HEAD `82613240626aa271176193c2092b953f61d84b40`, `main` and merge-base `2bb0d18142843a3e17829c1faae851482b1ed7c0`. `git merge-base --is-ancestor main HEAD` remained true; `main` was never changed.

Feature commits from that base:

1. `c97bd25c9e2f30c7ec136d3d0022ea661df88843` — `title: preserve compound node placement`
2. `82613240626aa271176193c2092b953f61d84b40` — `workflow: record title-layout implementation`
3. `934faa6125f7d1272a1209bf10d28374ebf3191e` — `title: match compound node placement`

Exact push:

```sh
git push --force-with-lease=refs/heads/agent/theme-title-layout:22c954e711233abbc3cfd5db11b76faede0631a2 origin agent/theme-title-layout
```

Output:

```text
To https://github.com/vincentqb/leantex
 + 22c954e7...934faa61 agent/theme-title-layout -> agent/theme-title-layout (forced update)
```

After this handoff record is committed and pushed, `git status --short` is empty, the checked-out branch is `agent/theme-title-layout`, and the remote feature tip equals local `HEAD`.

## Residuals and scope

- Browser report: `[feature] images/chromium` and `[fixture] figures/chromium` remain the same two cross-image failures; the gated HTML reader tier is current and green.
- Poppler box edges differ because of font descriptors; baseline placement and grounds pass independently.
- Non-layout compatibility notes from the private themes remain outside this fix.
- Recipe-book expansion, `\cancelto`, Big-O font selection, and `{%` whitespace semantics were not changed.
