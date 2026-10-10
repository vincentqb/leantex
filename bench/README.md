# Benchmarks

Run from the repository root after `lake build`:

```bash
lake env lean --run scripts/bench.lean
```

The harness regenerates `lorem.tex`, then reports median wall time over five
fresh process invocations. Set `N` to change the sample count. This is a
reference comparison, not semantic equivalence: lualatex loads a much larger
system and implements much more.

## Baseline — 2026-09-15

An x86_64 host; LuaHBTeX 1.24.0 (TeX Live 2026/Homebrew).

| Input | Size | leantex | lualatex | Ratio |
|---|---:|---:|---:|---:|
| `paragraphs.tex` | 1,043 B | 14 ms | 486 ms | 34.7× faster |
| generated `lorem.tex` | 129,507 B, 30 pages | 573 ms | 982 ms | 1.7× faster |

The large case is layout-bound; the `-v` phase trace attributes roughly 520 ms
to line breaking and page assembly. Keep this baseline when optimizing M6.

## Reference-list growth — 2026-09-28

The last rows time the `bib` phase (`-v`) over an invented `.bib` of 400 and
of 1600 entries, every one listed (`\nocite{*}` under plainnat, which sorts and
letters them), and fail the run when four times the entries cost more than
eight times the phase (linear is 4, quadratic 16). Before the phase was made
linear it measured 4,470 ms and 75,195 ms (16.8×); after, 24 ms and 97 ms
(4.0×), with every other row unchanged.

## Document cost

`lake env lean --run scripts/bench.lean --doc-cost` reports what the invented
reference documents of `scripts/DocBench.lean` cost to build: a 64-frame deck,
a 2,000-paragraph styled report, a 12-section paper with citations, 400
Markdown blocks through `\markdownInput`, and a 2,000-line Python listing. It
is `scripts/doccost.lean --bench`, which imports script modules `lake build`
does not build, so it builds them, and the engine, before it runs.
Every build is sealed — the corpus's fonts and images staged beside the
document, no tool on `PATH`, an empty `HOME` — and every face file it loads,
as the typed `faces` of its `font` phase name them, must be a staged one, so
each artifact is a function of the repository. Per
document and format the report prints cold and warm wall time (median of `N`,
default 3; cold is an empty application cache), edit-to-artifact latency (the
source renamed to its next revision under `--watch`, until the summary of the
build that answers it, the watcher's 200 ms poll included), the most memory
the engine held (`rssKiB` in the porcelain summary), bytes, and user-space
instructions where `perf` runs (median of `N`, with their spread); then each
family's growth from `n` to `4n` units, and from `4n` to `16n` for the deck,
the paper and the notes, with the headroom each pair leaves and the least
quadratic term that fails it; and the median of `N` builds' peak and
milliseconds for every corpus fixture.

Each reading is printed against the last run on the same host class (system,
architecture, logical cores) in `testdata/perf/documents.tsv`, and the
instruction counts are held to ±3% of it: three warm builds of one document
spread theirs by under 0.5% (the deck's PDF; the others under 0.2%), so a
move past the band is the engine's, not the host's. The counted builds are
sealed inside `perf` too, which puts `/usr/bin` back on the `PATH` it hands
the engine; each must load the very faces, out of as many scanned, as its
sealed priming build did. The warm deck is reported
against 400 ms (PDF) and 1.2 s (HTML), the report's PDF against 2.5 s. The
invented deck has no pictures and no figures, so its verdict is a floor: a
deck with them pays for them on top.

`--record` appends the run to the history (format: `scripts/PerfHistory.lean`;
union-merged, so two branches' runs both survive), and only from a clean
checkout of a commit `main` holds, measured by that tree's own up-to-date
build: `land` rebases a branch onto `main`, so a commit recorded on the branch
names a tree nobody can check out once it lands. Record from a branch made
from `main`, then land the rows. Each row also names the measured executable
by the first twelve hex digits of its SHA-256, which a commit alone cannot: a
saved or stale binary measures some other tree. `--history <path>` compares
with, and records into, a scratch history instead, for a before and after on a
branch. `scoreboard --bench` runs `lake build`, then the lualatex comparison,
then this report. Nothing here gates.

What gates is the `doccost` scoreboard tier, from sealed builds of every
family at `n` and `4n` units in both formats, and at `16n` for the deck, the
paper and the notes, whose `16n` builds are cheap:

- `rss-growth`: the least peak above the engine's fixed footprint (a run that
  reads no document) grows at most 8x for 4x the input. A peak made of phases
  that each grow linearly reads at most 4x however one hides another
  (`phasePeak_between`); a structure whose capacity doubles as it fills holds
  up to twice what it needs, so up to 8x (`growthWithin_doubled_covers`), and
  the bound fails neither. A healthy engine reads 0.9x to 1.9x. The price of
  that soundness is power. A term quadratic in the document's size fails an
  item exactly when its coefficient exceeds the item's headroom over `8n²`
  (`growthWithin_quadratic_exact`), which on this host runs from about 400 B
  per line squared (the listing's PDF) to about 6 MiB per section squared
  (the paper's HTML): terms that already add 380 MiB to 1.5 GiB at `4n`.
- `rss-growth-16n`: the same bound from `4n` to `16n`, which sees terms ten to
  eighteen times smaller: 2 to 3 KiB per frame squared on the deck's PDF,
  about 300 B per block squared on the notes' PDF. The report and the listing
  have no `16n` pair yet: their build time still grows faster than their
  input (3.8 s and 8.4 s at `16n`).

  `doccost --report` prints each item's headroom and least failing quadratic
  term; the tier file states the rule, not those figures, which move with the
  host and the run. `testdata/probes/u106/` holds two
  engine changes that show what the items see, with the commands that
  reproduce them: memory of 8 KiB per page squared fails the deck's two
  `16n` items (10.5x to 11.4x over three runs) and none of its `n` items
  (4.3x at most), while memory of 4 MiB per page, as heavy on the deck's
  `16n` document, fails nothing (3.7x at most).
- `size`: the size class of the `4n` gate document's artifact, in quarter
  octaves of KiB, held while the artifact stays within its committed class
  widened by an eighth of an octave each way, so a few bytes of drift at a
  boundary move nothing. A class heavier is a fall, which needs a
  `# lowered:` line saying why.

Milliseconds never gate: a peak is the process's own, a shared host's
milliseconds are anyone's.

### Document-cost baseline — 2026-10-09, before landing

Measured on the branch that introduced the report, over `main` as it then
stood, before it landed: a shared many-core x86_64 host (load
22–34); N=3. Later engine changes move these numbers; the record is the
history, `testdata/perf/documents.tsv`, whose runs are recorded from `main`.

| Document | Format | Cold | Warm | Edit | Peak | Bytes | Instructions |
|---|---|---:|---:|---:|---:|---:|---:|
| deck, 64 frames | PDF | 233 ms | 159 ms | 202 ms | 115.8 MiB | 166.0 KiB | 783 M |
| | HTML | 288 ms | 259 ms | 302 ms | 190.6 MiB | 1,543.2 KiB | 1,681 M |
| report, 2,000 paragraphs | PDF | 5,451 ms | 5,234 ms | 5,277 ms | 223.7 MiB | 666.3 KiB | 42,195 M |
| | HTML | 5,245 ms | 5,215 ms | 5,486 ms | 269.9 MiB | 2,183.6 KiB | 42,359 M |
| paper, 12 sections | PDF | 308 ms | 232 ms | 273 ms | 122.2 MiB | 180.6 KiB | 1,789 M |
| | HTML | 386 ms | 352 ms | 396 ms | 194.8 MiB | 1,760.1 KiB | 2,871 M |
| notes, 400 blocks | PDF | 521 ms | 404 ms | 474 ms | 123.7 MiB | 259.6 KiB | 2,949 M |
| | HTML | 566 ms | 520 ms | 581 ms | 206.4 MiB | 1,850.1 KiB | 3,925 M |
| listing, 2,000 lines | PDF | 2,392 ms | 2,320 ms | 2,360 ms | 114.8 MiB | 171.2 KiB | 12,108 M |
| | HTML | 2,504 ms | 2,485 ms | 2,532 ms | 188.2 MiB | 2,137.3 KiB | 13,724 M |

The warm deck is within its budgets (159 of 400 ms as PDF, 259 of 1,200 ms
as HTML), which is a floor, not a verdict on a deck with pictures or figures.
The report's PDF is not: 5,234 of 2,500 ms, with layout at 8.7 ms a page.
Peaks grow 0.9x to 1.9x per fourfold step above a 69.2 MiB footprint;
milliseconds grow up to 2.9x (the report's PDF) and 4.6x (the listing's PDF)
from `n` to `4n`, and 4.5x (the notes' PDF) from `4n` to `16n`. Corpus
fixtures peak at a median of 93.1 MiB as PDF (highest 107.2 MiB) and
206.4 MiB as HTML, where the five heaviest, which declare no fonts and so
embed the host's, peak near 500 MiB.
