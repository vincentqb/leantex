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

## Reference-list fields and field citations — 2026-10-10

Rows over field text the document's own elaborator reads — TeX fields
(accented names, a formula and a dash in each title) and TeX-heavy fields
(an `\emph`, a formula, an accent, a `\url`, a `\textit` and an `\&` in every
entry) — and a chain of field citations, each entry's `note` citing the
next, at 100 and 400 links. Median of 5 per row, two interleaved rounds,
before and after the field reading's context was built once per document,
the compatibility pass skipped for fields it leaves as they stand, the
database prepared once for every round, the chain followed entry by entry,
and a collation tailoring decoded only for the locale that sorts by it:

| row | 400 entries | 1600 entries |
|---|---|---|
| plainnat, TeX fields | 146, 143 → 53, 55 ms | 556, 569 → 212, 216 ms |
| plainnat, TeX-heavy fields | 144, 147 → 52, 53 ms | 579, 603 → 205, 209 ms |
| biblatex numeric | 173, 182 → 75, 78 ms | 680, 725 → 297, 292 ms |
| biblatex authoryear | 171, 195 → 74, 74 ms | 670, 758 → 299, 298 ms |
| biblatex authoryear, TeX-heavy fields | 163, 175 → 70, 67 ms | 635, 654 → 268, 262 ms |

The chain took 924 and 934 ms at 100 links and 14,521 and 14,854 ms at 400
(15.7×, past the bound); after, 20 and 21 ms and 84 and 82 ms (4.2×). The
artifacts are byte-identical before and after, on the corpus and on the
rows' own documents.

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

## SVG figures — 2026-10-09

`--svg-only` builds documents of 5 and 17 invented SVG figures (recoloured
copies of the corpus chart, which sets text, and one moving figure) to PDF
and to HTML, each cold (an empty private content cache) and warm (a primed
one), and reports the `images` phase beside the wall time. Before: every
figure went through xmllint, xsltproc and rsvg-convert, and a figure that
sets text is font-dependent, so its conversion is never cached and the warm
run repeats it; the HTML additionally validated every embedded SVG through
the same tools. After: the engine reads and draws them itself, and no tool
runs. Median of 5, shared host (load 30–58), so the absolute numbers are
provisional; the ratio is the claim.

| Build | before | after |
|---|---:|---:|
| 5 figures, PDF, warm | 1,288 ms (images 1,162) | 157 ms (images 29) |
| 5 figures, HTML, warm | 3,599 ms (images 1,132) | 487 ms (images 28) |
| 17 figures, PDF, warm | 4,554 ms (images 4,430) | 199 ms (images 60) |
| 17 figures, HTML, warm | 14,047 ms (images 5,083) | 530 ms (images 60) |

The default rows moved within the host's noise.

## Talk deck — 2026-10-16

`--talk-only` builds the invented deck `scripts/talkdeck.lean` writes: 60 frames with 43 minted
listings (Lean, Python, shell), overlays (item specs, `\pause`, `\uncover`, `\only`,
`\alert<n>`), blocks, tables, footnotes, a 4096×4096 RGBA PNG shown three times, an SVG chart
and two vector PDF charts. Its generator is compiled (`lake build talkDeck`), so its raster and
streams deflate at the engine's speed. Each build has no tool on `PATH`, an empty `HOME` and the
corpus fonts staged beside the deck (font discovery still reads the host's system font
directories), and must ship no loss; the report gives the median of `N` pairs of a cold build
(an empty application cache) and a warm one, in each format, with every phase, and fails when a
warm or a later cold build changes the artifact. When `LEANTEX_BENCH_COMPARE_BINARY` names another
compiler, a pair of its builds follows each pair, must reproduce the artifact and diagnostics, and
is reported beside, so load drift falls on both.

The web page's writer escaped every text node and attribute value through a list of characters and
encoded each data URL once per use, and once more for its closure check. It now returns a value
holding nothing to escape as it stands, writes attributes straight into the page, builds each
captured resource once per page so its URL is computed once, and keeps the encoder's ASCII output
valid UTF-8 as it grows rather than validating it after. Median of 5, shared host (load 48-78);
the html phase includes the faces phase:

| Build | before | after |
|---|---:|---:|
| HTML, warm | 2,855 ms (html 2,051) | 1,115 ms (html 392) |
| HTML, cold | 7,341 ms (html 3,225) | 5,342 ms (html 1,528) |
| PDF, warm | 819 ms | 836 ms |
| PDF, cold | 3,976 ms | 4,078 ms |

The artifacts are byte-identical before and after.

The images phase then dominated both builds: a 4096×4096 RGBA PNG inflated through a reader that
allocated a reader state, a pair and an option for every bit, split into its colour and alpha
planes with divisions for every byte, and every warm build inflated the vector charts' content
streams again to probe them. Bits and Huffman codes are now read by tail-recursive loops over a bit
position, a match of six bytes or more that ends before its destination is copied as one slice,
and the planes are cut row by row. Median of 5, back to back on a host at load 68-79: the
before column with `LEANTEX_BENCH_BINARY` naming the parent's saved compiler, the after column
with `LEANTEX_BENCH_COMPARE_BINARY` naming it for the byte comparison:

| Build | before | after |
|---|---:|---:|
| PDF, cold | 4,246 ms (images 3,458) | 1,804 ms (images 1,204) |
| PDF, warm | 818 ms (images 490) | 499 ms (images 154) |
| HTML, cold | 5,143 ms (images 3,414, faces 1,105) | 2,611 ms (images 1,218, faces 776) |
| HTML, warm | 1,040 ms (images 491) | 720 ms (images 153) |

The comparison found the artifacts and diagnostics byte-identical; `scripts/flate-fuzz.lean` still
reads and refuses exactly what zlib does, and `scripts/img-fuzz.lean` passes.

## Web pages — 2026-10-17

`--pages-only` builds three small web pages, `testdata/corpus/md-emphasis.md`, `md-code.md` and
`themed.tex`, the median of `N` builds each, then a page whose declared stylesheet holds 8,000 and
32,000 rules of characters outside ASCII, and bounds its html phase's growth.

A page's style and script payloads were searched for their closing tag through a list of the
payload's characters, lowered, and the stylesheet's and scripts' own checks lowered and split the
whole text, a copy of it for each character outside ASCII; on a small page the sheet is mostly the
embedded fonts' data URLs. All now search the UTF-8 bytes (`Html.holdsTerm`, which
`holdsTerm_exact` proves finds exactly what the character search finds). Median of 9, the median
of three alternating rounds at load 112-134, the before column with `LEANTEX_BENCH_BINARY` naming
the parent's compiler:

| Page | before | after |
|---|---:|---:|
| md-emphasis.md | 1,026 ms | 509 ms |
| md-code.md | 868 ms | 456 ms |
| themed.tex | 304 ms | 220 ms |
| 8,000 stylesheet rules, html phase | 1,374 ms | 276 ms |
| 32,000 stylesheet rules, html phase | 10,100 ms | 332 ms |

The stylesheet rows are the median of 3 in two rounds; the phase grew 7.4 times for four times
the rules before, 1.2 times after. Every corpus document's PDF and HTML is byte-identical before
and after.

## Raster deck — 2026-10-17

`--rasters-only` builds the deck `scripts/talkdeck.lean` writes when given a raster count: 8
frames, each showing its own invented 2048×2048 RGBA PNG (the talk deck's panels grained from
seeds 731 to 738, the first the talk deck's own), sealed as the talk deck is; then the flat raster
deck, the same frames over photograph-like RGB PNGs of about 11.6 MB each, which planning passes
through. The report gives each format's median peak resident memory beside its times.

Images were fetched one at a time, and a raster's colour and alpha planes were deflated one after
the other. Every source is now found and read in request order, then planned four at a time,
never two files of one size at once, so two of one content never plan at once and each plan
cache slot has one writer, and the alpha plane deflates beside the colour plane. Median of 5 per
round, the median of three rounds on a host at load 70-150, `LEANTEX_BENCH_COMPARE_BINARY` naming
the parent's saved compiler so the two compilers' builds alternate:

| Build | before | after |
|---|---:|---:|
| Raster deck PDF, cold | 2,410 ms (images 2,277), peak 174 MiB | 712 ms (images 568), peak 325 MiB |
| Raster deck PDF, warm | 125 ms (images 25) | 109 ms (images 11) |
| Raster deck HTML, cold | 2,951 ms (images 2,496), peak 217 MiB | 1,046 ms (images 670), peak 329 MiB |
| Raster deck HTML, warm | 342 ms (images 29) | 355 ms (images 13) |
| Talk deck PDF, cold | 2,059 ms (images 1,344), peak 255 MiB | 1,960 ms (images 1,200), peak 281 MiB |
| Talk deck PDF, warm | 576 ms (images 181) | 462 ms (images 95) |
| Talk deck HTML, cold | 3,103 ms (images 1,386), peak 270 MiB | 2,775 ms (images 1,158), peak 296 MiB |
| Talk deck HTML, warm | 803 ms (images 172) | 737 ms (images 105) |

The cold builds trade memory for time, four rasters decoding at once: the raster deck's cold PDF
build peaks 151 MiB higher. The flat raster deck has nothing to plan in parallel: its images phase
stays near 50 ms, about 5 ms slower over ten alternating cold builds of each format, and its
builds move within the host's noise, the html phase about 1.9 s of a 125 MB page either way. The comparisons found the artifacts and diagnostics byte-identical.
