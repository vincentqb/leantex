# The parity corpus: one integer per document, against a reference engine

Each fixture here is a *pair* of sources that declare the same document in
two vocabularies:

- `<name>.tex` — the leantex source. This is what the engine compiles.
- `<name>.ref.tex` — the same document in LaTeX's own vocabulary, compiled
  by `lualatex`. Geometry, body size, leading and paragraph gap are
  **declared on both sides** rather than left to either engine's defaults,
  because the defaults are one of the things that differ (see
  `measure.tex`, whose whole subject is that difference).
- `<name>.ref.pdf` — the committed reference artifact, byte-immutable once
  committed.
- `<name>.ref.txt` — its provenance sidecar: the content key of the
  artifact, the content key of *both* sources and of the source's body
  without its comments, the content key of every in-repo file the reference
  read, the engine's version string, the LaTeX format line, the argv, the
  page count, the overfull-box count, and the prose claim the fixture makes
  about its own pairing.

The pair is a human-reviewed correspondence, not a translation. Nothing
machine-checks that `<name>.tex` and `<name>.ref.tex` say the same thing —
what is checked is that neither has changed since the reference was
generated, because the sidecar pins both keys. Editing either source
without regenerating is a named failure, never a silent drift.

## The levels

Cumulative: a fixture's recorded level is the number of levels that hold
from the bottom, and `-1` means the reference engine refuses the document,
which puts the fixture outside the denominator.

| level | holds when |
|---|---|
| L0 build | `lualatex` compiles the reference under `-halt-on-error`, and the engine builds its half with no error diagnostic |
| L1 pages | the same page count |
| L2 census | per page, the same multiset of inked Unicode scalars |
| L3 order | per page, the same scalar sequence in reading order (lines top to bottom, each line left to right) |
| L4 lines | per page, the same partition into lines |
| L5 place | *not built.* Every glyph origin within 0.5 bp by one-to-one same-character matching. Measured 2026-09-25 on `prose`, whose lines agree exactly: |Δx| p50 0.29 bp, p95 1.58 bp, max 2.34 bp; |Δy| is a uniform 0.725 bp page offset (`first-baseline`) and 0 at p50 and p95 once that is removed. So the two engines distribute justification differently, which is a real difference and not a tolerance question — the level waits for an arm that says so, rather than for a number wide enough to pass |
| R raster | reported, never gated. Not built |

`L0`–`L2` are flashtex's `L0`–`L2` against pdflatex; `L3` and `L4` have no
flashtex analogue and exist because `pagebreak` passes census and order and
differs in lines; flashtex's `L3` is `L5` here and its `L4` is `R`.

Whitespace is dropped before every comparison, on both sides: the engine
separates words by positioning the next run and the reference sometimes by a
space glyph, and which a writer chose is not a difference in what the page
shows. So `L2`–`L4` cannot see a missing interword space — that belongs to
`L5`, which has the gap geometry.

## The two tools

`scripts/parity-regen.lean` runs `lualatex`. It is the only thing in the
repository that does, and it is never part of `lake test`. The reference it
writes is a function of its inputs and not of where it was built: the
trailer `/ID` is derived from the reference source's content key rather than
from LuaTeX's default MD5 of the timestamp, the working directory and the
output name. `--selftest` rebuilds one fixture in two directories at
different depths and compares the bytes, so that claim is measured and not
asserted.

`parity --check` reads the committed `.ref.pdf` and asks nothing of this
host. It computes each fixture's level and holds it against
`tests/scoreboard/parity.tsv`, which records one integer per fixture. A
level may rise — recorded, with `--record` — and may never fall, unless a
human wrote a `# lowered: <fixture> <old>→<new> — <why>` line that accepts
that one fall. `--record` refuses to write over a fall nobody accepted, over
a stale pairing, or over a fixture that vanished without a `# retired:`
line.

`parity --repin` is the hermetic half of regeneration: when only comment
lines of `<name>.tex` moved — a `% diverges:` declaration corrected, a
header reworded — it updates that one pin, leaving the reference untouched.
It refuses as soon as anything the reference depends on has moved. This
exists because the gate's own advice about its own annotations must be
followable on a host with no TeX install.

## What a fixture declares

A `% parity:` line says what the pairing is for; the regenerator refuses a
fixture without one. A `% diverges: <name>` line names a registry entry in
`scripts/ParityCore.lean` (`Divergence`), and means: if this fixture stops
below the top, that is why. A declaration never changes a verdict — it is
checked in both directions. An unregistered name fails the gate; a
declaration that does not account for the level the fixture stopped on fails
too, because it would sit in the file excusing whatever regression came
next; and a fixture that declares a divergence while reaching the top fails,
because a declaration nobody removed when the engine improved is a
declaration that would excuse the next regression. A fixture that declares
nothing is judged on its measurement alone.

## Probes that show no divergence (keep them: they are the regression floor)

- `prose.tex` — one page of justified prose at a declared geometry. Every
  level the ladder has holds here, line for line, and the fixture exists so
  that a change which breaks them has somewhere to fail.
- `pagebreak.tex` — two pages, the break declared rather than computed.
  Isolates the page *count* level from the page-*breaking* policy. Measured
  2026-09-25: it holds through reading order and stops at the line level —
  page 2's first line takes one more word on the engine's side. That stop is
  a measurement, not a target; the number is recorded and must not fall.

## The probe that is outside the denominator

- `refuses.tex` — its reference half requires a package that does not exist,
  so `lualatex` stops under `-halt-on-error` and the sidecar records
  `compiles: no`. The scoreboard records `-1`, which means "not measured",
  never "measured and bad". It exercises L0's other arm: a ladder whose
  bottom level is "both engines produced a document" needs a fixture where
  one did not. `compiles: no` is only ever written when the engine ran,
  refused, and left a log with a `!` error line — a machine with no TeX
  install regenerates nothing, and a kill or a failed spawn aborts the
  regeneration rather than being committed as a refusal.

## Probes that show a divergence

- `measure.tex` — no geometry declared on either side, so each engine
  chooses its own measure. leantex sets an article's text block by a
  copy-fitting table (312 bp); LaTeX's 10 pt article on letter paper sets
  345 pt = 343.7 bp, 10.2 % wider, so the prose rebreaks. The delta is in
  the reference half's header beside the number, the fixture declares
  `default-measure`, and the scoreboard records the level this reaches
  rather than the level it "should".
