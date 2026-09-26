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
without regenerating is a named failure, never a silent drift. Both halves
are checked out byte for byte (`.gitattributes` marks them `-text`), since a
line-ending conversion would move every key.

## The levels

Cumulative: a fixture's recorded level is the number of levels that hold
from the bottom, and `-1` means the reference engine refuses the document,
which puts the fixture outside the denominator.

| level | holds when |
|---|---|
| P0 build | `lualatex` compiles the reference under `-halt-on-error`, and the engine builds its half with no error diagnostic |
| P1 pages | the same page count |
| P2 census | per page, the same multiset of inked Unicode scalars |
| P3 order | per page, the same scalar sequence in reading order (lines top to bottom, each line left to right) |
| P4 lines | per page, the same partition into lines |
| P5 placement | *not built.* Every glyph origin within a declared tolerance by one-to-one same-character matching. Measured 2026-09-25 on `prose`, whose lines agree exactly: \|Δx\| p50 0.29 bp, p95 1.32 bp, max 1.88 bp with micro-typography declared off; \|Δy\| is a uniform 0.725 bp page offset (`first-baseline`). The re-review decomposed the \|Δx\| into three separable causes: micro-typography the pairing had not declared (now declared off here, and undeclared in `pagebreak`), LaTeX's sentence spacing (measured 2026-09-26 with `prose`'s reference declaring `\frenchspacing` too: p95 0.418 bp, max 0.493 bp; which half gives way is a human's decision), and the engine writing truncated widths. The level waits for all three, not for a tolerance wide enough to pass |
| R raster | reported, never gated. Not built |

`P0`–`P2` are flashtex's `L0`–`L2` against pdflatex; `P3` and `P4` have no
flashtex analogue and exist because `pagebreak` passes census and order and
differs in lines; flashtex's `L3` is `P5` here and its `L4` is `R`.

Whitespace is dropped before every comparison, on both sides: the engine
separates words by positioning the next run and the reference sometimes by a
space glyph, and which a writer chose is not a difference in what the page
shows. So `P2`–`P4` cannot see a missing interword space — that belongs to
`P5`, which has the gap geometry.

## The two tools

`scripts/parity-regen.lean` runs `lualatex`. It is the only thing in the
repository that does, and it is never part of `lake test`. The engine reads
each reference source where it stands and writes its outputs into a scratch
directory; a result is copied into this directory only once it is a
verdict. The reference is a function of its inputs and not of where it was
built: the trailer `/ID` is derived from the reference source's content key
rather than from LuaTeX's default MD5 of the timestamp, the working
directory and the output name. `--selftest` rebuilds one fixture in two
directories at different depths and compares the bytes with each other and,
on a host matching the sidecar's engine and format, with the committed
reference.

`parity --check` reads the committed `.ref.pdf` and asks nothing of this
host. It computes each fixture's level and holds it against
`tests/scoreboard/parity.tsv` under the ratchet every scoreboard tier
shares: a fall fails, a rise fails until it is recorded, and a bare
`parity` (the regenerate mode) refuses to write a fall no human-written
`# lowered: <fixture> <old>→<new> — <why>` line authorises. Before the
ratchet sees anything, a stale pairing, an unreadable reference or a
declaration that does not account for its fixture's stop stops the run
with nothing written.

`parity --repin` is the hermetic half of regeneration: when only comment
lines of `<name>.tex` moved — a `% diverges:` declaration corrected, a
header reworded — it updates that one pin, leaving the reference untouched.
It refuses as soon as anything the reference depends on has moved, and it
never clears an edit to a source the engine's lexer reads any part of raw
(a verbatim body is text, not comments). This exists because the gate's own
advice about its own annotations must be followable on a host with no TeX
install.

## What a fixture declares

A `% parity:` line says what the pairing is for; the regenerator refuses a
fixture without one. A `% diverges: <name>` line names a registry entry in
`scripts/ParityCore.lean` (`Divergence`), and means: if this fixture stops
below the top, that is why. A declaration never changes a verdict — it is
checked in both directions. An unregistered name fails the gate; a
declaration that does not excuse the level the fixture stopped on fails
too, because it would sit in the file excusing whatever regression came
next; and a fixture that declares a divergence while reaching the top fails,
because a declaration nobody removed when the engine improved is a
declaration that would excuse the next regression. A fixture that declares
nothing is judged on its measurement alone.

## Probes that show no divergence (keep them: they are the regression floor)

- `prose.tex` — one page of justified prose at a declared geometry, with
  micro-typography declared off on the engine's side because the reference
  loads no microtype. Every level the ladder has holds here, line for line,
  and the fixture exists so that a change which breaks them has somewhere
  to fail.

## The probe whose pairing is not yet declared alike

- `pagebreak.tex` — two pages, the break declared rather than computed.
  Isolates the page *count* level from the page-*breaking* policy. Its
  pairing differs in two ways neither half declares. The engine keeps its
  default micro-typography (protrusion and expansion), and the reference
  loads no microtype. The reference keeps LaTeX's default sentence spacing
  (`\nonfrenchspacing`, a wider space after a sentence's full stop), and
  the engine spaces every interword gap alike. As committed it stops at
  P4: page 2's first line takes one more word on the engine's side.
  Measured 2026-09-26, one variable per arm, through
  `parity-regen --force` and `parity --check`:

  | engine micro-typography | reference sentence spacing | level |
  |---|---|---|
  | on (committed) | default (committed) | 4 |
  | off | default | 2: the engine inks "be-" |
  | on | `\frenchspacing` | 2: the reference inks "be-" |
  | off | `\frenchspacing` | 5, the top |

  With both declared alike, both engines set "be-/lieved" and every level
  holds. There are two ways to get there: the engine implements LaTeX's
  space factor, or both halves declare the same micro-typography and
  sentence spacing and a registry divergence records it. Choosing between
  them is a human's decision, and until it is made the pairing stays as
  committed.

## The probe that is outside the denominator

- `refuses.tex` — its reference half requires a package that does not exist,
  so `lualatex` stops under `-halt-on-error` and the sidecar records
  `compiles: no`. The scoreboard records `-1`, which means "not measured",
  never "measured and bad". It exercises P0's other arm: a ladder whose
  bottom level is "both engines produced a document" needs a fixture where
  one did not. `compiles: no` is only ever written when the engine ran,
  refused, and left one of TeX's own error lines in its log — the classic
  `! <message>` or `-file-line-error`'s `<file>:<line>: <message>`. A
  machine with no TeX install regenerates nothing, and a kill or a failed
  spawn aborts the regeneration rather than being committed as a refusal.

## Probes that show a divergence

- `measure.tex` — no geometry declared on either side, so each engine
  chooses its own measure. leantex sets an article's text block by a
  copy-fitting table (312 bp); LaTeX's 10 pt article on letter paper sets
  345 pt = 343.7 bp, 10.2 % wider, so the prose rebreaks. It stops at P2:
  the engine hyphenates a word at the end of its first line and the
  reference, breaking elsewhere, inks no hyphen. The delta is in the
  reference half's header beside the number, the fixture declares
  `default-measure`, and the scoreboard records the level this reaches
  rather than the level it "should".
