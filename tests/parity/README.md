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
  artifact, the content key of *both* sources, the engine's version string,
  the argv, the page count, the overfull-box count, and the prose claim the
  fixture makes about its own pairing.

The pair is a human-reviewed correspondence, not a translation. Nothing
machine-checks that `<name>.tex` and `<name>.ref.tex` say the same thing —
what is checked is that neither has changed since the reference was
generated, because the sidecar pins both keys. Editing either source
without regenerating is a named failure, never a silent drift.

## The two tools

`scripts/parity-regen.lean` runs `lualatex`. It is the only thing in the
repository that does, and it is never part of `lake test`.

`scripts/parity.lean --check` reads the committed `.ref.pdf` and asks
nothing of this host. It computes each fixture's rung and holds it against
`tests/scoreboard/parity.tsv`, which records one integer per fixture. A rung
may rise — recorded — and may never fall.

## What a fixture declares

A `% parity:` line says what the pairing is for; the regenerator refuses a
fixture without one. A `% diverges: <name>` line names a registry entry in
`scripts/ParityCore.lean` (`Divergence`), and means: if this fixture stops
below the top, that is why. A declaration never changes a verdict — it is
checked in both directions. An unregistered name fails the gate, and a
fixture that declares a divergence while reaching the top fails too, because
a declaration nobody removed when the engine improved is a declaration that
would excuse the next regression.

## Probes that show no divergence (keep them: they are the regression floor)

- `prose.tex` — one page of justified prose at a declared geometry. Every
  rung the ladder has holds here, line for line, and the fixture exists so
  that a change which breaks them has somewhere to fail.
- `pagebreak.tex` — two pages, the break declared rather than computed.
  Isolates the page *count* rung from the page-*breaking* policy. Measured
  2026-09-25: it holds through reading order and stops at the line rung —
  page 2's first line takes one more word on the engine's side. That stop is
  a measurement, not a target; the number is recorded and must not fall.

## The probe that is outside the denominator

- `refuses.tex` — its reference half requires a package that does not exist,
  so `lualatex` stops under `-halt-on-error` and the sidecar records
  `compiles: no`. The scoreboard records `-1`, which means "not measured",
  never "measured and bad". It exercises T0's other arm: a ladder whose
  bottom rung is "both engines produced a document" needs a fixture where
  one did not. `compiles: no` is only ever written when the engine ran and
  refused — a machine with no TeX install regenerates nothing and cannot
  fabricate the verdict.

## Probes that show a divergence

- `measure.tex` — no geometry declared on either side, so each engine
  chooses its own measure. leantex sets an article's text block by a
  copy-fitting table (312 bp); LaTeX's 10 pt article on letter paper sets
  345 pt = 343.7 bp, 10.2 % wider, so the prose rebreaks. The delta is in
  the reference half's header beside the number, the fixture declares
  `default-measure`, and the scoreboard records the rung this reaches rather
  than the rung it "should".
