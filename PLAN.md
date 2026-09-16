# leantex — plan

Fast, certified, modern LaTeX-lookalike engine in Lean 4.

Not a TeX reimplementation: a clean language that reads and writes like LaTeX,
with specified semantics and modern defaults, judged on producing very good
documents. lualatex is the current go-to and the thing to beat, not to match.
flashtex sets the speed bar.

## Status

2026-09-15 — M2a landed: leantex produces PDFs. Knuth–Plass line breaking
(DP verified optimal against brute-force enumeration on small cases), sp
fixed-point dimensions with first proofs, sfnt font parsing (TrueType + CFF,
cmap 4/12, metrics), justified paragraph typesetting with fil glue and forced
breaks, page assembly, and a PDF 2.0 writer — cross-reference stream, object
stream, Identity-H CID font fully embedded, ToUnicode CMap — self-verified in
tests by re-parsing the xref of produced output, and extraction-checked with
pdftotext. `paragraphs.tex` → one justified page in ~6 ms. 105 tests green.
Remaining for M2 (next unit, M2b): Liang hyphenation, the bench harness vs
lualatex, and section/list visual styling. Deliberate debt unchanged from M1
(partial recursion; de-partialing + KP optimality proof queued as the proofs
unit).

## Why not TeX-compatible

The private reference corpus — real, carefully hand-tuned modern lualatex
documents, kept outside this repo — is a catalog of engine warts fought by
hand:

- Silent failures with exit 0: one metadata option flips an experimental list
  implementation and disables list styling; the document grows a page; the only
  trace is a stray note in the log. The regression guard is grepping that log
  from an external script.
- Trap state: `\baselineskip` reads wrong in the preamble while `1ex` is
  already right; font x-height ratios measured by hand and recorded in
  comments because metrics aren't queryable.
- Legacy leakage: `$\cdot$` silently embeds a Type 1 math font with no Unicode
  mapping into an otherwise all-OpenType document.
- A vertical-rhythm system (peer-separation vs label-binding units, documented
  ratios) built from `\newlength` arithmetic, because the engine has no notion
  of design tokens.
- Typed-ish commands via `\NewDocumentCommand`; data-driven body via an
  external template + YAML pipeline; layout invariants checked by scripts.

Compatibility would preserve every one of these. The project exists to delete
them.

## Principles

1. No silent failures. Configuration conflicts are errors. Layout invariants
   are first-class assertions (page count, font embedded, element fits) checked
   by the engine against what it actually shipped; violation fails the build.
2. Layout is a value, not a side effect. Fonts, metrics (x-height, cap height),
   spacing, the page tree: queryable, printable, diffable. "Why did this become
   two pages" is a question the engine answers.
3. Design tokens are native: named spacing scales (separate-peers vs
   bind-label), palette, type scale — defined relationships, no loose decimals
   at use sites.
4. Modern only: UTF-8 in, PDF 2.0 out (cross-reference streams, object
   streams, XMP metadata, UTF-8 text strings), OpenType only, every glyph
   Unicode-mapped. No DVI, no TFM, no 8-bit encodings, no aux-file fixpoint —
   cross-references resolve in memory in one run, no rerun dance, no artifact
   litter.
5. Clean theorems over faithful warts: the language is designed so the
   theorems are short (see Certification).
6. Fast: flashtex-fast one-shot builds, then a worker mode for live re-render.
7. Heavy machinery starts isolated, then gets absorbed. Anything uncertified
   or heavyweight lives behind a typed, cached boundary; the native Lean 4
   surface expands to absorb one boundary at a time, when it pays. Documents
   never change when a boundary is absorbed.

## The language

LaTeX-shaped surface, clean core:

- Familiar notation: `\command{...}`, environments, `%` comments, `$...$` and
  `\[...\]`, `\section`, `itemize`. Porting a well-written lualatex *body* is
  mostly mechanical; preambles are replaced by declarations — the preamble is
  where the warts lived.
- Static grammar: no catcode reprogramming; lexing is fixed and total.
- Typed commands: declared signatures (content, text, length, color, optional
  args), errors at definition and call sites.
- Terminating by construction: substitution plus bounded iteration/map, no
  unrestricted recursion (an explicit fueled escape hatch if ever needed).
- Lengths with units and stretch/shrink are typed values; font metrics are
  expressions; no preamble-time trap state.
- Data-driven documents: records and lists as values, mapped over in the
  document — replaces the external template + YAML pipeline.

## Heavy machinery: isolate, then absorb

The escape hatch generalizes into the project's growth mechanism. A boundary
is a contract: request type in, measured box or structured data out, a pinned
external tool behind it, a content-hash cache in front of it, and a trust
label. The certified core claims placement and measurement of boundary
output, never its contents — and every build can report its external-content
inventory: what on the page came through a boundary, from which tool.
Absorbing a boundary swaps the external tool for a native Lean implementation
behind the same type, so trust only ever grows and documents never notice.

- Graphics (boundary first): native TikZ would require the full TeX macro
  machinery — catcodes, `\expandafter`, registers — plus the pgf layers on
  top; there is no useful partial TikZ. `external[tikz]` blocks go to pinned
  lualatex + standalone and come back as opaque measured boxes. Cache-warm
  builds need no TeX installed. Absorbed later by a typed native graphics
  DSL (horizon, after M6).
- Assets (native from the start): `\figure{...}` places external PDF pages
  (form XObjects — vector stays vector), PNG, and JPEG as measured boxes;
  the only boundary is the filesystem.
- Shaping (native first, boundary if needed): Latin shaping is native; a
  shaping boundary can serve complex scripts before a native shaper exists.
- Bibliography (boundary long before native): a biber-shaped boundary
  returning structured data can serve papers well before any native
  implementation is worth writing.

## CLI and logging

Zero-config by intent: good defaults, flags for the rest, nothing required.

- Quiet success. Default output is errors, warnings, and one summary line —
  on stderr, nothing else. LaTeX's console spew is a named anti-goal.
- Verbosity is opt-in and layered (the ssh model): `-q` errors only ·
  `-v` phases and timings · `-vv` decisions · `-vvv` trace.
- stderr is for humans; stdout is reserved for machines. `--porcelain` emits
  JSONL events (diagnostics, phases, summary) on stdout for editors and
  scripts; the human channel goes silent.
- Diagnostics carry severity, a stable code, message, span (file:line:col),
  and help — rendered Rust-style for humans, structurally for porcelain.
  Same data both ways; never two sources of truth.
- Color: auto on TTY, `NO_COLOR` respected, `--color always|never|auto`.
- Exit codes are the API: 0 ok · 1 document errors · 2 assertions failed ·
  3 usage · 4 internal.

## Architecture

Pure pipeline, effects at the edge — IO only in the CLI driver; files and
fonts surface as request values the driver fulfills:

    bytes → UTF-8 → lexer → parser (AST) → elaborator (typed doc IR)
          → layout (boxes/glue, Knuth–Plass, pages) → PDF writer

- `leantex build doc.tex` — one shot, machine-readable diagnostics, exit code
  reflects assertions.
- `leantex worker` — JSONL protocol for live re-render (later milestone).

## Certification (theorems that pay)

- Parser: total, deterministic.
- Elaboration: terminating and deterministic — reachable only because the
  language is designed for it.
- Knuth–Plass: returns minimal total demerits over feasible breakpoints.
- Dimension arithmetic (fixed point, sp = 2⁻¹⁶ pt): exact, no silent overflow.
- Assertions: verdicts sound with respect to the shipped page tree.
- PDF: cross-reference and object streams correct by construction; every
  glyph carries a Unicode mapping.
- UTF-8: total decode, round-trip.

## Testing

- The in-repo corpus is synthetic only, and synthetic means invented: no
  text, topics, or distinctive design values (fonts, spacing constants,
  palettes) carried over from the private corpus. Placeholder names,
  `example.org` contacts; a dummy document is about leantex itself or a
  plainly fictional subject. The private corpus (real documents, including
  the text of talks) stays outside the repo and outside git.
- Two tiers: CI runs goldens, property tests, and assertions over
  `tests/corpus/`; the M3/M5 acceptance bars run locally against the private
  corpus and never enter CI.
- The corpus sketches are also the language design artifacts: syntax
  decisions land there first, then in the grammar.

## Milestones

- M0 scaffold: lake project, CLI + diagnostics + logging spine with the
  UTF-8 stage live, test harness, CI. Bench moves to M2 — nothing to measure
  sooner.
- M1 language core: lexer, parser, elaborator, typed commands; AST goldens;
  totality/termination/determinism theorems.
- M2 paragraphs: boxes/glue, Knuth–Plass with Liang hyphenation, PDF 2.0
  writer (xref + object streams from the start) with an embedded OTF;
  optimality theorem. Bench harness vs lualatex arrives here.
- M3 documents: sections, lists, color, geometry, headers/footers, hyperlinks
  and PDF metadata, design tokens, layout assertions.
  Acceptance (local, private corpus): the resume ported, one page asserted,
  side-by-side at least as good as the lualatex original, its external check
  scripts retired. CI equivalent: `tests/corpus/resume.tex`.
- M4 math: unicode-math-style input via OpenType MATH metrics.
- M5 figures + slides: asset embedding (PDF pages, PNG, JPEG), external
  render blocks with content-hash cache (the TikZ escape hatch), frames,
  overlays, speaker notes (second-screen build), verbatim code blocks,
  per-glyph font fallback chains.
  Acceptance (local, private corpus): the talk ported, figures included.
  CI equivalent: `tests/corpus/talk.tex`.
- M6 speed and polish: bench-driven optimization vs lualatex and flashtex;
  worker mode; microtype-grade protrusion.

## Non-goals

- Running latex.ltx or CTAN packages; byte or box compatibility with any
  engine.
- Native TikZ/pgf — the graphics boundary covers it (see Heavy machinery); a
  typed graphics DSL is the horizon replacement.
- Native bibliographies, indexing, glossaries: post-M6; a biber boundary can
  serve papers sooner if a document demands it.
- Tagged PDF: revisit later; whatever lands must never silently alter layout
  — that is the original wart.

## Open questions

- Math surface: how much amsmath notation to adopt vs simplify.
- Command definitions: LaTeX-shaped `\newcommand` syntax, Lean-flavored defs,
  or both with one desugaring into the other.
- Worker protocol: mirror flashtex's JSONL for editor reuse, or design our own.
- External tool pinning: how hermetic (a TeX Live snapshot? a container?) the
  escape-hatch renderers must be for cache keys to be trustworthy.

## Decisions

- 2026-09-15: LaTeX-lookalike with clean semantics over TeX compatibility.
  Rationale: the corpus shows compatibility preserves the warts; the goal is
  very good documents and clean theorems, not exactness to existing engines.
- 2026-09-15: lualatex is the quality and speed reference, not a semantics
  oracle. Differential testing means side-by-side quality comparison on the
  ported corpus, plus the assertion harness.
- 2026-09-15: target PDF 2.0 (ISO 32000-2) from the first shipped byte —
  xref streams, object streams, XMP. A downgrade switch only if a real
  consumer ever demands 1.7; none known.
- 2026-09-15: special packages (TikZ first) get an external-render escape
  hatch — pinned tool, content-hash cache, opaque measured box — rather than
  macro compatibility. Native graphics DSL is the eventual replacement.
- 2026-09-15: the escape hatch generalized into the growth mechanism —
  isolate heavy machinery behind typed, cached boundaries and progressively
  expand the native Lean 4 surface to absorb them. Trust is monotone:
  absorption replaces an opaque box with certified output behind an
  unchanged type.
- 2026-09-15: personal information includes the text and topics of private
  documents (talks, resume). In-repo fixtures are invented, not derived;
  the corpus sketches were scrubbed accordingly (fonts, spacing constants,
  and subject matter replaced).
- 2026-09-15: CLI and logging follow modern conventions (the clig.dev
  family): quiet success with one summary line, stderr for humans, stdout
  reserved for `--porcelain` JSONL, an `-v/-vv/-vvv` ladder, `NO_COLOR`
  respected, exit codes as API, zero required configuration. LaTeX-style
  console verbosity is an anti-goal.
- 2026-09-15: the in-repo test corpus is synthetic only; real documents stay
  private and local. Acceptance bars run locally, CI runs the dummies.
