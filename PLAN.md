# leantex — plan

Fast, certified, modern document engine in Lean 4: one language, two
surfaces, two backends.

Not a TeX reimplementation: a clean LaTeX-shaped language with specified
semantics and modern defaults, judged on producing very good documents — as
PDF 2.0 *and* as modern clean HTML. Markdown is a second surface defined by
desugaring into the same language. lualatex is the go-to to beat on the PDF
side; on the HTML side the incumbent is a hand-maintained static-site
pipeline. flashtex sets the speed bar.

## Status

**Where it is.** Two backends are real. PDF 2.0: justified paragraphs with
Knuth–Plass and Liang hyphenation, font families with true bold/italic/mono
faces, the `\tiny`–`\Huge` size scale, small caps, named colours,
font-relative design tokens, page geometry, running head/foot, hyperlinks as
link annotations, document metadata, and layout assertions that fail the
build. HTML5: a typed tree with a certified escaper, semantic markup, tokens
as CSS custom properties, `--css bulma` interop, one self-contained file.
A document written for lualatex compiles as written: LaTeX idioms translate
to the native declarations, unknown constructs degrade to their content with
a warning, and `-v` lists every translation with its shorter spelling.
Measured by `scripts/bench.lean`: 1 KB in ~16 ms against lualatex's ~476 ms; a
generated 129 KB / 30 pages in ~149 ms against ~983 ms, with paragraphs
broken in parallel.

**Where it is going.** This plan now covers one engine with **two surfaces**
(tex primary, markdown as sugar) and **two backends** (PDF and HTML,
including slides).

**Immediately next.** M4b theorem environments, or M5 slides. Slides were
blocked on the size scale, which now exists.

**Open, tracked, not hidden.** `Elab.takeArgs`/`elabInlines`/`elabBlocks`
are `partial` — three, not the two an earlier entry claimed; an audit found
ten and seven were removed (2026-09-16 entry). The Knuth–Plass optimality
theorem is held empirically by `scripts/kp-fuzz.lean`. Small caps are
synthesised rather than drawn, math is emitted as source, and element styling
(section fonts, list spacing) is not yet declarable, which is what keeps the
real resume from matching its lualatex build exactly.

### Log

Newest first. Entries are immutable; corrections are new entries.

2026-09-16 — two section headings rendered in poppler and Ghostscript and
not in macOS Preview. The PDF built on the Mac was byte-identical to the one
built here (the engine is deterministic across hosts, which made the
comparison possible), so the fault was in the file, and the only thing
those two lines had that no other line did was a `TJ` adjustment past
±32767: the gap before each heading's rule, 433pt at 12pt, written as
−36089 thousandths. Everything else in the document stayed under 16 bits,
and no other producer writes moves that large that way — TeX moves the pen
with `Td`. The writer now tracks the pen against the layout position and
writes a move only when glyphs follow: a `TJ` adjustment inside an open
array when it is small, an absolute `Tm` otherwise. A rule-only line (an
underline's sibling) writes nothing into the text object, where before it
wrote a `TJ` array with no strings. The tests pin both: no adjustment past
sixteen bits, no glyphless array, and a fill crossed with `Tm`.

2026-09-16 — the resume matches its lualatex build line for line, at
natural glue, and fits its page. The gap under the name was 28pt too wide
and the page ran to two. Five causes, each a rule TeX has and the engine
did not:

- Vertical space after a line was that line's own leading, so a `\Huge` title
  pushed the next line a Huge leading down. TeX's rule: the distance is the
  leading of the line being placed, unless the previous depth plus this
  height plus `\lineskip` is more. Heights are cap height (OS/2 `sCapHeight`,
  now parsed) and depths the font's descent, per run in its own face — the
  `hhea` ascent reserves room for accents and would space every body line
  apart.
- `\par` inside a scope group became a forced break, so `{\Huge Name \par}`
  set an empty Huge line. It now ends the paragraph, and the group's
  declarations carry into what follows: `{A \par B}` is `{A}\par{decls B}`.
- Vertical glue summed or replaced by accident. Now LaTeX's rules: `\vspace`
  is a `\vskip` and adds; an element's own space (a list's `topsep`, above
  and below; a heading's `before`) is an `\addvspace` and takes the larger
  against glue already owed; `parskip` is paid only when nothing was declared.
  The block walk owes a gap and pays it when the next line comes.
- `parskip` was a constant 6pt. It is a page property with rubber
  (`\page{ parskip = ... }`); a LaTeX class declares 0pt (KOMA's `parskip=`
  option, the parskip package and `\setlength{\parskip}` declare theirs), so
  LaTeX-written documents get LaTeX's spacing and native ones keep the
  engine's default.
- Skips carried no rubber into layout. Now a skip is glue, and a page is set
  like a line: skips shrink within their limits before a break is taken
  (reported as N0200 at -v), never stretch. The rubber the resume was written
  with — `1.8ex plus 0.8ex minus 0.4ex` — finally does the job it was for:
  the resume fits at natural glue now, but with 33pt of shrink in reserve.

Two more the same session made visible. A built-in tested before the user's
definitions shadowed `\link` silently, so the document's underlined link
macro never ran — the document's names now come first, and only
`builtinNames` are reserved (W0303). And `\href{#1}` printed the parameter's
name, because URL arguments were read as source text; `argText` substitutes
the caller's text. `dir` became `dirs`: fontspec names a `Path=` per face.

2026-09-16 — the fixtures were not portable, and the test suite was not
hermetic. `tests/corpus/resume.tex` failed on a Mac with E0403 `Nimbus Roman`:
not a Mac problem and not a font-installation problem — the fixture named
this Linux host's URW fonts, eight fixtures named some host's fonts, and the
harness read DejaVu from `/usr/share/fonts`. The invariant, now pinned: what
the checkout renders is a function of the checkout. Fixtures that name fonts
ship them in `tests/corpus/fonts/` (Source Serif Pro, Source Code Pro, Open
Sans: a CFF family and a TrueType one, so both parsers are exercised; OFL and
Apache-2.0 texts alongside) and declare `\fonts{ dir = "fonts" }`; the
harness scans that directory and nothing else. Verified in a mount namespace
with every system and TeX Live font directory emptied: every declaring
fixture builds and embeds the shipped faces; the bare ones report E0401, as a
machine with no fonts should. Two general pieces came out of it, both small:
`dir` in `\fonts`, resolved against the document like `\input` and searched
first, with fontspec's `Path=` carried into it by the compat layer (a font
file name then denotes its face's family, so the bold and italic beside it
resolve too); and the scan sorts directory entries, because `readDir` order
differs between hosts and resolution breaks ties by scan order — a latent
nondeterminism the same invariant forbids. A document that compiles under
lualatex on a machine compiles under leantex on the same machine because it
names fonts that machine has; that was never the fixtures' situation.

2026-09-16 — the real resume compiles as written. It produced 78 errors and
not one was the document's fault: 52 came from a preamble asking packages for
what the engine provides directly, the rest from the author's own macros and
five body idioms. Principle 8 came out of it. A compat pass rewrites LaTeX
idioms into the native declarations on the parsed tree — `geometry` →
`\page`, `\definecolor` → `\palette`, `\setlength` → `\tokens`,
`\NewDocumentCommand`/`\newcommand` → `\define` with `#k` as `\ak`,
`\hypersetup` → `\pdfmeta`, `\ihead`/`\ohead` → `\runninghead`,
`\linespread` → a leading factor, `\color{n}` → the declaration form, and
thirty packages that are a note rather than a warning. Unknown commands warn
once per name and keep their arguments as text; `\input` splices in the
driver. Notes print at `-v`; the success line counts them. Fixing this found a
layout bug older than the compat layer: a paragraph ending in `\\` vanished
whole, because the empty last line had no feasible predecessor and the
breaker returned nothing. What remains visible against the lualatex build is
element styling (coral sans headings with a rule, tighter bullets, no running
head on page 1), which is M3d.

2026-09-16 — three worker agents ran in parallel worktrees and landed by
fast-forward after a fresh-context audit of each diff. Lint: Lean 4.34 ships
no formatter, so `lake build --wfail` with the `linter.extra` set is the gate,
in a 68-line pre-commit hook that also rejects new `partial`/`sorry`/`unsafe`
and hand-edited goldens from the staged diff (0.03 s no-op, 5.7 s cold). Its
audit found ten `partial` defs where PLAN claimed two; seven were removed the
same day with byte-identical output. Parallel: layout was 93% of the 30-page
build and Knuth–Plass 77% of layout, so the block walk now emits jobs and one
pure `Task` per paragraph runs `kp`, placement replaying in document order:
576 → 149 ms, output byte-identical on every corpus file including the real
resume through the compat layer. Font probing runs in chunks of 64, 253 → 80
ms on an 1800-face tree. A font-scan disk cache was measured and declined:
default dirs scan in 35 ms. Principle 10 records the position these
implement.

2026-09-16 — process rule, from the user: before fixing an issue, write the
invariant whose absence allowed it — as a theorem statement if it is one, a
test if it is not — and fix to that, not to the symptom. AGENTS.md carries
it. The accumulator rule (a structural walk threads an `Array`; `#[x] ++
rest` is quadratic and cost 4 → 1157 ms twice in one afternoon) is the first
capture under it.

2026-09-15 — four latent no-ops found by rendering the same fixture through
both backends and looking at the output. Each was accepted by the elaborator
and then silently discarded, which is the failure mode this engine exists to
avoid, and none was visible to `lake test`.

The `\tiny`–`\Huge` scale did nothing: the PDF dropped size styles and HTML
emitted a class with no rule. The scale now lives in the IR because both
backends read it and must agree; HTML generates its rules from that table so
the two cannot drift. Boxes and glyph runs carry the size they were measured
at, so a paragraph may mix sizes, and vertical space follows the tallest run
on a line.

`\,` and its siblings were mapped to Unicode code points and set as
characters. No Type 1-derived face has a glyph at U+2009, so every one was
dropped — three times in the resume, around the separator they were spacing.
They are kerns now: width, no glyph, never a breakpoint.

`\scshape` did nothing. The PDF path synthesises small caps by splitting a
word into runs that carry their own size; HTML asks for `font-variant-caps`
so the browser can use a face's real ones. The two mechanisms differ on
purpose.

A palette name coloured to the end of its enclosing group, so
`\primary{Alex} Doe` painted Doe too. It binds a following group as its
argument now, and keeps the declaration reading when there is none.

Two decisions came out of this. `\hfill` on a line it shares with the fill
that runs out a paragraph now takes the whole leftover instead of half:
LaTeX splits it, and a row of dates that stops halfway to the margin is not
what anyone means. And a stretched row broken by `\\` becomes a column of
rows in HTML, because a `<br>` cannot end a flex line — Chromium does not
treat one as a flex item, so no stylesheet fixes it and the break has to be
structural.

Two process notes. Writing the first test that reads produced PDF bytes
immediately caught a regression in the same change: a default value on a new
constructor field turned `.run idx _ _ _ glyphs` into a pattern matching only
`size = 0`, so glyph collection found nothing and one face was embedded where
six belonged — with the whole suite green. Default values on inductive fields
let patterns under-specify silently and are not used here. Separately, `build`
and `dump` took the *next token* as their filename, so every flag written
after the command was eaten as the file; `--color` had been broken that way
since M0 and no test caught it, because every test passed flags before the
command.

2026-09-15 — M4 landed: the HTML backend. `Html` builds a typed tree and
`HtmlDoc` turns a `Doc` into a page. Nothing concatenates tag strings, and
two theorems say what the escaper buys: escaped content carries no `<`, so no
text node can open a tag, and an escaped attribute value carries no quote.
`style`/`script` payloads are checked for their own terminator instead,
because CSS and JS do not follow element-content rules. Tokens become CSS
custom properties and a named colour becomes `var(--name, literal)`, so the
tokens really are the styling API for both backends. `--css bulma` binds them
to `--bulma-*` without shipping the framework; `--css none` emits semantic
markup only. Running content warns (W0007) rather than vanishing, and math
rides in `data-tex` with `--math-boundary` for an optional renderer.

2026-09-15 — M3c landed: hyperlinks reach the PDF as Link annotations, with
adjacent runs sharing a destination merged into one rectangle per line.
Running content became `\runninghead`/`\runningfoot` taking inline content
rather than a `\page{header = ...}` key, because a key/value declaration
cannot carry `\hfill` or a `\pagenumber` placeholder; placeholders resolve
once the page count is known. A `\define` body may now produce blocks, and
`\\[len]` carries extra space after a break — with the bracket required to be
adjacent, where LaTeX skips spaces and so swallows the bracket of a line that
legitimately starts with one.

2026-09-15 — plan refined for HTML, slides, themes, and theorems. The leanmd
workstream merges in: markdown becomes a second surface defined by
desugaring, HTML becomes a peer backend, and the milestone ladder is rebuilt
around them (M4 HTML, M5 slides, M6 math, M7 markdown, M8 figures, M9
verified inclusions). Three positions were taken rather than deferred: HTML
slides are in scope with a ~3 KB vendored controller instead of reveal.js
(revising leanmd's zero-JS non-goal, with reveal available as a boundary);
a theme is a token bundle, and the default is a modernized Metropolis
successor with a first-class dark variant; theorem environments may bind to a
machine-checked Lean name, so a missing or unproved theorem fails the build.

2026-09-15 — M3b landed: the document surface a designed page needs.

`\fonts{ body/sans/mono }` selects installed families. Faces are discovered
natively — `FontDb` reads only each file's header plus its name, OS/2, head
and post tables, classifying 55 faces in ~35 ms. Resolution is weight-aware
rather than a bold flag, so URW Bookman's "Demi" (usWeightClass 600) is
correctly its bold face, and a plain face beats a same-family Condensed
variant; italic is categorical and never silently replaced by upright. Layout
resolves each style to a font index carried on boxes, penalties and runs; the
PDF emits one Identity-H CID font per *used* face with its own ToUnicode (12
declared, 6 embedded in the fonts fixture) and switches faces by closing and
reopening the TJ array.

`\palette` declares named sRGB colours, usable as `\textcolor{name}{...}` or
as bare declarations that colour the rest of their group; colour rides on runs
and emits `rg`, and a colour change closes the TJ array the way a font change
does.

`\tokens` declares named lengths that may be font-relative (`2ex plus 0.5ex`)
or derived from an earlier token (`sep = 0.75 * rhythm`). Entries are walked
one at a time, because parsing the block in one shot leaves in-block
references unresolved. Resolution happens at layout against the real font size
and OS/2 x-height, which is why `Dim.Length` keeps em/ex parts symbolic —
tokens are declared before any font is chosen. `\block[before = sep]` applies
one; `\hfill` pushes trailing content to the margin (the dated-entry shape).

Text symbols (`\middot`, `\endash`, `\ldots`, …) live in the *lexer*,
because they also bend the space-swallowing rule: a control word normally eats
the following whitespace so `\textbf {x}` adds no space, but a symbol takes no
argument, so eating it turns `a \middot b` into "a ·b" — a wart, not a
feature. `\hfill` keeps swallowing, since a space after the stretch would be
visible at the far margin.

The resume fixture is down from 14 diagnostics to two distinct ones: the
`header` page key, and `\block` inside a `\define` body. W0002 "styles are
not rendered" is gone.

2026-09-15 — M3a landed: the declaration layer. `\page` (size, width, height,
margin, vmargin, hmargin) resolves once into layout geometry via
`Geom.ofPage`; `\pdfmeta` writes the Info dictionary and an XMP packet;
`\assert` checks `pages <op> N` and `fonts.all_embedded` against the shipped
page tree, exiting 2 and writing no PDF when one fails — the "no silent
failures" principle now has teeth. Declaration values are typed (strings,
exact dimensions in pt/bp/in/cm/mm/pc/sp, numbers, names, opaque blocks) with
one diagnostic code per failure mode: unknown key names the known ones, wrong
type names what it wanted, and a declared-but-unimplemented key (`header`)
reports as pending with its milestone rather than as a type error. Verified
by Poppler: A5 page size, all four metadata fields, PDF 2.0.

2026-09-15 — M2 landed, then a proofs pass over the pipeline. The engine
produces readable, justified PDF 2.0 with automatic American-English Liang
hyphenation, section sizing, centered blocks, hanging list markers, and
multi-page assembly. Identity-H CID font, full OpenType embedding, ToUnicode,
object streams, cross-reference stream; tests re-parse every direct xref
offset, and Poppler independently reports PDF 2.0 with embedded,
Unicode-mapped fonts. Measured by `scripts/bench.sh` (five-run wall-time
median): 1 KB is 17 ms vs lualatex 481 ms; generated 129 KB / 30 pages is
598 ms vs 977 ms. Evidence and caveats in `bench/README.md`.

Termination status — `partial` is gone from the parser (rewritten as a
single pass over an explicit frame stack, so totality is immediate), the
UTF-8 validator (was fueled; now well-founded on bytes remaining), `rawSrc`,
the layout block walk, and the IR printers. Each rewrite was checked to
produce byte-identical output, not merely to pass.

Two functions remain `partial`: `Elab.elabInlines` and `Elab.elabBlocks`.
Nontermination is still impossible by design — a user command's body sees
only definitions that precede it — but the measure is lexicographic
(visible-command limit, then tree size), and the checker cannot see it while
argument consumption is interleaved with tree descent: a command consumes
`[...]`/`{...}` from its *siblings* and then continues on the remainder, so
cons-recursion alone does not expose the decrease. Designed fix, not an
annotation: split macro expansion from elaboration (Phase A substitutes user
commands, structurally recursing on the limit; Phase B elaborates a
command-free tree structurally). It needs supporting lemmas about suffixes
(`sizeOf (l.drop k) ≤ sizeOf l`) and `Array.toList`. Scheduled as its own
unit; it is a small formalization project, not a refactor.

Also open: the Knuth–Plass optimality theorem. Until it exists, optimality
is established empirically by `scripts/kp-fuzz.lean`, which differentially
tests the pruned DP against brute-force enumeration (2000 randomized
paragraphs with glue, flagged hyphen penalties, and forced breaks).

Determinism needs no proof: every stage is a pure Lean function, so it is
definitional. The claims worth real work are termination, totality (no
panicking index), and optimality.

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
8. Elaboration is non-blocking. For every input the parser accepts, a
   document comes out. A construct the engine does not implement never
   removes content — its arguments still render — and the diagnostic names
   the span and, where one exists, the native spelling. Only malformed
   syntax, a failed `\assert`, and a font that cannot be found stop a build.
   Best effort is the contract, not a fallback: a warning the author can act
   on beats a refusal they have to work around.
9. Each document class has a primary backend, and the other is a faithful
   degradation, never a failure. `article` is PDF-first and its HTML is a
   readable page; `slides` is HTML-first (the interactive deck) and its PDF
   is the handout. A template optimised for one medium behaves sensibly in
   the other because both read the same IR; no template targets both
   equally, and none has to.
10. All Lean 4. The only C is Lean's runtime — the small isolated kernel the
    project wants — and there is no Rust and no FFI. Parallelism is `Task`
    over pure functions, race-free because there is nothing to race on;
    results join in document order so output never depends on scheduling.
    Incrementality only where a measurement shows it pays; whole-document
    compile is fast enough that the document itself is never cached.

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

## Architecture

Pure pipeline, effects at the edge — IO only in the CLI driver; files and
fonts surface as request values the driver fulfills:

    .md ──parse──► MD AST ──desugar──► surface AST ◄──parse── .tex
                                            │ elaborate
                                            ▼
                                         doc IR ──emit──► HTML5 (+ slides)
                                            │
                                     layout (boxes/glue,
                                      Knuth–Plass, pages)
                                            │
                                            ▼
                                        PDF 2.0

The IR is the waist. Everything above it is surface syntax; everything below
is a backend. Both surfaces reach both backends, so markdown→PDF and
tex→HTML come for free rather than as N×M special cases.

- `leantex build doc.tex` — one shot, machine-readable diagnostics, exit code
  reflects assertions. `--emit pdf,html` selects backends.
- `leantex expand doc.md` — pretty-prints the desugared surface AST as real
  `.tex`: the inspectable witness of what markdown means, and the ejection
  path when a document outgrows it.
- `leantex worker` — JSONL protocol for live re-render (later milestone).

## Surfaces: LaTeX-shaped primary, markdown as sugar

Merged from the leanmd workstream (that repo reduces to a pointer; its plan
is superseded by this section plus the milestones).

The tex-shaped surface is the semantics of record. Markdown has **no
semantics of its own**: its meaning *is* its desugaring — a total,
deterministic, span-preserving function MD AST → surface AST. One elaborator,
one place where meaning lives. Deleting the markdown parser would change no
document's meaning.

That is the structural defense against the pandoc failure mode (N surfaces ×
M backends meeting in a lowest-common-denominator IR, with silent per-route
drift):

- Desugaring is AST → AST, never through generated text. Generating tex and
  re-parsing it would destroy diagnostic provenance and put two parsers in
  the pipeline; diagnostics carry original `.md` spans all the way through.
- Directives are typed-command sugar: `:::{figure}` desugars to the typed
  `\figure{...}`, and the directive registry is *derived from* command
  signatures. Markdown can never express what the surface language cannot.
- Asymmetry is one-directional by design: md ⊂ tex-expressible, and the tex
  surface never chases markdown features.

Dialect: CommonMark-shaped but strict. Raw HTML passthrough, lazy
continuation, and indented code blocks are **errors with fix-its**, not silent
divergence — the first is what keeps the injection-safety argument short, the
others are the measured ambiguity classes. CommonMark's emphasis
delimiter-run algorithm is kept faithfully: it is gnarly but specified and
deterministic, and the warts worth deleting are the silent ones, not the
ugly-but-deterministic ones. The 652-case spec suite is a **classifier, not a
gate**: every case carries a committed verdict (`match`,
`rejected-with-diagnostic`, `deliberate-divergence` + rationale) and an
unclassified deviation fails CI.

Extensions: YAML frontmatter (data-driven documents), `$…$`/`$$…$$`, typed
directives and roles, pipe tables, footnotes, and in-memory cross-references
(`{#id}` / `[](#id)`) with no aux-file fixpoint.

## The HTML backend

Not an afterthought export: a peer backend off the same IR, and the cheaper
one — it needs no layout engine, so it exercises the whole frontend at a
fraction of the cost.

**Typed tree, certified escaping.** A well-formed-by-construction HTML tree,
never string-concatenated tags. With raw-HTML passthrough deleted from the
markdown dialect and a certified escaper on every text node, document content
can never become markup. That argument is short *because* the dialect removed
the carve-outs.

**Semantic HTML5, zero dependencies by default.** `<article>`, `<section>`,
`<h1>`–`<h4>`, `<figure>`/`<figcaption>`, `<dl>` where it means a
description list. One self-contained file by default: critical CSS inlined, no
CDN, no webfont round-trip (a subset font inlined or self-hosted), works
offline and leaks nothing. A generated document should not require a network.

**Zero JavaScript for documents.** Non-negotiable for articles, papers, and
pages. Slides are the one exception and are argued below.

**Design tokens are the styling API.** `\tokens` and `\palette` map 1:1 onto
CSS custom properties, so the same declarations drive both backends: `sep`
becomes `--sep`, `primary` becomes `--primary`. A document's design intent
survives the trip to CSS instead of being re-encoded by hand.

**Framework interop, not framework dependency.** Bulma 1.x is a good tradeoff
for a hand-built site — CSS-only, no JS, and since 1.0 it is itself built on
CSS custom properties with a dark mode. But a *generated* document should not
ship a 200 KB framework to use four of its classes. So: the default
stylesheet is our own, token-driven, small; and `--css bulma` is an interop
mode that emits Bulma class names on containers and maps our tokens onto
`--bulma-*` properties, so generated pages drop into an existing Bulma site
and inherit its accent. Same for a plain `--css none` (semantic markup only,
bring your own sheet).

**Math, honestly staged.** MathML Core is now native in Chrome, Safari, and
Firefox, so it is the destination — no MathJax in the shipped output. Two
caveats that shape the plan: Chromium ships *no* math font, so the stylesheet
must supply one (`math { font-family: … }` with a self-hosted OpenType MATH
face), and all three engines still have rendering gaps. Until the math
milestone lands, HTML math is not faked: the source is emitted in a
`<span class="math" data-tex="…">` and an *optional* client-side renderer can
be attached as a boundary (`--math-boundary katex`). Native MathML replaces
it, the markup stays the same, and the boundary becomes unnecessary.

**Accessibility rides HTML.** Landmarks, heading order, contrast checked
against the token set, focus-visible styling, `prefers-reduced-motion`
honored. This is also why tagged PDF stays deferred: the accessible artifact
exists on the HTML path.

**A markdown alternate is an output, not a chore.** Since the markdown
surface exists, the engine can emit an `llms.txt`-style plain-markdown
rendition of the same IR alongside the HTML — one source, three artifacts.

## Slides

The engine already plans PDF slides (frames, overlays, speaker notes). Beamer
overlay specs (`\item<1->`) and reveal.js fragments are the *same construct*,
so once overlays exist in the IR, an HTML deck is nearly free. Both decks come
from one source.

**Revising the leanmd non-goal.** That plan said no HTML slides in v1, because
overlay interactivity conflicts with zero-JS. That was the wrong call:
navigation *is* interactive, and a CSS-only deck cannot do fragments, a
speaker view, or a timer. Pretending otherwise ships a worse artifact. The
resolution is a budget, not a ban.

**A tiny vendored controller, not reveal.js.** Target ≈3 KB, hand-written, no
dependencies, inlined in the file. It covers what is actually used from
reveal.js: keyboard/touch/click navigation, fragment stepping, URL-hash
deep-linking, a hairline progress indicator, and a speaker window (notes,
next-slide preview, elapsed timer) over `BroadcastChannel`. Not covered, on
purpose: 3D transitions, auto-animate, plugin ecosystem, markdown-in-HTML
slides (we have a markdown surface).

**Degradation is the feature.** With JavaScript disabled the deck renders as a
linear scrollable document with every slide and every fragment visible — a
readable handout. Decks get distributed and read without the speaker, so that
path is not a fallback, it is a second deliverable. reveal.js does not give
this by default.

**reveal.js stays available as a boundary.** `--emit reveal` produces
reveal-compatible markup for anyone who wants that ecosystem, exactly like the
TikZ boundary: pinned tool, no engine dependency, absorbed or not on its own
schedule.

**Overlays dim rather than hide.** A hidden fragment reflows the slide as it
appears; a dimmed one does not. Dimming also gives the PDF path a sane
rendering (one page per step, pending items in gray) and matches the taste
already visible in the reference deck, which sets covered content
transparent. One overlay semantics, two backends.

## Design system and themes

A theme is **a token bundle plus a small layout policy**, not a pile of
hard-coded rules — that is what `\tokens`/`\palette` are for, and it is what
makes a theme portable across both backends. `\theme{name}` selects one;
documents override any token.

The Metropolis/moloch lineage is the starting point and needs updating: it is
excellent 2015 flat design — sans throughout, flat blocks, minimal chrome, a
progress bar — and it shows its age in three specific ways worth fixing.

**1. Pure-flat has no depth.** Modern practice separates planes with a 2–4%
surface tint rather than borders or shadows: quiet on screen, invisible in
print, no skeuomorphism.

**2. One-mode-only.** Dark is now a first-class variant, not an inversion
hack: the same accent, re-checked contrast (AA body, AAA large), off-white
`#FAFAF9`-class surfaces and near-black `#18181B`-class ink rather than pure
white and pure black on either side.

**3. Type is too small and too uniform.** A modular scale (≈1.25) with body
around 22–24 pt at 16:9 reads from the back row; variable fonts give a display
axis for titles; tabular figures for data. Sans display + sans text with a
*matching math face* (a Fira Sans / Fira Math-class pairing) keeps math from
looking pasted in — the legacy failure this engine already refuses.

Chrome: hairline progress, section number and title in a small footer, no
logo on every slide, full-bleed accent section dividers with a large numeral.
Motion: none by default, and `prefers-reduced-motion` respected where any
exists.

## Theorem environments

A first-class need, not a package: `theorem`, `lemma`, `proposition`,
`corollary`, `definition`, `example`, `remark`, `proof`, with declared
numbering (per-section by default), optional names, and cross-references
resolved in memory.

**Design.** Not a boxed colored panel — that is the dated look, and it breaks
badly across pages. Instead: a 2 px accent rule on the leading edge, a
small-caps or medium-weight label carrying the number, the statement body set
apart by a slight surface tint or italic, generous space above and below.
`proof` is unnumbered with an italic label and a flush-right tombstone (∎).

**Markup.** A labelled container with a real heading and `aria-labelledby`.
No invented ARIA roles: DPUB-ARIA has no `doc-theorem`, and fabricating one
helps nobody.

**The binding worth building.** A theorem environment may cite a
machine-checked artifact:

    \begin{theorem}[Optimality][lean = LeanTex.Core.Layout.kp_optimal]

The build resolves that name against a manifest of the formal surface through
the verified-inclusion boundary: if the theorem is absent, unproved, or
carries a disallowed axiom, the build fails, and the rendered statement gets
a "verified" marker linking to the source. This is the engine's own
layout-assertion principle — check what actually shipped — extended from
layout facts to content facts, and it is why the reproducible-research
machinery below belongs in this project rather than bolted around it.

## Verified inclusions

Prose bound to machine-checked artifacts, with drift as build failure. A typed
request in (an inventory query, a measured count, a generated table), a
structured value out, a content-hash cache in front, a trust label, and an
inclusion inventory in every build's porcelain output: what on the page came
through a boundary, from which artifact, at which hash. A stale inclusion
fails the build.

The engine does **not** execute notebooks or arbitrary code in-process.
Computation happens outside; results enter through the boundary. The core
stays pure and builds stay deterministic — the same isolate-then-absorb
contract as the graphics boundary, with data instead of boxes coming back.

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
- Surface additions for the second surface and backend, contract unchanged:
  input may be `.md` or `.tex`; `--emit pdf,html,reveal,md`; `--css
  bulma|none`; `--math-boundary <tool>`; `expand` (md → tex ejection). The
  porcelain event schema gains inclusion-inventory records.

## Hyphenation

American English, Liang patterns from `hyph-en-us.tex` (ushyphmax: Knuth's
frozen `hyphen.tex` plus Gerard Kuiken's additions — a strict superset, 4938
patterns vs 4447), hyphenmins 2/3, embedded as generated Lean data with the
upstream licence notice preserved. Regenerate with
`lake env lean --run scripts/gen-hyphen-data.lean`.

Why the superset: it offers strictly more admissible break points, which is
what reduces loose and overfull lines — the quality axis that matters here.
The cost is that leantex legitimately differs from a default `lualatex` run,
which loads `hyphen.tex` (TeX Live's `language.dat` maps `english` to it, "do
not change!").

So the oracle must load the matching set: `scripts/hyphen-diff.lean` runs luatex
with `\input hyph-en-us` and compares word for word (552/552 exact as of
2026-09-15). Comparing against plain `lualatex` produces ~3% spurious
mismatches. `\showhyphens` lists every admissible break, not one rendering.

## Certification (theorems that pay)

- Parser: total by construction (one pass, explicit frame stack, no recursion).
- UTF-8: total decode (well-founded on bytes remaining), round-trip.
- Elaboration: terminating by design — the proof is open, see PLAN Status.
- Knuth–Plass: returns minimal total demerits over feasible breakpoints —
  open; held empirically by `scripts/kp-fuzz.lean`.
- Dimension arithmetic (fixed point, sp = 2⁻¹⁶ pt): exact, no silent overflow.
- Assertions: verdicts sound with respect to the shipped page tree.
- PDF: cross-reference and object streams correct by construction; every
  glyph carries a Unicode mapping.

Second surface and backend add:

- Desugaring: total, deterministic, span-preserving.
- Expand round-trip: `parse ∘ print ∘ desugar = desugar`.
- Injection safety: no raw-HTML passthrough plus certified escaping means
  document content can never become markup. Short because the dialect
  deleted the carve-outs.
- HTML well-formedness by construction (typed tree, no string concatenation).
- Verified inclusions: freshness sound with respect to what shipped — a
  reported hash matches the artifact the page was built from.
- Enumerated divergence from CommonMark: harness-enforced by the classifier,
  not a theorem, and labelled as such.

Determinism is definitional: every stage is a pure function. Claims are
marked open here until a machine-checked proof exists — an executable oracle
is evidence, not a theorem.

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
- Hermetic: what the checkout renders is a function of the checkout. A
  fixture that names a font ships it in `tests/corpus/fonts/` and declares
  `\fonts{ dir = "fonts" }`; the harness scans that directory and no host
  location. A fixture that names a host's font is a bug even when it passes
  here — it passes only here.
- The corpus sketches are also the language design artifacts: syntax
  decisions land there first, then in the grammar. A sketch whose commands do
  not exist yet is marked PENDING in its header and left out of the golden
  set until they do — `tests/corpus/theme-modern.tex` is the current example,
  and it exists so the theme is reviewable as data rather than as adjectives.
- HTML output is checked three ways, since "looks right" is not a test: the
  emitted tree is compared against goldens, the file is validated for
  well-formedness, and it is rendered headless and inspected. Differential
  testing for the markdown surface runs against the cmark reference binary on
  the spec suite; disagreements are classified, never ignored.
- Bench, per backend: lualatex on the PDF path (recorded in `bench/README.md`),
  typst as the speed bar, and for HTML the incumbent static-site generator.

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
  M3a (done): `\page` geometry, `\pdfmeta` (Info + XMP), `\assert` with
  `pages <op> N` and `fonts.all_embedded`, checked against the shipped page
  tree — a failing assertion exits 2 and writes no PDF. Declaration parser
  with per-key diagnostics (unknown key, wrong type, unreadable value).
  M3b (done): `\fonts` family selection with real bold/italic/mono/sans
  faces; `\palette` named colours via `\textcolor{name}{...}` and bare
  declarations; `\tokens` font-relative lengths (ex/em) with derived tokens;
  `\block[before = token]` spacing; `\hfill`; text symbols.
  M3c (done): `\runninghead`/`\runningfoot` with `\pagenumber`/`\pagecount`,
  hyperlinks as PDF Link annotations, block-producing `\define` bodies,
  `\\[len]`. Plus the size scale, small caps, and fixed-width kerns, which
  were declared in M3b and implemented nowhere.
  Acceptance (local, private corpus): the resume ported, one page asserted,
  side-by-side at least as good as the lualatex original, its external check
  scripts retired. CI equivalent: `tests/corpus/resume.tex`.
- M4 HTML backend (done, less markdown emission): typed tree, certified
  escaping, semantic HTML5, tokens → CSS custom properties, self-contained
  single-file output, `--css bulma` interop. Math emitted as source with an
  optional client-side boundary until M6. Markdown alternate emission moves to
  M7 with the rest of the markdown surface.
  Acceptance (local, private corpus): one personal-site page side by side
  against the current generator. CI equivalent: a synthetic site page.
- M4b theorem environments: the eight environments, per-section numbering,
  in-memory cross-references, the modern treatment (accent rule, small-caps
  label, tombstone) on both backends.
- M5 slides: frames, overlays with dim-not-hide semantics, speaker notes.
  HTML deck with the ≈3 KB controller and the no-JS linear handout;
  `--emit reveal` boundary. PDF deck one page per overlay step.
  Acceptance (local): the talk ported to both, side by side against the
  current beamer build. CI equivalent: `tests/corpus/talk.tex`.
- M5b themes: token bundles including the modernized Metropolis successor,
  dark variant, contrast checks as layout assertions.
- M6 math: unicode-math-style input; OpenType MATH metrics for PDF, MathML
  Core plus a self-hosted math font for HTML.
- M7 markdown surface: our strict CommonMark-shaped parser (total by
  construction, span-preserving), desugaring, `expand` with the round-trip
  theorem, the spec-suite classifier, frontmatter, directives.
- M8 figures and boundaries: asset embedding (PDF pages, PNG, JPEG), the
  external-render boundary with content-hash cache (TikZ), verbatim code
  blocks, per-glyph font fallback chains.
- M9 verified inclusions: the boundary, freshness assertions, inclusion
  inventory in porcelain output, and the `lean = …` theorem binding.
  Acceptance (CI): a synthetic publication twin builds with live counts, and
  the negative control holds — tampering with the inventory without
  rebuilding fails the build.
- M10 speed and polish: bench-driven optimization vs lualatex, typst, and
  flashtex; worker mode; microtype-grade protrusion.

## Non-goals

- Running latex.ltx or CTAN packages; byte or box compatibility with any
  engine.
- Native TikZ/pgf — the graphics boundary covers it (see Heavy machinery); a
  typed graphics DSL is the horizon replacement.
- Native bibliographies, indexing, glossaries: post-M6; a biber boundary can
  serve papers sooner if a document demands it.
- Tagged PDF: deferred while the accessible artifact is the HTML one;
  whatever lands must never silently alter layout — that is the original wart.
- No in-engine execution of notebooks or arbitrary code: computation enters
  through verified-inclusion boundaries only.
- No liberal authoring mode. Forgiving rendering is a terminal renderer's
  job; a compiler is loud.
- No in-file mixing of surfaces (tex blocks inside md) in v1; the escape is
  per-file ejection via `expand`. A parsed, typed `{tex}` block is a v2
  candidate.
- No framework dependency in generated output. Bulma interop is a mode, not
  a runtime requirement.
- Not a slide *framework*: the HTML controller stays a few kilobytes and
  covers navigation, fragments, notes, and deep-linking. Anything past that
  is what `--emit reveal` is for.

## Open questions

- Math surface: how much amsmath notation to adopt vs simplify.
- Command definitions: LaTeX-shaped `\newcommand` syntax, Lean-flavored defs,
  or both with one desugaring into the other.
- Worker protocol: mirror flashtex's JSONL for editor reuse, or design our own.
- External tool pinning: how hermetic (a TeX Live snapshot? a container?) the
  escape-hatch renderers must be for cache keys to be trustworthy.
- Directive fence syntax: ` ```{name} ` versus `:::{name}` (colon fences do
  not collide with code fences; MyST ships both).
- Whether the HTML backend emits one file per document always, or a
  multi-page site mode with a shared stylesheet — the site use case wants
  the latter, the paper use case the former.
- Slide aspect ratio policy: 16:9 default, and whether a 4:3 or 16:10 variant
  is worth a token bundle.
- Theme naming, and how many bundles ship. Names are cheap and deferred; the
  Metropolis successor is the one that must be good.
- Repo naming once markdown and HTML are visible faces of the engine.

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
- 2026-09-15: one engine, two surfaces, two backends. The tex-shaped surface
  is the semantics of record; markdown is sugar defined by total AST-level
  desugaring, never string translation. Rationale: kills the pandoc N×M drift
  structurally and keeps one place where meaning lives. The leanmd plan merges
  into this document; that repo reduces to a pointer.
- 2026-09-15: HTML is a peer backend off the shared IR, not an export — typed
  tree, certified escaping, semantic HTML5, zero JS for documents, tokens as
  CSS custom properties, self-contained by default. It lands before math and
  before the markdown surface because it needs no layout engine and unlocks
  real output immediately.
- 2026-09-15: framework interop, not dependency. Bulma 1.x is a sound choice
  for a hand-built site and its 1.0 custom-property model maps cleanly onto
  our tokens, so `--css bulma` emits its class names and binds
  `--bulma-*`; the default output ships our own small stylesheet and no CDN.
- 2026-09-15: HTML slides are in scope, revising leanmd's non-goal. Slide
  navigation is inherently interactive, so the zero-JS rule becomes a budget:
  a ≈3 KB vendored controller (nav, fragments, hash deep-links, progress,
  speaker window) instead of reveal.js, with the no-JS rendering being a
  readable linear handout rather than a broken page. reveal.js remains
  available as `--emit reveal`, a boundary like TikZ.
- 2026-09-15: overlays dim rather than hide, so the slide does not reflow as
  fragments appear and the PDF path renders pending items in gray. One overlay
  semantics for both backends.
- 2026-09-15: a theme is a token bundle plus a small layout policy, so themes
  are portable across backends and overridable per document. The default is a
  modernized Metropolis successor: surface tints instead of flat blocks, a
  first-class dark variant with re-checked contrast, a ≈1.25 modular scale
  with 22–24 pt body at 16:9, and a math face matched to the text face.
- 2026-09-15: theorem environments are first-class, styled with an accent rule
  and small-caps label rather than a boxed panel, and may bind to a
  machine-checked artifact (`lean = Name`) through the verified-inclusion
  boundary — absent, unproved, or axiom-carrying fails the build. This extends
  the layout-assertion principle from layout facts to content facts.
- 2026-09-15: MathML Core is the HTML math destination (native in all three
  engines now), with two consequences recorded: the stylesheet must supply a
  math font because Chromium ships none, and until the math milestone lands
  HTML math is emitted as source with an optional client-side boundary rather
  than faked.
- 2026-09-15: hyphenation ships the ushyphmax (`hyph-en-us.tex`) pattern set,
  not Knuth's frozen `hyphen.tex`, for the extra admissible breaks. Verified
  faithful against luatex loaded with the same patterns (552/552 words).
  Recorded because a default `lualatex` comparison looks like ~3% failures.
- 2026-09-15: the in-repo test corpus is synthetic only; real documents stay
  private and local. Acceptance bars run locally, CI runs the dummies.
