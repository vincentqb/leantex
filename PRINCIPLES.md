# Principles

These decide what the rules in `AGENTS.md` leave open, each naming its check (`scripts/cites.lean`).

## Always ship

Every readable input yields an artifact. A loss is repaired where it occurs, marked in the
artifact where content is absent, and reported once. Only unreadable input, a missing or cyclic
\input, no usable font, an unwritable output or the document's own failed \assert stops the
writer; the exit status is a separate policy (--werror, CI), never whether the artifact exists
(`testdata/scoreboard/external.tsv`, `machineLossChecks`; owed (U37): `DiagCode.error_iff_fatal`).

## The standard is the specification

Warts are not: meaning comes from the documented standards (LaTeX's manuals and sources, e-TeX,
CommonMark and GFM, OpenType MATH, MathML Core, HTML, CSS, PDF 2.0, WCAG 2.2), never from parameter
resets and discards, recovery quirks, once-only package loads or single-pass limits. A visible
departure names the axis it improves (legibility, accessibility, content fidelity) and the check
holding it, as code coloured by its token's role, never lualatex's per-type colours, does
(`codeRoleChecks`); lualatex parity and rhythm are tiers, not ceilings (`compatIndexChecks`,
`testdata/scoreboard/parity.tsv`, `testdata/scoreboard/rhythm.tsv`).

## Evident intent wins

At an ambiguity, take the standard's reading; where it is silent, the reading that keeps every
character written and the structure evidently meant, one rule per ambiguity beside its site, with a
witness. Never glue words, print configuration as ink, or refuse a construct the standard defines
unless a declared safety policy (raw HTML) refuses it (`scripts/commonmark.lean`, its strict
refusals still certified, their removal owed (U14); owed (U38): `elabUnknownCtrl_boundary_exact`).

## Declarations win

Taste is the default: the engine's opinions apply only where the document is silent. A declaration
is honoured even where LaTeX's own code resets it, with a note that LaTeX differs; a declared
spelling ships a different page from the document without it or is named as a loss, never translated
onto a token nothing reads (`pictureKeyGateChecks`; `paramSiteChecks`, whose rows still discard what
LaTeX resets, owed (U55)); a declared colour ships exactly, the engine solving legibility only for
colours it derives (`DeclaredColors.checks`).

## Designed defaults

Every class declares a coherent default independent of what the host ranks first: a superfamily
(text, sans, mono, math) chosen as data and resolved by design size, a fixed-pitch mono, literal
text never hyphenated or smartened, code that wraps on paper, images that fit the measure, ragged
slides (`testdata/scoreboard/typeset.tsv`, `monoCompanion_contract`; owed (U35): `slotFill_mem`).

## One fact in one IR value

A fact both artifacts honour (faces, numbering, anchors, alignment, language, title, spacing) is
one typed IR value with one resolving site, stated on the IR first; each backend's version is a
projection corollary, never re-derived or left to a platform (`footBand_projects`,
`backend_gaps_agree`, `html_fonts_cover_pdf`, `table_length_agree`; owed (U09):
`heading_family_agree`; owed (U11): `frameNumbers_keepFor_gapless`; owed (U41): `Ir.title_agree`).

## Typed boundaries

Values cross module boundaries as typed data with spans. Nothing crosses as source text the
receiver re-lexes, a control-word name it decodes or a string it sniffs; a closed vocabulary is
an inductive, and strings are only for names the author chose (`Md.altSource`,
`Md.desugar_vocabulary_mem`, `escapeText_no_lt`; owed (U51): `toName_unforgeable`).

## One mechanism per concept

Generic structure, specific semantics: one traversal per tree type, with identity, fusion and
census laws proved once; one command and environment registry with argument signatures; one
key=value reader; one counter model; one cache protocol. A predicate projects the registry,
never a hand-kept mirror (`Ir.mapInlines_text`, `Ir.mapBlocks_text`; owed (U92); owed (U20):
`KeyVal.parse_unbraced_comma_exact`).

## A canvas fits and a flow breaks

A frame is a fixed stage: overflow is absorbed by declared shrink, then a bounded tolerance, and
only beyond that does the frame continue, with a diagnostic. A flow paginates with keeps (headings,
rows, widows and clubs), and floats defer instead of closing the page. No ink leaves the medium: on
paper code wraps and wide boxes fit or wrap (`frameFit_between`, `print_lifts_stage_bounds_covers`,
`printLiftChecks`, `scripts/html-oracle.lean`; owed (U05)).

## One loss in one line

A diagnostic reports a loss in an artifact that ships, each wording once with its site count, a
source excerpt and help spelled in the document's own surface; a site's particulars are its detail,
never its words, and its header names a construct the author wrote or nothing (`repeatFoldChecks`,
`dvLint`, `DiagCode.namesPlace`). Severity follows what the reader loses, never the roadmap or the
emitter; standard behaviour is never a warning; a run ends with a total line
(`Diag.foldRepeats_visible_inj`, `Diag.tallySites_sum_exact`, `foldChecks`, `diagVoiceChecks`; owed
(U33): `view_carriers_card`). A diagnostic stays typed until Ui.diag renders it
(`diagnosticOutputBypasses`); a report reads porcelain JSON, never the human header (review).

## Theorems state guarantees

A theorem earns its place by stating an invariant an algorithm could break, over the
implementation's own constants, indexed in `THEOREMS.md` by its guarantee; restatements, single
samples and vacuous totality do not count. Proofs live in proof modules off the binary's
critical path (`scripts/cites.lean`, `buildGraphChecks`; owed (U71); owed (U28)).

## Linear by construction

Every per-element step is amortized O(1); none does whole-structure work. A value read from an
accumulator is a strict data dependency of the call updating it, never a let the compiler may float
past the call, nor read in the record update growing it. Growth is measured, never inferred: a gated
row of n against 4n (`quadraticPrepend`, `scripts/bench.lean`, `scripts/doccost.lean`; owed (U24)).

## Whole answers under complete keys

An external or derived answer is cached whole, keyed by all it depends on: bytes, recipe, tool
identity, font environment, the engine's own implementation (owed (U68): `record?_some_exact`).
Refusals are cached, an attempt with no evidence the tool ran is not, and a warm slot answers as the
fresh attempt did (`refusal_replays_exact`, `inconclusive_retried_exact`, `replay_record_exact`,
`versionStep_changed_exact`); a warm replay starts no tool (owed (U25)), and a run ships each
resource once (owed (U03): `shipFaces_nodup`).

## Rules are checks

Every rule here and in `AGENTS.md` names what holds it, owed until it lands or review's; `docFaults`
holds each name to one non-type declaration or a path, not that it states the rule (owed (U71)).
Checks read the compiled program or the shipped artifact, never the spelling of source lines, the
hook's line scans owed (U90); gates come from one table (owed (U29): `scripts/Gates.lean`); history
lives in git and in the docstrings of the checks it motivated, never a dated rule (`datedLines`).

## Decisions owed

The user owns these; until answered, the unit named builds the default given (review).

- Discarded list parameters are honoured with a note (U55); an unknown class takes the article
  model with a warning (U37); an undated build is a named loss (U76) (review).
- Faces: Latin Modern for LaTeX classes and Libertinus for markdown (U35); native article takes
  LaTeX's indent (U08); markdown smart typography on and definition lists off (U58), attributes
  and citations as pandoc where GFM is silent (U109); css = bulma becomes a neutral container
  class with bulma a deprecated alias for one cycle (U62) (review).
- Keep or delete the theme sketch `testdata/corpus/theme-modern.tex`: it stays (review).
