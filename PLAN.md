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
link annotations, document metadata, images (`\includegraphics`, `figure`,
beamer's `\logo`; PNG including alpha, JPEG), formal tables (booktabs by
construction: three sourced rule weights, padding that belongs to the
rules, no vertical lines) with captioned floats whose gaps are held to the
vertical rhythm by theorem, and layout assertions that
fail the build. HTML5: a typed tree with a certified escaper, semantic
markup, tokens
as CSS custom properties, `\output{ css = bulma }` interop, one
self-contained file.
A document written for lualatex compiles as written: LaTeX idioms translate
to the native declarations, unknown constructs degrade to their content with
a warning, and `-v` lists every translation with its shorter spelling.
Measured by `scripts/bench.lean` (2026-09-20, medians of 5): 1 KB in 91 ms
against lualatex's 674 ms; a generated 129 KB / 30 pages in 339 ms against
1786 ms, with paragraphs broken in parallel.

**Where it is going.** This plan now covers one engine with **two surfaces**
(tex primary, markdown as sugar) and **two backends** (PDF and HTML,
including slides).

**Immediately next.** M5's deck HTML pages by scroll-snap on a horizontal
row, steps uncover in place, and the slides class ships one constant
keyboard/uncover script (`deckScript`, the 2026-09-21 entry: a closed
literal, class-gated, the deck degrading to the pure-CSS pager without
it); `--emit reveal` died with `--emit` — the document declares what to
build (`\output{ formats = … }`).
What remains of the controller ask is the speaker view alone
(notes/timer/next-slide), a user decision behind a named `\output` key and
a design discussion, not a default; remote stepping and auto-advance are
likewise script-only and stay asks. The frame furniture landed 2026-09-17:
defined wrappers, `\centering`, columns, dim-not-hide overlays with the PDF
page-per-step handout, and speaker notes as a side channel.

**Open, tracked, not hidden.** No `partial` remains: an audit found ten,
seven were removed (2026-09-16 entry), the `takeArgs`/`elabInlines` knot
closed first (envLimit, then limit, then the weight of the remaining
slice; 2026-09-19), and `elabBlocks` followed (the third 2026-09-19
entry): the block knot terminates by the measure (envLimit, noteFlag,
visPars + slicePars, visWeight + sliceWeight, layer, scan) —
`elaboration_total` (Elab.lean) names the fact, the pre-commit hook keeps
the `partial` allowance at none, and the one state-carried edge (the
pendingNotes drain, refused inside a note body as E0359) is the measure's
`noteFlag` component, exactly as decided. The second measure-breaking
edge — a body `\define` inside a command expansion once reset `limit`
past the
expansion's own bound and looped a four-line document — is closed: the
arm binds at the visibility boundary (`bindCmd`), the invariant is the
theorem `bindCmd_monotone`, and with `elabBlocks` total the end-to-end
guarantee is the termination checker itself (the wall-clock regression
test stays as the integration witness). The Knuth–Plass optimality
theorem is held empirically by `scripts/kp-fuzz.lean`. Small caps are
drawn from a face's own `smcp`+`c2sc` when it carries both and synthesised
uniform otherwise (the 2026-09-18 entry), math renders its first two slices
(atoms,
spacing, scripts; then fractions, radicals, grown delimiters, big-operator
limits, and alignment grids — the second 2026-09-17 M6 entry lists what
still carries a named warning), and element styling
(section fonts, list spacing) is declarable through `\style{element}{ … }`
(`Ir.Styles.declare`; the `\style` help text in Elab.lean lists the
styleable elements).

### Owed obligations

The staging ratchet's registry (mechanism in the 2026-09-17 owed-theorems
log entry): every open proof hole under `Obligations/` carries a record
whose name must appear backticked here, so the debt never grows unnamed.
`lake env lean --run scripts/owed.lean` prints the queue with owner,
source, and blocker; the pre-commit hook enforces the ratchet. Discharging
an obligation (real proof, moved to its owner module) strikes it from this
list.

- `emission_conservation_paras` — weak public form of arch-provable I4:
  plain paragraphs ship exactly their declared ink or a diagnostic names
  the drop. The strong per-block form waits on the `Acc` split.
- `pages_partition_frames` — numbering as a partition over the page→frame
  attribution `PageOut.frame` now carries (written at `finishPage`): every
  page of a framed deck is attributed, and frame k's pages number exactly
  its overlay steps. Supersedes `pages_count_frame_steps`, whose count is
  this statement summed; the counting side is proved on the IR
  (`frameNumbers_gapless`, `frameNumbers_last_is_count`), the page side
  waits on the collect walk's `Acc` split.
- `frame_pages_footed` — numbering, per page: a page attributed to a
  countable frame carries the chrome foot (audit-numbering T2's page face,
  restated as a per-page fold over `PageOut.frame` — the attribution and
  the footer are written together at `finishPage`).
- `elab_inlines_option_run_dropped` — the W0341 arm's content claim as a
  commutation: elaboration with and without an unknown command's option
  run agree, whatever the run's text. Statable since the inline knot
  became total; blocked on the proof's elaboration budget, not the
  statement.
- `contrast_judged_complete` — the contrast judge's completeness over the
  shipped pages, `judged_pair_is_shipped`'s converse: every glyph run
  `Layout.run` ships, with its colour and the ground its resolving site
  declared onto it (`Seg.run.ground`, written where the palette epoch,
  the frame-title bar, and the standout inversion are resolved), lands in
  `Contrast.judgedPairs`. The geometric recovery is gone with refactor 2;
  what remains is the collect-walk induction behind the `Acc` split.
- `inflate_deflate_id` — the engine's inflate inverts its deflate on every
  input: the round trip the compressed PDF streams ride on, provable
  because the engine owns both halves. Blocked on the encoder's shape
  (imperative loops with no equational theory); the oracle meanwhile is
  `scripts/flate-fuzz.lean`, with a foreign inflater as second judge.
- `decodeBin_encodeBin_id` — the driver's image cache is transparent: its
  serialization inverts exactly, so a cache hit is the recomputation's
  value. Blocked on ByteArray equational coverage for the fixed-offset
  codec; the in-suite witnesses are the serialization rows in
  Tests/Backends.

### Log

Newest first. Entries are immutable; corrections are new entries.

2026-09-21 — silence is fidelity, the surface layer (accounts slice): a
construct the rewrite dispatcher consumed either has an effect or is
named — `rewriteCtrl_accounts` (Compat.lean, the `_accounts` shape's
first instance) holds it for every name and state by unfolding the
dispatcher's silence guard alone, arms opaque, so no future arm can break
it. The machinery: `St.writes`, a counter every state mutation bumps
through the one `write` door (intent, not effect: idempotent writes
count, no `BEq St`); the guard says **W0387** ("read and had no effect",
loss `.config`, `\allow`-acceptable, once per name) when an empty arm
result grew neither `diags` nor `writes`; the pre-commit hook rejects a
bare `modify`/`set` in Compat outside `say`/`write`/`account`
(`compatStateDoors`). First run of the guard over the corpus and the
reference documents surfaced and repaid: the `\RedeclareSectionCommand`/
`\setlist` silent drops (W0111 generalized, W0101 for unmapped entries),
`\clearpairofpagestyles` (implemented: clears the gathered fields),
`\urlstyle` (tt is agreement — `\url` is set mono, url.sty's default —
else W0104), `\KOMAoptions` (sepline-off is agreement, else W0101),
beamer's command-form `\column` (W0104, the environment form is the
modeled spelling), `\raggedbottom`/`\flushbottom` (configSkip, the vdist
ask), a bare `\note` in Elab (E0304), and the deliberate no-ops
(`\relax`, `\makeatletter`, …) now carry their reason as the N0100 note.
`\noindent` stays the guard's W0387 deliberately: whether a first-line
indent exists to suppress is the paragraph model's question, and the
guard's message stays true whichever way that lands. All reference
documents byte-identical (cmp against the branch base); bench flat. The
resolution layer — no unresolved `\cite`/`\ref`/image reaches a backend
unnamed — is the next slice of the same theorem.


2026-09-21 — a poster carries its title band and footer; the theme
carries the look (poster-chrome slice): the poster record gains a
headline (`ClassRecord.headline`), and a headline class draws the
`\title` family as a full-width band at the top of each face — the
gemini lineage's rule (its headline template reads the declarations
without a `\maketitle`) — title `\Huge` bold, author `\Large`, institute
`\normalsize` (the lineage's own font templates, as scale steps), in the
`frametitle` roles the deck bar already resolves at one site, aligned by
the `titlepage` style's declared token, the body's columns below.
`\logoleft`/`\logoright` are the band's two corner slots
(`Doc.logoLeft`/`logoRight`, the `\logo` machinery's shape), laid by the
furniture pass with their ink centred in the bar's recorded extent
(`PageOut.band`), decorative by role. HTML: the band is the page's own
`<header>` before `<main>`, the title its one h1, the same frametitle
tokens. The `gemini` bundle ships (beamercolorthemegemini.sty's values
onto the semantic keys; covered = 30%, the largest fraction where its
alert and example clear the 3:1 state change), `\usecolortheme{n}` reads
`beamercolortheme<n>.sty` beside the document through the `\usepackage`
splice, and `\setbeamercolor` maps the elements the engine has roles for
onto the palette — an element with no role keeps its named warning.
Image sizes now read the token environment (`0.2\paperheight`,
`0.5\colwidth` — the `\setlength` rule, eager); `\footercontent` is the
running foot; `\makebox` keeps its content and names its dropped box.
Known remainder: the private poster sets one line past its single face
(E0330) — every paragraph's first line breaks early (the fix-firstline
slice's defect) and the machine substitutes a wider default sans for the
document's absent brand face; the band itself fits with ~10 pt to spare
once either resolves.

2026-09-21 — a venue's refused redefinitions are declarations; read them
out (sty-readout slice). Rule (b) extended twice, in the maketitle
precedent's shape. The size ladder: a refused size command whose body
opens with `\@setfontsize\X<size><leading>` lands as a per-mille step of
the body in force — the venue's own normalsize, already honoured by the
Compat size idiom — on `Ir.PageSpec.sizes`, resolved by `PageSpec.scale`
(the one resolving site) and read by both backends: the PDF through
`Layout.Geom.scale` into the flatten state, the HTML through the `.size-`
rules and `::marker` declarations (`sizeLadderChecks` judges both on
shipped segments and the emitted stylesheet). The door is ordered by
construction — `Ir.setStep`/`Ir.setStepsAll` with `size_ladder_monotone`
and `size_ladder_monotone_all`; non-strict, because the NeurIPS lineage
sets `\footnotesize` = `\small`, and judged whole-first because a venue's
ladder is one declaration, not a sequence. A landed step drops its W0361
for an N0100; a disordering step keeps the built-in, named. Not read:
per-step leadings (the engine's leading is one page-level factor) and the
engine-derived default sizes (`sectionSize`, footnote mark/body, chrome —
reading the ladder there needs `heading_hierarchy` restated over any
ordered ladder, left named). Alongside: `\providecommand` of an
engine-defined name is LaTeX's no-op, kept silently (six venue shims had
each earned a W0361 'renders nothing'), and a run-in `\paragraph`
redefinition in the built-in's own font is satisfied by the built-in
run-in heading rather than refused with a stale 'not modelled'. The
reference venue paper: W0361 16 → 1 (the surviving one is `\maketitle`'s,
genuinely refused and styled), byte-identical output, as are the four
reference documents.

2026-09-21 — the graphics boundary opens by default (boundary-default):
a picture the rendered subset refuses routes whole to the boundary with
no declaration at all — the boundary tool belongs to the build
environment exactly as fonts do, and a warm cache needs no tool.
`\pictures{ tool = ... }` now *pins* a tool (a no-op for the default;
`\tikzexternalize` still spells the pin) and `tool = none` is the
declared refusal, restoring the subset's own named diagnostics — W0334
per construct, W0362's placeholder, W0301 for the set lines, W0103 for a
picture package's load — with no door warning, because the declaration
is the acceptance.

- Fulfilment stays the driver's alone. The request is a pure function of
  the document: `boundary_request_env_free` (Ir.lean) pins that
  repinning the tool field leaves `pictureRefs` untouched, the routing
  reads only the door's presence (a declaration value), and the
  executable half — the pinned and undeclared spellings elaborate to the
  identical `Doc` — runs in `boundaryChecks`. The driver runs the tool,
  serves the warm cache (with no tool at all, any cached render of the
  same content serves — the version half of the key only forces a
  re-render on upgrade), or says W0379.
- W0379's one meaning moved with the policy: no longer "no boundary tool
  declared" (Elab) but "no boundary tool available for a picture outside
  the rendered subset; a placeholder box marks each picture" — a driver
  diagnostic (`boundaryToolUnavailable`, loss `degraded`: the placeholder
  ships), fired once per run, help naming the install and the `tool =
  none` acceptance. W0378 keeps its two remaining meanings (tool ran and
  failed; converter missing). N0023 stays on every routed picture, and
  the porcelain inventory row stands.
- Two absorptions the default made load-bearing (both were tikz-boundary
  named-next items): a boundary picture's absent text alternative is
  N0023's fact, not W0376's — the trust label already reports the census
  loss and names the caption/alt fix, and the route was the engine's
  default, not a declared image (one loss, one diagnostic;
  `imagesSansAlt` excludes `picSrcPrefix`, a caption still propagates) —
  and an unsized boundary picture wider than the measure fits it exactly
  (Layout's `.img` arm: the box is the engine's to measure and place,
  the form is vector, no author size is overridden; an ordinary image
  keeps its natural size and LaTeX's honest W0005).
- `Compat.boundaryPkgs` (genealogytree, pgfplots, circuitikz — closed
  list, picture-only packages): their loads ride the boundary standalone
  (as `boundaryDecls` always carried them) instead of W0103, gated on
  the door (`Compat.boundaryRefused` reads the refusal order-free, the
  `picTool0` shape). The genealogy acceptance document now builds with 0
  warnings and N0023 once, its tree drawn by the real genealogytree with
  its `\gtrset` highlight style applied; the four reference documents
  and the poster are byte-identical.

2026-09-21 — a real deflate, image streams that compress, content-hash
caches (build-cache slice): `Flate.deflate` is a true RFC 1951 compressor
(LZ77 over a hash chain, one dynamic-Huffman block whose code sets come
from boundary package-merge in the counting formulation), and every
stream the PDF writer owns — content, ToUnicode, font files, XMP, the
object and cross-reference streams — now rides compressed when that is
smaller. An alpha PNG's decoded planes are Up-filtered and really
deflated (Predictor 15 declared on both the image and its SMask), so the
one deck whose 4575×4575 RGBA figure used to ship as 84 MB of stored
blocks writes a 2.2 MB PDF (85,340,066 → 2,226,785 bytes); the paper
drops 1,149,515 → ~643 KB, the résumé 1,617,002 → ~1,032 KB, the card
1,234,712 → ~519 KB. The round trip is the engine's own to prove —
deflate emits only symbols inflate's tables decode — and is owed as
`inflate_deflate_id` (fuzz oracle `scripts/flate-fuzz.lean`, every stream
cross-checked against a foreign inflater). Two content-hash caches join
the boundary cache's pattern under `~/.cache/leantex`: `imgs/` holds the
decoded-and-re-encoded image object (`Image.encodeBin`, transparency owed
as `decodeBin_encodeBin_id`), `flate/` the deflated font files
(`FontSet.zdata`, filled by the driver; the writer only picks the smaller
spelling). Warm rebuilds: the deck 4010 → ~200 ms, the paper ~151 →
~220 ms (the residual is the per-build deflate of content and metadata
streams, ~60 ms — measured, kept for the 44 % size win). The reference
PDFs are deliberately not byte-identical; equivalence is checked by
`pdftotext`, `pdfimages -list`, and pixel-identical 100 dpi rasters.

2026-09-21 — ragged looseness is priced, never free (fix-firstline): body
ragged setting (`raggedItems`) now gives interword glue finite stretch —
`displayItems`' six-times-its-width pricing, one scale for both ragged
tiers — instead of fil. Fil hides all looseness from badness (TeXbook
ch. 14), so every minimal-line-count break sequence tied and the DP's
tie-break packed lines from the paragraph's end, dumping the slack on the
first line: on a beamerposter every paragraph's first line broke at
roughly half its column. Plain TeX prices `\raggedright` finitely for
exactly this reason (TeXbook App. B: `\rightskip 0pt plus2em`); LaTeX's
`1fil` version is the wart ragged2e documents and fixes. The parfill and
an author's `\hfill` keep their fil (a last line is free; a declared fill
means the margin), and ragged lines still set unjustified, so the stretch
prices the break and never widens a rendered space. The oracle's empty
last line — a break at the terminator glue right before the forced pen,
which `kp`'s `a ≤ j` gate refuses — is now refused by `seqCost` in
kp-fuzz and Tests/Layout.lean too; the ragged-plus-protrusion shape the
finite glue newly exposes holds at 1000 fuzz cases.

2026-09-21 — weight is an axis, not a flag (font-weights slice): every
font key is now `(slot, weight, italic)`, weight the CSS/OpenType number
of an NFSS series (`Ir.Weight`, the nine LaTeX News 31 values; `m` = 400,
`sl` = 350 — the two placements no single registry settles, said so in
the docstring; `Weight.ofCss_css_id` is the bijection statement).
`\fontseries` and fontspec's `FontFace={series}{shape}{font}` are native:
the weight half honoured through the `@series:` marker and the
`slot.<series>[.italic]` declaration keys, the width half warned by name.
Resolution extends W0366's nearest-weight rule to the whole axis
(`FontDb.resolveWeight`; `pickWeighted_total` and `FontSet.index_total`
carry totality), the driver resolves exactly the keys a document's styled
ancestry can ask for (`Layout.docWeightKeys`, the docScalars precompute
shape), and both backends read one projection (`Ir.Style.weight?`,
`weight_agree`) — HTML emits the numeric weight per run and one
`@font-face` per face. Two defects fell out: a 0-ary definition's
trailing declaration styled the empty rest of its own body instead of
the rest of the enclosing group (`\newcommand{\x}{\bfseries}` produced
an empty `<strong>`), and a sans-only document's text face was font-0
fall-through rather than the sans declaration — both named, tested, and
fixed. The card embeds Inter-Medium and Inter-Light again, exactly
lualatex's set; deck, resume, paper byte-identical.

2026-09-21 — appendix and cleveref are native (pkg-numbering, audit
slices 3 and 4): `{appendices}` scopes the `\appendix` mark and restores
the counters (appendix.sty v1.2c's save/restore), and the cleveref family
resolves through the one label table.

- The table carries the kind of what a label names (`Ir.RefBinding` over
  `Ir.RefKind`: heading, equation, figure, table — a subfloat keeps its
  parent's kind), `Inline.ref`'s eqref Bool became `Ir.RefForm`, and
  `Ir.refText` is the one rendering site: kind name and number joined by
  cleveref's no-break space, equation numbers parenthesised in every cref
  form. `\crefrange` desugars in Compat to the pair the resolver reads.
- The names are locale data: `CrefName` fields on `Locale` for the four
  kinds plus the range conjunction, generated from cleveref.sty v0.21.4's
  language blocks (cited in the generator), `crefNameOf_covers` pinning
  every assigned kind named in every shipped record, complete by
  `RefKind.all_complete`.
- W0380 is the named refusal for the one kindless binding: a bare
  `\refstepcounter` numbers no node, so a `\cref` to its label sets the
  plain number, named. The appendix numbering contract is stated over the
  assignment function (`defaultSecNum_appendix_exact`/`_inj`).
- `{subequations}` (audit candidate 9) stays refused (amsmath.txt pins
  W0302); its numbering-pass plan is in the slice's RESULT.

2026-09-21 — the deck's logo is frame furniture in HTML too (html-logo):
W0007's "paged-media furniture" claim was wrong for a deck, where a frame
*is* a page and the logo is the frame's furniture exactly as the footer
is.

- One resolving site: `Ir.logoInForce` is the fold both backends read —
  the PDF's furniture pass keys the `\logo` spans by page index, the HTML
  deck walk keys the same declarations by body position, and
  `logo_frames_agree` states the invariance under the rekeying (the
  order-preserving map between the two key sequences), so neither backend
  carries a second interpretation. The census half is executable
  (`deckLogoChecks`): the frames whose section carries the `.slide-logo`
  strip are exactly the pages whose `Layout.Out` carries the furniture
  line.
- The alignment is declared, not hard-coded — the furniture-rule debt the
  AGENTS table names: `logo` is a styleable element whose `align` both
  backends read through `Ir.logoAlign` (the PDF as the line's x, HTML as
  the strip's flex distribution), defaulting to `right` — beamer's own
  lower-right corner (beamerouterthemedefault's `sidebar right` template).
  `\style{...}{align=right}` becomes sayable alongside left/center.
- The strip is decorative furniture (WCAG 2.2 SC 1.1.1, pure decoration):
  images ship `alt=""`, the carrier leaves the accessibility tree, and
  the no-alt census (`imagesSansAlt`) counts logo sources as decorative
  rather than missing — W0376 no longer flags a deck's logo image.
- In flow and face classes the logo stays paged-media furniture and
  W0007 keeps firing with its old words, now true everywhere it appears;
  the deck's W0007 is gone. In print the logo rides its handout card
  (furniture on paper too). Reference PDFs and the webpage fixture
  byte-identical; the deck's page census and stylesheet theorems restated
  over the extended rule set.

2026-09-21 — pseudocode as a value (pkg-algorithm): algorithm2e and
algorithmicx parse onto one IR node.

- `Block.algorithm` — lines of rich text (`AlgLine`: depth, closed
  `AlgKind`, content, comment) inside the float machinery via
  `FloatKind.algorithm`; the caption word joins the locale record for
  en/fr/de, cited from algorithm2e's own `\algorithmcfname` options.
  Keywords are generated text from the locale keyword table
  (`Ir.algWords`, algorithm2e's `\SetKw…` defaults), rendered at the one
  site both backends read (`AlgLine.rendered`); the census counts
  content and comment only (`algorithm_text`). Every walk carries the
  explicit arm per the obligation table; dim, map, number, recolor keep
  their `_text` theorems through the new arms.
- Two surfaces, one value: algorithm2e's grouped grammar (`\;`
  terminator, `\For{c}{b}` block forms expanded on a bounded work
  stack) and algorithmicx's flat `\For`…`\EndFor` both parse to the
  same lines. `\SetKw`/`\SetKwInOut`/`\SetKwFunction`/`\SetKwData` are
  document-global (preamble PDecl arms — compose-fuzz green) and
  substitute inside content; display settings outside the model are
  N0102 by name; a construct outside the subset is **W0383**
  (`.pending`), its content kept as plain lines.
- PDF: each line a display-type paragraph, depth × the `algindent`
  token (algorithm2e's `\SetInd{0.5em}{1em}` + 0.4 pt ≈ 1.5 em), line
  numbers as markers in the muted role held to one column
  (`ParaJob.markerIndent`). HTML: nested `<ol>`s built depth-driven,
  one CSS counter for the numbers — declarative, no script. The
  HTML-vs-PDF line-census agreement is pinned by an executable oracle
  (`algorithmBackendChecks`); the theorem form over a factored nesting
  builder with a typed-tree text census is the named remainder.
  Vertical block lines (`\SetAlgoLined`) are not drawn: named N0102
  until layout grows a vertical-rule op.

2026-09-21 — the graphics boundary is live (tikz-boundary): heavy TikZ
runs in real TeX at the edge; the engine places a measured vector box.

- The asset half first, native: `\includegraphics{x.pdf}` embeds page 1
  as a form XObject through a new pure reader (`Core/PdfRead.lean`) —
  classic xref tables *and* xref/object streams, page-1 box
  (CropBox-else-MediaBox, pdfTeX's inclusion rule), content streams
  decoded and concatenated, and the `/Resources` object graph copied
  whole, font programs verbatim, renumbered through typed holes.
  `resources_closed` (`_covers`, carried by the reader's subtype: no
  returned form dangles a reference) and `form_bbox_exact` (`_exact`: the
  normalizing `/Matrix` composed with the image path's `cm` lands the box
  corners on the requested rectangle, exactly in the rationals both
  render from). Totality over arbitrary bytes rides `scripts/img-fuzz.lean`
  (truncations, mutants, blobs; the fixture is the engine's own output,
  so the reader is tested against the writer).
- The boundary itself: one declared door — `\pictures{ tool = lualatex }`,
  or TikZ's `\tikzexternalize`, which sets the same declaration — and a
  tikzpicture the rendered subset refuses runs whole under the pinned
  tool as `\documentclass{standalone}` plus the preamble's closed list
  (non-native `\usepackage` lines, `\usetikzlibrary`, `\tikzset`,
  `\gtrset`, `\pgfplotsset`, `\definecolor`, the declared body family).
  The request rides the IR (`Ir.pictureRefs`, the `bibRefs` shape:
  content hash of the wrapped source — deterministic by purity); the
  driver fulfils it under a wall-clock budget and caches the PDF beside
  the font cache, keyed by hash and tool version, so a warm cache needs
  no TeX installed. The tool name is drawn from the engine's allowlist,
  never the document's own spelling: the driver executes it. Inventory
  per picture in `-v` and the porcelain phases: tool, version, hash,
  size. HTML converts the same cached PDF once, by pinned
  `pdftocairo -svg`, into `<stem>.assets/<hash>.svg` (the font-shipping
  shape). Codes: N0023 (drawn at the boundary; its text is not in the
  census — the trust label as a note), W0378 (tool failed; placeholder,
  the tool's last words in the help), W0379 (refused picture, door
  closed; the help names the declaration). The genealogy acceptance
  document builds with its tree drawn by the real genealogytree, 0
  errors, N0023 once.
- Absorption stays the recorded later option: audit-tree sized a native
  tree DSL (semantic `Diagram` value, contour-packed certified layout,
  census over node texts) at ≈1.4k LOC for genealogytree alone — the
  boundary covers pgfplots, circuitikz, and every picture outside the
  subset for ~350 lines of driver and routing, so isolation lands first
  and absorption is per-package, when it pays (trust is monotone:
  absorbing swaps the tool for a native implementation behind the same
  request type, and documents never notice).

2026-09-21 — margin line numbers land as a declared page feature
(pkg-lineno, audit-packages candidate 2, the submission requirement).
`\page{ linenumbers = on }` numbers every counted body line consecutively
across pages from 1; `modulo = n` prints only multiples while counting
every line. Compat maps `\usepackage{lineno}` + `\linenumbers`,
`\nolinenumbers`, `\runninglinenumbers`, and `\modulolinenumbers[n]` onto
the keys; the `\linenomath` pair is accepted inert and the pagewise
option family refused named (W0101) — continuous numbering is lineno's
default and the one mode shipped. Which lines count is sourced from the
lineno manual (line numbers on paragraphs, attached by the output
routine): galley paragraph lines including headings, list items, and
display math — numbered like every line here, where lineno's default
linenomath does not; the recorded divergence — never a float's caption
or body, footnotes, rule ink, picture labels, or furniture. The mark is
`Layout.LineOut.counted` (set at `placeLine`, off inside floats through
the reader); the numbers are furniture laid by the furniture pass at each
counted line's own baseline, muted at the footnotesize step, right-aligned
left of the measure (a declared `furnituregap` exact, the undeclared
column hanging from half the margin, `furnEdge`'s convention turned
sideways). The shipped-page contract is a census row over `Layout.Out`
(`linenoCensus`/`linenoModuloCensus`, two golden fixtures). HTML emits
nothing: line numbers are a paged-media fact and the twin has no fixed
lines — recorded on `Ir.PageSpec.linenumbers` and in
tests/compat-index/lineno.txt; no declarative per-line CSS construct
exists to argue for.

2026-09-21 — the deck is a horizontal row again, → is next, and the
slides class ships one constant script (slides-floor). Supersedes the
slides-vertical entry (2026-09-20, the axis and its push construction)
and this entry's own predecessors' "no controller"/"script being off the
table" lines; the deck-css-typed rule/theorem architecture stands and is
what the change was expressed in.

- The user, in their words: "wtf now you flipped to arrow down (vertical)
  instead of horizontal. i preferred arrow right to go next. also
  '1 / 2 ›' this is dumb and visually bad. i prefer no transparency
  instead!" — and, offered a pure-CSS floor or a small constant script
  when "home and end are not moving me to beginning and end rn", chose
  the script ("alright i guess i prefer you stick to the best practices
  with chromium"). The reasoning that lets the no-script rule bend: the
  script is a constant, so every cost the rule guards against —
  document data flowing into markup, an escaping obligation, a rule
  that holds only approximately — is discharged by construction; and
  the deck without it is still the whole pure-CSS pager, so the floor
  is not hostage to scripting.
- The axis: frames are `100vw` pages of a horizontal row
  (`x mandatory` on the root), the scroll itself the motion — the push
  animation, its `-100dvh` cancellation and the travel extension die
  with the axis; the title band holds still because every frame's band
  sits at the same y. The root clips y so no scrollbar can steal width
  from `100vw`: a snap area wider than the scrollport never lands
  flush, the invariant behind the old row's "several taps, partial
  slides" defect. Probed (Chromium 1280×720, the reference deck): every
  bound key moves exactly 1280 px — ArrowRight/Down, PageDown, Space
  forward; ArrowLeft/Up, PageUp, Shift+Space back; End 0→67 840
  (53 × 1280), Home back to 0; on the 4-step frame each press is one
  1280 px snap with the title band at x = 0 on all four snaps
  (the old last-snap ~56 px shift has no expression: the stage is
  sticky within its own track and no snap area shares an offset), and
  a mid-glide shot shows the two frames abutting exactly — sections at
  −659 and 621, both 1280 wide, no overlap (nothing transforms; the
  seam is the boundary of two opaque surfaces).
- The step control (`‹ k / N ›`) and the `:has(:target)` fallback are
  deleted, `fallback_uncovers_every_step` with them — a theorem about a
  deleted surface is not owed. Deep-link ids stay on the spacers.
- One snap door: every snap point carries `data-snap` at emission and
  `[data-snap]` is the deck's only snap-align rule
  (`snap_pages_partition_frames` restates over it: timeline path one
  snap per step plus one per stepless frame; floor one per frame). The
  script queries the same selector — the stylesheet and the script
  cannot name different snap points.
- The script (`deckScript`, ≈50 lines, emitted as a raw-text node of
  the typed tree under the `</script` guard): keys, `scrollIntoView`
  honouring reduced motion, and the Firefox floor's uncover — where
  `view()` timelines are missing it writes `data-snapped="k"` on the
  stepped track and numeric rules uncover steps 2..k
  (`snapped_uncovers_every_step`). Covered-on-the-floor exists only
  under `html[data-deck-script]`, the marker the script sets at
  startup: `floor_covered_script_gated` states that no floor rule dims
  without it — nothing may be dimmed that nothing can restore. The
  theorems that make the constant auditable: `deck_script_constant`
  (the literal is pinned; an interpolation entering the definition
  stops the build) and `deck_script_gated` (slides class only).
  Probed with the `@supports` condition renamed in a copy: spacers
  hidden, → uncovers step 2 in place (opacity 0.31 → 1.0, scroll
  unmoved), Home/End page the floor; with scripting off, every step
  computes opacity 1 and no marker is set — full colour, no control.
- Kept from the user's own commits (5817fcd, eafe49e, reachable at
  `wt/slides-floor@{1..2}`): `background: var(--surface)` on every
  section as an ungated rule (opaque on every path), the explicit
  `ltx-uncover` `to { opacity: 100%; transform: none }` endpoint,
  reduced-motion and print at full step colour, and the corrected
  Firefox support note (release unsupported; preview builds only;
  ESR 140 reports the feature false) in the `Feature` table. Not
  ported: the 101vw push and its `--muted` leading edge — the push
  died with the axis, and the seam the edge marked is now the honest
  boundary between two static frames.
- Verified: `lake build --wfail`, `lake test`, Obligations, precommit
  `--selftest`, `owed --check` green after rebase onto 589a55a; four
  reference PDFs and the webpage fixture HTML byte-identical, main's
  binary vs this branch's, on identical inputs (deck 62 pages /
  9 warnings / 0 errors); bench themed 81/85 ms pdf/html, paper
  152/147 (medians of 5, same session) — at baseline. One honest gap:
  the width-steal mechanism itself could not be re-produced on this
  host (headless Chromium uses overlay scrollbars, which steal no
  width), so `overflow-y: clip` is defence for the classic-scrollbar
  platforms the suspect names, held by the geometry probe, not by a
  reproduced failure.

2026-09-20 — the deck stylesheet is typed rules; the browser floors are
theorems (deck-css-typed). The user's charge: theorems that the deck
works in both Firefox and Chromium with minimal changes.

- The engine cannot prove what a browser does; it proves what it emits,
  and emits so that correctness does not depend on which features a
  browser has. Each deck rule is a `DeckRule` value (selector chunks,
  declarations, feature gate, media partition); `Feature` carries each
  gate's `@supports` test, its sourced support note (caniuse/MDN, read
  2026-09-20), and its dependency table; one grouping emitter
  (`emitDeckRules`) realizes the `@supports` blocks, the reduced-motion
  partition after the blocks it reverts, and the print partition.
- The guarantees, quantified over the rule set so a new rule is in the
  contract the moment it is written: `deck_css_partition` (a rule using
  a feature-dependent property or selector fragment sits in that
  feature's supported block and nowhere else — a browser lacking F
  never parses a rule that needs it, never loses one that does not);
  `floor_is_baseline` (every property in the base, the `not` blocks,
  the reduce and print partitions is in a declared, sourced Baseline
  list — the "works in Firefox" statement in the only form the engine
  can make it); `floor_hides_nothing` with `floor_opacity_mem` (no
  partition hides content; every opacity a rule sets is full or the
  design's covered fraction); `guards_by_construction` (every motion
  rule has a reduce counterpart in the same emitted set — subsumes the
  three per-definition guard lemmas, now deleted);
  `fallback_uncovers_every_step` (step n's uncover rule exists at
  target n, the uncover set being the selector's own data);
  `snap_pages_partition_frames` (both paths' snap carriers by
  membership in the right gate; counts via `track_snaps_exact`);
  `deck_text_path_free` (no rule ships text, so the census cannot
  depend on the path a browser takes).
- Minimal changes by construction: adding or dropping a feature
  dependency is one `requires` field; adding a browser fact is one
  `Feature` row; nothing else moves. What stays measured, never proved:
  Chromium's directional snapping, Firefox's lack of timelines, the
  page-scroll fraction — the dated Playwright probes of the
  vertical-deck entry are the oracle.
- Grouping is the only stylesheet change: the `:has()` floor rules move
  into a `selector(:has(a))` block (behaviour-neutral — an engine
  without `:has()` dropped the unparseable selectors before, and in a
  timeline engine the target rules are inert, animation declarations
  overriding normal ones), and the guards merge into one reduce block.
  A test pins the emitted declaration multiset to the typed set.
- Verified: gates green; three reference PDFs byte-identical vs main's
  binary; the reference deck's before/after stylesheets carry equal
  declaration and selector multisets (379 = 379); Playwright renders of
  frame 1 and a stepped frame's snaps 1–2 byte-identical to main's;
  bench themed 83/85 ms pdf/html, paper 154/153 (medians of 5) — at
  baseline.

2026-09-20 — the deck stacks vertically; the motion stays horizontal
(slides-vertical). Supersedes the horizontal row's axis and the entry
fade; the step-uncover construction rotates with it.

- The decision: without script a key does what the browser's scroller
  does with it, so the axis of the scroll space decides the keyboard. A
  vertical root scroller natively pages on Space, Shift+Space,
  PageDown/PageUp, ArrowDown/ArrowUp, Home/End, the wheel, swipe, and
  presenter remotes; the horizontal row answered only ArrowLeft/Right,
  and no declaration adds the rest to an x-scroller. The deck's scroll
  space is now `y mandatory` on the root — one snap page per frame and
  per overlay step — and Scroll Snap 1 §6.2's "a scroll with only an
  intended direction must always ignore the starting snap position"
  is the sentence that retires the several-presses defect (probed: one
  ArrowDown / PageDown / Space each moved exactly one 720 px page on
  the dev Chromium, plain and stepped frames alike).
- The motion: every frame rides a `.slide-track` in the stack as a
  sticky stage (`top: 0`); the track's `::after` extends its sticky
  travel exactly one page past its last snap, so the outgoing frame
  stays pinned through the whole transition. The incoming frame scrubs
  `ltx-push` — `translate(100vw, -100dvh) → none` — over its own
  `view(y)` entry range: the `-100dvh` leg cancels the scroll's
  vertical travel exactly (ranges ignore transforms and account for
  positioning, Scroll-driven Animations 1 §3.1, so the animation
  cannot feed its own timeline), leaving pure horizontal arrival —
  Keynote's push; the title band's y never moves (probed mid-glide: at
  scroll 557/720 the computed transform was `translate(289.8, -163)`,
  the exact cancellation). Frames pin their height to the viewport in
  this path; spill content stays reachable through the frame's own
  scrollbar, the visible control.
- Two invariants, by construction: snap areas live on static `.snap`
  spacers, never the sticky stage — a snap area is the *transformed*
  border box at its offset position (Scroll Snap 1 §5.1), so a pinned
  stage would define a snap position at every offset and paging would
  never correct. And the previous frame cannot paint over the next:
  sections are positioned boxes painted in tree order — the old
  stage-over-neighbour defect has no expression in this layout. Frame
  anchors move onto the track (a pinned section reads as "in view", so
  a backward fragment jump onto it would never scroll).
- The uncover rotates: `view-timeline: --frame y`; the track's border
  box is one viewport taller than its N pages, so `contain` spans N
  viewports and step n's range becomes `(n−2)/N → (n−1)/N` (probed:
  step-2 opacity 0.31 at snap 1, 1.0 at snap 2).
- The floor grows navigation: without `view()` timelines the deck is
  the plain vertical snap stack (all keys work, no motion) and covered
  steps stay covered — uncovered by the new always-visible `‹ k / N ›`
  control (`nav.step-nav`, one cluster per step over `:has(:target)`,
  numeric rules per step, no `calc()`; `:target` matches a hidden
  spacer's fragment, so the uncover fires in place without scrolling;
  keyboardable by Tab + Enter). Under the timeline path the control's
  links also scroll; its shown number follows the fragment, not the
  scroll — the declarative remainder. Reduced motion reverts the whole
  geometry to the static stack at full colour (`deckPushCss_guarded`,
  `deckStepCss_guarded`); print is the unchanged handout and hides the
  control.
- Verified: gates green; four reference PDFs and the webpage fixture
  HTML byte-identical against main's binary; the reference deck 62
  pages / 10 warnings / 0 errors; bench themed 80/82 ms pdf/html,
  paper 151/145 (medians of 5, same session) — at the previous
  session's numbers.

2026-09-20 — theorems layered: IR facts first, artifact theorems as
projections (impl-layers).

- The layer map (theorem-layers' census at 06b4253: 645 theorems and
  `Conserves` instances): L0 kernel arithmetic 95 (Dim, Oklab, Math,
  Image, ListMark, Picture, fonts — format-free); L1 the document's
  meaning 252 (Ir 177, Theme 41, Contrast 16, BibStyle 10, Diag 5,
  LocaleData 3); L1-mech surface→IR 124 (Elab 119, Compat 4, Parse 1);
  L2 artifact 174 (PDF: Layout 81 + Pdf 3; HTML: HtmlDoc 33 + Html 13 +
  MathMl 16; Markdown 27; Tests/Backends 1). The rule this slice adds to
  AGENTS § Conventions: a fact both artifacts must honour is one theorem
  on the IR, each backend a projection corollary; a resisting proof is a
  factorization finding, staged in `Obligations/` as the refactor it
  names.
- Landed under the rule: `Ir.VAlign.shares` (vdist table once,
  `VDist.of`/`vdistShares` rfl projections, the deckStructureChecks pin
  now `vdist_shares_agree`); `pdf_lang_declared` over `Pdf.catalogDict`
  (the twin of `emit_lang_declared`); W0377 + `links_judged_complete`
  (empty link text judged, `alt_judged_complete`'s shape);
  `track_snaps_exact` (the HTML step count over `Ir.maxStepBlocks`);
  `Ir.headingRank` beside the outline walk (MarkdownDoc's import of Html
  gone). Refactors 1–2: `PageOut.frame` written at `finishPage` (the
  page-counting obligations restate as `pages_partition_frames` and a
  per-page `frame_pages_footed`) and a declared `ground` on `Seg.run`
  written at the resolving sites (`contrast_judged_complete` is field
  equality now — `judged_pair_is_shipped`'s converse). References
  byte-identical throughout; bench flat.
- The covered-shade divergence, recorded as an honest non-theorem: the
  PDF dims pending overlay content by mixing in the engine's own Oklab
  (`Design.cover`, `labMix`), the HTML deck by emitting
  `color-mix(in oklab, …)` — the browser's mix, not the engine's — and
  the uncover animation composites opacity in sRGB besides. One declared
  fraction, three blends: the shared fact is the declaration, and no
  cross-backend equality is true to state. A backend theorem here would
  name a fact of the artifact, which is the honest layer for it.

2026-09-20 — a role names a hue; the contract chooses its lightness on
each ground (brand-palette).

- The rule (Material 3 tonal palettes, Radix light/dark scales, Tailwind
  v4 OKLCH ladders; WCAG 2.2 SC 1.4.3/1.4.11 the judged requirement): a
  palette role declares hue and chroma; where a (role, ground) pair a
  document ships fails its ratio, `Contrast.realize` binary-searches the
  Oklab lightness axis at the declared (a, b) — nearest passing lightness,
  chroma reduced toward neutral only when the axis never reaches — and
  N0022 (`Loss.info`) reports the realization. Unreachable pairs, inline
  (anonymous) colours, defaulted inks (W0330), and DeviceCMYK declarations
  keep their warnings exactly as before: never silent, never repainted in
  a model the author did not declare.
- Theorems: `realize_meets_contract` (postcondition by construction — the
  return is guarded by the judged quantity, no search argument is
  load-bearing), `realize_id_of_passing` (`_id`: a passing document's
  artifact cannot move), `realized_builtin_contract` (kernel, quantified
  over `Theme.builtin`'s own pairs), `recolorRoles_text` (`Conserves`:
  realization recolours, never rewrites content). The cross-ground census
  (content colours on each bundle's bar and standout ground) and the
  backend agreement (the PDF's recoloured run and the HTML's scoped
  custom property both carry the one solver's answer) are executable
  oracles in Tests.lean (`realizedChecks`), not theorems: the search is
  kernel-expensive off the identity path.
- The application site is `Contrast.realizeDoc` in `Elab.runRaws`: palette
  entries rewrite where the pair is the palette's own (frame-title bar,
  titled bars, standout, fg and content colours on their page, per
  epoch), role-named runs rewrite where a use sits on a local ground
  (`Ir.recolorRoles`, palette threading in flow scope); HTML additionally
  scopes `--alert`/`--example` per ground since its runs stay live
  `var()` references. moloch's `#A55A13` alert is now an instance of the
  rule rather than a hand derivation.
- Known remainder: grounds are read at judge time, so a realized `fg`
  that also grounds a defaulted standout inversion is realized against
  the pre-realization ground (rare: needs a failing declared fg under a
  standout frame with no standout keys); HTML scoped realization covers
  the content colours (`alert`, `example`) — an arbitrary role inside a
  frame title keeps its `:root` value in HTML while the PDF realizes it.

2026-09-20 — the harness reads what the wave landed: shared helpers, one
measure per fact, gates that police the new invariants.

- Tests: the eight local `hasStr`/`dvE`/line-collection copies now bind
  Support's helpers (`allLines` is new — `bodyLines` without the furniture
  filter); `main`'s regrown 21-call tail folded into the suite dispatchers
  (two new leaves, theme and font-face — the latter must not hide behind
  the layout suite's font gate); the mm/inch agreement and the integral
  `toPtString` case are compile-time examples beside `Dim` (the fractional
  case stays a runtime check: its `String.Slice` ops reduce for neither
  `decide`, `decide +kernel`, nor `rfl`).
- One resolving site per fact: `Bib.sourceName` for the `.bib` fulfilment
  rule (the driver's two resolvers and the harness's `elabFixture` read
  it), `Ir.frameSteps` for the frame-page measure (the
  `pages_count_frame_steps` obligation now ranges over the engine's own
  function; `deckStepChecks` reads it too).
- Hook: a splitOn-idiom gate (the shape all eight test copies shared); the
  seal/unseal mirror per file (q-elab's knots keep four hand-paired
  lists); the size-step-formula gate outside Ir (q-layout's `scaleStep`
  handoff); the free-severity gate retargeted to `demoted :=` (q-ir's
  derivation made `severity :=` uncompilable); the arm gate reads
  signatures split across lines and blesses the generic walks' leaf
  functions by name; the constant-false `partialAllowed` inlined away.
  `tests/golden/diagnostics.txt` merges by union (audit2-harness's other
  half was already in).
- PLAN Status, the Owed registry, and § Hyphenation brought back to the
  tree; bench re-measured this session (91 / 339 ms medians of 5 vs
  lualatex 674 / 1786).

2026-09-20 — a step appears on the arrow key: one sticky stage over N
snap points, script-free. Supersedes the reveal-in-place entry's
scroll-state trigger and its token items.

- The arrival-triggered uncover ran to completion within a second of
  the frame snapping, so the reader never saw the covered state and
  there was no presenter pacing. Now a stepped frame
  (`Ir.maxStepBlocks` N ≥ 2) is one sticky stage over N snap points: a
  `.slide-track` wrapper N × 100vw wide carries the frame section as a
  sticky stage (CSS Positioned Layout 3 §3.4) and N `.snap` spacers,
  each one viewport and a mandatory x-snap (CSS Scroll Snap 1), each a
  deep-link anchor `<frame>-k` claimed through the shared id door
  (W0327 names a colliding frame slug). An arrow press advances one
  snap point — the stage does not move; the scroll offset does. The
  track declares `view-timeline: --frame x` (Scroll-driven Animations 1
  §3.4; §4.2 scoping reaches the steps); step n uncovers over
  `animation-range: contain (n−2)/(N−1) → contain (n−1)/(N−1)` — its
  own snap interval, since `contain` spans snap 1 to snap N for a
  subject wider than the scrollport (§3.1) — and holds (fill both).
  Step 1 is never covered. The `calc()` of unitless custom properties
  × 100% in `animation-range` is spec-blessed (the appendix's
  `<length-percentage>` example) and render-verified on the dev
  Chromium. Support (caniuse, read 2026-09-20): Chromium 115+
  (Jul 2023), Safari 26, Firefox 159+ — the flag era is over; ≈87%
  global.
- Floors, honest and by construction (`deckStepCss_guarded`): without
  `view()` timelines the layout block never applies and the spacers
  hide — one page per frame, every item full colour, no dead arrow
  presses. Reduced motion likewise collapses the snap points and drops
  the fade: SC 2.3.3 removes motion and a colour fade alone is
  arguably not motion, but the base sheet's global reduce block strips
  every animation with `!important`, and a kept fade over dead snap
  presses would be the worst of both — decided as full colour on one
  page, the handout state, the why on `deckStepGuard`. Print hides the
  spacers and keeps the bordered card. The deck's progress hairline
  reads `scroll(root x)`, so a stepped frame advances it N times — its
  snap points are the PDF handout's pagination, page for page.
- Tokens: `--motionstagger` and `--motionduration` go — a scrubbed
  timeline has no delay and no duration, so nothing reads them; the
  time-typed `\tokens` key owed for them is owed no longer.
  `--motiondistance` stays (the come-in offset).

2026-09-20 — the elaborator's duplicated facts get one site each
(impl-q-elab, from the q-elab audit): factorization, behaviour-preserving,
reference documents byte-identical.

- The knot's measure vocabulary is one parametrized family: `measList
  (μ : α → Nat)` with append/push/drop/take/mem/extract, `sliceMeas` with
  here/le/end/elem/extract/splice, `visGo (f : UserCmd → Nat)` with
  mono/congr/expand, one `bindCmd_visGo`. The weight, pars, and items
  components are instances through one `_eq` bridge each; a future
  measure component is an instantiation, not a copy. Knot arms untouched;
  Elab.lean rebuild 75 s before, 73–75 s after (medians of 3).
- Class page geometry has one resolving site, `classPageDefaults`, read
  by the `elabDoc` fold and by `engineLengthTokens` — now an offer-mask
  filter over `engineLengthTokensOfPage ∘ classPageDefaults`, so the
  preamble token environment and the shipped page agree by construction;
  `engine_tokens_agree` states it (inclusion over the token array, the
  `_set_eq` shape). `PageSpec.textWidth`/`.textHeight` are the one
  spelling of the text block; the flow classes' undeclared Bringhurst
  block stays the fold's own `!sawPage` step and its token stays
  deliberately withheld pre-fold.
- Ten Compat arms became the `literalReplace` and `simpleNative` tables;
  `linespread`/`setstretch` are one arm. `measureFrac` carries the three
  fraction-of-measure parsers; `asColor` the four colour keys of
  `\style`; `parsePaletteOpts`, `storeTitlePart`, `takeOptRun`,
  `fontFragment` each replace a copied loop or match. W0304 and the two
  W0105 texts have one spelling each (`warnPaletteMiss`,
  `warnOverlaySpec`, `warnAltSpec`, sealed like `warnUnknownCmd`) — the
  seed for the duplicated-message lint handed to impl-q-harness, with
  the seal/unseal mirror check.
- `_hadv1` proved load-bearing by deletion+rebuild; the explicit-passing
  site drops the underscore, the tactic-only site keeps it (the linter
  cannot see an `assumption` use) with the why written beside it.

2026-09-20 — impl-q-ir: the q-ir audit's implement list lands — one walk
family, one keyed-store proof, derived diagnostic severity.

- The leaf-rewrite family is one generic map: `Ir.mapInline`/`mapBlocks`
  host `setAltBlocks`, `resolveRefs`, and `Layout.substPage` as leaf
  functions, with the explicit-arm obligation at the one walk. Census
  schemas over the map: `mapInlines_text`/`mapBlocks_text` (Conserves
  given a per-node hypothesis; `setAltBlocks_text` is a one-line
  instance) and `mapInlines_id` (conditional identity given a trigger
  census; `substPage_id` its instance). `wrap_text` is the same move for
  body-transparent wraps: `langWrap_text`/`footnoteWrap_text`/
  `underline_text` are one-line instances.
- Named behaviour changes, tests first: a figure body holding a list of
  images now inherits the caption alt (the old wildcard skipped those
  bodies), and an `\includegraphics` inside a `\footnote` or a defined
  role now appears in `imageRefs` — before, it shipped a silent
  placeholder while the file sat beside the document (the collect and
  the placement walked different descents; both are the fold now, and
  `imageSrcs*`/`hasPhysicalPage` are fold leaves). `altWalkChecks` pins
  both, over the HTML tree and `Layout.Out`.
- `Diag` stores its `DiagCode` plus one policy bit; severity and the
  rendered code string are projections, so a diagnostic disagreeing with
  its code's declared `Loss` is unrepresentable. The hook's
  severityAssign gate and its allowlist row now guard nothing
  (impl-q-harness's brief names them for deletion).
- Rhythm: `rhythmQuantum_pos`/`rhythmQuantum_lt_double` carry the omega
  key facts once; `heading_space_above_ge_below` drops the conjunct that
  restated `rhythm_table_exact`'s heading row;
  `Theme.titlepage_align_declared` (subsumed by `_engine`) and
  `Theme.step_find_eq`/`_ne` (verbatim copies of the now-public
  `Ir.declare_find_eq`/`declare_keeps`) are deleted; moloch/daylight
  share `lineageTokens`, all bundles `builtinChrome`. Goldens and the
  four reference documents byte-identical throughout; bench flat.

2026-09-20 — the deck pages sideways: the row, rubber image sizes, and
the come-in reveal. Supersedes the scroll-snap entry's `y mandatory` and
the reveal entry's `snapped: y`.

- Horizontal paging (ratified): most frames share a band structure with
  the title at the top, so advancing sideways keeps that band in place
  while the next frame's content arrives from the side — vertical paging
  scrolled the whole structure away on every step. `main` is the row
  (flex, one 100vw × 100dvh section per page), `html` snaps on
  `x mandatory`, and every scroll-driven timeline reads the same axis:
  the progress hairline `scroll(root x)`, the entry motion and the
  uncover fallback `view(x)`, the uncover trigger
  `scroll-state(snapped: x)`. A section page is one full page of the
  row, centred both axes (vertical flow could scroll past it as a band;
  a mandatory x-snap row has no between-pages place). Print stays the
  vertical handout; deep links still snap; a spill frame grows the row
  rather than clipping.
- Rubber image sizes: the stage is the viewport, so a deck image
  dimension ships as its share of the stage — `deckStageMilli`, the one
  projection deck type already rode, now generalized — in `vw`/`dvh`
  for absolute lengths, `\textheight` fractions and bare scales, and a
  picture's whole SVG box (the "very small image" was a tikzpicture). A
  `pt` length sized against CSS's 96 dpi ruler instead (5 cm of a
  160 mm stage: 31% of the PDF width, ≈15% of a 1280 px slide), and a
  `\textheight` fraction emitted nothing at all. `\textwidth` fractions
  stay percentages: both backends resolve them against the local
  measure (`Layout.collectPara`, minipage semantics).
  `image_share_agrees` states the cross-backend ratio over
  `Image.resolveSize` — Layout's own box — in the `backend_gaps_agree`
  mold; `deckImageChecks` holds the invariant that the deck's HTML
  carries no `pt` image or picture dimension, and that flow classes
  keep `pt`: paper is paper.
- The come-in reveal: a covered step sits dimmed (the handout's oklab
  mix, the floor and the print state) and offset `--motiondistance`
  along the row's axis; on snap it moves to place and takes full
  colour, staggered as before. Colour and transform only — neither
  reflows, so a page that differs by a step differs by nothing else
  (the user's ask). Reduced motion: static full colour, because the
  base sheet's global reduce block removes every animation with
  `!important`; a colour fade kept under reduce (SC 2.3.3 removes
  motion, not fades) would mean unwinding that contract for one effect
  — declined, and the why stands on `deckStepGuard`.

2026-09-20 — backend quality pass (q-backends): the writers call the
functions their theorems name, motion guards ride by construction, one
heading-rank site.

- `Pdf.pdfTextString`'s non-ASCII branch and `Pdf.xmlEscape` were
  byte-identical private twins of `utf16Hex` and `Html.escapeText`;
  both deleted, the XMP inherits `escapeText_no_lt`. `Pdf.write` now
  computes its keep set as `keepFaces` itself, the function
  `html_fonts_cover_pdf` quantifies over, instead of an inline twin an
  edit could silently detach.
- `revealCss` was the one animation site shipping unguarded under
  `css = none`/`bulma`; it now ends in `revealMotionGuard`
  definitionally (`revealCss_guarded`), and `motionSiteChecks` extends
  to `animation:` — every emission definition ends in its guard, spells
  the guard query, or is allowlisted with its reason.
- `Html.headingRank` is the one heading-rank site both text backends
  project; `heading_renderings_agree` now quantifies over every level
  (it was a `decide` over four constants). The rank belongs in `Ir`;
  handed off. Markdown escapes `|`, so a pipe-table cell containing one
  keeps its row (CommonMark §2.4).
- Honest non-theorems, named rather than dressed up: the UTF-8
  "round-trip" claim in Certification is *oracle-backed* —
  `utf8FuzzChecks`, a fuzz oracle against `String.fromUTF8?` — evidence,
  not a theorem; the round-trip theorem is owed. And the covered-step
  shade diverges by construction: the PDF mixes in the engine's own
  Oklab, the HTML delegates to the browser's `color-mix(in oklab)` —
  same declared fraction and space from one `Design`, but nothing ties
  the two mix implementations, so the agreement is a test-level fact,
  not a statable theorem over the engine's functions.

2026-09-20 — the text reveals itself: one HTML section per frame, steps
uncover in place. Supersedes the 2026-09-20 scroll-snap entry's
"steps are pages" item.

- HTML does not have to be made of pages: the per-step section expansion
  copied the PDF handout's pagination into a medium that animates. Now
  one `section.slide` per frame; `frames_sections` replaces
  `frames_pages` as the census — HTML section count = frame count = the
  PDF's page count less its per-step duplicates, both projections of
  `Ir.maxStepBlocks` (`deckStepChecks`). Presenter-paced stepping is
  given up deliberately (the user's call); the deck still snaps frame by
  frame. Label anchors return to their single site; frame ids stay
  unique through the shared claim walk.
- A `.step` starts covered — the design's own oklab `color-mix` shade,
  dim never hide, no reflow — and uncovers to full colour delayed by
  `(--step − 1) × --motionstagger` once its frame is the snapped one.
  Two declarative triggers under `@supports`, best first: scroll-state
  container queries (CSS Conditional 5 `scroll-state(snapped: y)`;
  Chromium 133+ only, ≈71% global, caniuse read 2026-09-20), else the
  `view()` timeline entry motion already uses, so the steps uncover as
  the frame scrolls in. Floor: full colour, the handout state; reduced
  motion likewise, guard by construction (`deckStepCss_guarded`). Print
  never sees a step rule. The emit-time cover plumbing (and
  `role_use_names_its_token_covered`) went with the expansion: coverage
  is a stylesheet state now, so an explicitly coloured run inside a
  covered step no longer dims pre-reveal — the remainder is named in
  the covered-pictures line of the scroll-snap entry's out-of-scope.
- Tokens: `--motionduration` gets its default after all, 0.4 s
  (reveal.js/Quarto default transition-duration) — the earlier "no
  duration token" reasoning held for scroll-scrubbed timelines and the
  snap trigger is time-based; `--motionstagger` defaults to 150 ms (no
  authority fixes a reveal stagger — Material's ≤20 ms choreography rule
  is for simultaneous surface creation — so the default takes one beat
  from Material's small-animation band, 150–200 ms). Both are var()
  doors; a time-typed `\tokens` key remains owed.

2026-09-20 — the stage is one declared key: beamer's aspectratio table
entire, and a native spelling.

- The defect class: two stage constants selected by string-matching
  `aspectratio=169`, so every other documented beamer ratio (`1610`,
  `149`, `141`, `54`, `32`) silently shipped 4:3. The invariant: option
  vocabulary and engine geometry come from one sourced table.
  `Ir.slidesStages` carries beamer's §8.1 / `beamer.cls` table (1610 →
  160×100 mm, 169 → 160×90, 149 → 140×90, 141 → 148.5×105, 54 →
  125×100, 32 → 135×90, 43 → 128×96), each row named by its ratio;
  every `aspectratio=` option and the native `\page{ size = 16:9 }` —
  the same `size` key papers use, `√2:1` by beamer's digits `141` —
  resolve through it, colon elided. Unknown names keep E0324; an
  unknown `aspectratio=` value keeps beamer's 4:3 default, silently for
  now (no allocated code).
- The contract travels with the table: `slides_lines_in_band`
  quantifies over every row (one `decide`, the `Theme.builtin`
  pattern), and `slides_lines_survive_bands` takes table membership —
  adding a stage is entering the contract. Witness fixture `deck1610`
  with its census row asserting the shipped 160×100 stage.
- HTML stays stage-free by construction, now stated: the screen deck
  reads only the stage-height ratio (`deck_type_is_stage_ratio`), so
  equal-height stages emit identical screen decks (16:9 vs 14:9,
  pinned in `deckCssChecks`) and the frame reflows on any viewport —
  "html can probably just do it itself", held as a test. Print is the
  handout, a paged medium; its measure legitimately reads the page.

2026-09-20 — the HTML ships the faces the PDF embeds: one `FontSet`, two
emitters.

- The convention (ratified): the artifact is a function of the document
  and the font environment, so the HTML artifact ships the faces the
  document resolved, exactly as the PDF does — the emission was
  name-only (`--font-body: "Fira Sans", Georgia, serif`), so a viewer
  without the face installed read the deck in Georgia. Now one
  `@font-face` per face of the driver's resolved set (`shipFaces`),
  under synthetic slot families (`ltx-body`/`-sans`/`-mono`/`-math`, so
  an installed font of the same name never substitutes), weight/style
  the face's own declarations, whole font programs written by the
  driver as `<stem>.fonts/` siblings from the emitter's write requests
  (`fontAssets`, effects as data). No WOFF (no compressor) and no
  subsetting yet — subsetting both backends is named next.
- The contract: `Pdf.html_fonts_cover_pdf` — every face the PDF writer
  would embed (`keepFaces`, the factored keep set) has a `@font-face`
  in the emission from the same set; stated as the superset (HTML never
  sees used-glyph data, so it declares every face), with
  `shipFaces_covers` and `shipFaces_src_shipped` the emitter halves.
  The census tests pin the deck fixture's rules, stacks, and requests.
- Degradation matches the PDF's: `body` states the resolved regular
  face's weight and `font-synthesis: small-caps` — no faux bold or
  oblique, a missing variant takes the nearest real face, as
  `FontSet.lookup` does (rendered proof: the deck's Light body and
  Regular titles now match pdftoppm). A slot's stack lists every family
  of the set after its own — the browser's per-character walk is the
  CSS spelling of `FontSet.fallbackFor`. The generic keyword comes from
  the face's OS/2 sFamilyClass / post isFixedPitch (both now parsed,
  fsType recorded, nothing gated), else the slot's declared kind.
- A document that declared its `css =` story owns fonts itself: the
  driver passes no set and nothing ships — the site port's `css = own`
  output is unchanged but for `.math` reading through `var(--font-math,
  <the old stack>)`, its new token.

2026-09-20 — the deck pages itself: scroll-snap supersedes the vendored
controller, and the same talk is a lightly animated HTML deck with zero
script.

- One tree, two media renderings, every rule gated on the slides class:
  on screen a paged full-viewport deck — the browser's own paging (CSS
  Scroll Snap 1, `y mandatory` + `scroll-snap-stop: always`), smooth
  scrolling guarded by construction (`smoothScrollCss_guarded`) — and in
  print the stacked-card handout, one slide per page (Tufte: the handout
  is the document). No `\output{ html = handout }` key: add it only if
  someone wants the scrolling view on screen. The webpage class's output
  byte-compares against main at every commit in the slice.
- Steps are pages: the deck walk expands each frame to one `section`
  per overlay step — the PDF handout's exact pagination, from the same
  `Ir.maxStepBlocks` — and on page k a pending step is *covered*, never
  hidden, in the page's own spelling: `color-mix(in oklab, …)` at the
  design's declared fraction (CSS Color 4 §12.2), each explicitly
  coloured run its own reference inside the mix
  (`role_use_names_its_token_covered`). `frames_pages` is the census:
  slide sections = Σ frameSteps, and with the themed section pages the
  PDF's shipped page count (`deckStepChecks`); footline agreement holds
  across the expansion by collapsing consecutive step pages, as the PDF
  side always has.
- A frame's declared vdist reaches the artifact: flex spacers carrying
  `Layout.VDist`'s own ratios (golden 2618:1000 included), stated once
  per backend and pinned to each other by test. Every slide claims an
  id through the article's uniqueness walk (`claimId`, shared) — deep
  links per slide, label anchors on a frame's first step page only.
- The lightly-animated half is scroll-driven CSS under `@supports`,
  floor = static and visible (revealCss's design): a viewport-top
  progress hairline scaled by `scroll(root)` reading the PDF's own
  `--progressheight`/`--progressfg`, and entry motion scrubbed by
  `view()` — fade plus a `--motiondistance` rise, guard travelling with
  the declaration (`deckEntryCss_guarded`). No duration token: a
  scroll-scrubbed timeline has none. `@view-transition` declined
  (cross-document only; weaker floor than snap).
- Keynote-clean is tokens: `--safearea` (Keynote masters keep ≈5–7%
  clear; default 6vmin), `--titleband` (≤1/8 of the slide), and type
  from the stage — `main` carries fontSize/stage-height in vh
  (`deck_type_is_stage_ratio`, the `backend_gaps_agree` mold), headings
  retaking their scale steps in em so nothing sizes from the reader's
  root.
- The controller: scroll-snap supersedes it for paging and stepping;
  `--emit reveal` is dead with `--emit`. What remains of M5's
  controller ask is the speaker view alone (notes/timer/next-slide) —
  a user decision behind a named `\output` key and a design discussion,
  not a default. Remote stepping and auto-advance are likewise
  script-only and stay asks.

2026-09-20 — footnotes: the note lands on the page of its mark, by
construction and by theorem.

- `\footnote` is a modelled node (`Inline.footnote`, inline body only —
  a paragraph break inside a note is a space, W0371), numbered at
  elaboration through `Ir.footnoteMark`: document-wide, `[num]` overrides
  unstepped (ltmiscen.dtx `\@xfootnote`), and
  `footnote_numbers_gapless` instantiates `numbers_gapless` over the
  step. The body is document text (`footnoteWrap_text`, a `Conserves`
  instance); the mark digit is generated ink, as `citeMark` is.
- Layout: the mark is a raised scriptsize run (`Ir.markRaise`, one named
  constant standing in for OS/2 `ySuperscript*`); each note is its own
  pre-broken block at footnotesize on the full measure, attached to the
  page when its mark's line commits and flushed bottom-anchored in
  `finishPage` before the vertical distribution — flush or centred
  bottoms never move a note, which is also what lands a deck's note at
  the frame foot. `\skip\footins` is the rhythm-quantized `footins`
  token (`footins_within_glue`: two quanta, inside the source glue's own
  rubber); `\footnoterule` and `\footnotesep` are sourced constants
  written where they stand. Whole-or-move: `placeLine_note_with_mark`,
  `footnote_with_mark`, and `note_whole` are theorems over the builder
  (the `float_whole` `PagesExtend` shape); a note taller than the text
  block ships whole with W0372 naming the overrun, never split (TeX's
  split insertions refused by design).
- HTML: `doc-noteref` marks, one `doc-endnotes` section with
  `doc-backlink`s (W3C DPUB-ARIA 1.1), no script; markdown sets `[^k]`
  with definitions after the body. Refusals named: W0370
  `\footnotemark`/`\footnotetext` pending, W0373 `\thanks` kept inline
  in the title block, W0374 a card face has no note apparatus.
- Named remainders: parsing OS/2 `ySuperscript*` (the mark raise's real
  authority); per-chapter numbering with a real `report` class (a
  `ClassRecord` field then); `\thanks` as a title-foot note with
  fnsymbol marks; note splitting across pages (a `runFloat`-class
  rework); `footmisc` (unfunded compat-index obligation); the markdown
  *reader*'s `[^k]`; per-frame renumbering on decks; underline siblings
  for links inside PDF notes; footnotes inside captions, table cells,
  and headings stay inline (no diagnostic yet).

2026-09-20 — the vertical convention lands: the line box is the leaded
metric extent, and everything against a line measures from metric lines.

- The PDF adopts CSS 2.1 §10.8.1's half-leading (the operator decision
  of 2026-09-19, ratifying vert-line): a line's box is the fonts'
  ascent/descent at each run's size plus half the leftover leading each
  way (`leadedBox`; the odd unit goes below), glyphs never consulted
  (`line_box_glyph_free`); consecutive baselines sit apart by
  below(prev) + above(next), which for uniform text is *exactly* the
  leading (`baselines_on_grid` — termination of the off-grid accident
  the old TeX collision rule allowed). `\lineskip` leaves the interline
  rule entirely and survives only as the furniture ink-clearance floor
  (`inkClearance`). `placeLine_gap_exact` drops its collision
  hypothesis; `first_baseline_declared` pins the `\topskip`-shaped
  first-baseline rule over metric ascent. The two backends now share
  one baseline convention — HTML already shipped it as `line-height`.
- Ink is read only to interrupt (the underline band) or to clear (page
  bottom, furniture bands, flush stacking under a table rule), never to
  position; `LineBox` carries the leaded box and the ink extent side by
  side. The accepted cost is written beside `lineExtent`: a
  descender-less title keeps its metric depth, so its optical gap is
  larger than its ink suggests. Grid-snap after size changes
  (ConTeXt-style) remains a candidate *declared* behaviour, not the
  default.
- The heading rule is raised half the x-height of the heading's own
  face at the heading's size in both backends (`xHeightOptical`: the
  measured ink 'x', the trust order the math match uses); it was the
  body's x-height at body size in the PDF and the bare baseline in
  HTML, whose comment claimed parity.
- The underline theorems close on a pure core: pass 2 is `subtract`
  over pass 1's `mergeIntervals`, whose `Chained` postcondition is
  proved — `underline_skips_ink`, `underline_covers_gaps`,
  `subtract_bounds`, `underline_text` (the registered `Conserves`
  instance), `underline_no_growth`. The band guard tightens to the
  face's own descender line (`underline_in_descent`); HTML declares the
  same band source (`text-decoration-thickness/-position: from-font`,
  CSS Text Decoration 4 §2.4.1/§2.8.2), dropping the unsourced 0.15em
  and 1px. A skip-ink-off knob is owed on demand, not built: nothing in
  the corpus asks for it (vert-underline implement-4 has the shape —
  an `underlinegap` token plus a declared off key).
- Small-cap synthesis scales per face (`smallCapScaleFor`,
  `smallcap_height_between`): 800‰ (fontinst tradition) lifted exactly
  where it would drop small caps below the lowercase x (Bringhurst
  §3.2.2), never above full caps.
- Owed, not fixed: `\textsuperscript`/text scripts stay the loud W0301
  refusal (pinned by test). When they land, the raise comes from the
  face's OS/2 `ySuperscript*`/`ySubscript*` metrics (or the MATH
  constants when the face has them), never a ratio — blocked on the
  OS/2 script metrics being unparsed in `Font.parse`; the machinery
  (`Seg.run` raise) is ready. Icon centring stays the face's own design
  until a rendered page argues otherwise (vert-align: do not change
  blind).

2026-09-19 — the taste slice lands what four advisors agreed on: decks
default to `daylight`, and six reader-visible defects close.

- `daylight` is a built-in bundle (warm paper, warm ink, one azure
  accent, no title bar) and the slides-class default when no theme is
  declared, installed *under* the document (`Theme.applyUnder`: a
  default never replaces a declaration). Print classes keep unpainted
  defaults — a bundle there paints every page edge to edge (99.9% pixel
  change measured on a one-page résumé). `\theme{default}` opts a deck
  back to the bare look, beamer's own spelling.
- The slides class sets its text in the declared sans family (beamer
  user guide §18: the default font theme is sans serif); named font
  weights resolve to the nearest installed weight with W0366, never a
  silent Bold-for-Light; a frame's title chrome repeats on every
  continuation page; a spliced class's `\@setfontsize` leading is
  honoured; headings carry their own rhythm tokens
  (`heading_space_above_ge_below`); display lines balance (a title
  never strands a word); paragraphs break in TeX's two passes with
  `\finalhyphendemerits`; contrast is judged per (ink, ground) pair;
  `\color` at block level declares the flow ink; non-ASCII PDF text
  strings are UTF-16BE with the BOM (ISO 32000-2 §7.9.2.2).
- `titlepage_align_declared_engine` discharged from the staging queue:
  restated over `Theme.apply t {}` — the function the `\theme` site
  calls — and proved by `decide`; the through-`Elab.run` reading stays
  with the executable oracles (WF recursion is kernel-irreducible, the
  2026-09-19 probe).

2026-09-19 — the last `partial` is off: `elabBlocks` terminates by a
proved measure, and the plan's termination claim has its checker.

- The block knot — the spine, its ctrl and env dispatch arms, the
  figure/columns/items loop members, the note drain, and the
  redefinition gate — is one mutual recursion terminating by
  (envLimit, noteFlag, visPars + slicePars, visWeight + sliceWeight,
  layer, scan): a user-environment expansion falls in `envLimit`; the
  frame's note drain falls in `noteFlag` (its bodies come from the
  state, so no weight fact covers them; inside a note body the drain is
  refused, E0359, so the flag never rises); the par-splice falls in the
  pars sum (`slicePars_splice`); every other edge falls in the weight
  sum — a body `\define` moves its body's weight from the slice into
  the visible-command sum and pays the consumed group's wrapper
  (`takeDefine`'s carried facts), and an expansion moves it back out
  (`visWeight_expand`). No fuel, no `sorry`, no weakened statement, no
  heartbeat raise — the arms with no recursion (tabular, display math,
  align, tikz, maketitle, the nav options) live outside the knot, which
  is what fits the pack in the default elaboration budget.
- `elaboration_total` (Elab.lean) names the fact for this plan to cite:
  the sentence that lied for twelve hours on 2026-09-19 ("nontermination
  is impossible by design") now has a checker — the termination checker
  verifies every recursive call against the measure at compile time, and
  the pre-commit `partial` allowance is *none*, so the exception list
  cannot silently regrow. The prior entry's interim rule ("or, until
  `elabBlocks` is total, the named test") is discharged; the wall-clock
  test stays as the end-to-end integration witness.
- Verified behaviour-preserving: the four reference documents
  byte-identical (PDF + HTML + normalized stderr) against the pre-rewrite
  binary; bench at-or-faster on every corpus document; the 2026-09-19
  hang document runs in 68 ms.

2026-09-19 — a guarantee stated in prose is not a guarantee: the
nontermination bug, and the theorem that now holds monotone visibility.

- **The bug.** The body-position `\define` arm landed at 01:56 (cffb141)
  set `limit := ctx.user.size + 1`: a definition made *inside* an
  expansion became visible to the expansion that made it, so a command
  whose body defines anything and then names itself looped forever — a
  four-line document reproduced it (exit 124). For those twelve hours the
  2026-09-15 entry's sentence "nontermination is still impossible by
  design — a user command's body sees only definitions that precede it"
  was false. Nobody caught it because the sentence is prose — a claim
  with no checker — and `elabBlocks` is `partial`, so the compiler could
  not see the measure break either. Every golden stayed green: goldens
  witness elaboration of documents that terminate, not termination.
- **The fix that landed first.** 14:14 (4cdfa0d, the venue-`.sty` slice)
  rewrote the arm to bind at the visibility boundary: the new command
  enters at `min limit user.size` and `limit` advances exactly past it,
  so the walk sees one more command and never the suffix beyond — a
  venue file's `\maketitle`, which renews a command and then names
  itself, now resolves its self-name to the definition *before* it
  instead of diverging. (departial3 had recommended refusing the
  construct instead, code E0360 allocated; the boundary insertion
  supersedes that — the construct is legal LaTeX and now terminates, so
  there is nothing to refuse. E0360 stays unregistered.)
- **The writedown the bug earned.** The design was right; what was
  missing was the statement that would have made cffb141 fail to
  compile. It now exists: both define sites go through one door
  (`bindCmd`), and `bindCmd_monotone` (Elab.lean) states that a command
  invisible before a bind — the one being expanded, at `j ≥ limit` — is
  after it the same command, still invisible, at its shifted index.
  Re-introducing cffb141's transform fails the build at that theorem
  (verified once, then reverted). Until `elabBlocks` is total the
  end-to-end guarantee is additionally held by a wall-clock regression
  test (`terminationChecks`): the four-line document elaborates under a
  30 s bound, and a regression fails loudly instead of hanging the
  suite — the test that would have caught cffb141.
- **The rule** (also in AGENTS.md § Conventions): termination, totality
  and determinism claims in this plan name the theorem — or, until
  `elabBlocks` is total, the named test — that holds them; a claim with
  neither is written as owed under `Obligations/`. The 2026-09-15
  paragraph stands as the counterexample: it was true when written,
  silently false later, and nothing could notice.

2026-09-19 — the preamble is a fold over declaration values, and T1's
proved tier is a theorem.

- **The fold (audit-compose item 7, landed).** `scanDecls` segments the
  preamble into `PDecl` values — pure, positional, extents only, with
  malformation facts (an unclosed `[`, a missing group) carried as data —
  and `elabDoc` is now `foldlM applyDecl` over them; `applyDecl` owns
  every diagnostic in scan order. The loop's recovery quirks are
  transcribed, not cleaned up: a declaration whose group never
  materialises consumes only what the loop consumed, and the tokens it
  looked past rescan as their own units. The refactor was proven, not
  argued: the whole corpus rendered to PDF and HTML at main and at each
  restructuring commit, byte-identical in every artifact, normalized run
  report, and exit code; no golden moved; bench flat.
- **The state split (compose-fix's named precondition).** The six keyed
  apply steps (page, fonts, pdfmeta, output, chrome, assert) plus allow
  are pure functions returning a value and ordered reporting events
  (`PEvent`: a diagnostic, a W0343 scalar note, a W0348 declared-key
  note); `applyEvent` is the one meaning behind `noteScalar` and
  `noteDeclared` too. Effects as data: a step's whole interaction with
  the elaboration state is an event list a lemma folds over.
- **T1, proved tier (`applyDecl_comm`).** Independent keyed declarations
  — different heads among page/pdfmeta/fonts/output/chrome/assert/allow
  (`PDecl.Independent`) — commute: the fold state agrees under
  `PreState.sem`, and the elaboration state returns reporting-equal to
  where it started under `ESt.sem`. The projections erase exactly the
  four stores whose only readers are diagnostic sites (diags, warn-once
  memo, W0343 store, W0348 store) and nothing else. Exceptions carried
  verbatim from the audit (reference→referent wholesale, `\theme`
  position, `\documentclass`, same-key order), plus one the proof forces
  into the open: the inline-content heads (running head/foot, logo,
  titles) elaborate through `elabInlines`, a tracked termination-checker
  exemption no theorem can range over — those stay oracle-only. The
  oracle is KEPT: it alone covers the content heads, same-head
  field-disjoint swaps, and the diagnostic-code multiset. `_comm` is a
  new theorem shape beside the registered suffixes: a two-order equality
  under a named projection, with an independence side condition.
- **Proof shape, learned the expensive way (the collectBlock lesson's
  twin).** A keyed arm is `stepDone` of a pure step; run lemmas are
  stated per projection (`EM.run_stepDone_fst/snd`) so pair literals
  never appear in goals; and a step's value is ONE record literal with
  any conditional inside the field (`sawPage := cond || s.sawPage`, a
  field-level match for asserts) — a branch at record level forced
  split-then-rfl through kernel-opaque terms and ground for hours, while
  the in-field form makes the whole 529-case dispatch elaborate in
  seconds. Whoever states the fold-permutation corollary: the remaining
  work is the suffix-congruence (a later arm's value must be shown to
  read only `sem` fields plus order-insensitive views of the keyed
  stores), not more pairwise cases.

2026-09-19 — M6's math-side interface: alphabets, accents, and macros in
formulas. W0012 degrades a whole formula, so each closed row un-degrades
every formula carrying it; the corpus audit's four largest math closers
land together.

- **Alphabets** (`\mathbb`/`\mathcal`/`\mathfrak`/`\mathbf`/`\bm`/
  `\boldsymbol`/`\mathit`/`\mathsf`/`\mathtt`/`\mathrm`, plain-TeX
  `\cal`/`\frak`): one char-level remap into the Mathematical Alphanumeric
  block (Unicode ch. 22.2, unicode-math's usv), the Letterlike Symbols
  holes individually — `\mathbb{R}` is U+211D, never tofu at the reserved
  U+1D549. Theorem: the map is injective on the letters, stated as a left
  inverse (`alpha_apply_inj`, `decide`, linear); the remap walk is the
  identity on the classes projection (`remapList_classes_id`), so spacing
  survives it. A mapped scalar no face covers renders as its base letter —
  bold/italic from the text face where that is the alphabet's essence, the
  plain letter for the shape alphabets — under a new note, N0018, naming
  the styling difference; the per-scalar fallback chain still wins first
  (W0009), and E0405 remains for scalars with no stand-in.
- **Accents** (`\hat`/`\bar`/`\vec`/`\tilde`/`\dot`/`\ddot`/`\widehat`,
  and `\overline`): the combining mark placed so its own
  MathTopAccentAttachment x lands on the base's (OpenType MATH
  MathGlyphInfo §MathTopAccentAttachment; half the advance where the face
  lacks the point), raised by the base ink's excess over
  `accentBaseHeight` — TeXbook Appendix G rule 12, base in the cramped
  style. The spec puts no bound on the attachment value, so the base-side
  read clamps into the advance and `Font.topAccentX_covers` is the
  placement bound; the mark side stays unclamped (a zero-advance mark
  attaches inside its own ink). `\widehat` stretches through horizontal
  MathVariants by `Math.pickWidest` (widest not overhanging — the reverse
  of a delimiter's pick; `pickWidest_covers`/`_mem`); `\overline` draws a
  rule from the overbar constants, exact at any width — the stated
  fallback for a face with no horizontal ladder, which Fira Math is.
- **Macros in math**: `elabMathInline` never consulted the macro table, so
  every `\define`d command un-rendered its formula. One raw-to-raw hook
  (`expandMathList`) expands before parsing; termination is the visible-
  prefix rule made structural — a body expands under `k < limit`, the
  lexicographic measure's first component — with arguments bound already
  expanded (the walk runs right to left), matching `takeArgs`' text-mode
  order. A self-reference stays outside its own prefix and degrades named.
  `\DeclareMathOperator` rewrites to a `\define` with an `\operatorname`
  body (amsldoc §5.1); `\ensuremath` enters math from text and is
  transparent inside it. Parameters of an enclosing text definition do not
  reach nested math (their bindings are inlines, not raws) — named W0012,
  the recorded remainder.
- **`\newif`** joins the `\ifdefined` pass: flags resolve in flow order,
  setters flip them, untaken branches never fire a setter, every
  resolution an N0114 note.
- The parser's pending argument slot became a chain, so a construction
  stands as another's argument: `x^\frac{1}{2}`, `V^\text{null}`,
  `x^\mathbb{R}` parse where each degraded its formula before.

Measured: the private reference paper's extracted text went from 22 lines
carrying backslash source (52 sequences) to 5 (25), all in formulas
carrying `\label` — the cross-reference slice's row. Deck/résumé/card
PDFs byte-identical under this slice's commits; bench medians within
main's noise band. Verified as pixels beside expectation for accents,
alphabets, and expanded macros.

2026-09-18 — `\scshape` means uniform small caps, so the text can carry
real casing.

- **The decision.** `\scshape` renders every letter as a small capital —
  CSS `all-small-caps`, OpenType `c2sc`+`smcp` — not the CSS/LaTeX
  small-caps rule that keeps capitals full height. The argument: under the
  old rule the source must lie about casing to get the canonical form
  (`{\scshape phd}` for a uniform PhD — Bringhurst 3.2.2 sets mid-text
  abbreviations in small caps, uniformly), and the lie survives into the
  markdown twin as a misspelled credential (W0344 named it; now retired).
  Under the new rule every style is reachable with true text: uniform is
  the default, and caps-and-small-caps — a legitimate style the old rule
  gave for free on mixed case — is still spelled `A{\scshape lex}`, the
  compositor's own decomposition. The corpus evidence: every shipped
  `\scshape` use is a running head or display name (`Alex Doe`, `A Linked
  Document`, `Alex Doe, phd`), which under this rule set as even small
  caps — the canonical running-head form — where before their capitals
  stayed full height; no fixture relied on the mixed-case effect on
  purpose, and `phd` (webpage.tex) was exactly the workaround this
  retires. All-lowercase input renders as before, verified over
  `Layout.Out`: the drawn gid+size sequence for `phd`, `PhD`, and `PHD`
  is identical under both mechanisms, which is what "uniform" means as a
  measured fact.
- **The mechanisms.** PDF: the sfnt reader now parses GSUB single
  substitution (LookupType 1, formats 1+2) for `smcp`+`c2sc`, resolved
  for `latn`/`DFLT` default LangSys, composed in LookupList order; a face
  carrying both features substitutes real small-cap glyphs at full size,
  text kept as typed (so extraction and ToUnicode carry the author's
  casing). Contextual/alternate/ligature/extension lookups, non-default
  language systems, and lookupFlag filtering are not read — no corpus
  face needs them for these two features. Fonts without both features are
  the normal case and keep synthesis, now uniform: the whole word takes
  its capital forms at `smallCapScale`, one size, replacing the old
  case-split that kept capitals full height (the mixed-case trap). HTML:
  `.sc` asks `font-variant-caps: all-small-caps` (CSS Fonts 4), the same
  feature pair, so the backends agree by construction.
- **Presence, measured** (`smallCapsGsubChecks`): Source Serif Pro
  Regular/Bold and Fira Sans carry both features; Open Sans, Source Code
  Pro, the Source Serif italics, Fira Math, and the icon face carry
  neither — so both mechanisms are exercised by shipped fixtures on every
  host.

2026-09-18 — scope: a setting's effect is confined to its declared extent,
and the model is written down.

- **The model (audit-scope, landed).** From-here-forward flow scope,
  uniform, no brace revert — the engine's documented `\centering` choice,
  and what `\logo`/`.framefoot` already implement. Before, scope was an
  accident of read time: elaboration-time readers saw from-here-forward
  while layout/emission-time readers saw last-write-wins whole-document
  (`bodyPalette`/`bodyTokens` displacing `doc.palette`/`doc.tokens`), so
  one `\palette{fg=…}` inside a `\block` recoloured the page retroactively
  and the HTML `:root` diverged from the PDF's baked ink — both
  machine-verified before the fix.
- **The mechanism.** Body `\palette`/`\tokens` are IR blocks
  (`.setPalette`/`.setTokens`) carrying the full state snapshot in flow
  order; elaboration's flow state carries the snapshot past a nested
  scope's close (one Nat generation guard per raw item), so
  elaboration-time and replay-time readers see one scope.
  `doc.palette`/`doc.tokens` are the preamble+theme state — epoch 0.
  Layout replays the block in the accumulator (palette, tokens, the ink
  derived from the palette in force; standout/frametitle restores
  recompute rather than restore a saved copy); a stateful block is
  gap-transparent. HTML redefines only the changed custom properties on
  each following sibling's own style attribute — a wrapper div would break
  the `* + *` adjacency the rhythm rules key on; `:root` carries epoch 0.
- **The misplaced-declaration door.** A declCtrl/runningCtrl name met
  where it cannot stand is ours, never W0301-unknown, and its arguments
  never become page ink: W0346 (config) for a declaration inside inline
  content, E0347 (dropped — the severity derives from the loss) for a body
  or inline running head/foot, whose group is content.
- **Retroactivity, per declaration.** palette/tokens — (a) forward, both
  backends, both read times (was: (a) xor (b) depending on the reader);
  logo/framefoot — (a) forward, unchanged; the preamble-only eight —
  fenced (W0340/E0347), honestly whole-document. Deliberate epoch-0
  remainders, stated not hidden: page background and the overlay cover
  fraction (page-scoped attributes of the run), `themeCss` feature gating,
  and chrome/running furniture and their contrast judgement.
- **Theorems and evidence.** `Acc.setPalette_emits_nothing`/`setTokens…`
  (proved, rfl): the arm touches no op, no owed glue, no gap flag — the
  checkable core of confinement. The walk-prefix statement
  (`setting_confined_to_suffix`) is blocked: unfolding `collectBlock`
  needs equation lemmas whose generation exhausts `whnf` (the
  `role_transparent_layout` blocker); its executable oracle in Tests
  (scopeChecks) compares the page closed before a declaration with and
  without it, both directions. `doc_geometry_uniform` (proved): the
  placement steps never write `geom`, so a second geometry is
  unrepresentable on the way to `Out`. Elaboration-side statements stay
  blocked on `elabBlocks` being `partial` (sanctioned); the tests are the
  evidence and say so.
- **Contrast per epoch.** The uses walk threads the palette in force: each
  use is judged on its epoch's effective page with its epoch's decorative
  exemption (a plain redeclaration removes the exemption from where it
  stands); each body epoch's effective pair is judged as epoch 0's
  (W0315/W0330); W0345 extends per epoch — the walk records which epochs
  ship a titled frame, standout, or pending content, and judges each
  against the palette in force there. Epoch-0-only documents are
  judgement-for-judgement unchanged.
- **The named divergence.** HTML cannot carry a nested epoch past its
  enclosing element's close (a custom property cannot reach an ancestor's
  later siblings without a wrapper): a nested epoch is brace-bounded in
  HTML and whole-flow in the PDF, pinned by test from both sides; the flow
  state re-synchronizes at the next declaration (snapshots diff against
  the walk's own state). Body-legal running head/foot (audit item 5)
  remains a milestone, not this slice.

2026-09-18 — settings compose: repeat semantics are decided by the key's
type, and the four accidents that broke that rule are gone.

- **The rule (audit-compose, landed).** The surface's repeat semantics are
  now uniform enough to predict from the key's type: keyed merge for open
  maps (palette/tokens/styles, per-slot chrome), append+dedup for genuine
  lists (formats, dirs, allow, asserts), last-wins for scalars. The four
  accidents: `\fonts` dotted faces were silently FIRST-wins (push read by
  `find?` — `FontSpec.declareFace` now mirrors `Tokens.declare`, per the
  fontspec manual's replace rule, with `faceFor_last_declared`);
  `applyChrome` merged slots within a block but replaced wholesale across
  blocks (now threads the previous chrome — one declaration, one meaning;
  a document block after `\theme` therefore refines per slot, the palette
  analogy its docstring already claimed); `[from]` was one variable shared
  by `\runninghead` and `\runningfoot` and sticky across redeclares (now
  `headFrom`/`footFrom`, each declaration's own, reset when the option is
  absent; the logo waits for the later of the two); Compat concatenated
  repeated fancyhdr fields that the fancyhdr manual defines as redefining.
  And `sawPage` is set only by geometry keys (`pageGeometryKeys`), so
  `\page{ parskip = … }` no longer silently forfeits the Bringhurst margin.
- **The conflict is named (W0343, config).** A scalar key given two
  *different* values warns at the preamble apply sites — page, pdfmeta,
  fonts families (aliases folded), output's css/stylesheet/md, chrome
  slots, replaced running content. Same-value repeats are silent (classes
  synthesize them); tokens/palette/style are exempt because
  redeclare-to-override is the layering mechanism; theme installs write
  outside the store, so overriding a theme default never warns.
- **The set-not-sequence claim, honestly graded.** T2
  (`Tokens/Palette.declare_last_wins`, `declare_overwrite`) and T4
  (`OutputSpec.addFormat_nodup`) are theorems; T3
  (`faceFor_last_declared`) likewise. T1 (adjacent preamble declarations
  commute up to the named exceptions — same key, reference→referent,
  `\theme` position) is **oracle-only**: `scripts/compose-fuzz.lean` swaps
  every adjacent pair with different heads, or the same head with
  field-disjoint key sets (`size` counted as width+height, `margin` as
  both margins), over the corpus plus synthetic preambles, comparing the
  `Doc` and the diagnostic-code multiset. An executable oracle is
  evidence, not a theorem. T1 is not merely unproved but *unstatable*
  today: the audit's statement quantifies over declaration values, and the
  preamble loop is an imperative scanner with no such values — the
  `applyDecl` fold extraction (audit-compose item 7) is the statement's
  precondition, not just the proof's. It also needs the elaboration state
  split so diagnostics, which legitimately reorder under a swap, live
  outside the compared projection. Left for the successor slice with the
  oracle riding; the oracle was watched catching the chrome
  wholesale-replace defect when that fix was temporarily reverted.

2026-09-18 — the rhythm is declared where both backends read, and each
backend proves it realizes it.

- **The user's complaint, verified.** "Theorem spacing has not been
  theorem-ized at a high enough level since it's not applied to html along
  with pdf" — right, and sharper: `default_rhythm_multiples` and
  `caption_gaps_rhythm` ranged over Ir tokens but were housed in Layout,
  so HtmlDoc could only cite them in comments. A comment was carrying a
  guarantee.
- **Layer 1, declaration (Ir).** The unit is the governing context's body
  leading (`Ir.leadingFor`, moved from Layout — moving a function to reach
  a theorem, not the reverse), the quantum its half, the peer token
  `Ir.parskipDefault`, and the multiples one table (`Ir.rhythmGapQuanta`:
  peer 1, heading 2, caption 1, float 2; `rhythm_table_exact`). The Layout
  spellings are deleted; artifacts byte-identical through the lift.
- **Layer 2, realization, PDF.** Over the placement's own functions:
  `flushGap_default_exact` (one `.skip` of the resolved parskip at an
  undeclared boundary, never two emissions), `placeLine_gap_exact` (the
  pending skip lands 1:1 above TeX's interline), `finishPage_shift_uniform`
  (page close moves the unpinned block by one delta on a page with no
  shrink spent and no fil, so gaps reach `Out` as placed). Rubber is the
  named negotiation: shrink only against a break and reported (N0200),
  stretch never.
- **Layer 2, realization, HTML.** The theorem is about the gap the box
  model realizes, which forces the encoding: one emitter per boundary —
  the element below owns its gap as `margin-top` via zero-specificity
  `:where(* + sel)` rules computed from the table (`quantaRem`; base size
  1.0625rem → 1rem makes every value exact), all block-element margins
  zero, so block collapse (max) and flex stacking (sum) agree
  (`single_owner_gap_exact`) and a consumer flex container cannot double
  a gap — the site port's 52px-for-32px defect is unrepresentable. One
  bottom-owned boundary, stated: a heading's band below is the heading's
  own (PDF's after-replaces-peer semantics; followers suppressed), so a
  consumer owns a heading's whole band with one rule — measured necessary
  against the port's audited h2 margin-bottom exception.
- **Layer 3, agreement.** `backend_gaps_agree`: over every pair of table
  rows, PDF sp and emitted milli-rem cross-multiply equal — the same
  integer ratios in both artifacts. Moduli named, not hidden: preferred
  values only (CSS has no glue; rubber is PDF-only and reported), and
  per-context units (half the print leading vs half the screen leading —
  the multiple is shared, the length is the context's).
- **Slides.** `slidesVMargin` was the engine's own and 0.888pt off two
  slides-context units; now derived (`2 * leadingFor slidesFontSize`),
  goldens regenerated, the 62-page acceptance deck unchanged in pages and
  diagnostics. Stated exceptions, kept with their sources: moloch-lineage
  em furniture (the theme's dtx is its bundle's authority), half-em
  furniture paddings (em-relative by design), booktabs ex seps (dtx).
  `vmargin_on_rhythm` pins the article inch = 6 units so the coincidence
  cannot drift silently.

2026-09-18 — palette roles: a role is defined by the palette, and a use of
it can never freeze.

- **The decision.** A role is defined by the palette; a command is
  generated from a role, never the reverse. `\muted{x}` already worked with
  no `\newcommand` (the elaborator's palette arm resolves any entry name),
  but nothing stated it, so nothing protected it. The rejected framing — a
  definition *modifies* the palette — would need the macro body as a signal
  of intent, and a body is not one: `{#1}` and `\textcolor{gray}{#1}`
  declare the same authorial role, so editing a body would silently re-bind
  a design token document-wide. A palette entry is re-bound in one place
  (`\palette{ muted = … }`) or it is not a token.
- **Stated and protected.** `every_role_is_invocable` (bundle keys lex and
  collide with no built-in; the document door already refuses both) with
  the executable `roleInvocationChecks` oracle over the real resolution
  order; `role_resolves_at_one_site` (`find?` is the single reader;
  `resolve`'s black/white atoms now yield to a declared entry — before,
  PDF ink and the HTML variable diverged on a palette naming `black`);
  `role_use_is_palette_dependent` + `role_use_names_its_token` (a use
  references `var(--r, …)` and the `:root` block follows the palette — the
  contrapositive of frozen-at-authoring-time; scoped to the sRGB face,
  since `cssColor` deliberately never reads the CMYK rider). The oracle
  caught a live interception: the native `\theme` never set Compat's
  `themed` flag, so `\alert` in a natively-themed deck lost the bundle's
  alert role.
- **The shadow is named (W0342, degraded).** `\newcommand{\muted}` over a
  palette declaring `muted` replaces a role that adapts with a value that
  cannot: the palette stops reaching those words, and the contrast judge —
  which sees a role use only because it resolves through the palette —
  goes blind to them; an unseen colour cannot fail a contrast check.
  Judged against the final palette, so declaration order cannot hide it;
  shadowing anything else stays silent, as in LaTeX.
- **The class hook (the classhook audit, landed).** `Inline.role` /
  `Block.role` wrap the expansion of a ≥1-parameter document-defined
  command, so `HtmlDoc.emit` of `\muted{x}` and of `x` are no longer
  byte-identical: `<span class="u-muted">` / `<div class="u-entry">`,
  injective (`roleClass_inj`), disjoint from every engine class
  (`roleClass_engine_disjoint` over the grep-maintained registry), one
  class token over the command-name alphabet (`roleClass_single_token`),
  census-transparent (`role_plaintext`, rfl), layout-transparent
  (`role_transparent_layout`; the block collector's half is the
  `roleLayoutChecks` PDF byte-identity oracle — its match resists equation
  generation). The two halves compose: a name the palette knows resolves
  as a role and adapts; a name it does not becomes an addressable class.
- **Colour only, decided.** A palette entry stays `name → Color`: every
  consumer today (contrast judge, `var(--name)` emission, PDF ink) reads
  exactly a colour, a `RoleStyle` with one populated field is the
  one-caller abstraction AGENTS forbids, and the class hook already lets a
  stylesheet attach weight or a paired background to a role
  (`.u-quiet { font-weight: 300 }`) with no engine change. What makes it
  cheap later: one resolving site (`find?`), one IR carrier
  (`.colored name`), one emission line (`paletteVar`) — a richer role
  value touches three named places, each under a theorem that would fail
  loudly.

2026-09-18 — the generalize slice: the theorem atlas's collapses, the
derive-not-tune derivations, two live defects closed, and a gate.

- **Two defects, one class, closed.** The contrast judge had drifted from
  the page it judges: `Contrast.headingCx` re-spelled the sectioning sizes
  as absolute 14/12 pt while `Layout.sectionSize` sets them from the type
  scale — at a 9 pt base the page sets a section at 12.96 pt (not WCAG
  large-scale) while the judge tested a phantom 14 pt bold (which is), so
  the judge passed text the page fails; verdicts agree at the 10 pt base,
  which is why nobody saw it. `headingCx` now reads `sectionSize` itself
  and `contrast_judges_what_layout_sets` pins the agreement — the drift
  reintroduced fails the theorem at build time, and a 9 pt fixture test
  beside it. And D1, the `icbrt_spec` class: `\page{ vmargin = -5mm }` was
  reachable and outside both band theorems' `0 ≤ vmargin` hypothesis; the
  shared key inequality is one hypothesis-free statement
  (`band_reserves`), so factoring it deleted the hypothesis — a
  strengthening for free. D2's gap closed from the guard side: E0323's
  fontsize check now requires the 1 pt floor `heading_hierarchy` holds
  above (below it the property genuinely fails; the statement stands).
  No diagnostic for a negative margin: the geometry is well-defined ink
  into the trim, a choice real designs make.
- **One overlay walk.** `shadeBlocks` was exactly `dimBlocks`' everything-
  pending mode, so the two walks are one algorithm with a `pending` flag
  that flips at `.step`: nine defs and the nine-theorem shade conservation
  family fold into the dim family, and a future `Ir` constructor owes one
  arm and one census case here, not two. The conservation shape is named —
  `Ir.Conserves census f := ∀ x, census (f x) = census x` — and the
  top-level walk theorems restate as instances.
- **Contracts quantify over the shipped list, finished.** The per-bundle
  `moloch_/plain_{contract,covered,cover_monotone}` were `builtin`-
  subsumed or one migration behind; `builtin_palettes_contract` and
  `builtin_covers_monotone` complete the rule (net −4 statements), and a
  third bundle now enters every contract by being added. The rule is an
  AGENTS convention line.
- **Derived, not tuned.** The HTML headings emit the scale's own
  LARGE/Large/large (h2 was already a rounding step off), the standout
  its Large step; both backends read one leading ratio (`Ir.leadingMilli`)
  and the math grid's baseline is `leadingFor` itself; the PDF descriptor
  states the parsed CapHeight and the post table's italicAngle (a host
  face declaring −11° exposed the −12 guess as wrong by a degree); the
  frame-title bar's negative margins and radius are computed from the
  slide box's own padding and the nested-corner rule. The HTML body
  leading moves 1.55 → 1.45: outside Butterick's 120–145 % band and
  undeclared before, at its top and pinned by `body_leading_in_band` now.
  The marker gap is `\labelsep` (classes.dtx, .5em; was an eye-picked
  0.4 em). Read against the primary source, the audit's "worst number"
  was moloch's own: 0.7875\linewidth is the section-page minipage width
  in beamerinnerthememoloch.dtx, and the 1 pt progress bar and 0.5 pt
  separator are its defaults — cited where they stand now, a reminder to
  check the source against the code before trusting either.
- **The gate.** The pre-commit hook scans the whole core tree for public
  IR-to-IR walk entries (def taking and returning `Array Block`/`Array
  Inline`); each must ship a theorem named with a registered conservation
  suffix (`_text` as a `Conserves` instance, `_covers`, `_id`) or the
  one-line refusal `-- conserves: none — <why>` beside the def. Proved
  load-bearing by staging the violation; `fillTemplate` (a splice) and
  the `setAlt` walks (an alt-only edit outside the census) are the escape
  hatch's first honest users. The suffix registry lands in AGENTS.md.

2026-09-18 — icons, the pinned control, and the declared reveal: the
site-polish slice, three pieces the site port asked for.

- **Icons are glyphs in a declared face with a required text alternative**
  (`Ir.Inline.icon`). The fontawesome5 spellings work as the package
  defines them — `\faGithub`, `\faIcon{arrow-up}`, the starred `-alt`
  forms — from a generated table (`FaData`, 1457 icons out of
  fontawesome5-mapping.def, CTAN 5.15.4, joined with Font Awesome's own
  `label` metadata; `scripts/gen-fa-data.lean` regenerates). No second
  font mechanism: the icon scalar rides `docScalars` (its own gather
  walk, since an icon's `plainText` is its label) into the per-scalar
  fallback precompute, so the face is whichever declared or installed
  face covers it — TeX Live's FontAwesome.otf serves a host that has it,
  a shipped `\fonts{dir=}` face serves hermetically, and no coverage is
  the ordinary E0405. Landing on the fallback face is the designed path,
  so no W0009. The invariant, decided before the code (WCAG 2.2
  SC 1.1.1): an icon without a text alternative is unrepresentable — the
  constructor requires the label, `\faIcon[label = ...]` overrides it —
  and HTML hides the PUA glyph from AT while naming the wrapper
  (`role="img"` + `aria-label`; WAI-ARIA 1.2 makes an img role's children
  presentational). The markdown twin renders the label. E0340 names an
  unknown icon; W0110's meaning widened to any command's unmodelled
  option. The corpus ships an invented "Example Icons" face (five original
  shapes at the FA codepoints, CC0, `scripts/gen-test-icons.py`), so
  `icons.tex` builds anywhere; its census row asserts the five glyphs as
  shipped ink, and `censusChecks` mirrors the driver's precompute for PUA
  scalars only — anything wider would silently upgrade the stand-in
  degradations `listChecks` pins.
- **A nav declares its label and its pin** (`Ir.NavSpec`, `Ir.Pin`).
  `label` is the landmark's accessible name (ARIA APG Landmark Regions:
  a repeated role needs unique labels), and W0325 counts only unlabeled
  navs now — the label mechanism it named as missing exists. `pin` is
  fixed positioning at a declared corner and offset (CSS Positioned
  Layout 3 §3.3), read by the HTML backend alone; the PDF and markdown
  walks read the body only, so a printed page ignores a pin by
  construction. `px` joined the unit table as the CSS pixel (1px =
  1/96 in, CSS Values 4 §6.2; relation in `unitScale_consistent`).
- **The reveal is declared, and the script boundary opened one notch** —
  a revision of the 2026-09-17 "no script emission" decision, on
  evidence: MDN browser-compat-data (2026-09-18) has
  `animation-timeline: scroll()` in Chrome 115+ and Safari 26+ but
  Firefox preview-only, and the user's reveal must work in release
  Firefox. `reveal = scroll | <length>` on a pinned nav ships, judged
  over the emitted tree: the `@supports` scroll-driven CSS (declarative
  where the platform has it) and a constant script fallback through the
  typed tree's `Node.script`. Boundary guarantees: the payload is an
  engine constant — no document byte enters it, it carries no `<`
  (`revealScriptClean`; the theorem form did not close under kernel
  reduction of `String.contains`, so this is a test and says so) — it
  ships only when a reveal is declared, and it exits where the
  declarative form exists, so no browser runs both. The reveal fades
  opacity/visibility only — a fade is not motion animation, so SC 2.3.3
  stays with the guarded `motion` key — and with neither script nor
  scroll-timelines the control is always visible: degradation, never
  breakage. `--math-boundary` remains the only other script path.
- Costs: bench medians 87–96/286–298/404–409 ms over two runs
  (paragraphs/lorem/underline) vs 80/285/400 recorded above — within the
  run-to-run spread on a loaded host, so the icon gather walk and the
  tree-facts extension are free at these sizes.
- Two findings the port surfaced, both fixed the same day: the markdown
  twin's served name is declared (`\output{ md = "llms.txt" }` —
  llmstxt.org fixes the name, and the head's alternate link must name the
  file as served; the port's build script renamed it after the fact and
  silently broke that link), and a face the document ships outranks the
  host's in the fallback picks (`FontDb.fallbackPicksPreferring`; this
  host's TeX Live FontAwesome.otf had displaced the port's shipped Font
  Awesome 5 faces, so "a document that carries its fonts renders the same
  on every host" was false exactly for fallback-resolved scalars).

2026-09-18 — zero diagnostics has a definition, and `--werror` enforces
it: **a document that declares its intent (an `\allow` for an accepted
loss, a `\palette[decorative]` for a deliberate low contrast) and uses
only supported constructs emits nothing; a document that does not is told
exactly what to write.** Landed in this slice: `--werror` (exit 1 on any
warning; output still written; the exit contract is one total function,
`Cli.exitFor`, the driver and the test matrix both read), and acceptance
now means silence — `\allow` and `--best-effort` downgrade to a note, so
an accepted loss is neither an error nor a warning anywhere, `--werror`
included, and the always-printed `accepted:` summary is what keeps
acceptance visible. The reference deck's remaining items were each
resolved to a state, never deleted: tikz and appendixnumberbeamer are
native package loads (the loss, where one occurs, is named at the
construct — W0334/E0333 at the picture, W0301 at `\appendix`);
`\usefonttheme{professionalfonts}` and `\setbeameroption{hide notes}`
ask for what the engine already does and agree silently;
`\ifdefined` resolves from the document's own definitions (N0114 names
the branch taken; any other `\if…` head keeps the skip-whole W0104);
`\directlua` reads as a refusal with `\allow{W0104}` as the declared
acceptance; `\def` stays mapped to `\define` in its help. W0315's
decorative escape now also matches an anonymous colour by value, so the
help's printed line is the line that silences it (it previously silenced
nothing for a mixed colour — the test now derives the declaration from
the fired help, so they cannot drift). W0315/W0338/W0005 on the
reference documents are the documents' own content and stay; the four
W0009 glyph fallbacks stay one-per-scalar pending the math-font slice,
which may resolve that chain differently (coordinate before aggregating).

2026-09-18 — the math face matches the body by default: the paired face,
scaled so x-heights agree. The user's oldest annoyance — "the font never
really matches the rest, and we need to do gymnastics to align the fonts" —
is now the default behaviour, no knob. Design (from the math-font-match
review, its rejected alternative recorded there): a document with a body
face and a formula gets the body family's *designed math companion* when
the host scan has one (`FontDb.mathCompanions`, sourced rows only — GUST
e-foundry for the TeX Gyre and Latin Modern pairs, stixfonts.org, CTAN
for Libertinus/Garamond-Math/Erewhon Math/Fira Math, licences checked,
unverified rows omitted), else the first MATH-table face under the one
documented order (`faceLt`, lifted out of `fallbackPicks`), and only a
host with no MATH face at all degrades to source text with W0003 as
before. `\fonts{ math = ... }` stays the override and always wins. The
splice alternative — body letters inside formulas — was examined and
rejected on the engine's own architecture: math letters are Mathematical
Alphanumeric scalars text faces lack; italic correction, math kerning and
top-accent attachment live only in the math face; the seam would move
inside the formula (Greek beside Latin in one identifier role); and
MathConstants are stated in the math font's own x-height and
rule-thickness terms, so constants and glyphs are designed together.

Either way the face is *rescaled so the math x-height equals the body's*
— fontspec's `Scale=MatchLowercase` rule as one integer expression
(`Math.mathSize`), the metric being the measured ink top of the face's
own 'x' (`Font.xInkTop`, lazy; OS/2 sxHeight lies in some fonts), else
sxHeight, else half the em — the existing metric order, clamped into
(0, upem] (`Font.xHeightOptical`). Theorems, not taste: the scaled math
x-height never exceeds the body's (`mathSize_matches`) and falls short
by at most one sp (`body_xheight_le_mathSize_next`) — the tolerance is
the division quantum of the sp arithmetic, nothing else. Measured on
this host: TeX Gyre Pagella → Pagella Math is the identity (both 469
per em, residual 0 sp — a designed pair matches by design); Source
Serif Pro → Fira Math at a 10 pt body sets math at 9.01 pt (x-height
345374 sp before, 311295 sp after against the body's 311296, residual
1 sp), and the pixels show the formula's x at the sentence's optical
size where it sat visibly larger before.

One fallback mechanism, not two: the scalar census now walks formula
bodies (the same traversal, `ScalarAcc`), so math scalars enter the
driver's existing per-scalar precompute; a scalar the math face lacks
sets from the precomputed face at the math size with W0009, and only a
scalar no installed face covers stays E0405. Assembly paths — grown
delimiters, radicals, display operators — never split across faces. The
companion pick is scan-order independent as a theorem
(`pickCompanion_set_eq` via `leastBy_set_eq`: the pick is a function of
the set of installed faces; `faceLt`'s order axioms are hypotheses since
it bottoms out in string comparison, and the suite checks them over the
shipped faces). The engine picked a face the document did not name, so
it says so once: N0016 (loss `info`), gated on the document actually
reaching math (`Layout.docMathScalars`); `leantex fonts` reports each
family's installed companion with the x-heights the match reads and the
measured stems — stem width is measurable (`Ink`) but no authority
publishes a mismatch threshold, so it is a report, never a gate.
Fixtures per branch: `math-companion.tex` (Fira Sans → Fira Math, both
shipped, OFL), `math-first.tex` (no row → first MATH face); the census
resolves an undeclared math face exactly as the driver does. The suite
passes with the host font directories tmpfs-emptied. Reference deck and
résumé: diagnostic profiles unchanged (the deck's four W0009 mono
substitutions resolve to the same face). Bench: 85/285–301/400–405 ms —
paragraphs.tex sits ~8 ms above its recorded band because its two
formulas now render (companion face parsed, math laid out) instead of
degrading to source text; the mathless benches are in band.

2026-09-17 — the caption seam is named before it is fixed: W0339
(`pending`) fires when a page break lands exactly between a float's
object and its caption — the table slice's largest honest gap, previously
silent. The mechanism is a `tie` op the float arm places on the seam
(both caption sides); placement consumes it at the next line, table rule,
or picture, and the break path reports it. The keep-together itself —
moving the object whole — is still owed to the float milestone; when it
lands, the code retires with its last emission site, as W0308 did.
Witness and seam test sweep a `\vspace` in 3pt steps across the page
bottom, so the firing input holds under any face's metrics.

2026-09-17 — M8's table story: booktabs is the layout, not a package, and
float/caption spacing is declared, rhythm-held, and enforced. The user's
two asks, in order of stated value: consistent spacing first, booktabs
second. The IR gains `.table` (columns from the spec, rectangular rows,
typed rules) and `.float` (figure/table, caption on its source side) with
every walk arm explicit and the conservation theorems over them
(`shadeTableRows_text`, `dimTableRows_text`, `keepForOne_covers`,
`textLeaves` arms). Design values are sourced constants in Ir —
booktabs.dtx's documented defaults (`\heavyrulewidth` .08em,
`\lightrulewidth` .05em, `\cmidrulewidth` .03em, `\belowrulesep` .65ex >
`\aboverulesep` .4ex, `\cmidrulekern` .5em, `\defaultaddspace` .5em),
classes.dtx's `\tabcolsep` 6pt and `\doublerulesep` 2pt — each held by a
theorem: `rule_weights_ordered` (the three-weight hierarchy),
`rule_seps_ordered` (a rule binds to what it closes), and
`caption_gaps_rhythm`, the user's complaint stated as an invariant: the
caption gap is the half rhythm unit (6pt), the float gap the full unit
(12pt, exactly LaTeX's `\intextsep`), quantized to `parskip` so spacing
cannot drift per document — no authority fixes the caption gap's absolute
value, so the statement takes the weakest sufficient property (ordering +
quantization) rather than an invented threshold. Rectangularity is the
alignment grid's statement shape restated for tables
(`padTableRows_rectangular`, `padTableRows_cells`; `MRows.pad_rectangular`
is monomorphic over math's own row type, so the shape transfers, the
theorem does not — one property, two statements, noted rather than
hidden). Layout places rules flush (`noInterline`, as TeX ignores
`\prevdepth` after an `\hrule`) padded by exactly their declared seps;
cells set through the column machinery so a row advances by its tallest
cell. Both backends read the same constants: HTML draws the rule classes
from `Ir.heavyRuleWidth` and friends as CSS custom properties with the
booktabs defaults as fallbacks; markdown sets the pipe table. Codes:
W0337 (ragged row padded/widened), W0338 (table wider than the measure,
in points) — drafted as W0336/W0337, moved once when the diagnostic slice
landed E0336 on main (the registry as landed wins a number race);
W0308 (tables as plain lines) lost its last emission site and
left the registry. `\hline` maps to the light rule, `\cline` to an
untrimmed `\cmidrule`, `\multicolumn` keeps its text and W0337 names the
lost span. Fixtures `tables` (the user's p-column shape, captions both
sides, a figure) and `tables-ragged`, each with census rows; rule extents
judged from `Layout.Out` in `tableChecks` (toprule = bottomrule extent,
cmidrule strictly inside — an executable check, not a theorem: the
extents live in `collectTable`'s local arithmetic). Owed, named here so
the next slice starts where this stopped: caption–object inseparability
across a page break (nothing prevents the break today; the page machinery
has no keep-together yet), the table width-sum-no-drift statement as a
theorem (needs `colX`/`tableW` extracted from `collectTable`),
`\multicolumn` spans, `\addlinespace`/gap rules and cmid trims in HTML,
per-rule `[width]` overrides (declined deliberately: weights are the
design), and `p`-cell vertical alignment (`m`/`b` set as `p`).

2026-09-17 — the diagnostic voice is gated, not groomed. Real output
carried `error[W0307]` (a warning-lettered error), `see PLAN.md` (a file
the reader does not have), and milestone names (`M6`, `M8`). Three
mechanisms, in order of strength. (1) The code letter now derives from
the declared `Loss`: `DiagCode.spec` carries digits only, `DiagCode.code`
is the one site that prepends `Loss.letter`, and
`DiagCode.code_letter`/`Diag.of_code_letter` state the rendered prefix's
two halves agree — `error[W…]` is unrepresentable. Renumbered where the
letter had drifted: W0313→E0336, W0324→E0334, W0004→E0405,
W0501→E0502, N0101→W0101, N0105→W0111 (retired numbers stay retired;
W0313's first landing as E0333 moved to E0336 when the picture slice
took E0333 on main — the registry as landed wins a number race).
W0307 itself kept its letter: `pending` (declared content absent but
owned by a milestone) landed as a warning by design, so the exhibit
resolved by reclassification, not renumbering.
(2) Every registered code has a firing witness (`diagWitness`, an
exhaustive match: a new code does not build until it names the input that
fires it) and every fired form renders into
`tests/golden/diagnostics.txt` — the whole voice reviewable in one diff.
The driver's fourteen messages moved into pure builders
(`Cli/DriverDiag.lean`) to be reachable there. (3) A voice lint judges
every fired message and help in `lake test`: no repo-internal reference,
length bounds taken from named exemplars (message ≤ 121 from W0315, help
≤ 181 from E0328's generated list), a help carries an action or does not
exist, no terminal period, sentence case, constructs quoted in single
quotes, no code named in prose that the reader cannot look up (W0013 and
E0329 exempt: they quote the user's own `\allow` entries). The pre-commit
hook rejects `PLAN.md`/`AGENTS.md`/`LeanTex/`/milestone tokens inside
string literals at the source level (`repoRefInString`). The rewrite that
followed is mechanical fallout: milestones and `see PLAN.md` deleted from
every message, helps that named no action dropped or given a spelling.

2026-09-17 — covered means the same colour, quieter. Covering used to
erase a colour: `shadeInline` repainted every nested `.colored` run to
the one palette `covered` constant, so a covered alert and a covered
example were the same grey (ΔEOK = 0 by construction; measured hue shift
149.0° for moloch's alert) — and the constant's own comment cited
Material, whose 38% disabled state is an *opacity*, per colour, not a
repaint. Cover is now a function: `cover c` keeps `c` at the bundle's
fraction of itself over the surface, mixed in Oklab (`Core/Oklab.lean`,
pure Nat/Int — the table-inverted transfer function makes the 8-bit
answer exact; `scripts/oklab-roundtrip.lean` checked the identity over
all 2²⁴ inputs, 0 mismatches). Because both shipped surfaces are exact
greys, hue preservation and chroma×fraction are algebra, not tolerance:
`Oklab.hue_preserved` / `chroma_scaled` / `toward_surface` are theorems
over the engine's own `labMix`; `icbrt_spec` bounds the one nonlinearity.
`Design.cover` is the one resolving site; the walks take `Ir.Cover` and
keep their shape, so `dimBlocks_text`/`shadeBlocks_text` survive.
`covered = <n>\%` declares the fraction per bundle — exactly beamer's
`\setbeamercovered{transparent=<n>}`, now lowered to it — and a colour
value stays accepted as the cover of uncoloured runs.
`Contrast.coveredContract` ranges over the per-colour cover of every
text role, not `fg` alone: at 38% moloch's alert/example reach only
2.89:1/2.75:1 against their active forms (under SC 1.4.11's 3:1), so
moloch declares 31% — the largest closing fraction, a finding about the
bundle, not a weakening of the contract. `coverMonotone` pins
cover∘cover quieter per bundle; the general integer statement needs
luminance monotonicity through the whole pipeline — a refactor this
slice does not claim, tracked here. Scope held: covered ONLY, not the
`!` mixes — cover is engine semantics, `!` is xcolor's declaration
language, and Contrast.lean pins its sRGB model as a fidelity anchor
(moving it would silently restyle every bundle: muted 4.79→5.24,
progressbg #CBC0B6→#C2B5AD). Verified: build --wfail, tests, the
exhaustive round-trip oracle, integer output byte-identical to the CSS
Color 4 float reference on every shipped role (no clipping; at 38%
chroma ×0.380–0.382, 8-bit hue shift ≤ 0.55°, 0 pre-quantisation by
theorem), themed pages rastered and looked at (covered alert dims
orange—or the fixture's declared pink—covered example dims teal, never
one grey), bench medians 74/281/393 ms (baseline 79/290/396, noise).

2026-09-17 — two mirrors closed: the head's missing band (F2) and the
contract's blindness to a defaulted pair (F3), one slice because both are
an invariant that existed for one case and not its reflection. F2: the
footer's reservation had no top analogue — `headY = vmargin/2 + ascent`
with nothing subtracted from the body area, so a tight declared `vmargin`
collided the head with the first body line (the numbering slice's owed
item above). The fix is the footer's own mechanism reflected, not a
second one: `headBandFor` feeds `footBandFor` the head's ink extent
below its half-margin line (ascent + descent, where the footer hangs its
ascent alone), `Geom.bodyTop` mirrors `Geom.bodyBottom`, the one top-edge
read (`B.placeLine`'s `firstY`) goes through it, `bodyTop_clears_head`
mirrors `bodyBottom_clears_footer` with the same key inequality, and
`slides_lines_survive_bands` proves both bands leave Tantau's 10–20 lines
at the slide defaults for any running line up to two em of ink — a bound
no spec provides (OS/2: "It is not a general requirement that
sTypoAscender − sTypoDescender be equal to unitsPerEm"), so it is a
declared coverage choice, with the shipped test faces pinned under it.
The headroom fixture collides before the fix and clears after (rendered
and looked at, both states); every other golden is byte-identical — at
the default margins the band is zero. F3: `docDiags` judged only pairs
the document spelled, so a declared dark page with the ink left defaulted
shipped black-on-dark undiagnosed. The fix judges the *effective* pair:
`effectivePair` reads the resolved design — and Layout now reads the same
`Design.ofDoc` fields for its doc-level ink, page fill, and muted, so
there is one resolving site (`judged_pair_is_shipped` pins fg
definitionally) — and `docDiags = effectivePairDiags ++ declaredUseDiags`
puts the judgment on a straight-line path, which is what lets
`defaulted_ink_cannot_escape` quantify over every document: a failing
effective pair that is not declared decorative always produces a
diagnostic. A declared illegible fg keeps W0315; the defaulted-ink case
is its own code (W0330, degraded) because its remedy differs: declare the
ink, not the intent. Reintroducing the blindness breaks the theorem —
the build fails before any test runs; with the theorem deleted too, the
W0330 test catches it. An undeclared document is never diagnosed for the
proven default pair.

2026-09-17 — severity stops being a choice: it derives from a declared
loss. The user's charge ("how come unsupported features are not Erroring
out? … looks like you are generally taking shortcuts") audited out to one
root cause: `Diag.severity` was an open field every call site picked ad
hoc, so nothing distinguished "content degraded but visible" from "content
silently gone" — fourteen sites shipped dropped content as warnings or
silence, and Principle 8 promised what W0307/W0104/W0501 did not deliver.
The old principle's wording was the original shortcut; it is rewritten
above to state the real guarantee. The mechanism now: `DiagCode` is an
inductive (one constructor per code — this supersedes the string
`diagRegistry` the entry below describes; the registry's checks survive
pointed at the type), each code declares a `Loss`
(dropped → error, degraded/config → warning, info → note), and `Diag.of`
copies the loss's severity, so a free severity is unrepresentable — the
theorem `(Diag.of c …).severity = c.loss.severity` is `rfl`, and the hook
rejects a `severity :=` outside Diag.lean. The escape hatch landed before
the promotions: `\allow{codes}` in the preamble accepts named losses,
`--best-effort` accepts all, with three teeth (unknown code errors E0329,
never-fired entry warns W0013, acceptance always prints). Promotions:
W0307, W0501, W0313, W0004 → error; N0101/N0105 → warning; \titlegraphic
(E0112) and a content-carrying \setbeamertemplate body (E0111) leave the
config warning they rode on; the silent sectionRule else-arms (E0113) and
the five "burned" option sites (N0102/N0103) are registered; the four
meaning-changing `inert` entries (raggedright, sloppy, selectlanguage,
pagestyle) warn from `configSkip`. Expired audit rows, checked against
main before promoting: W0107 \includegraphics and \logo — both since
implemented. Both real reference documents still build byte-identically;
the deck accepts W0307 for its M8 tikz hatch with one `\allow` line.
Integration with the web slices (which own W0320–W0327): the layout-only
skip code is W0329 here; the inductive surfaced a live string-registry
collision on main — W0319 meant both "unknown theme" and "running content
wraps" (the registry check passed because the string was registered) —
the wrap diagnostic is now W0328; and W0324 (ifbackend content addressed
to no backend) is a dropped loss under this entry's own test, so it
promotes to error with the others, `\allow{W0324}` accepting it.

2026-09-17 — a backend divergence is declared or reported: the
backend-agreement slice (FINDINGS F1, F4, F5). The obligation behind all
three findings — the same declared fact renders the same way in every
backend, or a diagnostic names the difference — now has a mechanism: an
agreement tier in Tests runs over every golden fixture, judging the
footline's slot pair from `Layout.Out` against the slide footers off the
typed HTML tree (`HtmlDoc.emitTree`, split from `emit` so the tree is
judgeable before render), and every declared list marker against what
`::marker` can express; a mismatch passes only when a diagnostic from
the naming set stands (W0007 physical furniture omitted from HTML,
W0331 marker substituted, W0332 sequences mixed). Per fact, both
backends now consume one resolving function, so they can only diverge
by rendering, never by resolving: `Ir.Chrome.footSlots`/`footLine`
(moloch's own footline row, beamerouterthememoloch.dtx:216-228 — left
slot, `\hfill`, right slot, the fill unconditional) and
`HtmlDoc.markerCss?` (CSS Pseudo-Elements 4 §4.1: color and the font
properties apply to ::marker, so a colour and a size step ARE
expressible and the honest degradation boundary is arbitrary inline
content). F5's PDF empty-left collapse was `runLine` discarding leading
glue via `lineStart` (written for broken-off paragraph lines; a running
line's leading fill is content) — theorems
`footSlots_right_ignores_left`/`footLine_eq_slots` state the slot
layout is a function of the declaration. F1's residual (a marker HTML
cannot express) is W0331, warning, naming the backend and key;
`markerCss?_text` proves expressed content is exactly the declared
characters. F4 (a `\framefoot{p. \pagenumber}` beside the theme's frame
slot) is declarable, not prevented: `Doc.chromeDeclared` records the
author naming their own `\chrome`, undeclared mixing warns W0332
naming both sequences, and the fusion direction is closed by theorems
(`frame_sequence_carries_no_physical`, `substPage_id`,
`substPage_leaves_frame_slot`: the physical pass rewrites exactly the
placeholders, and the frame slot's rendering carries none). The census
grew a per-line width so a fact can judge a right edge (fixtures
footer-left, footer-mixed, marker-styled, marker-content). Grade of the
strong agreement form: blocked — the two sides live in different result
types, so agreement-by-one-function is proved and the artifact-level
equality is held per fixture by the tier; recorded here so the next
slice extends the tier instead of trusting the construction.

2026-09-17 — fixed positions and a declared priority order: the F5
correction. The user corrected the entry above's flex-row reading ("no,
always right aligned, sometimes things can be painted over (eg dropped),
since page number is lower priority"), so the footline is not one line
whose slots land where the content pushes them — each slot has a fixed
position, a function of the declared layout and the page geometry alone,
and when two boxes would overlap the lower-priority slot yields in
place: painted under, never moved, the yield named. Mechanism:
`Ir.Chrome.footBand` supersedes `footLine` (the pair resolver
`footSlots` and its theorems stand; `footBand_projects` replaces
`footLine_eq_slots` — both backends still resolve one pair). A slot's x
is `Layout.bandSlotX (side, geometry, own width)` — the other slot is
not an argument, so content-independence of position holds by
construction, and `bandSlotX_right_pinned` proves x + w is the right
margin for every width (the folio's anchor is a constant of the
geometry; the empty-left case is deleted, not fixed). The order:
`ChromeSlot.priority` — frame number low, section title above it, a
`\framefoot` note above both — `priority_injective` proven, and
`BandSlot.rank` breaks the one representable tie (the same datum on
both sides) by side (`rank_ne_of_side_ne`), so which slot yields is a
fact of the declaration. Yielding is paint order: the PDF pushes the
lower rank first (under), the HTML carries `z-index` = rank per span
with each span pinned to its declared edge; both report W0333
(degraded — the ink is present, not as declared) naming the yielded and
the displacing slot; the per-slot wrap keeps W0328. Verified on the
reference deck: the frame number's xMax is 425.197pt (the right margin)
on the empty-left page and the two section pages alike, where the
empty-left page previously collapsed to xMin 28.35. Fixture
footer-collide forces a collision with an unbreakable overlong note;
bandChecks holds the number's box byte-identical across empty, filled,
and colliding left slots and pins the yield direction both ways. Grade:
position-pinning and order-totality are theorems; content-independence
is by construction (argument absence) with the fixture family as its
executable face; yield-reporting is a test (the single collision site
emits the diagnostic in the same branch).

2026-09-17 — declared once, derived everywhere: the web metadata slice
(site-port gaps 1 and 7). `\pdfmeta` grows `url`, `image`, `favicon` — an
extension of the one `Ir.Meta` record, not a second declaration — and each
surface derives its own rendering: the HTML head gets `rel=canonical`
(RFC 6596), `rel=icon`, `rel=alternate type=text/markdown` to the llms.txt
twin (name passed in by the driver, which is the one who knows it),
the Open Graph set plus `og:type=website` (ogp.me: og:url required,
website its own default type), `twitter:card=summary` (X falls back to
og:* for the facts), and a JSON-LD `WebPage`; the PDF reads `url` into XMP
`dc:identifier` (ISO 16684-1 §8.3); the markdown twin keeps its preamble.
og:title and `<title>` are the same fact rendered twice — the drift the
site port measured ("Experience" vs "Professional Experience") is now
unrepresentable, pinned cross-backend by `webMetaChecks`. JSON-LD goes
through a certified escaper, never a blob: `escapeJson_no_quote` and
`escapeJson_no_lt` are theorems in Html.lean, and the second composes
with the raw-payload guard (no `<` means no `</script`, so the data block
survives verbatim). `Node.script` carries attrs now; a script with a
non-JS type is a data block (HTML §4.12.1), so the no-script rule —
which is about behaviour — holds. Owed, recorded here: a typed
`\person`/`\organization` declaration rendering to full JSON-LD (today
only fields the existing declarations carry are emitted), and Unicode
NFC normalisation of slugs (UAX #15) — two spellings of `é` still make
two anchors, stated in `slug`'s docstring rather than hidden.
Slugs themselves (gap 7): the fold to ASCII degraded accented and CJK
anchors and could silently merge two distinct titles. `slugChar` now
keeps any non-White_Space scalar (HTML §3.2.6 forbids only ASCII
whitespace in an id; WHATWG URL §4.3 keeps the fragment addressable) —
`slug_no_whitespace` proves that half of the id contract — and
`sectionize` assigns ids uniquely against the set of *assigned* ids,
which also closed a real hole: a title whose own slug was `noise-2`
used to collide with the number handed to a repeated `Noise`. Two
distinct titles that still fold together warn as W0327 and take
distinct ids; a repeated identical title numbers quietly. Each
regression test was shown failing with its defect re-introduced.

2026-09-17 — behaviour is declared, and a backend can decline: the web
surface's three gaps (site-port gaps 3, 4, 5), one slice because the nav
is the case that needs the conditional and its hover states are the
interaction states.

- **`{ifbackend}{html,md}`** (`Ir.Block.only`): content addressed to a
  subset of the backends. The engine still elaborates once; each backend
  resolves the conditional at its own entry with `Ir.keepFor`, the one
  drop site. The conservation theorem `Ir.keepFor_covers` (proved): with
  every conditional keeping at least one backend along its nesting path
  (`Ir.orphanFree` — path intersection, so `{pdf}` nested in `{html}`
  addresses nothing), every declared text leaf survives in some backend's
  kept view — stated over the `plainText` census like the overlay
  conservation theorems, lifted to whole leaves because `keepFor` drops
  whole subtrees. Elaboration walks the same intersection and fires W0324
  exactly where `orphanFree` goes false (pinned by test, not theorem —
  `Elab` is monadic); W0323 names a typo'd backend.
- **`{nav}`** (`Ir.Block.nav`): a landmark, not a widget — `<nav>` in
  HTML, a transparent group in the PDF and the markdown twin. Two
  contracts judged over the *emitted typed tree*, never the IR (a
  conditional may keep a nav on one surface only): at most one unlabeled
  `<nav>` per page (W0325; ARIA Authoring Practices, Landmark Regions:
  a repeated landmark role needs unique labels, and no label mechanism is
  modelled yet) and every in-page link resolves to an emitted anchor
  (W0326, naming the anchors; `#` and any-ASCII-case `#top` exempt per
  the HTML spec's "select the indicated part").
- **Interaction states are style keys**: `hover`, `focus`, `motion` on
  `\style`, beside the keys already there; they style the element's links
  (`nav` is styleable now), keep token spelling in CSS, and the PDF reads
  none of them. The invariant: a declared motion carries its
  reduced-motion form *by construction* — WCAG 2.2 SC 2.3.3 (Animation
  from Interactions, technique C39) over CSS Media Queries 5 §12.1.
  `HtmlDoc.motionCss` is the engine's only `transition:`-spelling site
  (`motionSiteChecks` scans the tree, the `diagChecks` shape), appends
  the guard unconditionally, and `motionCss_guarded` proves output =
  rule ++ guard — deleting the guard fails the build, observed once. The
  guard travels per declaration because `css = none` ships no base sheet.
- The boundary decision stands: declarative platform, no script emission
  (`--math-boundary` remains the only script path). Nothing else became
  declarable here; a burger-menu disclosure is `<details>`, content the
  existing tree can carry when a document asks.
- Costs: bench medians 80/285/400 ms (paragraphs/lorem/underline) vs the
  77/275/408 recorded above — noise, so `keepFor`'s extra pass is free at
  these sizes. resume/deck/talk rebuilt to all nine outputs before and
  after: byte-identical.
- Found by looking at the rendered fixture, not by the suite: a document
  palette name that collides with a base-stylesheet token (`ink`)
  silently restyles the page — recorded, not fixed; a token-namespace
  question for the Design work.

2026-09-17 — compound engineering: the obligation table, and the gates
that make it mechanical. A user found six defects by looking at one page
while every check was green; the root cause was not six bugs but that
nobody knew, when adding a feature, which invariant that kind of feature
owes. The knowledge is now a table (condensed in AGENTS.md, full rows
here), and every row that is checkable today is a gate that fails the
commit or the suite rather than a rule an agent can forget. Derived from
the three architecture audits (faithfulness, provability, design) and
the defects themselves.

The rows, each with its why:

- An `Ir` constructor owes an explicit arm in every IR-to-IR walk and
  both backend consumers — no wildcard. The walk catch-alls were how
  covered content could ship undimmed; a future constructor (`.image`,
  M8) must answer everywhere before it compiles. Enforced: the ten
  catch-alls (`Ir.fillOne`, `maxStepBlock`, `maxStepInline`,
  `shadeBlock`, `shadeInline`, `dimBlock`, `dimInline`,
  `unwrapItemStep`; `Layout.substPageOne`, `raggedItems`) are spelled
  out, so the compiler rejects an unanswered constructor, and the hook
  rejects the two spellings that would silence it again (`| other =>
  other` anywhere in core, `| _ => <numeral>` in Ir.lean). One
  catch-all was a real drop and gained a real arm with a test that
  failed first: a font template's hole inside a link or step wrapper
  now fills. A step inside a section title stays one handout page —
  furniture sits outside the overlay model, as the dim walks already
  decided — but the answer is now an explicit arm pinned by test, not a
  wildcard's accident. The gate showed its worth mid-flight: the chrome
  slice added `Block.framefoot` while this one was in review, and the
  closed walks refused to build until every walk answered for it.
  The arms that deliberately keep a block whole under shade/dim
  (section, note, frame, framefoot) now say so where they stand.
- A golden fixture owes a `censusTable` row in Tests.lean: assertions
  over the pages the engine ships (`Layout.Out`), so no fixture enters
  the suite witnessed by its IR dump alone. All six defects were
  invisible to goldens by construction — goldens witness elaboration
  only. Enforced: `censusChecks` fails when a `goldenNames` entry has no
  row; proven by deleting the notes row (coverage failed) and by
  re-breaking the dim walk (the covered facts of talk, overlays, and
  furniture failed).
- A backend emission owes the census assertion that it appeared — the
  footer that is declared and read by nothing is the defect shape.
  Enforced per fixture today (fills, rules, covered runs, resolved page
  numbers, line positions for centring and columns); the role census the
  faithfulness audit designed extends `Check.Shipped` and should absorb
  the Tests-side table when it lands.
- A diagnostic code owes one meaning, held in `diagRegistry`, and a test
  that fires it. The registry's first run found W0314 already meaning
  both "column width is not a fraction" and "unknown theme"; while the
  renumber was in flight the chrome slice took W0318 for "\chrome
  outside slides" — the third collision of the same day, so the theme
  meaning is W0319 (deck golden regenerated). The card slice had dodged
  the same class by hand (W0315 → W0317). Enforced: `diagChecks` scans
  every quote-delimited code literal in the engine — each must be
  registered, no number twice, no entry outliving its last emission
  site. The firing test stays convention, not yet checked.
- A design constant owes a source or a token. `sectionSize`'s pt 14 /
  pt 12 ignoring the type scale and the progressheight fallback `pt 1`
  are the standing examples (design audit I3/I4, still open). Enforced:
  the hook rejects an added bare `pt`/`mm`/`mm100`/`inch` literal on a
  commentless line in the four backend files; it checks that a why was
  written, not that it is right.
- A recursive IR walk owes a `List` companion with a threaded
  accumulator (the existing append hook holds the cost half) and its
  conservation statement where it is one. The overlay slice landed
  exactly these for the dim walks — `Ir.shadeBlocks_text` /
  `dimBlocks_text` prove shading and dimming preserve every character —
  by the accumulator-lemma-then-mutual pattern the faithfulness audit
  demonstrated; `substPage` and `fillTemplate` owe theirs the same way.
- A palette role or token the engine reads owes a single resolving site,
  its contrast contract, and a per-bundle completeness check. moloch
  declares `separator` and no code reads it; sectionpage alignment fell
  back per `getD` site. The resolve-once `Design` record landed while
  this entry was in flight (the theme-contract entry above): the pairing
  contract quantifies over `Theme.builtin`, the role census runs in
  Tests, and `separator` gained its consumer (the title-page rule) and
  moved into `consumedRoles`.
- A page-opening path owes a declared vertical distribution, never a
  default. The title jammed at the top of its page, and the plain-frame
  branch opens a page with no `pageStyle` at all. Landed while this
  entry was in flight: `VDist` rides on `pageStyle` (the
  vertical-distribution slice, design audit R1) with the exact-split
  theorems; the rule stands for any new page-opening path.
- A furniture element owes a declared alignment: `\maketitle` hard-coded
  `.center` where the moloch source is ragged-left under golden-ratio
  glue. Landed while this entry was in flight: `align` on `ElementStyle`
  (design audit R2), the title page styled through it.
- An `AssertKind` owes its judge in `Check.one` (the match is exhaustive
  — the compiler collects) and a test that re-breaks each guarantee once
  (the card slice's pattern).
- A document class owes sourced defaults and its contract as implied
  assertions — the card entry below is the template.

Costs, measured on the rebased tree (medians of 3, warm, a no-op change
staged): the whole hook 1395 ms, of which `lake build --wfail -q` is
208 ms and interpreting the script dominates the rest; the hook at main
measured 1310 ms, so this entry's three new checks add ~85 ms. The test
executable, census layout of all 27 fixtures and the diagnostic-code
scan included, runs in ~1.6 s.

The shared shapes, named once so the next agent extends instead of
reinventing (status as of this entry):

- Resolve-once-then-total: exists — `Ir.Design.ofDoc`, landed with the
  theme-contract slice (provability audit's keystone R1+R2, themes as
  typed values); Contrast and HtmlDoc read it, the Contrast spec copies
  are deleted, and `Layout.Acc`'s adoption is the recorded follow-up.
- Ratio vertical distribution: exists — `Layout.VDist` on `pageStyle`
  with the exact-split theorems (the vertical-distribution slice,
  design audit R1); frames declare `[t]`/`[c]`/`[b]`, the title page
  takes the golden split.
- Declared alignment: exists — `align` and `separator` on
  `ElementStyle`, `titlepage` styleable (design audit R2).
- One bracket scanner: exists — `Elab.scanBracketArg`, the single scan
  that four disagreeing copies collapsed into (2026-09-16 entry).
- One census: `Check.Shipped` exists and is the lever; the role census
  (text per page, marker runs with kind, fills, covered runs, link
  rectangles, per-line x) extends it. The `censusTable` in Tests.lean is
  deliberately thin and local so that growth absorbs it rather than
  competing with it.
- One bottom edge: exists — the chrome slice landed `Geom.bodyBottom`
  as the one place the page bottom is read, with the footer band
  reserved inside it (`bodyBottom_clears_footer`); Check's own bottom
  reading should migrate to it.
- Every tree walk: `List` companion in a `mutual` block with a threaded
  `Array` accumulator (`Compat.rewriteList`, `Html.render`, the Ir
  overlay walks). Exists as the house pattern; the hook rejects the
  quadratic spelling and, now, the wildcard one.

2026-09-17 — one frame numbering, and the model stated. The engine now has
exactly **two** number sequences, each with one definition site, never mixed
implicitly:

- **Frame numbers** — `Ir.frameNumbers`/`Ir.frameCount`: the k-th countable
  frame (a `.frame` with `standout = false` and `valign ≠ .golden`; only
  `\maketitle` produces `.golden`) bears k, everything else none. moloch's
  own semantics: `\maketitle` is `\frame[plain,noframenumbering]{\titlepage}`
  (beamerinnerthememoloch.dtx:314-320), standout likewise (:777-778), and
  beamer's `noframenumbering` does not advance the counter (user guide §8.1).
  Chrome footers, the progress bar, and the HTML deck all read this array;
  a new count consumer reads it too, never counts for itself.
- **Physical pages** — `\pagenumber`/`\pagecount`, substituted per page by
  `substPage`, `\pagecount = pages.size` by definition. Page furniture is
  physical (beamer's page counter is too); collapsing the two sequences
  would re-create the confusion one level down, so a document mixing them
  in one footer band gets each slot per its own model, explicably.

Invariants at their closed strength: numbered iff countable
(`frameNumbers_numbered_iff_countable`, theorem); monotone/gapless somes =
`range' 1 count` (`frameNumbers_gapless`, theorem); every number ≤ count
and the count reached (`frameNumbers_le_count`,
`frameNumbers_last_is_count`, theorems) — so the progress clamps were dead
and are deleted, with emission gated on `frameCount > 0` (moloch clamps
only because its total lags in the aux file; nothing here lags). One
numbering for both backends is structural, not a theorem: the second
counters (`Acc.framesSeen`/`framesTotal`, HtmlDoc's `seen`/`total`) are
deleted and both backends index the one array, pinned by the corpus test
that the PDF footer text equals the HTML footer text. A frame number
becomes text only in `Ir.ChromeSlot.render` (slot `framefraction` added:
moloch's `numbering=fraction`, beamerouterthememoloch.dtx:156-188).
`runningFrom` now gates only physical furniture (head, foot, logo), not
frame chrome; a running line that would wrap warns by name (W0319) instead
of silently keeping its first line.

Owed from this slice: the running **head** has no reserved band — `headY`
is `vmargin/2 + ascent` with no top analogue of `footBand`, so a small
declared `vmargin` can collide the head with body text. The fix is the
`footBandFor` analogue (`headBandFor`) reserving the band in `Geom` and a
`bodyTop` the placements read, with the mirror of
`bodyBottom_clears_footer`. Separate slice.

2026-09-17 — the theme contract ranges over the engine's values now, and
the resolved design is a type. Correction to the colour entry below: its
bundle theorems held over hand-transcribed palettes (`molochResolved`)
because `Theme` stored its bundles as unparsed surface strings the kernel
could not evaluate — a theorem about a parallel definition reads as a
guarantee and is not one. `Theme` now carries palette/tokens/styles as
typed values, mixes evaluated at definition time with the same `Color.mix`
step the document path folds, installed at `\theme` through the shared
`Palette.declare`/`Tokens.declare`/`Styles.declare` replace-on-redeclare
helpers the document declarations use; `moloch_contract`/`plain_contract`
restate over `Theme.moloch.palette` by the same `decide` (the raised
`maxRecDepth 4096` sufficed — the mixes are integer arithmetic, not a
string parse) and the transcriptions and their pinning tests are deleted.
The two roles the slices below added ride along typed: `muted` and
`covered` as `Color.mix` chains (xcolor spelling beside each), and the
bundles' chrome as typed `Ir.Chrome` — declared data, not colour, no
theorem over it. `Ir.Design` is the resolved design: one `Design.ofDoc`
applies every default the consumers used to apply per site (`fg`/`bg`,
`covered`, `muted`, the frame-title and progress pairs, the standout
inversion, `separator`, `progressheight`, per-element style),
presence-is-the-feature fields (`frametitle`, `progress`) as `Option` of
total pairs. Contrast's `docDiags` and `paletteContract` and HtmlDoc's
`themeCss` read it; `builtin_designs_legible` quantifies the contrast
contract (muted's 4.5:1 included) over `Theme.builtin` itself, and
`coveredContract` restates over the resolved design, quantified the same
way (`builtin_designs_covered`). A role census in Tests names any bundle
key no backend consumes — it found what it exists for: both bundles
declare `separator` and nothing reads it (why the title-page rule never
draws); it stays a named warning until its consumer lands. Verified:
goldens unmoved, whole corpus byte-identical by `cmp` (PDF and HTML)
against the base commit. Follow-up, deliberately not here:
`Layout.Acc`'s `pal`/`tokens`/`styles`/`fg` collapse onto `Design` —
Layout.lean has six concurrent workers in it.

2026-09-17 — owed theorems: state the obligation before you can prove it.
The advisories named a couple of dozen invariants whose strongest form was
not reached; the statable ones now live as type-checked statements with
open proofs in `Obligations.lean` — its own lake target, outside the
default build and `lake test`, never imported by `LeanTex/`. The rule that
a `sorry` in the library is a lie wearing a theorem's clothes is not
weakened: the hook still rejects it everywhere else, and the staging path
is gated by a ratchet (`scripts/owed.lean`, run by the hook) — one hole
per owed record, every record's name registered in § Owed obligations
above, the whole tree scanned (not the diff) so the count cannot drift.
Statements range over the engine's own public functions; what is only
statable over private internals (`Acc`, `B`, `Op`, `collect*`) is recorded
as each obligation's blocker instead — opening a `private` was
deliberately not done. Unstatable without inventing definitions, so not
staged: the loss ledger (arch-provable I7, needs a `Loss` type),
`elabInlines`/`elabBlocks` termination (needs the phase split's total
definitions to even state a measure), and walk-coverage (arch-provable I3,
a compiler-exhaustiveness property, not a proposition). The gate was
proved load-bearing by staging a hole outside the path and an unrecorded
hole inside it and watching both commits fail.

2026-09-17 — M6's second slice: math renders as math, alignment first. The
reference deck's display math is `align*`, which the first slice left to
source text — raw backslash commands on a projected page. Now
`align`/`align*`, `gather`/`gather*`, and `array` (inside math) elaborate
to one grid nucleus: every cell runs through the existing atom pipeline,
one assembly places cells at column offsets every row shares
(`Math.colOffset`), pads them into their columns (`ColAlign.pad`,
alternating right/left for align with amsmath's `{}#` empty Ord opening
the even cells, so a leading relation keeps its thick space), sets rows a
baselineskip plus `\jot` apart (plain TeX's 12 pt and 3 pt at the 10 pt
base) or further when ink would collide, and centres the grid on the
axis. With it: `\frac`/`\over` (Appendix G rule 15 over the MATH
constants, gaps opened until ink clears, `\nulldelimiterspace` each
side), `\sqrt` with its index (radical constants; the surd grows through
MathVariants, ink top at the overbar), `\left…\right` (rule 19 with
plain's `\delimiterfactor`/`\delimitershortfall`, the chosen variant
centred on the axis), big operators at `displayOperatorMinHeight` with
limits above/below in display style (rule 13/13a, the upper/lower limit
constants), primes, `\limits`/`\nolimits`, `\text`/`\mbox`/`\operatorname`.
The engine reads glyph ink extents from the outlines (`Ink.yExtentAt`,
memoized per gid like `underlineInk`) — gap minima, delimiter growth, and
limit placement are against real ink, not nominal metrics; `Item.rule`
carries fraction bars and overbars to the existing `Seg.rule`; struts tell
`placeLine` the true height of an assembled construction.

Invariants, strongest closed form: a padded grid is rectangular and
conserves its cells — theorem (`MRows.pad_rectangular`, `MRow.pad_cells`);
cell padding stays inside its column and centring is symmetric to the sp —
theorems (`pad_within`, `pad_center_symmetric`); the assembled grid width
is the column widths plus the declared gaps exactly — theorem
(`colOffset_total`) over the same function the assembly places cells with,
so alignment points share one x per column by construction (pinned in sp
by `mathChecks` across rows); the picked variant covers its content
whenever the font can, and is never an invented glyph — theorems
(`pickVariant_covers`, `pickVariant_mem`); fraction constituents never set
larger than their base — theorems (`frac_styles_descend`,
`sizeFor_mono_rank`); limits are scripts (rule 13a), so `sizes_shrink`
covers their sizes, said in its docstring. Assembly conserves content at
test strength: the census (now rendering math-declaring fixtures with the
shipped math face) witnesses the display ∑, an aligned row's glyphs, and
all eight fixture rules; nothing-silently-dropped stays the diagnostic
regime — a ragged row is W0014, padded and rendered; a numbered
`align`/`gather`/`equation` renders its rows under one W0015 naming the
owed numbers; everything else keeps W0012 with the construct's name.
Verified against lualatex + unicode-math on the same shipped face, as
pixels; the reference deck went from five slides showing raw math source
to zero.

What M6 still owes, warned by name today: accents (`\hat`, `\bar`, …),
`\binom`/`\atop`, the amsmath matrix wrappers (`pmatrix`, `bmatrix` — the
plain `array` renders), `\\[len]` extra row space in alignments, equation
numbers (W0015) and `\tag`, glyph assembly past the largest MathVariants
size (the largest variant is the ceiling), `\dfrac`/`\tfrac` style forcing
(set as `\frac`), amsmath's stretching tabskip between align pairs (a
fixed 2 em stands in, stated unsourced), italic correction and math
kerning (MathGlyphInfo), stretchy muskips, and native MathML on the HTML
path — the HTML backend is deliberately unchanged (source in `data-tex`,
`--math-boundary` still the tool). `\text` sets in the math face, not the
body face — visible only when the two differ. Line heights inside math now
follow real ink through struts; plain text lines keep capHeight+raise.

2026-09-17 — M6's first vertical slice: formulas render. `$x^2$` is glyphs
now, not the characters `x^2` — inline `$...$`/`\(...\)` and display
`\[...\]`/`equation*`/`displaymath` elaborate to math atoms (TeX's eight
classes) and set from the document's math face (`\fonts{ math = ... }`,
fontspec's `\setmathfont` rewritten onto it) as one unbreakable box in the
existing line machinery; display math is its own centred block. Variables
set italic via the Mathematical Alphanumeric scalars, digits and the
TeXbook's named functions upright (ISO 80000-2 §7 / TeXbook ch. 18).
Scripts set at the MATH table's script percentages, shifted by the
base-size-scaled constants, cramped variant under subscripts, stacked
sup/sub advancing by the wider plus `spaceAfterScript`.

The invariants, in their strongest closed forms:

- Style recursion terminates — theorem (`style_progression_decreasing`,
  `scriptscript_fixed_point`): the progression decreases and bottoms out at
  scriptscript; the layout recursion itself is structural on the formula
  tree (no new `partial`), the theorem is what makes its style parameter
  meaningful.
- The spacing table is total and correct — theorem
  (`spacing_agrees_with_luatex`): spacing is a total function of (left,
  right, style); degrade-then-space reproduces by `decide`, over all 64
  class pairs in both style bands, exactly the named muskips luatex
  inserts (`\showbox` probe, TeX Live 2026), Bin degradation included —
  `$-x$` sets tight (`bin_leading_degrades`).
- Sizes shrink monotonically — theorem (`sizes_shrink`): over every font's
  percentages (clamped into (0,100] on parse, ss ≤ script), no script sets
  larger than its base at any style.
- A box is a box — test (`mathChecks`): a formula's advance equals the sum
  of its glyph advances plus the table's kerns, held in sp against widths
  recomputed from the font's own advances, formula by formula (a+b's two
  medium spaces, =' s thick ones, script suppression, stacked-script max,
  spaceAfterScript). A theorem would quantify over the layout walk itself;
  the walk computes width as the fold the test checks, and the honest label
  today is test.
- Nothing silently dropped — diagnostics, each pinned by test: an
  out-of-scope construct earns W0010 naming it and its source still sets
  (align kept its `&`); a glyph the math face lacks is W0004 naming the
  face; no usable math face is one W0003 with the declaring fix in help; a
  declared face without a MATH table is W0011 naming face and path.

What M6 still owes, warned by name today: fractions, radicals,
`\left...\right` with grown delimiters (MathVariants), big-operator
display-size variants and above/below limits, `align`/`gather`/`array`/
matrices, `\over`, accents, `\text{}` in math, primes, italic correction
and math kerning (MathGlyphInfo), stretchy muskips, numbered `equation`,
and native MathML on the HTML path — the HTML backend is deliberately
unchanged (source in `data-tex`, `--math-boundary` still the tool).

Measured: bench medians 77/287/398 ms (paragraphs/lorem/underline),
within the noise band of the entries above — the math pass costs only
documents that carry formulas. The fixture renders on both backends and
was inspected as pixels beside a lualatex + unicode-math twin on the same
shipped faces: same glyphs, same script placement, same spacing classes;
the visible differences are exactly the owed items (display-size ∑ with
limits below, italic correction). With the slice: the pre-commit keyword
gate now strips string literals first — the math tables' `"partial"`
(TeX's `\partial`) was a data entry, not a declaration.

2026-09-17 — M6 opens: the two design decisions, written before the code.

- **Math metrics come from the OpenType `MATH` table** (Microsoft OpenType
  spec, learn.microsoft.com/typography/opentype/spec/math), not TeX's
  `\fontdimen` parameters. The engine is OpenType-only by principle 4 —
  there is no TFM to read a `\fontdimen` from — and every math face a
  document can name (Latin Modern Math, the TeX Gyre maths, STIX Two, Fira
  Math) is an OpenType MATH font whose designer tuned exactly these
  constants; the table's `MathConstants` are the direct successors of
  Appendix G's σ and ξ parameters. Appendix G and TeXbook chapters 17–18
  remain the *algorithm* of record where the spec describes only data: atom
  classes, the inter-atom spacing table, the style recursion, Bin
  degradation. Two consequences the spec states and the engine follows:
  script-attachment constants are read from the font of the *base* and
  scale with the base's size, and `scriptPercentScaleDown` /
  `scriptScriptPercentScaleDown` set the script sizes (sanitized into
  (0,100] on parse, so "script sizes never grow" is a theorem over every
  font, not a hope about well-behaved ones). A declared math face with no
  MATH table earns a diagnostic naming the face and the formula is set as
  source text — never silent wrong spacing from invented constants.
- **The math fixture ships Fira Math** (`FiraMath-Regular.otf`, 180 KB, SIL
  OFL 1.1, copyright Xiangdong Zeng, licence text alongside): the smallest
  real-MATH-table face found — smaller than the already-shipped
  SourceSerifPro-Regular (218 KB) — it is CFF like the Source faces the
  parser already exercises, and a Fira-class sans math face is the pairing
  the M5b theme direction already names. Considered and passed over on
  size: Latin Modern Math (GUST, 734 KB), TeX Gyre Pagella Math (601 KB),
  STIX Two Math (838 KB), Asana Math (436 KB).
- The inter-atom spacing table was transcribed from TeXbook p. 170 and then
  read back out of luatex itself before being encoded: a probe boxes every
  (left class, right class) pair under anchor Ord atoms in all four styles
  and reads the named muskip out of `\showbox` dumps (`\thinmuskip` /
  `\medmuskip` / `\thickmuskip`), including that a Bin first, last, or
  after Bin/Op/Rel/Open/Punct degrades to Ord. The engine's table is
  pinned to that transcription by `decide` over all 64 pairs × 4 styles.

2026-09-17 — images exist: `\includegraphics` through PNG/JPEG to both
backends, the first native piece of M8's asset story. The shape is effects
as data, exactly as fonts: the IR carries one image node (source path, size
request, alt text), `Ir.imageRefs` lists the files a document names, the
CLI driver reads and decodes them into an `Image.Store`, and layout and
both backends consume that value — `LeanTex/Core/Image.lean` and
`Flate.lean` do no IO. The `figure` environment (caption becomes the
image's alt and a paragraph, placement option burned, numbering not yet)
and beamer's `\logo` reduce to the same node. `\logo` is stateful as in
beamer — the body form is a `Block.logo` declaration replayed per page, so
`\logo{...}` before a frame and `\logo{}` after badge exactly that frame's
pages at the lower-right; the preamble form is the initial state. In layout
an image is an unbreakable box with height and no depth through the
existing item machinery; missing files warn (W0601) and place an outlined
box of the requested size, best effort as everywhere. Invariants, strongest
closing form: sizing is a theorem (`resolveSize_*`: declared size wins to
the sp, a derived dimension holds the intrinsic ratio to within one sp,
`keepaspectratio` fits inside its box — re-breaking it fails the build,
tried); decoders are total over `ByteArray` (bounds-checked reads; unit
tests plus `scripts/img-fuzz.lean`, 15347 inputs, an oracle not a theorem);
the PDF xref self-check holds with image XObjects in the file, and the
content stream's `cm` matrix is asserted to carry the placed size (the
check that catches a blank box a structural test would miss). Formats: PNG
greyscale/truecolour/indexed pass their zlib stream through as
`/FlateDecode` with the predictor declared (ISO 32000-2 §7.4.4.4),
byte-identical (tested); 8-bit alpha really decodes — a total inflate (RFC
1950/1951), the scanline unfilter, colour/alpha split, stored-block zlib
back out, `/SMask` in the PDF; JPEG (JFIF, 1- and 3-component, 8-bit)
embeds whole as `/DCTDecode`. Undeclared density is 72 ppi (PNG leaves it
unknown without pHYs, ISO/IEC 15948 §11.3.5.3; JFIF unit 0 is aspect-only;
72 is pdfTeX's `\pdfimageresolution` default) and that convention is a
theorem (`width_at_default_dpi`). HTML emits `<img>` through the typed
tree: intrinsic pixel size as attributes so the page never reflows,
`0.8\textwidth` as a percentage, `height: auto` carrying the ratio
invariant; a bare graphicx name (`figures/plot`) resolves to the file on
disk and the link names it. Not in this slice, recorded: interlaced PNG,
16-bit alpha, CMYK JPEG (each refused with its reason and a placeholder
box), tRNS transparency on passthrough types, figure numbering, `\label`
inside figures, PDF-page embedding (form XObjects), and beamer's
`keepaspectratio`-free `totalheight` is mapped to `height` since an image
box has no depth. Fixtures are synthetic and shipped
(`tests/corpus/rects.{png,jpg}`, `rects-alpha.png`, provenance in
`images-note.md`); pages rastered and eyeballed, not just golden-checked.
Bench medians 77/283/395 ms vs 74/276/383 at base (noise).

2026-09-17 — the overlay slice: covered content must be visibly covered.
A real deck showed four ways it was not, each fixed to its invariant:

- Range ends are modelled: `Ir.step` carries an optional inclusive end,
  so `\onslide<1>{...}` dims again from step 2 and `<2-3>` gives a frame
  three pages — beamer's transparent covering, which the earlier "the
  range's end is not modelled" reading silently dropped. `stepPending`
  names the page test.
- Covered means covered: the shade repaints nested explicit colours (an
  alert-heavy slide used to defeat its own covering — every inner
  `.colored` won over the wrapper) and verbatim dims through a `covered`
  field (paused code used to stay crisp while its sentence dimmed).
  Nothing vanishes is now a theorem: `Ir.dimBlocks_text` /
  `shadeBlocks_text` prove the walks preserve every character, so each
  handout page carries the whole frame.
- Block content steps whole: an overlay group routes through the block
  elaborator when its body is block-shaped (the same judgment environment
  bodies get), so a list inside `\onslide<2->{...}` steps instead of dying
  with E0312, a multi-paragraph group is not spliced down to its first
  paragraph, and the bare open form between blocks steps the rest of the
  scope instead of an empty step. `\alt<n>{a}{b}` joins at both levels: b
  is a step through n−1. `\pause` between list items steps the rest of
  the list (it used to step the empty rest of the previous item).
- Themes own their dim: `covered = fg!38!bg` in both bundles (38% is the
  Material disabled-state opacity, and what the default #A1A1AA already
  encoded over white), held by theorem to `Contrast.coveredContract` —
  quieter than the body ink, and the state change ≥ 3:1 (SC 1.4.11's
  ratio for state-identifying information; SC 1.4.3 exempts the covered
  text itself, as already pinned). `\setbeamercovered{transparent}` is
  agreement with dim-not-hide and no longer warns; `transparent=<n>`
  declares the covered colour as an n% mix; `invisible` keeps the honest
  warning naming the divergence.

Verified: build --wfail, tests, bench medians 77/288/384 ms (within the
noise band of the entries below); the reference deck renders with covered
steps reading as covered on the pages that used to show them crisp.

2026-09-17 — slide chrome: the frame footer, from defect ("the frame
footer to the slide is not visible") to declared data. Four units:

- The band before the ink: `Geom.bodyBottom` is the one place the page
  bottom is read (placement and vertical centring), and a footer
  reserves its band inside it (`footBandFor`: what the foot line's
  ascent plus `lineskip` clearance needs beyond the half margin its
  baseline sits below the body). `bodyBottom_clears_footer` proves the
  reservation sufficient for every geometry; with default margins the
  band is zero and undeclared pages are unchanged. This helper is the
  agreed merge seam with the vertical-placement slice, which named the
  same function without the band term — reconcile to this one.
- Chrome as data: `\chrome{ footer = { left = \sectiontitle, right =
  \framenumber } }` (the theme-modern sketch's surface), `Ir.Chrome` in
  the IR, both bundles declaring it — moloch's footline read as data,
  not imitated as code. The footer's colour is the new semantic key
  `muted = fg!70!bg`, the strongest quieting that still clears SC
  1.4.3's 4.5:1 at the footer's small size (4.79:1 moloch, 6.36:1
  plain; 60:40 fails at 3.65:1); `moloch_contract`/`plain_contract`
  now kernel-check the pairing, and a document overriding `muted` under
  an active footer is judged by W0315 like a declared `fg`. `\chrome`
  outside slides warns (W0318) rather than dying silently.
- Laying it: frames emit a `.foot` op under the driver's single
  `framesSeen`, so a footer shows its frame's OWN number and a stepped
  frame's pages share it; section pages and standout frames carry none;
  spill pages inherit their frame's. PDF lays the line into the bottom
  half margin at the scale's small step in `muted`; HTML closes each
  frame `<section>` with a `footer.slide-foot size-small` styled by
  `var(--muted)` — one design, two backends, no literals.
  `\runningfoot` still overrides the whole footer; an unthemed deck's
  output is byte-identical.
- The deck's own spelling: `\setbeamertemplate{frame footer}{...}` —
  alone or expanded from a `\newenvironment` wrapper — is now the
  native `\framefoot{...}` (`Block.framefoot`, a state change in
  document order): the note takes the footer's left slot for the frames
  that follow, empty clears back to the default, the frame number keeps
  its slot. Other templates keep the honest W0104, naming `\framefoot`.
  `tests/corpus/chrome.tex` is the end-to-end fixture.

Every invariant pinned in chromeDeclChecks / footerBandChecks /
chromeFooterChecks / frameFootChecks, the band and frame-number ones
shown failing with their bugs re-introduced. Bench 77–78/278–290/388 ms
(vs 73–78/276–283/376–405 recorded — noise). The reference deck: 62
pages, 18 warnings against 19 at the base commit (the frame-footer
skip is gone), and its footer now renders. Known coarse edges, recorded
not hidden: the title frame (`\maketitle`) carries the footer with
frame number 1 (`\thispagestyle{empty}` suppresses page 1's furniture,
the same spelling articles use); the running head has no symmetric band
at the page top; the chrome band assumes the footer sets at its
declared small step (an override styling itself larger is not measured).

2026-09-17 — the card slice reconciled with the three slices that landed
under it (typography, colour, M5b themes), each conflict a design
question, not a merge:

- Base size: the card takes the shared `PageSpec` resolution the
  typography slice introduced (`\page{ fontsize }` → class option → the
  10 pt base) — no card-private constant existed or was added; pinned by
  test on the default and on a `[12pt]` class option.
- The legibility floor composes with the type scale now:
  `Ir.cardXHeightFloor` names the 1.4 mm bound and
  `card_floor_within_scale` proves every scale step from `footnotesize`
  up clears it at the card's own base size under the conventional
  x-height ratio — the class never implies an assertion its own defaults
  violate, and what fails the floor (`scriptsize`, `tiny`) is exactly
  what the shipped-ink judge exists to catch, font by font.
- Contrast stays the colour slice's contract, reused rather than
  restated: a card runs through the same `docDiags` walk as every class,
  so an illegible pairing earns W0315 and `\palette[decorative]`
  silences it — both pinned in cardChecks; nothing card-side was
  reimplemented.
- The card's dropped-running-furniture warning renumbered W0315 → W0317:
  the colour slice owns W0315 (the pairing warning) and one code must
  mean one thing.
- W0201, the measure band, does not apply to a card: the band's own rule
  is about continuous reading and a card is display text like slides.
  The class gate in layout is pinned by test at the card's default
  measure (~214 pt, which would earn "widen" in an article).
- `Block.frame` grew to (title, standout, body) in the M5b slice; the
  card's face count follows the arity.
- trio-deck's golden regenerated through the harness: the IR dump
  records `fontsize 11` for slides since the typography slice; nothing
  else in the trio moved. Verified post-rebase from scratch: build
  --wfail, tests, kp-fuzz 200 (justified and ragged, all optimal), bench
  medians 77/275/408 ms (paragraphs/lorem/underline — within the noise
  band of the entries below), trio fixtures rendered to PDF and HTML and
  inspected on both backends, and an over-full card refused with both
  E0330s and no output file.

2026-09-17 — the third artefact: a `card` document class, the sharpest
test of the design system because at 85.60 × 53.98 mm nothing can be
fudged. The class differs from `article` and `slides` in defaults only —
every mechanism it uses is shared, and each default is sourced rather
than guessed:

- Trim sizes from the trade standards: ISO/IEC 7810 ID-1 by default (the
  credit-card size most business cards follow; iso.org/standard/31432),
  class options `us` (3.5 × 2 in) and `jis` (91 × 55 mm, the meishi
  4-gou). Margins default to the print safe zone, 5 mm inside the trim
  (banana-print.co.uk names 4–5 mm; solopress.com 3 mm as the minimum).
  `\page{ bleed = 3mm }` — the 3 mm / 0.125 in shop convention
  (solopress.com/support-guides/bleed) — grows the PDF medium, shifts the
  content with the trim corner, and records the TrimBox (ISO 32000-2
  §14.11.2); zero bleed is byte-identical output by `cmp` across the
  corpus. Two faces are two `frame` environments: the page-boundary
  mechanism every class already had.
- What a card guarantees is stated as assertions the engine already fails
  builds on, implied by the class and silenced by declaring the same
  form: content fits its faces (`pages <= N`, N counted from the frames);
  ink respects the safe margin (`text.in_area`, new, judged from the
  shipped lines with each run's font cap height and descent at its size —
  cap height because hhea ascent reserves accent headroom that is blank,
  and the trio card's `\Large` name proved it by failing with no ink out
  of bounds); and the smallest type clears the fluent-reading floor at
  hand-held distance (`text.xheight >= 1.4mm`, the 0.2° angular x-height
  at 40 cm bounding the fluent range in Legge & Bigelow 2011,
  PMC3428264 — read from each font's own OS/2 x-height at the run size,
  the metric the source speaks in). Each check was re-broken once and its
  test failed. Contrast is deliberately absent here: it is the colour
  worker's contract, and a card participates through the shared palette
  like any other class.
- The invariant whose absence made a plain-prose card impossible: below
  the 40-character working minimum for justified text (Bringhurst,
  Elements §2.1.2), a measure must be set ragged. At card width no line
  has the stretch justification needs, so the breaker could only choose
  among overfull lines and shipped one giant one. `justify = on|off` and
  `hyphenate = on|off` are now `\page` keys with class defaults (both off
  for card only); ragged is an item transform — glue keeps its natural
  width and gains fil, `\raggedright`'s glue model — so `kp` itself is
  untouched, and `scripts/kp-fuzz.lean` now holds the breaker optimal
  over both item shapes (300 cases, justified and ragged). A first
  flag-in-kp attempt was measured and rejected; with the transform,
  alternating A/B bench runs on the underline arm read 404/405/408 ms
  before vs 404/393/407 after — no attributable cost. The shipped-ink
  walk behind the new assertions runs only when something asserts.
- The trio fixtures (`trio-page`, `trio-deck`, `trio-card`) carry
  byte-identical `\fonts`/`\palette`/`\tokens`/`\style` blocks; both
  backends rendered, rasterized, and inspected — the amber ruled section
  style reads identically on the page, the deck divider, and in the HTML
  of all three; the card's two faces imposed on one sheet for the print
  shop. All content invented.
- What a fourth artefact would cost, from doing the third: one defaults
  block in the elaborator plus any genuinely new page keys — no backend
  was touched for `card` beyond the bleed mechanism, which is a `\page`
  key any class may use. The residual wart is pre-existing, not new: the
  `slides` class is tested by name in layout (`Acc.slides`: sections and
  frames open fresh pages) and in the elaborator (`\maketitle` makes a
  frame), so a fourth class wanting either behaviour would extend those
  name tests. The clean form is a policy value beside `hyphenate`/
  `justify` ("sections break pages"), left undone here to keep this diff
  out of the concurrent workers' files.

2026-09-17 — colour is a checkable contract now, not a palette of guesses.
WCAG 2.2 gives contrast a formula (relative luminance over linearised
sRGB, ratio (L1+0.05)/(L2+0.05)), so "every pairing the engine ships is
legible" became a theorem rather than a review comment. `Core/Contrast.lean`
tabulates the channel linearisation at 1e-7 (all 256 entries pinned to the
spec formula by test) and kernel-checked `decide` proves the pairings:
both baseCss token sets clear their thresholds — 4.5:1 text (SC 1.4.3),
3:1 focus indicator (SC 1.4.11) — and both built-in theme bundles clear
theirs (fg/alert/example on bg at 4.5:1; frametitle pair at 4.5:1, 12pt
bold being under WCAG's large-scale sizes; standout pair at 3:1, 14.4pt
bold being over them). The bundle theorems hold over pre-resolved
palettes because the kernel cannot evaluate the string parse; tests pin
the constants to `bundlePalette` and that to what `\theme` installs. The
check found two real defects on arrival: dark mode kept the light accent
(2.64:1 on the dark surface; dark now carries the same hue two tints
lighter, 6.97:1, and baseCss renders the proven constants so stylesheet
and theorem cannot drift), and moloch's alert — metropolis's own
#EB811B — read at 2.61:1 as body text (now #A55A13, the same hue at 70%
over black, 4.94:1). The covered default stays deliberately dim, pinned
as an exemption (SC 1.4.3, inactive); progress bar and separator are
exempt as supplementary indicators outside SC 1.4.11's scope, recorded.
Document-side, the same arithmetic drives W0315: text coloured below its
threshold against the page (palette `bg` or the shipped surface) warns
with the measured ratio — large-scale text held to 3:1, a declared fg
judged against bg directly — and themed.tex's own fg!50!bg mix earns it
at 2.79:1. `\palette[decorative]{...}` declares intent and silences;
`covered` is exempt by role; an unknown `\palette` option skips the block
with W0316 rather than restyling the base. SC 1.4.1 (colour never the
only signal) closed two gaps: themed `\alert` is colour AND bold now
(metropolis colours only; deliberate divergence), and a PDF link draws
the underline the HTML anchor always had — it previously had no visual
signal at all. `docDiags` is a whole-document pass, measured: 0.07 ms on
the 30-page bench document. APCA stays out: a WCAG 3 working draft; 2.x
is the standard in force.

2026-09-17 — typography as enforced relations: the measure, the type
scale, the vertical rhythm, and the slides stage each carry a sourced
invariant now, as a theorem where one closes and a diagnostic where the
check is about a document. Sources are primary or the citable record of
one: Bringhurst's *Elements* §2.1.2 (45–75 characters satisfactory for a
single column of text-size prose, 66 ideal) and his copy-fitting table
through the memoir manual's fitted lines (L₆₅ = 2.042α + 33.41 pt,
L₄₅ = 1.415α + 23.03 pt over the lowercase alphabet length α), §2.2.1
(10/12 is a routine setting; longer measures need more lead), §2.2.2
(vertical space in measured intervals), Butterick's *Practical
Typography* (line length 45–90; space below a heading smaller than the
space above), and the beamer user guide (§5.6.1, §18.2.1, §8.3).

- The scale: the `\tiny`–`\Huge` table is LaTeX's size10.clo ladder, and
  what makes it a scale is now four theorems — strict monotonicity, every
  adjacent ratio inside [10⁄9, 7⁄5], ×1.2 (`\magstep`, to per-mille
  rounding) above `normalsize`, and the `normalsize` anchor. Checked
  against Material 3 (role steps ~1.14–1.27) and Apple HIG (~1.08–1.3):
  a 1.2 modular scale sits inside current practice, so the values stand.
  Verbatim's 4/5 was the scale's own footnotesize and is now spelled as
  the lookup — the one engine-internal size that was a loose decimal.
- The measure: layout computes the characters per line the text width
  holds from the body face's own lowercase alphabet through the fitted
  copy-fitting lines, and W0201 fires when an article document sets
  continuous text (a paragraph of ≥4 full-measure lines) outside 45–90;
  `\page{ measure = free }` declares the document takes responsibility,
  and slides are display text outside the rule's own scope. Calibration,
  measured: the estimate says ~100 characters for 10 pt Source Serif Pro
  on a 1-inch-margin letter page, pdftotext counts 102–105 on the set
  lines; the new default sets 68–71 against the 66 ideal. The default
  itself was the violation: the word-processor inch gave a 468 pt line.
  An undeclared letter page now takes a 26-pica text block — Bringhurst's
  table's own suggestion for a 130 pt alphabet, the middle of the 10 pt
  text-face range — and a document that declares any `\page` geometry
  keeps every value it named. Goldens: one page line in each of the seven
  default-geometry fixtures.
- The rhythm: the defaults were one system nobody had written down —
  parskip (6 pt) is half the base leading, so a heading's default space
  above (2×parskip) is exactly one rhythm unit — and
  `default_rhythm_multiples` now holds it, positivity making the
  heading's space above strictly exceed its space below. For declared
  styles the same rule is W0202: `\style` with `after` resolving larger
  than `before` warns, both-sides-declared only.
- The slides stage: the base size moves into `PageSpec` (resolved
  `\page{ fontsize }` → class option `11pt`/`fontsize=11pt` → 11 pt for
  slides, the 10 pt base otherwise) and the stage constants into Ir, so
  beamer's documented defaults are the engine's and HTML derives its
  measure from the same value. `slides_lines_in_band` pins Tantau's rule:
  both default stages carry 15 (16:9) and 16 (4:3) full lines, inside his
  10–20. Slide fixture page counts are unchanged at 11 pt (talk 6, deck
  8, furniture 6); the verbatim code-frame convention carries 75 columns
  of a 0.6 em mono at 16:9 now, not the 80 the 10 pt base gave.
- The baseline grid: decided against, and why is a result. The engine
  sets pages the way it sets lines — skips shrink within declared rubber
  before a break is taken (N0200), and a line's height follows the
  tallest run on it — and a hard grid forbids exactly those two
  mechanisms; TeX's own model made the same trade. Bringhurst's rule is
  not a device grid but measured intervals, which survives here as the
  rhythm-multiple theorem over the values the engine owns; a grid
  quantization diagnostic on documents would fire on any document using
  the rubber the resume was written with, i.e. on reasonable documents.

Bench, medians of 5, same session, across the default-measure change:
paragraphs 78 → 73 ms, lorem 279 → 281 ms, underline 387 → 405 ms — the
underline arm sets more lines at the narrower default; no pass changed
shape. Every diagnostic is silent on the shipped corpus (checked through
the CLI on every non-PENDING fixture), W0201/W0202 tests were each shown
failing with the check weakened and restored, and the wide/narrow/free/
slides/short-text cases are pinned in `measureChecks`.

2026-09-17 — the theme slice rebased onto the frame-furniture batch; the
crossing of standout frames with overlay steps resolved as one design
rather than two flags. `Block.frame` carries title, standout, and body —
steps stay content inside it, so the two features compose freely and every
pattern spells the full arity. Correction to the furniture entry below:
`Ir.expandOverlays` is gone; `Layout.run`'s top-level driver expands a
multi-step frame itself (same `Ir.dimBlocks` copies, same pages), because
the furniture state must be the frame's — all step pages of a frame share
one `framesSeen`, so a progress bar shows the deck position in frames and
never advances mid-frame, and the standout flag rides onto every step
page. `framesSeen`/`framesTotal` both count top-level frames, matching the
HTML path. Notes stay a side channel through the themed paths too: the
standout walk routes non-paragraph blocks through the normal walk, which
drops them. Each invariant pinned in `themeReconcileChecks`, shown failing
with the bug re-introduced and passing after.

2026-09-17 — M5b's first slice: a theme is a token bundle, and `\theme`
selects one. `Theme.lean` holds each bundle as declaration bodies in the
surface language — palette, tokens, element styles — applied at the
`\theme` site through the same code paths the document's own declarations
use; `\palette` and `\tokens` now replace on redeclare, so everything
after the site overrides and a theme is a default, never a lock. Two
bundles ship: `moloch` (the Metropolis lineage's light preset mapped onto
the semantic keys) and `plain`; a third theme is one more table of
values. The semantic keys are the whole backend contract: `fg`/`bg`
colour body text and page, declaring `frametitlebg` turns the frame
title into a full-width colour bar, `progressfg`/`progressbg` draw the
section page's progress bar (width = frames seen over total, thickness
the `progressheight` token), and `standoutfg`/`standoutbg` invert a
`[standout]` frame — now in the IR (`Block.frame` carries the flag),
centred and Large bold on its own page, defaulting to the inverse of the
page's own colours when the keys are absent. Layout pages gained fills
the PDF paints before the text object; the HTML stylesheet gained the
same rules keyed on the same palette entries, so both backends read one
design. xcolor's `!` mixing landed with it (`black!2`,
`progressfg!50!black!30` in the bundle, `fg!50!bg` at use sites, with
`fg`/`bg` naming the current semantic foreground and background), because
the moloch palette and the reference deck both write it; a mix that
cannot resolve still warns W0304. Compat rewrites `\usetheme{name}` to
`\theme{name}` and, for a known bundle, `\alert` to `\textcolor{alert}`;
an unknown name warns W0314 naming the bundles, and the remaining W0104
skips (`\setbeamercolor`, `\setbeamerfont`, `\setbeamertemplate`,
`\usecolortheme`, `\usefonttheme`) name their native spellings in help.
`tests/corpus/themed.tex` is the end-to-end fixture (theme through
compat, a document override, a mixed colour, bar, section page,
standout), with per-element checks each shown failing before its code
and re-broken once after. Found by those tests: `B.commit` rebuilt the
current page with only its lines, so every fill placed before another
line vanished — fixed to the invariant that what the walk attaches to a
page survives to that page's output. Measured: bench medians 78/276/376
ms against 73/283/379 at the base commit, same session (noise); the
private deck 52 pages, 0 errors, 34 → 32 warnings (the `\usetheme` skip
and the mixed-colour W0304 are gone), ~86 ms per backend, and its frame
pages raster with the title bar and tinted page. Recorded, not done:
`\palette[dark]` variants and the contrast assertions the milestone
names; per-frame `framefooter`/`framelogo` environments (the deck's
`\newenvironment` forms still warn; a document-wide `\runningfoot` is
the near spelling); the title-page separator rule (`separator` is
declared, unread); and the frame-title bar's padding follows the body
font size rather than moloch's strut geometry.

2026-09-17 — the frame furniture a real deck is built from, in five units,
each a construct that was a warning and is now a meaning:

- `\newenvironment{name}[n][dflt]{begin}{end}` translates to a native
  `\defineenv{name}(sig) {begin} {end}` exactly as `\newcommand` does to
  `\define` (Compat's body flag became a scoped count of two). At
  `\begin{name}` the parameters bind through the same `takeArgs`, then the
  begin half, the content, and the end half each contribute — the halves
  under the definition-time limits, which keeps expansion terminating and
  makes self-reference impossible. Deleted W0104-def + W0302 + W0313 in one
  move for any deck that defines wrappers. Built-in environment names
  refuse redefinition with W0303. Divergence, deliberate: an inline half
  beside block content becomes its own paragraph rather than fusing.
- `\centering` is a declaration: a block boundary wrapping the rest of its
  scope in `.center`, a scope group carrying it is a block scope (the brace
  ends its reach), and it counts as a declaration for the par-splitting
  rule, so it carries across `\par` like `\bfseries`. Divergence: text
  earlier in a broken paragraph stays uncentred where LaTeX re-aligns the
  whole paragraph. Inline positions keep W0108, now saying why.
- `Block.columns` carries per-column widths as per mille of the text width
  (`{0.5\textwidth}` spellings; W0314 and an equal share for anything
  else). PDF: a new `Acc.measure` narrows the paragraph target, and flat
  `colOpen`/`colNext`/`colClose` ops rewind the vertical position per
  column through a save stack (`B.freshStart` reproduces the page-top
  formula). Leftover measure: equal shares to widthless columns, else
  equal gutters. HTML: a grid of percentage/fr tracks. Not modelled,
  recorded: vertical alignment options (top only), absolute widths, a
  column outliving its page, exact page-shrink bookkeeping inside columns,
  the `\column` command spelling (still inert).
- Overlays: `Inline.step`/`Block.step` carry an overlay range (from-step
  plus optional inclusive end) as pure grouping. `\uncover`/`\visible`/
  `\only`/`\onslide<spec>{...}` (one dim semantics for all), `\alt` (both
  alternatives on the page, the active one crisp within its spec),
  `\item<n->`, and `\pause` (a block boundary numbering cumulatively
  through `Ctx.stepBase`, list items included) elaborate to steps; a
  grouped body routes through the block elaborator when it is
  block-shaped, so lists and multi-paragraph groups step whole;
  `<+->`-style specs keep W0105, naming the spec. The PDF path expands
  each multi-step frame to one page per step before layout, recolouring
  pending content — nested explicit colours and verbatim included; covered
  means covered — to palette `covered` (default #A1A1AA, 38% black: the
  Material disabled-state opacity; themes declare `covered = fg!38!bg`,
  held to `Contrast.coveredContract`; declare `covered` to restyle).
  Only colours differ between the copies, so no step reflows — by
  construction, by test, and `Ir.dimBlocks_text` proves no character
  vanishes. HTML keeps one slide per frame with `class="step"
  data-step="n"` (`data-step-last` for ranges), everything visible: the
  no-JS handout. Recorded limits: a mid-paragraph `\pause` splits its
  paragraph, dimmed items keep black bullets, section headings inside a
  pending step stay crisp, absolute specs do not synchronise with `\pause`
  counting beyond the wrapper's own base, bare `\onslide` cannot close an
  open-form step already begun, and `\alt`'s otherwise-side dims past a
  mid-deck range (the complement of a range is not one range).
- `\note` is `Block.note`, a side channel: omitted from the PDF handout
  (the page is byte-identical to the same frame without it), an inert
  hidden `<aside class="note">` in HTML for the coming speaker view. A
  note opening a paragraph is a block in place; one met mid-sentence
  stashes and drains to its frame's end, so the paragraph flows on
  unbroken and nothing leaks. A note's body absorbs reserved characters
  as beamer absorbs them — the acceptance deck writes code-ish
  underscores in notes, and 17 E0311s said the elaborated-as-content
  design was wrong before the fixture said it.

Every unit carries a fixture + golden and a check shown failing before its
change and re-broken once after (wrapper: lookup off, 7 failures;
centering: boundary off, 4; columns: rewind off, the shared-baseline check;
overlays: identity expansion, 3; notes: layout rendering them, 1; note
absorption: off, 1). The combined `furniture.tex` deck renders to 6 PDF
pages and 4 HTML slides, both rasterized and inspected. The private
acceptance deck, PDF and HTML: 0 errors (17 before this batch, all E0311
in notes), 62 pages each (52 frames-and-dividers plus the overlay steps),
94/86 ms on this branch alone and 157/148 ms rebased onto the same-day
font-fallback batch, warnings down to constructs genuinely outside this
slice — beamer templating and fonts config (W0104/W0103, owned by the
theming and font workers or M5b), one tikzpicture (W0307, M8), one table
degradation (W0308, M8), one colour-mix key (W0304, M5b). Bench, medians
of 5 in one session against the base commit built in a scratch clone:
paragraphs 75 → 77 ms, lorem 275 → 277 ms, underline 377 → 379 ms.

2026-09-17 — fonts honour the faces a document names, and a missing glyph
is set from another face instead of dropped. Three fixes in one area, each
with the invariant that carries it:

- fontspec's per-variant face options (`UprightFont`/`BoldFont`/
  `ItalicFont`/`BoldItalicFont`) reach resolution: the compat layer carries
  them into new dotted `\fonts` keys (`sans.bold = "X"`, on any slot
  alias), and a declared face wins over the family's own variant — met by
  definition, resolved like any named face, a file name denoting that
  exact scanned face. A declared face the host lacks degrades to the
  family's best with a W0006 that says the declaration could not be met;
  W0006 now always names the face actually used, family and subfamily,
  and an unsatisfied regular says "regular" (it used to say "italic").
  `FontFace={...}{...}{...}` (positional) is not carried.
- per-glyph fallback, the mechanism `\fontfallback` was reserved for:
  layout consults a per-scalar map only when the styled face lacks a
  glyph, and sets the scalar from the mapped face at the same size in its
  own one-glyph box. The driver precomputes the map from the document's
  own scalars (`Layout.docScalars`: text, titles, verbatim, running
  content with its digits, style templates, each cased scalar's uppercase
  for small caps) — the first declared face covering the scalar in
  declaration order, else the first covering scanned face in a documented
  order (family, upright before italic, weight nearest regular, then
  subfamily and path: `FontDb.fallbackPicks`, reading candidate cmaps
  alone through the probe's now-shared `tableImage` splice). Layout stays
  pure — the disk was read before layout began — and `LEANTEX_FONT`, one
  face with no scan behind it, gets no fallback. Invariants tested: a
  document whose faces cover their text is byte-identical under any map;
  the report is once per family+glyph (W0009 substitution / W0004 drop,
  both naming families, through the existing message collapse); malformed
  or vanished candidates yield nothing, totally. Declared chains (the
  `\fontfallback` command itself) remain M8; a `\directlua` fallback
  stays a warning.

Measured: bench medians of 5, back-to-back in one session — paragraphs
77 → 75 ms, lorem 278 → 283 ms, underline 380 → 394 ms with the
attributable cost ~3 ms in the font phase (41 → 44 ms; layout unchanged;
`docScalars` folds ASCII into a bitmap because a hash insert per document
character alone cost ~15 ms), a trivial one-liner 60 → 62 ms. Corpus
PDF+HTML byte-identical by `cmp` except talk.pdf, where U+2297/U+21A6 —
dropped before — are now set from a scanned face. On the private deck:
0 errors, 52 pages, ~156 ms PDF and ~170 ms HTML; the four missing-glyph
W0004s are gone, four W0009 substitutions in their place (mono notation
set from a scanned face), and W0006 is gone — the declared faces resolve.

2026-09-17 — the pre-commit gate now rejects the four defect classes the
audit rounds actually produced, each with a stated blind-spot list and a
selftest: the quadratic prepend in every spelling (`expr ++ recurse rest`,
dotted head included — not only a `#[` literal; the `mut` self-append and
the parenthesised accumulator stay legal), a default value on an inductive
constructor field (the binder shape `(name : … := …)` is required, so a
Markdown table row in a docstring no longer fires), IO added under
`LeanTex/Core/` (FontDb excepted; `--` comments are stripped first), and a
backend reaching into the surface (`import`, `open`, or qualified use of
`Lex`/`Parse`/`Elab`/`Compat`, not import alone). Every predicate carries
positive cases — the shapes whose escape prompted it — and negative cases
from this tree, run as `--selftest` from `lake test`. Hook cost, measured:
0.03 s on a commit touching no `.lean` file, 1.3 s warm on one that does.
The AGENTS rules now say what the hook rejects, no more than the checks
enforce, and the hot-path example shows a shape the gate really catches
(`#[x] ++ walk rest`; the bare `#[x] ++ rest` it used to show is a
spelling the gate deliberately passes).

The five `expr ++ recurse` sites the review named were re-measured rather
than rewritten. `leantex dump` on the lorem bench doc at 1×/4×/16× body
scale runs 46/144/580 ms — a quadratic fit puts the copy term under 1 ms
at real document scale and ~60 ms at 16×, on a debug-only path that is
frontend-dominated. `Html.escapeText`/`escapeAttr` append `List Char`,
which copies the ≤5-element left operand and shares the recursive tail —
linear by construction, and the shape carries the escaper theorems.
`Ir.plainText` feeds on argument-sized inline arrays. All five stay as
they are; the gate keeps the pattern out of new code, where the same
spelling over a `String` accumulator did turn 4 ms into 1157 ms.

2026-09-17 — the round-three review: two corrections to the second-round
entry below, and one root cause under its four remaining symptoms. The
entry claims the recovery "takes the group wherever the line break falls";
when written, a blank line still killed the build — the recovery broke at
`.par`, W0312 said "skipped", and the orphaned group died as E0313, the
never-fatal path creating the fatal case. The claim is true only as of
this batch: the group is taken across any whitespace, blank lines
included, and never past another construct. The same entry claims the
pre-commit check "rejects any future flat warn-once key in either store";
it read keys only from two literal spellings, inspected two lines in the
whole tree, and would have passed the round-two offender `sayOnce name`.
The check is now structural about the call site — every warn-once call in
core code must spell its namespace where it stands, and a key the line
cannot prove namespaced is rejected outright — which is the enforceable
version of the claim, and what it now says.

The root cause behind the symptoms: five near-duplicate forward walks
over `Array Raw` that disagreed about when junk ends and what it is. One
`spanRaws` now carries the walk, `malformedRun` states the
stop-at-the-anchor's-line rule once, and the disagreements closed with
it: an unclosed bracket's run is content wherever content can live
(`\section[never closes IMPORTANTWORDS {Recovered}` keeps its words; only
the preamble drops the run, with W0310 already pointing at it); an
unknown environment's body splices into the same inline scan that reads
its neighbours, so its edge spaces separate words — whitespace is one
separator, never a glue and never a double — and `trimEdgeSpaces` is
deleted rather than taught what a newline is; the begin-line groups that
go with an unknown wrapper are counted by a new W0313, so W0302's "its
body is kept" no longer overstates; and `bodyIsBlock` gained the `.verb`
arm the boundary rule already had and descends into scope groups and
environment bodies — block content one group deeper is block content.
Every behavioural fix carries a test shown failing before it, and each
was re-broken once to watch its test fail.

2026-09-17 — underline skip-ink is decided by the font's own outlines. A
new `LeanTex/Core/Ink.lean` decodes TrueType `glyf` (simple and composite)
and CFF Type 2 charstrings, flattens curves to eight chords, and reports
the merged x-intervals where a glyph's ink crosses the underline band;
`Font.underlineInk` memoizes one `Thunk` per glyph (Lean's `Thunk` is
call-by-need: 0.6 µs per repeated read against 387 µs for a cold CFF
decode), and `Layout.underlineSegs` collects obstructions across the whole
line in line coordinates, dilates each by twice its run's rule thickness,
and subtracts. The descender character list is gone. Two invariants carry
the design and each is tested: decode-or-clear — every outline the decoder
cannot answer for (budgets, point-matching, CID CFF, truncation, corrupt
tables) clears its whole advance, and a declared bbox is trusted only on a
simple glyph, where it is the glyph's own point data; and band-projection
coverage — no ink inside the band escapes the reported intervals, because
ink either has a contour edge on its vertical line inside the band (the
clipped edge projection covers it) or spans the band and the midline
winding fill covers it. The fill leg requires that no vertex lie on its
scanline; the flattener now emits chord vertices computed in font units
then doubled, so every vertex is even and the odd scanline meets none
(before this, `/64` chord division could land a vertex on the scanline and
drop a crossing pair — SourceSerifPro gid 490 reported a phantom gap that
tracked the band position). Tests pin both invariants, plus a coverage
oracle that shares nothing with the fill (Float flattening, half-open
crossing rule). An earlier PDF-side approach — a white glyph halo stroked
into the band, render mode 2 — was abandoned: the halo clears vertically
too, erasing the rule under glyphs whose ink never reaches the band, and
it is a second extractable copy of the text (`pdftotext` returned it
twice). Measured now: 600 dpi poppler AND Ghostscript per-column oracle on
`\Huge \underline{anq}` — CFF 292 no-ink columns full thickness / 0
partial / 37 rule-free (the clearance beside the q stem, gaps 20/17 px ≈
2× the 11 px rule), TTF 314/0/20 (gs 315/0/19); no column anywhere has a
rule through ink, both formats, both rasterizers, and extraction returns
the text once. `scripts/bench.lean` medians of 5: paragraphs 133 ms, lorem
342 ms, and the new every-word-underlined arm 447 ms.

2026-09-17 — a runtime audit: every pass is linear, so the work went to the
constant. A 25–600-paragraph ladder (generated lorem, `leantex -v`, min of
3) shows lex, elab, layout, and pdf all scaling ~2× per doubling — no
superlinear pass anywhere — while the font machinery cost every run a fixed
~95 ms on this host (2856 installed faces once the TeX Live tree is in the
roots): a trivial one-line document built in ~99 ms of which fonts were ~92.
Three fixes, output byte-identical across the corpus by `cmp` (PDF and
HTML), each measured before and after:

- The warm scan re-walked every font tree per run (~50 ms: a readDir per
  directory, a stat per entry). A directory's listing is now cached keyed by
  the directory's own mtime — POSIX moves it on any entry add/remove/rename,
  and an in-place file edit that it misses is exactly what the per-file
  probe key catches — so a warm walk is one stat per directory; the per-file
  key stats run in parallel chunks like probing. fontdb 72 → 34 ms.
  `scripts/fontcache-check.lean` now also exercises membership staleness
  (file added, new subdirectory, removal), and fails when the mtime key is
  ignored.
- Both font-cache writes replaced the file with the current scan's entries,
  so any probing scan of one small root (the test suite scanning
  `tests/corpus/fonts`, `fontcache-check`'s /tmp directory) evicted ~2900
  system classifications and the next build re-probed everything, ~380 ms —
  observed live during this audit. Writes now merge into what was loaded:
  after a small-root scan the cache holds 2883 lines where it held 13.
- `FontDb.resolve` normalised all 2856 family names (four allocations each)
  per query, twelve queries per build: ~15 ms, found by elimination —
  a trivial document under `LEANTEX_FONT` (no scan, no resolve) builds in
  14 ms. The target normalises once; faces compare via an allocation-free
  fold. And the lexer paid a cons cell per character three ways
  (`toList.toArray`, per-token `extract`/`ofList`, `matchAt` rebuilding its
  pattern per position): lex 18 → 12 ms on the 129 KB bench doc.

`scripts/bench.lean` medians, N=5, same session: paragraphs.tex 128 → 73 ms
(lualatex 675), lorem.tex 337 → 269 ms (lualatex 1292). The resume fixture
99 → 45 ms end to end. The PLAN entries above quote ~16 ms and ~149 ms for
these documents; on this host today the *before* numbers were already 128
and 337 with lualatex slower in proportion (~476 → ~675 ms), so the older
figures reflect a lighter host state and a smaller font tree (the kpsewhich
roots landed after them), not a regression in the engine. What remains of
the constant, measured: ~34 ms fontdb (≈16 ms of it the per-file stats that
correctness demands — `fontcache-check` pins that an in-place replacement
under an unchanged name is seen), ~8 ms font file reads + parses. Layout
stays ~1 ms/paragraph and is the dominant term past ~40 paragraphs.

2026-09-17 — the developer loop, measured and two costs deleted. Medians
of ≥3, this host, `lake build --wfail` unless said otherwise. Cold build
(`lake clean` first) 14.6 s — the "~2 min" folk number is the first-ever
toolchain fetch, not a clean rebuild. Warm no-op 0.20 s. A comment-only
edit rebuilds only its own module: lake hashes the produced olean and
cuts downstream off when it is unchanged, so Pdf.lean alone was 1.8 s. An
interface-visible edit (a def added) costs 5.1 s in a leaf like Pdf and
12.2 s in Diag, which everything imports — that path is Compat→Elab→
Layout elaboration plus their C, and stays. `lake test` warm is 0.28 s:
0.20 s lake no-op plus a 79 ms test binary; no single check dominates
(the font scan reads the nine shipped faces). The two deletions:
Tests.lean's `main` was one ~710-line do block, and the compiler's LCNF
pass is superlinear in block size — 5.4 s of the file's 9.7 s elaboration
was that one decl (`lake env lean -D profiler=true Tests.lean`). Split
verbatim into per-section defs (the shape the file already used for
lineChecks), elaboration is 3.3 s and the core-edit-to-green loop
(def added to Pdf.lean, then `lake test`) 13.6 → 7.1 s. And Tests:c.o
was 4 s of clang at the default optimization: `-O0` on the test
executable only makes the add-a-test loop (append a def to Tests.lean,
`lake test`) 9.2 → 5.5 s and the binary 43 → 79 ms. Measured and left
alone: HyphenData.lean elaborates in ~10 ms over the per-module floor
(675 vs 665 ms), so its flat-string form is already the cheap one; -O1
saves almost nothing (3.9 s c.o); the pre-commit hook is 13 ms on an
irrelevant commit and ~1.0 s on a relevant one, most of it the lean
interpreter starting on precommit.lean, honest both ways.

2026-09-16 — correction to the M3a entry below: the pending-key mechanism
is gone. `pagePending` reported a declared-but-unimplemented `\page` key as
pending with its milestone rather than as a type error; its last entry
(`header`) left the list when running content landed, its only consumer
went with it, and the empty list is now deleted. An unknown `\page` key
today is E-diagnosed like any other; a future declared-ahead key gets a
design decision then, not a dormant list now.

2026-09-16 — the second-round review: two corrections to the entry below,
and its last findings closed. The entry below records the `\title` typo's
E0313 as closed; that held on one line and failed on two — the `.unclosed`
recovery searched only the command's own line, so `\title[never closes`
with its group on the next line still died as a fatal E0304 + E0313 with
no output. The recovery (`skipOptArg`, shared with `\section`) now takes
the group wherever the line break falls, and a declaration with no group
left is skipped whole with W0312, never an error. The same entry defends
unknown environments staying paragraph boundaries because "guessing
block-ness from a body's shape would make paragraph structure depend on
the wrapper's content"; that rationale is withdrawn — it rejects exactly
the mechanism the `@input:` exemption in the same clause uses. One rule
now: the body's shape decides, so an inline unknown environment stays in
its sentence and a block one breaks it, through the same argument scan
either way. With them: a skipped preamble command's junk stops at the
next construct rather than the next line, so a declaration sharing the
malformed command's line survives and the misdirecting W0304 is gone for
good; `\section[short]{long}` — the one optional-argument site the shared
scanner had not reached — goes through it with the same never-fatal
recovery; and Compat's `sayOnce` keys are namespaced (`ctrl:`/`spec:`/
`beamer:`) with a pre-commit check that rejects any future flat warn-once
key in either store. Every behavioural fix carries a test that failed
before it.

2026-09-16 — the M5 slice's review findings closed, root causes first.
One bracket-argument scan existed in four copies that disagreed about two
rules, and the missing halves each lost content silently: an unclosed `[`
emptied a frame, swallowed a `\palette` declaration and then advised the
author to write one, or turned a `\title` typo into a fatal E0313; a frame
whose content merely opened with `[1]` lost it. The rule, now in one
`scanBracketArg` every consumer shares: an argument's `[` opens on its
command's line and closes; anything else is content, reported as W0310 when
a bracket never closes. Alongside it: `Dim.mm` was TeX's 7227/2540 in an
engine whose point is the big point, so the default beamer stage disagreed
with `\page{ width = 160mm }` by 0.375% — now 7200/2540, held by an
`mm_eq_inch` theorem rather than a test; warn-once keys gained `env:`/`ctrl:`
namespaces so an environment and a command of one name cannot silence each
other; the overfull-line collapse carries its count, the only signal of
scale a spanless warning has; and the `@input:` wrapper is a paragraph
boundary only when the file holds block content, so an inline `\input` stays
in its sentence — an unknown environment still breaks the paragraph,
deliberately, because guessing block-ness from a body's shape would make
paragraph structure depend on the wrapper's content. Small closures with it:
`\hline`/`\cline` inert and `\multicolumn` keeping only its cell text,
milestone references reconciled against this plan (figure, fontfallback,
external, and W0003's math note), verbatim dropping every trailing blank
line, and a second `\frametitle` warning (W0311) instead of silently
replacing the first. Every fix carries a test that failed before it.

2026-09-16 — the first coherent M5 slice: the real beamer talk compiles
best-effort to both backends, 66 errors to zero, and every remaining
diagnostic names its construct once and the file that holds it. The load
divided into invariants, each now pinned by a test:

- Unsupported configuration is skipped whole. Beamer templating
  (`\usetheme`, `\setbeamercovered`, `\addtobeamertemplate`, …), TeX's macro
  layer (`\def`, `\newenvironment`, `\ifdefined…\fi`), `\directlua`, and
  `\setmathfont` each consume their own arguments and warn once — never an
  unknown-command error plus a stray-content cascade per construct.
- Content survives what the engine cannot render. Unknown environments keep
  their body (arguments on the `\begin` line go with the wrapper), reserved
  constructs warn once per name instead of erroring, `\textcolor` with an
  unresolvable key keeps its words, and overlay specifications strip to
  beamer's own handout semantics: everything shown, one warning.
- `{verbatim}` is a first-class block set literally: no reflow, no invented
  hyphens, spaces as no-break kerns, a blank line still a line (a forced
  break into an empty line has no feasible predecessor and the breaker
  dropped it — re-introduced once to watch the test fail). 4/5 body size,
  the code-frame convention that fits 80 columns on a 16:9 slide.
- A frame is an IR block and a page boundary (Principle 9): one `<section>`
  of the HTML deck, one page of the PDF handout, sections between frames
  their own divider pages, spill to a continuation page rather than a clip.
  Titles come from the adjacent group — adjacent meaning no paragraph
  break, where LaTeX's own argument scanning stops — or `\frametitle`.
  `\title`/`\author`/… store from preamble or body; `\maketitle` sets a
  centered title frame and feeds the PDF Info dictionary. The slides class
  fills beamer's stage (160×90 mm at 16:9) unless `\page` says otherwise.
- Math environments carry their source whole and tables degrade to rows of
  cells, so `&` never reaches inline elaboration as a reserved-character
  error. TikZ is skipped with one honest warning, never spilt as source.
- `\input` files ride in a synthetic wrapper environment, so a diagnostic
  names the file that holds the construct — flat splicing had 21 of the
  talk's diagnostics pointing into the main file at lines it does not have.
- A fontspec face name ("Family Light") resolves via family+subfamily when
  no family matches: the named weight serves as regular, its italic sibling
  comes along, and a bold request degrades with the existing warning rather
  than silently substituting a heavier face.

Measured on the private deck: 0 errors, 24 distinct warnings each naming
one construct, 52 pages against the lualatex build's 54 (which include
overlay steps), ~80% of the word count surviving (the gap is math set as
source, dropped page-number furniture, and unrendered tikz labels), 150 ms
PDF, 173 ms HTML. Layout on the 30-page bench is 151 ms against the 149 ms
recorded before the slice. Honest degradation, recorded: `\centering` and
frame options are dropped with a warning, math is source text, tables are
rows, tikz diagrams and speaker notes are absent, and a handful of exotic
glyphs the Fira faces lack are warned per character (per-glyph fallback is
M8). Found, not chased: every `FontDb.scanRoots` rewrites the shared disk
cache with only its own roots, so a test run evicts the system entries and
the next build re-probes ~2900 faces (~340 ms).

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
8. Elaboration is non-blocking, and loss is never silent. For every input
   the parser accepts, a document comes out — but what the engine
   guarantees about content is honest now: content is either kept, or its
   loss carries a diagnostic whose severity derives from the loss itself
   (`Loss` in Diag.lean). Declared content the reader of the output cannot
   recover is an error unless the document accepted it (`\allow{...}` in
   the preamble, `--best-effort` on the CLI); a degradation the reader can
   see, and configuration the engine does not model, are warnings; and
   acceptance always prints in the build summary, so it is declared, never
   ambient. The diagnostic names the span and, where one exists, the
   native spelling. Only malformed syntax, an unaccepted loss, a failed
   `\assert`, and a font that cannot be found stop a build. Best effort is
   a mode a document opts into, not a fallback the engine imposes.
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
- Exit codes are the API: 0 ok · 1 document errors (and, under `--werror`,
  any warning that was not accepted) · 2 assertions failed ·
  3 usage · 4 internal.
- Surface additions for the second surface and backend, contract unchanged:
  input may be `.md` or `.tex`; `--emit pdf,html,reveal,md`; `--css
  bulma|none`; `--math-boundary <tool>`; `expand` (md → tex ejection). The
  porcelain event schema gains inclusion-inventory records.

## Hyphenation

Liang patterns per language, embedded as generated Lean data with each
upstream licence notice preserved, one `langs` row in
`scripts/gen-hyphen-data.lean` per language — adding a language is adding a
row. Regenerate with `lake env lean --run scripts/gen-hyphen-data.lean`.
Shipped rows: American English from `hyph-en-us.tex` (ushyphmax: Knuth's
frozen `hyphen.tex` plus Gerard Kuiken's additions — a strict superset, 4938
patterns vs 4447), hyphenmins 2/3; French from `hyph-fr.tex`; German
(1996 orthography) from `hyph-de-1996.tex`. A document's declared language
selects the set through `Locale.forTag`/`Hyphen.forTag`; English is the
default.

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
- M8 figures and boundaries: asset embedding (PNG and JPEG landed
  2026-09-17, including alpha via SMask; PDF pages as form XObjects
  remain), the external-render boundary with content-hash cache (TikZ),
  verbatim code blocks, per-glyph font fallback chains.
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

- 2026-09-17: no baseline grid. The page model is glue with declared
  rubber, set at one ratio per page, with line height following the
  tallest run — a hard grid forbids both, and TeX made the same trade.
  Bringhurst's "measured intervals" rule survives as the rhythm-multiple
  theorem over the engine's own defaults instead; a per-document grid
  diagnostic would fire on any document using rubber, which the diagnostic
  boundary forbids. Revisit only if a fixed-layout class (no shrinkable
  glue) ever lands.
- 2026-09-17: the readable-measure band is enforced as W0201 (45–90
  characters per line, Bringhurst's satisfactory band widened to
  Butterick's outer edge), computed from the body face's lowercase
  alphabet length via the copy-fitting fits, scoped to continuous text in
  page classes, silenced by `\page{ measure = free }`. The undeclared
  letter page takes a 26-pica text block so the default satisfies the band
  it enforces.

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
