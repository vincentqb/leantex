# AGENTS.md

leantex: fast, certified, modern document engine in Lean 4 — one language,
two surfaces (tex primary, markdown as sugar), two backends (PDF 2.0 and
HTML). The living plan is `PLAN.md` — design decisions and milestone status
land there, not here. Never record personal information (names, emails, and
the text or topics of private documents) or local paths to private documents
in this repo; refer to the private reference corpus abstractly.

## Setup

- Toolchain: elan-managed, pinned by `lean-toolchain` (track stable; v4.34.1 today).
- This host is AL2 (glibc 2.26): the toolchain's bundled clang cannot run.
  Export before any `lake` command (verified working):

  ```bash
  export LEAN_CC=/home/linuxbrew/.linuxbrew/bin/clang
  export LIBRARY_PATH="$(lean --print-prefix)/lib:$(lean --print-prefix)/lib/lean"
  ```

- Interactive shell is fish: unmatched globs are hard errors; run bash-isms
  via `bash -c '...'`.

## Build / test

- `lake build` — proofs are checked here; a broken theorem is a broken build.
- `lake test` — golden corpus + property tests. Run both before declaring done.
- `git config core.hooksPath scripts/hooks` — one-time: installs the
  pre-commit hook (build with warnings-as-failures + convention checks).
  The harness is Lean throughout (`scripts/*.lean`, run via
  `lake env lean --run`); the one exception is this hook, where git executes
  a file, so `scripts/hooks/pre-commit` stays a few-line sh trampoline into
  `scripts/precommit.lean`.
- `lake exe Tests --update` — regenerate goldens after an intended IR change.
- Deeper oracles, not in `lake test` (too slow / need TeX): run
  `scripts/kp-fuzz.lean` when touching line breaking,
  `scripts/hyphen-diff.lean` when touching hyphenation,
  `scripts/compose-fuzz.lean` when touching the preamble apply sites in
  Elab.lean (declaration commutation — T1's oracle until the theorem
  closes),
  `scripts/oklab-roundtrip.lean` when touching `Core/Oklab.lean`
  (sRGB→Oklab→sRGB identity over all 2²⁴ inputs, ~30 min),
  `scripts/img-fuzz.lean` when touching the image decode paths
  (`Image.decode` totality — truncations, mutants, random blobs — plus the
  pristine fixtures decoding to their known sizes), and
  `scripts/fontcache-check.lean` when touching the font scan or its cache
  (it replaces a font under the same name and checks the answer follows
  the file).
- `lake env lean --run scripts/owed.lean` — what does this engine not yet
  guarantee? Prints every owed obligation (a type-checked statement whose
  proof is open, staged under `Obligations/`) with owner, source, and
  blocker. Exits non-zero only when the ratchet is violated.
- `lake env lean --run` interprets the `.olean` files as they stand and
  rebuilds none of them, so build the libraries a script imports first
  (`lake build scoreboard` for `scripts.Board`). A script library built
  against an older `LeanTex` structure crashes the interpreter with a bare
  segfault: `Ir.Pic.LabelInk` gaining fields took `scripts/html-oracle.lean`
  down that way.
- Performance claims come only from `scripts/bench.lean` (vs lualatex on the
  corpus), never from reasoning about the code.

## Conventions

- Before fixing an issue, write down the invariant whose absence allowed it —
  as a theorem statement when it is one, as a test when it is not — then fix
  to that invariant, not to the symptom. The test fails before and passes
  after; if the lesson generalises, it becomes a rule here or a hook check.

- A claim about what a page shows comes only from a rendered page or the
  shipped-page census (`censusChecks` over `Layout.Out`, `Check.Shipped`),
  never from an IR dump or golden — goldens witness elaboration, not the
  artifact; six visual defects once passed a fully green suite this way. A
  visual bug's regression test asserts over `Layout.Out` or the typed HTML
  tree (or a raster), never over `Ir.dump`.

- The obligation table: adding a kind of thing owes an invariant, decided
  before the code. The PLAN 2026-09-17 obligations entry carries each
  row's why and the defect it would have caught; enforcement in
  parentheses.

  | when you add… | you owe… |
  |---|---|
  | an `Ir` constructor | an explicit arm in every IR-to-IR walk and both backends — no wildcard (compiler + hook) — and its census fact once it ships ink |
  | a golden fixture | a `censusTable` row asserting its shipped pages (`lake test` coverage check) |
  | a backend emission | the census assertion that it appeared (`censusTable`) |
  | a PDF text-positioning emission (a `TJ` element, `Tm`, `Tz`, a `/W` width) | placement by the viewer's arithmetic over what the file states — the pen model reads the file's own spellings (`Sp.toPtMilli`, `pdfWidthμ`), never the writer's belief of where its pen stands (`place_between`) — and every corpus page held to its layout's glyph positions by the artifact tier (`artGlyphPlacementOffences`). The writer once believed its pen stood at the layout's x after each run while the viewer advanced by nominal widths: kerns never reached a page, and text after a font change overlapped the word before it |
  | a diagnostic code | a `DiagCode` constructor with its declared `Loss` — severity and the code letter derive from the loss, one code one meaning (compiler + `lake test`; the hook rejects a severity written outside Diag.lean) — a firing witness in `diagWitness` whose rendered form lands in the diagnostics golden, and a message that passes the voice lint: self-contained (no repo file, no milestone), an action or no help, one convention (Tests.lean; the hook rejects repo-internal references in strings). Registering a new code is one constructor, one `spec` arm, and `count + 1` — nothing else: `all` is derived, and `all_complete`/`all_nodup` make a miscount a build failure in both directions. It also owes a decision: a `DiagAudit.registry` row (`Tests/DiagAudit.lean`) with its verdict, target rung and a pin that resolves, or the `diagaudit` tier falls |
  | a design constant | a token, or the source written where it stands (hook, backend files) |
  | a recursive IR walk | a `List` companion + accumulator (hook), and its census statement: a public Block/Inline walk ships a theorem named with a registered conservation suffix — `_text` (census equality, stated as a `Conserves` instance), `_covers`, `_id` — or the one-line refusal `-- conserves: none — <why>` beside the def (hook, whole tree) |
  | a palette role or token the engine reads | one resolving site, its contrast contract, a per-bundle check (`Ir.Design.ofPalette` is the resolving site — the argument is a palette because the layout resolves the *epoch* palette in force at a frame and `Design.ofDoc` the document's, through the one chain, `frametitle_agree`; Contrast.lean holds the contracts, the bundle pins the checks) |
  | a page-opening path | a declared vertical distribution and ground, never a default (`Layout.VDist` is the vocabulary; the ground is the palette in force, read at `Ir.frameGroundOf`, which `artStageGroundChecks` holds both artifacts to; declare through them) |
  | a furniture element | a declared alignment, never a hard-coded `.center` (`align` on `ElementStyle` carries it) |
  | an `AssertKind` | its judge in `Check.one` (exhaustive match) and a test that breaks it once |
  | a cached external answer | the *failure* cached too, under the same content key, replayed as the identical diagnostic — and an attempt with no evidence the tool ran (kill, failed spawn, nonzero exit with no log) cached not at all (`Cli/PicCache.lean` holds the policy as values; `step_cold_exact`, `remembers_verdict_exact`, `unlogged_retried_exact`, `picCacheChecks`) |
  | a document class | sourced defaults, and its contract as implied assertions |
  | a `nativePackages` entry | `tests/compat-index/<pkg>.txt` covering the package's *documented* command list — the manual section named in its header, one row per command, `impl` proved by no W0301/W0302 — nor W0012, under which a formula is its own source text and differs from the renamed call by spelling alone — and `refuse:<code>` by the code firing (`lake test` probes every row; the hook rejects an entry without its file) |
  | a math symbol | a row `scripts/gen-mathsym-data.lean` derives from its declaring file (class) and unicode-math's table (scalar), not a hand row: a hand row of `MathParse.ctrlAtom` that shadows a generated one says the same or is a `handDivergences` entry; a declared command with no scalar of its own is a refused row naming the glyph it lacks; its glyph is in the shipped math face or a `firaGaps` entry, both ways; and its line in a parity fixture holds its scalar to lualatex's (`mathSymChecks`, parity `amssymb`/`mathsym`) |
  | a text symbol or accent | a row `scripts/gen-textsym-data.lean` derives from tuenc.def (the TU encoding lualatex sets) and the kernel names latex.ltx defines as one, not a hand row: a hand table that answers a generated name first (`Elab.escapes`, `Bib.charCommands`, `Lex.textSymbols`, `Compat`'s literal rewrites) sets the same scalar, an accent composes by NFC to every tuenc.def composite, and a palette role no symbol spells (`textSymChecks`) |
  | a gate on the declared setup (context, config, declarations, state) that names, silences, or demotes a loss | the check that falsifies its premise, named beside it: `-- premise: <pin> — <why>`, or the refusal `-- premise: none — <why>` (hook, whole tree; the pin must resolve to a theorem the build checks or a check block the suite runs). A premise about another subsystem is a claim, and prose rots — three defects shared that shape. The shape of such a check is two builds differing by the gate's own condition: a byte-identical artifact with different diagnostics means nothing else was handling the case, so the gate is a silencer (`pictureKeyGateChecks`) |
  | a diagnostic emission at a site another code already names | one accounting, not two: fold the fragment into the first code's message, or land a `siteAccounting` row naming the file that owes the merge (`siteAccountingChecks`). A `degraded`/`pending` code is *censused* (`DiagCode.censused`) and the census runs on `subject` alone — `tallySites` returns a subjectless diagnostic untouched — so such a code carries a subject at every emission, or a frozen `subjectDebt` baseline row that may fall and never rise (`subjectCensusChecks`). `W0301` counted its command while `W0341` printed once per site for a fragment of that same command, at the same span |
  | a comparison level with a declared blind spot | the pair of inputs differing only in what it ignores, asserted equal under that level and unequal under the level above — for **every** level with a blind spot, not the newest one (`parity --selftest` holds `censusKey` blind and `orderKey` sighted, and `orderKey` blind and `lineKey` sighted). A "blind to" column nobody checks is prose: the reading-order level was believed to see line breaking until two pages with identical scalar sequences and different line partitions both passed it. Also owed: the level's *ordering premise* as a check, not a docstring — the line reading claimed first-paint order was reading order, which a float placed away from its source position falsifies. A record format owes the same of its empty value — round-trip every field empty, which is the arm a real fixture eventually takes and the one a hand-written example never does |
  | a `forIn`/`Id.run` loop whose state an owed statement must cross | the invariant, written in the loop's own module (where the private state is nameable) and exported as the corollary the statement reads — never the loop restated as a fold. `LeanTex.Core.Loop` reads a loop that `break`s, which is exactly where the stdlib's `foldl` bridges stop, and `Obligations.floorMask_id` is the worked example: three loops, no change to the walk. A pure invariant is blind to how much input the loop consumed, so a claim about the loop's *value* (a census, a round trip) owes the progress-indexed form or its own algebra instead — say which of the two the statement is (review) |
  | a measurement a goal is judged by | a tier, not a number in a report: `tests/scoreboard/<t>.tsv` (`<t>` matching `[a-z0-9-]+`, which the aggregate faults otherwise; `#` provenance lines, then `item<TAB>integer`, higher is better, sorted, unique) written only by `scripts/<t>.lean` in the three modes (regenerate / `--check` / `--selftest`), plus its name in `Scoreboard.declaredTiers`, whose absence is a **fault** unless the name is also on `pendingTiers` — and a pending name whose tier has both halves fails the selftest, so landing a tier and removing its name are one commit. The contract the aggregate reads is `--check`'s exit status alone: a porcelain line (`tierLine`) is optional and can never override a non-zero exit, and `# encoding:` is an optional ranking hint (absent: gated, unranked). An absent or empty baseline under `--check` is a fault; only regeneration starts from nothing — and the aggregate faults an empty or rowless baseline itself, whatever its producer exits. One ratchet for every tier (`Board.ratchet`, applied by the `tierMain` a producer is built on): a fall or an unretired vanish fails, and so does an **unrecorded rise** (`result=stale`) — record it by regenerating, in the commit that earned it, as `subjectDebt` and `siteAccounting` are read in both directions. Weakening is a request a human writes in the committed file and regeneration spends once: a fall needs `# lowered: <item> <old>→<new> — <why>` naming exactly the fall from the committed floor, and is written back as the record `# lowered (applied): …`, which authorises nothing again, so a second fall of one item needs a second request; a committed file still holding a request that names its committed floor is `stale`, and one holding a request that names any other floor is a fault (the message says: mark it `# lowered (applied):` if it records a fall already written, otherwise correct or delete it). A shrink-is-good metric is encoded as headroom (`cap - count`), never as the count, because a ratchet points one way for every tier; an item is retired only by a `# retired: <item> — <why>` line written beside its row, which regeneration applies by dropping the row (a measurement that still produces a retired item is malformed), and a whole tier only by a `# retired-tier: <why>` tombstone in its file. `scoreboard --check --base <rev>` is the gate the land tool runs, `<rev>` the main it lands onto: against the files committed at `<rev>`, read with replacement objects off, a fall or a vanish needs a line new since `<rev>` (a record spending a request `<rev>` holds is new), a baseline present at `<rev>` may not disappear, a base git cannot read is a fault, and every tier file in the tree — one new since `<rev>` included — must validate and is `stale` while it holds any request, so neither a hand-edited floor nor a deleted-and-regenerated baseline launders one; a pass prints each weakening and each new line it credited, control characters spelled out, which is where the human reads them. `--check` is hermetic — committed references and in-repo data only — and anything needing another engine, the network or the host's TeX tree is a report (`scoreboard --bench`), never a gate (`scoreboard --selftest` fans out to every tier's) |
  | an HTML emission assistive technology must name or reach, or is told to skip — an `<svg>`, an `<img>`, a box a stylesheet rule scrolls (`overflow: auto`), a box under `aria-hidden` | its fact in the judge `HtmlDoc.a11yFacts` — a scroll rule also enters `declaresScroll`, or the judge cannot see the box: a name (`carriesName`), a non-blank `alt` or a declared decorative role, `tabindex="0"` and — where the role takes one — a name, and no tab stop under `aria-hidden` (`tabbable`). A judge that skips what `aria-hidden` removes still counts the tab stops in it, or hiding a link scores as a fix: a linked logo shipped that way. `htmlA11yChecks` holds `svg`, `scroll` and `hidden-focus` at zero on every shipped page; the `htmla11y` tier ratchets the rest, and axe over the rendered corpus is its report |
  | a box a stylesheet rule bounds and scrolls on screen (a fixed height, `overflow: auto`) | its print lift: paper has no scroll, and a scroll container is monolithic there, so it clips what exceeds it — on paper the box grows or its lines wrap, and growing leaves no sheet blank (`print_lifts_stage_bounds_covers` for the deck's stages; the reader oracle's `print-spill` and `print-sheets` rows on the printed corpus). A frame of 30 items once printed 14, and the first lift printed three blank sheets |
  | a surface reader (a second front end to the one elaborator) | its spec suite as a *classifier*: every case carries a committed verdict — `match`, `rejected`, `divergence` (with its reason in the script), or `owed` — and an unclassified deviation fails. **No bucket may be certified by the reader under test**: a strict refusal is a claim, and `rejected` needs corroboration from outside the reader — a raw-HTML refusal's text passes through the spec's own expected HTML verbatim, an indented-code or lazy refusal is on a reviewed list that fails in both directions (`tests/commonmark/strict-reviewed.tsv`) — or the case is `owed` with the refusal named. A case whose run names a markdown route (or a `W0110`, an option the desugaring leaked) is never a `match`, however the trees compare; when the trees agree once exactly the named gaps are hidden, its note names the gap that blocks it — the verdict row an IR gap owes, never a false match — and a gap construct the expected page carries that the engine's page drops, where the element it sits on did ship, must be named by the run or every mode fails (`silentGaps`: a list before `* * *` once shipped no rule and raised nothing). A case waiting on a dialect decision the user owns carries that decision as its note and stays `owed`. Comparison is over trees, and every attribute is compared unless a declared row drops it beside what it hides; an attribute that decides whether content reaches a reader (`hidden`, `aria-hidden`, `role`, `lang`) is never a row, on a construct or on the chrome the comparison unwraps. `--selftest` breaks every normalization in both directions: it hides what it declares and not the difference beside it (the class normalization once hid three lost languages, and a six-attribute keep-list certified a page whose every paragraph was `hidden` as 323 matches). The reader desugars to the surface AST, and no reader text reaches a re-parse: where the elaborator reads a construct back from option text (a listing's language, an image's alternative), what crosses is an IR value (`Ir.ListingLang`) or a spelling the elaborator's own splitter is checked to read back exactly (`MdDesugar.altSource`), never the author's text — a `]` in an info string once ended the option head and leaked into the code. A construct the surface AST cannot express is *routed* by a keyed diagnostic whose loss class is decided by what reaches the page — `pending` only where nothing does — and a construct the AST *can* express is carried through its one existing resolving site, never routed (`scripts/commonmark.lean --check`, `tests/commonmark/verdicts.tsv`, `tests/scoreboard/commonmark.tsv`) |
  | a refusal of a construct by name (a definition, a redefinition, a use) | a check quantified over what it refuses, two builds apart: the refused spelling raises no error, is named by its code alone, and ships the page of the document without it — or, for a use, the page of its braced spelling — since a refusal that adds ink or fails the build is the loss it claims to avoid (`refusedEnvChecks` over `builtinEnvNames` × `splitShapes`, `delimitedUseChecks`). What the refused construct's parts owe is judged by its definer, never by the parse that read them (`Elab.settleSplits`) |
  | a name the engine gives a raw that a document could also write — an environment wrapper, a definer body's half | a character no word token holds — a space, since a word is a run of characters neither special nor white space and a document's environment name is one word — never a prefix a word can spell: the `@` claim was false twice, and `\begin{@open:center}` failed a build as a half (`reservedEnvNameChecks` over `Parse.splitOpen`, `splitClose`, `inputEnv`) |
  | a script that runs git in repositories it makes — a harness, a probe | one guard before every command: git names the command's repository from the command's own directory and environment, and the command runs only when that repository, and anything it creates, lies inside a fresh root the run made — a push naming by path a bare repository the run made; the run refuses to start when any repository encloses its root; every child runs under `GIT_ALLOW_PROTOCOL=file` (`hcall_writes_owned`; the `hookdir`, `incheckout`, `guard` and `nonet` scenarios). Scrubbing inherited variables is one layer, not the guard: without the scrub, a harness run under a hook's `GIT_DIR` pushed that repository's `main` to its origin and rewrote its config |
  | a vendored third-party corpus | its licence verbatim beside it; a `PROVENANCE.txt` naming the upstream commit and what was taken, what was left and why — a user's own document is left, since fixtures here are invented; a `SHA256SUMS` over the upstream bytes that `sha256sum -c` checks from that directory; only documents the reference builds under `-halt-on-error`, so every one is in the denominator; and the reading that needs neither fonts nor TeX as a tier, its premise checked by the report wherever both readings exist (`tests/external/flashtex`, `scripts/external.lean`: a 0 is a refusal, held on 216 of 216 and missed on 1 of 1,031 upstream, where a face refuses a TAB after elaboration). `tests/commonmark` vendors a spec the same way |
  | an HTML rule for an engine role that only spaces or styles, or a block margin | a class on the element it governs, never an element of its own (`withClass`) — a consumer stylesheet's combinators were written against the element tree, and one wrapper `div` took a site port's layout in every viewport; the environment and its declaration ship one tree (`trivlistChecks`). A vertical margin on a block element lives only in `blockGapRules`, all inside `:where()`, resets first (`blockGap_owner_contract`; `htmlRhythmChecks` fails any other rule that declares one) — an element rule at (0,0,1) once outranked every gap rule, and no paragraph gap rendered |
  | a setting a document declares — a length, a counter, a size, a key — or a default that stands in for one | LaTeX's behaviour, exactly, measured under lualatex on a synthetic probe, down to what LaTeX itself discards: that is discarded here too and said in a note, never honoured against LaTeX (a preamble `\itemsep` reaches no list, since the class's `\@listi` sets it again — `Compat.paramSites`' reset rows, `paramSiteChecks`). A departure only when it is *measurably better* on a named axis — contrast (a WCAG ratio), accessibility (an `a11yFacts` fact), rhythm (a baseline gap on `Layout.Out`), alignment (an offset in sp) — and *barely different* inside a bound declared beside the rule (an Oklab distance, a fraction of a point, a sub-pixel offset), a check holding both. A setting no engine site reads is named where it stands (W0104, keyed by the parameter), never translated onto a token nothing reads: every carried row sets exactly the page its native spelling sets, and a different page from the document without it |
  | a breakage the user reports | a `Reports.reports` row (`Tests/Reports.lean`): its date, the report in abstract words — the construct, never the document — and pins to its guards that resolve or do not compile (`thm%`, `check%`, a tier item; an out-of-repo acceptance run in abstract words), closed only as `guarded`: the tree its guards failed on (the broken commit, or the fix reverted) and whose record says so, before the fix lands. A report with no guard yet is `owed` to a named owner under its guard's name, and the suite fails once that name lands until the row is promoted; the `unwitnessed` and `owed` counts are baselines held in both directions (`reportChecks`). A green check asserting the reported behaviour keeps the defect: two rows once pinned the user's false W0104 as expected |

- TeX package/class warning and info controls are log-only compatibility rows: consume their exact groups in `Compat.meaningFree`, require N0100 accounting through a deferred-hook test, and never let those groups enter body recovery. Arbitrary unknown commands must still preserve their arguments.

- Theorems are stated on the IR first. A fact both artifacts must honour
  (structure, numbering, census, palette, language, alternatives) is one
  theorem over `Ir`/`Theme`/`Design`, and each backend's version is a
  projection corollary over the one IR value both artifacts read —
  `html_fonts_cover_pdf`, `backend_gaps_agree`, `footBand_projects` are the
  shape. A backend theorem with no IR statement behind it either names a
  fact genuinely of the artifact (placement, escaping, xref) or is
  mis-layered — say which in its docstring.

- A proof that resists is a factorization finding, not a tactic problem:
  case analysis the statement never mentions, a private state the
  statement cannot name, a heartbeat wall. Write it as the refactor it
  needs — a field the statement can read, a state split, an equation
  pack — and stage the statement in `Obligations/` meanwhile. Never work
  around it with fuel, `decide` over samples, or a test in a theorem's
  clothes.

- The **kernel** owns the page models (flow / frame / face — three today,
  `report`'s chapter-page a candidate fourth). A **document class** is a
  named bundle *over* a page model: defaults, furniture semantics, implied
  assertions, metadata contract. `resume`, `webpage`, `poster` are classes
  in this sense — as `article`, `slides`, `card` already are. `\theme`
  stays the *visual* layer only (palette, tokens, styles), orthogonal to
  class, as LaTeX's packages are orthogonal to its classes. The guard is
  the record shape (`Ir.ClassRecord`): a class is a *record*, not a module
  with its own layout code — if a proposed class needs layout code rather
  than values, assertions and furniture flags, it is asking for a new page
  model and goes to the kernel discussion instead.

- Theorem shape suffixes are a registry, not a habit: `_text` (census
  equality; state it as a `Conserves` instance), `_covers`, `_id`, `_inj`,
  `_rectangular`, `_exact`, `_monotone`, `_fixed_point`, `_contract`,
  `_set_eq`, `_between` (a value inside two named bounds), `_mem` (the
  result is drawn from the input set), `_accounts` (an empty result is
  paid for by a diagnostic or a write — `rewriteCtrl_accounts` is the
  shape), `_named` (every element of a census has a diagnostic whose
  `subject` is its key — `pending_named` is the shape; the census is a
  fold, the judge reads the same fold, and matching is the structured
  `Diag.subject`, never the message text), `_projects` (a backend value
  is the projection of one IR value — `footBand_projects` is the shape),
  `_agree` (two projections of one IR value agree — `backend_gaps_agree`
  is the shape), `_gated` (a mutating output implies a proven state — the
  landing's merge and push are proposed only from a state whose every gate
  observation was ok; a shape of its own because the antecedent is the
  *action*, not the value, so no other suffix's reading applies), `_pinned`
  (the landing's run invariant — the gated tip, the gate tree's read-back
  and the landed `main` are one sha — holds initially and is preserved by
  every transition: `init_pinned`, `step_pinned`, `trace_pinned`), `_owned`
  (every write an action declares is one the state it was proposed from
  owns — a shape of its own because the conclusion is about *where* an
  output writes, not what it names: `step_writes_owned`,
  `trace_writes_owned`). A new
  property instantiates a
  suffix, or the review says why
  it is a new shape; the first three are what the hook's walk gate looks
  for. `_in_measure` is not a shape (`kern_measure_exact` once carried
  it). A step lemma is not a property and takes no suffix from this list:
  `<step>_<field>` says what one step of a walk does to one field of the
  walk's state (`pushRun_runs`, `moveTo_plainOps`), and the statement the
  walk's step lemmas assemble carries the shape (`contentOps_text`,
  `mark_ink_exact`). A contract over shipped bundles quantifies over `Theme.builtin`,
  never per bundle — adding a bundle is entering the contract.

- A new collector over the IR is a `foldBlocks`/`foldInlines` leaf
  function; a new leaf-rewrite is a `mapInlines`/`mapBlocks` function; a
  hand-rolled mutual walk states its reason beside the def. Ten copies of
  the two generic shapes accumulated before the walks were factored — two
  of the three wildcards among them hid real gaps (a footnote's image
  shipped a silent placeholder).

- A generated module (`*Data.lean`) carries only data; contracts and
  lookups over it live in a hand-owned module (`LocaleContract.lean` is
  the shape). Code embedded in a generator's output drifts from the
  checked-in file the first time one of the pair is edited alone, and no
  check can see it: regeneration needs this host's TeX tree, so CI cannot.

- Pure core: modules under `LeanTex/Core/` do no IO (`FontDb` is the one
  exception; the pre-commit hook rejects new IO in core). Files, fonts,
  anything external surfaces as request values the CLI driver fulfills
  (effects as data).
- The artifact is a function of the document and the font environment;
  flags are not arguments to it. What to build is the document's to declare
  (`\output`); a flag says where output lands (`-o`), when (`--watch`), how
  the run reports (`-q`/`-v`, `--porcelain`, `--color`), the run's exit and
  acceptance policy (`--werror`, `--best-effort`), or extends the font
  environment (`--font-dir`). The statement is the theorem
  `artifact_flag_free` (Args.lean); the hook rejects a `Config` read in
  Main.lean whose field is not on the declared allowlist
  (`driverConfigReads` in scripts/precommit.lean) — the token a new flag
  would start from on its way toward a backend. `--math-boundary` is the
  one recorded remainder, carried as a named hypothesis in the theorem
  until `\output` grows its key.
- Removing a CLI surface is a migration, not a deletion, and its callers are
  not all in this repo: the site port's build script and every private
  document's build recipe invoke the binary too. Grepping this tree returns
  clean and proves nothing — `--emit` was deleted that way and broke the site
  build on the next run. No hook can see those repos, so the check is manual
  and belongs in the same commit: run every out-of-repo build that invokes
  leantex before declaring the surface gone.
- Backends consume the IR and nothing else. A backend never re-parses, and
  never reaches back into the surface AST — that is how md→PDF and tex→HTML
  stay free instead of becoming N×M special cases. The hook rejects a
  surface reach-in — an import, `open`, or qualified use of
  `Lex`/`Parse`/`Elab`/`Compat` — in a backend module.
- HTML is built as a typed tree with a certified escaper, never by
  concatenating tag strings. Any new node type goes through the escaper by
  construction; if you find yourself writing `"<" ++ …`, stop.
- No backend emits script to compensate for a platform. Say what the page
  means, declaratively, and let the platform — or the stylesheet framework a
  document chooses — decide how widely it works. Where a declarative feature
  is unevenly supported, the honest floor is the degraded state (a control
  that is always visible, not one that is permanently hidden), and shipping a
  shim instead buys a small effect at the cost of a permanent escaping
  obligation and a rule that then holds only approximately. Two script paths
  stand: `--math-boundary`, for genuinely computational behaviour a document
  asks for by name, and the slides class's constant keyboard/uncover script —
  permitted because it is a constant (no escaping obligation,
  `deck_script_constant` pins the literal), gated on the class
  (`deck_script_gated`), and the deck degrades to the pure-CSS pager when
  scripting is off (`floor_covered_script_gated`). A third path needs the
  same three properties or a design discussion.
- Design tokens are the styling API for both backends: a new visual knob is a
  token, not a hard-coded constant in a backend.
- Hot paths use `Array`/`ByteArray`/packed `UInt32`; no `List`. A structural
  walk over a `List` (the totality pattern below) accumulates into an
  `Array` it threads through: building the result as `#[x] ++ walk rest`
  copies the walk's result at every element and turns a 4 ms pass into
  600 ms on a 30-page document — the hook rejects an append whose trailing
  text is a call ending in a bare variable, whatever the left side spells.
  Appending to a `mut` string or array in a loop is fine: unique ownership
  appends in place (`Pdf.write` builds the whole file that way).
  Bit-level work in a hot loop is `UInt64`/`UInt32`, never `Nat`: a `Nat`
  shift (`<<<`) is an out-of-line bignum call with no small-number fast
  path (~80 ns; `+`, `*`, `>>>`, `&&&` are inline), and two of them per
  byte were three quarters of the compressor. A `Nat` loop variable that
  only indexes is fine.
  `scripts/bench.lean` is the check; run it when touching any pass over the
  whole document.
- A kernel `decide` over shipped constants belongs in a leaf module, off
  the import chain to Elab: the next structure its module declares waits
  for the pending kernel check, so the check runs in series with every
  module downstream. A zero-argument `def` is evaluated when its module
  initializes, in every process; take `Unit` to defer the cost to first
  use.
- The inline elaboration knot compiles at its heartbeat budget (more than
  198k of 200k on 2026-09-27), and its cost grows with `ESt`'s top-level
  fields: state the knot never reads goes in a record of its own
  (`Counters` is the shape), never a new top-level field.
- `Elab`'s block knot (the mutual block around `elabBlocksGo`) is at its
  compiler budget. An arm's new logic goes in a helper outside it
  (`tikzArm`, `boxOptsArm`), and no knot function gains a parameter: one
  on `columnsGo` alone tipped the knot's compilation past the default
  200000 heartbeats. A value an inner walk needs travels in the raws
  (`Compat.columnsRowPos`) instead.
- A cache over an external tool caches the tool's *whole* answer, not
  only the answer that succeeded. A verdict remembered for the drawn case
  and dropped for the refused one means the slow path is the one that
  repeats: six unrenderable pictures cost six `lualatex` startups on every
  build, forever (4,524 ms of a 4,754 ms run), while the renderable ones
  warmed after the first. So the failure goes in the same slot under the
  same content key, and the replay reports the identical diagnostic with
  the tool's own words — a cached loss is still named, once, at full
  strength. The line a cache must not cross: an attempt the tool never
  finished is not a verdict. A budget kill, a spawn that raised, and a
  nonzero exit that left no log are all facts about the machine, not the
  request, and caching one would let a busy minute — or a missing
  install — permanently condemn a picture that renders. An exit code alone
  cannot make that call: a missing tool still reaches `exec` and returns
  127, so the evidence is that the tool left a log. The policy lives as
  values in the driver (`Cli/PicCache.lean`) precisely so it is checkable
  with no tool installed.
- Theorems only where they pay (parser totality, elaboration termination and
  determinism, line-break optimality, dimension arithmetic, PDF xref, UTF-8).
  The language is designed terminating — a construct that breaks that property
  needs a design discussion, not a fuel parameter. A guarantee stated in
  prose is not a guarantee: termination, totality and determinism claims
  in PLAN name the theorem that holds them, and a claim with no theorem
  is written as owed — the 2026-09-19 nontermination bug lived twelve
  hours behind a PLAN sentence with no checker (`bindCmd_monotone` is
  the statement that would have failed the commit). In a statement meant for
  `omega`, spell binders and structure fields `Int`, not `Sp`: omega reads
  the bare spelling only, and an `Sp`-typed hypothesis is silently invisible
  to it. `omega` handles `Int.max`/`min` directly — no `Int.max_def` unfold,
  no generalize-the-max; and a `decide` that needs `maxRecDepth` raised is
  spelled `decide +kernel` instead. A case split whose branches read
  identical may still be load-bearing for elaboration cost — judge dead
  proof structure by deletion and rebuild, never by inspection.
- A theorem the engine does not yet earn is stated anyway — in
  `Obligations/`, the staging queue: its own lake target, outside the
  default `lake build` and `lake test`, never imported by `LeanTex/` (the
  hook and `scripts/owed.lean` check mechanically). `sorry` is permitted
  only there, one per obligation, each carrying an
  owed/owner/source/blocker/goldens record whose name is registered in
  PLAN.md § Owed obligations — the ratchet: the debt may never grow
  unnamed. A discharged obligation moves into its owner module with a real
  proof; the queue is not a home. Statements range over the engine's own
  functions, never a spec copy.
- No default values on inductive constructor fields — patterns then
  under-specify silently; the hook rejects them. Structure fields keep theirs.
- Never add `partial` to reach a green build. Tree recursion over `Array`
  fields works via mutual recursion through `List` (see `Compat.rewriteList`,
  `Html.render`); a `map`/`flatMap` over children hides the call behind a
  lambda the checker cannot see, and a list matched against a literal pattern
  with a catch-all variable loses the tail — write the `List` companion
  instead. Index loops bounded by `[0:xs.size + 1]` are total without it.
  None remain: `takeArgs`, `elabInlines`, and `elabBlocks` all terminate by
  proved lexicographic measures (`elaboration_total` in Elab.lean names the
  fact; the pre-commit hook rejects any `partial` at all). The shape to
  copy is the elabBlocks knot: explicit index recursion whose measure facts
  stand as `have`s beside each call — and mind that the termination goals
  zeta-expand plain `let`s while hypotheses keep the variable, so a value a
  measure fact describes travels as a subtype pattern, never a bare `let`.
- A claim is open until machine-checked. An executable oracle
  (`scripts/kp-fuzz.lean`) is evidence, not a theorem — say which one you have.
- Comments: nearly none. Names and tests carry the what; a comment only for a
  why the code cannot say.
- Linters: the core linters plus the `linter.extra` set run inside
  `lake build` (enabled in `lakefile.toml`); a warning fails the pre-commit
  hook, and `linter.missingDocs` stays off deliberately.
- A test helper used by two check blocks moves to the shared section
  (`Tests/Support.lean`) the moment the second caller appears. Fifteen
  copies of one deck builder grew from parallel slices each lacking a
  visible shared builder; the by-phase split fixed the ordering that caused
  it, and this rule prevents regrowth.
- In-repo tests and fixtures are synthetic, and synthetic means invented: no
  text, topics, or distinctive design values (fonts, spacing constants,
  palettes) copied from the private corpus. Placeholder names, `example.org`
  contacts. The private corpus never enters this repo; acceptance runs
  against it locally, never in CI.
- Fixtures and tests never depend on what this host has installed. A fixture
  that names a font ships it in `tests/corpus/fonts/` (with its license) and
  declares `\fonts{ dir = "fonts" }`; `Tests.lean` scans only that directory
  (`FontDb.scanRoots [testFonts]`), never `FontDb.scan`. To prove a change
  hermetic, build the corpus in a namespace with the font directories
  emptied: `unshare -Urm`, `mount -t tmpfs none /usr/share/fonts` (and the
  TeX Live tree), `HOME` and `PATH` pointed at empty directories.

## Don't touch

- `lean-toolchain` — bumps are deliberate, in their own commit.
- `tests/golden/**` — regenerate through the harness, never hand-edit.

## Commits

- Commit each verified unit (build + tests green); imperative subject line.
- Never push without being asked.
- Landing a branch onto `main` goes through `land` (`scripts/land.lean`) — never
  a hand rebase or merge. It reads preconditions from
  `git status --porcelain` and `git rev-parse` *through files*, makes a
  detached gate tree at the branch tip it read and rebases *there* onto the
  `main` it read, runs every gate in that tree, re-reads the branch and `main`
  after them, fast-forwards `refs/heads/main` by name to the *sha the gates
  ran on*, reads the new tip back, and writes one ledger row per fact. It never
  writes the branch or its owner's worktree: every action declares what it
  writes, and `step_writes_owned` holds the core to the run's own tree and
  ledger, and `main` and the remote only to the gated tip on a proven run; a
  verdict claiming a landing implies `main` was read back at that sha. Prose
  reports of repository state obey the rule claims about a page obey: from the
  artifact. The landing never resolves a conflict: a conflict outside the
  union-merged files is a refusal with exit 2 that touches nothing of the
  owner's, and the branch's owner rebases and resolves it in their own
  worktree, then re-runs `land check` — keep-both once doubled an owed
  record's `blocker:` line, which is why the tool refuses rather than guesses.
  A branch landed onto a `main` that had moved keeps its original commits: the
  ledger records the tip it read, and `land retire` reads that. A landed
  branch is never continued: while `main` holds its landing, `land` refuses
  it and sends the next unit to a new branch from `main` (`land new <name>`);
  a landing `main` no longer holds — `main` put back before a push — counts
  for nothing, and the branch lands again (`step_unheld_exact`,
  `step_barred_exact`).
- Never `git stash`: the stack is per-repository, not per-worktree, and agents
  here work in parallel worktree checkouts — a `pop` can apply, and drop,
  another worktree's entry. Set work aside with file copies instead (the file
  moved away to prove a test fails before the fix, copied back after). One
  four-minute test run was long enough for a second agent's stash to take
  `stash@{0}`; the pop planted its 115-line `Compat.lean` rewrite in the first
  agent's tree and removed it from the stack. Recovery worked only because the
  stash commit outlives the stack entry in the shared object store:
  `git stash store <sha>` puts it back, with the SHA the pop printed.
