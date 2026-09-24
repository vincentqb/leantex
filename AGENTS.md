# AGENTS.md

leantex: fast, certified, modern document engine in Lean 4 — one language,
two surfaces (tex primary, markdown as sugar), two backends (PDF 2.0 and
HTML). The living plan is `PLAN.md` — design decisions and milestone status
land there, not here. Never record personal information (names, emails, and
the text or topics of private documents) or local paths to private documents
in this repo; refer to the private reference corpus abstractly.

## Setup

- Toolchain: elan-managed, pinned by `lean-toolchain` (track stable; v4.34.0 today).
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
  | a diagnostic code | a `DiagCode` constructor with its declared `Loss` — severity and the code letter derive from the loss, one code one meaning (compiler + `lake test`; the hook rejects a severity written outside Diag.lean) — a firing witness in `diagWitness` whose rendered form lands in the diagnostics golden, and a message that passes the voice lint: self-contained (no repo file, no milestone), an action or no help, one convention (Tests.lean; the hook rejects repo-internal references in strings). Registering a new code is one constructor, one `spec` arm, and `count + 1` — nothing else: `all` is derived, and `all_complete`/`all_nodup` make a miscount a build failure in both directions |
  | a design constant | a token, or the source written where it stands (hook, backend files) |
  | a recursive IR walk | a `List` companion + accumulator (hook), and its census statement: a public Block/Inline walk ships a theorem named with a registered conservation suffix — `_text` (census equality, stated as a `Conserves` instance), `_covers`, `_id` — or the one-line refusal `-- conserves: none — <why>` beside the def (hook, whole tree) |
  | a palette role or token the engine reads | one resolving site, its contrast contract, a per-bundle check (`Ir.Design.ofPalette` is the resolving site — the argument is a palette because the layout resolves the *epoch* palette in force at a frame and `Design.ofDoc` the document's, through the one chain, `frametitle_agree`; Contrast.lean holds the contracts, the bundle pins the checks) |
  | a page-opening path | a declared vertical distribution, never a default (`Layout.VDist` is the vocabulary; declare through it) |
  | a furniture element | a declared alignment, never a hard-coded `.center` (`align` on `ElementStyle` carries it) |
  | an `AssertKind` | its judge in `Check.one` (exhaustive match) and a test that breaks it once |
  | a cached external answer | the *failure* cached too, under the same content key, replayed as the identical diagnostic — and an attempt with no evidence the tool ran (kill, failed spawn, nonzero exit with no log) cached not at all (`Cli/PicCache.lean` holds the policy as values; `step_cold_exact`, `remembers_verdict_exact`, `unlogged_retried_exact`, `picCacheChecks`) |
  | a document class | sourced defaults, and its contract as implied assertions |
  | a `nativePackages` entry | `tests/compat-index/<pkg>.txt` covering the package's *documented* command list — the manual section named in its header, one row per command, `impl` proved by no W0301/W0302 and `refuse:<code>` by the code firing (`lake test` probes every row; the hook rejects an entry without its file) |
  | a gate on the declared setup (context, config, declarations, state) that names, silences, or demotes a loss | the check that falsifies its premise, named beside it: `-- premise: <pin> — <why>`, or the refusal `-- premise: none — <why>` (hook, whole tree; the pin must resolve to a theorem the build checks or a check block the suite runs). A premise about another subsystem is a claim, and prose rots — three defects shared that shape. The shape of such a check is two builds differing by the gate's own condition: a byte-identical artifact with different diagnostics means nothing else was handling the case, so the gate is a silencer (`pictureKeyGateChecks`) |

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
  is the shape). A new property instantiates a
  suffix, or the review says why
  it is a new shape; the first three are what the hook's walk gate looks
  for. `_in_measure` is not a shape: `kern_symmetric_in_measure` is an
  `_exact` statement and takes that suffix the next time Layout.lean is
  open. A contract over shipped bundles quantifies over `Theme.builtin`,
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
- Never `git stash`: the stack is per-repository, not per-worktree, and agents
  here work in parallel worktree checkouts — a `pop` can apply, and drop,
  another worktree's entry. Set work aside with file copies instead (the file
  moved away to prove a test fails before the fix, copied back after). One
  four-minute test run was long enough for a second agent's stash to take
  `stash@{0}`; the pop planted its 115-line `Compat.lean` rewrite in the first
  agent's tree and removed it from the stack. Recovery worked only because the
  stash commit outlives the stack entry in the shared object store:
  `git stash store <sha>` puts it back, with the SHA the pop printed.
