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
  a file, so `scripts/hooks/pre-commit` stays a 3-line sh trampoline into
  `scripts/precommit.lean`.
- `lake exe Tests --update` — regenerate goldens after an intended IR change.
- Deeper oracles, not in `lake test` (too slow / need TeX): run
  `scripts/kp-fuzz.lean` when touching line breaking,
  `scripts/hyphen-diff.lean` when touching hyphenation,
  `scripts/oklab-roundtrip.lean` when touching `Core/Oklab.lean`
  (sRGB→Oklab→sRGB identity over all 2²⁴ inputs, ~30 min), and
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
  | a diagnostic code | a `DiagCode` constructor with its declared `Loss` — severity and the code letter derive from the loss, one code one meaning (compiler + `lake test`; the hook rejects a severity written outside Diag.lean) — a firing witness in `diagWitness` whose rendered form lands in the diagnostics golden, and a message that passes the voice lint: self-contained (no repo file, no milestone), an action or no help, one convention (Tests.lean; the hook rejects repo-internal references in strings) |
  | a design constant | a token, or the source written where it stands (hook, backend files) |
  | a recursive IR walk | a `List` companion + accumulator (hook), and its conservation statement where it is one |
  | a palette role or token the engine reads | one resolving site, its contrast contract, a per-bundle check (arrives with `Design`; today Contrast.lean + bundle pins) |
  | a page-opening path | a declared vertical distribution, never a default (arrives with `vdist`; until then set `centerV` deliberately) |
  | a furniture element | a declared alignment, never a hard-coded `.center` (arrives with `align` on `ElementStyle`) |
  | an `AssertKind` | its judge in `Check.one` (exhaustive match) and a test that breaks it once |
  | a document class | sourced defaults, and its contract as implied assertions |

- Pure core: modules under `LeanTex/Core/` do no IO (`FontDb` is the one
  exception; the pre-commit hook rejects new IO in core). Files, fonts,
  anything external surfaces as request values the CLI driver fulfills
  (effects as data).
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
  obligation and a rule that then holds only approximately. `--math-boundary`
  remains the one script path, for genuinely computational behaviour a
  document asks for by name.
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
  `scripts/bench.lean` is the check; run it when touching any pass over the
  whole document.
- Theorems only where they pay (parser totality, elaboration termination and
  determinism, line-break optimality, dimension arithmetic, PDF xref, UTF-8).
  The language is designed terminating — a construct that breaks that property
  needs a design discussion, not a fuel parameter.
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
  `Elab.takeArgs`/`elabInlines`/`elabBlocks` are the three known exceptions,
  tracked in PLAN; the pre-commit hook rejects any new one.
- A claim is open until machine-checked. An executable oracle
  (`scripts/kp-fuzz.lean`) is evidence, not a theorem — say which one you have.
- Comments: nearly none. Names and tests carry the what; a comment only for a
  why the code cannot say.
- Linters: the core linters plus the `linter.extra` set run inside
  `lake build` (enabled in `lakefile.toml`); a warning fails the pre-commit
  hook, and `linter.missingDocs` stays off deliberately.
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
