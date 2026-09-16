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
- `lake exe Tests --update` — regenerate goldens after an intended IR change.
- Deeper oracles, not in `lake test` (too slow / need TeX): run
  `scripts/kp-fuzz.lean` when touching line breaking,
  `scripts/hyphen-diff.sh` when touching hyphenation, and
  `scripts/fontcache-check.lean` when touching the font scan or its cache
  (it replaces a font under the same name and checks the answer follows
  the file).
- Performance claims come only from `scripts/bench.sh` (vs lualatex on the
  corpus), never from reasoning about the code.

## Conventions

- Before fixing an issue, write down the invariant whose absence allowed it —
  as a theorem statement when it is one, as a test when it is not — then fix
  to that invariant, not to the symptom. The test fails before and passes
  after; if the lesson generalises, it becomes a rule here or a hook check.

- Pure core: modules under `LeanTex/Core/` do no IO. Files, fonts, anything
  external surfaces as request values the CLI driver fulfills (effects as data).
- Backends consume the IR and nothing else. A backend never re-parses, and
  never reaches back into the surface AST — that is how md→PDF and tex→HTML
  stay free instead of becoming N×M special cases.
- HTML is built as a typed tree with a certified escaper, never by
  concatenating tag strings. Any new node type goes through the escaper by
  construction; if you find yourself writing `"<" ++ …`, stop.
- Design tokens are the styling API for both backends: a new visual knob is a
  token, not a hard-coded constant in a backend.
- Hot paths use `Array`/`ByteArray`/packed `UInt32`; no `List`, no `String`
  concatenation in loops. A structural walk over a `List` (the totality
  pattern below) accumulates into an `Array` it threads through: building
  the result as `#[x] ++ rest` copies `rest` at every element and turns a
  4 ms pass into 600 ms on a 30-page document. `scripts/bench.sh` is the
  check; run it when touching any pass over the whole document.
- Theorems only where they pay (parser totality, elaboration termination and
  determinism, line-break optimality, dimension arithmetic, PDF xref, UTF-8).
  The language is designed terminating — a construct that breaks that property
  needs a design discussion, not a fuel parameter.
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

## Don't touch

- `lean-toolchain` — bumps are deliberate, in their own commit.
- `tests/golden/**` — regenerate through the harness, never hand-edit.

## Commits

- Commit each verified unit (build + tests green); imperative subject line.
- Never push without being asked.
