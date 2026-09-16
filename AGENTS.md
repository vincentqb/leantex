# AGENTS.md

leantex: fast, certified, modern LaTeX-lookalike engine in Lean 4. The living
plan is `PLAN.md` — design decisions and milestone status land there, not here.
Never record personal information (names, emails, and the text or topics of
private documents) or local paths to private documents in this repo; refer to
the private reference corpus abstractly.

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
- `lake exe Tests --update` — regenerate goldens after an intended IR change.
- Deeper oracles, not in `lake test` (too slow / need TeX): run
  `scripts/kp-fuzz.lean` when touching line breaking, and
  `scripts/hyphen-diff.sh` when touching hyphenation.
- Performance claims come only from `scripts/bench.sh` (vs lualatex on the
  corpus), never from reasoning about the code.

## Conventions

- Pure core: modules under `LeanTex/Core/` do no IO. Files, fonts, anything
  external surfaces as request values the CLI driver fulfills (effects as data).
- Hot paths use `Array`/`ByteArray`/packed `UInt32`; no `List`, no `String`
  concatenation in loops.
- Theorems only where they pay (parser totality, elaboration termination and
  determinism, line-break optimality, dimension arithmetic, PDF xref, UTF-8).
  The language is designed terminating — a construct that breaks that property
  needs a design discussion, not a fuel parameter.
- Comments: nearly none. Names and tests carry the what; a comment only for a
  why the code cannot say.
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
