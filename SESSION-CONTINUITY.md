# Session continuity

## Status

Two side sessions handed work over through this file. Both are complete and
landed on `main`; neither has work in flight.

## The Lean 4.34.1 runtime-closure experiment

Branch `agent/lean4-runtime-minimal`, first based on `8d3df368`.

- `c3dceec2`, the toolchain pin to v4.34.1, landed alone as `302e69dc`.
- `c9deaff3`'s setup notes and PLAN finding landed rewritten as `2d895d64`.
- `50f0e826`, the direct imports, landed rebased onto today's modules as
  `3527244e`: `Main.lean` imports the modules it calls, `LeanTex.Version`
  holds the version, and `defaultTargets` keeps the `LeanTex` umbrella, so
  every proof stays in the default build. The PLAN entry "the executable
  imports what it calls" corrects the earlier one that kept the umbrella.
- This file replaces the branch's own handoff (`effc6a23`), written before
  anything landed.

Findings, unchanged: the executable initializes only the Lean runtime, and its
ELF carries no compiler or elaborator initializer. The direct imports save a
few kilobytes and buy no resolved speedup; claim none. At the landing the
executables built with and without them wrote byte-identical artifacts on the
test corpus and the private reference corpus. Converting `Main.lean` alone to
the module system fails, since a module cannot import the legacy modules, and
a whole-graph migration has no measured prize.

A module `Main.lean` comes to call is imported there by name: the umbrella no
longer brings it.

The Lean-runtime-versus-Rust investigation is a separate workstream. Do not
move its code, private evidence, or product-specific identifiers into this
repository.

## Package and class diagnostics

The package/class diagnostic recovery defect is fixed (`9315dcfc`, "Keep
package diagnostics out of body text"). LaTeX package and class warning and
info controls write TeX's log, not document ink: their exact argument groups
are consumed before inline elaboration (`Compat.meaningFree`, two-group rows
for `PackageWarning`, `PackageWarningNoLine`, `PackageInfo`, `ClassWarning`,
`ClassWarningNoLine` and `ClassInfo`), with N0100 accounting, while ordinary
unknown body commands keep their argument content. `Tests/Surface.lean` holds
the synthetic deferred-hook rows for all six names. If another log-only
control reproduces the failure, verify its public LaTeX arity, add one exact
compatibility row, and extend the deferred-hook table; do not special-case
characters in private style files.

## Next action

None. Start new work from `main` in a fresh worktree.
