# Compound title-slot layout implementation

- Date: 2026-09-29
- Mode: autopilot, concise
- Status: complete
- Task source: direct implementation request; no Taskei or Pippin project
- Build system: Lake with the repository-mandated Lean compiler environment

## Invariant and TDD evidence

One source title node owns one placed box. Its ordered datum parts may carry independent font, colour, exact size, alignment, line, and gap declarations; omitting empty optional data removes only that part and its gap, never the box or another part.

- RED at base `82e1e271`: an invented compound-node page fell back to flow, emitted the named placement loss, and disagreed with the two-pass reference placement.
- GREEN at `33870703`: the focused title, typed HTML, accessibility, and shipped-page census checks pass for one datum, same-style multiple data, differently styled data, and empty/nonempty optional data.

## Validation

- `lake build`: passed
- `lake test`: passed
- Targeted title, HTML accessibility, and census checks: passed
- Aggregate scoreboard check and compiled self-test: passed; all declared tiers report no regression
- Declaration-commutation fuzz: passed over synthetic inputs and the corpus
- Whole-document benchmark: passed its growth bound
- Browser reader matrix: refreshed for the changed HTML; its tier gate passes. Two pre-existing cross-image target cells remain non-passing and unchanged.
- Independent staged-diff review: approved with no blocking or important findings
- Authorized local acceptance references: both produced one page and the same visible datum set as their two-pass reference builds; no private material was retained

## Delivery

- Commit: `33870703ade6fc365df50ce032c6d96dbf90996b`
- Branch: `agent/theme-title-layout`
- Base and remote primary branch were identical; rebase was a no-op
- No CR, Taskei update, or Pippin sync was requested
