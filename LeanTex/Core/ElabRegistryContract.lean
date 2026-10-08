module

public import LeanTex.Core.Elab
import all LeanTex.Core.Elab
import LeanTex.Core.Ir
import all LeanTex.Core.Picture
import all LeanTex.Core.Theme
import all LeanTex.Core.Lex

namespace LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Ir

/-- One verdict per name: no built-in is both unconditionally protected
and rule-(b) gated — a name in both would fire W0303 at `takeDefine` and
never reach the gate, making the registry's promise (a clean body wins) a
lie for exactly that name. -/
public theorem structural_rendered_disjoint :
    (structuralNames.all fun n => !renderedBuiltins.contains n) = true := by
  decide +kernel

/-- The ratchet: every name W0303 used to protect still has a verdict —
unconditional refusal or the rule-(b) gate. Narrowing the structural core
cannot silently strip a built-in of both protections. -/
public theorem builtin_verdict_total :
    (builtinNames.all fun n =>
      structuralNames.contains n || renderedBuiltins.contains n) = true := by
  decide +kernel

/-- The invariant the phantom defect wanted, registry half: a command whose
whole meaning is *size without ink* is a name this dispatch gives a meaning
of its own. The family (`Picture.phantomCtrl`, where the label salvage reads
it) and the two registries are written out apart on purpose — a registry
spliced from the family would read `xs ⊆ A ++ xs ++ B` and could not witness
a member missing from it, which is the shape this statement had on its first
attempt and the reason it is spelled this way now.

What it does *not* reach is the arm: a name can be registered here and still
fall through to the unknown-command recovery, whose rule is "keep the braced
arguments as text" and which is how `\vphantom{y}`'s letter reached the page.
The arm's own gate is `phantomReservesWidth`, held to the family by
`phantom_axes_set_eq`; the page is `phantomChecks`, over `Layout.Out`. Three
statements, because no one of them can see the other two's failure. -/
public theorem phantom_rendered_covers :
    (Picture.phantomCtrl.all fun n =>
      renderedBuiltins.contains n && builtinNames.contains n) = true := by
  decide +kernel

/-- The same family against the *salvage* tables: every member's group is a
naming argument (`Ir.floorNamedArgs`), so a recovery path that keeps content
groups — the math floor, a picture label — drops a phantom's group instead
of setting it. This one held before the fix as well: it is the reason
`$a\phantom{=}b$` never shipped an `=`, and it stays here as drift
insurance, not as the defect's witness. -/
public theorem phantom_named_covers :
    (Picture.phantomCtrl.all fun n =>
      (Ir.floorNamedArgs.lookup n) == some 1) = true := by
  decide +kernel

/-- Family and axes, exactly each other's keys, and one row per key. This is
the statement that reaches the arm: the dispatch fires on this table, so a
member added to `Picture.phantomCtrl` and not here does not merely lose a
default — it is not dispatched at all, and falls to the unknown-command
recovery that shipped the letter. The no-duplicates conjunct pins the value
too: `lookup` takes the first row, so two rows for one name would leave the
axes decided by list order rather than by the table. The last conjunct is
the family's defining property — no member inks, so none of them is a
content wrapper that wandered in. -/
public theorem phantom_axes_set_eq :
    ((Picture.phantomCtrl.all fun n => (phantomAxes.lookup n).isSome) &&
      (phantomAxes.all fun e => Picture.phantomCtrl.contains e.1) &&
      (phantomAxes.map (·.1)).Nodup &&
      (phantomAxes.all fun e => e.2.width || e.2.extent)) = true := by
  decide +kernel

/-- Every palette role is invocable: a role is *defined by the palette* —
`\muted{Alex}` works with no `\newcommand`, because the palette arm of the
inline elaborator resolves any entry name — so no role can exist without
its command. The document door (`applyPalette`) already refuses a key that
collides with a built-in (E0303) and validates its characters; a theme's
bundle installs without that door, so the shipped bundles enter the
contract here: every key lexes as one control word (`Lex.nameChar`) and
collides with no registered built-in. Resolution *order* lives in
`elabInlines`, whose sanctioned recursion is opaque to proof — that every key
really reaches the palette arm is the paired executable check in
Tests.lean (`roleInvocationChecks`), an oracle, not a theorem. -/
public theorem every_role_is_invocable :
    (Theme.builtin.all fun t => t.palette.entries.toList.all fun e =>
      e.1.toList.all Lex.nameChar && !builtinNames.contains e.1) = true := by decide

end LeanTex.Core.Elab
