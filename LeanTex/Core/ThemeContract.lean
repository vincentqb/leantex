module

public import LeanTex.Core.Theme
import all LeanTex.Core.Theme
import all LeanTex.Core.Ir

/-!
Kernel-checked contracts over the shipped bundles, kept in a leaf so the
evaluations run beside the build rather than in series with every module
that imports `Theme`. Each quantifies over `Theme.builtin`: adding a bundle
is entering the contract.
-/

namespace LeanTex.Core.Theme

open LeanTex.Core.Ir

/-- Arch-design I2, the engine half: what `\theme` installs is what the
bundle declares — the install function is `apply`, the very function the
elaborator calls at the `\theme` site, so a bundle's title-page alignment
and separator survive the install onto an undeclared document. The literal
through-`Elab.run` reading stays with the executable oracles: Elab's WF
recursion is kernel-irreducible, and this statement over the install
function is the same fact one definitional step earlier. -/
public theorem titlepage_align_declared_engine :
    (builtin.all fun t =>
      match (apply t {}).styles.find? "titlepage" with
      | some st => st.align.isSome && st.separator.isSome
      | none => true) = true := by decide

/-- The class layer under the theme layer: a class fixes the page model
and its implied contract, and a theme may override neither. `apply`'s
whole domain and codomain is `Decls`, which has no class, page, or
assertion field; the checkable residue is that every key a shipped bundle
installs lives on one of the four visual surfaces. -/
public theorem theme_layer_contract :
    (builtin.all fun t => (declares t).toList.all fun e =>
      ["palette", "tokens", "style", "chrome"].contains e.1) = true := by decide

/-- Every shipped bundle declares each style element once, so
`apply_fixed_point` covers it. -/
public theorem builtin_styles_nodup :
    (builtin.all fun th => nodupKeys th.styles.entries.toList) = true := by decide

/-- Every name a shipped bundle declares reads as itself in an expression,
so `resolve_find_exact` covers each: `\textcolor{<name>}` and every reader of
the entry agree on it. -/
public theorem builtin_names_plain :
    (builtin.all fun th => th.palette.entries.toList.all fun e => plainName e.1.key) = true := by
  decide

end LeanTex.Core.Theme
