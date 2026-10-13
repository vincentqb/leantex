module

public import LeanTex.Core.Elab
import all LeanTex.Core.Elab
import LeanTex.Core.Ir
import all LeanTex.Core.Picture
import all LeanTex.Core.Theme
import all LeanTex.Core.Lex

namespace LeanTex.Core.Elab

open LeanTex.Core LeanTex.Core.Ir

public theorem structural_rendered_disjoint :
    (structuralNames.all fun n => !renderedBuiltins.contains n) = true := by
  decide +kernel

public theorem builtin_verdict_total :
    (builtinNames.all fun n =>
      structuralNames.contains n || renderedBuiltins.contains n) = true := by
  decide +kernel

public theorem phantom_rendered_covers :
    (Picture.phantomCtrl.all fun n =>
      renderedBuiltins.contains n && builtinNames.contains n) = true := by
  decide +kernel

public theorem phantom_named_covers :
    (Picture.phantomCtrl.all fun n =>
      (Ir.floorNamedArgs.lookup n) == some 1) = true := by
  decide +kernel

public theorem phantom_axes_set_eq :
    ((Picture.phantomCtrl.all fun n => (phantomAxes.lookup n).isSome) &&
      (phantomAxes.all fun e => Picture.phantomCtrl.contains e.1) &&
      (phantomAxes.map (·.1)).Nodup &&
      (phantomAxes.all fun e => e.2.width || e.2.extent)) = true := by
  decide +kernel

public theorem every_role_is_invocable :
    (Theme.builtin.all fun t => t.palette.entries.toList.all fun e =>
      e.1.key.toList.all Lex.nameChar && !builtinNames.contains e.1.key) = true := by decide

end LeanTex.Core.Elab
