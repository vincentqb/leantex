module

public import LeanTex.Core.Compat

namespace LeanTex.Core.CompatContract

open LeanTex.Core.Parse

/-- At an ordinary body cursor, an exact declared argument
prefix of every registered row contributes no replacement
tokens and the walk resumes at its end. -/
public theorem ctrl_groups_consumed_contract :
    (∀ row ∈ Compat.meaningFree,
      Compat.ControlGroupsConsumed row.1 row.2.1) ∧
    (∀ row ∈ Compat.configSkip,
      Compat.ControlGroupsConsumed row.1 row.2.1) ∧
    Compat.UnknownControlPreserved "zzNotAControl" := by
  exact ⟨Compat.meaningFree_control_contract,
    Compat.configSkip_control_contract, Compat.unknown_control_contract⟩

/-- The operand the style-file scanner reads from an expanded loading call. -/
@[expose] public def loadArgument (command : String) (pos : Pos) (tail : Array Raw) : String :=
  let call := #[Raw.ctrl command pos] ++ tail
  rawSrc ((Compat.takeGroups call (Compat.takeOpt call 1).2 1).1.getD 0 #[])

/-- Every nonempty non-native name in an expanded
package-loading operand is asked for, and every nonempty
theme-loading operand asks for its registered prefix. -/
public theorem nameRefusals_asked (pos : Pos) (tail : Array Raw) :
    (∀ command, command = "usepackage" ∨ command = "RequirePackage" →
      ∀ part ∈ (loadArgument command pos tail).splitOn ",",
        part.trimAscii.toString.isEmpty = false →
        Compat.nativePackages.contains part.trimAscii.toString = false →
        (Compat.localStyCandidates (#[.ctrl command pos] ++ tail)).contains
          part.trimAscii.toString = true) ∧
    (∀ row ∈ Compat.themeAsking,
      (loadArgument row.1 pos tail).trimAscii.toString.isEmpty = false →
      (Compat.localStyCandidates (#[.ctrl row.1 pos] ++ tail)).contains
        (row.2 ++ (loadArgument row.1 pos tail).trimAscii.toString) = true) := by
  constructor
  · intro command hcommand part hpart hnonempty hnative
    apply Array.contains_iff_mem.mpr
    exact Compat.localStyCandidates_package_covers command pos tail
      part.trimAscii.toString hcommand ⟨part, hpart, rfl⟩ hnonempty hnative
  · intro row hrow hnonempty
    apply Array.contains_iff_mem.mpr
    have hlookup : Compat.themeAsking.lookup row.1 = some row.2 := by
      simp only [Compat.themeAsking, List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hnames : row.1 ≠ "usepackage" ∧ row.1 ≠ "RequirePackage" := by
      simp only [Compat.themeAsking, List.mem_cons, List.not_mem_nil, or_false] at hrow
      rcases hrow with rfl | rfl | rfl | rfl | rfl <;> simp
    exact Compat.localStyCandidates_theme_covers row.1 row.2 pos tail
      (loadArgument row.1 pos tail).trimAscii.toString
      hnames.1 hnames.2 hlookup rfl hnonempty

end LeanTex.Core.CompatContract
