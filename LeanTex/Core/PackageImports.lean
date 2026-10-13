module

public import Init.Data.List.Find

namespace LeanTex.Core.PackageImports

/-- Literal package options in written order: split at unbraced commas, spaces outside groups
zapped (`\zap@space`), braces kept, nothing expanded. -/
public def literalOptions (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut item := ""
  let mut depth := 0
  let mut escaped := false
  for c in s.toList do
    if c == ',' && depth == 0 && !escaped then
      unless item.isEmpty do out := out.push item
      item := ""
    else
      if !c.isWhitespace || depth != 0 || escaped then item := item.push c
      if !escaped then
        if c == '{' then depth := depth + 1
        else if c == '}' then depth := depth - 1
    escaped := c == '\\' && !escaped
  unless item.isEmpty do out := out.push item
  return out.toList

/-- Packages whose bodies have been admitted, with their first effective option lists. -/
public abbrev Loads := List (String × List String)

/-- A package body runs only on `load`; `skip` with a nonempty list names an option clash. -/
public inductive Decision where
  | load
  | skip (newOptions : List String)
  deriving Repr, BEq, Inhabited

/-- LaTeX's repeated-load check, by membership in the first list (latex.ltx `\@pass@ptions`);
forwarded options precede direct ones. -/
public def admit (loads : Loads) (name : String) (options passed : List String) :
    Decision × Loads :=
  match loads.lookup name with
  | none => (.load, (name, passed ++ options) :: loads)
  | some first => (.skip (options.filter fun o => !(first ++ passed).contains o), loads)

public theorem admit_first_exact (loads : Loads) (name : String)
    (options passed : List String)
    (h : loads.lookup name = none) :
    admit loads name options passed = (.load, (name, passed ++ options) :: loads) := by
  simp [admit, h]

public theorem admit_loaded_exact (loads : Loads) (name : String)
    (options passed first : List String) (h : loads.lookup name = some first) :
    admit loads name options passed =
      (.skip (options.filter fun o => !(first ++ passed).contains o), loads) := by
  simp [admit, h]

public theorem admit_compatible_exact (loads : Loads) (name : String)
    (options passed first : List String) (h : loads.lookup name = some first)
    (compatible : ∀ o ∈ options, o ∈ first ++ passed) :
    admit loads name options passed = (.skip [], loads) := by
  rw [admit_loaded_exact loads name options passed first h]
  have empty : options.filter (fun o => !(first ++ passed).contains o) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro o ho
    simp [compatible o ho]
  rw [empty]

public theorem admit_clash_exact (loads : Loads) (name : String)
    (options passed first : List String) (h : loads.lookup name = some first) (o : String) :
    (match (admit loads name options passed).1 with
      | .load => False
      | .skip missing => o ∈ missing) ↔ o ∈ options ∧ o ∉ first ++ passed := by
  simp [admit, h]

public theorem admit_lookup_exact (loads : Loads) (name observed : String)
    (options passed : List String) :
    (admit loads name options passed).2.lookup observed =
      if observed = name then (loads.lookup name).orElse (fun _ => some (passed ++ options))
      else loads.lookup observed := by
  cases h : loads.lookup name with
  | none =>
    by_cases same : observed = name
    · simp [admit, h, same]
    · simp [admit, h, List.lookup_cons, same, beq_eq_false_iff_ne.mpr same]
  | some first =>
    by_cases same : observed = name
    · simp [admit, h, same]
    · simp [admit, h, same]

public theorem admit_repeat_fixed_point (loads : Loads) (name : String)
    (options passed again : List String) (h : loads.lookup name = none)
    (compatible : ∀ o ∈ again, o ∈ passed ++ options) :
    admit (admit loads name options passed).2 name again [] =
      (.skip [], (admit loads name options passed).2) := by
  rw [admit_first_exact loads name options passed h]
  exact admit_compatible_exact _ name again [] (passed ++ options) (by simp)
    (by simpa using compatible)

public theorem admit_distinct_agree (loads : Loads) (left right observed : String)
    (leftOptions rightOptions leftPassed rightPassed : List String) (distinct : left ≠ right) :
    (admit (admit loads left leftOptions leftPassed).2 right rightOptions rightPassed).2.lookup
        observed =
      (admit (admit loads right rightOptions rightPassed).2 left leftOptions leftPassed).2.lookup
        observed := by
  simp only [admit_lookup_exact]
  by_cases hl : observed = left
  · simp [hl, distinct]
  · by_cases hr : observed = right
    · simp [hr, Ne.symm distinct]
    · simp [hl, hr]

end LeanTex.Core.PackageImports
