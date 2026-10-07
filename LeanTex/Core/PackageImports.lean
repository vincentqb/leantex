module

public import Init.Data.List.Find

namespace LeanTex.Core.PackageImports

/-- Literal package options, in their written order. Only an unbraced
comma separates options; spaces outside groups are zapped, as by the
kernel's `\zap@space`. Braces remain part of the comparison key: an option
first passed as `{a}` does not make a later `a` compatible. Keeping nested
values whole also prevents two different key/value pairs from becoming
the same bag of comma fragments. This scanner does not expand TeX macros. -/
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

/-- Packages whose bodies have been admitted, with their first effective
option lists. A reservation precedes execution, so a back edge in a style
dependency graph sees the same entry as a completed import.

This is execution state, separate from the conditional reader's account
of package declarations. A missing file makes no reservation. -/
public abbrev Loads := List (String × List String)

/-- A package body runs only on `load`. `skip []` is a compatible repeat;
a nonempty list names the new options of an option clash. The caller must
diagnose that list while preserving the first body's effects. -/
public inductive Decision where
  | load
  | skip (newOptions : List String)
  deriving Repr, BEq, Inhabited

/-- LaTeX's repeated-load comparison is membership, not option-list
equality: reordered or repeated members of the first list are compatible.
The first list itself keeps its order and multiplicity for `ProcessOptions*`.
Forwarded options precede direct options on a first load. A late
`PassOptionsToPackage` extends the compatibility list without rerunning
handlers (latex.ltx, `\@pass@ptions`). -/
public def admit (loads : Loads) (name : String) (options passed : List String) :
    Decision × Loads :=
  match loads.lookup name with
  | none => (.load, (name, passed ++ options) :: loads)
  | some first => (.skip (options.filter fun o => !(first ++ passed).contains o), loads)

/-- The first admission reserves exactly the original ordered list before
any caller can execute a body or follow its dependencies. -/
public theorem admit_first_exact (loads : Loads) (name : String)
    (options passed : List String)
    (h : loads.lookup name = none) :
    admit loads name options passed = (.load, (name, passed ++ options) :: loads) := by
  simp [admit, h]

/-- Both compatible repeats and clashes leave the original reservation
unchanged and cannot select the body-running decision. -/
public theorem admit_loaded_exact (loads : Loads) (name : String)
    (options passed first : List String) (h : loads.lookup name = some first) :
    admit loads name options passed =
      (.skip (options.filter fun o => !(first ++ passed).contains o), loads) := by
  simp [admit, h]

/-- A compatible repeat skips the body and preserves all prior imports,
for arbitrary option lists, including duplicates and permutations. -/
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

/-- Every reported clash item came from this request and was absent from
the first load and all passes in force here. No compatible option is
diagnosed as new. -/
public theorem admit_clash_exact (loads : Loads) (name : String)
    (options passed first : List String) (h : loads.lookup name = some first) (o : String) :
    (match (admit loads name options passed).1 with
      | .load => False
      | .skip missing => o ∈ missing) ↔ o ∈ options ∧ o ∉ first ++ passed := by
  simp [admit, h]

/-- Looking up the admission result reads the old first list if present,
or the new list for this name alone. This is the state the two production
gates carry, not a reordered model of their effect stream. -/
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

/-- A back edge, or any later compatible import, cannot run the first
body twice. The reservation itself is enough; completing the body is not
a prerequisite for stopping a cycle. -/
public theorem admit_repeat_fixed_point (loads : Loads) (name : String)
    (options passed again : List String) (h : loads.lookup name = none)
    (compatible : ∀ o ∈ again, o ∈ passed ++ options) :
    admit (admit loads name options passed).2 name again [] =
      (.skip [], (admit loads name options passed).2) := by
  rw [admit_first_exact loads name options passed h]
  exact admit_compatible_exact _ name again [] (passed ++ options) (by simp)
    (by simpa using compatible)

/-- Admissions of distinct package names commute under every lookup.
Their bodies still execute in source/dependency order. Artifact-level
commutation additionally needs independent declarations, as expressed by
`Elab.applyDecl_comm`; conflicts deliberately do not satisfy that premise. -/
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
