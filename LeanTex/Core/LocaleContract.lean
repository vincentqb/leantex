module

public import LeanTex.Core.LocaleData
import all LeanTex.Core.Locale
import all Init.Data.Array.Basic

/-! Lookups and contracts over the generated locale data, which carries only data. -/

namespace LeanTex.Core.Locale

/-- The locale a BCP 47 tag names by its primary subtag; `none` is a language without a record. -/
public def forTag (tag : String) : Option Locale :=
  let primary := (tag.splitOn "-").headD tag
  builtin.find? (·.tag == primary)

public theorem builtin_total : builtin.all (fun l =>
    !l.tag.isEmpty && !l.figure.isEmpty && !l.table.isEmpty &&
    !l.algorithm.isEmpty &&
    !l.abstract.isEmpty && !l.references.isEmpty &&
    !l.proof.isEmpty && !l.contents.isEmpty &&
    l.months.size == 12 && l.months.all (!·.isEmpty) &&
    !l.quoteOpen.isEmpty && !l.quoteClose.isEmpty &&
    !l.quoteInnerOpen.isEmpty && !l.quoteInnerClose.isEmpty &&
    l.leftMin > 0 && l.rightMin > 0 &&
    !l.listing.isEmpty && !l.decimal.isEmpty && !l.group.isEmpty) = true := by
  decide +kernel

public theorem builtin_tags_nodup : (builtin.map (·.tag)).Nodup := by decide +kernel

public theorem babelNames_resolve : babelNames.all (fun p =>
    builtin.any (·.tag == p.2)) = true := by decide +kernel

end LeanTex.Core.Locale
