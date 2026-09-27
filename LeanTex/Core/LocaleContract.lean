import LeanTex.Core.LocaleData

/-!
Contracts and lookups over the generated locale data. The generated
module (`LocaleData.lean`) carries only data; the code that reads it and
the theorems that pin it are hand-owned here, so regeneration can never
drift logic and a logic edit can never be overwritten by the generator.
-/

namespace LeanTex.Core.Locale

/-- The locale a BCP 47 tag names, by primary subtag: `fr-CA` finds `fr`.
`none` is a language the engine has no record for — the caller names it
(W0368) and uses English. Primary subtags compare as spelled — BCP 47
conventionally lowercases them. -/
def forTag (tag : String) : Option Locale :=
  let primary := (tag.splitOn "-").headD tag
  builtin.find? (·.tag == primary)

/-- locale_data_total: the record type has no `Option` and no defaults,
so a shipped locale answers every site; this closes the loop by pinning
that no generated value is empty either. -/
theorem builtin_total : builtin.all (fun l =>
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

/-- One record per tag: `forTag` is unambiguous. -/
theorem builtin_tags_nodup : (builtin.map (·.tag)).Nodup := by decide +kernel

/-- Every babel option name the engine maps resolves to a shipped
record: the name table cannot point at a locale that is not there.
(Stated over the tag lookup directly: `forTag`'s subtag split does not
kernel-reduce.) -/
theorem babelNames_resolve : babelNames.all (fun p =>
    builtin.any (·.tag == p.2)) = true := by decide +kernel

end LeanTex.Core.Locale
