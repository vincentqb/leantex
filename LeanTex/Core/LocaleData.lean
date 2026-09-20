/-
Generated from babel's locale ini files (babel-en.ini, babel-fr.ini,
babel-de.ini); do not edit by hand. Regenerate with:
lake env lean --run scripts/gen-locale-data.lean

The ini data is sourced from the Unicode CLDR (each file's header says
so) and shipped with babel; adding a language to the engine is rerunning
the generator over one more file — babel's own design, copied.

licence: the babel locale ini files are released under the LaTeX Project
Public License (LPPL 1.3); their data derives from the Unicode CLDR
(UNICODE LICENSE V3, https://www.unicode.org/license.txt).
-/
import LeanTex.Core.Locale

namespace LeanTex.Core.Locale

/-- en: babel-en.ini. -/
def en : Locale := {
  tag := "en"
  figure := "Figure"
  table := "Table"
  abstract := "Abstract"
  references := "References"
  months := #["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"]
  quoteOpen := "“"
  quoteClose := "”"
  quoteInnerOpen := "‘"
  quoteInnerClose := "’"
  leftMin := 2
  rightMin := 3 }

/-- fr: babel-fr.ini. -/
def fr : Locale := {
  tag := "fr"
  figure := "Figure"
  table := "Table"
  abstract := "Résumé"
  references := "Références"
  months := #["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août", "septembre", "octobre", "novembre", "décembre"]
  quoteOpen := "«"
  quoteClose := "»"
  quoteInnerOpen := "«"
  quoteInnerClose := "»"
  leftMin := 2
  rightMin := 3 }

/-- de: babel-de.ini. -/
def de : Locale := {
  tag := "de"
  figure := "Abbildung"
  table := "Tabelle"
  abstract := "Zusammenfassung"
  references := "Literatur"
  months := #["Januar", "Februar", "März", "April", "Mai", "Juni", "Juli", "August", "September", "Oktober", "November", "Dezember"]
  quoteOpen := "„"
  quoteClose := "“"
  quoteInnerOpen := "‚"
  quoteInnerClose := "‘"
  leftMin := 2
  rightMin := 2 }

/-- The shipped locales. Contracts quantify over this list — adding
a locale is entering the contract (the `Theme.builtin` pattern). -/
def builtin : List Locale := [en, fr, de]

/-- The locale a BCP 47 tag names, by primary subtag: `fr-CA` finds `fr`.
`none` is a language the engine has no record for — the caller names it
(W0368) and uses English. -/
def forTag (tag : String) : Option Locale :=
  let primary := (tag.splitOn "-").headD tag
  builtin.find? (·.tag == primary)

/-- locale_data_total: the record type has no `Option` and no defaults,
so a shipped locale answers every site; this closes the loop by pinning
that no generated value is empty either. -/
theorem builtin_total : builtin.all (fun l =>
    !l.tag.isEmpty && !l.figure.isEmpty && !l.table.isEmpty &&
    !l.abstract.isEmpty && !l.references.isEmpty &&
    l.months.size == 12 && l.months.all (!·.isEmpty) &&
    !l.quoteOpen.isEmpty && !l.quoteClose.isEmpty &&
    !l.quoteInnerOpen.isEmpty && !l.quoteInnerClose.isEmpty &&
    l.leftMin > 0 && l.rightMin > 0) = true := by decide +kernel

/-- One record per tag: `forTag` is unambiguous. -/
theorem builtin_tags_nodup : (builtin.map (·.tag)).Nodup := by decide +kernel

/-- Every babel option name the engine maps resolves to a shipped
record: the name table cannot point at a locale that is not there.
(Stated over the tag lookup directly: `forTag`'s subtag split does not
kernel-reduce.) -/
theorem babelNames_resolve : babelNames.all (fun p =>
    builtin.any (·.tag == p.2)) = true := by decide +kernel

end LeanTex.Core.Locale
