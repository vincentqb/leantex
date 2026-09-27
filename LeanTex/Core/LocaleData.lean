/-
Generated from babel's locale ini files (babel-en.ini, babel-fr.ini,
babel-de.ini); do not edit by hand. Regenerate with:
lake env lean --run scripts/gen-locale-data.lean

The ini data is sourced from the Unicode CLDR (each file's header says
so) and shipped with babel; adding a language to the engine is rerunning
the generator over one more file — babel's own design, copied. This
module carries only data; contracts and lookups over it live in the
hand-owned LocaleContract.lean.

licence: the babel locale ini files are released under the LaTeX Project
Public License (LPPL 1.3); their data derives from the Unicode CLDR
(UNICODE LICENSE V3, https://www.unicode.org/license.txt). The cref name
fields are read from cleveref.sty v0.21.4 (2018/03/27), also LPPL 1.3;
the generator carries that table, cited beside it.
-/
import LeanTex.Core.Locale

namespace LeanTex.Core.Locale

/-- en: babel-en.ini; cref names from cleveref.sty v0.21.4. -/
def en : Locale := {
  tag := "en"
  figure := "Figure"
  table := "Table"
  algorithm := "Algorithm"
  abstract := "Abstract"
  references := "References"
  proof := "Proof"
  contents := "Contents"
  months := #["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"]
  quoteOpen := "“"
  quoteClose := "”"
  quoteInnerOpen := "‘"
  quoteInnerClose := "’"
  leftMin := 2
  rightMin := 3
  crefSection := { one := "section", many := "sections", capOne := "Section", capMany := "Sections" }
  crefEquation := { one := "eq.", many := "eqs.", capOne := "Equation", capMany := "Equations" }
  crefFigure := { one := "fig.", many := "figs.", capOne := "Figure", capMany := "Figures" }
  crefTable := { one := "table", many := "tables", capOne := "Table", capMany := "Tables" }
  crefAlgorithm := { one := "algorithm", many := "algorithms", capOne := "Algorithm", capMany := "Algorithms" }
  crefRangeTo := "to"
  listing := "Listing"
  decimal := "."
  group := "\u2009" }

/-- fr: babel-fr.ini; cref names from cleveref.sty v0.21.4. -/
def fr : Locale := {
  tag := "fr"
  figure := "Figure"
  table := "Table"
  algorithm := "Algorithme"
  abstract := "Résumé"
  references := "Références"
  proof := "Démonstration"
  contents := "Table des matières"
  months := #["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août", "septembre", "octobre", "novembre", "décembre"]
  quoteOpen := "«"
  quoteClose := "»"
  quoteInnerOpen := "«"
  quoteInnerClose := "»"
  leftMin := 2
  rightMin := 3
  crefSection := { one := "section", many := "sections", capOne := "Section", capMany := "Sections" }
  crefEquation := { one := "équation", many := "équations", capOne := "Équation", capMany := "Équations" }
  crefFigure := { one := "figure", many := "figures", capOne := "Figure", capMany := "Figures" }
  crefTable := { one := "tableau", many := "tableaux", capOne := "Tableau", capMany := "Tableaux" }
  crefAlgorithm := { one := "algorithme", many := "algorithmes", capOne := "Algorithme", capMany := "Algorithmes" }
  crefRangeTo := "à"
  listing := "Liste"
  decimal := ","
  group := "\u202F" }

/-- de: babel-de.ini; cref names from cleveref.sty v0.21.4. -/
def de : Locale := {
  tag := "de"
  figure := "Abbildung"
  table := "Tabelle"
  algorithm := "Algorithmus"
  abstract := "Zusammenfassung"
  references := "Literatur"
  proof := "Beweis"
  contents := "Inhaltsverzeichnis"
  months := #["Januar", "Februar", "März", "April", "Mai", "Juni", "Juli", "August", "September", "Oktober", "November", "Dezember"]
  quoteOpen := "„"
  quoteClose := "“"
  quoteInnerOpen := "‚"
  quoteInnerClose := "‘"
  leftMin := 2
  rightMin := 2
  crefSection := { one := "Abschnitt", many := "Abschnitte", capOne := "Abschnitt", capMany := "Abschnitte" }
  crefEquation := { one := "Gleichung", many := "Gleichungen", capOne := "Gleichung", capMany := "Gleichungen" }
  crefFigure := { one := "Abb.", many := "Abb.", capOne := "Abbildung", capMany := "Abbildungen" }
  crefTable := { one := "Tabelle", many := "Tabellen", capOne := "Tabelle", capMany := "Tabellen" }
  crefAlgorithm := { one := "Algorithmus", many := "Algorithmen", capOne := "Algorithmus", capMany := "Algorithmen" }
  crefRangeTo := "bis"
  listing := "Listing"
  decimal := ","
  group := "." }

/-- The shipped locales. Contracts quantify over this list — adding
a locale is entering the contract (the `Theme.builtin` pattern). -/
def builtin : List Locale := [en, fr, de]

end LeanTex.Core.Locale
