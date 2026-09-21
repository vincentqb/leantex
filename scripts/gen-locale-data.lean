import Std.Data.HashMap

/-
Regenerate LeanTex/Core/LocaleData.lean from babel's locale ini files.
Run with:

  lake env lean --run scripts/gen-locale-data.lean [--output path]

The ini files (babel-en.ini, babel-fr.ini, babel-de.ini) are located via
kpsewhich.
-/

def notice : String := "/-
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
"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def findIni (lang : String) : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #[s!"babel-{lang}.ini"] }
  catch _ =>
    die "kpsewhich not found"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die s!"kpsewhich could not find babel-{lang}.ini"
  return path

structure IniLocale where
  tag : String := ""
  figure : String := ""
  table : String := ""
  abstract : String := ""
  references : String := ""
  months : Array String := #[]
  quotes : String := ""
  leftMin : Nat := 0
  rightMin : Nat := 0
  decimal : String := ""
  group : String := ""

def parseIni (text : String) : IniLocale := Id.run do
  let mut loc : IniLocale := {}
  let mut sec := ""
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.startsWith "[" && line.endsWith "]" then
      sec := ((line.drop 1).dropEnd 1).toString
    else if let k :: v := line.splitOn "=" then
      let k := k.trimAscii.toString
      let v := (String.intercalate "=" v).trimAscii.toString
      if sec == "identification" && k == "tag.bcp47" then
        loc := { loc with tag := v }
      -- [captions] is the Unicode section; [captions.licr] repeats it in
      -- LICR spelling and must not overwrite.
      else if sec == "captions" then
        if k == "figure" then loc := { loc with figure := v }
        else if k == "table" then loc := { loc with table := v }
        else if k == "abstract" then loc := { loc with abstract := v }
        else if k == "ref" then loc := { loc with references := v }
      else if sec == "date.gregorian" && k.startsWith "months.wide." then
        loc := { loc with months := loc.months.push v }
      else if sec == "typography" then
        if k == "lefthyphenmin" then loc := { loc with leftMin := v.toNat?.getD 0 }
        else if k == "righthyphenmin" then loc := { loc with rightMin := v.toNat?.getD 0 }
      else if sec == "characters" && k == "delimiters.quotes" then
        loc := { loc with quotes := v }
      else if sec == "numbers" then
        if k == "decimal" then loc := { loc with decimal := v }
        else if k == "group" then loc := { loc with group := v }
  return loc

def leanStr (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

/-- One kind's four cleveref name forms: `\crefname{k}{one}{many}` and
`\Crefname{k}{capOne}{capMany}`. -/
structure CrefGen where
  one : String
  many : String
  capOne : String
  capMany : String

/-- cleveref's names per language, read from cleveref.sty v0.21.4
(2018/03/27): the `\cref@addlanguagedefs{english}` block and the `german`
and `french` option blocks, under the package's own defaults — `abbrev`
on (`\@cref@abbrevtrue`), `capitalise` off (`\@cref@capitalisefalse`).
This is package data, not babel ini data, so the table lives here and
regenerates with the rest. Order per language: section, equation,
figure, table, then `\crefrangeconjunction`'s word. -/
def crefData : List (String × (CrefGen × CrefGen × CrefGen × CrefGen × String)) :=
  [("en", ({ one := "section", many := "sections",
             capOne := "Section", capMany := "Sections" },
           { one := "eq.", many := "eqs.",
             capOne := "Equation", capMany := "Equations" },
           { one := "fig.", many := "figs.",
             capOne := "Figure", capMany := "Figures" },
           { one := "table", many := "tables",
             capOne := "Table", capMany := "Tables" }, "to")),
   ("fr", ({ one := "section", many := "sections",
             capOne := "Section", capMany := "Sections" },
           { one := "équation", many := "équations",
             capOne := "Équation", capMany := "Équations" },
           { one := "figure", many := "figures",
             capOne := "Figure", capMany := "Figures" },
           { one := "tableau", many := "tableaux",
             capOne := "Tableau", capMany := "Tableaux" }, "à")),
   ("de", ({ one := "Abschnitt", many := "Abschnitte",
             capOne := "Abschnitt", capMany := "Abschnitte" },
           { one := "Gleichung", many := "Gleichungen",
             capOne := "Gleichung", capMany := "Gleichungen" },
           { one := "Abb.", many := "Abb.",
             capOne := "Abbildung", capMany := "Abbildungen" },
           { one := "Tabelle", many := "Tabellen",
             capOne := "Tabelle", capMany := "Tabellen" }, "bis"))]

def emitCref (c : CrefGen) : String :=
  s!"\{ one := {leanStr c.one}, many := {leanStr c.many}, " ++
  s!"capOne := {leanStr c.capOne}, capMany := {leanStr c.capMany} }"

/-- Invisible separators spelled as escapes, so the generated file shows
which space a locale groups by rather than an unreadable blank. -/
def leanStrVis (s : String) : String :=
  if s == "\u2009" then "\"\\u2009\""
  else if s == "\u202F" then "\"\\u202F\""
  else if s == "\u00A0" then "\"\\u00A0\""
  else leanStr s

/-- The listing caption word per tag. Not CLDR data — the babel inis carry
no listing caption — so this table is embedded here with its sources:
English is listings' own default (listings.sty,
`\lst@UserCommand\lstlistingname{Listing}`); French and German are
cleveref's language definitions (cleveref.sty, `\crefname{listing}`:
french "Liste", ngerman "Listing"). -/
def listingWord : List (String × String) :=
  [("en", "Listing"), ("fr", "Liste"), ("de", "Listing")]

/-- The digit-group separator per tag: the ini's `[numbers] group`, except
English, whose ini groups by "," — plain-prose grouping. `\num`'s spelling
is siunitx's, whose default `group-separator` is `\,`, the thin space
(siunitx manual §"Printing numbers"), so en groups by U+2009. -/
def groupOf (tag iniGroup : String) : String :=
  if tag == "en" then "\u2009" else iniGroup

def quoteAt (s : String) (i : Nat) : String :=
  match s.toList[i]? with
  | some c => String.ofList [c]
  | none => ""

def emit (name : String) (l : IniLocale) : String :=
  let cref := (crefData.lookup l.tag).getD
    ({ one := "", many := "", capOne := "", capMany := "" },
     { one := "", many := "", capOne := "", capMany := "" },
     { one := "", many := "", capOne := "", capMany := "" },
     { one := "", many := "", capOne := "", capMany := "" }, "")
  let (sec, eq, fig, tab, to) := cref
  s!"/-- {name}: babel-{l.tag}.ini; cref names from cleveref.sty v0.21.4. -/
def {name} : Locale := \{
  tag := {leanStr l.tag}
  figure := {leanStr l.figure}
  table := {leanStr l.table}
  abstract := {leanStr l.abstract}
  references := {leanStr l.references}
  months := #[{String.intercalate ", " (l.months.toList.map leanStr)}]
  quoteOpen := {leanStr (quoteAt l.quotes 0)}
  quoteClose := {leanStr (quoteAt l.quotes 1)}
  quoteInnerOpen := {leanStr (quoteAt l.quotes 2)}
  quoteInnerClose := {leanStr (quoteAt l.quotes 3)}
  leftMin := {l.leftMin}
  rightMin := {l.rightMin}
  crefSection := {emitCref sec}
  crefEquation := {emitCref eq}
  crefFigure := {emitCref fig}
  crefTable := {emitCref tab}
  crefRangeTo := {leanStr to}
  listing := {leanStr ((listingWord.lookup l.tag).getD "Listing")}
  decimal := {leanStr l.decimal}
  group := {leanStrVis (groupOf l.tag l.group)} }

"

def main (args : List String) : IO UInt32 := do
  let output := match args with
    | "--output" :: p :: _ => p
    | _ => "LeanTex/Core/LocaleData.lean"
  let mut body := ""
  for lang in ["en", "fr", "de"] do
    let text ← IO.FS.readFile (← findIni lang)
    let loc := parseIni text
    if loc.months.size != 12 then
      die s!"babel-{lang}.ini: {loc.months.size} months"
    if (crefData.lookup loc.tag).isNone then
      die s!"no cref names for '{loc.tag}': add its cleveref.sty language block to crefData"
    if loc.decimal.isEmpty || loc.group.isEmpty then
      die s!"babel-{lang}.ini: missing [numbers] decimal or group"
    body := body ++ emit lang loc
  let content := notice
    ++ "import LeanTex.Core.Locale\n\n"
    ++ "namespace LeanTex.Core.Locale\n\n"
    ++ body
    ++ "/-- The shipped locales. Contracts quantify over this list — adding
a locale is entering the contract (the `Theme.builtin` pattern). -/
def builtin : List Locale := [en, fr, de]

end LeanTex.Core.Locale
"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}"
  return 0
