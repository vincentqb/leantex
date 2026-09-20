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
the generator over one more file — babel's own design, copied.

licence: the babel locale ini files are released under the LaTeX Project
Public License (LPPL 1.3); their data derives from the Unicode CLDR
(UNICODE LICENSE V3, https://www.unicode.org/license.txt).
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
  return loc

def leanStr (s : String) : String :=
  "\"" ++ ((s.replace "\\" "\\\\").replace "\"" "\\\"") ++ "\""

def quoteAt (s : String) (i : Nat) : String :=
  match s.toList[i]? with
  | some c => String.ofList [c]
  | none => ""

def emit (name : String) (l : IniLocale) : String :=
  s!"/-- {name}: babel-{l.tag}.ini. -/
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
  rightMin := {l.rightMin} }

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
    body := body ++ emit lang loc
  let content := notice
    ++ "import LeanTex.Core.Locale\n\n"
    ++ "namespace LeanTex.Core.Locale\n\n"
    ++ body
    ++ "/-- The shipped locales. Contracts quantify over this list — adding
a locale is entering the contract (the `Theme.builtin` pattern). -/
def builtin : List Locale := [en, fr, de]

/-- The locale a BCP 47 tag names, by primary subtag: `fr-CA` finds `fr`.
`none` is a language the engine has no record for — the caller names it
(W0368) and uses English. Primary subtags compare as spelled — BCP 47
conventionally lowercases them. -/
def forTag (tag : String) : Option Locale :=
  let primary := (tag.splitOn \"-\").headD tag
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
"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}"
  return 0
