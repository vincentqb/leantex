/-
Regenerate LeanTex/Core/HyphenData*.lean from the hyph-utf8 pattern files.
Run with:

  lake env lean --run scripts/gen-hyphen-data.lean [source] [--lang en|fr] [--output path]

Without a source argument the language's file is located via kpsewhich.
Each language is one row of `langs`: adding a language to the engine is
adding a row and rerunning — babel's data-not-code design, copied.
-/

structure LangSpec where
  lang : String
  source : String
  output : String
  ns : String
  notice : String

def langs : List LangSpec :=
  [{ lang := "en"
     source := "hyph-en-us.tex"
     output := "LeanTex/Core/HyphenData.lean"
     ns := "LeanTex.Core.HyphenData"
     notice := "/-
Generated from hyph-en-us.tex (hyph-utf8); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-hyphen-data.lean

title: Hyphenation patterns for American English
copyright: Copyright (C) 1990, 2004, 2005 Gerard D.C. Kuiken
licence: Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved.
hyphenmins: left 2, right 3
-/
" },
   { lang := "fr"
     source := "hyph-fr.tex"
     output := "LeanTex/Core/HyphenDataFr.lean"
     ns := "LeanTex.Core.HyphenDataFr"
     notice := "/-
Generated from hyph-fr.tex (hyph-utf8); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-hyphen-data.lean --lang fr

title: Hyphenation patterns for French
copyright: Copyright (C) 1994-2002 Daniel Flipo, Bernard Gaulle,
2016 Arthur Reutenauer
licence: MIT (https://opensource.org/licenses/MIT)
hyphenmins: left 2, right 3
-/
" },
   { lang := "de"
     source := "hyph-de-1996.tex"
     output := "LeanTex/Core/HyphenDataDe.lean"
     ns := "LeanTex.Core.HyphenDataDe"
     notice := "/-
Generated from hyph-de-1996.tex (hyph-utf8); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-hyphen-data.lean --lang de

title: Hyphenation patterns for German, reformed orthography
copyright: Copyright (C) 2013-2023 Stephan Hennig, Werner Lemberg,
Guenter Milde et al. (dehyph-exptl)
licence: MIT (https://opensource.org/licenses/MIT)
hyphenmins: left 2, right 2
-/
" }]

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def defaultSource (file : String) : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #[file] }
  catch _ =>
    die s!"kpsewhich not found; pass the path to {file}"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die s!"kpsewhich could not find {file}"
  return path

/-- The whitespace-separated words of the `\command{ … }` block, comments
stripped, matching the Python generator token for token. -/
def block (text command : String) : IO (List String) := do
  let marker := "\\" ++ command ++ "{"
  let parts := text.splitOn marker
  if parts.length < 2 then
    return []
  let tail := String.intercalate marker (parts.drop 1)
  let mut body : List String := []
  for line in tail.splitOn "\n" do
    let line := ((line.splitOn "%").headD "").trimAscii.toString
    if line == "}" then
      return body
    if !line.isEmpty then
      body := body ++ ((line.split Char.isWhitespace).toList.map (·.toString)).filter (!·.isEmpty)
  return body

def leanString (value : String) : String :=
  (value.replace "\\" "\\\\").replace "\"" "\\\""

def main (args : List String) : IO UInt32 := do
  let mut source : Option String := none
  let mut lang := "en"
  let mut output : Option String := none
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--output" :: v :: more => output := some v; rest := more
    | "--output" :: [] => die "'--output' needs a path"
    | "--lang" :: v :: more => lang := v; rest := more
    | "--lang" :: [] => die "'--lang' needs a language"
    | a :: more =>
      if a.startsWith "--output=" then
        output := some (a.splitOn "=" |>.drop 1 |> String.intercalate "=")
      else
        source := some a
      rest := more
  let some spec := langs.find? (·.lang == lang)
    | die s!"no language row for '{lang}'; rows: {String.intercalate ", " (langs.map (·.lang))}"
  let outPath := (output).getD spec.output
  let sourcePath ← match source with
    | some p => pure p
    | none => defaultSource spec.source
  let text ← IO.FS.readFile sourcePath
  let patterns ← block text "patterns"
  let exceptions ← block text "hyphenation"
  if patterns.isEmpty then
    die s!"{sourcePath} has no \\patterns block"
  let content := "module\n\n" ++ spec.notice
    ++ s!"namespace {spec.ns}\n\n"
    ++ s!"public def patterns : String := \"{leanString (String.intercalate " " patterns)}\"\n\n"
    ++ s!"public def exceptions : String := \"{leanString (String.intercalate " " exceptions)}\"\n\n"
    ++ s!"end {spec.ns}\n"
  IO.FS.writeFile outPath content
  IO.println s!"wrote {outPath}: {patterns.length} patterns, {exceptions.length} exceptions"
  return 0
