/-
Regenerate LeanTex/Core/HyphenData.lean from hyph-en-us.tex. Run with:

  lake env lean --run scripts/gen-hyphen-data.lean [source] [--output path]

Without a source argument the file is located via kpsewhich.
-/

def notice : String := "/-
Generated from hyph-en-us.tex (hyph-utf8); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-hyphen-data.lean

title: Hyphenation patterns for American English
copyright: Copyright (C) 1990, 2004, 2005 Gerard D.C. Kuiken
licence: Copying and distribution of this file, with or without
modification, are permitted in any medium without royalty provided the
copyright notice and this notice are preserved.
hyphenmins: left 2, right 3
-/
"

def die (msg : String) : IO α := do
  IO.eprintln msg
  IO.Process.exit 1

def defaultSource : IO String := do
  let out ← try
    IO.Process.output { cmd := "kpsewhich", args := #["hyph-en-us.tex"] }
  catch _ =>
    die "kpsewhich not found; pass the path to hyph-en-us.tex"
  let path := out.stdout.trimAscii.toString
  if out.exitCode != 0 || path.isEmpty then
    die "kpsewhich could not find hyph-en-us.tex"
  return path

/-- The whitespace-separated words of the `\command{ … }` block, comments
stripped, matching the Python generator token for token. -/
def block (text command : String) : IO (List String) := do
  let marker := "\\" ++ command ++ "{"
  let parts := text.splitOn marker
  if parts.length < 2 then
    die s!"source has no {marker}"
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
  let mut output := "LeanTex/Core/HyphenData.lean"
  let mut rest := args
  repeat
    match rest with
    | [] => break
    | "--output" :: v :: more => output := v; rest := more
    | "--output" :: [] => die "'--output' needs a path"
    | a :: more =>
      if a.startsWith "--output=" then
        output := (a.splitOn "=" |>.drop 1 |> String.intercalate "=")
      else
        source := some a
      rest := more
  let sourcePath ← match source with
    | some p => pure p
    | none => defaultSource
  let text ← IO.FS.readFile sourcePath
  let patterns ← block text "patterns"
  let exceptions ← block text "hyphenation"
  let content := notice
    ++ "namespace LeanTex.Core.HyphenData\n\n"
    ++ s!"def patterns : String := \"{leanString (String.intercalate " " patterns)}\"\n\n"
    ++ s!"def exceptions : String := \"{leanString (String.intercalate " " exceptions)}\"\n\n"
    ++ "end LeanTex.Core.HyphenData\n"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}: {patterns.length} patterns, {exceptions.length} exceptions"
  return 0
