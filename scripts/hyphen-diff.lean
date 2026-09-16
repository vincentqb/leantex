/-
Differential test: leantex hyphenation vs real TeX on a word list. Run with:

  lake env lean --run scripts/hyphen-diff.lean [wordlist]

The oracle is luatex loading THE SAME pattern set the engine embeds
(hyph-en-us.tex / ushyphmax), with matching hyphenmins. Note that plain
`lualatex` would be the wrong oracle: TeX Live's language.dat maps the
`english` language to hyphen.tex (Knuth's frozen set), a strict subset, so
it legitimately reports fewer break candidates.

`\showhyphens` lists every admissible break, not one chosen rendering.
Our side calls `Hyphen.hyphenate` in-process; no leantex binary needed.
-/
import LeanTex

open LeanTex.Core

def die (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return code

/-- `word` with `-` at each admissible break: the `\showhyphens` format. -/
def showHyphens (pats : Hyphen.Patterns) (word : String) : String := Id.run do
  let breaks := Hyphen.hyphenate pats word
  let mut out := ""
  for (c, i) in word.toList.zipIdx do
    if i > 0 && breaks.contains i then
      out := out.push '-'
    out := out.push c
  return out

/-- Lowercase-alphabetic words of length ≥ 6 from the corpus and docs,
sorted and deduplicated — the same list the shell pipeline built with
tr/grep/sort -u. -/
def defaultWords : IO (Array String) := do
  let mut text := ""
  for entry in (← System.FilePath.readDir "tests/corpus").qsort (·.fileName < ·.fileName) do
    if entry.fileName.endsWith ".tex" then
      text := text ++ (← IO.FS.readFile entry.path) ++ "\n"
  for doc in ["PLAN.md", "AGENTS.md"] do
    text := text ++ (← IO.FS.readFile doc) ++ "\n"
  let isLetter := fun (c : Char) => (c ≥ 'a' && c ≤ 'z') || (c ≥ 'A' && c ≤ 'Z')
  let tokens := (text.split (fun c => !isLetter c)).toList.map (·.toString)
  let keep := tokens.filter fun w =>
    w.length ≥ 6 && w.toList.all (fun c => c ≥ 'a' && c ≤ 'z')
  let sorted := keep.toArray.qsort (· < ·)
  let mut out : Array String := #[]
  for w in sorted do
    if out.back? != some w then
      out := out.push w
  return out

def main (args : List String) : IO UInt32 := do
  let haveLuatex ← try
    pure ((← IO.Process.output { cmd := "luatex", args := #["--version"] }).exitCode == 0)
  catch _ => pure false
  if !haveLuatex then
    return (← die 2 "luatex not found")

  let words ← match args.head? with
    | some path =>
      let contents ← IO.FS.readFile path
      pure (((contents.splitOn "\n").filterMap fun line =>
        let w := line.trimAscii.toString
        if w.isEmpty then none else some w).toArray)
    | none => defaultWords
  let total := words.size

  let work ← IO.FS.createTempDir
  try
    let mut oracleTex := #["\\newlanguage\\probelang",
      "\\language=\\probelang",
      "\\lefthyphenmin=2 \\righthyphenmin=3",
      "\\input hyph-en-us"]
    for w in words do
      oracleTex := oracleTex.push s!"\\showhyphens\{{w}}"
    oracleTex := oracleTex.push "\\end"
    IO.FS.writeFile (work / "oracle.tex") (String.intercalate "\n" oracleTex.toList ++ "\n")
    let _ ← IO.Process.output
      { cmd := "luatex", args := #["--interaction=batchmode", "oracle.tex"], cwd := work }

    let log ← IO.FS.readFile (work / "oracle.log")
    let oracle := ((log.splitOn "\n").filterMap fun line =>
      match line.splitOn "\\tenrm " with
      | _ :: rest@(_ :: _) =>
        some ((String.intercalate "\\tenrm " rest).replace " " "")
      | _ => none).toArray
    if oracle.size != total then
      return (← die 2 s!"oracle produced {oracle.size} lines for {total} words; cannot compare")

    let pats := Hyphen.load
    let mut mismatches : Array String := #[]
    for (w, i) in words.zipIdx do
      let ours := showHyphens pats w
      let tex := oracle.getD i ""
      if tex != ours then
        mismatches := mismatches.push s!"  {w}: tex {tex} | leantex {ours}"
    if !mismatches.isEmpty then
      IO.println "mismatches:"
      for m in mismatches do
        IO.println m
      IO.println s!"hyphen-diff: {mismatches.size}/{total} words disagree"
      return 1
    IO.println s!"hyphen-diff: {total} words, leantex matches TeX exactly"
    return 0
  finally
    IO.FS.removeDirAll work
