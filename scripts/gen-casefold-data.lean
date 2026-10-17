import scripts.GenData

open GenData

/-
Regenerate LeanTex/Core/CaseFoldData.lean from CaseFolding.txt (TeX Live's `unicode-data`, found
with kpsewhich without a source).
Usage: lake build scripts.GenData && lake env lean --run scripts/gen-casefold-data.lean [source] [--output path]
-/

def notice (version : String) : String := s!"/-
Generated from {version} (Unicode Character Database); do not edit by hand.
Regenerate with: lake env lean --run scripts/gen-casefold-data.lean

Full case folding: the common (C) and full (F) mappings, the folding CommonMark's link label
matching names. The table is fixed-width lowercase hex with no separators, read by byte offset
when a process first folds a character (`CaseFold.load`).

licence: UNICODE LICENSE V3 (Unicode data files); see
https://www.unicode.org/license.txt
-/
"

def hexToNat (s : String) : Nat := Id.run do
  let mut v := 0
  for c in s.toList do
    let d := if c.isDigit then c.toNat - '0'.toNat
      else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
      else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
      else 0
    v := v * 16 + d
  return v

/-- Fixed-width lowercase hex, left-padded; a value that does not fit dies. -/
def hexOf (width n : Nat) : IO String := do
  let ds := String.ofList (Nat.toDigits 16 n)
  if ds.length > width then
    die s!"{n} does not fit in {width} hex digits"
  return String.ofList (List.replicate (width - ds.length) '0') ++ ds

def main (args : List String) : IO UInt32 := do
  let (source, output) ← match args with
    | [] => pure (none, "LeanTex/Core/CaseFoldData.lean")
    | [s] => pure (some s, "LeanTex/Core/CaseFoldData.lean")
    | ["--output", o] => pure (none, o)
    | [s, "--output", o] => pure (some s, o)
    | _ => die "usage: gen-casefold-data.lean [source] [--output path]"
  let path ← match source with
    | some p => pure p
    | none => locate "CaseFolding.txt" "pass the path to CaseFolding.txt"
  let text ← IO.FS.readFile path
  let version := ((text.splitOn "\n").headD "").drop 2 |>.trimAscii.toString
  let mut entries : Array (Nat × List Nat) := #[]
  for line in text.splitOn "\n" do
    let body := ((line.splitOn "#").headD "").trimAscii.toString
    match (body.splitOn ";").map (·.trimAscii.toString) with
    | code :: status :: mapping :: _ =>
      if status == "C" || status == "F" then
        let parts := (mapping.splitOn " ").filter (!·.isEmpty) |>.map hexToNat
        entries := entries.push (hexToNat code, parts)
    | _ => pure ()
  if entries.isEmpty then die s!"no C or F mapping in {path}"
  let mut fold := ""
  for (cp, parts) in entries.qsort (fun a b => a.1 < b.1) do
    fold := fold ++ (← hexOf 6 cp) ++ (← hexOf 1 parts.length)
    for p in parts do
      fold := fold ++ (← hexOf 6 p)
  let header := notice version
  let content := "module\n\n" ++ header
    ++ "namespace LeanTex.Core.CaseFoldData\n\n"
    ++ "/-- The full case foldings: 6 hex digits for the codepoint, 1 for the count of the\n"
    ++ "characters it folds to, then 6 per character. Ascending by codepoint. -/\n"
    ++ s!"public def fold : String := \"{fold}\"\n\n"
    ++ "end LeanTex.Core.CaseFoldData\n"
  IO.FS.writeFile output content
  IO.println s!"wrote {output}: {entries.size} foldings from {version}"
  return 0
