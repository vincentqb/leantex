import Tests.Support

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-! # A file is read up to its live `\endinput`

TeX reads the rest of the terminator's line and no more of the file, so
what a style file parks after it — alternate definitions, settings the
author switched off — never takes. Fixtures in tests/corpus/sty-parity,
synthetic and invented; lualatex ships exactly the pages asserted here. -/

/-- The body text a `sty-parity` fixture ships, read off the laid-out
pages, with its diagnostics. -/
def endInputPage (fonts : Font.FontSet) (name : String) : IO (String × Array Diag) := do
  let (doc, ds, _) ← runStyParity name
  return (" ".intercalate ((bodyLines (layoutOf fonts doc)).toList.map (lineText ·)), ds)

def endInputChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet) : IO Unit := do
  let t := check ref
  let named (ds : Array Diag) (file : String) (line : Nat) : Bool :=
    ds.any fun d => d.span.any fun s => s.file == file && s.pos.line == line
  let (text, ds) ← endInputPage fonts "endinput"
  t "a style file's definitions before its terminator take"
    (hasStr text "Kept words stand here.")
  t "and a redefinition after it does not" (!hasStr text "Dead words")
  t "nothing after the terminator's line is read"
    (!named ds "venueend.sty" 6 && !named ds "venueend.sty" 7)
  t "the terminator is honoured, never refused as an internal"
    (Compat.styCounts "venueend.sty" ds == (3, 0, 0) &&
     ds.all fun d => d.subject != some "ctrl:endinput" || d.code == "N0100")
  let (text, _) ← endInputPage fonts "endinput-guard"
  t "a terminator whose condition holds ends the file"
    (hasStr text "Guarded words stand here." && !hasStr text "Dead words")
  let (text, _) ← endInputPage fonts "endinput-input"
  t "an \\input file ends at its terminator too"
    (hasStr text "Part words stand here." && hasStr text "Closing words." &&
     !hasStr text "Dead words")
