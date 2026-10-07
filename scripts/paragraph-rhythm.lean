import Tests.ParagraphMathRhythm

/-!
Focused shipped-line regression checks using invented text and bundled fonts.
Build the imported module first:

    lake build Tests.ParagraphMathRhythm
    lake env lean --run scripts/paragraph-rhythm.lean
-/

def main : IO UInt32 := do
  let ref ← IO.mkRef []
  paragraphMathRhythmChecks ref
  let failed ← ref.get
  for name in failed.reverse do IO.eprintln ("FAIL " ++ name)
  IO.println s!"paragraphMathRhythmChecks: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
