import Tests.SvgValidation

/-! External SVG converter oracle. Build leantex Tests.SvgValidation first.
Requires xmllint and rsvg-convert; no document or network inputs. -/

def main : IO UInt32 := do
  let failures ← IO.mkRef []
  Tests.svgValidationChecks failures
  let failed ← failures.get
  for name in failed.reverse do
    IO.eprintln s!"FAIL: {name}"
  IO.println s!"SVG converter oracle: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
