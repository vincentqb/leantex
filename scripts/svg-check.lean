import Tests.SvgValidation
import Tests.SvgTerminal

/-! External SVG converter oracle. Build leantex Tests.SvgValidation
Tests.SvgTerminal first. Requires xmllint, xsltproc, rsvg-convert and
Poppler; all documents are synthetic and no network inputs are used. -/

def main : IO UInt32 := do
  let failures ← IO.mkRef []
  Tests.svgValidationChecks failures
  Tests.svgTerminalBoundaryChecks failures
  Tests.svgTerminalDriverChecks failures
  let failed ← failures.get
  for name in failed.reverse do
    IO.eprintln s!"FAIL: {name}"
  IO.println s!"SVG converter oracle: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
