import Tests.SvgValidation
import Tests.SvgTerminal
import Tests.SvgBrowser
import Tests.SvgFaces
import Tests.SvgPublication
import Tests.SvgParity

/-! External SVG oracle: the native reader against libxml2 and libxslt, the converter's faces,
publication.
Usage: lake build leantex Tests.SvgValidation Tests.SvgTerminal Tests.SvgBrowser Tests.SvgFaces Tests.SvgPublication Tests.SvgParity && lake env lean --run scripts/svg-check.lean -/

def main : IO UInt32 := do
  let failures ← IO.mkRef []
  Tests.svgBrowserSourceChecks failures
  Tests.svgFacePreparationChecks failures
  Tests.svgPublicationChecks failures
  Tests.svgValidationChecks failures
  Tests.svgTerminalBoundaryChecks failures
  Tests.svgTerminalDriverChecks failures
  Tests.svgParityChecks failures
  let failed ← failures.get
  for name in failed.reverse do
    IO.eprintln s!"FAIL: {name}"
  IO.println s!"SVG converter oracle: {failed.length} failures"
  return if failed.isEmpty then 0 else 1
