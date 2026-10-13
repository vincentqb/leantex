import Tests.SvgValidation
import Tests.SvgTerminal
import Tests.SvgBrowser
import Tests.SvgFaces
import Tests.SvgPublication
import Tests.SvgParity

/-! External SVG oracle: the native reader's parity with the libxml2 and
libxslt boundary it replaced, the converter's faces, and publication.
Build every imported check and the CLI before running:

```
lake build leantex Tests.SvgValidation Tests.SvgTerminal Tests.SvgBrowser Tests.SvgFaces Tests.SvgPublication Tests.SvgParity
lake env lean --run scripts/svg-check.lean
```

Requires xmllint, xsltproc, rsvg-convert and Poppler — the oracle's tools,
none of them on the render path but librsvg for a figure the engine does
not draw whole; all documents are synthetic and no network inputs are
used. -/

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
