import Tests.SvgValidation
import Tests.SvgTerminal
import Tests.SvgBrowser
import Tests.SvgFaces
import Tests.SvgPublication

/-! External SVG converter and publication oracle. Build every imported
check and the CLI before running:

```
lake build leantex Tests.SvgValidation Tests.SvgTerminal Tests.SvgBrowser Tests.SvgFaces Tests.SvgPublication
lake env lean scripts/svg-check.lean
```

The driver checks import Main, so this entry uses `#eval`; run without
`--run`. Requires xmllint, xsltproc, rsvg-convert and Poppler; all documents
are synthetic and no network inputs are used. -/

#eval (do
  let failures ← IO.mkRef []
  Tests.svgBrowserSourceChecks failures
  Tests.svgFacePreparationChecks failures
  Tests.svgPublicationChecks failures
  Tests.svgValidationChecks failures
  Tests.svgTerminalBoundaryChecks failures
  Tests.svgTerminalDriverChecks failures
  let failed ← failures.get
  for name in failed.reverse do
    IO.eprintln s!"FAIL: {name}"
  IO.println s!"SVG converter oracle: {failed.length} failures"
  if !failed.isEmpty then
    throw <| IO.userError "SVG converter oracle failed"
  : IO Unit)
