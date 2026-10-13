module

public import Tests.Support
public import Tests.SvgLegacy
public import LeanTex.Core.SvgImport
public import LeanTex.Core.SvgPoster

public section

/-! The native judge and terminal projection answer as libxml2 and libxslt did over the shared
matrices, but for the declared widenings (`svgBoundaryWidened`); needs xmllint and xsltproc. -/

namespace Tests

open LeanTex.Core

def svgParityChecks (ref : IO.Ref (List String)) : IO Unit := do
  for (name, body) in svgBoundaryAdmitted do
    let legacy ← SvgLegacy.judge (svgDocument body)
    let native := (Svg.judge (svgDocument body)).toBool
    if svgBoundaryWidened name then
      check ref s!"SVG parity {name}: the native judge's declared widening" (native && !legacy.toBool)
    else
      check ref s!"SVG parity {name}: both boundaries admit" (native && legacy.toBool)
  for (name, body) in svgBoundaryRefused do
    let source := svgDocument (svgRedSquare ++ body)
    check ref s!"SVG parity {name}: both boundaries refuse"
      (!(Svg.judge source).toBool && !(← SvgLegacy.judge source).toBool)
  for (name, source, text?) in svgBoundaryEncodings do
    let native := (Svg.judge source).toBool
    let legacy := (← SvgLegacy.judge source).toBool
    if svgBoundaryNarrowed name then
      check ref s!"SVG parity encoding {name}: the native reader's declared narrowing" (!native && legacy)
    else
      check ref s!"SVG parity encoding {name}: both readers agree" (native == legacy && native == text?.isSome)
  for (name, source) in svgBoundaryMalformed (String.fromUTF8! (svgDocument svgRedSquare)) do
    check ref s!"SVG parity {name} source: both readers refuse"
      (!(Svg.judge source.toUTF8).toBool && !(← SvgLegacy.judge source.toUTF8).toBool)
  let doc (body : String) := svgDocument (width := 32) (height := 16) body
  for (name, body) in svgTerminalRefused do
    let legacy ← SvgLegacy.terminal (doc body)
    check ref s!"SVG parity terminal {name}: both projections refuse, naming the pose"
      ((match SvgPoster.pose (doc body) true with
        | .error e => hasStr e "SVG last poster"
        | .ok _ => false) &&
       (match legacy with
        | .error e => hasStr e "SVG last poster"
        | .ok _ => false))
  for (name, body, _) in svgTerminalAccepted do
    let native := (SvgPoster.pose (doc body) true).map fun t => (Svg.importTree t).fig.marks
    let legacy := (← SvgLegacy.terminal (doc body)).bind fun bytes =>
      (SvgPoster.pose bytes false).map fun t => (Svg.importTree t).fig.marks
    check ref s!"SVG parity terminal {name}: both projections end in one pose"
      (match native, legacy with
        | .ok a, .ok b => a == b
        | _, _ => false)

end Tests
