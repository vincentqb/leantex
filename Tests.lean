import Tests.Support
import Tests.Surface
import Tests.Layout
import Tests.Census
import Tests.Backends
import Tests.Diag
import Tests.Themes
import Tests.FontMath

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

/-- The backend blocks, dispatched together so each stays a leaf the
module split can place; main runs this right after compatChecks, which
used to carry these calls as its tail. -/
def backendSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  footnoteBackendChecks ref
  styleChecks ref
  htmlLayoutChecks ref
  htmlRhythmChecks ref
  classHookChecks ref
  runinChecks ref
  abstractChecks ref
  headingNumberChecks ref
  argTokenChecks ref
  anchorChecks ref
  markdownChecks ref
  mdPreambleChecks ref
  backendChecks ref
  landmarkChecks ref
  pinChecks ref
  mdNameChecks ref
  interactionChecks ref
  motionSiteChecks ref
  fontShipChecks ref
  deckCssChecks ref
  deckImageChecks ref
  deckStructureChecks ref
  deckProgressChecks ref
  mathmlChecks ref

/-- The layout, census, theme, and chrome blocks all read the same shipped
face; dispatched together so each stays a leaf the module split can place.
fontSuiteChecks used to carry these calls in its parse-success arm — it
still owns reporting a missing or unparsable font, so failure here only
skips. -/
def layoutSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let pats := Hyphen.english.get
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let oneFace := oneFaceOf font
  let geom : Layout.Geom := {}
  pdfFaceChecks ref geom oneFace font
  webMetaChecks ref geom oneFace

  lineChecks ref geom oneFace
  footnoteLayoutChecks ref oneFace
  headingRhythmChecks ref oneFace
  titleBreakChecks ref oneFace
  bodyColorChecks ref oneFace
  listChecks ref oneFace font
  filChecks ref oneFace
  underlineChecks ref geom oneFace font
  linkSignalChecks ref geom oneFace
  inkGeometryChecks ref
  spacingChecks ref geom oneFace font
  titleBarChecks ref geom oneFace font
  slideChecks ref oneFace
  tableChecks ref oneFace
  recoveryChecks ref oneFace
  roleLayoutChecks ref geom oneFace
  navLayoutChecks ref geom oneFace
  vdistChecks ref geom oneFace
  headBandChecks ref oneFace
  furnitureSymmetryChecks ref oneFace
  pageNumberChecks ref oneFace
  cardChecks ref oneFace pats
  posterChecks ref oneFace
  censusChecks ref oneFace pats
  scopeChecks ref oneFace
  bandChecks ref oneFace
  agreeChecks ref oneFace pats
  pictureLayoutChecks ref oneFace
  quoteChecks ref oneFace
  refChecks ref oneFace
  titleChecks ref
  outlineChecks ref
  columnsChecks ref oneFace
  overlayChecks ref oneFace
  overlayBlockChecks ref oneFace
  deckStepChecks ref oneFace
  noteChecks ref oneFace
  themeFurnitureChecks ref oneFace
  themeReconcileChecks ref oneFace
  chromeDeclChecks ref
  layerDiagChecks ref
  footerBandChecks ref oneFace
  chromeFooterChecks ref oneFace
  numberingChecks ref oneFace
  composeChecks ref oneFace
  frameFootChecks ref oneFace
  scannerChecks ref
  rhythmChecks ref oneFace
  measureChecks ref oneFace
  imageChecks ref oneFace

/-- The surface-and-math suite: the dispatcher for the compat, class,
bibliography, and math elaboration blocks, so an added block lands here and
`main`'s spent elaboration budget stays flat — the regrowth the two suite
dispatchers above exist to prevent. -/
def surfaceSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  terminationChecks ref
  compatIndexChecks ref
  compatConservationChecks ref
  classOptionChecks ref
  footnoteChecks ref
  mathChecks ref
  bibChecks ref
  bibStyleChecks ref
  bibIrChecks ref
  bibApplyChecks ref
  dataChecks ref

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)
  let t := check ref

  utf8Checks ref
  argsChecks ref
  renderChecks ref
  lexChecks ref
  nfcChecks ref
  accentChecks ref
  localeChecks ref
  parseChecks ref
  elabDocChecks ref

  -- goldens
  runGoldens update (failures ref)
  floatRefAgreementChecks ref

  -- dim
  t "sp pt string" ((Dim.pt 10).toPtString == "10" && (Dim.pt 3 / 2).toPtString == "1.5")
  dimChecks ref
  -- The two spellings of one length must agree: the engine's pt is the big
  -- point everywhere, so a default deck stage and \page{ width = 160mm }
  -- name the same number of sp.
  t "dim mm agrees with inch" (Dim.mm 254 == Dim.inch 10)

  kpChecks ref
  hyphenChecks ref
  walkChecks ref
  diagChecks ref
  pictureElabChecks ref
  diagVoiceChecks ref update
  allowChecks ref
  werrorChecks ref
  declChecks ref
  tokensChecks ref
  compatChecks ref
  posterCompatChecks ref
  styParityChecks ref
  surfaceSuiteChecks ref
  backendSuiteChecks ref
  unitChecks ref
  exprChecks ref
  wrapperChecks ref
  centeringChecks ref
  fontDiagChecks ref
  declaredFaceChecks ref
  fallbackChecks ref
  smallCapsGsubChecks ref
  iconChecks ref
  smartChecks ref
  linkHtmlChecks ref
  paletteChecks ref
  mixChecks ref
  contrastChecks ref
  a11yChecks ref
  themeChecks ref
  designChecks ref
  roleChecks ref
  roleInvocationChecks ref
  realizedChecks ref
  roleShadowChecks ref
  fontsDeclChecks ref
  fontSuiteChecks ref
  layoutSuiteChecks ref

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1

