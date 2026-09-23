import Tests.Support
import Tests.Surface
import Tests.Layout
import Tests.Census
import Tests.Backends
import Tests.Images
import Tests.Diag
import Tests.Themes
import Tests.FontMath
import Tests.Struct
import Tests.PdfConformance

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
  algorithmBackendChecks ref
  listingLanguageChecks ref
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
  alphaSplitChecks ref
  deckStructureChecks ref
  deckProgressChecks ref
  mathmlChecks ref
  linkHtmlChecks ref
  tableHtmlChecks ref
  contentOpsChecks ref
  outputContractChecks ref
  htmlAssetChecks ref
  anchorCostChecks ref

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
  sizeLadderChecks ref oneFace

  lineChecks ref geom oneFace
  declBlockChecks ref geom oneFace
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
  cutMarkChecks ref oneFace
  posterChecks ref oneFace
  censusChecks ref oneFace pats
  titledGroundChecks ref oneFace
  scopeChecks ref oneFace
  bandChecks ref oneFace
  agreeChecks ref oneFace pats
  artifactMarkChecks ref oneFace pats
  structTreeChecks ref oneFace
  pictureLayoutChecks ref oneFace
  boundaryFitChecks ref oneFace
  pictureDefnReachChecks ref oneFace
  pictureEveryLevelChecks ref oneFace
  quoteChecks ref oneFace
  refChecks ref oneFace
  titleChecks ref
  outlineChecks ref
  columnsChecks ref oneFace
  overlayChecks ref oneFace
  overlayBlockChecks ref oneFace
  alertOverlayChecks ref oneFace
  deckStepChecks ref oneFace
  deckRangeEndChecks ref oneFace
  deckAltChecks ref oneFace
  deckOverprintChecks ref oneFace
  deckOverprintDegradeChecks ref oneFace
  deckOverprintUnnumberableChecks ref oneFace
  deckOverlayWarnOnceChecks ref
  deckLogoChecks ref oneFace
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
  colorKeyChecks ref oneFace
  planChecks ref
  pdfFormChecks ref oneFace
  pdfCensusChecks ref oneFace
  pdfContractChecks ref oneFace
  objTableChecks ref oneFace
  featureCensusChecks ref oneFace
  pdfConformanceChecks ref oneFace
  leafAttributionChecks ref oneFace pats
  inlineAttributionChecks ref oneFace pats

/-- The surface-and-math suite: the dispatcher for the compat, class,
bibliography, and math elaboration blocks, so an added block lands here and
`main`'s spent elaboration budget stays flat — the regrowth the two suite
dispatchers above exist to prevent. -/
def surfaceSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  terminationChecks ref
  hookChecks ref
  hookSeamChecks ref
  urlFaceChecks ref
  compatIndexChecks ref
  compatConservationChecks ref
  crefChecks ref
  classOptionChecks ref
  linenoChecks ref
  footnoteChecks ref
  mathChecks ref
  bibChecks ref
  bibStyleChecks ref
  bibIrChecks ref
  bibApplyChecks ref
  dataChecks ref
  wrapperChecks ref
  unitChecks ref
  exprChecks ref
  centeringChecks ref
  smartChecks ref
  boundaryChecks ref
  picCacheChecks ref
  toolProbeChecks ref
  posterChromeCompatChecks ref
  keyedLookupChecks ref

/-- The theme, palette, and role blocks (Tests/Themes.lean), dispatched
together so each stays a leaf and `main`'s spent elaboration budget stays
flat. -/
def themeSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  paletteChecks ref
  mixChecks ref
  contrastChecks ref
  a11yChecks ref
  themeChecks ref
  designChecks ref
  roleChecks ref
  roleInvocationChecks ref
  realizedChecks ref
  realizeDocIdChecks ref
  roleShadowChecks ref
  geminiChecks ref

/-- The font-face blocks (Tests/FontMath.lean), run unconditionally:
fontSuiteChecks owns reporting a missing or unparsable font, so none of
these may hide behind the layout suite's font gate. -/
def fontFaceSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  fontDiagChecks ref
  weightAxisChecks ref
  weightResolveChecks ref
  declaredFaceChecks ref
  fallbackChecks ref
  smallCapsGsubChecks ref
  iconChecks ref
  fontsDeclChecks ref
  fontSuiteChecks ref

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)

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
  corpusCoverageChecks ref
  runGoldens update (failures ref)
  floatRefAgreementChecks ref

  dimChecks ref
  -- The integral toPtString case and mm/inch agreement are compile-time
  -- examples beside Dim; this fractional case is not decide-able (its
  -- String.Slice ops get stuck for decide and the kernel alike).
  check ref "sp pt string fractional" ((Dim.pt 3 / 2).toPtString == "1.5")
  kpChecks ref
  hyphenChecks ref
  walkChecks ref
  diagChecks ref
  pendingChecks ref
  structChecks ref
  ctxFoldChecks ref
  pictureElabChecks ref
  diagVoiceChecks ref update
  allowChecks ref
  werrorChecks ref
  declChecks ref
  tokensChecks ref
  compatChecks ref
  listingChecks ref
  posterCompatChecks ref
  columnFormChecks ref
  styParityChecks ref
  missingFileSpanChecks ref
  citeNoBibChecks ref
  surfaceSuiteChecks ref
  backendSuiteChecks ref
  themeSuiteChecks ref
  fontFaceSuiteChecks ref
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

