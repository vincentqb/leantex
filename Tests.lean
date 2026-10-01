import Tests.Support
import Tests.Surface
import Tests.FontSize
import Tests.CancelRegression
import Tests.CancelHtml
import Tests.BeamerHooks
import Tests.BeamerColors
import Tests.MintedSettings
import Tests.ListingHighlight
import Tests.Markdown
import Tests.MarkdownInput
import Tests.XparseProvide
import Tests.XparseIgnoredOperands
import Tests.OverlaySets
import Tests.FrameHeadingScope
import Tests.Census
import Tests.Backends
import Tests.Images
import Tests.SvgImages
import Tests.SvgTools
import Tests.AnimatedGraphics
import Tests.AnimatedFaces
import Tests.PdfPageSelection
import Tests.PdfReadObjects
import Tests.RasterPages
import Tests.Diag
import Tests.Themes
import Tests.FontMath
import Tests.MathAlphaGeometry
import Tests.MathAlphaSemantics
import Tests.Struct
import Tests.PdfConformance
import Tests.Artifact
import Tests.CompatGate
import Tests.HtmlTokens
import Tests.HtmlA11y
import Tests.Conditionals
import Tests.MacroBinding
import Tests.MacroArguments
import Tests.PackageOptions
import Tests.BoxRow
import Tests.RecipeStructure
import Tests.PackageCode
import Tests.DiagAudit
import Tests.MathSym
import Tests.AmsMath
import Tests.Refusal
import Tests.EndInput
import Tests.Redefine
import Tests.Settings
import Tests.Kernel
import Tests.PicturePaths
import Tests.PictureKeys
import Tests.TextSym
import Tests.InlineVerb
import Tests.VerbatimAmbient
import Tests.OwnBib
import Tests.BigDelim
import Tests.Regress
import Tests.Reports
import Tests.Natbib
import Tests.LinkColor

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open Tests (mintedSettingsChecks listingHighlightChecks svgAssetChecks svgToolChecks
  animatedGraphicsChecks animatedFacesChecks markdownInputChecks xparseProvideChecks
  xparseIgnoredOperandsChecks macroBindingChecks macroArgumentChecks packageOptionChecks
  overlaySetChecks mathAlphaSemanticsChecks)

/-- The backend blocks, dispatched together so each stays a leaf the
module split can place; main runs this right after compatChecks, which
used to carry these calls as its tail. -/
def backendSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  footnoteBackendChecks ref
  styleChecks ref
  htmlLayoutChecks ref
  htmlRhythmChecks ref
  htmlListGapChecks ref
  htmlSectionGapChecks ref
  printLiftChecks ref
  classHookChecks ref
  runinChecks ref
  abstractChecks ref
  headingNumberChecks ref
  argTokenChecks ref
  anchorChecks ref
  markdownChecks ref
  algorithmBackendChecks ref
  listingLanguageChecks ref
  mintedSettingsChecks ref
  listingHighlightChecks ref
  mdPreambleChecks ref
  markdownInputChecks ref
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
  htmlTokenClosureChecks ref
  htmlSourcedGapChecks ref
  htmlA11yChecks ref

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
  let arts ← goldenArts oneFace
  pdfFaceChecks ref geom oneFace font
  webMetaChecks ref geom oneFace
  sizeLadderChecks ref oneFace

  lineChecks ref geom oneFace
  declBlockChecks ref geom oneFace
  footnoteLayoutChecks ref oneFace
  themeTitleShipChecks ref oneFace
  titleSlotShipChecks ref oneFace
  beamerHookChecks ref oneFace
  beamerColorsChecks ref oneFace
  titleTemplateOptionalChecks ref oneFace
  titleTemplateColorChecks ref oneFace
  headingRhythmChecks ref oneFace
  titleBreakChecks ref oneFace
  bodyColorChecks ref oneFace
  colorModelChecks ref oneFace
  listChecks ref oneFace font
  algNumberColumnChecks ref oneFace
  filChecks ref oneFace
  raggedSideChecks ref oneFace
  boxSideChecks ref oneFace
  boxSideHtmlChecks ref
  headlineSideChecks ref
  titleHeadingChecks ref oneFace
  boxWidthChecks ref oneFace
  minipageRowChecks ref oneFace
  recipeLinkWrapperChecks ref oneFace
  boxPosRowChecks ref oneFace
  underlineChecks ref geom oneFace font
  linkSignalChecks ref geom oneFace
  inkGeometryChecks ref
  spacingChecks ref geom oneFace font
  displayTexChecks ref oneFace
  titleBarChecks ref geom oneFace font
  slideChecks ref oneFace
  fragileNoopChecks ref oneFace
  tableChecks ref oneFace
  multicolumnSpanChecks ref oneFace
  recoveryChecks ref oneFace
  floorPolicyChecks ref oneFace
  mathContainChecks ref oneFace
  cancelReportChecks ref oneFace
  cancelGeometryChecks ref oneFace
  cancelBoxChecks ref oneFace
  cancelHtmlChecks ref
  roleLayoutChecks ref geom oneFace
  navLayoutChecks ref geom oneFace
  vdistChecks ref geom oneFace
  headBandChecks ref oneFace
  furnitureSymmetryChecks ref oneFace
  pageNumberChecks ref oneFace
  footskipChecks ref oneFace
  cardChecks ref oneFace pats
  cutMarkChecks ref oneFace
  drawnMarkChecks ref oneFace
  pdfVersionChecks ref oneFace
  driverOptionChecks ref oneFace
  posterChecks ref oneFace
  censusChecks ref oneFace pats
  titledGroundChecks ref oneFace
  realizedAgreeChecks ref oneFace
  inkBoundChecks ref oneFace
  oneInkChecks ref oneFace
  scopeChecks ref oneFace
  bandChecks ref oneFace
  agreeChecks ref oneFace pats
  artifactMarkChecks ref oneFace pats
  structTreeChecks ref oneFace arts
  pictureLayoutChecks ref oneFace
  pictureBoxChecks ref oneFace
  pictureBendChecks ref oneFace
  pictureInlineChecks ref oneFace
  pictureKeyNameChecks ref
  pictureWidthChecks ref oneFace
  pictureFontChecks ref oneFace
  pictureTextBoxChecks ref oneFace
  pictureAlignChecks ref oneFace
  pictureClosedPathChecks ref oneFace
  pictureOutlineChecks ref oneFace
  pictureNodeCentreChecks ref oneFace
  pictureOuterSepChecks ref oneFace
  boundaryUnfinishedChecks ref
  pictureHtmlFaceChecks ref
  pictureInlineLineChecks ref oneFace
  trivlistChecks ref oneFace
  listRhythmChecks ref oneFace
  vspaceKeptChecks ref oneFace
  fillCentreChecks ref oneFace
  faceCentreChecks ref oneFace
  vspaceStarChecks ref oneFace
  flushBottomChecks ref oneFace
  partopsepChecks ref oneFace
  listIndentChecks ref oneFace
  afterHeadingListChecks ref oneFace
  headingKeepChecks ref oneFace
  frameBodyChecks ref oneFace
  frameContentEndChecks ref oneFace
  footlineChecks ref
  topskipChecks ref oneFace
  labelBaselineChecks ref oneFace
  boundaryFitChecks ref oneFace
  frameSpecChecks ref oneFace
  boxArgChecks ref oneFace
  phantomChecks ref oneFace
  pictureDefnReachChecks ref oneFace
  pictureRouteChecks ref oneFace
  tikzInlineChecks ref oneFace
  pictureEveryLevelChecks ref oneFace
  pictureStyleHandlerChecks ref oneFace
  pictureNodePlaceChecks ref oneFace
  pictureNodeFloorChecks ref oneFace
  pictureNodeStyleChecks ref
  pictureSubpathChecks ref oneFace
  pictureInkBoxChecks ref oneFace
  pictureCondChecks ref oneFace
  pictureNodePrologueChecks ref oneFace
  pictureAnchorChecks ref oneFace
  nodeExtentChecks ref
  pictureLabelFaceChecks ref
  pictureKeyGateChecks ref oneFace
  pictureHyphenKeyChecks ref oneFace
  pictureMacroReachChecks ref oneFace
  pictureInnerSepChecks ref oneFace
  pictureAutoLabelChecks ref oneFace
  pictureGlobalKeyChecks ref oneFace
  condAccountingChecks ref oneFace
  picStateChecks ref oneFace
  ifxMeaningChecks ref oneFace
  macroUseChecks ref oneFace
  macroBindingChecks ref oneFace
  macroArgumentChecks ref oneFace
  packageOptionChecks ref oneFace
  picSiteChecks ref oneFace
  settleChecks ref
  quoteChecks ref oneFace
  kernelThmChecks ref
  kernelThmSpaceChecks ref oneFace
  kernelQedHereChecks ref
  kernelVerseChecks ref oneFace
  kernelDescChecks ref
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
  svgAssetChecks ref
  svgToolChecks ref oneFace
  animatedGraphicsChecks ref oneFace
  animatedFacesChecks ref oneFace
  pdfPageSelectionChecks ref
  pdfReadObjectsChecks ref
  rasterPageChecks ref oneFace
  imageRowChecks ref oneFace
  colorKeyChecks ref oneFace
  planChecks ref
  pdfFormChecks ref oneFace
  pdfCensusChecks ref oneFace
  pdfContractChecks ref oneFace arts
  objTableChecks ref oneFace
  featureCensusChecks ref oneFace
  pdfConformanceChecks ref oneFace arts
  artifactChecks ref oneFace pats
  kernPlacementChecks ref
  artBandParityChecks ref oneFace pats
  artGroundParityChecks ref oneFace pats
  artStageGroundChecks ref oneFace
  logOnlyChecks ref oneFace pats
  leafAttributionChecks ref oneFace pats
  inlineAttributionChecks ref oneFace pats
  loadedTestChecks ref oneFace
  packageCodeChecks ref oneFace
  xparseProvideChecks ref oneFace
  xparseIgnoredOperandsChecks ref oneFace
  overlaySetChecks ref oneFace
  frameHeadingScopeChecks ref oneFace
  nestedStageChecks ref oneFace arts
  refusedEnvChecks ref oneFace
  splitPairingOwedChecks ref
  groupPrimitiveChecks ref
  groupedBlockChecks ref oneFace
  reservedEnvNameChecks ref oneFace
  delimitedUseChecks ref oneFace
  delimitedSigChecks ref oneFace
  registerArithChecks ref oneFace
  composedLengthChecks ref
  endInputChecks ref oneFace
  abstractRedefChecks ref oneFace
  captionScopeChecks ref oneFace
  globalCaptionSkipChecks ref oneFace
  environChecks ref oneFace
  seamChecks ref oneFace
  abstractSkipChecks ref oneFace
  paramSiteChecks ref oneFace
  paramDemoteChecks ref oneFace
  sizeCommandChecks ref oneFace
  counterChecks ref oneFace
  listLevelChecks ref oneFace
  unreadableLengthChecks ref oneFace
  registerScopeChecks ref oneFace
  operandChecks ref oneFace
  listBodyChecks ref oneFace
  kernelLengthChecks ref oneFace
  natbibChecks ref oneFace
  natbibListChecks ref oneFace
  bibTextChecks ref oneFace
  plainnatChecks ref oneFace
  natbibLabelChecks ref oneFace
  nociteChecks ref oneFace
  citetextChecks ref oneFace
  nocitePlaceChecks ref oneFace
  natbibRowChecks ref oneFace
  natbibSortChecks ref oneFace
  biblatexChecks ref oneFace
  natbibCiteStyleChecks ref oneFace
  hspaceAffineChecks ref oneFace
  inlineRuleChecks ref oneFace
  fontSizeAffineChecks ref oneFace
  linkColorChecks ref oneFace

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
  mathAlphaGeometryChecks ref
  mathAlphaSemanticsChecks ref
  isolatedHoleChecks ref
  mathSymChecks ref
  textSymChecks ref
  inlineVerbChecks ref
  verbatimAmbientChecks ref
  ownBibChecks ref
  amsmathChecks ref
  bigDelimChecks ref
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
  compatAccountingChecks ref

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
  titleGroundChecks ref
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
  slotLossChecks ref
  artifactPitchChecks ref
  fontSuiteChecks ref

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let ref ← IO.mkRef ([] : List String)

  utf8Checks ref
  argsChecks ref
  renderChecks ref
  lexChecks ref
  braceEolChecks ref
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
  salvageChecks ref
  diagSiteCountChecks ref
  porcelainCensusChecks ref
  siteAccountingChecks ref
  diagAuditChecks ref
  reportChecks ref
  optionRunAccountingChecks ref
  visibleRunAccountingChecks ref
  monoSlotChecks ref
  structChecks ref
  ctxFoldChecks ref
  pictureAltChecks ref
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
  themeStyChecks ref
  themeSpellingChecks ref
  beamerColorChecks ref
  beamerFontChecks ref
  translationOwedChecks ref
  missingFileSpanChecks ref
  citeNoBibChecks ref
  surfaceSuiteChecks ref
  backendSuiteChecks ref
  themeSuiteChecks ref
  fontFaceSuiteChecks ref
  layoutSuiteChecks ref
  mdSurfaceChecks ref

  let failed := (← ref.get).reverse
  if failed.isEmpty then
    IO.println "tests: all passed"
    return 0
  else
    for name in failed do
      IO.eprintln s!"FAIL {name}"
    IO.eprintln s!"tests: {failed.length} failed"
    return 1
