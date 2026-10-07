import Tests.Support
import Tests.CliFoundationInterface
import Tests.DiagInterface
import Tests.LeafInterfaces
import Tests.MathInterface
import Tests.ImageInterface
import Tests.InkInterface
import Tests.FontInterface
import Tests.FontDiscoveryInterface
import Tests.FontSubsetInterface
import Tests.GlyphBoundsInterface
import Tests.IrInterface
import Tests.MathParseInterface
import Tests.MdParseInterface
import Tests.PictureInterface
import Tests.ParseInterface
import Tests.DataInterface
import Tests.TcolorboxInterface
import Tests.PdfReaderInterface
import Tests.PdfBoundaryInterface
import Tests.Batch
import Tests.CacheInterface
import Tests.Compression
import Tests.BrowserFaceBatch
import Tests.CacheIO
import Tests.PictureAssets
import Tests.ToolMemo
import Tests.Surface
import Tests.ElabContracts
import Tests.FrontendContracts
import Tests.FrontendInputContracts
import Tests.FrontendPictureContracts
import Tests.FrontendControlContracts
import Tests.ElabFrameSources
import Tests.LayoutSources
import Tests.ElementSpacing
import Tests.ContrastContracts
import Tests.FlateInterface
import Tests.FontSize
import Tests.FontSelection
import Tests.CancelRegression
import Tests.CancelHtml
import Tests.CancelAlignment
import Tests.CancelMetric
import Tests.CancelContext
import Tests.CancelReview
import Tests.BeamerHooks
import Tests.BeamerColors
import Tests.BeamerTemplates
import Tests.ListDeclarations
import Tests.Tcolorbox
import Tests.TcolorboxColors
import Tests.BlockBar
import Tests.MintedSettings
import Tests.ListingHighlight
import Tests.ListingProvider
import Tests.PublicationPaths
import Tests.Markdown
import Tests.MarkdownInput
import Tests.InputUse
import Tests.XparseProvide
import Tests.XparseIgnoredOperands
import Tests.OverlaySets
import Tests.OverlayStyles
import Tests.OverlayContracts
import Tests.OverlayInputs
import Tests.OverlaySingleton
import Tests.OverlaySingletonHtml
import Tests.FrameHeadingScope
import Tests.Census
import Tests.Backends
import Tests.Images
import Tests.ImageCodec
import Tests.SvgImages
import Tests.SvgTools
import Tests.AnimatedGraphics
import Tests.AnimatedFaces
import Tests.PdfPageSelection
import Tests.PdfReadObjects
import Tests.PdfReadRoundtrip
import Tests.PdfReadRepresentability
import Tests.PdfEncoding
import Tests.PdfBounds
import Tests.PdfFontsProof
import Tests.RasterPages
import Tests.Diag
import Tests.DiagnosticFormat
import Tests.DiagnosticTrigger
import Tests.DiagnosticImageOrigins
import Tests.DiagnosticFontScope
import Tests.DiagnosticOrigins
import Tests.SourceAnnotations
import Tests.InputOrigins
import Tests.ImageOrigins
import Tests.Themes
import Tests.SeedPalette
import Tests.SlideLabels
import Tests.FontMath
import Tests.FormulaFloor
import Tests.MathAlphaGeometry
import Tests.MathAlphaSemantics
import Tests.MathAlphaEntry
import Tests.Struct
import Tests.PdfConformance
import Tests.PdfWriter
import Tests.PdfStructCoherence
import Tests.Artifact
import Tests.UnderlineSpacing
import Tests.CompatGate
import Tests.CompatExecution
import Tests.HtmlTokens
import Tests.HtmlContained
import Tests.HtmlA11y
import Tests.Conditionals
import Tests.StringConditionals
import Tests.MacroBinding
import Tests.MacroArguments
import Tests.MacroDefaults
import Tests.MacroRoles
import Tests.MacroAccent
import Tests.MacroForwarding
import Tests.RoleShaping
import Tests.MacroHookScope
import Tests.MacroDelimiterScope
import Tests.PackageOptions
import Tests.BoxRow
import Tests.RecipeStructure
import Tests.PdfDestination
import Tests.TableContext
import Tests.TableFlex
import Tests.ColumnFlow
import Tests.ColumnGeometry
import Tests.TitlePageLifecycle
import Tests.LinkMacroLayout
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
import Tests.PictureBoundary
import Tests.FontDefaults
import Tests.PictureContracts
import Tests.PictureKeys
import Tests.PictureLabelSpacing
import Tests.PictureHtmlBaseline
import Tests.PictureMathLabels
import Tests.TextSym
import Tests.InlineVerb
import Tests.VerbatimAmbient
import Tests.OwnBib
import Tests.BigDelim
import Tests.Regress
import Tests.RegressionCorpus
import Tests.Reports
import Tests.Natbib
import Tests.LinkColor

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open Tests (mintedSettingsChecks listingHighlightChecks svgAssetChecks svgToolChecks
  shellReplyChecks listingProviderChecks publicationPathChecks
  htmlContainedChecks htmlContainedPublicationChecks htmlContainedSvgColorChecks
  htmlContainedCliChecks htmlContainedCorpusChecks
  animatedGraphicsChecks animatedFacesChecks markdownInputChecks xparseProvideChecks
  xparseIgnoredOperandsChecks macroBindingChecks macroArgumentChecks macroDefaultChecks macroPhaseChecks
  macroRoleChecks macroAccentChecks macroForwardingChecks roleShapingChecks
  macroHookScopeChecks macroDelimiterScopeChecks packageOptionChecks
  overlaySetChecks overlayStyleChecks overlayContractChecks overlayInputChecks overlaySingletonHtmlChecks
  diagnosticFormatChecks diagnosticTriggerChecks diagnosticImageOriginChecks diagnosticFontScopeChecks diagnosticOriginChecks sourceAnnotationChecks inputOriginsChecks imageOriginsChecks
  mathAlphaSemanticsChecks tableContextChecks linkMacroLayoutChecks
  inputUseChecks mathAlphaEntryChecks listDeclarationChecks stringConditionalChecks)
open TcolorboxChecks (tcolorboxChecks tcolorboxSourceChecks)
open TcolorboxColors (tcolorboxColorChecks)
open PictureBoundary (pictureBoundaryChecks)
open Tests (fontDefaultsChecks fontDefaultsOverrideChecks blockBarChecks batchChecks)

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
  shellReplyChecks ref
  listingProviderChecks ref
  mdPreambleChecks ref
  markdownInputChecks ref
  inputUseChecks ref
  backendChecks ref
  pictureBoundaryChecks ref
  fontDefaultsChecks ref
  fontDefaultsOverrideChecks ref
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
  htmlContainedPublicationChecks ref
  htmlContainedSvgColorChecks ref
  htmlContainedCliChecks ref
  htmlContainedCorpusChecks ref
  publicationPathChecks ref
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
  layoutSourceChecks ref oneFace
  for (name, ok) in LeanTex.Tests.LayoutContracts.ownershipChecks oneFace do
    check ref s!"layout ownership: {name}" ok
  for (name, ok) in LeanTex.Tests.LayoutContracts.attributionChecks oneFace do
    check ref s!"layout attribution: {name}" ok
  for (name, ok) in LeanTex.Tests.LayoutContracts.reflowChecks oneFace do
    check ref s!"layout reflow: {name}" ok
  for (name, ok) in LeanTex.Tests.LayoutContracts.footerChecks oneFace do
    check ref s!"layout footer: {name}" ok
  for (name, ok) in LeanTex.Tests.LayoutContracts.partitionChecks oneFace do
    check ref s!"layout partition: {name}" ok
  for (name, ok) in LeanTex.Tests.ElementSpacing.elementSpacingChecks oneFace do
    check ref s!"element spacing: {name}" ok
  htmlContainedChecks ref oneFace
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
  beamerTemplateChecks ref oneFace
  listDeclarationChecks ref oneFace
  tcolorboxChecks ref oneFace
  tcolorboxSourceChecks ref oneFace
  tcolorboxColorChecks ref oneFace
  blockBarChecks ref oneFace
  stringConditionalChecks ref oneFace
  seedPaletteChecks ref oneFace
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
  linkMacroLayoutChecks ref oneFace
  pdfDestinationChecks ref oneFace
  recipeParacolChecks ref oneFace
  recipeTabularxChecks ref oneFace
  recipeTabularxSharesChecks ref
  recipeColModChecks ref
  tableContextChecks ref oneFace
  tableFlexChecks ref oneFace
  tableFlexOverflowChecks ref oneFace
  columnFlowChecks ref oneFace
  columnGeometryChecks ref oneFace
  recipeTitlePageChecks ref oneFace
  titlePageLifecycleChecks ref oneFace
  recipeUlemChecks ref oneFace
  recipeLinkAffordChecks ref oneFace
  boxPosRowChecks ref oneFace
  underlineChecks ref geom oneFace font
  underlineSpacingChecks ref oneFace
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
  Tests.formulaFloorChecks ref oneFace
  mathContainChecks ref oneFace
  cancelReportChecks ref oneFace
  cancelGeometryChecks ref oneFace
  cancelBoxChecks ref oneFace
  cancelHtmlChecks ref
  CancelAlignment.checks ref oneFace
  CancelMetric.checks ref oneFace
  CancelContext.checks ref
  CancelReview.checks ref oneFace
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
  PictureContracts.provenanceRenderChecks ref oneFace
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
  PictureLabelSpacing.checks ref oneFace
  pictureHtmlBaselineChecks ref oneFace
  pictureMathLabelChecks ref oneFace
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
  macroLengthExecutionChecks ref oneFace
  macroBindingChecks ref oneFace
  macroArgumentChecks ref oneFace
  macroDefaultChecks ref oneFace
  macroRoleChecks ref oneFace
  macroAccentChecks ref oneFace
  macroForwardingChecks ref oneFace
  roleShapingChecks ref oneFace
  macroPhaseChecks ref oneFace
  macroHookScopeChecks ref oneFace
  macroDelimiterScopeChecks ref oneFace
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
  slideLabelChecks ref oneFace
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
  imageCodecChecks ref
  pdfFormChecks ref oneFace
  pdfCensusChecks ref oneFace
  pdfWriterChecks ref oneFace
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
  overlayStyleChecks ref oneFace
  overlayContractChecks ref oneFace
  overlayInputChecks ref oneFace
  overlaySingletonChecks ref oneFace
  overlaySingletonHtmlChecks ref
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
  mathAlphaEntryChecks ref
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
  batchChecks ref
  Tests.compressionChecks ref
  Tests.browserFaceBatchChecks ref
  Tests.cacheIdentityChecks ref
  Tests.pictureAssetsChecks ref
  Tests.toolMemoChecks ref
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
  contrastContractChecks ref
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
  diagnosticFormatChecks ref
  diagnosticTriggerChecks ref
  diagnosticImageOriginChecks ref
  diagnosticFontScopeChecks ref
  diagnosticOriginChecks ref
  sourceAnnotationChecks ref
  inputOriginsChecks ref
  imageOriginsChecks ref
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
  Tests.regressionDocumentChecks ref
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
  elabWarningContractChecks ref
  elabTitleBoundaryChecks ref
  frontendTitleContextChecks ref
  frontendInputRequestChecks ref
  frontendPictureCompositionChecks ref
  frontendControlContractChecks ref
  elabUnknownDispatchChecks ref
  elabFrameSourceChecks ref
  porcelainCensusChecks ref
  siteAccountingChecks ref
  diagAuditChecks ref
  reportChecks ref
  optionRunAccountingChecks ref
  visibleRunAccountingChecks ref
  monoSlotChecks ref
  structChecks ref
  pdfStructCoherenceChecks ref
  pdfReadRoundtripChecks ref
  pdfReadRepresentabilityChecks ref
  pdfEncodingChecks ref
  pdfBoundsChecks ref
  pdfFontsProofChecks ref
  for (name, okay) in Tests.PdfReaderInterface.checks do
    check ref ("PDF reader interface: " ++ name) okay
  ctxFoldChecks ref
  pictureAltChecks ref
  pictureElabChecks ref
  PictureContracts.checks ref
  diagVoiceChecks ref update
  allowChecks ref
  werrorChecks ref
  declChecks ref
  tokensChecks ref
  compatChecks ref
  compatExecutionChecks ref
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
