import Tests.HtmlInterface
import Tests.CompatInterface
import Tests.ElabInterface
import Tests.SlotLossInterface
import Tests.InputInterface
import Tests.CliDriverInterface
import Tests.FrontendContractInterface
import Tests.UmbrellaInterface
import Tests.LayoutContractInterface
import Tests.PdfInterfaces
import Tests.DocumentContractInterfaces
import Tests.ColourInterface
import Tests.ContrastInterface
import Tests.PresentationInterfaces
import Tests.Support
import Tests.BuildGraph
import Tests.JsonParity
import Tests.SplitParity
import Tests.CliFoundationInterface
import Tests.BoundaryInterface
import Tests.DriverDiagInterface
import Tests.ListingHighlightInterface
import Tests.PublicationInterface
import Tests.DiagInterface
import Tests.LeafInterfaces
import Tests.MathInterface
import Tests.ImageInterface
import Tests.BibPendingInterface
import Tests.InkInterface
import Tests.FontInterface
import Tests.FontDiscoveryInterface
import Tests.FontPipelineInterface
import Tests.StructureInterface
import Tests.FontSubsetInterface
import Tests.GlyphBoundsInterface
import Tests.LayoutInterface
import Tests.IrInterface
import Tests.MathParseInterface
import Tests.MdParseInterface
import Tests.PictureInterface
import Tests.TitleTemplateInterface
import Tests.TitleTemplateScan
import Tests.ParseInterface
import Tests.DataInterface
import Tests.TcolorboxInterface
import Tests.PdfReaderInterface
import Tests.PdfCensusInterface
import Tests.PdfBoundaryInterface
import Tests.Batch
import Tests.CacheInterface
import Tests.PictureAssetsInterface
import Tests.ImageAssetsInterface
import Tests.Compression
import Tests.EngineCache
import Tests.BrowserFaceBatch
import Tests.CacheIO
import Tests.KeyVal
import Tests.PictureAssets
import Tests.ToolMemo
import Tests.World
import Tests.OracleWaits
import Tests.TexFontTrees
import Tests.Surface
import Tests.ElabContracts
import Tests.FrontendContracts
import Tests.FrontendInputContracts
import Tests.FrontendPictureContracts
import Tests.FrontendControlContracts
import Tests.ElabFrameSources
import Tests.LayoutSources
import Tests.LayoutTextConservation
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
import Tests.BeamerColorOrigins
import Tests.BeamerTemplates
import Tests.ListDeclarations
import Tests.Tcolorbox
import Tests.TcolorboxColors
import Tests.BlockBar
import Tests.ReadableBar
import Tests.ColorNames
import Tests.PaletteData
import Tests.PaletteDefaults
import Tests.Schemes
import Tests.SpotColor
import Tests.PageBoxes
import Tests.PrintX4
import Tests.Icc
import Tests.PrintColour
import Tests.ItemLabels
import Tests.WebMeasure
import Tests.MarginNote
import Tests.LabelLines
import Tests.ListGaps
import Tests.ListLabels
import Tests.ItemBoxes
import Tests.Tabbing
import Tests.ScrExtend
import Tests.ItemRefs
import Tests.DeclaredColors
import Tests.BlockBody
import Tests.BlockRegionFit
import Tests.BlockHeaderClearance
import Tests.BlockGeometry
import Tests.FrameArea
import Tests.BlockSkips
import Tests.BlockTemplate
import Tests.ElementBoundaries
import Tests.FrameGeometry
import Tests.FrameFit
import Tests.NestedLedgers
import Tests.DeclaredLadder
import Tests.FlowClass
import Tests.PageOverrun
import Tests.PageTurns
import Tests.BlockFillConditionals
import Tests.PaletteTextEpoch
import Tests.GroupScope
import Tests.MintedSettings
import Tests.ListingHighlight
import Tests.ListingStyleTable
import Tests.ListingProvider
import Tests.PygmentsLexers
import Tests.PublicationPaths
import Tests.Markdown
import Tests.MarkdownHtml
import Tests.MarkdownHeadings
import Tests.MarkdownTables
import Tests.MarkdownPage
import Tests.ClassArea
import Tests.MarkdownWarnings
import Tests.MonoDefault
import Tests.MarkdownCode
import Tests.CodeDoc
import Tests.LeanStatements
import Tests.LeanViews
import Tests.LeanProse
import Tests.LeanProseReading
import Tests.Blueprint
import Tests.MarkdownInput
import Tests.MarkdownDoors
import Tests.MarkdownTwin
import Tests.MarkdownCite
import Tests.LeanCite
import Tests.BibEdges
import Tests.DocCiteEdges
import Tests.MdNoteEdges
import Tests.MdCiteEdges
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
import Tests.SectionPages
import Tests.Contents
import Tests.Census
import Tests.GfxRegression
import Tests.GfxMatrix
import Tests.PdfFigures
import Tests.PdfNative
import Tests.GfxPaint
import Tests.Backends
import Tests.MetaEscape
import Tests.Images
import Tests.ImageCodec
import Tests.SvgImages
import Tests.SvgTools
import Tests.SvgNative
import Tests.SvgRoute
import Tests.SvgHtml
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
import Tests.DiagDeletion
import Tests.DiagFold
import Tests.DiagnosticFormat
import Tests.RunCost
import Tests.DiagnosticTrigger
import Tests.DiagnosticImageOrigins
import Tests.DiagnosticFontScope
import Tests.DiagnosticOrigins
import Tests.DiagnosticContrastOrigins
import Tests.DiagnosticLayoutOrigins
import Tests.DiagnosticLiteralOrigins
import Tests.DiagnosticListingOrigins
import Tests.DiagnosticProducerOrigins
import Tests.SourceAnnotations
import Tests.InputOrigins
import Tests.InputDecoding
import Tests.ImageOrigins
import Tests.Themes
import Tests.SeedPalette
import Tests.SeedSeries
import Tests.PaletteFloor
import Tests.PaletteCover
import Tests.CoveredSteps
import Tests.AlertMark
import Tests.ColourSolve
import Tests.ThemePalette
import Tests.ThemeCss
import Tests.SlideLabels
import Tests.SlidesBench
import Tests.FontMath
import Tests.FormulaFloor
import Tests.MathAlphaGeometry
import Tests.MathAlphaSemantics
import Tests.MathAlphaEntry
import Tests.MathDiagnosticOrigins
import Tests.MathDelimiterTriggers
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
import Tests.HtmlRead
import Tests.PdfTextRead
import Tests.MachineLoss
import Tests.HtmlA11y
import Tests.Conditionals
import Tests.StringConditionals
import Tests.FlagCommands
import Tests.InlineBoxes
import Tests.EnvCode
import Tests.Chapters
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
import Tests.InertProbes
import Tests.BoxRow
import Tests.RecipeStructure
import Tests.PdfDestination
import Tests.TableContext
import Tests.TableFlex
import Tests.TableSide
import Tests.FrameAnchors
import Tests.ColumnFlow
import Tests.ColumnGeometry
import Tests.TitlePageLifecycle
import Tests.LinkMacroLayout
import Tests.PackageCode
import Tests.PackageImports
import Tests.ParagraphMathRhythm
import Tests.LineRhythm
import Tests.BeamerProof
import Tests.DiagAudit
import Tests.MathSym
import Tests.AmsMath
import Tests.Refusal
import Tests.EndInput
import Tests.Redefine
import Tests.Algorithm
import Tests.ParamCensus
import Tests.ParamCensusDecl
import Tests.ParamCensusCli
import Tests.DeclSettings
import Tests.UnusedSettings
import Tests.ListsKoma
import Tests.Settings
import Tests.Kernel
import Tests.PicturePaths
import Tests.PicturePathSyntax
import Tests.PictureShrink
import Tests.PictureBoundary
import Tests.FontDefaults
import Tests.PictureContracts
import Tests.PictureKeys
import Tests.TikzCd
import Tests.TikzCoverage
import Tests.BoundaryFaces
import Tests.GraphicsPath
import Tests.TikzLongTail
import Tests.TikzShapes
import Tests.TikzTips
import Tests.TikzCdNative
import Tests.PictureLabelSpacing
import Tests.PictureHtmlBaseline
import Tests.PictureMathLabels
import Tests.TextSym
import Tests.InlineVerb
import Tests.InlineCode
import Tests.VerbatimAmbient
import Tests.OwnBib
import Tests.BigDelim
import Tests.Regress
import Tests.RegressionCorpus
import Tests.Reports
import Tests.Premises
import Tests.Natbib
import Tests.BibModel
import Tests.LinkColor
import Tests.Privacy

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open Tests (mintedSettingsChecks listingHighlightChecks pygmentsLexerChecks pygmentsDataChecks
  pygmentsLinearChecks
  svgAssetChecks svgToolChecks
  shellReplyChecks shellHighlightChecks listingProviderChecks listingStyleTableChecks codeRoleChecks codeExportChecks
  seededCodeChecks definitionNameChecks hashCommandChecks
  publicationPathChecks
  htmlContainedChecks htmlContainedPublicationChecks htmlContainedSvgColorChecks
  htmlContainedCliChecks htmlContainedCorpusChecks
  animatedGraphicsChecks animatedFacesChecks markdownInputChecks markdownInputHtmlChecks
  disclosurePrintChecks
  xparseProvideChecks
  xparseIgnoredOperandsChecks macroBindingChecks macroArgumentChecks macroDefaultChecks macroPhaseChecks
  macroRoleChecks macroAccentChecks macroForwardingChecks roleShapingChecks
  macroHookScopeChecks macroDelimiterScopeChecks packageOptionChecks
  overlaySetChecks overlayOnlyChecks overlayVisibleChecks overlayStyleChecks overlayContractChecks
  overlayInputChecks
  overlaySingletonHtmlChecks
  diagnosticFormatChecks diagnosticTriggerChecks diagnosticImageOriginChecks diagnosticFontScopeChecks diagnosticOriginChecks diagnosticContrastOriginChecks sourceAnnotationChecks inputOriginsChecks imageOriginsChecks
  mathAlphaSemanticsChecks tableContextChecks linkMacroLayoutChecks
  inputUseChecks mathAlphaEntryChecks mathDiagnosticOriginChecks mathDelimiterTriggerChecks
  mathDollarSurfaceChecks
  diagnosticProducerOriginChecks diagnosticAggregationOriginChecks diagnosticPipelineOriginChecks
  listDeclarationChecks stringConditionalChecks)
open TcolorboxChecks (tcolorboxChecks tcolorboxSourceChecks)
open TcolorboxColors (tcolorboxColorChecks)
open PictureBoundary (pictureBoundaryChecks pictureWrapperChecks pictureShipChecks)
open Tests (fontDefaultsChecks fontDefaultsOverrideChecks weightSubstitutionRecordChecks
  blockBarChecks batchChecks)

/-- The backend check blocks, dispatched together after `compatChecks`. -/
def backendSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  footnoteBackendChecks ref
  styleChecks ref
  htmlLayoutChecks ref
  htmlRhythmChecks ref
  Tests.LineRhythm.htmlStepChecks ref
  Tests.LineRhythm.htmlGapChecks ref
  htmlListGapChecks ref
  htmlListSpacingChecks ref
  htmlSectionGapChecks ref
  printLiftChecks ref
  classHookChecks ref
  runinChecks ref
  abstractChecks ref
  headingNumberChecks ref
  argTokenChecks ref
  anchorChecks ref
  markdownChecks ref
  markdownHtmlChecks ref
  mdHtmlAccountsChecks ref
  htmlTwinChecks ref
  refusedDisclosureChecks ref
  cellBreakChecks ref
  mdRawHtmlHelpChecks ref
  mdTwinBreakChecks ref
  breakRunAgreeChecks ref
  disclosurePrintChecks ref
  markdownHeadingChecks ref
  Tests.MarkdownTables.markdownTableChecks ref
  Tests.MarkdownPage.markdownPageChecks ref
  Tests.ClassArea.classAreaChecks ref
  Tests.MarkdownWarnings.markdownWarningChecks ref
  Tests.MarkdownWarnings.markdownMonoChecks ref
  Tests.MonoDefault.monoDefaultChecks ref
  Tests.MonoDefault.companionDepartureChecks ref
  Tests.MonoDefault.faceKeyAgreementChecks ref
  Tests.MonoDefault.fontCollectionChecks ref
  Tests.MarkdownCode.markdownCodeChecks ref
  Tests.MarkdownCode.htmlCodeAtomChecks ref
  Tests.CodeDoc.codeDocChecks ref
  Tests.CodeDoc.docMarkupChecks ref
  Tests.LeanStatements.leanStatementChecks ref
  Tests.LeanViews.leanViewChecks ref
  Tests.LeanProse.leanProseChecks ref
  Tests.LeanProseReading.readingChecks ref
  Tests.Blueprint.blueprintChecks ref
  algorithmBackendChecks ref
  listingLanguageChecks ref
  mintedSettingsChecks ref
  listingHighlightChecks ref
  pygmentsLexerChecks ref
  pygmentsDataChecks ref
  pygmentsLinearChecks ref
  shellReplyChecks ref
  shellHighlightChecks ref
  jsonParityChecks ref
  splitParityChecks ref
  listingProviderChecks ref
  listingStyleTableChecks ref
  hashCommandChecks ref
  codeRoleChecks ref
  seededCodeChecks ref
  codeExportChecks ref
  definitionNameChecks ref
  mdPreambleChecks ref
  markdownInputChecks ref
  Tests.MarkdownDoors.markdownDoorChecks ref
  Tests.MarkdownDoors.markdownDoorDriverChecks ref
  Tests.MarkdownDoors.markdownHybridChecks ref
  Tests.MarkdownTwin.markdownTwinChecks ref
  Tests.MarkdownCite.mdCiteChecks ref
  Tests.MarkdownCite.mdMetadataChecks ref
  Tests.LeanCite.leanCiteChecks ref
  Tests.LeanCite.citeFootnoteChecks ref
  Tests.BibEdges.quoteChecks ref
  Tests.BibEdges.duplicateChecks ref
  Tests.BibEdges.alphaChecks ref
  Tests.BibEdges.missingChecks ref
  Tests.BibEdges.siteChecks ref
  Tests.BibEdges.encodingKeyChecks ref
  Tests.DocCiteEdges.documentChecks ref
  Tests.DocCiteEdges.docstringChecks ref
  Tests.DocCiteEdges.caseChecks ref
  Tests.DocCiteEdges.mathChecks ref
  Tests.DocCiteEdges.flankChecks ref
  Tests.DocCiteEdges.caseFoldChecks ref
  Tests.MdNoteEdges.altChecks ref
  Tests.MdNoteEdges.noteChecks ref
  Tests.MdNoteEdges.noteTwinChecks ref
  Tests.MdNoteEdges.inlineNoteChecks ref
  Tests.MdNoteEdges.citeNoteChecks ref
  Tests.MdNoteEdges.citeNoteEdgeChecks ref
  Tests.MdNoteEdges.captionAltChecks ref
  Tests.MdCiteEdges.keyDigitChecks ref
  Tests.MdCiteEdges.everyEntryChecks ref
  Tests.MdCiteEdges.bracketTailChecks ref
  Tests.MdCiteEdges.breakTailChecks ref
  Tests.MdCiteEdges.listTitleChecks ref
  Tests.MdCiteEdges.abbrevChecks ref
  Tests.MdCiteEdges.abbrevEdgeChecks ref
  Tests.MdCiteEdges.escapedSpaceChecks ref
  Tests.MdCiteEdges.twinChecks ref
  Tests.LeanCite.selfDocChecks ref
  markdownInputHtmlChecks ref
  inputUseChecks ref
  backendChecks ref
  pictureBoundaryChecks ref
  pictureWrapperChecks ref
  fontDefaultsChecks ref
  fontDefaultsOverrideChecks ref
  weightSubstitutionRecordChecks ref
  landmarkChecks ref
  pinChecks ref
  mdNameChecks ref
  interactionChecks ref
  motionSiteChecks ref
  fontShipChecks ref
  faceUseChecks ref
  deckCssChecks ref
  deckImageChecks ref
  alphaSplitChecks ref
  deckStructureChecks ref
  deckProgressChecks ref
  mathmlChecks ref
  mathLineChecks ref
  linkHtmlChecks ref
  tableHtmlChecks ref
  contentOpsChecks ref
  gfxMatrixChecks ref
  gfxGradientFrameChecks ref
  gfxIdChecks ref
  gfxStampChecks ref
  gfxKitChecks ref
  Tests.svgNativeChecks ref
  pdfFiguresChecks ref
  pdfContentLexChecks ref
  glyphListChecks ref
  pdfFontChecks ref
  pdfInterpreterChecks ref
  pdfOptionalContentChecks ref
  pdfNestingChecks ref
  pdfTransformChainChecks ref
  pdfStateChecks ref
  pdfStreamLossChecks ref
  inflateZlibChecks ref
  figureRouteChecks ref
  converterDoorChecks ref
  nativeFaceClosedChecks ref
  pdfFixtureChecks ref
  pngEncodeChecks ref
  outputContractChecks ref
  htmlAssetChecks ref
  htmlContainedPublicationChecks ref
  htmlContainedSvgColorChecks ref
  htmlContainedCliChecks ref
  Tests.mathBoundaryChecks ref
  Tests.bulmaSheetChecks ref
  Tests.machineLossChecks ref
  htmlContainedCorpusChecks ref
  Tests.htmlReadChecks ref
  publicationPathChecks ref
  Tests.publicationWriteChecks ref
  Tests.overwritePlanChecks ref
  Tests.publicationInputChecks ref
  Tests.outputNameChecks ref
  anchorIdChecks ref
  htmlTokenClosureChecks ref
  htmlRoleClosureChecks ref
  htmlSourcedGapChecks ref
  htmlInternalTokenChecks ref
  htmlA11yChecks ref
  pageTitleChecks ref
  htmlMathChecks ref

/-- The declaration settings' census and reader blocks, dispatched together so `layoutSuiteChecks`
stays within its elaboration budget. -/
def declSettingSuiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) (font : Font) :
    IO Unit := do
  texEdgeChecks ref oneFace
  texStateChecks ref oneFace
  Tests.ParamCensus.bodyParskipChecks ref oneFace
  Tests.ParamCensus.declCensusChecks ref oneFace
  Tests.ParamCensus.builtCensusChecks ref
  Tests.ParamCensus.declaredScopeChecks ref
  Tests.UnusedSettings.firesChecks ref
  Tests.UnusedSettings.scopeChecks ref
  Tests.UnusedSettings.accountingChecks ref
  Tests.UnusedSettings.redefinitionChecks ref
  Tests.UnusedSettings.oracleChecks ref oneFace
  Tests.UnusedSettings.faceChecks ref
  Tests.UnusedSettings.metadataChecks ref
  Tests.DeclSettings.setlistChecks ref oneFace font
  Tests.DeclSettings.styleFontChecks ref oneFace
  Tests.DeclSettings.markerScopeChecks ref
  Tests.DeclSettings.listSpacingChecks ref oneFace
  Tests.DeclSettings.listSpacingStyleChecks ref oneFace
  Tests.ListsKoma.komaListChecks ref oneFace
  Tests.ListsKoma.quoteKindChecks ref oneFace
  Tests.ListsKoma.quoteBoundaryChecks ref oneFace
  Tests.ListsKoma.quoteKindHtmlChecks ref
  Tests.ListsKoma.labelChecks ref oneFace
  Tests.ListsKoma.exChecks ref oneFace
  Tests.DeclSettings.frameTitleKeyChecks ref oneFace
  Tests.DeclSettings.emptyTemplateChecks ref oneFace
  Tests.DeclSettings.emptyTemplateMeasuredChecks ref
  Tests.DeclSettings.defaultTemplateChecks ref oneFace
  Tests.DeclSettings.counterReadChecks ref
  Tests.DeclSettings.titlePageChecks ref oneFace
  Tests.DeclSettings.inlineDisplayChecks ref
  Tests.ItemLabels.checks ref oneFace
  Tests.ItemLabels.openerChecks ref oneFace
  Tests.WebMeasure.checks ref
  Tests.WebMeasure.paperLossChecks ref oneFace
  Tests.MarginNote.checks ref oneFace
  Tests.LabelLines.checks ref oneFace
  Tests.ListGaps.checks ref oneFace
  Tests.ListLabels.checks ref oneFace
  Tests.ItemBoxes.checks ref oneFace
  Tests.Tabbing.checks ref oneFace
  Tests.ScrExtend.checks ref oneFace
  Tests.ItemRefs.checks ref
  Tests.ItemLabels.cellChecks ref oneFace
  Tests.ItemLabels.itemSpaceChecks ref oneFace
  nativeCarrierChecks ref oneFace

/-- Print colour: inks, page boxes, the PDF/X-4 claim, the output profile's transforms, and what a
document declaring one shows and prints. -/
def printColourChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  Tests.SpotColor.checks ref oneFace
  Tests.PageBoxes.checks ref oneFace
  Tests.PrintX4.checks ref oneFace
  Tests.Icc.checks ref
  Tests.PrintColour.checks ref oneFace
  Tests.PrintColour.previewChecks ref oneFace
  Tests.PrintColour.driverChecks ref

/-- The page blocks: what overruns a page, and where a flow's pages turn. -/
def pageSuiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  Tests.PageOverrun.checks ref oneFace
  Tests.PageTurns.checks ref oneFace

/-- The table blocks: a cell's side, leading, lengths, strut and column widths. -/
def tableSuiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  Tests.tableSideChecks ref oneFace
  Tests.tableRaggedChecks ref oneFace
  Tests.tableLeadingChecks ref oneFace
  Tests.tableLengthChecks ref oneFace
  Tests.tableStrutChecks ref oneFace
  Tests.tableDimexprChecks ref oneFace
  Tests.tableFaceOrderChecks ref oneFace

/-- The section blocks: a deck's section pages and both models' tables of contents. -/
def sectionSuiteChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  sectionPageChecks ref oneFace
  contentsChecks ref oneFace
  contentsEdgeChecks ref oneFace
  contentsEdgeChecks2 ref oneFace
  contentsGapChecks ref oneFace
  contentsDeckChecks ref oneFace
  frameCountChecks ref oneFace
  footlineTemplateChecks ref oneFace
  chapterContentsChecks ref oneFace

/-- The layout, census, theme and chrome blocks over the shipped face; a missing or unparsable font
only skips them, `fontSuiteChecks` reporting it. -/
def layoutSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  let pats := Hyphen.english.get
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let oneFace := oneFaceOf font
  layoutSourceChecks ref oneFace
  pdfReadbackChecks ref oneFace
  diagnosticLayoutOriginChecks ref oneFace
  Tests.diagnosticLiteralOriginChecks ref oneFace
  Tests.diagnosticListingOriginChecks ref
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
  for (name, ok) in LeanTex.Tests.LayoutTextConservation.textConservationChecks oneFace do
    check ref s!"layout text conservation: {name}" ok
  for (name, ok) in LeanTex.Tests.ElementSpacing.elementSpacingChecks oneFace do
    check ref s!"element spacing: {name}" ok
  htmlContainedChecks ref oneFace
  let geom : Layout.Geom := {}
  let arts ← goldenArts oneFace
  pdfFaceChecks ref geom oneFace font
  webMetaChecks ref geom oneFace
  Tests.MetaEscape.metaEscapeChecks ref geom oneFace
  Tests.MetaEscape.templateArgChecks ref geom oneFace
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
  Tests.ReadableBar.checks ref oneFace
  Tests.ColorNames.checks ref oneFace
  Tests.PaletteData.checks ref
  Tests.PaletteDefaults.checks ref oneFace
  Tests.PaletteDefaults.yieldChecks ref
  Tests.PaletteDefaults.reseedChecks ref
  Tests.Schemes.checks ref
  Tests.Schemes.dropChecks ref
  Tests.Schemes.darkListingChecks ref
  Tests.Schemes.printChecks ref oneFace
  Tests.Schemes.forcedColorChecks ref
  Tests.Schemes.darkTextChecks ref
  Tests.Schemes.subsetChecks ref
  Tests.Schemes.plateChecks ref
  Tests.Schemes.literalChecks ref
  Tests.Schemes.contractChecks ref
  Tests.ColorNames.xcolorCodeRoleChecks ref oneFace
  Tests.ColorNames.htmlDecimalChecks ref oneFace
  Tests.ColorNames.unreadKeyChecks ref
  Tests.ColorNames.missingBothWaysChecks ref
  Tests.ColorNames.unreadKeyFlipChecks ref oneFace
  Tests.DeclaredColors.checks ref oneFace
  Tests.DeclaredColors.listingGroundChecks ref oneFace
  Tests.DeclaredColors.focusGateChecks ref
  Tests.DeclaredColors.stageFocusChecks ref
  Tests.BlockBody.checks ref oneFace
  Tests.BlockRegionFit.checks ref oneFace
  Tests.BlockHeaderClearance.checks ref oneFace
  Tests.BlockGeometry.blockGeometryChecks ref oneFace
  Tests.BlockSkips.blockSkipChecks ref oneFace
  Tests.BlockTemplate.checks ref oneFace
  Tests.ElementBoundaries.elementBoundaryChecks ref oneFace
  Tests.BlockFillConditionals.blockFillConditionalChecks ref oneFace
  Tests.PaletteTextEpoch.paletteTextEpochChecks ref oneFace
  Tests.GroupScope.groupScopeChecks ref oneFace
  Tests.ThemeCss.epochChecks ref oneFace
  stringConditionalChecks ref oneFace
  Tests.SeedPalette.tripleChecks ref
  Tests.SeedPalette.amberChecks ref
  Tests.SeedPalette.oklchChecks ref
  Tests.SeedPalette.deckChecks ref oneFace
  Tests.SeedPalette.exportChecks ref oneFace
  Tests.SeedPalette.seedRoleChecks ref oneFace
  Tests.SeedPalette.failureChecks ref
  Tests.SeedPalette.scriptChecks ref
  Tests.SeedSeries.seriesChecks ref
  Tests.SeedSeries.seriesScriptChecks ref
  Tests.PaletteFloor.floorChecks ref
  Tests.PaletteFloor.fillChecks ref
  Tests.PaletteFloor.regionChecks ref
  Tests.PaletteCover.coverChecks ref
  Tests.PaletteCover.deckChecks ref
  Tests.PaletteCover.hiddenChecks ref
  Tests.AlertMark.containerChecks ref
  Tests.AlertMark.markChecks ref
  Tests.AlertMark.placeChecks ref
  Tests.ColourSolve.checks ref
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
  pdfDestinationChecks ref oneFace arts
  recipeParacolChecks ref oneFace
  recipeTabularxChecks ref oneFace
  recipeTabularxSharesChecks ref
  recipeColModChecks ref
  tableContextChecks ref oneFace
  tableFlexChecks ref oneFace
  tableSuiteChecks ref oneFace
  tableFlexOverflowChecks ref oneFace
  columnFlowChecks ref oneFace
  columnGeometryChecks ref oneFace
  recipeTitlePageChecks ref oneFace
  titlePageLifecycleChecks ref oneFace
  environmentArgumentChecks ref oneFace
  recipeUlemChecks ref oneFace
  recipeLinkAffordChecks ref oneFace
  boxPosRowChecks ref oneFace
  underlineChecks ref geom oneFace font
  underlineSpacingChecks ref oneFace
  linkSignalChecks ref geom oneFace
  inkGeometryChecks ref
  spacingChecks ref geom oneFace font
  paragraphMathRhythmChecks ref
  Tests.LineRhythm.stepLeadingChecks ref oneFace
  Tests.LineRhythm.raggedFrameChecks ref oneFace
  Tests.LineRhythm.listingPitchChecks ref oneFace
  Tests.LineRhythm.displayStepChecks ref oneFace
  Tests.LineRhythm.deckListingChecks ref oneFace
  Tests.LineRhythm.cellStepChecks ref oneFace
  Tests.LineRhythm.paraEndChecks ref oneFace
  Tests.LineRhythm.venueLadderChecks ref oneFace
  Tests.LineRhythm.inlineRunChecks ref oneFace
  Tests.LineRhythm.overlayGapChecks ref oneFace
  Tests.LineRhythm.disclosureGapChecks ref
  Tests.LineRhythm.carrierDisplayChecks ref oneFace
  Tests.LineRhythm.onlyGapChecks ref
  Tests.LineRhythm.visibleScreenChecks ref
  Tests.LineRhythm.headingLeadChecks ref oneFace
  Tests.LineRhythm.centredRuntChecks ref oneFace
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
  strutLengthChecks ref oneFace
  cardChecks ref oneFace pats
  cutMarkChecks ref oneFace
  drawnMarkChecks ref oneFace
  printColourChecks ref oneFace
  pdfVersionChecks ref oneFace
  driverOptionChecks ref oneFace
  posterChecks ref oneFace
  censusChecks ref oneFace pats
  titledGroundChecks ref oneFace
  oneInkChecks ref oneFace
  scopeChecks ref oneFace
  bandChecks ref oneFace
  agreeChecks ref oneFace pats
  artifactMarkChecks ref oneFace pats
  gfxDefectChecks ref oneFace
  gfxLabelOrderChecks ref oneFace
  gfxContentPageChecks ref oneFace
  pdfFigureWriterChecks ref oneFace
  gfxInkRasterChecks ref oneFace
  gfxAgreementChecks ref oneFace arts
  gfxStrokeCensusChecks ref arts
  copiedFormChecks ref arts
  structTreeChecks ref oneFace arts
  pictureLayoutChecks ref oneFace
  picturePathSyntaxChecks ref oneFace
  pictureShrinkChecks ref oneFace
  PictureContracts.provenanceRenderChecks ref oneFace
  pictureBoxChecks ref oneFace
  pictureBendChecks ref oneFace
  pictureInlineChecks ref oneFace
  pictureGroupSentenceChecks ref oneFace
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
  pictureAlphabetLabelChecks ref oneFace
  labelSettleChecks ref oneFace
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
  listMarginChecks ref oneFace
  abstractFormChecks ref oneFace
  afterHeadingListChecks ref oneFace
  headingKeepChecks ref oneFace
  frameBodyChecks ref oneFace
  frameContentEndChecks ref oneFace
  footlineChecks ref
  Tests.FrameArea.checks ref
  Tests.FrameArea.htmlChecks ref
  Tests.FrameArea.footBoxChecks ref
  Tests.FrameArea.frameNoteChecks ref
  Tests.FrameArea.classAlignChecks ref
  Tests.FrameArea.openingChecks ref
  Tests.FrameArea.footWeightChecks ref
  Tests.FrameArea.trivlistOpeningChecks ref
  Tests.FrameArea.standoutAlignNoteChecks ref
  Tests.FrameGeometry.titleInsetChecks ref
  Tests.FrameGeometry.standoutNumberChecks ref
  Tests.FrameGeometry.sectionMeasureChecks ref
  Tests.FrameGeometry.titleOpeningChecks ref
  Tests.FrameGeometry.centreSplitChecks ref
  Tests.FrameGeometry.vfillChecks ref
  Tests.FrameGeometry.nestedFillChecks ref
  Tests.FrameGeometry.fillCarrierChecks ref
  Tests.FrameGeometry.fillCensusChecks ref
  Tests.FrameGeometry.articleFillChecks ref
  Tests.FrameGeometry.alertChecks ref
  Tests.FrameFit.overhangChecks ref
  Tests.FrameFit.squeezeChecks ref
  Tests.FrameFit.breakableTitleChecks ref
  Tests.FrameFit.runningFootChecks ref
  Tests.FrameFit.titlePageSqueezeChecks ref
  Tests.NestedLedgers.checks ref oneFace
  Tests.DeclaredLadder.checks ref oneFace
  pageSuiteChecks ref oneFace
  Tests.FrameArea.floatLevelChecks ref
  topskipChecks ref oneFace
  labelBaselineChecks ref oneFace
  boundaryFitChecks ref oneFace
  frameSpecChecks ref oneFace
  boxArgChecks ref oneFace
  phantomChecks ref oneFace
  pictureDefnReachChecks ref oneFace
  pictureRouteChecks ref oneFace
  tikzcdRouteChecks ref oneFace
  boundaryFidelityChecks ref
  tikzTreeChecks ref oneFace
  tikzScopeChecks ref oneFace
  tikzPathChecks ref oneFace
  Tests.boundaryFaceChecks ref
  tikzLongTailChecks ref oneFace
  tikzShapeChecks ref oneFace
  tikzTipChecks ref oneFace
  tikzcdNativeChecks ref (← mathSetOf oneFace)
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
  Tests.macroRoleChecks ref oneFace
  macroAccentChecks ref oneFace
  macroForwardingChecks ref oneFace
  roleShapingChecks ref oneFace
  macroPhaseChecks ref oneFace
  macroHookScopeChecks ref oneFace
  macroDelimiterScopeChecks ref oneFace
  packageOptionChecks ref oneFace
  picSiteChecks ref oneFace
  picNumberTextChecks ref oneFace
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
  deckStillChecks ref
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
  styleMergeChecks ref
  footerBandChecks ref oneFace
  chromeFooterChecks ref oneFace
  numberingChecks ref oneFace
  slideLabelChecks ref oneFace
  Tests.frameAnchorChecks ref
  composeChecks ref oneFace
  frameFootChecks ref oneFace
  scannerChecks ref
  rhythmChecks ref oneFace
  measureChecks ref oneFace
  imageChecks ref oneFace
  svgAssetChecks ref
  svgToolChecks ref oneFace
  Tests.svgNativePdfChecks ref oneFace
  Tests.svgFontMatchChecks ref oneFace
  Tests.svgHtmlChecks ref
  Tests.svgRasterFigureChecks ref oneFace
  Tests.svgFormTextChecks ref oneFace
  Tests.svgCorpusHtmlChecks ref oneFace
  Tests.svgTitleAltChecks ref
  Tests.svgRouteChecks ref
  Tests.svgConverterSuiteChecks ref
  Tests.svgLinkNoteChecks ref
  Tests.svgGlyphGapChecks ref oneFace
  Tests.figuresDeclChecks ref
  animatedGraphicsChecks ref oneFace
  animatedFacesChecks ref oneFace
  pdfPageSelectionChecks ref
  pdfReadObjectsChecks ref
  pdfXrefRowsChecks ref
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
  Tests.packageImportChecks ref oneFace
  Tests.beamerProofChecks ref
  xparseProvideChecks ref oneFace
  xparseIgnoredOperandsChecks ref oneFace
  overlaySetChecks ref oneFace
  overlayOnlyChecks ref oneFace
  overlayVisibleChecks ref oneFace
  overlayStyleChecks ref oneFace
  overlayContractChecks ref oneFace
  overlayInputChecks ref oneFace
  overlaySingletonChecks ref oneFace
  overlaySingletonHtmlChecks ref
  frameHeadingScopeChecks ref oneFace
  sectionSuiteChecks ref oneFace
  nestedStageChecks ref oneFace arts
  refusedEnvChecks ref oneFace
  splitPairingOwedChecks ref
  groupPrimitiveChecks ref
  groupedBlockChecks ref oneFace
  reservedNameChecks ref oneFace
  delimitedUseChecks ref oneFace
  delimitedSigChecks ref oneFace
  registerArithChecks ref oneFace
  composedLengthChecks ref
  endInputChecks ref oneFace
  abstractRedefChecks ref oneFace
  ignoredDefinitionChecks ref oneFace
  captionScopeChecks ref oneFace
  globalCaptionSkipChecks ref oneFace
  environScopeChecks ref oneFace
  environChecks ref oneFace
  algKeywordChecks ref oneFace
  Tests.ParamCensus.paramCensusChecks ref oneFace
  Tests.ParamCensus.paramTruthChecks ref oneFace
  Tests.ParamCensus.paramSilenceChecks ref oneFace
  Tests.ParamCensus.textHeightChecks ref oneFace
  Tests.ParamCensus.textBlockChecks ref
  Tests.ParamCensus.engineTokenChecks ref
  declSettingSuiteChecks ref oneFace font
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
  bibModelChecks ref oneFace
  hspaceAffineChecks ref oneFace
  inlineRuleChecks ref oneFace
  fontSizeAffineChecks ref oneFace
  normalFontChecks ref
  linkColorChecks ref oneFace
  algorithmReadChecks ref oneFace

/-- The artifact text readers' blocks over the corpus: the PDF's text layer read from its bytes; a
missing or unparsable font skips them. -/
def textLayerChecks (ref : IO.Ref (List String)) : IO Unit := do
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  Tests.pdfTextChecks ref (oneFaceOf font)

/-- The covered-steps blocks: a body's covering, the dim path's colours and a pause's reach. -/
def coveredStepsChecks (ref : IO.Ref (List String)) : IO Unit := do
  Tests.CoveredSteps.bodyShareChecks ref
  Tests.CoveredSteps.dimPathChecks ref
  Tests.CoveredSteps.pauseScopeChecks ref

/-- The world premises' blocks: the inert rows' probes, the runtime's process boundary, the
toolchain's spawners, and the registry held to the source. -/
def worldPremiseChecks (ref : IO.Ref (List String)) : IO Unit := do
  Tests.inertProbeChecks ref
  Tests.processRuntimeChecks ref
  toolchainSpawnChecks ref
  premiseChecks ref

/-- The url, listings, flag, column-ground, inline-box, environment-code, algorithm-word and chapter
blocks, dispatched apart so the surface and layout suites stay within their elaboration budgets; a
missing or unparsable font skips the face blocks. -/
def commandSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  pathFaceChecks ref
  Tests.lstInlineChecks ref
  pointDoorChecks ref
  texLengthChecks ref
  let some fontData ← findFont | return ()
  let .ok font := Font.parse fontData | return ()
  let oneFace := oneFaceOf font
  Tests.FlagCommands.flagCommandChecks ref oneFace
  columnGroundChecks ref oneFace
  Tests.InlineBoxes.inlineBoxChecks ref oneFace
  Tests.InlineBoxes.boxArgumentChecks ref oneFace
  Tests.InlineBoxes.boxScopeChecks ref oneFace
  Tests.InlineBoxes.boxBlockChecks ref oneFace
  Tests.EnvCode.templateCodeUseChecks ref oneFace
  Tests.EnvCode.inlineEnvScopeChecks ref oneFace
  Tests.EnvCode.wrapEnvChecks ref oneFace
  Tests.EnvCode.blockArgChecks ref oneFace
  if let some faces ← serifFacesSet then algWordChecks ref faces
  Tests.Chapters.chapterChecks ref oneFace
  Tests.FlowClass.checks ref oneFace
  Tests.Chapters.twosideChecks ref oneFace
  Tests.Chapters.markChecks ref oneFace
  Tests.Chapters.chapterReadingChecks ref oneFace
  Tests.Chapters.chapterDeclarationChecks ref oneFace
  Tests.Chapters.numberingStateChecks ref oneFace
  classLeadingChecks ref oneFace

/-- The compat, class, bibliography and math elaboration blocks, dispatched together so `main` stays
within its elaboration budget. -/
def surfaceSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  terminationChecks ref
  hookChecks ref
  hookSeamChecks ref
  urlFaceChecks ref
  compatIndexChecks ref
  compatConservationChecks ref
  crefChecks ref
  classOptionChecks ref
  Tests.keyValChecks ref
  linenoChecks ref
  footnoteChecks ref
  mathChecks ref
  mathAlphaGeometryChecks ref
  mathAlphaSemanticsChecks ref
  mathAlphaEntryChecks ref
  mathDiagnosticOriginChecks ref
  mathDelimiterTriggerChecks ref
  mathDollarSurfaceChecks ref
  isolatedHoleChecks ref
  mathSymChecks ref
  textSymChecks ref
  inlineVerbChecks ref
  Tests.inlineCodeChecks ref
  Tests.inlineCodeRequestChecks ref
  verbatimAmbientChecks ref
  argumentBlockChecks ref
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
  Tests.engineCacheChecks ref
  Tests.engineIdentityChecks ref
  Tests.imageCopyChecks ref
  Tests.engineWatchChecks ref
  Tests.browserFaceBatchChecks ref
  Tests.cacheIdentityChecks ref
  Tests.cacheRecordChecks ref
  Tests.pictureAssetsChecks ref
  Tests.toolMemoChecks ref
  Tests.World.checks ref
  Tests.oracleWaitChecks ref
  toolProbeChecks ref
  Tests.texFontTreeChecks ref
  posterChromeCompatChecks ref
  keyedLookupChecks ref
  compatAccountingChecks ref
  privacyMatcherChecks ref
  privacyGateChecks ref

/-- The theme, palette and role blocks. -/
def themeSuiteChecks (ref : IO.Ref (List String)) : IO Unit := do
  paletteChecks ref
  Tests.ThemePalette.checks ref
  Tests.ThemeCss.checks ref
  mixChecks ref
  contrastChecks ref
  contrastContractChecks ref
  a11yChecks ref
  themeChecks ref
  designChecks ref
  roleChecks ref
  titleGroundChecks ref
  roleInvocationChecks ref
  docReportChecks ref
  roleShadowChecks ref
  geminiChecks ref

/-- The font-face blocks, run unconditionally: none may hide behind the layout suite's font gate. -/
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
  hexChecks ref
  inputDecodingChecks ref
  argsChecks ref
  renderChecks ref
  runCostChecks ref
  Tests.slidesBenchChecks ref
  watchDeliveryChecks ref
  diagnosticFormatChecks ref
  diagnosticTriggerChecks ref
  diagnosticImageOriginChecks ref
  diagnosticFontScopeChecks ref
  diagnosticOriginChecks ref
  diagnosticContrastOriginChecks ref
  Tests.beamerColorOriginsChecks ref
  diagnosticProducerOriginChecks ref
  diagnosticAggregationOriginChecks ref
  diagnosticPipelineOriginChecks ref
  pictureShipChecks ref
  Tests.boundaryFaceRetryChecks ref
  algLabelFaceChecks ref
  Tests.graphicsPathChecks ref
  bibFieldShipChecks ref
  bibFuzzShipChecks ref
  sourceAnnotationChecks ref
  buildGraphChecks ref
  inputOriginsChecks ref
  imageOriginsChecks ref
  nativeFigureBuildChecks ref
  pdfOptionalContentShipChecks ref
  lexChecks ref
  braceEolChecks ref
  nfcChecks ref
  accentChecks ref
  localeChecks ref
  parseChecks ref
  elabDocChecks ref

  corpusCoverageChecks ref
  runGoldens update (failures ref)
  if update then Tests.FlowClass.update
  Tests.regressionDocumentChecks ref
  floatRefAgreementChecks ref

  dimChecks ref
  -- A fractional case: its String.Slice ops get stuck for decide, so it runs here.
  check ref "sp pt string fractional" ((Dim.bp 3 / 2).toBpString == "1.5")
  kpChecks ref
  hyphenChecks ref
  walkChecks ref
  diagChecks ref
  mirrorChecks ref
  pendingChecks ref
  salvageChecks ref
  diagSiteCountChecks ref
  Tests.DiagFold.foldChecks ref
  Tests.DiagFold.reflowAccountChecks ref
  Tests.DiagFold.frameOverfullChecks ref
  Tests.DiagFold.subjectDoorChecks ref
  elabWarningContractChecks ref
  elabTitleBoundaryChecks ref
  frontendTitleContextChecks ref
  frontendInputRequestChecks ref
  frontendPictureCompositionChecks ref
  frontendControlContractChecks ref
  ctrlGateChecks ref
  ctrlLeaveChecks ref
  lowerEmitChecks ref
  elabUnknownDispatchChecks ref
  elabFrameSourceChecks ref
  porcelainCensusChecks ref
  siteAccountingChecks ref
  diagAuditChecks ref
  reportChecks ref
  worldPremiseChecks ref
  optionRunAccountingChecks ref
  visibleRunAccountingChecks ref
  monoSlotChecks ref
  structChecks ref
  pdfStructCoherenceChecks ref
  pdfReadRoundtripChecks ref
  pdfWideContainerChecks ref
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
  Tests.DiagDeletion.ignoredDeletionChecks ref
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
  commandSuiteChecks ref
  backendSuiteChecks ref
  themeSuiteChecks ref
  fontFaceSuiteChecks ref
  layoutSuiteChecks ref
  coveredStepsChecks ref
  textLayerChecks ref
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
