import Tests.DiagAudit
import Tests.PdfWriter
import Tests.Icc
import Tests.PrintColour
import Tests.TexFontTrees
import Tests.ItemLabels
import Tests.LabelLines
import Tests.WebMeasure
import Tests.EngineCache
import Tests.BuildGraph
import Tests.DeclaredColors
import Tests.ColorNames
import LeanTex.Core.ControlContract
import LeanTex.Core.CodeDocContract
import Tests.Surface
import Tests.Regress
import Tests.Census
import Tests.Conditionals
import Tests.StringConditionals
import Tests.BoxRow
import Tests.RecipeStructure
import Tests.PdfDestination
import Tests.TableContext
import Tests.TableSide
import Tests.FrameAnchors
import LeanTex.Core.PdfAgreement
import Tests.TableFlex
import Tests.ColumnFlow
import Tests.ColumnGeometry
import Tests.TitlePageLifecycle
import Tests.LinkMacroLayout
import Tests.PackageCode
import Tests.PackageImports
import Tests.ParagraphMathRhythm
import Tests.BeamerProof
import Tests.MarkdownHtml
import Tests.MarkdownHeadings
import Tests.MarkdownTables
import Tests.MarkdownPage
import Tests.MarkdownWarnings
import Tests.MonoDefault
import Tests.MarkdownCode
import Tests.Settings
import Tests.Artifact
import Tests.UnderlineSpacing
import Tests.HtmlTokens
import Tests.HtmlContained
import Tests.Settings
import Tests.Redefine
import Tests.NestedLedgers
import Tests.DeclaredLadder
import Tests.PageOverrun
import Tests.PageTurns
import Tests.ParamCensus
import Tests.ParamCensusDecl
import Tests.DeclSettings
import Tests.Images
import Tests.SvgImages
import Tests.SvgTools
import Tests.SvgNative
import Tests.AnimatedGraphics
import Tests.AnimatedFaces
import Tests.PdfPageSelection
import Tests.RasterPages
import Tests.FontSize
import Tests.CancelRegression
import Tests.CancelHtml
import Tests.CancelAlignment
import Tests.CancelMetric
import Tests.CancelContext
import Tests.CancelReview
import Tests.MathSym
import Tests.BeamerHooks
import Tests.StandoutPalette
import Tests.BeamerColors
import Tests.BeamerColorOrigins
import Tests.BeamerTemplates
import Tests.ListDeclarations
import Tests.Tcolorbox
import Tests.TcolorboxColors
import Tests.BlockBar
import Tests.BlockBody
import Tests.BlockGeometry
import Tests.BlockSkips
import Tests.BlockTemplate
import Tests.BlockFillConditionals
import Tests.BlockRegionFit
import Tests.BlockHeaderClearance
import Tests.FrameArea
import Tests.FrameGeometry
import Tests.FrameFit
import Tests.PaletteTextEpoch
import Tests.GroupScope
import LeanTex.Core.GroupContract
import Tests.ThemePalette
import Tests.ThemeCss
import Tests.MintedSettings
import Tests.ListingHighlight
import Tests.ListingProvider
import Tests.ListingStyleTable
import Tests.PublicationPaths
import Tests.MarkdownInput
import Tests.MarkdownDoors
import Tests.MarkdownTwin
import Tests.InputUse
import Tests.MathAlphaEntry
import Tests.MathDiagnosticOrigins
import Tests.MathDelimiterTriggers
import Tests.OverlaySets
import Tests.OverlayStyles
import Tests.OverlayContracts
import Tests.OverlayInputs
import Tests.OverlaySingleton
import Tests.OverlaySingletonHtml
import Tests.DiagnosticFormat
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
import Tests.ImageOrigins
import Tests.SlideLabels
import Tests.PictureLabelSpacing
import Tests.PictureHtmlBaseline
import Tests.PictureMathLabels
import Tests.HtmlA11y
import Tests.FormulaFloor
import Tests.PicturePathSyntax
import Tests.PictureShrink
import Tests.PictureBoundary
import Tests.FontDefaults
import Tests.Batch
import Tests.ElabFrameSources
import Tests.LayoutSources
import Tests.LineRhythm
import Tests.Privacy
import Tests.DiagFold
import Tests.InlineCode
import scripts.LandCore
import Tests.World
import Tests.OracleWaits
import Tests.ProcessRuntime
import Tests.PaletteFloor
import Tests.AlertMark
import Tests.SeedSeries
import Tests.MetaEscape
import Tests.Algorithm
import Tests.Layout
import Tests.FrameHeadingScope
import Tests.SectionPages
import Tests.Contents
import Tests.Themes
import Tests.SeedPalette
import Tests.PaletteCover
import Tests.UnusedSettings
import Tests.BibEdges
import Tests.DocCiteEdges
import Tests.MdNoteEdges
import Tests.MdCiteEdges
import Tests.LeanProseReading
import Tests.AmsMath
import Tests.CoveredSteps
import Tests.ListsKoma
import Tests.FlagCommands
import Tests.InlineBoxes
import Tests.EnvCode
import Tests.Chapters
import Tests.Schemes
import Tests.MacroRoles
import Tests.SvgHtml

/-! Every breakage the user reported, as a row whose pins hold it closed; a report closes only as
`guarded`, and the unwitnessed and owed counts are held both ways. -/

open LeanTex.Core
open DiagAudit (Pin suiteText)
open Tests (mintedSettingsChecks listingHighlightChecks listingPaletteContinuationChecks
  shellReplyChecks shellHighlightChecks listingProviderChecks listingStyleTableChecks publicationPathChecks
  htmlContainedChecks htmlContainedRawContextChecks htmlContainedPublicationChecks htmlContainedSvgColorChecks
  htmlContainedCliChecks htmlContainedCorpusChecks
  listingPaletteAuditChecks listingRoleEpochChecks svgAssetChecks svgNativeBoundaryChecks animatedGraphicsChecks
  animatedFacesChecks imageContentUrlChecks svgToolChecks markdownInputChecks
  markdownInputHtmlChecks disclosurePrintChecks overlaySetChecks overlayOnlyChecks overlayVisibleChecks
  overlayStyleChecks
  overlayContractChecks overlayInputChecks overlaySingletonHtmlChecks diagnosticFormatChecks diagnosticTriggerChecks diagnosticImageOriginChecks diagnosticFontScopeChecks
  diagnosticOriginChecks diagnosticContrastOriginChecks sourceAnnotationChecks inputOriginsChecks imageOriginsChecks
  tableContextChecks linkMacroLayoutChecks inputUseChecks mathAlphaEntryChecks mathAlphaRegionChecks
  mathDiagnosticOriginChecks mathDelimiterTriggerChecks mathDollarSurfaceChecks
  diagnosticProducerOriginChecks diagnosticAggregationOriginChecks diagnosticPipelineOriginChecks
  listDeclarationChecks stringConditionalChecks codeRoleChecks seededCodeChecks definitionNameChecks
  hashCommandChecks)
open TcolorboxChecks (tcolorboxChecks tcolorboxSourceChecks)
open TcolorboxColors (tcolorboxColorChecks)
open PictureBoundary (pictureBoundaryChecks pictureWrapperChecks pictureShipChecks)
open Tests (fontDefaultsChecks fontDefaultsOverrideChecks weightSubstitutionRecordChecks
  blockBarChecks batchChecks)

namespace Reports

/-- Whose record shows a guard failing. -/
inductive Seen where
  /-- An independent reviewer's run. -/
  | reviewer
  /-- The fix's author, in its commit or its plan entry. -/
  | author
  /-- This registry's own run. -/
  | audit
  deriving Repr, BEq

/-- The tree a failing run built. -/
inductive Run where
  /-- The tree at the named commit, before the fix. -/
  | before
  /-- The tree at the named commit with the fix reverted. -/
  | revert
  deriving Repr, BEq

/-- Where a report stands. -/
inductive State where
  /-- Its guards failed on `sha` (built as `run`, recorded by `seen`) and
  pass on this tree. -/
  | guarded (sha : String) (run : Run) (seen : Seen)
  /-- Guarded, but no failing run is on record. -/
  | unwitnessed
  /-- Measured or decided: no defect of the engine as it stands; the pins
  hold the measurement. -/
  | answered
  /-- Not closed: `owner` owes it, and `guards` are the names its guards
  land under. -/
  | owed (owner : String) (guards : List String)

structure Report where
  id : String
  date : String
  what : String
  pins : List Pin
  accept : List String := []
  state : State

/-- The reports, oldest first. -/
def reports : List Report := [
  { id := "R01", date := "2026-09-16"
    what := "two section headings vanished in one PDF viewer and showed in two others: a text-positioning adjustment past sixteen bits"
    pins := [check% pdfStreamChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R02", date := "2026-09-16"
    what := "a résumé did not build as written, set the gap under its large name line far too wide, ran onto a second page, and let a built-in shadow the document's own macro"
    pins := [check% spacingChecks, check% compatChecks]
    accept := ["the résumé's own check recipe, against its lualatex build"]
    state := .unwitnessed },
  { id := "R03", date := "2026-09-16"
    what := "a fixture failed on another machine: fixtures named the host's fonts, and the harness read the host's font directories"
    pins := [check% runGoldens]
    accept := ["the corpus built in a mount namespace with every system and TeX font directory emptied"]
    state := .unwitnessed },
  { id := "R04", date := "2026-09-17"
    what := "unsupported constructs shipped as warnings or in silence where the content was lost"
    pins := [check% diagChecks]
    state := .unwitnessed },
  { id := "R05", date := "2026-09-17"
    what := "the footline's right slot must stay pinned to the right margin, a lower-priority slot painted over rather than reflowed"
    pins := [thm% Layout.bandSlotX_right_pinned, check% bandChecks]
    state := .unwitnessed },
  { id := "R06", date := "2026-09-17"
    what := "a slide's frame footer was not visible"
    pins := [thm% Layout.bodyBottom_clears_footer, check% footerBandChecks,
      check% chromeFooterChecks]
    state := .guarded "7ff2ddec" .revert .author },
  { id := "R07", date := "2026-09-17"
    what := "six defects visible on one rendered page while every check was green"
    pins := [check% censusChecks]
    state := .unwitnessed },
  { id := "R08", date := "2026-09-17"
    what := "caption and float spacing drifted from document to document"
    pins := [thm% Ir.caption_gaps_rhythm, check% tableChecks]
    state := .unwitnessed },
  { id := "R09", date := "2026-09-17"
    what := "a site's metadata title drifted from its visible title, and anchor slugs folded to ASCII, merging two distinct titles"
    pins := [check% webMetaChecks, thm% Ir.slug_no_whitespace]
    state := .guarded "29173800" .revert .author },
  { id := "R10", date := "2026-09-18"
    what := "the math face never matched the text face's size, so documents aligned the two by hand"
    pins := [thm% Math.mathSize_matches]
    state := .unwitnessed },
  { id := "R11", date := "2026-09-18"
    what := "the vertical rhythm held for PDF by theorem and for HTML only by a comment"
    pins := [thm% HtmlDoc.backend_gaps_agree, check% htmlRhythmChecks]
    state := .unwitnessed },
  { id := "R12", date := "2026-09-18"
    what := "a site port rendered a declared 32 px gap as 52 px: two rules owned one boundary"
    pins := [check% htmlRhythmChecks]
    accept := ["the site port's build and its structural comparison"]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R13", date := "2026-09-18"
    what := "a declared scroll reveal did not play in a browser's release version; decided since: the reveal is declarative where supported, and elsewhere the content stands visible with no script"
    pins := [check% pinChecks]
    state := .answered },
  { id := "R14", date := "2026-09-18"
    what := "a site port's alternate markdown link named a file other than the one served, and a face installed on the host displaced the face the document ships"
    pins := [check% mdNameChecks, check% fallbackChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R15", date := "2026-09-20"
    what := "a picture on a slide shipped far too small, and an image sized against the text height emitted nothing in HTML"
    pins := [thm% HtmlDoc.image_share_agrees, check% deckImageChecks]
    state := .unwitnessed },
  { id := "R16", date := "2026-09-21"
    what := "the HTML deck advanced on the wrong axis, took several key presses per frame, showed partial slides between frames and drew step-counter chrome"
    pins := [thm% HtmlDoc.deck_script_constant, thm% HtmlDoc.snap_pages_partition_frames,
      check% deckCssChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R17", date := "2026-09-21"
    what := "a construct the engine misunderstands reached a backend with no warning naming it"
    pins := [thm% pending_named, check% pendingChecks]
    state := .unwitnessed },
  { id := "R18", date := "2026-09-23"
    what := "a build stayed slow: pictures the external tool refused were re-rendered on every build"
    pins := [thm% LeanTex.Cli.PicCache.probed_present_exact, check% picCacheChecks]
    state := .guarded "fe4de50f" .revert .author },
  { id := "R19", date := "2026-09-24"
    what := "a diagram node's anchors sat on its letters rather than its border, so edges started inside the text"
    pins := [thm% Picture.borderHalf_between, check% pictureInnerSepChecks]
    state := .guarded "af457b47" .before .author },
  { id := "R20", date := "2026-09-24"
    what := "a diagram node written with a second key bracket was refused, so its label went missing and edges naming it were refused"
    pins := [thm% Picture.prologue_swap_agree, check% pictureNodePrologueChecks]
    state := .guarded "b0b3ec31" .before .author },
  { id := "R21", date := "2026-09-24"
    what := "two words side by side, one with a descender, looked vertically misaligned; measured: no glyph moves a label's baseline here"
    pins := [thm% Layout.labelVStep_glyph_id, check% labelBaselineChecks]
    state := .answered },
  { id := "R22", date := "2026-09-24"
    what := "a deck's HTML front page rendered nearly blank: a title page inside the author's own frame opened a slide inside a slide"
    pins := [check% nestedStageChecks]
    state := .guarded "ae063c0b" .revert .audit },
  { id := "R23", date := "2026-09-24"
    what := "a themed deck's HTML ignored the frame-title bar's padding token and emitted no title band"
    pins := [check% htmlTokenClosureChecks, check% artBandParityChecks]
    state := .guarded "6a143e3f" .before .author },
  { id := "R24", date := "2026-09-24"
    what := "a title's declared two-line break shipped as three lines, flush left, then indented, then flush left"
    pins := [check% titleBreakChecks]
    state := .guarded "3294654b" .before .author },
  { id := "R25", date := "2026-09-24"
    what := "a style file's package-loaded test printed the tested package's name, and both branches, at the top of a paper's first page; reported again after a first fix"
    pins := [check% loadedTestChecks, check% packageCodeChecks,
      thm% Elab.recoverPackageCmd_accounts]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R26", date := "2026-09-24"
    what := "a cancel-to construct met a package that does not load, and its floor set the two arguments as a product"
    pins := [check% pictureNodeFloorChecks, check% mathContainChecks, check% compatIndexChecks]
    state := .guarded "0417420a" .before .author },
  { id := "R27", date := "2026-09-25"
    what := "a theme declared a full-bleed title-page ground, and the title page still rendered the built-in"
    pins := [check% artGroundParityChecks, thm% Ir.Design.titleGround_exact]
    state := .guarded "32ef2dd7" .revert .author },
  { id := "R28", date := "2026-09-25"
    what := "a URL-style selector drew a warning that URLs set monospace, which the page contradicted, and the selector was discarded rather than honoured"
    pins := [check% monoSlotChecks, check% compatIndexChecks, .tier "compat" "url.impl"]
    state := .guarded "efcd27e2" .before .reviewer },
  { id := "R29", date := "2026-09-25"
    what := "one unknown command carrying an option run printed two warnings for one construct at one site"
    pins := [check% optionRunAccountingChecks, check% siteAccountingChecks,
      thm% Elab.unknownCmdDiag_code_exact]
    state := .guarded "efcd27e2" .before .reviewer },
  { id := "R30", date := "2026-09-26"
    what := "a deck's title page ignored its theme's title-page template: the default ground, sizes and separator"
    pins := [check% themeTitleShipChecks, check% titleSlotShipChecks,
      thm% Layout.slotShift_exact]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R31", date := "2026-09-26"
    what := "two boxes declared side by side stacked one above the other"
    pins := [check% minipageRowChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R32", date := "2026-09-26"
    what := "a picture drawn under different macro states drew the same branch every time"
    pins := [check% condAccountingChecks, check% picStateChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R33", date := "2026-09-26"
    what := "a picture node's bold text set in the regular face"
    pins := [check% pictureNodeStyleChecks]
    state := .guarded "17ac92f4" .before .reviewer },
  { id := "R34", date := "2026-09-26"
    what := "the space around a drawn picture on a slide was too tight"
    pins := [check% pictureBoxChecks, check% trivlistChecks, check% frameBodyChecks,
      thm% Ir.Pic.Picture.box_declared_exact]
    state := .guarded "f9ebb1e5" .before .reviewer },
  { id := "R35", date := "2026-09-26"
    what := "main was pushed to the public remote twice with nobody's approval; the harness mechanism is guarded, the cause is unproven"
    pins := [thm% Land.hcall_writes_owned, thm% Land.hpush_owned]
    state := .owed "the user: a pre-push hook that refuses an unapproved push" [] },
  { id := "R36", date := "2026-09-27"
    what := "declared settings were reported as ignored across documents rather than implemented"
    pins := [check% paramSiteChecks, check% abstractRedefChecks]
    state := .guarded "da9b049d" .before .author },
  { id := "R37", date := "2026-09-27"
    what := "a business card rendered wrong: its page boxes, bleed, marks, lengths and faces"
    pins := [check% filChecks, check% driverOptionChecks, check% drawnMarkChecks,
      check% pdfVersionChecks]
    accept := ["an out-of-repo print check of the engine's PDF: page boxes, cut marks, embedded faces and set text"]
    state := .guarded "da9b049d" .before .author },
  { id := "R38", date := "2026-09-27"
    what := "a website broke: every centred environment gained a wrapper element"
    pins := [check% trivlistChecks, thm% HtmlDoc.pictureSvg_overflow_contract,
      thm% HtmlDoc.blockGap_owner_contract]
    accept := ["the site port's build script and its structural comparison at three widths"]
    state := .guarded "da9b049d" .before .author },
  { id := "R39", date := "2026-09-27"
    what := "a website's build named a declared line break lost where the author's line held and only the prose after it wrapped"
    pins := [check% titleBreakChecks]
    accept := ["the site port's build, whose diagnostics name no declared-line-break loss"]
    state := .guarded "f66f9381" .before .author },
  { id := "R40", date := "2026-09-27"
    what := "a business card's text did not stand vertically centred on its faces: the gaps above and below its block differed"
    pins := [check% faceCentreChecks]
    accept := ["an out-of-repo print check of both faces, against the lualatex build of the same source"]
    state := .guarded "f16b1321" .before .author },
  { id := "R41", date := "2026-09-28"
    what := "a slide's rows of images, two to a row parted by a fill, stood clumped at the middle and too small where TeX sets them at the measure's two edges: a centred line gave its fill no share of the slack, and a text-height fraction sized against the engine's own margins rather than the frame's text area"
    pins := [check% imageRowChecks]
    accept := ["the deck's image pages measured against its lualatex build, and its slides in Chromium"]
    state := .guarded "95ce05dd" .before .author },
  { id := "R42", date := "2026-09-28"
    what := "a custom title-page template declared a full-page dark ground, but mixed node content made both artifacts fall back to the document ground"
    pins := [check% artGroundParityChecks, check% titleGroundChecks,
      thm% Ir.Design.titleGround_exact]
    accept := ["the private presentation's first page measured against its lualatex build"]
    state := .guarded "fed62cd2" .before .author },
  { id := "R43", date := "2026-09-29"
    what := "a book used affine dimension expressions and local measures across boxes, tables and images, which were refused or widened to the enclosing measure"
    pins := [check% exprChecks, check% boxWidthChecks, check% tableChecks,
      check% imageChecks]
    accept := ["the private book's check recipe, with positions and sizes measured against its lualatex build"]
    state := .guarded "82e1e271" .before .reviewer },
  { id := "R44", date := "2026-09-29"
    what := "a book's horizontal space, inline rules and arbitrary font sizes kept source syntax or ignored local measures instead of shipping their declared geometry"
    pins := [check% hspaceAffineChecks, check% inlineRuleChecks,
      check% fontSizeAffineChecks]
    accept := ["the private book's check recipe, with geometry measured against its lualatex build",
      "the public affine fixture's computed screen and print geometry in Chromium"]
    state := .guarded "82e1e271" .before .reviewer },
  { id := "R45", date := "2026-09-29"
    what := "modelled colour specifications were parsed as missing groups, and a page-colour reset failed to restore the opening ground"
    pins := [check% colorModelChecks, thm% Ir.Palette.resolveSpec_models_exact,
      thm% Ir.Palette.restore_exact]
    accept := ["the external reference corpus builds with its direct colours and restored page ground"]
    state := .guarded "82e1e271" .before .author },
  { id := "R46", date := "2026-09-29"
    what := "a title-page node containing independently styled optional data lost its page pin and set each datum in the default flow"
    pins := [thm% Ir.TitleSlot.ofNodeParts_exact,
      thm% Ir.TitleSlot.ofNodeParts_projects, check% titleSlotShipChecks]
    accept := ["two private title-page builds measured against their lualatex pages"]
    state := .guarded "82e1e271" .before .author },
  { id := "R47", date := "2026-09-29"
    what := "two title-page theme shapes placed the same metadata differently because compound optional parts lost their baseline skips and the node anchor used nominal face metrics"
    pins := [thm% Layout.slotShift_exact, check% titleSlotShipChecks,
      check% titleTemplateOptionalChecks]
    accept := ["the external synthetic title placement differential against LuaLaTeX",
      "invented-metadata builds through both private theme variants measured against their LuaLaTeX pages"]
    state := .guarded "82613240" .before .author },
  { id := "R48", date := "2026-09-29"
    what := "a cancellation's target disappeared and coloured cancellation inside an aligned formula fell back to source text"
    pins := [check% cancelReportChecks, check% cancelGeometryChecks,
      check% cancelBoxChecks, check% cancelHtmlChecks,
      thm% Math.cancelBand_between, thm% Math.cancelHead_between,
      thm% Math.cancelShaft_between, thm% Math.cancelGeom_polys_between,
      thm% Math.cancelGeom_to_polys_exact,
      thm% Math.cancelto_value_clears_between]
    accept := ["the private presentation's cancellation formulas in both artifacts",
      "the invented cancellation page in the browser and its printed output"]
    state := .guarded "671e3fa6" .before .author },
  { id := "R49", date := "2026-09-29"
    what := "block spacing and explicit standout footer hooks were skipped, and a dormant failure callback was executed"
    pins := [check% beamerHookChecks, thm% Ir.Chrome.standoutFootBand_exact,
      thm% Ir.Design.standoutFootLook_projects]
    accept := ["the private presentations build with their declared block spacing and explicit standout notes"]
    state := .guarded "2bb0d181" .before .author },
  { id := "R50", date := "2026-09-29"
    what := "kernel-declared long implication arrows were absent from the generated symbol table, turning whole aligned formulas into source text"
    pins := [check% longArrowReportChecks]
    accept := ["the private presentation's aligned implication formulas in both artifacts"]
    state := .guarded "671e3fa6" .before .author },
  { id := "R51", date := "2026-09-29"
    what := "minted defaults were skipped, so listings lost their declared font size, tab stops, wrapping and scoped option precedence"
    pins := [check% mintedSettingsChecks]
    accept := ["the private presentation's listings compared with their lualatex build"]
    state := .guarded "2bb0d181" .before .author },
  { id := "R52", date := "2026-09-30"
    what := "declared listing languages shipped as plain text without syntax highlighting"
    pins := [check% listingHighlightChecks, thm% Ir.listing_source_exact,
      thm% Listing.token_inline_source_exact]
    accept := ["the private presentations' code blocks in both artifacts",
      "invented light and dark listings on screen and in print"]
    state := .guarded "2bb0d181" .before .author },
  { id := "R53", date := "2026-09-30"
    what := "beamer colour inheritance was discarded, and declared subtitle, section and footer colours had no paint sites"
    pins := [check% beamerColorsChecks, check% titleTemplateColorChecks,
      thm% Ir.beamerColors_agree]
    accept := ["the private presentations' title, section and footer colours compared with their lualatex builds"]
    state := .guarded "2bb0d181" .before .author },
  { id := "R54", date := "2026-09-30"
    what := "vector figures failed image discovery and browser publication, while an animation command leaked its arguments instead of showing the selected poster"
    pins := [check% svgAssetChecks, check% animatedGraphicsChecks,
      check% animatedFacesChecks, check% pdfPageSelectionChecks,
      check% rasterPageChecks, thm% Image.fulfilRequests_covers,
      thm% Image.Loaded.size?_exact, thm% HtmlDoc.img_request_src_shipped,
      thm% HtmlDoc.imagePosterHref_covers]
    accept := ["the private presentation builds through both engines, with the selected poster in the native PDF and the original moving SVG in the browser",
      "synthetic SVG validation and static print and reduced-motion faces through the installed vector converters"]
    state := .guarded "a9116a2f" .before .author },
  { id := "R55", date := "2026-09-30"
    what := "a palette declared inside a frame did not reach later browser frames, and the contrast audit retained the frame-entry ground after a body declaration"
    pins := [check% listingPaletteContinuationChecks,
      check% listingPaletteAuditChecks, check% listingHighlightChecks]
    accept := ["the private presentations retain readable code across frame palette changes"]
    state := .guarded "2eedd96b" .before .author },
  { id := "R56", date := "2026-09-30"
    what := "a contrast repair was reported after a frame palette declaration while both artifacts still painted the original role ink against the new ground"
    pins := [check% listingRoleEpochChecks, check% listingHighlightChecks,
      thm% Elab.completePrepared_doc_exact]
    accept := ["invented title and standout frames paint the audited role ink after direct and nested palette declarations"]
    state := .guarded "09e4aa72" .before .author },
  { id := "R57", date := "2026-09-30"
    what := "an exporter doctype identifier caused a self-contained vector drawing to become a placeholder in both artifacts"
    pins := [check% svgNativeBoundaryChecks]
    accept := ["synthetic exporter-doctype inputs through the installed converters, with original browser bytes and painted native PDF pixels",
      "the private reference figure rendered from its original vector source"]
    state := .guarded "4ead28ae" .revert .author },
  { id := "R58", date := "2026-09-30"
    what := "a rebuilt browser figure retained the address of its cached blank response, so replaced image bytes did not reach the page"
    pins := [check% imageContentUrlChecks, check% htmlAssetChecks,
      thm% HtmlDoc.imageAssetName_inj, thm% HtmlDoc.img_request_src_shipped,
      thm% HtmlDoc.imagePosterHref_covers]
    accept := ["a controlled browser cache preserves a blank private figure after its asset changes, while the rebuilt content-keyed page draws it"]
    state := .guarded "5e8c83c9" .before .author },
  { id := "R59", date := "2026-09-30"
    what := "a direct build from vector sources lost both figures because a static include required an absent export and the final animation poster required a prebuilt frame sequence"
    pins := [check% svgAssetChecks, check% animatedGraphicsChecks,
      thm% Image.fulfilRequests_covers, thm% HtmlDoc.img_request_src_shipped]
    accept := ["synthetic source-only builds paint the final animation and static figure in the native PDF, publish the original browser sources and a painted print poster, and create no figure exports",
      "the private presentation builds directly from its vector sources without a preprocessing helper"]
    state := .guarded "3fcf4348" .before .author },
  { id := "R60", date := "2026-09-30"
    what := "crowded browser slides shrank scrollable code boxes and hid trailing lines inside their backgrounds"
    pins := [check% deckCssChecks, thm% HtmlDoc.deck_script_constant,
      thm% HtmlDoc.deck_script_gated]
    accept := ["the private presentation shows each code block at its content height and scrolls the crowded slide to expose its final lines",
      "numbered browser fragments reach the visible frame number, retain reveal steps, follow navigation and survive reload and history traversal"]
    state := .guarded "39fc3818" .before .author },
  { id := "R61", date := "2026-09-30"
    what := "a vector image build with a missing conversion executable shipped a placeholder and suggested re-export instead of installation or PATH recovery"
    pins := [check% svgToolChecks]
    state := .guarded "db831892" .before .author },
  { id := "R62", date := "2026-09-30"
    what := "Markdown file inclusion in a TeX document printed the filename and skipped the fragment instead of rendering its content"
    pins := [check% markdownInputChecks, check% inputUseChecks]
    accept := ["invented article and slide fragments preserve content and code spacing in both artifacts, with file lookup compared against lualatex"]
    state := .guarded "db831892" .before .author },
  { id := "R63", date := "2026-09-30"
    what := "a comma-separated overlay selection was treated as a continuous interval and showed content on steps the source excluded"
    pins := [check% overlaySetChecks, thm% Ir.OverlaySpec.selects_exact,
      thm% Ir.OverlaySpec.union_selects_exact]
    accept := ["four-step native and browser slides select the first and fourth steps, with the interval spelling retained as an independent control"]
    state := .guarded "db831892" .before .author },
  { id := "R64", date := "2026-09-30"
    what := "an unavailable calligraphic alphabet selected an unrelated host glyph instead of the math face's ordinary source glyph"
    pins := [thm% Math.resolveMathAlphas_covers,
      thm% Math.resolveMathAlphas_fixed_point,
       thm% Layout.resolveMathAlphas_layout_agree,
       thm% MathMl.resolveMathAlphas_html_agree,
       thm% Ir.resolveMathAlphas_fixed_point,
       thm% Ir.resolveMathAlphas_diags_exact,
       thm% Ir.resolveMathAlphas_named,
       thm% Layout.run_resolve_pages_agree,
       thm% HtmlDoc.emitTree_resolve_agree,
       check% mathAlphaEntryChecks, check% mathAlphaRegionChecks,
       check% mathChecks]
    state := .guarded "236d3b06" .before .author },
  { id := "R65", date := "2026-10-01"
    what := "a native PDF cancellation target followed a superscript baseline instead of the arrow's direction and left no measured clearance from its tip"
    pins := [check% CancelAlignment.checks,
      thm% Math.inkRayOrigin_between,
      thm% Math.inkRayOrigin_forward_between,
      thm% Math.inkRayOrigin_translation_exact,
      thm% Math.inkRayOrigin_clears_between,
      thm% Math.inkRoom_covers,
      thm% Math.cancelto_value_between,
      thm% Math.cancelto_room_covers]
    accept := ["native PDF renders of narrow, wide and tall arrows with ordinary and raised targets"]
    state := .guarded "41c36677" .before .reviewer },
  { id := "R66", date := "2026-10-01"
    what := "internal link and target wrappers around boxes kept words but lost navigation and demoted nested tables"
    pins := [check% recipeLinkWrapperChecks, check% linkMacroLayoutChecks,
      thm% Ir.linkBlocks_text,
      thm% Ir.Styles.linkBodyAfford_text]
    state := .guarded "82e1e271" .before .author },
  { id := "R67", date := "2026-10-01"
    what := "a parallel-column wrapper kept switch commands as prose and lost its declared widths and independent flows"
    pins := [check% recipeParacolChecks, check% columnFlowChecks, check% columnGeometryChecks,
      check% macroLengthExecutionChecks,
      thm% Ir.boxWidth_tracks_agree]
    state := .guarded "b91c2555" .before .author },
  { id := "R68", date := "2026-10-01"
    what := "a target-width table wrapper kept its cells as loose text and treated flexible columns as unknown"
    pins := [check% recipeTabularxChecks, check% tableContextChecks,
      check% tableFlexChecks, check% tableFlexOverflowChecks,
      check% recipeTabularxSharesChecks, check% recipeColModChecks,
      thm% Ir.tableColShares_flex_contract,
      thm% HtmlDoc.tableColEls_share_projects,
      thm% Layout.table_natural_width_exact,
      thm% Layout.table_flex_span_width_contract]
    state := .guarded "8a9cf04a" .before .author },
  { id := "R69", date := "2026-10-01"
    what := "strikeout was requested without a shared through-line geometry for both artifacts"
    pins := [check% recipeUlemChecks, thm% Ir.decorated_text,
      thm% Layout.lineThroughRaise_exact]
    state := .guarded "b2a4a435" .before .author },
  { id := "R70", date := "2026-10-01"
    what := "a title page environment kept its body as loose text under an unknown-environment warning instead of an isolated page between the surrounding matter"
    pins := [check% recipeTitlePageChecks, check% titlePageLifecycleChecks,
      thm% Ir.PageState.opening_contract, thm% Ir.PageState.ship_contract,
      thm% Ir.titlepage_empty_exact, thm% Ir.pageOpening_marker_exact]
    state := .guarded "a0aa65a1" .before .author },
  { id := "R71", date := "2026-10-02"
    what := "internal links around boxes kept their annotations but used URI fragments instead of destinations on the final PDF pages"
    pins := [check% pdfDestinationChecks, check% recipeLinkWrapperChecks]
    state := .guarded "4fec4fd2" .before .reviewer },
  { id := "R72", date := "2026-10-02"
    what := "HTML slides mixed title-derived fragments with frame numbers, omitted the first reveal suffix, and excluded standout content from the shared frame count"
    pins := [check% slideLabelChecks, thm% Ir.Chrome.standoutFootBand_exact]
    state := .guarded "7214eeb2" .before .reviewer },
  { id := "R73", date := "2026-10-02"
    what := "numbered selectors on text modifiers appeared as literal angle text instead of applying the modifier on the selected reveals"
    pins := [check% overlayStyleChecks, check% overlayInputChecks, thm% Ir.OverlaySpec.pageOrder_select_exact,
      .thm `Ir.exclusiveOccurrences_exact _ (@Ir.exclusiveOccurrences_exact.{0})]
    accept := ["selector fragments, final-slot precedence and once-only body effects reproduced on e5a5428a and f6d3a50f before correction"]
    state := .guarded "0358eb0d" .before .author },
  { id := "R74", date := "2026-10-02"
    what := "overlay contracts excluded zero and reversed selectors, one-reveal frames failed to evaluate selectors, and nested covering multiplied dimming"
    pins := [check% overlayContractChecks, check% overlaySingletonChecks, check% overlaySingletonHtmlChecks,
      thm% Ir.OverlaySpec.pageSteps_partition_contract, thm% Ir.OverlaySpec.pending_nested_exact,
      thm% Struct.onSteps_id,
      thm% HtmlDoc.overlayUsesRange_contract, thm% HtmlDoc.overlay_pending_agree,
      thm% HtmlDoc.overlay_alternation_agree]
    accept := ["rendered numbered states in both browser engines, plus reduced motion, print and script-free readings"]
    state := .guarded "e5a5428a" .before .author },
  { id := "R75", date := "2026-10-02"
    what := "diagnostics lacked a compact fixed category and inline source position, while a report reader inferred warning records from human text"
    pins := [check% diagnosticFormatChecks]
    accept := ["the report reader selftest distinguishes diagnostic records from quoted codes and unrelated log text",
      "the convention gate rejects a direct diagnostic-print mutation that the previous gate allowed"]
    state := .guarded "e5a5428a" .before .author },
  { id := "R76", date := "2026-10-02"
    what := "native link underlines stopped at each word and left interword spaces unpainted, including shared frame footers"
    pins := [check% underlineSpacingChecks, thm% Layout.appendUnderline_exact,
      thm% Layout.appendUnderline_covers]
    accept := ["native reference-deck footer inspected before and after the spacing correction"]
    state := .guarded "75c71d1e" .before .author },
  { id := "R77", date := "2026-10-02"
    what := "shell listings retained their text but lacked language classification and the resulting syntax colors in both artifacts"
    pins := [check% shellReplyChecks, check% listingProviderChecks, check% shellHighlightChecks,
      thm% ListingReply.lookup_source_exact, thm% ListingReply.plainAnswer_source_exact]
    accept := ["disabling consumption of checked replies fails 36 actual PDF and typed HTML paint assertions; installed language accuracy is checked separately"]
    state := .guarded "07e3714e" .before .author },
  { id := "R78", date := "2026-10-02"
    what := "HTML output depended on neighboring font and image files and external styles instead of being one movable, self-contained file"
    pins := [check% htmlContainedChecks, check% htmlContainedRawContextChecks,
      check% htmlContainedPublicationChecks, check% htmlContainedSvgColorChecks,
      check% htmlContainedCliChecks, check% htmlContainedCorpusChecks, check% publicationPathChecks,
      thm% HtmlResource.close_covers, thm% HtmlDoc.emitClosed_covers,
      thm% HtmlResource.style_context_refused_exact, thm% HtmlResource.script_context_refused_exact]
    accept := ["capture guards failed on the earlier publisher; publication uses the checked bytes after source files change or disappear",
      "fourteen publication checks failed before destination validation; colliding formats and filesystem aliases cannot overwrite the verified page",
      "seventeen raw-context guards failed at ac1b5347; the foreign-style witness also produced an intercepted external image request in Chromium",
      "copied reference artifacts render their images and embedded fonts offline in Chromium and Firefox; Chromium also checks print and reduced-motion posters"]
    state := .guarded "e5a5428a" .before .author },
  { id := "R79", date := "2026-10-03"
    what := "delayed font, image and input diagnostics lost the source location that requested the failing operation"
    pins := [check% diagnosticOriginChecks, check% sourceAnnotationChecks, check% inputOriginsChecks,
      check% imageOriginsChecks, thm% Data.fileRefsAt_input_exact,
      thm% Ir.eraseLocations_text, thm% Ir.displayParts_location_exact]
    accept := ["glyph guards failed on four source cases before the fix, including a later occurrence after a covered scalar and an included listing",
      "nine display and spacing assertions failed during integration; transparent source annotations now preserve display classification and control spaces",
      "synthetic driver requests preserve included file positions and macro ancestry without inventing a source for top-level filesystem failures"]
    state := .guarded "7d46cc5d" .before .author },
  { id := "R80", date := "2026-10-03"
    what := "diagnostic prose mixed the triggering construct, problem, recovery and advice, and animation notices described output formats that were not being built"
    pins := [check% diagnosticFormatChecks, check% diagnosticFontScopeChecks, check% animatedGraphicsChecks,
      thm% Diag.forOutputs_mem, thm% Diag.forOutputs_id,
      thm% Diag.sameLoss_output_exact, thm% Diag.tallySites_record_exact,
      thm% Diag.accept_record_exact]
    accept := ["formatter guards failed before the record projection changed; terminal controls and hostile line separators remain escaped data",
      "synthetic PDF and HTML builds reproduced mixed-format notices before output filtering; the convention gate checks diagnostic sinks",
      "forty-two real CLI assertions failed before native glyph output scoping; publication, acceptance, refusal and warning policy now follow the selected outputs",
      "six census checks and two CLI note-count checks failed before scope-aware accounting; repeated common records count once and independent output losses remain distinct"]
    state := .guarded "7d46cc5d" .before .author },
  { id := "R81", date := "2026-10-03"
    what := "diagnostic headers repeated the requested output format, omitted compatibility command triggers and used a different visual style from completion summaries"
    pins := [check% diagnosticFormatChecks, check% diagnosticTriggerChecks,
      check% diagnosticImageOriginChecks, check% beamerColorOriginChecks,
      thm% Compat.SourceTriggers.attribute_record_exact,
      thm% Compat.atSource_record_exact, thm% Compat.rebase_source_exact,
      thm% Elab.Ctx.sourceSpan_call_projects]
    accept := ["formatter checks failed 405 assertions before the icon and scope projection changed",
      "two real CLI guards failed before compatibility warnings carried their command; two mixed-output guards failed before Markdown counted in the presentation context",
      "twenty-three source-attribution guards failed before commands were indexed by their parsed source sites",
      "twelve colour-origin assertions failed before deferred warnings retained their per-key declaration sites across includes and later updates; four further cases failed before implicit-default cycles named an authored relationship within the cycle",
      "nine expansion assertions failed before included macro bodies and omitted defaults named their actual uses without relocating written arguments or newly read files",
      "ten image-origin assertions and both reference output builds failed before delayed alternative warnings carried an object label; a macro guard then failed before that label stopped guessing the authored command",
      "four immediate macro-origin guards and one delayed image-origin guard failed before ordinary replacement code used the written call; arguments retain their own sites",
      "routine notes stay hidden by default, remain available in verbose output and match the completion count"]
    state := .guarded "3d7169d0" .before .author },
  { id := "R82", date := "2026-10-03"
    what := "delayed image diagnostics labeled the trigger with an invented object name instead of the command written at the reported source position"
    pins := [check% diagnosticImageOriginChecks, check% diagnosticTriggerChecks,
      check% imageOriginsChecks, thm% Compat.SourceTriggers.attribute_record_exact,
      thm% Pos.beq_command_exact]
    accept := ["twenty-five focused assertions failed before source-token evidence reached delayed image diagnostics, including real CLI image failures and conversion warnings",
      "the guards cover direct commands, macro calls, included files, repeated assets and environment whitespace; synthetic and Markdown inputs never invent an authored TeX command",
      "six further assertions failed before original-input evidence preserved escaped line endings and Unicode command spellings through normalization",
      "source attribution preserves the diagnostic subject, acceptance, scope and alternative accounting"]
    state := .guarded "4527e7af" .before .author },
  { id := "R83", date := "2026-10-03"
    what := "missing image alternatives were counted as compilation warnings instead of informational authoring advice"
    pins := [check% a11yChecks, check% diagnosticImageOriginChecks]
    accept := ["four focused assertions failed before severity, warning counts, presentation and old-code migration followed the information policy",
      "explicit accessibility assertions continue to enforce the same alternative facts"]
    state := .guarded "9ede34c4" .before .author },
  { id := "R84", date := "2026-10-03"
    what := "cancellation arrows lost their visible heads and their targets sat below the forward ray instead of beyond the tip with measured clearance"
    pins := [check% CancelAlignment.checks, check% CancelMetric.checks,
      check% CancelContext.checks, check% CancelReview.checks,
      check% cancelHtmlChecks, thm% Math.cancelHead_shape_exact,
      thm% Math.CancelIn.hasValueInk_contract, thm% MathMl.widthParts_contract,
      thm% Math.inkRayOrigin_between, thm% Math.inkRayOrigin_clears_between,
      thm% Math.cancelGeom_envelope_between, thm% Layout.cancelMetric_em_agree]
    accept := ["native guards failed before arrowheads retained their full triangle and the measured target ink was centered on the forward ray",
      "seventy-two shared-provider assertions failed before both artifacts used the native style and font measurements",
      "typed HTML guards failed 320 fraction-style assertions and 352 script-scale assertions before current-style projection removed browser-dependent implicit scaling",
      "ninety-eight baseline projection assertions failed before the SVG used an explicit bottom baseline with its full measured viewport",
      "review guards failed on signed advances and leftward attachment origins before portable margins preserved the native pen in both browsers",
      "twelve local-context assertions failed before physical math lengths and text-sourced alphabets used the current box measure and text em; the stale-callback control also fails shared-column scope restoration",
      "forty-four review assertions failed before empty and nonpainting targets preserved advance without extending the reserved height or surrounding native line baselines",
      "three typed font-size assertions and a rendered Firefox text-target comparison failed before an equivalent calc spelling preserved the measured font ratio on family changes",
      "Firefox and Chromium render the same baseline projection and all forty-two script-size cases; screen and printed artifacts retain each head and target",
      "the private reference corpus builds in both formats and its affected native pages show the target beyond the arrow tip"]
    state := .guarded "9ede34c4" .before .author },
  { id := "R85", date := "2026-10-05"
    what := "path labels sat too close to strokes, multiline labels lost their clearance, diagonal or curved labels used the wrong attachment side, and browser label baselines differed from native pages"
    pins := [check% PictureLabelSpacing.checks, check% pictureHtmlBaselineChecks,
      thm% Ir.Pic.Box.axisOffset_contract, thm% Ir.Pic.Box.attachOffset_contract,
      thm% Ir.Pic.labelTextBox_translate_exact, thm% Picture.translateLabel_box_projects,
      thm% Picture.autoDir_swap_exact,
      thm% Ir.Pic.labelBaseline_box_exact, thm% HtmlDoc.pictureLabelBaseline_projects]
    accept := ["one hundred eighteen shipped-geometry assertions failed before measured whole-label attachment, covering fonts, stroke widths, explicit separation, styles, path reversal, corners and local curve tangents",
      "five hundred eighty-one artifact assertions failed before SVG alphabetic baselines projected the same measured IR band as native pages, including multiline and declared-height nodes",
      "eighty follow-up assertions failed before font-relative padding retained its surrounding dimension font, rectangle paths retained automatic attachment, and multiline labels read the document body size",
      "forty-two synthetic LuaLaTeX builds checked 263 assertions over sourced separation defaults, font and length ordering, and automatic corner placement"]
    state := .guarded "df359890" .before .author },
  { id := "R86", date := "2026-10-05"
    what := "continuous integration failed because image validation and conversion tools required by the artifact tests were absent"
    pins := [check% htmlContainedPublicationChecks, check% htmlContainedSvgColorChecks]
    accept := ["seventeen existing artifact assertions failed in continuous integration and in a local run with image tools absent from the process search path",
      "the same assertions pass with the declared image tools available before the build and test action"]
    state := .guarded "7e7ce504" .before .author },
  { id := "R87", date := "2026-10-05"
    what := "a slide deck failed to compile because list declarations, numbered footers and custom content boxes were read as stray content, and picture requests lacked style dependencies"
    pins := [check% beamerTemplateChecks, check% listDeclarationChecks,
      check% tcolorboxChecks, check% tcolorboxSourceChecks, check% tcolorboxColorChecks,
      check% blockBarChecks,
      check% boundaryChecks, check% pictureBoundaryChecks, check% stringConditionalChecks,
      check% fontDefaultsChecks, check% fontDefaultsOverrideChecks,
      thm% Elab.ESt.titleInsert_exact, thm% Elab.withBlockDecls_exact,
      thm% Tcolorbox.lower_body_covers, thm% Ir.pictureRefs_design_projects,
      thm% Parse.scopeEnv_source_exact, thm% Layout.reserveBelow_covers]
    accept := ["synthetic artifact guards failed before the list, footer and box translations, including local declarations, optional arguments and helpers declared after use templates",
      "both versions of the reference deck compile to native pages and self-contained browser output"]
    state := .guarded "6e8c3692" .before .author },
  { id := "R88", date := "2026-10-06"
    what := "independent external pictures compiled sequentially and made documents slow to build"
    pins := [check% batchChecks,
      .thm `LeanTex.Cli.Batch.plan_exact _ @LeanTex.Cli.Batch.plan_exact.{0, 0},
      .thm `LeanTex.Cli.Batch.plan_bounded _ @LeanTex.Cli.Batch.plan_bounded.{0, 0},
      .thm `LeanTex.Cli.Batch.plan_keys_nodup _ @LeanTex.Cli.Batch.plan_keys_nodup.{0, 0}]
    accept := ["two process scheduling assertions fail when bounded batches are changed to single requests: independent work no longer overlaps and a failing request prevents its independent peers from starting",
      "the real picture benchmark checks cold and warm output byte equality and measures sixteen uncached requests at 13048 milliseconds before batching and 3346 milliseconds after",
      "the existing subprocess checks hold exit, pipe closure, timeouts, capture limits and descendant cleanup"]
    state := .guarded "4b76ad6d" .revert .author },
  { id := "R89", date := "2026-10-06"
    what := "frame overflow and overfull-line diagnostics lacked the source opening or line, and bibliography cleanup shifted later frame locations"
    pins := [check% elabFrameSourceChecks, check% layoutSourceChecks,
      thm% Layout.frameSpansForPdf_covers,
      .thm `LeanTex.Core.Bib.remapSources_projects _ @LeanTex.Core.Bib.remapSources_projects]
    accept := ["two actual-layout assertions failed when a nonprinting citation paragraph was removed before identical overflowing frames; both frames retain their exact opening through bibliography rewriting and repeated elaboration"]
    state := .guarded "45f6ec8a" .before .author },
  { id := "R90", date := "2026-10-06"
    what := "a shell comment on the last source line used plain text ink instead of the colour of earlier comments"
    pins := [check% shellReplyChecks, check% listingProviderChecks, check% shellHighlightChecks,
      thm% ListingReply.ofTokens_source_exact]
    accept := ["sixty-three artifact assertions failed before the lexer boundary supplied a terminal newline, covering shell aliases, both listing styles and both source surfaces",
      "the repaired path paints final and earlier comments alike in native glyphs, emitted PDF commands and typed HTML; validation preserves all authored whitespace and the original content key",
      "a reference presentation compiles to both artifacts; its eight comments share computed screen and print colours, and the final comment is present in the native PDF raster"]
    state := .guarded "f373a48c" .before .author },
  { id := "R91", date := "2026-10-06"
    what := "mathematics in diagram labels was printed as structural plain text in HTML, adding punctuation around scripts"
    pins := [check% pictureMathLabelChecks, check% pictureHtmlBaselineChecks,
      check% pictureHtmlFaceChecks, thm% HtmlDoc.labelFormula_glyphs_agree,
      thm% HtmlDoc.pictureLabelBaseline_projects,
      thm% HtmlResource.foreignObject_requests_exact]
    accept := ["365 assertions fail against the previous renderer, across scripts, fractions, roots, five anchor directions and three font scales; native first-letter and script checks already pass",
      "the repaired labels preserve their mathematical leaves and native PDF ink; passive HTML carriers retain the declared baseline and keep resource validation recursive",
      "a reference presentation renders intact labels and native scripts in Chromium and Firefox on screen and in print"]
    state := .guarded "f373a48c" .before .audit },
  { id := "R92", date := "2026-10-07"
    what := "block body colours were ignored, leaving filled headings above unpainted bodies and losing the shared theme palette across output formats"
    pins := [check% Tests.BlockBody.checks, check% Tests.BlockFillConditionals.blockFillConditionalChecks,
      check% Tests.BlockRegionFit.checks,
      check% faceCentreChecks, check% fillCentreChecks,
      check% Tests.ThemePalette.checks,
      thm% Ir.Design.titledBody_projects, thm% Ir.Design.titledBodyPaint_contract,
      thm% Layout.closed_box_rule_covers,
      thm% Layout.Spacing.Tail.join_covers, thm% Layout.Spacing.Tail.join_comm,
      thm% Layout.Spacing.Tail.join_assoc,
      thm% Layout.Spacing.Tail.join_boxDepth_exact,
      thm% SeedPalette.generated_beamer_contract]
    accept := ["eighteen artifact assertions and forty-eight generated-palette assertions failed before the body renderer, covering normal, alert and example blocks with and without titles",
      "independent rendered review checks local colour changes, nested insets, empty filled bodies and page continuations against native ink and rendered browser pages",
      "reference presentations use six title and body colour pairs derived from their common theme palette in both renderers",
      "one hundred forty-nine source and artifact assertions cover command availability, guarded defaults and explicit overrides; four mutations remove, truncate or mispaint the body and each is rejected",
      "twelve typed HTML controls check actual declaration ownership and nesting; six malformed variants accepted by the earlier assertions are now rejected",
      "four further layout assertions fail before complete painted bounds enter page fitting and distribution; all sixteen region checks pass after repair",
      "fifty-one emitted PDF checks cover nested title padding, empty siblings, title and body seams, link annotations, source conservation, page edges and footer clearance; three fail before repair and none after, with five native pages inspected at 216 dpi",
      "two further artifact assertions fail when a following rule overlaps a closed surface; all twenty-six region checks pass after box bounds become an explicit spacing reference",
      "four column-order assertions fail when a text column hides a neighbouring surface's lower padding; all ninety-eight region checks pass after the shared column join preserves both ink and leaded bounds",
      "six existing card-centering assertions and six native PDF raster probes fail when column joins discard measured text depth; preserving that third bound restores centering while all one hundred forty-nine surface and page-boundary PDF checks still pass",
      "sixteen final-layout assertions fail when empty columns contribute inherited spacing; joining only contributing columns restores neutrality in each alignment and column order while preserving empty filled bodies and invisible struts"]
    state := .guarded "a77aeab8" .before .reviewer },
  { id := "R93", date := "2026-10-07"
    what := "changing or clearing the foreground left HTML text and listings in the previous colour, including after a filled block"
    pins := [check% Tests.PaletteTextEpoch.paletteTextEpochChecks,
      thm% HtmlDoc.Config.advancePalette_ink_projects]
    accept := ["fifteen typed artifact comparisons fail before the correction in ordinary flow and after leaving a filled body",
      "eighteen browser text colour checks agree with native layout after the correction, including plain text, mathematics, listings and foreground erasure",
      "both native documents remain byte-identical while the HTML foreground is repaired",
      "eighteen additional HTML assertions fail before declaration state is threaded through list items and ordinary containers; their native glyph checks already pass",
      "the corrected path passes typed and native checks for itemized, numbered and description lists, nested containers, and declarations scoped inside columns or notes"]
    state := .guarded "4f9dc31d" .before .reviewer },
  { id := "R94", date := "2026-10-07"
    what := "diagram paths rejected supported relative coordinates and misplaced orthogonal corners or labels"
    pins := [check% picturePathSyntaxChecks, thm% Picture.coordStep_offset_exact,
      thm% Picture.coordStep_advance_exact, thm% Picture.orthogonalCorner_exact]
    accept := ["forty-seven artifact assertions fail before the parser correction, covering balanced coordinate expressions, relative endpoints and labels before or after endpoints",
      "thirty-two additional orthogonal-corner assertions fail against the earlier corner calculation; both artifacts agree with the reference engine after repair",
      "a reference presentation compiles without its three path syntax errors, while unsupported transformations remain diagnosed"]
    state := .guarded "872d7e02" .before .author },
  { id := "R95", date := "2026-10-07"
    what := "sparse HTML palettes used unrelated literal colours instead of the shared theme defaults"
    pins := [check% Tests.ThemeCss.checks]
    accept := ["eight typed stylesheet assertions and twenty-two of one hundred and six computed browser colour checks fail before the shared fallback correction",
      "built-in and sparse palettes now agree on screen and in print while authored stylesheet overrides remain effective"]
    state := .guarded "e746d229" .before .author },
  { id := "R96", date := "2026-10-07"
    what := "delayed list marker warnings omitted the declaring source file, line and command"
    pins := [check% diagnosticOriginChecks, check% diagnosticFormatChecks]
    accept := ["three real compiler runs omit all source coordinates before repair: a direct style, a translated template and an included declaration",
      "five additional typed and CLI assertions fail until style fragments retain their declaration and delayed HTML diagnostics resolve its written command",
      "typed diagnostic checks retain the exact declaring line without changing either artifact; three real HTML outputs remain byte-identical after the final source attribution repair"]
    state := .guarded "2a9f1cf8" .before .author },
  { id := "R97", date := "2026-10-07"
    what := "page compression moved diagram labels without their boxes and arrows"
    pins := [check% pictureShrinkChecks, thm% Layout.InkOut.shiftY_zero_id,
      thm% Layout.InkOut.shiftY_add_exact, thm% Layout.InkOut.shiftY_cancel_id]
    accept := ["ten artifact assertions fail before repair when three pictures follow different amounts of shrinkable space",
      "emitted PDF coordinates and native layout now translate labels, fills, arrowheads and cubic control points by the same displacement",
      "a page requiring no compression keeps byte-identical PDF output"]
    state := .guarded "5f521c69" .before .reviewer },
  { id := "R98", date := "2026-10-07"
    what := "body palette declarations overrode title and standout surfaces, including frames inside structural scopes"
    pins := [check% Tests.ThemeCss.epochChecks,
      thm% HtmlDoc.Config.advancePalette_ink_projects]
    accept := ["one hundred and twenty computed browser colour assertions fail before separating stage paint from palette tokens",
      "twenty-four additional artifact assertions fail when conditional or alignment wrappers apply ordinary flow paint to their returned stage",
      "eighty-four authored fixtures now compare typed stage colours with native page fills and glyph ink while preserving the author's stylesheet priority"]
    state := .guarded "5f521c69" .before .reviewer },
  { id := "R99", date := "2026-10-07"
    what := "delayed compatibility notes, palette repairs and repeated contrast diagnostics lost their authored location and trigger"
    pins := [check% diagnosticContrastOriginChecks,
      check% Tests.beamerColorOriginsChecks,
      check% diagnosticProducerOriginChecks,
      check% diagnosticAggregationOriginChecks,
      check% diagnosticPipelineOriginChecks,
      thm% Compat.SourceTriggers.attribute_record_exact,
      thm% Compat.SourceTriggers.attribute_fixed_point]
    accept := ["six source-origin checks fail before repair across authored declarations, uses, anonymous mixes and changed palette epochs",
      "equal ink on a later contrasting ground identifies the later use instead of an earlier passing use",
      "repeated-site accounting preserves the first owning source and attribution changes only the trigger field",
      "fourteen additional assertions fail before the late compatibility pass restores nested and sibling input filenames",
      "four native pipeline probes preserve complete source records and direct versus included HTML bytes",
      "nine inherited and aliased colour ownership assertions fail before the shared resolver carries each winning channel's authored origin",
      "reapplying lexical attribution is a fixed point"]
    state := .guarded "5f521c69" .before .author },
  { id := "R100", date := "2026-10-07"
    what := "Math font selection and missing alphabet diagnostics lacked their owning formula source"
    pins := [check% mathDiagnosticOriginChecks,
      check% mathDelimiterTriggerChecks,
      check% mathDollarSurfaceChecks,
      thm% Ir.mathFaceRequest_covers,
      thm% Ir.resolveMathAlphas_origin_covers]
    accept := ["one hundred six authored source assertions fail before repair and pass after",
      "ordinary formulas, later alphabet requests, macro calls, included content, captions and furniture retain their owning source",
      "thirty-three delimiter assertions fail until the source index retains the opener already recorded by the lexer",
      "seventy-seven dollar assertions fail until the production parser distinguishes inline and display delimiters and retains their authored opener",
      "source attribution preserves shipped glyphs, typed math and serialized artifacts"]
    state := .guarded "6792a009" .before .author },
  { id := "R101", date := "2026-10-07"
    what := "overfull lines, wide pictures and page compression diagnostics lost the source that caused the loss"
    pins := [check% diagnosticLayoutOriginChecks,
      check% Tests.diagnosticLiteralOriginChecks,
      check% Tests.diagnosticListingOriginChecks,
      thm% Compat.SourceTriggers.attribute_unmapped_id,
      thm% Compat.SourceTriggers.atSource_unmapped_id]
    accept := ["six source assertions fail before repair on body text, footnotes, repeated pictures and a compression-causing macro",
      "sparse picture sources, backend selection, overlay replay and column cursor changes preserve the owning source",
      "the responsible box is the one that last increased the page deficit, so a later short column cannot replace it",
      "twenty-two literal assertions fail until the lexer retains exact authored text and coordinates through normalization and delayed diagnostics",
      "two independent assertions fail before repair when a normalized Unicode split fragment without an authored boundary borrows the adjacent underscore or math opener as its trigger",
      "twelve additional listing assertions fail until authored columns and tokens survive highlighting, tab expansion and generated line numbers",
      "source metadata preserves shipped layout paint and PDF bytes; absent evidence remains absent"]
    state := .guarded "0fa9c4da" .before .author },
  { id := "R102", date := "2026-10-07"
    what := "Slide blocks could lose their opening space below the header, including on continuation pages"
    pins := [check% Tests.BlockHeaderClearance.checks,
      thm% Ir.frameBodySkip_exact,
      thm% Layout.frameBodySkip_projects,
      thm% Layout.frame_opening_paint_covers,
      thm% HtmlDoc.frameBodySkip_projects,
      thm% HtmlDoc.cssLength_zero_exact]
    accept := ["the retained pre-fix integration snapshot fails twelve typed artifact assertions across ordinary paragraphs and titled, titleless and nested blocks",
      "twenty-one additional assertions fail before the opening space composes with authored margins and skips hidden speaker notes",
      "five additional assertions fail before zero-length root tokens, fallbacks and in-frame token changes retain their units for CSS length addition",
      "six continuation assertions fail before top, centre and bottom aligned frames repeat the resolved body opening and report the header they paint",
      "the fixed opening derives from the shared frame rule and leaves remaining space to the declared vertical alignment",
      "the placement theorem names its header clearance and preceding strut premises instead of claiming arbitrary overflow cannot collide"]
    state := .guarded "5f521c69" .before .author },
  { id := "R103", date := "2026-10-08"
    what := "Repeated package imports could reload definitions or disagree about dependencies already loaded"
    pins := [check% Tests.packageImportChecks,
      thm% PackageImports.admit_first_exact,
      thm% PackageImports.admit_repeat_fixed_point,
      thm% PackageImports.admit_distinct_agree]
    accept := ["fifty-nine focused assertions fail before package admission records successful loads and compatible repeated options",
      "independent checks cover cycles, repeated imports and failed dependencies reached through two parents",
      "commutation is claimed only for distinct package admissions whose effects are independent"]
    state := .guarded "376a50aa" .before .author },
  { id := "R104", date := "2026-10-08"
    what := "Small inline math could enlarge paragraph line spacing even when it fitted the shared line envelope"
    pins := [check% paragraphMathRhythmChecks,
      thm% Layout.inlineMathGap_covers,
      thm% Layout.inlineMathGap_fixed_point,
      thm% Layout.inlineMath_extent_fixed_point,
      thm% Layout.Spacing.inlineMath_placement_fixed_point]
    accept := ["twenty-four focused assertions fail before bounded math uses the paragraph strut",
      "shipped glyph positions preserve ordinary baselines while tall formulas still reserve their measured reach",
      "independent checks cover surrounding text, neighboring lines and collision clearance"]
    state := .guarded "888469cd" .before .author },
  { id := "R105", date := "2026-10-08"
    what := "Proof environments supplied implicitly by the slide class were reported as undefined"
    pins := [check% Tests.beamerProofChecks,
      thm% Compat.classPackages_ams_agree]
    accept := ["one hundred seventy focused assertions fail before the class admits its implicit theorem and math packages",
      "artifact checks cover ordinary proofs, named proofs, displayed math and nested blocks",
      "class options retain their source order, explicit opt-out remains effective, and repeated package loads preserve content once"]
    state := .guarded "53f39495" .before .author },
  { id := "R106", date := "2026-10-08"
    what := "Markdown comments, disclosures and empty anchors were refused despite having typed representations"
    pins := [check% markdownHtmlChecks,
      thm% LeanTex.Core.Md.textRaws_covers,
      thm% LeanTex.Core.Md.disclosureRaws_contract,
      thm% LeanTex.Core.Md.anchorRaws_fixed_point,
      thm% LeanTex.Core.Ir.labelAnchor_fixed_point,
      thm% LeanTex.Core.Ir.labelAnchor_single_token]
    accept := ["thirteen typed HTML and shipped layout assertions fail before the typed lowering",
      "six Unicode anchor and four comment-boundary assertions fail before their corrections",
      "comments remain invisible, disclosure content appears once in source order, and anchors retain their resolved names",
      "disclosure expansion remains diagnosed and unsupported HTML remains refused"]
    state := .guarded "53f39495295029ffd0fe47a1067e50fd07f7b053" .before .author },
  { id := "R107", date := "2026-10-08"
    what := "Markdown headings below the third level lost their distinct structural ranks"
    pins := [check% markdownHeadingChecks,
      thm% Ir.headingRank_between,
      thm% Ir.headingRank_inj,
      thm% Parse.headingControl_exact,
      thm% MarkdownHeadings.heading_artifacts_agree,
      thm% MarkdownHeadings.heading_marker_between]
    accept := ["twelve artifact assertions fail before all six heading ranks are preserved",
      "typed HTML and parsed PDF retain each heading rank independently of document titles and nesting",
      "native section numbering and run-in headings preserve their existing behavior"]
    state := .guarded "e1f84ab8e797e2a827415e683b79ce4e52d54b30" .before .author },
  { id := "R108", date := "2026-10-08"
    what := "Listing highlighting lost the selected Python environment when its interpreter was a symbolic link"
    pins := [check% listingProviderChecks]
    accept := ["twelve provider invocation assertions fail before interpreter paths preserve their environment",
      "absolute, relative and empty search path entries resolve before the child process changes directory",
      "provider replacement, failure and recovery follow the selected executable without stale answers"]
    state := .guarded "45c57eb94d1db0b99054f0f50932e6d9cfde6fef" .before .author },
  { id := "R109", date := "2026-10-08"
    what := "Standout frames ignored appended colour aliases and could retain them beyond their scope"
    pins := [check% Tests.StandoutPalette.standoutPaletteChecks,
      thm% BeamerColor.restoreAliases_contract]
    accept := ["nineteen typed HTML and shipped layout assertions fail before standout aliases are applied",
      "selected aliases restore their opening values while unrelated palette changes survive",
      "native PDF, HTML and reference output agree on the resolved frame colours",
      "unsupported callback content remains diagnosed"]
    state := .guarded "45c57eb94d1db0b99054f0f50932e6d9cfde6fef" .before .author },
  { id := "R110", date := "2026-10-08"
    what := "A proof hole in a highlighted listing shipped as a bold keyword instead of its highlighting style's error red, and every token type the style styles beyond a few coarse classes lost its colour and weight, in both artifacts; decided since: a token paints in its code role, so the types of one role share its colour and weights, a hole is the error role's, and the token-box diagnostic is retired"
    pins := [check% listingStyleTableChecks, check% shellReplyChecks,
      thm% Listing.paint_declared_mem, thm% Listing.token_inline_source_exact]
    accept := ["a presentation deck's proof-hole slide against its lualatex build, in PDF and HTML: the hole sets in the style's red at regular weight and no other page changes",
      "one hundred thirty-seven guard assertions fail with the fix reverted: the hole lexed as a keyword, weights composed as the resolved style rather than the lualatex chain, style colours beyond seven classes dropped, and the token-box diagnostic absent",
      "eight assertions fail with the hole lexing alone reverted: the hole as a bold keyword in both styles and both artifacts",
      "every standard token type of both shipped styles resolves and composes as the installed highlighter answers, from a table its generator regenerates"]
    state := .guarded "9db3a0ec" .revert .author },
  { id := "R111", date := "2026-10-08"
    what := "A math alphabet in a picture label shipped unresolved: an error element framed in red on yellow in HTML, and the source italic on the page"
    pins := [check% pictureAlphabetLabelChecks,
      check% htmlMathChecks,
      check% censusChecks,
      check% labelSettleChecks,
      check% mathDiagnosticOriginChecks,
      thm% Compat.tikzsetKeys_input_exact,
      thm% Ir.mathRequests_resolve_covers,
      thm% MathMl.formula_merrorFree_contract,
      thm% Layout.labelMetric_resolve_id,
      thm% Layout.resolveMathAlphaPicture_box_id]
    accept := ["in a run with the fix reverted — the alphabet pass skipping picture labels, the label measure reading source glyphs, and each label formula its own math root — fifty-four assertions fail, thirty-four of them this report's: label glyphs, error elements and page scalars against the same formula in a paragraph over nine invented alphabet labels, the corpus error census, the diagram fixture's upright label, the alphabet note a label's formula owes in both text families, and the driver taking a face that lacks a label's alphabet for one that measures it",
      "on the same tree, five assertions fail with the label measure alone reverted: four drawn outlines on the shipped page, each up to half a point off a text node's inner sep around the glyphs the page sets, and the settle check",
      "on the same tree, nine assertions fail with the driver probing the resolved document's labels and label formulas left unlocated: the settle check, and in both text families the face and alphabet notes of a label's formula naming no source",
      "on 40c926f8, before a label's formula was sited where its opener was written, twenty-five assertions fail: twenty in both text families, a formula the picture walk read out of a macro's definition text naming a position that text invents in the picture's file; four, a formula a style sets naming the file that includes the style or the picture rather than the file that wrote the style; and one, a setting's unread key named at the including file's line of that number",
      "a fresh build of a presentation deck ships no error element, and its alphabet edge label sets upright in both artifacts as the reference build does"]
    state := .guarded "c95d78db" .revert .author },
  { id := "R112", date := "2026-10-08"
    what := "Formulas in picture labels nested a second MathML root inside the label's own"
    pins := [check% htmlMathChecks,
      check% pictureAlphabetLabelChecks,
      check% Tests.formulaFloorChecks,
      thm% HtmlDoc.pictureKids_unnested_contract,
      thm% HtmlDoc.labelNodesList_mathFree_contract,
      thm% MathMl.formula_unnested_contract]
    accept := ["in the run that reverts R111's fix with this one, twenty of the fifty-four failing assertions are this report's: one root per label over nine invented labels, the corpus nesting census and ten structured label formulas",
      "a fresh build of a presentation deck ships no math element inside another, where the base build shipped seven"]
    state := .guarded "c95d78db" .revert .author },
  { id := "R113", date := "2026-10-08"
    what := "a slide's formal table ran past the foot of its browser stage while its printed page held it, and its text column took the centring of its scope in the browser where the column spec sets it flush left"
    pins := [check% Tests.tableSideChecks, check% Tests.tableRaggedChecks,
      check% Tests.tableLeadingChecks, check% Tests.tableLengthChecks,
      check% Tests.tableStrutChecks, check% Tests.tableFaceOrderChecks, check% censusChecks,
      thm% HtmlDoc.tableCellNode_align_projects, thm% Pdf.table_cell_side_agree,
      thm% Pdf.table_length_agree, thm% HtmlDoc.printLeading_exact,
      thm% Layout.strutBox_exact, thm% Layout.tableStrut_exact]
    accept := ["the browser oracle's stage-fit row fails on the invented table deck, one stage 53 px past its foot, before table rows take the print leading, and passes after at the deck's own aspect with no stage a pixel past its foot",
      "ninety-seven guard assertions fail with every fix this row pins reverted and the guards kept: cells stating no left side and taking their scope's, the scope's side reaching a cell's lines, modified columns justified flush left or moved off their letter's side, rows at the prose leading in the stylesheet and on their glyphs beside a rule on the page, booktabs measured in the body face and at a nominal 11pt, a preamble's ex resolved in the table's face, stylesheet lengths in points, and no warning for booktabs loaded after its face",
      "twenty of them failed on the base before any fix, the guards as they then stood, four of them the page's own text column set flush right under a right-set scope",
      "a table that fills one frame of a presentation deck fits its stage at 1280 by 720 with no scrollbar and room to spare, its text column flush left and its rule and column gaps lualatex's; on its printed pages each row stands as far from the rule beside it as lualatex sets it, to the raster's 0.12 pt"]
    state := .guarded "e7ba68fd" .revert .author },
  { id := "R114", date := "2026-10-08"
    what := "a slide whose title changes colour by overlay step was anchored and named by both alternatives of its title, each word doubled in its fragment and its accessible name"
    pins := [check% Tests.frameAnchorChecks, thm% Ir.slug_altSteps_exact]
    accept := ["six anchor, name, caption-alternative and title-metadata assertions fail with the first-page reading reverted and the guards kept, and the anchor theorem no longer holds",
      "four of them failed on the base before any fix, the guard as it then stood: alternation, colour, alert and cover steps among them",
      "every titled stage of the corpus decks is anchored and named by the words its title shows, every id held by one element",
      "a presentation deck's doubled anchors read once, a repeated title numbered rather than doubled"]
    state := .guarded "e7ba68fd" .revert .author },
  { id := "R115", date := "2026-10-08"
    what := "building the engine had become very slow: one comment line in the IR module cost over six minutes, both backends and every test module elaborating again, and one edit to a large module still costs over a minute"
    pins := [check% buildGraphChecks, check% censusChecks, thm% HtmlDoc.emitTree_resolve_agree]
    accept := ["on the base tree the build-graph check fails six ways: one hundred seventy-two test files outside the module system, both backends reading the IR's private part, the IR's private readers beyond its declared list (both backends, the markdown emitter and the colour space among them), and the two largest test files reading every module",
      "the check reads each header with the build tool's own reader: its model cases fail five ways under the line-by-line reader it replaced, which a comment in a header blinded",
      "one comment line appended to the IR module rebuilt 184 modules in 386 seconds before and 12 in 101 seconds after",
      "one comment line appended to the layout module rebuilt 171 modules in 230 seconds before and 9 in 146 seconds after",
      "the HTML backend builds in 40 seconds instead of 105: the kernel checks its emitter agreement in under a tenth of a second, under a heartbeat bound the destructuring form exceeds",
      "the census module builds in 7 seconds instead of 69, its rows in parts the census check caps",
      "the lint stage of each commit's gate took about 17 minutes and takes about 4: the source audit's compilers draw from one queue, not batches that waited for their slowest member, and its checks run at once",
      "still slow: the layout module waits about 100 of its 136 seconds behind earlier proofs, the IR module elaborates in 60, and the lint audit elaborates every source again on each commit"]
    state := .owed "a follow-up once the concurrent branches land: large-module declarations ahead of the proofs they wait behind, proof companions, and a lint audit read from the build" ["declBarrierChecks"] },
  { id := "R116", date := "2026-10-08"
    what := "personal identifiers and material from private documents reached the tree"
    pins := [check% privacyMatcherChecks, check% privacyGateChecks]
    accept := ["the lint gate's check of the staged tree against the clone's local denylist names locations at the broken commit and none after the scrub",
      "a scratch repository and a scratch clone with an invented denylist: the commit gate refuses an added line in UTF-8, Latin-1 or Windows-1252, a wrapped phrase, an accent command before a blank, an added or renamed path, and a binary naming a listed term in its own bytes or in what it inflates to (a PDF's stream or string, a PNG's compressed text, a gzip or zip member), under the default, no-prefix and mnemonic-prefix diff settings alike; the lint gate refuses an unpushed commit adding a term that a later commit removes, a message naming one in either encoding, and a clone keeping the list without the remote ref that bounds its unpushed commits; every finding prints a location, a path masked where it holds the term, and never the term",
      "an out-of-repo comparison with the private reference corpus finds none of its distinctive text, names or design values in the tree"]
    state := .guarded "fa516a828a2a36549fc2a56f1e1cb4d138b3b934" .before .author },
  { id := "R117", date := "2026-10-08"
    what := "The space between a slide block's heading and its body was far too large"
    pins := [check% Tests.BlockGeometry.blockGeometryChecks,
      thm% Ir.titledPadding_contract]
    accept := ["thirty-five distances the reference engine measures on an invented probe fail before the block template's two colour boxes and hold within 0.02 points after, across painted, transparent, title-only and body-only blocks, titled and untitled; the heading-to-body distance was 22 points against 17.6",
      "a wrapped heading painted only behind its last line, and heading and body text inset half an em from the measure, fail before; the paint now covers every heading line and reaches 0.75 ex beyond the measure, the text standing on it",
      "two presentation decks built fresh by both engines keep the reference's page counts, which one overran before; their text-bodied blocks' bars and bodies match the reference within 0.1 points, and a code-bodied block's bar and seam match while its body differs by the code listing's own spacing",
      "beamer's nested colour boxes share their parent's reach, so the earlier body report's nested-inset guard now holds a nested box at its parent's width, the parent keeping its inset and the child's skips around it",
      "review of the second fix: the body box painted under its heading's bar where the two overlap, wrapped code ended its box on its last line's letters rather than the strut each such line carries, a frame opening on a stepped block lost the block's space above in the browser, and a tcolorbox took the slide block's geometry, an untitled one shipping an empty heading line; three assertions fail on the second fix, and a tcolorbox now stands as its package sets it, seven baseline distances the reference engine measures on an invented article holding within 0.02 points where the second fix stood as much as nine points off"]
    state := .guarded "fa516a828a2a36549fc2a56f1e1cb4d138b3b934" .before .author },
  { id := "R118", date := "2026-10-08"
    what := "Consecutive slide blocks ran together as one box with no space around them"
    pins := [check% Tests.BlockGeometry.blockGeometryChecks,
      thm% HtmlDoc.blockGap_owner_contract]
    accept := ["consecutive painted blocks stood one paragraph skip apart, or touched where the page declared none, against the reference's 10 points; they now stand the template's small and medium skips and line skip apart, and a paragraph after a block spends its own skip",
      "on a presentation deck consecutive blocks stand the reference engine's 10 points apart wherever the frame has room, and where a frame overfills both engines shrink those skips",
      "in the browser consecutive blocks shared one box; each block now owns its boundary in the shared gap sheet and keeps its children's margins inside its box",
      "review of the first fix: the space around a block held the kernel's values whatever the document set the two skip registers to, and a block after a paused step lost its space above in the browser; three distances the reference engine measures and four sheet values fail on the first fix, and both artifacts now spend the registers in force, the browser's step carrier owning the boundary its block meets"]
    state := .guarded "fa516a828a2a36549fc2a56f1e1cb4d138b3b934" .before .author },
  { id := "R119", date := "2026-10-08"
    what := "Block colours did not look adjusted and their surface was a dull grey"
    pins := [check% Tests.BlockGeometry.blockGeometryChecks, check% Tests.BlockBody.checks,
      check% beamerReachChecks]
    accept := ["the grey surface was the deck's own declared colour, which the reference engine paints too; with the decks' current declarations both engines paint every block bar and body in the same colours",
      "nine shipped-colour assertions fail before: an empty colour value was refused, the theme's fill option was ignored in all three spellings, the alerted and example bodies did not inherit the block body, and a heading given only a bar took the page colour as ink",
      "a covered block on a stepped frame kept its full bars under faded text; its bars and heading now take the step's cover, as the reference fades them",
      "the theme's fill option now paints the reference engine's heading bar exactly and its bodies within one unit per channel",
      "review of the first fix: it gave every theme one theme's relationships, so under the default theme the alerted and example bodies took the block body's fill, under the inheriting theme the block title took the structure colour, and a block an overlay item opens shipped at full ink on the steps hiding the item; six assertions fail on the first fix, against the reference engine's one body fill, three bodies, title inks and covered bars",
      "review of the second fix: the inheriting theme's model claimed a block option it does not load, so a fill declared on a text role no longer painted the alerted and example bars; a declared structure colour that reached no paint went unnamed while the shipped pages stayed byte-identical; and a guard testing for the theme's own setter read it as undefined; nine assertions fail on the second fix, and a premise check two builds apart now holds every modelled colour element, under both colour themes, to being named unused exactly when the shipped pages do not change"]
    state := .guarded "fa516a828a2a36549fc2a56f1e1cb4d138b3b934" .before .author },
  { id := "R120", date := "2026-10-08"
    what := "Slide content was not centred in the slide's text area as the slide class centres it: standout frames, untitled frames and section pages stood against the slides margins on the page and inside a safe area in the web deck, a restored standout note pushed its frame down, a standout frame naming an alignment took it, and once centred dropped that alignment unnamed, the class options' top alignment was dropped, and the web deck centred a frame on its screen line boxes rather than its glyphs"
    pins := [check% Tests.FrameArea.checks, check% Tests.FrameArea.htmlChecks,
      check% Tests.FrameArea.classAlignChecks, check% Tests.FrameArea.openingChecks,
      check% Tests.FrameArea.standoutAlignNoteChecks,
      check% vdistChecks, check% faceCentreChecks, thm% Layout.frameFloor_exact,
      thm% frame_area_agree, thm% Ir.sectionPageStrut_between]
    accept := ["one assertion fails with the third review's note reverted onto the recorded commit: an alignment named with standout, before or after it, raises no note; five failed with the second review's fixes reverted onto 5a7802b8 — a standout frame naming an alignment, on the page and in the elaborated frame, the class options' top alignment twice, and the web deck's last-line trim — and the earlier guards with theirs reverted onto dbaea645",
      "a presentation deck's quote frame stands its first line within a tenth of a point of its reference typesetting on the page, and its section pages within a quarter",
      "a section page that follows a templated title page opens where every other section page does",
      "a title with no bar opens in the web deck where its page sets it, within a tenth of a point",
      "the web deck's standout frames in a presentation deck stand their first lines within a point and a fifth of their reference typesetting, where they stood up to five points high"]
    state := .guarded "39d2c95c" .revert .author },
  { id := "R121", date := "2026-10-08"
    what := "Slide footers in the web deck did not set at the footline's own size, weight and place: a standout frame's restored note took the frame's enlarged type, every footline stood a safe area above the slide's edge, a light body's footline set in the family's regular face, and a frame whose content overran it pushed its footline off the slide"
    pins := [check% Tests.FrameArea.htmlChecks, check% Tests.FrameArea.footBoxChecks,
      check% Tests.FrameArea.footWeightChecks, .tier "htmlreader" "feature.chromium.pass"]
    accept := ["two assertions fail with the second review's fixes reverted onto the recorded commit: the footline's weight under a light body, read by a cascade over the shipped stylesheet, and its place on an overrun stage; the earlier eight footline assertions failed with their fixes reverted onto dbaea645",
      "a presentation deck's web footline notes and frame numbers stand within three hundredths of a point of its reference typesetting's, its quote frame's note at the footline's own size and colour",
      "every web footline's text in both presentation decks sets in the body's light face, as the page and the reference typesetting do, its formulas in the math face",
      "an overrunning frame's web footline stays on the slide's edge, within a hundredth of a point of its reference",
      "both presentation decks print each frame on sheets that hold its content, never a footline alone"]
    state := .guarded "5a7802b8" .revert .author },
  { id := "R122", date := "2026-10-08"
    what := "The space between a slide's title bar and its first line differed from the slide class's: the web deck padded the bar below its line box, untitled frames paid a paragraph gap at their top, a first line larger than the body stood too close to the opening, a first line in the web deck stood on its screen line box, an opening list lost its top separation there, an opening image stood flush on the opening on the page, a frame opening on a center, a flush environment or a figure spent the rhythm's quantum or a float's gap on the page and nothing in the web deck, a trivlist inside a list spent the top level's topsep, a figure inside a list item read the top level's float space in the web deck, and a figure's caption the rhythm's quantum where beamer spends 7pt"
    pins := [check% Tests.FrameArea.htmlChecks, check% Tests.FrameArea.checks,
      check% Tests.FrameArea.openingChecks, check% Tests.FrameArea.trivlistOpeningChecks,
      check% Tests.FrameArea.floatLevelChecks, check% vdistChecks]
    accept := ["four assertions fail with the fifth review's fixes reverted onto the recorded commit: a figure in a list item reading its own level's float space in the web deck, a declared topsep reaching the deck as the stage's share with its note, each level's spaces on selectors the cascade reads, and beamer's caption order; seven failed with the fourth review's fixes reverted onto f516d0dc — a center inside a list item on the page, a captioned figure's skips on the page, the class option's size file's topsep, and in the web deck the description's strut, the root's and each list level's topsep as the stage's share and the caption skips; seven failed with the third review's fixes reverted onto 39d2c95c — the frame's trivlist space, a trivlist's and a figure's opening on the page and their space between paragraphs, their opening space and first-line strut in the web deck, and the deck's declared spaces — three with the second review's reverted onto 5a7802b8 — the web deck's first-line strut and opening list space, and the page's opening image — and the bar's strut box, every frame's body opening and a bar-less title's top margin with theirs reverted onto dbaea645",
      "a presentation deck's web title bars match its shipped pages' height, and on the page a short frame's first line stands within a fifth of a point of its reference typesetting",
      "an untitled frame's opening paragraph and opening list stand their first lines within a tenth of a point of their reference typesetting on the page and in the web deck, and an opening image within a sixth on the page",
      "an untitled frame opening on a center, a flushleft, a flushright, a figure, a centred image or a description stands its first line or image within a tenth of a point of its reference typesetting on the page, and a top-aligned one its lines within a tenth in the web deck too, its images a point high there",
      "on the page a center inside a first-level list item and the lines after it stand within a quarter of a point of their reference typesetting, a captioned figure's next line within an eighth of its distance from the caption, and a 9pt deck's center within a third",
      "in the web deck a figure inside a list item stands within three points of its reference typesetting, where it stood eight low"]
    state := .guarded "445f6518" .revert .author },
  { id := "R123", date := "2026-10-08"
    what := "How the two surfaces, the include of markdown in tex and the backends fit had no stated agreement, and a document's markdown twin did not read back to it: paragraphs read back as lists and headings, code lost its text, listings broke their fences and lost their blank lines, list items lost their code blocks, adjacent lists merged, a link in code-set text lost its link, a pipe in a table cell's code split the cell, and a hard break in a heading split it from its text"
    pins := [thm% Elab.elabBlocks_input_exact, thm% Elab.markdownInput_blocks_exact,
      thm% Md.desugar_vocabulary_mem, thm% Md.desugar_blockStart_contract,
      thm% MarkdownDoc.escapeLineStart_contract, thm% MarkdownDoc.rowLine_cells_exact,
      thm% MarkdownDoc.headingText_contract, thm% MarkdownDoc.titleLine_contract,
      check% Tests.MarkdownDoors.markdownDoorChecks,
      check% Tests.MarkdownTwin.markdownTwinChecks,
      .tier "mdtwin" "corpus.reread-clean", .tier "mdtwin" "cm.Lists.reread-exact"]
    accept := ["the record's failing run is the twin's: on the base tree forty-three round-trip rows fail, the thirty-seven first recorded and six of the seven added in review, for a link in code-set text, a listing's blank lines and lists side by side in an item or closing one",
      "the seventh added row, a code-set URL, holds a face the base twin kept and the first fix lost: it passes on the base tree and fails on that fix's tree, with four of the other six",
      "the theorems pinned here did not exist on the base tree, where the agreement between the surfaces and what an include means was prose",
      "the door checks are a measurement, not a guard seen failing: the elaborator they measure is the base tree's, unchanged here, and each fails on a planted divergent door; under one surface at a time, over a synthetic family reaching every markdown node to depth two and over every CommonMark example, the neutral host's whole document is the file alone under the host's surface, and a frame whose content is the include is the frame with the file's raws in its place, with the call written tight and on a line of its own",
      "a host's redefinition of each ordinary vocabulary control reaches the included file as it reaches the same raws spliced at the call",
      "two rows added in the third review round fail on the second round's twin: an item whose paragraph and nested list sit in a resolved step wrote a blank line between them, which a CommonMark reader reads as a loose list, and an item opening with a block that writes nothing wrote an empty item before its text",
      "rows added in the fourth review round fail fourteen ways on the third round's twin: a table row split at a pipe in code, a destination or a formula, a cell's hard break ended its row, and a heading's or frame title's hard break split it from its text; the fifth round's rows fail eight ways on the fourth's: the metadata title and summary written raw, a bare link the driver's document carries in a source location written as a link, a heading's hash before trailing space read as its closing sequence, a titled block's spaced title not bold, and a footnote's hard break ending the footnote",
      "the sixth round's rows fail three ways on the fifth's: a run's closing tab or hard break left inside its delimiters, and a reference list's markers written raw, so the driver's bibliography twin was no fixed point",
      "the twin's table rows read under an external GFM table reader as GFM's row grammar reads them, on every corpus twin that writes one"]
    state := .guarded "fa516a82" .before .author },
  { id := "R124", date := "2026-10-09"
    what := "An explicit vertical skip between beamer blocks was absorbed"
    pins := [check% Tests.BlockSkips.blockSkipChecks]
    accept := ["in the browser a skip was an empty box whose margin collapsed into the next element's in block flow and overrode the space the element above leaves below it, and was written in print points where every other gap is in the screen's unit: a big skip between two blocks stood 15.3 points apart against the page's 22, and on an invented probe matrix of paragraphs, blocks, lists, centred blocks, displays and listings a big skip moved what follows by 0.69 of itself after a paragraph, 0.44 after a block, 0.19 after a centred block and by less than nothing after a display",
      "the skip is now a box of its own as tall as the skip in the screen unit, the element above owning its space below before it: every skip box of the probe matrix realizes the sum of the three addends in a browser, and two blocks across a big skip stand the page's 22 points",
      "with a document paragraph skip, a skip opening a frame moved its first paragraph or list 16 points against the reference engine's 12, the frame's own negative paragraph skip lost; it now moves it 12",
      "seventy-nine assertions fail on the tree before the fix and hold after; a presentation deck's PDF is byte-identical, its block gaps match the reference engine's within 0.002 points wherever both set the same content height, and its browser deck stands each skip whole at every skip site",
      "the primitive vertical skip, its glue unbraced, was an unknown command whose value shipped as a line of text; it now moves what follows as the reference engine does, by 7 and by -3 points, and its infinite spelling stands where the fill command stands; seven assertions fail before and hold after",
      "review of the fix: a skip inside a table cell, a bold run, a footnote or a frame or block title failed the build, an infinite stretch of another order or factor became the fill command, and in the browser a skip opening an untitled frame or a paused step, or opening an item, stood a paragraph skip deeper, a paragraph past a skip after a list or a theorem paid the sheet's peer gap where the page pays the paragraph skip, and a title bar's skips added a rule's default margins and the title's own; thirty-three assertions fail on the fix and hold now, every reviewed probe moves what follows by the skip in a browser within 0.01 points, and a title bar stands its own skip alone from the title in the browser",
      "second review of the fix: in the browser the follower past a skip right after a heading, or opening a centred block, a flushleft or an item, paid the paragraph gap where its place pays nothing without the skip, six points too far, and moved what followed a negative skip down; a glue keyword run into its dimension shipped the skip's rubber as unnamed text; and a page shipping none of the engine's stylesheet lost every skip; twenty-nine assertions fail on the reviewed tree and hold now, and every reviewed heading and container probe moves what follows by the skip in a browser within 0.01 points"]
    state := .guarded "7284e33a" .before .author },
  { id := "R125", date := "2026-10-09"
    what := "a picture outside the rendered subset fell back to the subset's drawing because its standalone wrapper loaded the deck's theme, which only the presentation class defines"
    pins := [check% pictureWrapperChecks]
    accept := ["with the class family's filter reverted and the guards kept, three wrapper assertions fail: a theme a local style requires, an add-on named for the presentation class, a colour theme the deck loads and a presentation tool's package reach the standalone",
      "an invented deck whose local style requires its theme draws its picture at the boundary under lualatex, five filled circles and a label, where the base build's standalone stopped on the theme's first command and the page shipped the subset's label alone"]
    state := .guarded "269bd628" .revert .author },
  { id := "R126", date := "2026-10-09"
    what := "a picture the rendered subset drew in part and the boundary tool refused stopped the whole document: the run exited with an error and wrote nothing, and the picture's loss was several lines"
    pins := [check% pictureShipChecks, check% pictureRouteChecks,
      thm% LeanTex.Cli.Boundary.fold_covers]
    accept := ["with the fold, the placeholder's degraded loss and a line's own request reverted and the guards kept, seventy ship, pipeline and registry assertions fail: a picture drawn in part and one drawn by no one exit 1 and write neither artifact on a host whose tool refuses, on one whose tool never finishes and under the document's own declaration of no tool, a picture written twice is not one warning with its count, a refused picture in a table cell leaves its cell empty, and the full pipeline names no single line for a withdrawn picture",
      "an invented document whose picture has an expression the subset cannot read and a construct outside it, and whose tool refuses it, ships its page with one warning naming every left-out construct and the tool's own words, where the base build exited 1 and wrote nothing"]
    state := .guarded "269bd628" .revert .author },
  { id := "R127", date := "2026-10-09"
    what := "picture node labels sat about one and a half points above where lualatex sets them"
    pins := [check% labelBaselineChecks, thm% Ir.Pic.labelBaseline_between,
      thm% Layout.label_centre_glyph_free]
    accept := ["measured against lualatex in one shared face at ten points on a raster at 1200 dpi, the ink centre from a rule at the anchor: a word of capitals 1.71 points high before and 0.99 after, a word of x-height letters 0.75 and 0.03, one with a descender 0.51 high and 0.21 low, one with an ascender 2.01 and 1.29; the seat is now pgf's own mid anchor, and what remains is the wobble lualatex's centre anchor adds",
      "over the labels of a presentation deck's diagrams in its own face, measured as lualatex boxes, the mean departure from lualatex fell from 0.94 to 0.55 points and the largest from 1.72 to 1.21",
      "with the band split at the face's baseline restored and the guards kept, six assertions fail: the seat, a word of x-height letters on lualatex's baseline against a rule on the page and in the browser, and the declared bound for a word of capitals, one with an ascender and one of figures"]
    state := .guarded "269bd628" .revert .author },
  { id := "R128", date := "2026-10-09"
    what := "A block template's rule beside the title was not drawn"
    pins := [check% Tests.BlockTemplate.checks, thm% Ir.blockTitleFont_axes_exact]
    accept := ["on a presentation deck whose theme replaces the block templates with a rule in the margin beside each title's box, neither artifact drew the rule, and the title set in the regular face where the theme names a semibold family for it; both artifacts now draw the rule and set the title in that face, and in the PDF every rule's offset into the margin, width, height and place beside its title match the reference engine's within a raster pixel at 400 dots per inch",
      "sixty-five assertions fail on the tree before the fix and hold after, over invented probes of three template shapes, titled, untitled and wrapped, plain, alerted and example: every rule's position and size and every distance around the template's boxes within 0.002 points of the reference engine's, the browser's stylesheet drawing each rule from the record the page reads, a template outside the vocabulary named once with the default blocks kept, and a declared font family setting the block title in both artifacts",
      "review of the fix: an untitled block took the titled arm's skip between title and body; a template keeping an empty title box set neither the box nor its rules in the PDF while the browser drew them; a second rule beside one box ran a paragraph skip too tall; a title's strut read the page's size, not its own font's; the alerted and example titles took the plain title's font whole where beamer merges it axis by axis, so a declared family was lost and a declared plain size reached the alerted title the theme sizes itself; beamer's default blocks set a sized title about two points low per block; the browser stood none of a template's skips; a rule painted through a colour element's background channel painted the page; a provide form redefined a family command already defined; a block's style keys no site reads raised nothing; and the IR dump dropped declared families; 114 assertions fail on the reviewed tree and hold now: every reviewed probe's rules and distances within 0.002 points of the reference engine's, each block title in its face and size, the browser standing each template skip as the block's own padding, and each unread key named once with both artifacts unchanged",
      "second review of the fix: the browser set a template's empty title box at the body's line height and drew its rules where the reference engine's unstrutted box has no height to draw them; a rule painted through two colour elements took the later element's unset channel instead of the earlier one's; a title font declared with its own leading stood the page's leading; a title size declared before the theme outlived the theme's own; a block's unread style key raised a second code beside another refusal at its site and, stored, took a page without a palette its dark scheme; a title with no box of its own stood the page's interline rule, and an empty one lost its struts' line or, unstrutted, stood about three points short; and a title font declared with the star kept the theme's bold; forty-three assertions fail on the tree before the fix and hold after: every probe's rules and distances within 0.002 points of the reference engine's, each title in its face, size and weight, each rule in the channel its colour elements bind, the browser's empty title box as tall as its title font's strut with no rule beside a box of no height, and each unread key one warning with both artifacts unchanged on a page with no palette"]
    state := .guarded "f42becf3" .before .author },
  { id := "R129", date := "2026-10-10"
    what := "A markdown pipe table shipped as one run-on paragraph, its delimiter row set as dashes"
    pins := [check% Tests.MarkdownTables.markdownTableChecks,
      thm% LeanTex.Core.Md.tableRaws_contract]
    accept := ["twenty-two typed HTML and shipped layout assertions fail before the reader reads pipe tables",
      "eight more fail where every table set at its natural width: a table too wide for its measure narrows its columns as a browser's automatic table layout does, each keeping its widest word, its cells wrapping ragged with every word on the page in both artifacts; a table whose words alone pass the measure keeps them whole; and every cell of a row stands on one baseline",
      "the GFM specification's eight table examples are classified: seven match and one waits on the smart punctuation decision",
      "a long markdown report's summary table sets inside the measure under booktabs' three rules in both artifacts, where it ran forty points past it",
      "a table of prose descriptions keeps every word on the page in the PDF, on screen and in print, where its description column was cut at the page edge",
      "fourteen more fail on the rebased branch with narrowed cells' ragged right skip, the step-down and the centred overhang reverted: one-word and code lines packed onto overfull lines over the next column, and a table whose words alone passed the measure kept its size and ran off the paper in both artifacts",
      "one more fails with a tex ragged p column set unhyphenated, as a narrowed markdown cell sets: its words packed onto one line over the next column, where main's setting wraps them",
      "a results table of single figures too wide for the measure sets a size step smaller, its figures whole and inside the measure, the HTML stating the same step; one too wide even at the smallest step stands centred across both margins, on paper while no wider than the measure and both margins, and is named, with a remedy markdown can write",
      "on the branch before cells measured their code as they set it and the decision read the table's own measure, invented probes ran off the paper or out of their container: a table whose code holds hyphens kept its body size with its last column past the paper edge, a table in a quotation and one in a list item kept a size their measure could not hold, and a sixteen-column table of figures lost its edge columns; on this tree each fits its measure at the step both artifacts state, or stands centred on the paper at the last step"]
    state := .guarded "08e2326b" .revert .author },
  { id := "R130", date := "2026-10-10"
    what := "A markdown document took the article's narrow measure, leaving two-inch margins on a letter page"
    pins := [check% Tests.MarkdownPage.markdownPageChecks,
      check% Tests.MarkdownCode.markdownCodeChecks]
    accept := ["eight shipped layout and HTML measure assertions fail before markdown pages take their own text block",
      "eight listing and shipped layout assertions fail before markdown code sets small and wraps as listings wraps",
      "three more fail where inline code could not break: a justified markdown paragraph now breaks a long identifier after the url package's break characters, every line inside the measure and no word space three of its own wide, and the page's stylesheet lets a browser break one where it would overflow, while a tex document's typewriter run never breaks",
      "every shipped text face sets the markdown measure between seventy and ninety characters with the readable band judge quiet",
      "a long markdown report's side margins narrow from about two inches to about one and a half, and none of its code runs past its measure or off the page, where two hundred twenty-two lines ran off before",
      "a wrapped code line continues twenty points in on screen as on paper",
      "a justified paragraph holding a kebab-case flag longer than the measure breaks after the flag's hyphens, every line inside the measure, where on the branch before it the paragraph's rest ran past the paper on one overfull line"]
    state := .guarded "fa516a82" .before .author },
  { id := "R131", date := "2026-10-10"
    what := "A markdown document with no preamble set its code in the proportional text face, hyphenated it, and printed every repeat of a loss as its own warning"
    pins := [check% Tests.MarkdownWarnings.markdownWarningChecks,
      check% Tests.MarkdownWarnings.markdownMonoChecks,
      thm% Diag.foldRepeats_sum_exact,
      thm% Diag.foldRepeats_error_exact,
      thm% FontDb.monoCompanion_contract,
      thm% Layout.paragraphBreaksOf_undeclared_exact]
    accept := ["five assertions over the typewriter face, code line ends and the default log fail before markdown code takes its designed typewriter companion and repeated warnings fold",
      "one more fails where a markdown hard break was read as a declared line shape: the page sets as its tex twin's and names no re-flow, as LaTeX names none",
      "a long markdown report's two thousand four hundred sixty-six warning lines become four, each carrying its site count",
      "with no DejaVu installed a markdown document's code sets in the URW typewriter face beside the URW sans, with no warning",
      "a tex document that declares no typewriter face keeps the body family and the one warning that names it",
      "two presentation decks render pixel-identical, their logs only folding a repeated glyph fallback"]
    state := .guarded "fa516a82" .before .author },
  { id := "R132", date := "2026-10-10"
    what := "Inter-line spacing came out wider than the reference engine's: a paragraph in a named size stood on the body's leading, the larger sizes and code listings at six fifths of their type, and a slide's lines and gaps on screen at the screen's prose rhythm instead of the page's"
    pins := [check% Tests.LineRhythm.stepLeadingChecks, check% Tests.LineRhythm.htmlStepChecks,
      check% Tests.LineRhythm.htmlGapChecks, check% Tests.LineRhythm.listingPitchChecks,
      check% Tests.LineRhythm.displayStepChecks, check% Tests.LineRhythm.deckListingChecks,
      check% Tests.LineRhythm.cellStepChecks, check% Tests.LineRhythm.paraEndChecks,
      check% Tests.LineRhythm.venueLadderChecks, check% Tests.LineRhythm.headingLeadChecks,
      check% Tests.LineRhythm.inlineRunChecks, check% Tests.LineRhythm.overlayGapChecks,
      check% Tests.LineRhythm.carrierDisplayChecks,
      thm% Ir.runLead_between, thm% HtmlDoc.blockGapThrough_owner_contract,
      thm% Ir.carrierDisplays_text,
      thm% Ir.stepSkip_normalsize_exact, thm% Ir.sizeSkipScale_between,
      thm% Ir.stepLead_between, thm% Ir.stepLead_ratio_between, thm% Ir.skipRowOf_between,
      thm% Ir.paraStep_paraAt_exact, thm% Ir.paraAt_text,
      thm% HtmlDoc.stepLineHeight_between,
      thm% Ir.liftParaStep_text, thm% HtmlDoc.deck_root_between,
      Pin.tier "rhythm" "article-steps/step-footnotesize.within",
      Pin.tier "rhythm" "slides-steps/step-small.within"]
    accept := ["a ten-point deck rebuilt in both artifacts beside the reference engine's: body, small-size and code lines at its line pitch",
      "the same deck's slides measured in a browser: line pitch and paragraph gaps at the page's on the stage, and a code slide that fits its page fits its stage",
      "a heading, a document title and a frame title set in a named size, wrapped across lines: their lines in the size's own proportion to their type, none solid; a frame title set in a smaller size keeps the title's own leading, as the reference engine's group around the inserted title does",
      "a venue style's own size ladder: each declared step's lines at the leading it declares, beside the reference engine's",
      "the same deck's slides with pauses measured in a browser: every paragraph gap the declared one through each step, as on the page"]
    state := .guarded "fa516a828a2a36549fc2a56f1e1cb4d138b3b934" .before .author },
  { id := "R133", date := "2026-10-10"
    what := "A slide of running prose read worse than the reference engine's: justified and hyphenated where the slide class sets its text ragged right"
    pins := [check% Tests.LineRhythm.raggedFrameChecks,
      check% Tests.LineRhythm.centredRuntChecks]
    accept := ["a ten-point deck's closing prose slide beside the reference engine's page in both artifacts: ragged right, unhyphenated, at its leading",
      "the same slide's thirteen lines each ending at the reference engine's word, as its ragged right fills every line first"]
    state := .guarded "2b555dcfbad3803d9ebbb3d54fdc8571b36e9ea7" .before .author },
  { id := "R134", date := "2026-10-10"
    what := "A beamer deck's build printed one warning per listing for a listing option the engine does not honour, while other repeated losses printed once with a site count: the option's emitter named no subject, and a repeat in the same words with no subject printed at every site"
    pins := [check% Tests.DiagFold.foldChecks, check% Tests.DiagFold.subjectDoorChecks,
      thm% Diag.foldRepeats_sum_exact, thm% Diag.foldRepeats_line_exact,
      thm% Diag.foldRepeats_wording_between, thm% Diag.foldRepeats_visible_inj]
    accept := ["twenty-one assertions fail with the fold's subjectless and wording arms and the listing and siunitx subjects reverted onto the recorded commit, the census-keyed fold standing: a listing option's one line and count at five listings, every listing arm's words keying its loss, a siunitx option's one line, a subjectless repeat's one line with its werror, acceptance and porcelain counts, a loss's second wording, which the census-keyed fold hid, a loss that opens on a note, whose warning it hid, and the door scan naming twelve subjectless emissions of a counted code",
      "a presentation deck's build prints its listing option once with its site count and a repeated glyph fallback once, and its porcelain keeps every record, the sites summing to the records",
      "an invented document whose thousands of paragraphs each hold symbols its face lacks prints one line per symbol"]
    state := .guarded "e942f189" .revert .author },
  { id := "R135", date := "2026-10-10"
    what := "Raw HTML in markdown had no decided policy across the two artifacts: harmless spellings were refused, and a refused disclosure was accounted twice"
    pins := [check% mdHtmlAccountsChecks, check% htmlTwinChecks, check% refusedDisclosureChecks,
      check% cellBreakChecks, check% mdRawHtmlHelpChecks, check% mdTwinBreakChecks,
      check% markdownInputHtmlChecks, check% disclosurePrintChecks,
      check% markdownHtmlChecks, check% mdSurfaceChecks, check% pdfDestinationChecks,
      thm% LeanTex.Core.Md.desugar_vocabulary_mem, thm% LeanTex.Core.Md.textRaws_covers]
    accept := ["one hundred twenty-four guard assertions fail with the fix reverted, the reader, the disclosure's output scoping and the twin's break spelling together: ninety-three twin-spelling, eight help, seven refused-disclosure, four print and inclusion scoping, four tex twin round-trip, three included-markdown and three site-accounting assertions, the accounts family and the diagnostics golden",
      "fifteen twin round-trip assertions fail with the twin's break spelling alone reverted: a heading split in two, and the next line of a list item or a quotation refused as lazy",
      "with the refusal's earlier help restored, its assertion fails at all eight sites, and its blank-line advice entered as a fix splits the block it was shown in at four",
      "every raw HTML element of a generated family of names, shapes and sites is lowered or refused once, at its own position",
      "the CommonMark verdicts and tier are unchanged: no spec case holds a vocabulary spelling",
      "thirty guard assertions fail with the review's corrections reverted and the leading-break records removed: fifteen twin round trips, where text spelling a tag or a reference read back as that construct and code read back with its escapes; nine scope assertions, where a build of the markdown twin named no lost collapse; three refused summaries, each a second refusal of its disclosure; and three leading-break records",
      "one hundred fifty-nine guard assertions fail on the branch's tree before the fourth review with the whole fix reverted",
      "fourteen fail on the rebased tree with the corrections for the third review reverted: three refused summaries whose tag spans lines, each refused a second time at its disclosure; a break in a heading or a table cell read back as a space, in six twin round trips and three heading twins; an empty target or its id dropped from the twin, its link left without a page anchor, twice, and a tex label written as no target; and a note inside code-set text copied into the code, its mark lost",
      "eighteen more fail before the corrections for the fourth review: seven where a table cell's break set its lines flush left in a right or centred column, in a column as wide as the cell's words on one line, and eleven twin round trips, where a run ending on a break, alone or before text, in a list item or a quotation, wrote the break as a backslash outside the run, which a block's end reads as itself",
      "thirteen more fail before the corrections for the fifth review: six where a tex cell without a break was set as broken lines without its hyphenation, a word overfull or a pair wrapped, and seven where a tex run's closing break was written as `<br>` before a word, through an enclosing run or a wrapper, or in a heading or a cell, so its emphasis read back as asterisks; after them every corpus document and both presentation decks ship byte-identical PDF and HTML to the base's",
      "a long markdown report of several hundred disclosures and two presentation decks ship byte-identical PDF and HTML; the report's PDF build names no lost collapse while its HTML and markdown builds name every one, and its markdown twin is its own twin"]
    state := .guarded "3d122253" .before .author },
  { id := "R136", date := "2026-10-10"
    what := "a colour declared inside an environment reached every page after it: a title page's own ink on its own ground stayed in force, so the body text after it shipped near the page's own colour in both artifacts and read as blank pages"
    pins := [thm% Elab.texGroup_scope_id, thm% Elab.elabBlocks_env_scope_id,
      thm% Elab.elabBlocks_group_scope_id, check% Tests.GroupScope.groupScopeChecks]
    accept := ["a private document's own build: on the base tree most of its text could not be read against its ground in either artifact, its PDF pages showing only explicitly coloured runs; on the fixed tree every text node reads, and its pages show their headings, lists and paragraphs where the reference engine's do",
      "the class the report belongs to, measured under lualatex on invented probes and held by the guards: a colour declared inside a brace group, a begingroup or bgroup pair, an environment, a frame or a list reached text after the group's end; a Beamer colour set inside a frame reached the next frame; a block-level language switch reached text after its environment; a colour or size declared in a paragraph's own text stopped at the paragraph's end where TeX keeps it to the group's end, past list items too; and the command that restores the document's normal colour was unknown",
      "review of the fix: a colour declared in a paragraph moved the display or list after it, and a display after a list, quote or theorem that coloured its text, by two to twelve points; side-by-side boxes shared one colour state; the normal-colour command ignored a colour set in the preamble; a palette name carried past a paragraph outranked every later colour; a declaration that ended a paragraph dropped the colour carried out of it; a group's end dropped the Beamer colours a global palette entry derives; and an epoch-heavy document's HTML grew with the square of its groups; twenty-five assertions fail on the reviewed tree and hold now, and the space after a colour command no longer sets a second space",
      "second review: small caps set after an italic dropped the slant, a URL face stopped at the first paragraph end inside its group, carried sizes and emphasis grew the HTML with the square of their paragraphs, text after a colouring group shipped a concrete ink where the page's own text reads the stylesheet's, a colour declared before a group that restores its lengths stopped at that group, a page colour inside braces or a begingroup pair never reached its page, and a group after a colour command took the colour alone; twenty-one assertions fail on the reviewed tree and hold now"]
    state := .guarded "e5233428" .before .author },
  { id := "R137", date := "2026-10-10"
    what := "A frame title on a moloch-style deck started at the text margin, where the slide class insets it from the paper's edge by its title bar's own margin"
    pins := [check% Tests.FrameGeometry.titleInsetChecks]
    accept := ["six assertions fail with the fix reverted onto the recorded commit: both title steps' start on the page, against the reference typesetting, and in the web deck's bar",
      "a presentation deck's frame titles start within half a point of their reference typesetting on the page and in the web deck, where they stood eighteen points right"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R138", date := "2026-10-10"
    what := "A section page's progress bar on a moloch-style deck stood shorter than the slide class draws it, a standout frame taking a number and advancing the count the bar and the footlines read, and the web deck set the section page's title and bar in a narrower measure than the page"
    pins := [check% Tests.FrameGeometry.standoutNumberChecks,
      check% Tests.FrameGeometry.sectionMeasureChecks, check% slideLabelChecks]
    accept := ["forty-five assertions fail with the fix reverted onto the recorded commit: the footline numbers on the page and in the web deck, the section page's bar on both, the web section page's measure, and forty of the web deck's frame labels, which named a standout frame by a number",
      "a presentation deck's section-page progress bars and footline numbers match their reference typesetting on every page, where the bars stood a tenth short and every number after its first standout frame ran one ahead; its web section pages' titles and bars stand where the page sets them, where they stood twenty points right",
      "the section pages' vertical place is R120's guard (Tests.FrameArea.checks)"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R139", date := "2026-10-10"
    what := "Under the default theme a titled frame's first line stood several points further below its title than the slide class sets it, and the web deck kept no title box"
    pins := [check% Tests.FrameGeometry.titleOpeningChecks,
      .tier "rhythm" "slides-default/frametitle-body.near",
      .tier "rhythm" "slides-default/frametitle-block.near"]
    accept := ["two assertions fail with the fix reverted onto the recorded commit: the first line's place below the title on the page, and the web deck's title box",
      "the rhythm tier's default-theme frame-title rows stand within three points of their reference, where they stood six and a half points deep"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R140", date := "2026-10-10"
    what := "A centred frame split its leftover space evenly whatever its theme, where the slide class sets the body two fifths of the way down and only a moloch-style theme centres it"
    pins := [check% Tests.FrameGeometry.centreSplitChecks, check% vdistChecks,
      thm% vdist_shares_agree]
    accept := ["five assertions fail with the fix reverted onto the recorded commit: beamer's split on the page and in the web deck, the web deck's moloch shares in the frame glue's units, a standout frame's even spacers under beamer's keys, and the page's centred share two fifths of the way down",
      "an untitled centred frame under either keys stands its lines within a tenth of a point of their reference typesetting on the page"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R141", date := "2026-10-10"
    what := "A vertical fill in a frame took all of the frame's leftover space on the page, where the slide class shares it with the frame's own fill glue of its order and sets a fill inside a box at its natural height, a breakable centred frame split its leftover as an unbreakable one does, and the web deck rendered nothing for a fill"
    pins := [check% Tests.FrameGeometry.vfillChecks, check% Tests.FrameGeometry.nestedFillChecks,
      check% Tests.FrameGeometry.fillCarrierChecks, check% Tests.FrameGeometry.fillCensusChecks]
    accept := ["seventy-six assertions fail with the fix reverted onto the recorded commit: the lines around a fill on the page and the web deck's spacers and carriers under either keys, at the frame's top level, after an overlay pause, between list items and descriptions, in a group, a figure, a table, a link, a backend's share, an alternation and a block's declared template, in a block and a column, and in a breakable frame, a breakable centred frame's own split, the fills the page closes on in a block and a column, and the web build naming the fills it cannot grow",
      "a top, centred and bottom frame holding a fill stand their lines within a tenth of a point of their reference typesetting on the page, under either keys"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R142", date := "2026-10-10"
    what := "An alerted word set bold where the slide class sets it in the body's face in its theme's alert colour, and in a deck naming no theme it took no colour at all"
    pins := [check% Tests.FrameGeometry.alertChecks]
    accept := ["six assertions fail with the fix reverted onto the recorded commit: the moloch word's face on the page and its emphasis in the web deck, and in a deck naming no theme the word's face and colour on the page and its emphasis and colour in the web deck",
      "a presentation deck's alerted words set in the body's weight, coloured"]
    state := .guarded "e841ab4a" .revert .author },
  { id := "R143", date := "2026-10-10"
    what := "In highlighted listings a proof hole and a raised not-implemented error shipped in two colours, though a deck's theme gives both its one alert colour: every token type took its highlighting style's own colour and weight, no palette colour reached a listing, and the theme's redefinitions of the style's macros run only under a TeX engine"
    pins := [check% codeRoleChecks, check% listingStyleTableChecks, check% shellReplyChecks,
      thm% Listing.brush_role_exact, thm% Listing.paint_role_exact,
      thm% Listing.paint_declared_mem, thm% Listing.paint_derived_exact,
      thm% CodeColor.resolve_style_exact, thm% CodeColor.derive_none_opens,
      thm% CodeColor.tone_meets]
    accept := ["thirteen assertions fail on the tree before the fix: ten artifact ones, in PDF and HTML alike — in the default style the hole set in the style's error red and the raised error in its bold exception red, in the friendly style the raised error took the keywords' green, and under an invented palette, its error colour named by role or derived, both kept the style's colours — and the formatcom line, the two builds a declared style changes no page of, and that style's naming",
      "a presentation deck's hole and not-implemented slides, in PDF and HTML: both markers in the deck's alert, every other listing token in a colour its palette derives, minted's formatcom one info line over its listings where each listing had warned of an unknown option, and its declared style, which now colours no token there, named once"]
    state := .guarded "9ec36474" .before .author },
  { id := "R144", date := "2026-10-10"
    what := "A frame not declared breakable that ran a point or two past its page shipped a continuation page holding its last line, where the slide class sets it on its one page, and its loss stated only the first line past the page; a declared squeeze was named and ignored, the web deck scrolled a frame the page fitted by shrinking its lists' glue, and a breakable frame left a block's title alone at a page's foot"
    pins := [check% Tests.FrameFit.overhangChecks, check% Tests.FrameFit.squeezeChecks,
      check% Tests.FrameFit.breakableTitleChecks, thm% Ir.frameFit_between,
      thm% Ir.frameFit_id, thm% Layout.frameFit_accounts, thm% Layout.runFitted_accounts,
      thm% Layout.runFitted_projects]
    accept := ["twenty assertions fail with the engine reverted onto the recorded commit: a frame, two overlay steps, a picture and an alternation's shown side a point or two past their text area each shipping a page per step and named by W0400; a far frame's loss stating its whole overrun, one baselineskip more for one more line; a frame a point past its page below a footnote continuing; the declared squeeze read, its items a baselineskip apart; the web deck squeezing the frame the page shrank, with its stage's class, item gap and trivlist rule; the breakable frame's block title on its body's page; and W0400's witness and both codes' golden blocks",
      "the in-repo corpus builds to the same PDF and HTML bytes, its one frame past its page now stating its whole overrun, and a private reference deck builds to the same bytes in both artifacts",
      "on invented probes the overrun a continuing frame's loss states is the slide class's own overfull report, apart from the text area's distance from the slide class's (R146)"]
    state := .guarded "426db813" .revert .author },
  { id := "R145", date := "2026-10-10"
    what := "a frame declared to shrink is set as one not declared so, where the slide class sets it again at a wider measure and scales it down to fit its page"
    pins := []
    state := .owed "the beamer frame layout owner: a declared shrink set at the measure over its factor and scaled by it" ["frameShrinkChecks"] },
  { id := "R146", date := "2026-10-10"
    what := "a slide frame's text area ends above the slide class's: about two and a half points under the moloch-style theme at ten points, by a frame-number footline the default theme does not draw, and by several lines where the footline is empty or a running foot owns the foot, whose frames take the slides margins; and its lines stand a fraction of a point further apart; so a frame the slide class fits overruns here, and one it sets a point overfull continues"
    pins := []
    state := .owed "the beamer frame layout owner: the frame's text area and line pitch as the slide class measures them" ["frameTextAreaChecks"] },
  { id := "R147", date := "2026-10-10"
    what := "declared colours shipped repainted toward a contrast target, a role's ink on the page and on a frame-title bar, a mix of two named colours and a highlighting style's token colours among them, and a deck's stage-size text was held to the small-text ratio, so a three-colour palette's accent was reported as illegible on the page it was designed for"
    pins := [check% Tests.DeclaredColors.checks, check% listingRoleEpochChecks,
      thm% Elab.completePrepared_doc_exact, thm% Listing.paint_declared_mem,
      thm% Contrast.defaulted_ink_cannot_escape]
    accept := ["eleven of the guard's assertions fail on the tree before the fix: the role's warning named a repair, the pair on the frame-title bar was not reported once naming the bar, the mix and the style's token colours shipped repainted in both artifacts and were noted as realized rather than reported, a document's page text at 3.95:1 drew no warning, and a declared focus ring short of non-text's 3:1 drew none",
      "a presentation deck's declared three-colour palette ships its exact values in both artifacts, as its lualatex build does, its accent passing at the stage's size and its highlighting style's comment colour reported once"]
    state := .guarded "d16aafc8" .before .author },
  { id := "R148", date := "2026-10-11"
    what := "A function's name shipped in one colour where a listing defined it and in another where it was called, and a name read differently from one language to the next: a definition's own name took the name role, while its uses and every name a Lean listing defines set in the ink"
    pins := [check% definitionNameChecks, check% codeRoleChecks,
      thm% Listing.paint_role_exact, thm% Listing.brush_role_exact]
    accept := ["twenty-four of the guard's assertions fail on the tree before the fix, in PDF and HTML alike, under a style and an invented palette: a Python function's and class's definitions set apart from their call, their use, a parameter and the Lean function, and a builtin sharing the definitions' paint",
      "a presentation deck's Python function names at their definitions and their calls, a test function's name, and a Lean function at its definition and its recursive call, all in the identifiers' ink in PDF and HTML"]
    state := .guarded "dbbfba91" .before .author },
  { id := "R149", date := "2026-10-11"
    what := "a listing's code colours declared by xcolor definitions of the code roles' keys, the one spelling both engines compile, reached no listing: its tokens shipped the colours the palette derives, with nothing reported, where the same declarations had coloured them before the colour registry"
    pins := [check% Tests.ColorNames.xcolorCodeRoleChecks, thm% Ir.Palette.defineXcolor_role_exact,
      thm% Ir.Palette.defineXcolor_design_id]
    accept := ["six of the guard's assertions fail on the tree before the fix: the two roles undeclared, the keyword and the literals in derived colours on the page, the page and the HTML body apart from the palette spelling's, and the stylesheet's two roles not the declared colours",
      "a presentation deck whose theme declares its code roles by xcolor definitions ships its declared code colours in both artifacts"]
    state := .guarded "dbbfba91" .before .author },
  { id := "R150", date := "2026-10-12"
    what := "a build wrote its artifact over the file it was built from: a markdown source built onto its own name was replaced by its markdown twin, and a markdown twin declared under the source's name, an include's, the bibliography's, an image's, a face's, the stylesheet's or the icon's replaced that file"
    pins := [check% Tests.publicationInputChecks, check% Tests.overwritePlanChecks]
    accept := ["run against the binary built from the tree before the fix, thirty of the guard's assertions fail: each of fifteen destinations, among them a link to the source, a link to its directory, a hard link of it, a face the run's font directory holds, and the stylesheet and icon a build of any formats declares, is published over the file the build read, which then differs; the destinations that are no input publish as before"]
    state := .guarded "1f801005" .before .author },
  { id := "R151", date := "2026-10-12"
    what := "an output name with no format's extension was refused on plain standard error, outside the porcelain stream a tool reads and with no code, and the refusal named the PDF and HTML extensions but not the markdown one"
    pins := [check% Tests.outputNameChecks]
    accept := ["run against the binary built from the tree before the fix, three of the guard's assertions fail: no porcelain record carries the refusal, the rendered refusal bears no code, and no refusal lists the markdown extension"]
    state := .guarded "1f801005" .before .author },
  { id := "R152", date := "2026-10-12"
    what := "a long markdown report's build printed an overfull-line warning for every line of its code blocks, each header quoting a fragment of that line's code, beside unlocated re-flow warnings whose words changed at every site: a census key that told sites apart split one wording into a line per site, a header quoted whatever text stood at the site, a site's page, frame and measure stood in the words, and a build that shipped no PDF printed the PDF page's overruns"
    pins := [check% Tests.DiagFold.foldChecks, check% Tests.DiagFold.reflowAccountChecks,
      check% repeatFoldChecks, check% diagVoiceChecks, check% Tests.diagnosticListingOriginChecks,
      check% Tests.diagnosticLiteralOriginChecks, check% diagnosticLayoutOriginChecks,
      check% diagnosticFormatChecks, check% diagnosticFontScopeChecks,
      thm% Diag.foldRepeats_line_exact, thm% Diag.foldRepeats_visible_inj,
      thm% Diag.Spelling.ofWritten?_exact]
    accept := ["ninety-four of the guards' assertions fail with the fix reverted onto the recorded commit — the fold keyed by census subject again, a site's particulars back in its words, every written word a header and the place codes' headers back, the re-flow unlocated and keyed by its index, acceptance read off the delivered severity, and the page's losses unscoped: a wording whose census keys tell its sites apart printed once per site, the re-flow's sites, its output scope and its accepted count, fifteen witnesses written twice printing a line per site, twenty-eight voice and diagnostics-golden assertions, the listing, literal and layout origins' headers, the record format's headers and the font scope's",
      "an invented markdown document whose code lines overrun prints one overfull warning carrying their sites, its header ending at its location, where the tree before printed one per line quoting each line's code",
      "a long private markdown report built to HTML in a font environment with no monospace face prints no overfull line where the tree before printed twenty-five, and built to PDF prints them as one line carrying their sites"]
    state := .guarded "0ec6b963" .revert .author },
  { id := "R153", date := "2026-10-12"
    what := "A block template's rule beside its title stood off the title's capitals in both engines, spanning the paragraph skip its box opens on; the template that centres it, reading the box's lines, the title font's cap height and its leading in a dimension expression and length registers, was not read, and its blocks set as beamer's default boxes"
    pins := [check% Tests.BlockTemplate.checks, thm% Layout.edgeLinesSpan_centred_exact,
      thm% Ir.BlockMetric.halfLeading_centred_exact]
    accept := ["thirty-three assertions fail on the tree before the fix and hold after, over an invented probe of five frames: the template named and its blocks set as beamer's default boxes, no rule beside its ten titles and every title and body line away from the reference engine's, a reach's native spelling unread, and the readings of a box's height alone and of lines no strut bounds not named for them; on this tree every rule's place and size is within 0.002 points of the reference engine's, titles whose ink passes their struts, two title lines a skip apart and last lines deeper than their struts among them, each rule beside lines struts bound centred on its capitals exactly in the PDF and within a device pixel in Chromium, whose header stands as low as the PDF's title for the rule's rise and keeps the body as far below a rule deeper than its box",
      "a presentation deck whose theme centres its block rules on the titles' capitals ships them centred in both artifacts, as its lualatex build does, every other pixel of the deck unchanged"]
    state := .guarded "bc2adb38" .before .author },
  { id := "R154", date := "2026-10-12"
    what := "a picture's baseline given as a coordinate whose y carries units, such as (0,5pt), read that y as so many units of the picture's y vector, scaled by the picture's scale, which pgf reads the coordinate without, so the picture stood away from where the length 5pt stands it"
    pins := [check% boxPosRowChecks]
    accept := ["three of the guard's assertions fail on the tree before the fix: a coordinate whose y is in points, the same coordinate in a scaled picture, and the HTML picture's lift each stand the picture apart from the one whose baseline is that length"]
    state := .guarded "1f801005" .before .author },
  { id := "R155", date := "2026-10-12"
    what := "an environment the rewrite turns into a group, a title page, a language switch or a refused column form, opened right after a command and its braced arguments in the same paragraph was read as one more argument of that command: it stayed in the paragraph, a title page's page marks were named as an unknown command and a page break out of place, and a list inside failed the build"
    pins := [check% titlePageLifecycleChecks, check% environmentArgumentChecks]
    accept := ["thirty-two of the guards' assertions fail on the tree before the fix: after a link, a bold word and a forced line break, a title page recovers by an error and an unknown command and its pages are not those of plain words in the command's place; after a bold word and a link, with or without a picture opening the paragraph, a language switch or a refused column form around a list recovers by an error, and a language switch around two paragraphs loses its paragraph break", "with the place the rewrite keeps read as an environment by the in-sentence picture scan, six of them fail on the fixed tree: behind a picture, the sentence running on past the environment is not named as it is after plain words"]
    state := .guarded "1f801005" .before .author },
  { id := "R156", date := "2026-10-12"
    what := "the flate, image-plan and conversion caches keyed their answers by the release version, which every build of a release shares, so a rebuilt or replaced engine was served the answers an earlier engine stored, and a planted equivalent answer changed another binary's PDF"
    pins := [check% Tests.engineCacheChecks, check% Tests.engineIdentityChecks,
      thm% SlotRecord.lookup_exact]
    accept := ["on the tree before the fix, the guard's second copy of the binary reads the image plan the first copy stored, its images phase reporting the plan cached; the guard's plant, which writes the keyed slots of the fix, finds none there"]
    state := .guarded "1f801005" .before .author },
  { id := "R157", date := "2026-10-12"
    what := "an HTML build given the math renderer flag published nothing: the page named the renderer as a script source, which the self-contained publication gate refuses, so every such build failed"
    pins := [check% Tests.mathBoundaryChecks, thm% HtmlDoc.math_boundary_contract,
      thm% HtmlDoc.math_boundary_floor_exact]
    accept := ["run against the binary built from the tree before the fix, the guard's two end-to-end assertions fail: the HTML build with the flag is refused, and no page carries the renderer"]
    state := .guarded "1f801005" .before .author },
  { id := "R158", date := "2026-10-12"
    what := "the Bulma stylesheet mode was documented as styled by a host page's framework sheet, while publication refused a page declaring no framework sheet of its own, and the refusal named no declaration to write"
    pins := [check% htmlContainedCliChecks, check% Tests.bulmaSheetChecks]
    accept := ["run against the binary built from the tree before the fix, one of the guard's assertions fails: the refusal of a Bulma page with no declared sheet does not name 'stylesheet = ...'"]
    state := .guarded "1f801005" .before .author },
  { id := "R159", date := "2026-10-12"
    what := "a wrapped line of code split an assignment operator across two lines, its colon ending one line and its equals sign opening the next: a wrap fell between two characters of one token"
    pins := [check% Tests.MarkdownCode.codeTokenWrapChecks, check% Tests.MarkdownCode.markdownCodeChecks]
    accept := ["five of the guards' assertions fail with the fix reverted onto the recorded commit: an operator or a fallback token parted in each of eleven Lean, Python and plain fences, after a space and inside a run wider than the line, where the sweeps stand it at the measure's end; a character literal the Lean highlighter splits into runs parted at its quote; the last fitting space losing to a later token break in a Python and in a plain fence; and a declared listing's wrapped lines set apart from the units a LuaLaTeX probe of the same invented lines keeps whole, a number's digits and a list's commas",
      "an invented markdown document's long Lean line wraps before its assignment operator, where the tree before set the operator's colon and equals sign on two lines"]
    state := .guarded "ce4db8b2" .revert .author },
  { id := "R160", date := "2026-10-12"
    what := "a markdown report's folded overfull warning named its first site on a code block's opening fence line, at the column a verbatim opener would end at, where the block had no info word: the code's characters stood one line early, and a block whose code opened on a blank line lost that line"
    pins := [check% Tests.MarkdownWarnings.markdownWarningChecks,
      .tier "commonmark" "Fenced code blocks.match", .tier "mdtwin" "cm.Fenced code blocks.reread-exact"]
    accept := ["on the tree before the fix one of the guard's assertions fails: a fence with no info word names its overrun on the fence's line, while the same fence with a language names the code's own line",
      "the CommonMark tier's fenced-code item rises by the case whose code opens on a blank line, and the markdown twin's reread of the same section by one"]
    state := .guarded "bc2adb38" .before .author },
  { id := "R161", date := "2026-10-12"
    what := "a markdown report built on macOS set its code in the proportional text face and named the loss, the document declaring no typewriter family: its text family had no designed companion the scan served, and the system's own monospace faces ship as font collections, which the scan skipped"
    pins := [check% Tests.MonoDefault.monoDefaultChecks, check% Tests.MonoDefault.fontCollectionChecks,
      thm% FontDb.monoFor_contract, thm% FontDb.monoDefault_mem]
    accept := ["fifteen of the guards' assertions fail on the tree at effc6b16 with the fix reverted, the assembly's markdown-only companion and a scan that lists no collection restored: the platform monospace filling the slot on either surface, the code's runs on the page and the HTML's typewriter stack and face, a tex document taking the companion, and a collection's faces found, cached, assembled and shipped",
      "the report's own HTML and PDF builds in a namespace whose fonts are a text family with no designed companion and one platform monospace: with the fix reverted the HTML named the typewriter slot and four overfull lines and set its code in the text face, and with the fix it names neither and sets its code in the monospace; on this Linux host's own fonts both builds are unchanged; macOS itself was not run, so Menlo's reach through its collection is inferred",
      "this supersedes R131's acceptance that a tex document declaring no typewriter face keeps the body family: it now takes the same default a markdown document does, and a document setting no typewriter run loads no typewriter face",
      "the review's guards: with a collection's member paths restored among a build's inputs, two assertions fail as the markdown twin is written over a collection the run's font directory holds; a document shipping its fonts sets the face it ships whatever the host holds, a picture's label and a formula's typewriter alphabet each load the default, and a directory naming one region again and again is refused"]
    state := .guarded "effc6b16" .revert .author },
  { id := "R162", date := "2026-10-12"
    what := "a markdown report's HTML build printed a warning carrying every one of its several hundred disclosures, that their collapse was not carried, where the page could ship each as the platform's own element: a disclosure shipped as a bold line and its body in every artifact"
    pins := [check% disclosurePrintChecks, check% htmlTwinChecks, check% markdownHtmlChecks,
      check% refusedDisclosureChecks, check% Tests.MarkdownTwin.markdownTwinChecks,
      check% htmlA11yChecks, check% Tests.LineRhythm.disclosureGapChecks,
      thm% Ir.disclosureSummary_text, thm% LeanTex.Core.Md.desugar_vocabulary_mem]
    accept := ["thirty-five of the guards' assertions fail with the fix reverted, the engine at the base of the recorded commit and its tests kept: eight print and inclusion assertions, where the page shipped no element, the twin wrote none and the HTML and twin builds named a lost collapse; twelve of the HTML vocabulary's, where a disclosure shipped as a bold paragraph and a summary with no text was read; six twin rows, where the open and the closed spelling shipped one page and named their collapse; three refused-summary assertions; and six twin round trips",
      "a long markdown report of several hundred disclosures builds its HTML with no warning where one warning carried every disclosure, each the browser's own element, closed as written, opening and closing on its summary and printing expanded; its PDF keeps its pages and its diagnostics",
      "the first review's guards: with the disclosure not read through at its foot, four gap assertions fail, the block after a disclosure ending on a list or a quotation standing a peer gap where it stands the list's space outside one; a disclosure in a list item names its loose list as CommonMark reads it, and a summary of characters drawn as nothing is refused and named unnamed",
      "the second review's guards, written to its probes and not on record failing: a closed disclosure's hidden body moves no gap on screen while paper reads every disclosure through, a list item opening on a disclosure keeps its marker on paper, and a disclosure whose body opens on a list or a quotation names its loose list"]
    state := .guarded "04a2ea83" .revert .author },
  { id := "R163", date := "2026-10-12"
    what := "inline code a slide's footer wrote with minted's inline command shipped as its arguments' text in the footer's face, the command unknown, its language a word and its braces gone; minted's inline settings were unknown too, a display listing written in an argument or on a line of text was set unhighlighted, and HTML set all inline code smaller than the text around it"
    pins := [check% Tests.inlineCodeChecks, check% Tests.inlineCodeRequestChecks,
      thm% Listing.inlineCode_source_exact]
    accept := ["forty-five of the guard's assertions fail on the tree at ef5d2b87 before the fix: inline code named unknown in a paragraph, under a weight, a slant, a size and a colour, in a frame's footer, its title and a block's title; its sizes under minted's settings; a definition's parameters in its code; the one-line display command; a listing written where LaTeX cannot set it; a misspelt lexer; and the stylesheet's shrink of inline code",
      "a presentation deck whose footer writes inline code with minted's inline command, its inline size left to the text around it: the footer's code ships at the footer's size, its keywords painted and its other tokens in the footer's ink, in both artifacts, every word of the footer within four tenths of a point of where the deck's own lualatex build sets it"]
    state := .guarded "ef5d2b87" .before .author },
  { id := "R164", date := "2026-10-12"
    what := "A block template that sets the body in a box its begin half opens and its end half closes, puts the body back unboxed where it stood and stands the body's part of the title's rule on the last baseline — one rule beside the whole block — was not read, and its blocks set as beamer's default boxes; such a rule had no native spelling, no place on the page past the title's lines and none in the web page, and the template's own macros named losses of their own"
    pins := [check% Tests.BlockTemplate.checks, thm% Layout.edgeLinesFrom_abuts_exact]
    accept := ["sixty-six assertions fail on the tree before the fix and hold after, over an invented probe of four frames — paragraphs, a list, a display alignment, a large title, a picture, an untitled block, a title alone and a listing — and its variants: the template named and its blocks set as beamer's default boxes, no rule beside its nine titled blocks and their lines away from the reference engine's, the native spelling of a rule beside the whole block unread or refused for another reading, the templates that would move a line or the rule refused for other readings than their own and those that set the body back as TeX does read otherwise, the web page's rule ending short of a nested block's skip below, a brace's line end read as no space, and the template's own macros naming losses at their definitions; on this tree each rule is one, within 0.002 points of the reference engine's from 9.569 points above its title's first baseline to its depth below the block's last, every line where the title's rule alone leaves it, and in Chromium the web page's rule ends within a device pixel of the PDF's",
      "a presentation deck whose theme runs its block rules over the whole block ships them so in both artifacts, as its lualatex build does, every one of its lines where the title-only rule left it",
      "the second review's probes, run as documents through the engine of the tree before its answer: nine read otherwise than lualatex sets them — a line end after a brace before the rule, in the template or in a macro's text, a starred colour use with no channel before it, and a peel run twice through a macro the expansion leaves for the run each read as one rule where lualatex sets two pieces or leaves items above the rule; a flag the preamble sets after the templates and a template macro it redefines there read as at their definitions; a flag the body changes before a block unnamed; glue after the rule refused; and the web page's rule beside a block ending in a block whose skip below is in ems ending that em short"]
    state := .guarded "bcfef652" .before .author },
  { id := "R165", date := "2026-10-12"
    what := "a declared line that re-flowed and still ran past the measure drew a re-flow warning and an overfull warning per overrunning line, one construct accounted twice, where the re-flow can say the overrun"
    pins := [check% Tests.DiagFold.reflowAccountChecks, check% siteAccountingChecks]
    accept := ["twelve of the guards' assertions fail with the fix's behaviour reverted onto the recorded commit, its records kept: no re-flow saying its overrun, carrying it or naming where it opens; an overfull warning for each line a re-flow accounts for, so the page's overruns count twice, the log and the HTML and PDF builds print it on a line of its own, accepting the re-flow leaves it a warning and an acceptance of the overfull warning reads stale; a paragraph's re-flowed lines and their overruns as more than one diagnostic; overlay steps that measure one declared line apart, that differ in whether it runs past, or that re-flow different declared lines, each drawing a record of their own; and a macro's re-flowed line that runs past drawing an overfull warning beside its re-flow"]
    state := .guarded "373b2f34" .revert .author },
  { id := "R166", date := "2026-10-12"
    what := "a build printed a warning line per site for losses whose words stated a site's particulars, a byte offset, an alignment row, a data record's index, a count or a measure taken there, so one loss printed as several; the witness check repeated identical content at one site and could not see them"
    pins := [check% repeatFoldChecks, check% diagVoiceChecks, check% inputDecodingChecks,
      check% weightSubstitutionRecordChecks]
    accept := ["on the tree before the fix, the guards as they stand after the first review, forty-one of their assertions fail: two where the data warning's witness written again at another site prints a line per site, with and without its sources; twenty-five where twenty-one codes' witnesses state a number outside what they quote; twelve of the input decoding's, where a file's warning stated an offset in its words and two files' losses folded to one line naming neither; and two where two weights a family lacks, served by one face, printed two lines whose words named each weight",
      "the first review's guards: two weights served by one face keep a record each through the font assembly and fold to one line; a covered form's ratio is its detail; a boundary picture's missing face has one wording per reason, each with its remedy; each file's byte-level loss names the file; the codes whose witness cannot repeat are a baseline read in both directions, each with its reason; and the number lint reads a quote before a possessive and an apostrophe inside double quotes",
      "the second review's guards, written to its probes and not on record failing: located and unlocated overfull lines laid out together both reach the log's lines, the unlocated lines' one record in words of its own, and two environments' ragged rows each warn in their own words"]
    state := .guarded "fb46f760" .before .author },
  { id := "R167", date := "2026-10-12"
    what := "an undeclared typewriter slot set code in the text face where the host held a monospace without italics, in the host's monospace where a tex document's own TeX distribution held lualatex's Latin Modern Mono shapes, and proportional in a document shipping its text fonts on a host with a monospace"
    pins := [check% Tests.MonoDefault.monoDefaultChecks, check% diagVoiceChecks,
      check% Tests.MonoDefault.faceKeyAgreementChecks,
      thm% FontDb.monoPick_contract, thm% FontDb.latinModernMono_contract,
      thm% FontDb.servesMono_contract]
    accept := ["twenty-five of the guards' assertions fail with the fix reverted onto the first review's answer, e8e84d86, a typewriter default again requiring every corner, read from a document's own faces alone and never from lualatex's shapes, with its old help: the note's driver probe, witness and golden block, and the help's; the help naming Latin Modern Mono and both remedies; a font-shipping document's slot from the host after its own faces, and its shipped upright italics; a family served upright only in either surface, on the page and on the web; the note named exactly where italic code is set, a listing's comment among it, and its declared twin; and lualatex's shapes first beside a declared text face, last beside the engine's own, and upright alone",
      "the first review's guards: with its fixes reverted onto e8e84d86, thirteen assertions fail: a document setting no italic code named in three, a family holding one italic of two served in six, a document on the engine's own text face taking lualatex's shapes before the platform list, lualatex's upright shapes alone refused in two, and a shipped monospace's italics read from the host",
      "on this host, against lualatex over one invented probe: a tex document declaring its text face embeds for its 10-point typewriter runs the four Latin Modern Mono faces lualatex embeds, and for a footnote-size run LMMono10-Regular where lualatex embeds LMMono8-Regular, the optical size recorded as pending work; a tex document on the engine's own text face, and a markdown document, embed DejaVu Sans Mono's four beside DejaVu Sans, where lualatex sets Latin Modern Mono beside its own Latin Modern Roman",
      "the second review's guards: with its fixes reverted onto the recorded commit, eighteen assertions fail: a heading's italic template and a KOMA heading font over code naming no note, and the template's declared twin standing apart from it; a template no element uses, an italic over empty code and a typewriter switch with nothing after it each naming one; the census disagreeing with the page on seven invented documents; a shipped monospace's note sending its author to install italics the host already holds; the help leaving out a family's italics; and a semibold run under lualatex's shapes set in another file than its nearest corner's",
      "sealed from the host's fonts, through the binary: a heading template's italic code names one note where its declared twin names each italic corner over the same page, a template no element uses and empty italic code name none, a shipped upright monospace's note names the document's font directory whatever the host holds, and a semibold run under lualatex's shapes ships in the Light family's bold, its weight named"]
    state := .guarded "86966b55" .revert .author },
  { id := "R168", date := "2026-10-12"
    what := "a markdown report's HTML code blocks wrapped their long lines at the browser's own break points: a line broke inside an operator such as `->` or a comment's `--`, and on a narrow page inside a name, where the PDF wraps at a space or between two of its tokens"
    pins := [check% Tests.MarkdownCode.htmlCodeAtomChecks, check% Tests.MarkdownCode.codeScriptWrapChecks,
      .tier "htmlreader" "feature.chromium.pass"]
    accept := ["all twenty-four of the guard's assertions, as first written, fail with the fix's HTML emission reverted onto its commit: no token of eighteen invented plain, Python and Lean lines held on one line, no listings unit held or parted at a break opportunity in three declared listings, the stylesheet without the atom's rule, the wrapping block without its declaration, and a fence's arrow beside inline code unheld",
      "the browser oracle's code-wrap judge, run in Chromium on the code fixture's page built with the fix's emission reverted, finds a wrap inside a comment's `--` at 360 px and two inside names in print at 480 px; on this tree every wrap of the fixture's four code blocks falls at a space or between two tokens, at 320, 360, 480, 600 and 900 px on screen and 480, 600 and 794 px in print, and the oracle's controls fail the judge once the atoms are released and once two units stand unmarked",
      "the first review's guards: twenty-four assertions fail with its answer's behaviour reverted onto the recorded commit, its guards kept — a Japanese comment, a Thai and a Korean string with no space, read as one token, running past the measure on the page and held whole on the web page, in a fence and in a declared listing; three invented lines in each of three languages holding each fallback token where a stretch between two spaces stands whole; a fence's arrow held as an atom where its stretch is; a token wider than any line held; and a run held whole wrapped in an element of the page's own",
      "the browser oracle's paper judge, Chromium printing on Letter and pdftotext reading it back, run on its control page built by the binary of the tree before the answer: the page runs 486 px past the printable width and 37 of its letters miss paper; built on this tree it prints whole at its own scale, and a held atom wider than the sheet fails the judge",
      "the second review's guards: six assertions fail with its answer's behaviour reverted onto the recorded commit, its guards kept — a breaking listing's Japanese, Thai and Korean lines marking a break between two of their characters, Thai and Lao numbers parted digit by digit, every held unit held in every box, and the stylesheet without the rule a narrow box releases its longer units by",
      "the browser oracle's controls, run in Chromium on the engine's page of a breaking listing in a box a fifth of the line wide, beside prose and before a wider box, and of a breaking Thai listing: built by the binary of the tree before the second answer, its boxes run 202 px past themselves at 600 and 900 px and 186 px on paper, where the page prints at 92 percent, and its Thai parts inside words at 320, 360, 600 and 900 px; built on this tree every line stays in its box and the Thai parts only where the browser's segmenter finds a word, at 480 px too, and a held atom in a narrow box beside prose and a Thai line parted between its letters fail the judges"]
    state := .guarded "35a51d50" .revert .author },
  { id := "R169", date := "2026-10-13"
    what := "a palette generated from a brand's few colours left its code mostly in the ink: under an ink with no hue of its own, a listing's keywords and names set in the ink, and under an ink with one, keywords and names shared one colour, so only literals, comments and errors stood apart"
    pins := [check% seededCodeChecks]
    accept := ["eighteen of the guard's assertions, as the first review left them, fail on the tree at 1805d55c before the fix: for a black ink beside a yellow accent, a neutral ink beside a magenta one, and the black ink beside a declared literal, keywords and names in the ink, and beside a declared keyword its names, showing no hue, the web page painting no colour for them and the export a TeX build reads defining none; and for a violet ink beside an orange accent, keywords and names in one colour, their hues not apart",
      "the first review's guards: with its answer reverted onto 34b7ad87, three assertions fail: keywords planned over a literal its own key declares, 13° from it, names over a declared keyword, 20° from it, and two inks a channel step apart setting names in hues 132° apart, where equal arcs fell to rounding",
      "the second review's guards: with its answer reverted onto 04961d69, four assertions fail: a literal planned over a keyword its own key declares, a degree from it; names and keywords both shipping a name's declared colour; and a literal shipping an error's declared colour"]
    state := .guarded "1805d55c" .before .author },
  { id := "R170", date := "2026-10-13"
    what := "beamer's `only` overlay command covered its argument on the steps its selector does not select and kept its space, as `uncover` does, where beamer typesets the frame there as if the argument were not written: a frame whose steps swap blocks by it stood every step at the height of all of them and continued on further pages, and an unnumbered formula holding it was set as its source text, selectors included"
    pins := [check% overlayOnlyChecks, check% Tests.LineRhythm.onlyGapChecks,
      check% overlaySetChecks, check% overlayContractChecks, check% overlayInputChecks,
      thm% HtmlDoc.altPairNodes_floor_contract, thm% Ir.carrierDisplays_text]
    accept := ["one hundred and seventy-six of the guards' assertions fail with the fix reverted onto the commit answering the first review: one hundred and five of the reading guard's — every step whose selector leaves the argument out kept it on the page and in the web page's snap, inline, as paragraphs, around a display, a list or a paragraph break inside a paragraph, as a next token, a control word and the starred onslide, in a frame's title, a block's title and a caption, an item and a cell, a list's item and a table's row, under a union and nested, and beside a document's own alt; a display, an unnumbered equation and an inline formula holding it named a loss and set as their text; the frame swapping two ten-line blocks continued on further pages; a block read per step showed later steps' text on the deck's floor; and an uncover opening an uncover set its display a line low — twenty-one of the screen guard's, every snap of eight frames standing its gaps or its opening and closing off its reading's, and fifty of the set, contract and input guards, which held the covering reading",
      "the first review's probes, run as invented frames through the binary of this tree and in Chromium: block and caption titles step their frame, an absent display or list leaves its paragraph whole, swapped displays stand where lualatex sets them, a document's own alt and only keep their meanings, a numbered formula and a picture keep the only they wrote in their one loss, and every snap of eleven frames opening, closing or swapping content by it, and of a frame opening on a user-written alternation, stands every word where the frame written with that step's reading stands it, where that alternation stood its content five pixels off",
      "a presentation deck whose frames swap content by it ships as many pages as its lualatex build, where it shipped more, each page the step lualatex sets there; one whose table cells it reveals ships each step's cells absent where lualatex leaves them out, its page count unchanged and lualatex's; two decks that never write it ship byte-identical PDF and the same HTML markup, their stylesheets grown by the rules that give an overlay carrier's opening to its first block; and the in-repo corpus ships byte-identical PDF, and the same HTML markup but in two fixtures: an overprint's readings stand side by side, and a list and a paragraph on a carrier opening their frame take its opening, as the frame written without the carrier does",
      "the second review's guards: twenty assertions fail with its answer reverted onto the recorded commit, its guards kept — a selector nested inside the argument past the outer one's steps, in a paragraph and in a formula, gives its frame no page there; a paragraph opening on a centring switch and one in a centred scope set their steps' pages off their readings'; a theorem's body is not read per step; with no snap state a paragraph read per step hides an argument a later step shows; sixteen readings nest each alternation inside another's group; on the screen a paragraph after a frame title or a blank line keeps the absent paragraph's opening, and a centred scope's paragraph read per step loses its opening strut; and a stage whose title holds an absent argument is named by its first step's words where the page with no snap state shows the argument",
      "the second review's probes, run as invented frames through the binary of this tree, under lualatex and in Chromium: a selector nested past its outer one's steps in a paragraph, a list, a frame's opening, around a display and in a formula, a centring switch opening a paragraph or a later one, a definition, a face switch inside a paragraph, a centred scope, a frame title and a theorem each give their frame lualatex's page count; and every snap of a frame opening on a nested selector, a centring or alignment switch, a centred scope, a frame title, a blank line, a theorem or a document's own alternation of paragraphs stands every word where the frame written with that step's reading stands it; a paragraph holding a face switch further in, kept as written, still parts at its absent display, and a formula holding another overlay command's selector keeps its only as written and its one page, where lualatex sets three"]
    state := .guarded "6f94e4e0" .revert .author },
  { id := "R171", date := "2026-10-13"
    what := "beamer's `visible` overlay command, and `onslide` with its plus modifier, which beamer defines as it, covered their argument on the steps their selector does not select, dimmed as `uncover` covers, where beamer sets the argument invisible there, its space kept"
    pins := [check% overlayVisibleChecks, check% Tests.LineRhythm.visibleScreenChecks,
      check% normalFontChecks, thm% HtmlDoc.hidden_script_gated]
    accept := ["ninety-eight of the guards' assertions fail on the tree before the fix, its guards added: on the steps its selector leaves out, the argument of every one of thirty-six invented frames, set in two face sets, shipped dimmed where the page showing it ships nothing in its place — a paragraph, an image alone, a list, a description, two tables, a numbered equation, a figure, a listing, a bibliography, a shaded picture, a block, a theorem, an image in a node, a block link, inline text, colour boundaries, ligatures, a formula, an inline image, a rule, a link, an underline, normal type, a footnote mark, an open selector, inside a cover, an uncover inside it, nested, a block title, a figure caption, a table caption, a title page, columns, inside a column and inside a block — a frame holding it in a block title, a caption or its title page kept one page, the web page's snaps showed it in eight frames, and normal type dropped the size, colour, link and underline in force",
      "forty of them fail on the branch's first cut, which painted the argument one invisible colour: a description, two tables, a numbered equation, a figure, a listing and a bibliography shipped the ink layout draws for them, an image alone on its line took a rule's spacing, a shaded picture shipped black, a block link kept its annotation, runs split at colour boundaries kerned and ligated as one, normal type shipped black and dropped the size, colour, link and underline in force, and a frame holding it in a block title, a caption or its title page kept one page and never showed it, in the web page as in the PDF",
      "fourteen of them fail on the first review's answer: that frame kept one page in both artifacts, and beamer's article mode lost the argument from the PDF, where lualatex and the web page show it",
      "the in-repo corpus ships byte-identical PDF but in the fixture writing it, and the same HTML markup, its deck stylesheets grown by the hiding rules; four presentation decks that never write it ship byte-identical PDF"]
    state := .guarded "6d66d873" .before .author },
  { id := "R172", date := "2026-10-13"
    what := "the suite's checks of a tool its budget ends failed under parallel load, and with them every agent's commit: they held the wall clock to a few seconds past a short budget, and a loaded host took longer"
    pins := [check% Tests.World.checks, check% Tests.processRuntimeChecks]
    accept := ["with the checks' process held stopped six seconds of every 6.1, the checks as b6e1a170 wrote them fail: the killed run, the hung version question and the runtime overrun each answer in about 6,100 ms against bounds of 4,000 and 5,200; the fixed checks pass under the same stalls, and eight suites run at once at a load average of 46 to 79 all pass"]
    state := .guarded "b6e1a170" .before .author },
  { id := "R173", date := "2026-10-13"
    what := "the landing tool read its help option as an agent name, taking the landing lock and writing a refused ledger row, as it did any lone option it does not read; beside a subcommand such an option became the name it acted on, and elsewhere it made a run directory before the usage"
    pins := [thm% Land.parseArgs_run_exact, thm% Land.parseArgs_unknown_exact,
      thm% Land.parseArgs_help_exact]
    accept := ["the landing tool's usage scenario fails against the tool built at b6e1a170 before the fix: the help option and its short form exit 2 having taken the lock and written a refused ledger row, and every unknown option makes a run directory; with the fix every scenario passes"]
    state := .guarded "b6e1a170" .before .author },
  { id := "R174", date := "2026-10-13"
    what := "a colour missing both as text and as the page ground was named once: whichever use came first silenced the other, and its warning counted both uses in its own words"
    pins := [check% Tests.ColorNames.missingBothWaysChecks]
    accept := ["the guard's thirteen assertions fail at b6e1a170 before the fix: in every order the second use is a note without its help, and the first warning counts two sites"]
    state := .guarded "b6e1a170" .before .author },
  { id := "R175", date := "2026-10-13"
    what := "a palette generated for a light page set its accent's text, its code and its chart series above the floor their use owes, dark and near one another, so on the paper they read as dull near-blacks barely apart from the ink or from each other; a yellow accent darkened into a disliked olive; and a chart's series stood apart for typical colour vision alone"
    pins := [check% Tests.PaletteFloor.floorChecks, check% Tests.PaletteFloor.fillChecks,
      check% Tests.PaletteFloor.regionChecks, check% seededCodeChecks, check% Tests.SeedSeries.seriesChecks,
      check% Tests.AlertMark.containerChecks, check% Tests.AlertMark.markChecks,
      check% Tests.AlertMark.placeChecks, thm% Contrast.depth_text_exact,
      thm% SeedSeries.generated_series_contract, thm% ContrastSolve.bandClear_contract]
    accept := ["seventy-three of the guards' assertions fail with the fix's behaviour reverted onto the recorded commit, the guards kept — text and marks on a light page back at 4.6:1 and 3.1:1 whatever the medium, no container, no disliked region, and series picked for typical vision alone: a deck's accent text, muted ink and code, and an orange meeting a deck's floor, stand off the deck's 3:1; series fail their bound for the simulated readers; yellows and a mustard derive disliked tones; and no alert sets on a mark",
      "the review's guards: thirty assertions fail with its answer's behaviour reverted onto the recorded commit — a tone both of whose hues are disliked kept at its own hue, the container decided at each scheme's text target with the ink at 4.5:1 on its mark, a mark under every alert the palette marks, one per run and space, and the web page's mark element: a lemon, a pure yellow's example and a mustard derive disliked tones; a container falls away in the scheme asking more contrast, and a mark stands under an ink too faint on it; an alert is marked on the ink and after the document redeclares it; and a long alert's lines are marked run by run",
      "the second review's guards: twenty-four assertions fail with its answer's behaviour reverted onto 93b09d91 — no cleared tone on a dark page or ground, the accent on the ink solved unfiltered, the seeds carried to the other polarity as reflected, a dark page's tints at the accent's own hue, and the other polarity's view keeping the mark: an olive on a dark page and yellows carried to one fail to generate; a carried accent, a gold's and a dark mustard's text on the ink and a cleared hue asking more stand in the disliked region; a dark band's alert takes no tone; and a deck asking a dark scheme ships no transparent mark there",
      "a presentation deck's two brand palettes regenerated and built under lualatex and leantex, PDF and HTML: the accent's text, the muted ink and the code on the paper within 0.03 of the deck's 3:1 floor, the code in one band, a yellow brand's alert in the ink on its mark in both engines and quieted on a covered step as each engine quiets its text, the series at least ΔEOK 0.07 apart for every simulated reader; one build's warnings unchanged, the other's gaining one state-contrast warning, a covered alert against its revealed form, which its accent shipped as given at the floor entails"]
    state := .guarded "52508293" .revert .author },
  { id := "R176", date := "2026-10-14"
    what := "Lean's `#` commands set in a listing's ink at regular weight, in both artifacts: `#check`, `#eval`, `#print` and the rest, which Lean's own highlighter reads as keywords and the mirrored highlighter's keyword rule reached only after a word character, `#print`'s words with them, and `#exit`, which Lean highlights as it highlights a proof hole"
    pins := [check% hashCommandChecks]
    accept := ["the guard's twenty-eight assertions fail at 1d0b4eae before the fix: in both styles and both artifacts, every command and `#print`'s word in the ink at regular weight, and `#exit` in the ink; an array's `#[` and the names keep the ink before and after",
      "a presentation deck's Lean listings built by this tree and by its parent: only the pages holding `#` command lines change, each command and a `#print` form's word set bold in the keyword colour in the PDF and in the keyword colour and weight `def` takes in HTML, and no other HTML markup changes"]
    state := .guarded "1d0b4eae" .before .author },
  { id := "R177", date := "2026-10-14"
    what := "six of the suite's checks held a pass's wall-clock time to a fixed bound to claim it linear, not cubic or memoized, so a stalled host failed them and with them a commit, where no such bound measures the growth it names"
    pins := [check% anchorIdChecks, check% fontDiagChecks, check% keyedLookupChecks,
      check% contrastChecks, check% underlineChecks]
    accept := ["with the checks' process held stopped six seconds of every 6.1, the checks as 8127ac12 wrote them fail: in three rounds the anchor claim three times at about 12,250 ms against 1,500, the contrast judge twice and the float merge and the failing pairing once each at about 6,050 ms against 1,500, 800 and 400; with the stall's phase drawn at random, the families check nine times in 240 runs at about 6,030 ms against 200, and the glyph ink check once in 300 runs stopped 0.6 s of every 0.61, at 606 ms against 500; the hang guards replacing them pass in every run",
      "the claims stand as bench rows, compiled, judged by their growth over four times the input: anchors 13.0 to 13.4 against a bound of 32, since each claim probes the ids before it, families 4.4, the float merge 5.2 to 6.0 over 400,000 keys, the contrast judge 4.1 to 4.2 over legible runs and 4.0 to 4.1 over one failing pairing's uses, and a glyph ink decode costs about 1,390 memoized reads"]
    state := .guarded "8127ac12" .before .author },
  { id := "R178", date := "2026-10-14"
    what := "Mathlib's prefix notations `#s` and `#α` set as bold keywords in a listing, in both artifacts, where Lean's own highlighter, keying on the atom, reads a bare `#` before a name: the `#` command rule read `#` and a name anywhere, not only where a command starts"
    pins := [check% hashCommandChecks]
    accept := ["twelve of the guard's new assertions fail at 9bed5b00 before the fix: `#s` after `:=` and in parentheses, and `#α`, set bold in the keyword ink in both styles and both artifacts; a command indented after a line break, one after `in` on its line and one indented on the line after `in` keep the keyword before and after"]
    state := .guarded "9bed5b00" .before .author },
  { id := "R179", date := "2026-10-14"
    what := "a web page whose document declares a title but sets neither it nor any other level-one heading named itself with none, the title reaching only the window's name: a deck declaring its title with no title frame, and every document declaring its title only as metadata, handed assistive technology a page with no title heading, and three corpus pages declaring no title at all entered the accessibility tier below its cap"
    pins := [check% pageTitleChecks, .tier "htmla11y" "diagram-shapes.h1",
      .tier "htmla11y" "palette-seeds.h1", .tier "htmla11y" "alert-mark.h1"]
    accept := ["eighteen of the guard's assertions fail at 9bed5b00 before the fix, the guard alone added: thirteen titled corpus pages, two of them decks, hand assistive technology no level-one heading, and a titled deck with no title frame, a titled article setting no title and a declared metadata title name no page",
      "the review's guards: twenty assertions fail with its answer's behaviour reverted onto 1526b209, where the hidden heading wrapped word by word under the page's balanced heading wrap and a titled page with a level-one heading of its own was given a second",
      "the seventeen corpus pages the fix changes differ from their parent's HTML by the banner, the three now declaring titles also by their window's name, which read Untitled, and the one page carrying a figure's hidden words by their hiding written inline; each shows no visible difference on screen at arm's length and prints the same sheets with the same text; no corpus PDF changes but those three, by their metadata title alone, each the same on paper",
      "the accessibility tier's level-one heading items rise to its cap on the sixteen pages, the three lowered among them"]
    state := .guarded "9bed5b00" .before .author },
  { id := "R180", date := "2026-10-14"
    what := "the landing lock went to whichever waiting landing's retry woke first after a landing ended, so one branch was refused for 6.7 hours while five that asked after it landed"
    pins := [thm% Land.turn_take_exact, thm% Land.turn_first_exact, thm% Land.turn_behind_mem,
      thm% Land.enter_arrivals_exact, thm% Land.leave_arrivals_exact]
    accept := ["the landing tool's five queue scenarios fail against the tool built at 1deee4be before the fix: three landings waiting behind a fourth land in the reverse of their arrival, the latest asking most often, a waiter behind one that was killed is refused, a later waiter asking more often lands before an earlier one, the first waiter is refused rather than waiting for the lock, and four waiters entering at one moment get no order; with the fix all five pass, and the first waiter takes the lock 0.2 s after the holder exits"]
    state := .guarded "1deee4be" .before .author },
  { id := "R181", date := "2026-10-14"
    what := "a print document's spot colour stopped the build: colorspace was skipped, its spot colour definition was an unknown command, and the colour named from it could not be read, so no ink reached the file a press reads"
    pins := [check% Tests.SpotColor.checks]
    accept := ["the guard's probe documents built by the engine at 3c258580 skip the package and its definition command and stop at an unreadable colour; built here, its twenty-seven assertions pass over the PDF bytes and the web page one document ships",
      "the review's guards, added with its answer: a full tint in the boundary standalone, a colorant outside ASCII, a mix in a picture, a gradient and a formula, the rgb and gray alternates, the paper over an ink, a one-ink shading and a figure's ink read back, each failing on the branch's first cut",
      "a private print document under lualatex and here: the separation's colorant and alternate as lualatex writes them, the ink painted at full tint on both faces; with its spot colour declared as a process colour instead, this tree and its parent write byte-identical PDF, and the two documents here show no visible difference on paper at 35 cm"]
    state := .guarded "3c258580" .before .author },
  { id := "R182", date := "2026-10-14"
    what := "the browser oracle failed a deck's keyboard step on a loaded host and passed it on the rerun: it held its deck-link waits to a fixed 2.5 s of wall clock, its page loads to 30 s and two of its reads to fixed sleeps, and reported a wait that ran out as the page's failure"
    pins := [check% Tests.oracleWaitChecks]
    accept := ["the guard's three probe assertions fail on the oracle at 3c258580 before the fix: eight fixed waits, two 2,500 ms waits, four 30,000 ms loads and two sleeps, a page opened on no budgeted context, and a launch held to Playwright's implicit default",
      "the oracle's load check fails against its probe at 3c258580: an invented deck's link check passes with its renderer unloaded and fails on a 2,500 ms wait with the renderer held 200 times slower through the keyboard step; with the fix it passes both ways, and fails, loaded or not, once the arrow key is swallowed before the page reads it, and fails at once on a page that stops scrolling after its first key"]
    state := .guarded "3c258580" .before .author },
  { id := "R183", date := "2026-10-15"
    what := "a print document's page boxes and the definitions computing them were skipped: every edef was refused, the shipout hook assigning the page attribute was skipped, and the trim the file carried was guessed from the drawn cut marks"
    pins := [check% Tests.PageBoxes.checks, check% Tests.SpotColor.checks]
    accept := ["twenty-eight of the guard's checks, judged over the PDF, the web page, the dump and the diagnostics of their probe documents built by the engine at e2bef615, fail there, where the edefs are refused, the hook skipped and an overprinted text's commands left unread; built here, all pass, and the two foreground checks, ink off the medium and paint over the text, hold in both",
      "the reviews' guards: an edef reads the definitions and lengths in force where it stands as TeX scopes them, inline as well as in the preamble, its uses expanding to its text; only allocated lengths are read, refused after register arithmetic, a measuring, primitive, signed or register assignment, an environment's or a macro's code the pass does not run, and for a kernel length, kept after the, a comparison or a global setlength; a protected definition and a control after noexpand stand; an expansion past the step cap is refused; a length's units read as the paper's; a later page-attribute assignment replaces an earlier one, one expanding the attribute in force first keeps it, an unexpanded one is named, and a box whose numbers do not read is named; an attribute outside a hook is read; a box with no area is dropped and named, the art box follows a declared trim",
      "a private print document under lualatex and here: its edefs and its hook read with no skip, its declared boxes written as lualatex writes them up to its rounding, and its PDF byte-identical to its parent's, whose guess from the cut marks named the same boxes"]
    state := .guarded "e2bef615" .before .author },
  { id := "R184", date := "2026-10-15"
    what := "a value the compatibility layer copied into a native declaration was spliced into its string unescaped, so a quote in an author's metadata set the subject, one in a font family's name set the typewriter slot, and one in a declared language set the title; hyperref's metadata reached the PDF's information and XMP and the web page's head as its TeX, an escaped ampersand a backslash and a blank beside the ampersand; a return in the information read back as a line feed, and the XMP packet held characters XML refuses"
    pins := [check% Tests.MetaEscape.metaEscapeChecks, thm% Decl.parseValue_quote,
      thm% PdfRead.textString_representable, thm% PdfRead.literal_representable,
      thm% PdfRead.xmpText_admitted]
    accept := ["nine of the guard's assertions fail at 3c258580 before the fix: a quoted value read back with its quotes doubled; a return in the information's strings read back as a line feed and the XMP packet holding a return or a control character did not read back; a quote in hyperref's author set the subject; the escaped title read back as written in both lowerings; and a quote in the declared language and in a font family's name set the title and the typewriter slot",
      "the corpus built by this tree and by 3c258580, PDF and HTML: 221 of 224 artifacts byte-identical, the deck, math and math-text pages' HTML differing in a formula's TeX attribute alone, with no visible difference",
      "the review's guards fail on the branch's first cut: an underscore, a caret or an ampersand in a value stopped the build; a value's footnote renumbered the body's and its label took the body's; the PDF string reading set the second argument's alternative, a dropped footnote and the author list's separator as their TeX; a control character spelled in a literal string a reader decodes otherwise; and a colour's name, a colour's value, a line spread or a link colour set another key, the first stopping the build",
      "the second review's guards fail at its tip, 09783a787: the title and author LaTeX keeps read as unknown commands and an empty value set an empty title; a value's body TeX read as unknown or warned; a control space ending a braced value took the next key; the reading held at the top level alone; a reference in a value read as question marks unnamed; and a hyphenated colour name stopped the build"]
    state := .guarded "3c258580" .before .author },
  { id := "R185", date := "2026-10-15"
    what := "algorithm2e's keyword definitions lost to the package's own words and an io keyword ran into the next line; an option written on the line after an algorithmic, algorithm, figure, table, theorem, list, frame, columns or minipage opening was set as text or refused the build, and a bracket opening a float's centre was taken for its placement; a braced or spaced step was refused or misread; a function keyword was forgotten after its algorithm; and a declared io word's characters reached no font, so a word the faces lacked stopped the PDF"
    pins := [check% algorithmReadChecks, check% algLabelFaceChecks]
    accept := ["six of the guard's assertions fail at bcb532b0 before the fix: the io lines' words and semicolons, the body-local keywords, the next-line and comment-line step, the braced and zero steps, a next-line bracket holding no step, and the next-line float placement",
      "the first review's twelve guards, nine in the reading checks and three over the label's face, fail at b2e42c6b with only the guards added: a step named in its words, a spaced or zero-led step numbering every line, a function keyword unknown in the next algorithm, a declared io word absent from the font census, a figure's next-line placement and a table's after a comment line set as text, a float's second bracket swallowed, a next-line empty placement set as text, a theorem's next-line note set as text, a list's next-line options refused before its first item, and the label's face missing from both artifacts, the PDF refused",
      "the second review's five guards fail at 182af134 with only the guards added: a bracket opening a float's spliced centre taken as its placement and dropped, a placement's letters standing apart set as text, an io keyword without braces refusing the build, a frame's, columns' and minipage's options on the next line set as ink or refused, and the label's replaced glyph reported with no site"]
    state := .guarded "bcb532b0" .before .author },
  { id := "R186", date := "2026-10-15"
    what := "a column's or a minipage's diagnostics were dropped, so a picture wider than its column and a list nested too deep inside one went unnamed and a menu inside a minipage left the outline; a box taller than its page on a page holding nothing else overran it silently, an untitled frame's and a flow page's alike; and a size a document declared for a named step reached inline text alone, its headings, frame titles, standout, footline and stylesheet kept the ten-point steps, and the contrast judge read the footline there too"
    pins := [check% Tests.NestedLedgers.checks, check% Tests.DeclaredLadder.checks,
      check% Tests.PageOverrun.checks]
    accept := ["seventeen of the guards' assertions fail at 3c258580 before the fix, the guards alone added: a list nested five deep goes unnamed in a minipage, in the second of two and in a beamer column; a picture wider than its column or its minipage is unnamed and a minipage's menu misses the outline; a heading, a twelve-point article's heading, a plain frame title and a standout set at the ten-point steps against the declared ones, in the page and the stylesheet, as does the footline; and an untitled frame's rule, a titled frame's continued one and a flow page's rule taller than the text block, the first one opening the document, are named by nothing",
      "the corpus built by this tree and its parent: every PDF and HTML byte-identical and every run's diagnostics the same; a declared-ladder probe's heading sets at the declared 16 pt, as lualatex sets it, a visible change on the page and the screen, and the overrun and column probes ship identical bytes with their losses named",
      "the first review's guards: six assertions fail with its answer's behaviour reverted onto its parent commit — a long tabular, a tabular in a frame with declared breaks and two minipages at a page's foot named a box taller than the text block and split a row's cells across two pages, a tall float was named twice, a frame's rule under a footnote was named as the note, and a titled frame's rule continued onto a page holding only the title; and the judge's heading check fails with the judge reading the default ladder",
      "the second review's guards: thirteen assertions fail with its answer's layout reverted, the guards alone added — a tabular, a moloch frame's, a three-column one, tabulars in beamer columns and paragraphs in beamer columns breaking in a titled frame drew its title twice or more on a continuation page, in the lines and the tagged title's marked content; a titled and an untitled frame's box past its page on one step and overhang on another were named as two lines at one site, which the site audit now probes; a float whose footnote alone overruns its page named the float; a box past its page under a note was named with the note's height; and a titled frame's tall float shipped a page holding only the title"]
    state := .guarded "3c258580" .before .author },
  { id := "R187", date := "2026-10-15"
    what := "an environment definition in the document body stopped the build or set its text on the page, a definition's optional argument default was dropped, and a definition made inside a brace group outlived it"
    pins := [check% environScopeChecks]
    accept := ["nineteen of the guard's first twenty-two assertions fail on the engine at e2bef615 before the fix: each body definer's page and its one warning, a definition inside inline content, an absent optional argument's default and a definition inside a group",
      "the review's guards fail on the branch's first answer at 1e048315: a solution environment a skipped conditional's argument hides shows its body in five spellings, an unused default holding a length assignment moves the next paragraph down 4 cm, a second body definition of a theorem, an environment or a built-in strips its heading or stops the build, and a native body definition's use with an argument ships nothing"]
    state := .guarded "e2bef615" .before .author },
  { id := "R188", date := "2026-10-15"
    what := "a formula's text runs wrapped in the web page where TeX sets each as one unbreakable box: a deck's alignment of steps and their reasons, in a window narrower than the deck, showed each reason's first word and lost the rest to a line the page never drew, and a run's own spaces at its edges fell away"
    pins := [check% mathLineChecks, thm% MathMl.formula_linesHeld_contract,
      thm% HtmlDoc.labelNodesList_linesHeld_contract]
    accept := ["twelve of the guard's assertions fail with the fix reverted onto 3dc4692e, the guard kept: an alignment's reasons, an inline run, a box and an upright run, function and operator names, a run's edge spaces, a hyphenated run, runs in a script and a fraction, a coloured run, a cases column, a struck run, a frame's reasons and a picture label's formula each set a text run nothing keeps on its line",
      "the browser oracle's math-line judge, counting a collapsed space as lost, fails the text fixture and the deck fixture on the pages 3dc4692e builds: the text fixture's long reason parts at 320 and 360 px and its condition's trailing space collapses at every width, and the deck's two reasons part at 320 and 360 px; on the pages built here every math text run keeps its line and its spaces at 320, 360, 600 and 900 px; its controls part a narrowed run and collapse a run's edge spaces under nowrap, and keep both under pre",
      "a presentation deck built by 3dc4692e and here: in a 16:10 window of 1280 by 800 an alignment's reasons showed only their first words before and show whole after, inside the stage; at visualdiff's 1920 by 1080 the two builds show no visible difference on any slide",
      "of the corpus pages the fix changes, the deck, the Greek and the math pages show no visible difference at 1920 by 1080, and the text page's one visible difference is its condition, which reads if x where it read ifx, the space TeX and the PDF set"]
    state := .guarded "3dc4692e" .revert .author },
  { id := "R189", date := "2026-10-15"
    what := "a nested list stood its own kind's level of margin, not its depth's, so a list in a list of another kind or in a quotation stood short of where LaTeX sets it; an article abstract's list took its margins at the abstract's small size; the web page measured lists at the body size with an ex of half of it, counted no depth inside boxes and hung no margin on the abstract; and a margin set in the body, a level macro's margin naming another level or none, a declared list indent inside the abstract and the deep levels' spacing each shipped or claimed a margin the other artifact or LaTeX does not"
    pins := [check% listIndentChecks, check% listMarginChecks, check% abstractFormChecks]
    accept := ["the first cut's guards fail at bcb532b0 before the fix: declared margins at 20, 40 and 80 points where lualatex sets 20, 60 and 75; a redefined second level at 22 where it sets 55; an abstract's lists at 44.8 and 61.63 where it sets 47 and 65.7; the 11 point class at 27.5 and 24.2 where it sets 27.375 and 24.09; the web page's measure in a box, in the abstract and of an ex, and its abstract unhung",
      "the review's guards: seven of its nine assertions fail at 763f4e70, the first cut, the two class abstracts measured on its build: a body margin in ems left to the browser's font, a native body ex too, a body margin named as a loss both artifacts honour, a level macro's margin naming another level dropped and one setting none not kept, a declared indent lost to the depth's rule in the page and its unit, the fifth level's spacing claimed set, a report's abstract hung as a quotation with its lists two deep, and a deck's lists in its abstract two deep",
      "the second review's guards, added with its answer, fail at 964924582, the tip it read, as its probes and that tip's build show: a deck's abstract text at the frame's edge where lualatex sets it 21.82 bp in beside lists at 21.82 and 43.64, its web page's paragraphs not inset; a poster's at its edge where beamer's template sets 49.76; a report's abstract redefined on a quote at the full measure where lualatex sets 24.9, its refusal naming no quotation margins; a first level's declared indent stopped at the second level in the stylesheet; and a body table length's em fixed at the class size where LaTeX evaluates it in the font in force"]
    state := .guarded "bcb532b0" .before .author },
  { id := "R190", date := "2026-10-15"
    what := "a deck built to the web page alone said nothing of a frame's line past its measure, though the stage sets the frame's measure in the web page as the PDF page does: its overfull line and its re-flowed declared line were each named only by a PDF build, an overfull line never said how far it ran, and how each window shape a reader brings cost a deck's frames was measured nowhere"
    pins := [check% Tests.DiagFold.frameOverfullChecks]
    accept := ["four of the guard's five assertions fail with the layout change reverted onto d837f341, the guard kept: a stage's overfull line and its re-flowed declared line are the PDF's alone, an HTML build of the deck prints neither, and an overfull line, a stage's or a flow page's, states no amount; the fifth holds a poster's lines to the PDF both ways",
      "the review's guards, added with its answer: an overfull line two overlay steps set to different widths is one record at the furthest, matching the laid-out line, where the branch's first cut kept two, and the stage is one fact for both codes, so a line after a break inside a frame and a section divider's line reach the web page while a poster's stay the PDF's",
      "the browser oracle writes a window-shape report it never gates: per corpus deck and shape, at the deck's own aspect, 16:10, 4:3 and a portrait phone, each stage that clips an element or sets a text block on more lines than at the deck's own aspect; at their own aspect the corpus decks fit but the frames built to spill or collide, a failing read or control writes an unmeasured row, and its control names a held run a narrow window clips and a line it re-wraps"]
    state := .guarded "d837f341" .revert .author },
  { id := "R191", date := "2026-10-15"
    what := "a print document declaring the PDF X-4 standard with its output profile and the profile's registry entry got none of it: the standard, the profile and the PDF version were dropped, the profile's description skipped as expl3, and the file was written as PDF 2.0 with no output intent, its white page ground in DeviceRGB"
    pins := [check% Tests.PrintX4.checks]
    accept := ["the guard's probe card built by the engine at 3c258580 drops the standard, the profiles and the version, skips the profile's description, and writes PDF 2.0 with no output intent or X identification and a DeviceRGB page ground; built here it claims X-4, a page number after a coloured run stays black ink in DeviceGray, and the judge's rules each break on the facts a file could carry",
      "an invented X-4 card under lualatex and here, sized alike: the same PDF 1.6 header, media, bleed and trim boxes, separation and output intent fields, the same Info dates and trapping; this file also states the metadata's trapping and identification",
      "the reviews' guards: a figure holding an unembedded font in a direct or a composite font dictionary, DeviceRGB in a Type 3 glyph or a pattern's cell or under an indexed, a DeviceN or a pattern space's separation, an ICC 4.4 profile, a transfer function, PostScript or a reference to another file's page withholds the claim, named, where the branch's earlier cuts claimed it; a claimed file writes no link and names it, its web page keeping the links, where the first cut wrote them not to print; a page with no declared trim is trimmed inside its crop and bleed boxes; the metadata's instance identifier reads the pages; an unknown trapping, wherever it is declared, and a declared version are named and replaced only where the claim stands; and xcolor's colours but the grays stay RGB, so a document's magenta link keeps its web schemes",
      "a private print document under lualatex and here: with its dates declared it claims X-4 and passes a byte-level X-4 marker check, its media box, separation and output intent fields as lualatex writes them, its bleed and trim boxes nested exactly, and no art box beside the trim box; undated, the claim is withheld and the dates named; it shows no difference from its parent's build on paper at 35 cm",
      "the in-repo corpus built here and by its parent: the same HTML everywhere; every PDF differs in the spelling of its names and of the default black, and none shows a difference on paper at 35 cm",
      "the port onto the quoted declarations: with its quoting reverted, the guards kept, a quote in a declared profile's name sets the title and one in the profile description's value drops the key, and the rest of the guard passes",
      "the port's review guards fail on its first cut, 3657b570b: a setup's dates and trapping stood as a second declaration, so its note named two and a setup in the body was named twice; a dropped date and a cut value were two warnings and a setup whose every entry dropped had a note saying the engine did it; a brace pair or a command in a profile description's value broke its declaration, refusing the file or setting the title; and a date's short field was read; with the description's values in quotes but unescaped, the guards kept, a quote in one sets the registry",
      "the second review's guards fail at its tip, 956040199: a setup or a profile description in the body dropped the next group and split its paragraph, an offset of ninety-nine minutes was read, and the judge read a metadata date spelled as the Info's and an Info date spelled as the metadata's"]
    state := .guarded "3c258580" .before .author },
  { id := "R192", date := "2026-10-15"
    what := "a document defining its colours through its own macros was warned at each definition that a colour name or value no palette entry spells left the colour undefined, though every use defined it as written: a macro parameter handed to a colour, colour-let or spot colour definition, a language switch, span or environment, a font series, a length setting, a page style or a beamer template was judged where the macro was defined; each such warning named a loss no use has, and beside a hostile value's warning at its use stood one at the definition naming the parameter"
    pins := [check% Tests.MetaEscape.templateArgChecks]
    accept := ["thirteen of the guard's assertions fail at 22525202 before the fix: a definition through two macros, a colour let, a spot colour, a language span and switch, a font series, a length setting, two uses with two values and a nested definition's doubled parameter each raised at the definition a warning its text written out does not, and a name with a space its expansion spells drew a second warning, where its macro was defined, naming the parameter; a page style, a language environment and a beamer template no use reaches were judged where their macros were defined too",
      "the fix's first cut left each such command as written in a body the elaborator expands, so an environment setting a colour, a language, a span's language, a length or the PDF title from its argument, or calling a colour or language macro, printed the argument on the page and the web page; here no argument reaches either, and each setting an environment takes from its argument is named once where the environment is defined, no use applying it"]
    state := .guarded "22525202" .before .author },
  { id := "R193", date := "2026-10-15"
    what := "a setting a document declared could be accepted and then read by nothing and named by nothing: package options, hyperref's keys, class options, a list's own options, a theme's options and a length set but never read shipped the page the document without them ships, with no word that they were dropped"
    pins := [check% Tests.ParamCensus.paramCensusChecks, check% Tests.ParamCensus.paramTruthChecks,
      check% Tests.ParamCensus.paramSilenceChecks, check% Tests.ParamCensus.engineTokenChecks]
    accept := ["the census over the readers as 3c258580 has them, its tables kept, reports 226 of its 391 settings across 61 readers read by nothing and named by nothing; here none",
      "a mutant dropping geometry's margin in silence and one silencing the package-option fallback each make the census fail, naming geometry's margin=3cm and the invented option on every native package tried",
      "the review's guards, added with its answer, each failing on the first cut: parskip's skip=10pt plus1pt stopped the build and now sets the 22pt gap lualatex sets at 21.9 bp, and a medium skip the 18pt it sets at 17.9 bp; hyperref's pdftex, verbose and pageanchor=true were named unread and are silent, and the outline bookmarks asks for, which nothing writes, is named; reqno, twoside=false and openany as class options, fontenc's TU and csquotes' autostyle=true were named and are silent; a length set and never read was silent and is named",
      "the census judges what a page shows, a custom property no var() reads counting for nothing and a setting noted as changing nothing failing it when it changes an artifact, and each reader's own key table is walked; of the review's three surviving mutants, geometry's bindingoffset read as nothing fails it naming bindingoffset=1cm, and openany listed as a flag the flow model reads fails the flag check",
      "the second review's guards, each failing on the second cut: standard settings LuaLaTeX ships the same page with and without (csquotes' english=american, microtype's tracking, kerning and spacing off, amsmath's nointlimits and centertags, cleveref's english, siunitx's decimal point, fontspec's no-math, KOMA's version=last, titlepage=false, footinclude=false, open=any and headings=openany, beamer's unicode and presentation) or whose ask the engine already answers (hyperref's pdfencoding=auto, hyperfootnotes=false, pdfpagelabels=false and pdfpagemode=UseNone) were named unread and are noted, and an invented KOMA thesis preamble of them warned 18 times and warns of nothing; a class option a loaded package declares reaches it as LaTeX offers it (english to babel, usenames to xcolor) and one no package takes is named; bibsep, belowcaptionskip, topskip and bibhang were named unread though the engine reads them, and every token name an engine site reads by literal now stands in Ir.engineTokenNames; a text height under geometry's 1in margins moved the first line from 84.4 to 158.4 bp (500pt) and 348.4 bp (120pt), where LuaLaTeX keeps 84.9, and now leaves it at 84.4, named; an unreadable length literal and a language without a locale were named twice and are named once; an unreadable value stopped the build and now ships the page, named; geometry's nofoot with footskip=1cm named the page declaration and now the later key wins; a list's [<+->] is named an overlay specification; an unknown class's or theme's options were named again and are not",
      "the keys geometry, crop, natbib, biblatex, cancel, the font packages and the KOMA and microtype setups dropped, listed under one W0101, are each named W0104 keyed by the key; biblatex's hyperref=true, which asks for citation links nothing writes, and a main fontenc encoding that sets Latin input in another script's glyphs (OT2, T3, LGR, OML, OMS, OMX) were noted as losing nothing and are named",
      "the guards added on the landing pre-check, each failing on 36a5f348: a length value the door cannot read was named W0104 as a setting nothing reads, and a word given as the value lost the door's translation note, so the coverage probe read setlength as unknown; it is named once W0107, a degraded operand keyed by its length, beside the translation, and the page ships; report's own title page, an article's titlepage and a report's notitlepage, which set the abstract's form, were named unread class options and are read"]
    state := .guarded "3c258580" .before .author },
  { id := "R194", date := "2026-10-15"
    what := "a deck covered its pending overlay steps at the engine's own 38%, and each bundle at a share of its own, where beamer hides them unless the document declares how it covers, so a deck's PDF and web page showed steps lualatex never shows; and a covered share declared decorative was still judged"
    pins := [check% Tests.PaletteCover.coverChecks, check% Tests.PaletteCover.deckChecks,
      check% Tests.PaletteCover.hiddenChecks, check% overlayVisibleChecks,
      check% Tests.AlertMark.placeChecks, check% Tests.SeedSeries.seriesScriptChecks,
      check% Tests.SeedPalette.scriptChecks, thm% SeedPalette.generated_cover_contract,
      check% compatChecks, check% Tests.ParamCensus.paramCensusChecks, check% htmlA11yChecks,
      thm% HtmlDoc.animations_script_gated]
    accept := ["beamer under lualatex, on a probe of invented words: a deck declaring nothing and one declaring `invisible` ship no pending word on its first step, `transparent` ships it at 15% of the ink over the page and `transparent=40` at 40%; leantex ships the same steps in PDF and HTML, its PDF mixing in Oklab, so its covered word stands about 0.02 darker than beamer's",
      "a hundred and seventy-one of the guards' assertions fail with the hidden default reverted onto the recorded commit, the engine's 38% and the bundles' shares back: an uncover and an onslide in a deck declaring no share leave visible's pages in every overlay shape, a deck declaring no share judges and ships its pending step, items, block and alert mark, a share declared before a theme gives way to the bundle's, and eight corpus census facts see the pending content on the step pages that now hide it",
      "twelve fail with the hidden cover recolouring what it covers and leaving a lifted item lead as it stands: an uncover in a kerned face where colours meet or ligatures cross them, and one over a description list, no longer ships visible's pages, and a hidden item's image and markers show",
      "two fail with a hidden item's marker outside its lead's region: a marker in its own colour and an image marker ship on the step hiding their items",
      "five fail with a stepped item's step inside its li on the web page, its marker outside the step",
      "two fail with a closed range's declared end carried as a second li inside the item's: a list item stands inside another, and an item no longer carries its selector on its own element",
      "five fail with a cover declared in the body reaching the judge alone: nothing names it, and the judge reads a share or a colour no page covers with",
      "twenty-three fail with the seeds bound by the cover again and a decorative share judged: a seed meeting its floor moves at fifteen shares and schemes, the deck's alert leaves the accent and reports nothing, and the decorative deck reports its alert",
      "forty-four fail with the derived tones unbound, a hidden word's gap shipped as a word gap and a decorative share judged: thirty derived tones lose the covered-state contract or a browser's alpha, the light accent's alert neither darkens nor keeps it at a declared share, the export's first series and alert follow, and seven corpus decks ship word gaps beside no ink",
      "beamer's dynamic covering sets the two steps next to show at 10% and later ones at 5%, and highly dynamic its next step at 15%; here every pending step covers at 10% and at 15%, named W0109, as a share past 99% covers at 99%, named too",
      "three fail with dynamic, highly dynamic and a share past 99% named as settings nothing reads again, reverted onto 8ef16a5e: the settings census finds dynamic and highly dynamic named unread though they change the page, and the compat checks find none of the three named W0109",
      "two fail with a pending step's reach left to its parent's at every share, reverted onto 8ef16a5e: in a deck declaring no share and one declaring invisible, a pending step fades from nothing but stays in reach before its reveal",
      "with the reveal, recover and both rules running without the script's marker again onto 8ef16a5e, the engine no longer builds: animations_script_gated finds a step rule running an animation on a page the script does not run; with that theorem dropped too, one fails, the reduced-motion guard's",
      "in Chromium 151.0.7922.34, on invented decks of links: where steps hide, a link in a pending step takes no Tab stop at the first snap and a click at its box misses it, and from a pixel into its reveal it takes both, at opacity 0.001, 0.5 and 1; at beamer's transparent share it takes both throughout; with scripting off every step and list item shows at full opacity and every link takes focus; under reduced motion a pending step shows, visible and focusable",
      "the corpus decks declaring no share change visibly against main on the step pages whose pending content is now hidden, in PDF and HTML alike: footer-mixed, furniture, lists-deck, overlays-blocks, overlays, tables-deck, talk and themed; deck, which declares beamer's transparent share, changes only on its web page, where its pending step no longer slides in; the rest ship as before",
      "a private deck declaring its covered steps decorative, built under lualatex -Werror and leantex, PDF and HTML: its colours and every page as before, and its leantex builds report no covered-state loss where they reported one each"]
    state := .guarded "5139d571" .revert .author },
  { id := "R195", date := "2026-10-15"
    what := "a deck's web page slid each step in by a rem as it faded in, so a revealed step's text moved, where it should only fade"
    pins := [check% deckStepChecks, check% deckRangeEndChecks, check% deckStillChecks]
    accept := ["in Chromium 151.0.7922.34, on an invented stepped deck, the second step's box stands at x 43.19 px at its fade's start, middle and end, its opacity 0, 0.5 and 1 where steps hide and 0.15, 0.575 and 1 at beamer's transparent share; with the slide-in restored it starts 25.69 px, one rem, to the right and moves",
      "thirteen of the guards' assertions fail with the slide-in restored onto the recorded commit: the uncover's keyframes and the still-steps check of both step decks, and ten stepped corpus decks'"]
    state := .guarded "5139d571" .revert .author },
  { id := "R196", date := "2026-10-15"
    what := "a deck's focused slide drew the browser's own focus ring on its outermost pixels, a line along the window's edges that ran between slides as the reader paged on: every stage was a tab stop, focused when an address named its id or a click landed on it and shown once a key was pressed, and the deck declared no indicator for a stage"
    pins := [check% Tests.DeclaredColors.stageFocusChecks]
    accept := ["three of the guard's four assertions fail on main at 26720a07: its stylesheet declares no mark for a focused stage nor a ring of its own in forced colours, and its pager leaves every stage a tab stop; the fourth, that a stage marks in its ink so a focus colour no link ships is not judged, holds both ways",
      "the browser oracle's stage-focus row fails on every corpus deck the engine at 26720a07 builds: under the pager each stage stays a tab stop, and read without it each draws the browser's auto outline and no mark, focusing one changing the viewport's outermost pixels; on every deck built here no stage is a tab stop under the pager, and read without it every stage draws no outline but its mark, focusing one stage of each kind changing two bands of pixels a rule wide inside its side margins and none at the viewport's edges or in its band, footline or logo, at the deck's own aspect at 1x and 2x and at 16:10, 4:3 and a portrait phone, the bands holding still as a stage that spills scrolls, and in forced colours a focused stage still shows its focus; its controls fail a stage keeping the browser's ring, a mark run into a footline, a mark that scrolls with its stage, a mark forced colours drop and a stage left a tab stop under the pager",
      "a presentation deck opened at a frame's address in 16:9 and 16:10 windows at 1x, 1.5x and 2x and paged with the arrow keys: before, the address focused the frame, whose browser ring drew along the window's edges and ran between slides as it scrolled away; after, the address, a click in a margin and the keys focus no stage, no ring or mark shows, and each of the 20 snaps from the frame on shows one slide alone"]
    state := .guarded "26720a07" .before .author },
  { id := "R197", date := "2026-10-15"
    what := "settings a document declared through listing defaults, list styles, boxes and beamer's templates, sizes and fonts could be read by nothing with no word, or named only in aggregate: beamer's size setting, a box setup and a new counter were unknown commands, a template's predefined and empty forms went unnamed, inline code's display keys and minted's language key changed nothing, and a frame-title font no bar sets was dropped"
    pins := [check% Tests.ParamCensus.declCensusChecks, check% Tests.DeclSettings.setlistChecks,
      check% Tests.DeclSettings.frameTitleKeyChecks, check% Tests.DeclSettings.emptyTemplateChecks,
      check% Tests.DeclSettings.counterReadChecks, check% Tests.DeclSettings.titlePageChecks,
      check% Tests.DeclSettings.emptyTemplateMeasuredChecks,
      check% Tests.DeclSettings.defaultTemplateChecks]
    accept := ["the declaration census over the engine before this branch reports 24 settings across 6 readers read by nothing and named by nothing (beamer templates 10, beamer sizes 6, inline code defaults 4, beamer fonts 2, minted defaults 1, a new counter 1); here none",
      "the list, frame-title, template and counter checks fail on this branch's first cut: a first level's label styled every level and a counting label printed (*), level 0 stopped the build, a later kind scope overwrote a level's margin, one list setup warned four to eight times, a frame-title font nobody declared was named with no site, a predefined template took the next line as its body and stopped the build, and a counter a theorem shares was named twice; here they pass, positions as lualatex sets them",
      "a mutant silencing the list setup's per-key names and the beamer size reader's makes the census fail on both readers, naming nosep, align=left and the invented option, and text margin left=2cm",
      "the census counted a setting named by any diagnostic spelling it, notes and refusals that ship nothing included, and read where any one of its documents changed; judged strictly on this branch's second cut, 123 settings across 26 readers are read by nothing and named by nothing in a document that tries them, among them listing keys keyed by their words, invented options under one subject per package, beamer's covered setting under one subject, a frame-title template refused that ships nothing and page lengths set in the body named as the page declaration; here none, a setting named only by a warning keyed by it, a translation or an inert row's note keyed by it, in every document holding what it acts on",
      "mutants: unreadParam's warning demoted to a note fails the census on 75 readers, a frame-title font named under a bar fails it on beamer's font setting, a level scope dropped past the first on the list setup, a listing key keyed by its words on listing and minted defaults, the covered setting keyed by its command on beamer's covered setting; a scope's unstyled part dropped beside a styled part survives",
      "the second review's guards, each failing on this branch's third cut (1861eb6c): a counter a step, a value, a numbering or counter within it, a setting, a reference step, an addition or a list's use reads was named at its allocation as one nothing reads, or gave W0387 there; each is silent at its allocation and named at its use, and one nothing reads is named once where it is allocated, a macro's at its use, linear in the document (10 and 300 counters over a 2.6 MB body: 26.3 and 26.8 s, main 27.8 and 27.6 s, the third cut 324.5 s and past 794 s); an article's titlepage named the title command in a document with neither a title nor an abstract, where LuaLaTeX sets the same single page either way, and is named only at the title command and at the abstract, where LuaLaTeX sets two pages and the engine one; a page length set in a body group was named twice, W0104 beside the W0346 of a declaration it synthesized, and is named once; a frame-title font asking for the plain title's Large size or bold series, which the engine sets already (LuaLaTeX's size alike, its default title not bold), was named unread, and is noted",
      "the stricter census: a setting is read only where an artifact changes, a translation note alone reading nothing; a keyed declaration's setting is tried after a neighbour key; beamer's fonts are tried in every deck that draws their element; listing defaults in a deck too; the empty and default templates projected from the reader's tables, each measured; mutants caught: the unread warning demoted to a note (77 failures), a translation note in its place (84), beamer's fonts dropped under moloch (1), enumerate scopes' labels dropped (2), a frame-title template claimed empty (1), a declaration's keys keyed by its first (2); a list setup's unstyled scope parts silenced survives"]
    state := .guarded "47b07e39" .before .author },
  { id := "R198", date := "2026-10-15"
    what := "in a deck whose theme declares no section page a section between two frames made a page holding only its heading, and the web deck set a bare heading between the two stages, a strip that moved every later slide off the pager's grid so a seam showed a sliver of the next slide; a subsection did the same under every theme; the section's anchor stood on that page, text set outside the frames stood bare between stages and split at a section, a reference to a deck's section showed question marks, and the document's own section hook was an unknown command, skipped in the preamble and its frame set as content in the body"
    pins := [check% sectionPageChecks, check% frameHeadingScopeChecks]
    accept := ["206 of the section guard's 291 assertions and 5 of the heading-scope guard's 217 fail with the elaborator, layout, web writer and PDF writer of d381cd9b under them, the guards kept: every deck ships a page for each section and subsection whatever its theme or its own hook declares, and the section anchors, a label in a title and one after the last frame stand on those pages; its web deck sets those headings in the row between stages and every label outside the stage it names; text outside the frames stands bare between stages and splits at a section, a note outside the frames rides no frame, no tagged heading names a section no page inks, and a reference to a section shows question marks",
      "the browser oracle's snap judge, reading every snap point against the grid of whole viewports and the scroll space against one viewport per snap, fails the corpus deck, the trio deck, the sections deck and the hooks deck as main's binary builds them, the deck's later stages six off the grid by its 151 pixel strip, and passes every deck this tree builds",
      "invented decks under lualatex: the default theme ships one page per frame and none for a section, a starred one or a subsection, a section's bookmark and the label after it on the next frame's page; moloch ships its section page for a section and a starred one and none for a subsection, its bookmark on that page; the document's section hook sets its frame before each section and, unless its optional argument says otherwise, each starred one, through a command the document defines too, and a theme loaded after it sets its own; a reference counts a starred section and runs on past the appendix, 1, 3, 4 and 1 in both, and a label after a frame takes its section's number; where this tree differs it names the loss: a label inside a frame, the frame's number there, sets question marks, and a hook declared after a section, which beamer applies to the sections after it, is ignored",
      "by design a deck naming no theme takes the daylight bundle, its section page included, and a hook's own frame is not set yet: each section it opens stands on a page showing its title, the loss named once",
      "the corpus built by main's binary at d381cd9b and this tree: 193 of 226 artifacts byte-identical; 26 deck web pages show no visible difference slide by slide, the deck's and the trio deck's among them, whose row loses the strip between stages the per-slide judge does not see; the deck and trio deck PDFs each lose the one page that held a section's heading and show no visible difference with that page set aside; the sections deck loses four heading pages and its references print numbers; the hooks deck sets its two section pages as section pages, drops two heading pages and prints its references; the float caption fixture's table caption stands as far below its tabular as the figure's below its text, as LaTeX sets both, where the label after it had left an empty line's gap"]
    state := .guarded "d381cd9b" .revert .author },
  { id := "R199", date := "2026-10-16"
    what := "a definition of a built-in the engine ignores whole, through a command, document command, plain, let, environment, document environment or environ definer, or of a float other than around its kernel core, from a style file or the preamble, was accounted twice at its site: the refusal that the built-in stands, beside a translation note and the warnings for losses in a text that never runs, a conditional's skip, a box's dimensions or a length nothing reads; a let or a document environment definer of one was named an unknown command, the refusal unsaid"
    pins := [check% ignoredDefinitionChecks, check% siteAccountingChecks]
    accept := ["with the fix reverted onto 0073deb37 the guards fail for every one of fifteen definers of an ignored built-in, from a style file and in the preamble: each raises a warning, a note or an unknown command beside its refusal or in its place, and two site-accounting probes find a loss and a translation note at a refusal's site, with no row; the built-in's page stands either way",
      "the first review's cases fail on this branch's first cut (6912d88b): environ's redefinition of a built-in environment there discarded every use of it, its page losing the list or quotation, and a let, the three document environment definers and a float's other redefinition each raised one to four accountings; here each is its one refusal and the page stands, environ's redefinition of a float too, which the second review found discarding the float's uses at the first answer (c9b19f21)",
      "a refused redefinition of a built-in the engine renders keeps its text's losses beside the refusal, now a site-accounting row naming the redefinition gate as owing the merge: the gate decides only after the compatibility pass has reported them, and that pass's reports are each kept (completePrepared_reports_contract)"]
    state := .guarded "0073deb3" .revert .author },
  { id := "R200", date := "2026-10-16"
    what := "a geometry or preamble length reading the strut box, a quarter inch over its height as a foot skip, was dropped as arithmetic the engine cannot evaluate, so the page number stood where an undeclared foot skip hangs it, several points from where LaTeX sets it; and every geometry value spelled as an e-TeX dimension expression was dropped the same way"
    pins := [check% strutLengthChecks]
    accept := ["lualatex on invented probes: the strut box is 8.39996pt high and 3.60004pt deep under a 10pt class, 9.51996pt high under 11pt and 10.14995pt under 12pt, as the class's baselineskip sets it; here the foot skip a quarter inch over it hangs the foot's baseline that far below the text area under article, report and KOMA-Script classes at each size, from geometry and from a preamble setlength, and a page number in an invented letter-size article moves from 6.7 bp below lualatex's to 0.5 bp, the engine's own offset at any literal foot skip",
      "the strut stays unread, named once and the page left as without it, under a KOMA-Script class with no size option, whose 11pt the engine does not take, and after a preamble line spacing, setspace spacing, font size, size command, KOMA-Script font size or stretch redefinition, each of which may set the strut box again",
      "fourteen of the guard's assertions fail with the fix reverted onto 0073deb37: each class's geometry and setlength foot skip over the strut, and a geometry value's expression over literals, is dropped and named",
      "the first review's cases fail on this branch's first cut (828fd05e) and hold on 0073deb37, which dropped every expression: a geometry value over the head height, the top skip, the paper size, a side margin or the margin-note width stopped the build with E0321 and no artifact, a side's value was named not honoured where it is a dropped expression, a quotient was read, and memoir at 9pt and 14pt and a box assigned to the strut box left the strut read at 8.39996pt where lualatex's preamble holds 6.99997pt, 12.24994pt and 20pt; here each is named with its spelling and the page ships",
      "the second review's cases fail on the first answer (c9b19f21) and hold on 0073deb37: an expression in em or ex reached the page as a font-relative value its keys refuse, stopping the build with E0323, and one in px was read as a screen pixel, 15pt where lualatex sets 20.07477pt; a box assigned to the strut box by the box commands of LaTeX left it read; here each is named and the page ships"]
    state := .guarded "0073deb3" .revert .author },
  { id := "R201", date := "2026-10-16"
    what := "enumitem's paragraph and vertical-mode list skips were named not honoured though the page models them, so a list declaring no space above it took the class's default where LaTeX takes none; its item and top skips replaced the item and paragraph skips and the vertical-mode skip LaTeX adds to them; its shorthands spaced nothing; and a list's own options were named and ignored, so a dense page's lists drifted apart from LaTeX's, list by list"
    pins := [check% Tests.DeclSettings.listSpacingChecks, check% Tests.DeclSettings.listSpacingStyleChecks,
      check% Tests.DeclSettings.setlistChecks, check% htmlListSpacingChecks,
      check% Tests.ParamCensus.declCensusChecks,
      check% Tests.ParamCensus.paramCensusChecks, thm% Ir.listSpacing_undeclared_exact,
      thm% Ir.listSpacing_declared_exact]
    accept := ["lualatex on invented probes, article and scrartcl at 10pt: the space above a list after a paragraph break, around an inline list, between items and between an item's paragraphs under each vertical key, nosep, noitemsep and nolistsep through every list's, a kind's, a level's and a kind's level's scope, a later scope of one name replacing the earlier one or adding to it starred, and a list's own options; and article's nested lists, a second level keeping a first level's declared partopsep as size10.clo's level macro leaves it; here every step is lualatex's to the point",
      "the guard's documents built by 0073deb37's binary: a declared partopsep or topsep moved a list's top by 2pt, a parsep or itemsep its items by 4pt, nosep left 10pt and 8pt where lualatex sets none, and a list's own options changed nothing",
      "a length enumitem stores and the preamble cannot read, such as half a baselineskip, stopped the build with two errors and is named and skipped; the list keeps its level's spacing",
      "lualatex on invented probes: a list whose last item closes on a nested list ends on that list's skip with its own parsep on it, less the parskip outside, where larger than its own, as LaTeX's trivlist end sets it, under a declared topsep, parsep and level scope, after an inline and an opened nested list, an inline list's with the class's own values too; the page, and in Chromium 151.0.7922.34 the web page, set every step lualatex sets, the web page through a rule per closing spine, where this branch's first cut (58fe1657) set 2 to 6pt less",
      "the second review's cases: a list opening an item, in its label, takes the item's line and leaves no skip below it, as LaTeX's noparlist sets it, where main set 2 to 4pt above it and the first answer (c9b19f21) up to 8pt above and 6pt below; a quotation closing on a declared nested list ends on the larger of their skips, 24pt where lualatex sets 24pt and main 22pt, where the first answer re-skipped it at the quote's parsep, 4pt more; the web page reaches a description list's items and an abstract's closing list, and an inline list's re-skip without a declaration, as the page",
      "in Chromium 151.0.7922.34, the item after a nested list declaring spacing, by a scope, the list's own options or an inherited partopsep, at the second level and the fourth, stands where the page sets it, 21 to 31pt, where the first cut's web page took the class's level for it, 14 to 22pt",
      "the first review's cases: a level declaring only spacing kept its kind's label and margin on 0073deb37 and lost them on the first cut, here kept in either order; a later scope without vertical keys left an earlier one's vertical keys standing, here replaced as enumitem replaces them; an article's abstract was no list level, so its list took the first level's scope, here the second's"]
    state := .guarded "0073deb3" .before .author },
  { id := "R202", date := "2026-10-16"
    what := "a setting a document declared that nothing it set used shipped with no word: a colour nothing painted, a face no text was set in, listing defaults no listing read, a style for an element the document never showed, citation metadata in a markdown document or a Lean page's directive citing nothing; one a package, class or theme declares, or a file one of them inputs, must never be named, nor one a construct the engine refuses still names"
    pins := [check% Tests.UnusedSettings.firesChecks, check% Tests.UnusedSettings.scopeChecks,
      check% Tests.UnusedSettings.accountingChecks, check% Tests.UnusedSettings.oracleChecks,
      check% Tests.UnusedSettings.faceChecks, check% Tests.UnusedSettings.metadataChecks]
    accept := ["main names no declaration a document leaves unused; the guards need the W0449 code and build on this branch's first review cut (75f6f88c, its probes run on its pre-rebase twin 3cdcbfa0), where the review's probe pairs they restate fail: a colour a tikz-cd diagram, the boundary preamble or a refused construct alone names, a title page style an author-only title reads, a list macro's definition, a file a package or theme inputs, and citation metadata a citation no key carries or an image's text alternative sets were each named although the document without them ships a different PDF, web page or twin",
      "the second review's guards fail on its cut (bb5548e4): a colour a refused column modifier or a formula refused whole names, one declared inside a paragraph it ends, listing defaults an inline listing reads, and a Lean page's citation directive went named or unnamed against what the build reads; a colour only an honoured caption's words or an unread picture style names, and a beamer block colour a box reads, were silenced or named wrongly",
      "a first cut naming unpainted colours everywhere broke 147 suite checks; scoped to the document's own files, its own cut broke 139, each fixture made honest or its unread declarations accepted where they are the point; the colour export's fixtures name exactly the colours their deck leaves unused, and the regression decks' shared preamble declares only the faces they set, their PDFs byte-identical and their web pages visually so; the typeset report keeps its typewriter face, without which its web page would ship its body face's programs a second time for that slot, and accepts the loss",
      "both reviews' 518 probe pairs rebuilt on this tree, each judged by visualdiff on the PDF and the web page and by the twin's bytes: no declaration named unused changes an artifact but a hypersetup naming a title, whose help names only its link keys; the corpus's 224 artifacts are byte-identical to main's binary's",
      "the judge adds 2 to 5 percent to main's own time: 4000 unused colours build in 73.1 s and 1000 over 40000 reads in 39.8 s, main 69.3 and 38.4 s, the first cut 104.9 and 52.9 s"]
    state := .guarded "75f6f88c" .before .reviewer },
  { id := "R203", date := "2026-10-16"
    what := "a citation's PDF link went nowhere: it named a destination the file never defined, so a viewer ignored it, while a reference linked in the web page and not in the PDF; a link to the document's top, to a label whose anchor spelling differs from its key, to a section whose anchor took a number, to a deck frame by its title, step or number, or to a section page went nowhere in the PDF, a citation of an entry no list sets linked to nothing in both artifacts, an outline entry landing nowhere navigated nowhere, and a label written right after its heading or in a float landed below the heading or the caption in both"
    pins := [check% pdfDestinationChecks]
    accept := ["the destination judge, reading every navigation in a file's bytes, finds the corpus PDFs main builds at 5123c431 failing in seven fixtures: five cite into nothing (the bibliography, both markdown and both Lean citation fixtures), the icons fixture names an undefined top and the web navigation fixture holds an outline entry with no destination; here every corpus file's navigation reaches a page it writes, and the PDF links each in-page target as often as its web page does",
      "invented probes under lualatex with hyperref: a citation's destination stands on its reference-list entry's line, one baseline skip above its baseline, a section's on its heading, a table's at its caption and a footnote's on its note's line, where the caption package's hypcap moves a float's to its top; a label names the last anchor set before it (the heading it follows, a run-in heading, a phantom section, a float, an equation, a list item), a hypertarget its own place, and in a beamer deck a label after its section stands on the frame set next; this tree opens a label written right after its heading at the heading, a float's labels at the float's top, its caption above or its picture's ink, a deck's label on the frame set next, and any other label or target at its own line's ink top, a label later under its heading with no anchor between included, which hyperref opens at the heading",
      "a citation or reference inside a URL link took its own link in the PDF and the enclosing one in the web page; both now keep the enclosing link, as the web page and Pandoc set a citation inside a link's text"]
    state := .guarded "5123c431" .before .author },
  { id := "R204", date := "2026-10-16"
    what := "a markdown Lean division reached its inclusion as option text the inclusion command read again, so a value closing a brace wrote an option of its own, named as one no inclusion has, and a key holding a comma read as two keys; a host document's definition of the inclusion command replaced the divisions of every markdown file it included; and lualatex's leantex package lacked the citation style key and the prose and documentation views, each warned as an option it does not have"
    pins := [check% Tests.LeanViews.leanViewChecks, thm% Md.LeanDivision.ofRaw?_raw,
      thm% Code.includeLean_vocabulary_mem]
    accept := ["main's binary at da86ec89 on invented probes: a division whose show value closes a brace and opens an option zz names zz as an option the division does not have, and a host redefining the inclusion command sets its replacement text where the markdown file's division included its Lean file",
      "lualatex on an invented probe with the package as main ships it: an inclusion showing math and prose, and one showing the documentation view under a citation style, each warn that the inclusion has no option prose or biblio-style beside the warning that the whole file sets as code; with this package the views warn nothing of their own and biblio-style warns that the inclusion takes no such key, its citations setting in the document's style"]
    state := .guarded "da86ec89" .before .author },
  { id := "R205", date := "2026-10-16"
    what := "a markdown file or a Lean file a TeX document included was read through the compatibility walk among the document's own commands, so a document renewing a command the markdown's emphasis, strong emphasis, code, links, images, anchors or line breaks lower onto, or a math command a Lean file's formula spells, changed the included file, against the decision that markdown and code lower straight into the engine's vocabulary; and the markdown package's hybrid option, under which a file's text is TeX, was named as not applied and its setup command was unknown"
    pins := [check% Tests.MarkdownDoors.markdownDoorChecks,
      check% Tests.MarkdownDoors.markdownDoorDriverChecks,
      check% Tests.MarkdownDoors.markdownHybridChecks, thm% Parse.spliceKeptList_keptRaw]
    accept := ["main's binary at 0e5db3b5 on invented probes: a host renewing the emphasis command sets its replacement where an included markdown file emphasises a word and where an included Lean file's documentation does, a host renewing a math command changes a Lean file's formulas, the hybrid package option warns that it is not applied and the setup command that it is unknown, each file's commands then set as written",
      "lualatex with the markdown package on invented probes: a file's commands, braces and dollars set as written, and as TeX under hybrid, whether the package's option, the setup command before the inclusion or the inclusion's own option declares it, the inclusion's applying to it alone, its hybrid=false overriding the package's, a setup inside a group, an environment or an included file ending with it and an option passed after the package loads applying to nothing; under hybrid a group, an environment or math spans the file's emphasis and paragraphs, a percent sign comments out the rest of its line before the markdown is read and an escaped hash or percent sign sets as itself",
      "lualatex: without hybrid a host renewing the emphasis, bold, typewriter or first item label command changes the included markdown, which the package sets through them; this tree departs from it by the decision, the door checks naming the departure",
      "the corpus built by main's binary at 0e5db3b5 and by this tree's: all 347 artifacts byte-identical, and its markdown, code and including sources warn alike"]
    state := .guarded "0e5db3b5" .before .author },
  { id := "R206", date := "2026-10-16"
    what := "the prose view's sentences marked where a scope ends with nothing but parentheses or the sentence's end, so a reader could take an 'if and only if' a quantifier or a conclusion holds for the sentence's own, and a hypothesis's extent from marks a reader passes over"
    pins := [check% Tests.LeanProseReading.readingChecks, check% Tests.LeanProse.leanProseChecks,
      check% censusChecks, thm% LeanProse.parse_render_exact, thm% LeanProse.render_inj]
    accept := ["on the markdown twin da86ec89's binary writes of the invented statements fixture, its parentheses read as scope marks, a reader weighing every reading the words allow finds two readings of Tide.iff_nest, Tide.imp_iff and Tide.swap_and, so it and a reader running each scope to its block's end agree on 28 of the 31 sentences; on this tree's twin both read back all 31, and all 357 statements of the invented corpus, 300 of them random, from the page, the web page, the twin, and the web page and the tagged file as assistive technology reads them",
      "set at the margin, each of the corpus's 12 blocks bounding an equivalence leaves its sentence read otherwise, 11 of them two ways by the reader weighing every reading, and each of the 15 a quantifier, an existential or 'if' opens leaves it misread by the reader running each scope to its block's end; the 10 bounding neither are for the eye, both readers reading their sentences without them"]
    state := .guarded "da86ec89" .before .author },
  { id := "R207", date := "2026-10-16"
    what := "a deck's web page under focus and other window shapes: the browser oracle's stage-focus judge failed two decks whose progress bar had not caught up with a scroll between its shots, and read 1x and 2x only; a focused stage's mark lay over the content of a deck declaring a safe area under 4 px, was a ring on the stage's edge in forced colours and never drew a declared focus colour; a code block clicked and paged past, or a focused spilling stage, kept its ring or mark sliding away with the slide; the pager ate the keys a focused code block or spilling stage needed to scroll; a phone scrolled a whole stage sideways for a display wider than it; and read without the pager, an address naming a page-less section's label or a default scroll into view of its heading landed one stage early"
    pins := [check% Tests.DeclaredColors.stageFocusChecks]
    accept := ["the browser oracle's controls against main's judge and engine (ac870b67): the judge fails a stage whose top bar runs once across the viewport, as the two decks' progress bars ran, on 'changes the viewport's outermost pixels', and fails a page that never rests; this judge passes the first once the page rests and reads the second, and a page moving in steps, inconclusive; the engine's control deck built by main pages a focused code block running past its box instead of scrolling it and leaves the focus in the stage it paged past, makes its stage scroll sideways for its display at a phone's shape, and lands its page-less section's address and heading on the stage before, and a deck with a 2 pt safe area fails main's judge at every shape; built here each passes",
      "the guards fail with the fix reverted onto 0e5db3b5, the guards kept: a declared focus colour judged on no stage, the stage's own outline and its background mark, no declared colour on it, a ring on its edge in forced colours, code blocks, summaries and displays in the browser's ring, the pager keeping a stage's focus and every key, no display the pager marks wide, and a page-less section's heading and label away from its stage's corner",
      "the first review's probes rerun on this tree: a Tab across stages keeps the element it reaches as main does, a focused stage scrolls nowhere sideways, a display that fits is no scroller and no tab stop, under the pager a wide one at a phone's shape, in a step's alternative too, scrolls in its own box holding its ink's height, while without the pager it still scrolls its stage as main's does, and a diagram set as a display is as main sets it; a page that pauses or blinks between the shots reads inconclusive",
      "every corpus deck passes the stage-focus judge at 1x, 1.5x and 2x and at every reader shape; unfocused, each deck's web page shows no visible difference from main's, and every corpus document's diagnostics are main's"]
    state := .guarded "0e5db3b5" .revert .author },
  { id := "R208", date := "2026-10-17"
    what := "a deck's stages and sections apart in the two artifacts: an empty frame set a web stage but no PDF page, where beamer ships one, so the frames after it were numbered apart, and what it named, or what a last frame setting nothing named, landed on another page or nowhere; a web deck gave its sections no anchor, so a link to a section's slug went nowhere on the web page while the PDF reached a slug no ledger claimed; and moloch's sectionpage=none was skipped, its section pages kept"
    pins := [check% sectionPageChecks, check% deckDestinationChecks]
    accept := ["lualatex with beamer: an invented deck of four frames, two of them empty, ships four pages and defines each empty frame's target; moloch's sectionpage=none sets no section page, as its own empty section hook does; this tree ships the same pages, opens each target at its page's top, and sets a web stage for each with the PDF's frame numbers",
      "the guards fail with the fix reverted onto f27361cd, the guards kept: the empty frames ship two pages of four and their targets open elsewhere, the sections' slugs land in neither artifact as the web deck names them, moloch's sectionpage=none keeps its section pages and is skipped (W0104)",
      "the review's guards: a break opening an untitled frame ships no page of its own, for each of three breaks, and a label meeting a section's slug keeps its name in both artifacts, the section taking the numbered form",
      "a deck's sections claim their slugs in one ledger with its frames in flow order: a section and a later frame of one title take x and x-2 in both artifacts; a page-less section's slug stands on its heading at the next stage's corner, a section page's on its stage"]
    state := .guarded "f27361cd" .revert .author },
  { id := "R209", date := "2026-10-17"
    what := "a deck's overruns named apart from what they ran past: a frame's footnote past its measure said overfull line with no frame or amount, columns wider than their frame's measure ran past it in silence, a section page's title past its measure was a frame's line on a frame, and a protruding line's stated overrun counted its protrusion"
    pins := [check% Tests.DiagFold.frameOverfullChecks]
    accept := ["lualatex: beamer warns of two columns of 0.7 text widths an overfull box 66pt wide, its columns allowed the margins, and microtype's protrusion shortens an invented overfull line's stated amount from 23.6pt to 20.51pt; this tree names the columns past its own text width in a record of their own, and states a protruding line's overrun past the target its protrusion widens",
      "the guards fail with the fix reverted onto b7efbc12, the guards kept: the footnote, columns and section page wordings and the protruding line's amount, its protrusion counted"]
    state := .guarded "b7efbc12" .revert .author },
  { id := "R210", date := "2026-10-17"
    what := "a one-letter word in math, from a text command or an operator name, was an identifier the browser set in italic on the web page, where the PDF sets it upright"
    pins := [check% textInMathChecks]
    accept := ["main's binary at b7efbc12 writes such a word as an identifier with no variant, which MathML sets italic; this tree marks a one-scalar word normal, as it marks a lone scalar, and a longer word stays as it was"]
    state := .guarded "b7efbc12" .before .author },
  { id := "R211", date := "2026-10-17"
    what := "the PDF X-4 judge took a figure's halftone named for a device for one the standard admits and resolved every reference by a linear search of the file, and the fonts-embedded census passed a copied figure printing in an unembedded font whose dictionary stood directly in its resources"
    pins := [check% Tests.PrintX4.checks, check% censusDirectFontChecks,
      thm% PdfCensus.Index.find?_exact, thm% PdfCensus.Index.deref_exact]
    accept := ["probe documents built by the engine at da86ec89: a card copying a figure whose graphics state names its halftone keeps its PDF X-4 claim, and a document asserting its fonts embedded over a figure with a direct unembedded Helvetica passes; built here the claim is withheld, the construct named, and the assertion fails naming the font",
      "the guards fail on da86ec89 with the halftone case and the census's direct fonts, and hold here; the index finds what the linear search finds by proof"]
    state := .guarded "da86ec89" .before .author },
  { id := "R212", date := "2026-10-17"
    what := "a print document declaring its output intent's profile showed its CMYK colours on the web page, and judged their contrast, as xcolor projects them rather than as the press the profile characterizes prints them, a listing's fitted ink, a shading's stops and an ink declared again among them; the engine's own colours, a theme's, a listing's, a missing image's and a shading's, stood in RGB, so a document whose own colours were CMYK lost its PDF X-4 claim to them; and xcolor's cyan, magenta, yellow and olive were RGB where xcolor declares them in CMYK"
    pins := [check% Tests.Icc.checks, check% Tests.PrintColour.checks,
      check% Tests.PrintColour.previewChecks, check% Tests.PrintColour.driverChecks,
      check% Tests.PrintX4.checks]
    accept := ["LittleCMS 2.19 as the oracle, relatively colorimetric: 600 random ink mixes through FOGRA39L shown alike to the byte, Ghostscript's default and PostScript CMYK profiles and two invented version 4 profiles 592 to 597 of 600 alike and the rest a byte apart, and sRGB colours printed to within a thousandth of an ink",
      "the guards' documents built by the engine at da86ec89 show the CMYK accent as #ff4d00 under the profile, judge its contrast there, and paint a listing, a placeholder and a shading in DeviceRGB under it, losing the claim; built here they show and judge the profile's colour, paint the same inks, and print the engine's own colours in the press, the claim standing",
      "an invented card declaring FOGRA39L with a CMYK accent, a listing, cyan text and a missing image: at da86ec89 its claim is withheld for DeviceRGB in its page; here it claims PDF X-4 and its page holds no DeviceRGB",
      "the review's cases, its invented probes rebuilt here under FOGRA39L: the first cut pressed the document's RGB mixes into CMYK, and painted a moloch deck's colours in DeviceRGB, losing the claim; here the mixes paint the RGB main paints, 1 0.702 0.702 for red at 30, and the deck paints in DeviceCMYK, its page's grey in black ink alone, the claim standing; a listing's ink fitted from a CMYK colour, a shading's middle and ball stops and an ink declared again showed xcolor's projection and raised a contrast warning on the fitted ink, here they show through the profile and the warning is gone",
      "the second review's cases: the answer still painted in DeviceRGB what the engine derives at a site, a covered overlay step's ink, a generated tone on a block or a standout frame and a picture pin's grey, so a themed deck with transparent covering lost the claim, and pressed a palette's declared seeds; a colour is now the engine's unless a source reader declares it, those paint in the press and the seeds as declared; a listing ink fitted from a CMYK colour took up to a hundred profile conversions, 1379 ms against main's 797 for 320 listings, now found by bisection, 794 against 749, the press computed once per colour"]
    state := .guarded "da86ec89" .before .author },
  { id := "R213", date := "2026-10-17"
    what := "a print document naming one of the profiles l3pdfmeta describes, FOGRA39L coated or sRGB, got no output intent: the engine looked for the profile beside the document alone, where LaTeX finds it in the colorprofiles package, and gave it none of l3pdfmeta's description"
    pins := [check% Tests.colorProfileLayoutChecks, check% Tests.colorProfileDiskChecks,
      check% Tests.PrintX4.checks, thm% LeanTex.Cli.TexFontTrees.colorProfile_runless_exact]
    accept := ["lualatex on an invented card naming FOGRA39L coated: the output intent embeds the colorprofiles package's profile with the condition FOGRA39L Coated, the FOGRA registry and l3pdfmeta's description of the press; the engine at da86ec89 names the profile missing and writes no intent; here, under a TeX Live layout holding an invented profile of that name, it embeds that profile with the same description and claims PDF X-4, running no TeX program"]
    state := .guarded "da86ec89" .before .author },
  { id := "R214", date := "2026-10-17"
    what := "an itemize label a document redefined, its colour and its glyph, marked nothing: the class's bullet and dash stood on the page and the web page, and nothing named the definition"
    pins := [check% Tests.ItemLabels.checks, thm% HtmlDoc.cssString_no_lt]
    accept := ["lualatex on an invented article redefining the first and second labels: a red bullet and a plain dash, the third level's asterisk as the class sets it; the engine at da86ec89 sets the class's black bullet and bold dash; here the red bullet and the plain dash on the page and the web page, an enumitem label over the redefinition, and a redefinition in the body named",
      "the review's cases: the first cut loaded no math face for a label's formula and set a typewriter label in the body face, printed a ding's number or nothing for labels the engine cannot set, named a formula label inexpressible on the web page, named a begin-document hook's label as the body's, and let a label spelling a closing style tag end the web page's stylesheet; here the faces load, the class's bullet stands with the loss named once, the web page marks the formula's symbol, the hook's label marks every list, and the CSS string escapes its angle bracket by proof",
      "the second review's cases: a label whose loss had been named before raised only a note, so its ding printed again; the rollback now reads the loss, not its presentation; a structured formula label reached the web page linearized, now named; the fallback's help names the level's own command"]
    state := .guarded "da86ec89" .before .author },
  { id := "R215", date := "2026-10-17"
    what := "a share or covered colour a deck's body declared was ignored, named W0340, where beamer covers the frames after it; a pending item's marker in its own colour shipped at full ink, an item whose text was all one colour lent its marker that colour, and a covered description item set a bullet and moved its label; a covered run with no colour of its own took the preamble ink's cover whatever ink the body set or colour enclosed it; and a pause revealed after it only the rest of its own column, list or block, so a frame's later columns, items and paragraphs showed on the steps before it, and the rest of a pause inside a block uncover or only showed on no step; a bare pause between frames stepped the rest of the deck; and each later step of a frame opened in the colours its body had left on the step before"
    pins := [check% Tests.CoveredSteps.bodyShareChecks, check% Tests.CoveredSteps.dimPathChecks,
      check% Tests.CoveredSteps.pauseScopeChecks, check% Tests.PaletteCover.deckChecks,
      thm% Ir.dimBlocks_text, thm% Ir.OverlaySpec.fromStep_selects_exact]
    accept := ["beamer under lualatex on invented decks: beamer's transparent covering declared in the body between frames covers the frames after it at 15%, and one inside a frame covers to that frame's end, the next frame back at the share in force before it; here the PDF covers each pending step at the share in force where it starts, and the web page through each epoch's --ltx-step-share and --ltx-step-reach, in Chromium 151.0.7922.34 a pending step after the body's share at opacity 0.15 and visible, and one inside the frame declaring invisible at 0 and hidden",
      "lualatex: a pending item's red marker covers at 15% of red, an item whose text is all red keeps its marker in the label's colour, and text after a switch to red or inside a red text colour covers at 15% of red; here each covers in the cover of its own colour, mixed in Oklab toward the page, and a covered description item runs its label in where it stands shown",
      "lualatex: a pause in a column covers the next column and what follows the columns; one after a nested list the next item and what follows the list; one in a nested list the outer items after it; one inside a block uncover<3> covers what follows the group from step 2 and shows its rest at 3; one inside only<2> covers nothing outside it and shows its rest at 2; here each is so, beamer's pause counter read per frame",
      "lualatex: a covering declared in a frame after two uncovers leaves the later one covered at 15% on step 2; one declared inside a covered step hides a step nested in it until that step's own reveal; one inside only<3> hides what follows it on step 3 alone, one inside only<1-> on every step; here the PDF follows each, and the web page each but only<3>'s on its step, Chromium 151 hiding a nested step at the first snap and Tab passing its link by",
      "lualatex: a pause in a note leaves the next frame its two steps; a bare pause between frames, where beamer ships an empty page and sets the next frame on one step, and a pause in a list between frames, where beamer drops the rest of the list, reveal nothing here",
      "twenty-eight of the guards' thirty-eight assertions fail built on main at e5afdc634 with only the guards added: the body's covers are named ignored and its frames hidden, approximated body coverings unnamed as W0109, the web page restating no share, markers and runs covered in the ink's cover, the description item's bullet, a step's colours, the next column, item and paragraph after a pause shown on the step before it, the rest inside uncover<3> and only<2> never, and pauses in a note or between frames unnamed; nine of the first thirty-six fail on this change's first reviewed state: a pause in a note or between frames, a share declared mid-frame on later steps, a step nested in a covered one, a share past only<3> on the web page, a share-only epoch's ink, a marker in the covered colour, and a step's colours; on its second, an article's markers after a pause and an item stepped between frames lose their marker's ink",
      "the corpus's overlays-blocks deck covers its second column on the step before the pause in its first, as beamer does"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R216", date := "2026-10-17"
    what := "a quote after a citation, emphasis, a group or a formula opened in TeX text and in a bibliography field, so a possessive read as an opening quote; a key two entries of one reference list held took the first without a word; alpha's label read an empty author as present, where alpha.bst labels by the editor, and set an apostrophe straight; a bibliography file that is not there stopped the build with no artifact; a citation with no entry was named at no place, and for an included markdown file in TeX's words; a Lean page's bibliography that is not UTF-8 registered its keys from Latin-1 bytes while its list read UTF-8, so such a key showed '?'"
    pins := [check% Tests.BibEdges.quoteChecks, check% Tests.BibEdges.duplicateChecks,
      check% Tests.BibEdges.alphaChecks, check% Tests.BibEdges.missingChecks,
      check% Tests.BibEdges.siteChecks, check% Tests.BibEdges.encodingKeyChecks]
    accept := ["main's binary at e5afdc63 on invented probes: a citation's, an emphasized word's and a group's possessive, and a field's possessive after a braced group or a formula, set an opening quote; a key in two files of one list, and twice in one file, took the first entry with no diagnostic; a missing bibliography file was an error and wrote no artifact; a citation with no entry carried no span, and one in an included markdown file was told to fix a TeX command; a Lean page citing a key of a Latin-1 bibliography showed '?' beside the replaced bytes' warning",
      "bibtex 0.99e's alpha.bst over thirty invented entries, von parts, braced and accented names, an initial, keys, organizations, an empty author and odd years: every label's text and the list's order are the engine's but the empty author's, which alpha.bst reads as missing and labels by its editor, and lualatex prints a label's apostrophe curly; its et al. mark prints raised, which a list's plain marker cannot carry",
      "biber 2.22 and bibtex on two files sharing keys: both keep the first entry and name each later one, bibtex reading keys case-blind; here, keys read as biber reads them, a later entry is named where the list reads its key, cited, listed, a set's or lending its fields to another entry, and the fields it sets differ, in any order or wrapping and an empty one read as missing, the first's place in its detail; a bibliography file there but unreadable leaves each citation's '?' named, and a biblatex list's file is its resource however the list is printed",
      "the corpus built by main's binary at e5afdc63 and by this tree's, on 320e1b58: every PDF and markdown twin both build is byte-identical, and every web page but for the stage and focus rules main's commits since add; their diagnostics differ in three fixtures, a citation with no entry now at its command in two and a Lean inclusion's bibliography naming the key the document's file holds first"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R217", date := "2026-10-17"
    what := "KOMA-Script's classes set as a 10pt article: a document naming no size set its body at 10pt where KOMA-Script sets 11pt; parskip=half and full were read as fractions of an em, short of the class's half and whole line at 11pt and 12pt; and every list nested in another, and every list under parskip=half or full, took its level's own skips where KOMA-Script's lists take the parskip in force as their parsep, with no topsep and no itemsep, so nested lists stood 2 to 8pt apart from LaTeX's; quote, quotation and verse were one environment, so a quotation's paragraphs were spaced and unindented as a quote's, a verse's long lines did not hang and were named as declared lines that did not fit, a declared partopsep or a deep list's topsep and parsep did not reach a quotation, and a quotation closing on a nested list ended up to 4pt short; a list or a quote opening a quote took a skip above it where it stands in the label; beamer's verse set its stanzas touching; a level-two list setting reaching a list in a quote was named unused; a paragraph a display ended with an explicit paragraph break went on as the display's own; and the class's written options gave way to those passed to it before it loads"
    pins := [check% Tests.ListsKoma.komaListChecks, check% Tests.ListsKoma.quoteKindChecks,
      check% Tests.ListsKoma.quoteBoundaryChecks, check% Tests.ListsKoma.quoteKindHtmlChecks,
      thm% Ir.ListExtra.koma_exact, thm% Ir.quoteSpacing_own_exact]
    accept := ["lualatex on invented probes, scrartcl, scrreprt and scrbook with no size option, at 10pt and 12pt, under parskip=never, half and full, and article at 10pt: three nested lists and a quote, a quotation and a verse between paragraphs set every gap lualatex sets, to a tenth of a point, past each page's own baselineskip; a quotation's paragraphs indented by 1.5em under article and 1em under KOMA-Script and a verse's continuation lines 1.5em past its lines; main's binary at ac870b67 set the nested lists 2 to 4pt and the KOMA-Script parskip lists 8pt apart from lualatex's, the quotation 2 to 8pt, a fifth-level quote 5pt and the verse's continuations at its lines' margin",
      "in Chromium the web page sets the same gaps as shares of its line height, within 0.002, and the quotation's 1em indent and the verse's 1.5em hang; the page's own line height at 11pt stays the engine's 1.2 of the body, so an 11pt page's lines stand 13.2pt apart where KOMA-Script's stand 13.6pt",
      "lualatex on invented probes: a list or a quote opening a quote adds no skip of its own above or below it (main's binary 6pt more); a quotation's paragraph going on past a display, a list, a display listing, a skip after a list, a heading or a run-in heading starts at the margin, text after a list a quotation opens with is indented, and a verse line going on past a list stands at the hang; a beamer verse's stanzas stand 8.2pt apart (main 0) and a line a step reveals after its line's end a line below at the margin; small paragraphs in a quotation stand 11pt apart (12.2 before); and the web page's quotes, quotations, verses and the lists in them set main's gaps and margins in both artifacts, in Chromium too",
      "59 assertions in all; 48 fail built against b7efbc12c's tree; the eleven that hold there guard what the two reviews found the cuts broke (the web page's quotations and their lists in both artifacts, a page without quotation or verse, a verse under a font declaration, a list opening a verse, a declared parskip in a box, and the options passed to a KOMA-Script class before it loads) and article's nested lists"]
    state := .guarded "b7efbc12" .before .author },
  { id := "R218", date := "2026-10-17"
    what := "a list opening a list's item set its own first label alone, where LaTeX keeps the item's label on that line, each at its own item's place"
    pins := [check% Tests.ListsKoma.labelChecks]
    accept := ["lualatex on invented probes, article at 10pt: an enumerate item opening on an itemize sets 1. and the bullet on the inner first item's line, the number right-aligned where 2. stands, a label anchor before the list included; with the second level's left margin at 9pt its label overlaps the outer one, (a) at 16.22 to 29.00 over 1. at 12.22 to 20.00, the text at 34.00, where this tree sets 1. and (a) from 12.22 to 29.06 and the text at 34.00; beamer's invisible cover hides the outer label with an inner first item a later step reveals, its transparent cover leaves it black; the web page drew both labels already",
      "seven assertions; five fail built against c9dd4f3d6's tree; the two that hold there guard the label staying off the next item and off a list the inner first item holds, where that item opens on a centre or a description term, which the reviews found the first cuts let through; flush right the labels stand by their line's text as a lone label does, where LaTeX sets the whole list flush left"]
    state := .guarded "c9dd4f3d" .before .author },
  { id := "R219", date := "2026-10-17"
    what := "the web page read an ex as half an em in its list, quotation and skip gaps and its declared parskip, and as nothing in its skip registers, beamer's trivlist and float spaces and a frame's opening, where the PDF and the browser read the x-height of the face the page ships"
    pins := [check% Tests.ListsKoma.exChecks]
    accept := ["lualatex on invented probes, article at 10pt with enumitem's topsep at 10ex and itemsep at 2ex: a serif face of 475 thousandths opens the list 47.5pt down, Latin Modern 43.1pt; in Chromium this tree's web page stands those gaps at 3.957 and 0.790 of its line height where lualatex's stand at 3.958 and 0.792 of its baselineskip, and at 3.590 and 0.717 in Latin Modern against 3.592 and 0.718, where the tree before stood 4.165 and 0.832 in both",
      "a deck in a sans face declaring its partopsep at 3ex opens a frame's list with lualatex's 42.19pt to the first baseline and the PDF's 42.17; the web page's frame opening now stands at 7.493vh, its pt equivalent's 7.492vh, where it stood at 1.102vh, the partopsep read as nothing",
      "nine assertions; five fail built against a22f93197's tree, among them an article's and a deck's web page declaring nine lengths and a skip in ex against the same in sp; the four that hold there guard the PDF's own reading of the face and the half em of a page shipping no face"]
    state := .guarded "a22f9319" .before .author },
  { id := "R220", date := "2026-10-17"
    what := "a PDF's outline held only a declared navigation menu, never its headings, and hyperref's outline keys were named as lost or as honoured where they were neither; a deck's label in a frame set question marks; nameref was an unknown command printing its key; and a note a paragraph's or an environment's inline content held outside every frame, as after a loose label, vanished without a word"
    pins := [check% pdfOutlineChecks, check% sectionPageChecks, check% noteChecks,
      thm% Ir.outlineHeadings_depth_step]
    accept := ["invented probes under lualatex: hyperref's outline holds an article's unstarred headings down to the subsubsection, titled without numbers, nested and closed, the catalog opening it, and its bookmarks, bookmarksopen, bookmarksnumbered and pdfpagemode keys turn it off, open it, number it and name the mode; beamer's holds a deck's sections and subsections, starred too, open; pandoc's holds a markdown document's headings down to the third rank; this tree ships the same, but bookmarks a heading's full title where hyperref takes a short title given beside it",
      "invented probes under lualatex: a label in a beamer frame refers to the frame's number; nameref sets a section's title as typeset with the references in it resolved, a float's caption, an unnumbered heading's title, and for a frame's label its section's title; a starred reference sets its text without the link; this tree ships the same, numbering a frame label as its frame's number shows, which leaves out a title frame beamer counts, and naming a theorem's label and a run-in heading's by the section before them",
      "a note outside every frame stands right after the paragraph, heading or item that held it, before any block that follows, as a note in a frame stands with its frame",
      "main at 0e5db3b5 bookmarks no heading, sets a frame's label as question marks, keeps nameref's key as text, stops on a starred reference and drops the stashed notes; the guards fail there"]
    state := .guarded "0e5db3b5" .before .author },
  { id := "R221", date := "2026-10-17"
    what := "a markdown text's link reference definitions read as text, so a document's reference links and images stayed brackets, and a Lean docstring's own definition of a key's label still cited the key, where doc-gen4's definitions it appends come after the author's; a docstring's label alike to a cited key but in case stayed text, where doc-gen4 links it to the key's entry; a docstring's bracket before braces cited nothing; and a docstring's formula between dollars read as markdown, a bracket in it citing where doc-gen4 sets a formula"
    pins := [check% Tests.DocCiteEdges.documentChecks, check% Tests.DocCiteEdges.docstringChecks,
      check% Tests.DocCiteEdges.caseChecks, check% Tests.DocCiteEdges.mathChecks]
    accept := ["main's binary at e5afdc63 on invented probes: a document's reference, collapsed and full links and a reference image set their brackets and the definition lines as text; a Lean page's own definition of a cited key's label set as text, the key cited inside it and where the label stood, a label alike to a key in case stayed bracketed, a bracket before braces stayed text and a formula's bracket cited; this tree's binary links each reference and hides each definition, links the defined key's label to the author's address, the label alike in case to the key's entry under its own text, cites before the braces and sets the formula",
      "md4c's own source built with doc-gen4's flags (GitHub's dialect, LaTeX math spans, no HTML) over the docstring probe with the definitions doc-gen4 appends: the author's definition links its label, the label alike in case links to the key's entry, the bracket before braces is a reference and the formula's bracket no link, as this tree reads them; a formula between dollars that whitespace, punctuation (Unicode's P and S categories) or the text's edge flanks on their outer sides takes no link, citation or emphasis inside, a link read before it keeps its dollar and emphasis closing before it takes the dollar it passes; md4c links a defined label that spells a citation, as Pandoc's commonmark_x reader does and this tree does, though md4c and commonmark_x show the label as its text where this tree reads the link's text, citing in it as Pandoc's markdown reader cites in a link's text, and md4c and Pandoc's commonmark reader read a dash underline under definitions alone as a thematic break, as this tree does; doc-gen4 reads formulas only in a Lean file's documentation, and this tree reads none in a shell or Python file's",
      "the CommonMark tier: link reference definitions' examples matching rise from 3 to 14, links' from 35 to 61, images' from 5 to 8 and emphasis's from 121 to 123, none falling"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R222", date := "2026-10-17"
    what := "a markdown image's text alternative holding a citation read its key, the work uncited; and the markdown reader read no footnote, so a document's references and definitions set as bracket text, and the twin of a document whose footnote held a citation set every citation as its marks, a footnote's citation read back after the body out of a numbered list's order"
    pins := [check% Tests.MdNoteEdges.altChecks, check% Tests.MdNoteEdges.noteChecks,
      check% Tests.MdNoteEdges.noteTwinChecks]
    accept := ["main's binary at e5afdc63 on invented probes: an image's alternative with two citations set their keys as its name and named the loss, the works unlisted; a document's footnote references and definitions set as text; a TeX document citing in a footnote twinned every citation as its marks and its twin read the note back as a paragraph after the body",
      "pandoc 3.12 over the probes: an alternative's citations print as the style sets them, inside its emphasis or links or an image nested in it too, and their works are listed where the alternative alone cites; a footnote's label matches exactly, a definition after a list is read, its first paragraph takes its wrapped lines indented or not and its indented paragraphs, a definition's empty line takes the next line and, past one blank line, the one after, an empty definition is an empty note, a reference inside a definition is its text, a label's last definition stands, an unused one is warned of, a note named in an image's alternative sets nothing, and a reference after a citation, a reference link or a bang is a note; this tree reads each so, naming what Pandoc drops unsaid, but for a definition inside a list item or a block quote, which stays its container's text, a line opening a block after a note's first line, which ends the note, a lazy line inside a note's quote or list, refused as at the top level, a note's blocks other than paragraphs, which set as the note's lines, named, a note in a citation's prefix, dropped and named where Pandoc sets it, and an inline note, which stays text",
      "the mdtwin tier: Pandoc citations re-read exactly rise from 14 to 17 with an alternative's and a note's, and twins that are their round trip's fixed point from 106 to 107"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R223", date := "2026-10-18"
    what := "a markdown citation key holding another script's digits or numbers read only to the first, its work unfound; the citation of every entry, Pandoc's star key, set as text listing nothing; a citation group before braces holding no attribute list stayed bracket text; an in-text citation whose line ended in two spaces lost its locator on the next line to a line break; a reference-section-title heading stood over a list of no entry; the space after an abbreviation such as p. stayed breakable where Pandoc's smart punctuation joins it; and the twin spelled a TeX citation note's edge spaces"
    pins := [check% Tests.MdCiteEdges.keyDigitChecks, check% Tests.MdCiteEdges.everyEntryChecks,
      check% Tests.MdCiteEdges.bracketTailChecks, check% Tests.MdCiteEdges.breakTailChecks,
      check% Tests.MdCiteEdges.listTitleChecks, check% Tests.MdCiteEdges.abbrevChecks,
      check% Tests.MdCiteEdges.twinChecks]
    accept := ["main's binary at e5afdc63 on invented probes: a key with an Arabic-Indic digit named no entry, the bracketed star key set as escaped text, a group before braces holding x set as bracket text, an in-text citation before two spaces and a locator on the next line set a line break and the bracket, and p. 3 kept a plain space; this tree's binary cites each key, sets and lists nothing for the star and names it, cites before the braces, reads the locator and joins the space",
      "pandoc 3.12 over the probes with citeproc: the Arabic-Indic key whole, the citation id star printing and listing nothing, the group before braces a citation, the two-space line end and the next line's bracket one in-text citation whose suffix joins p. and 3 by a no-break space, and p. 3 joined so; its natbib writer joins a locator's p. and 33 by a tie"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R224", date := "2026-10-18"
    what := "a deck's section hook set a page showing each section's title instead of its own frame, a hook declared after a section was ignored and one declared in a group outlived it; the commands naming the section in force were unknown; a frame's label option was dropped, its references showing question marks; and a frame holding only the section page was a frame"
    pins := [check% sectionPageChecks, check% slideLabelChecks, check% frameHeadingScopeChecks]
    accept := ["invented probes under lualatex with beamer: a section hook's frame stands right after each section it opens, its starred code after a starred section or one with a blank title, the code itself when no starred code is given and nothing when it is empty; a hook declared after a section opens the later sections; a hook declared in a group ends with the group; insertsection names the section in force; a frame's label option refers to the frame's number; this tree ships the same, a theme's section page standing as the theme's own hook sets it",
      "the corpus built by main's binary at f753a486 and by this tree's, past what the list and outline units this stacks on change: every PDF visually identical but the hooked deck's, whose hook frames stand where its section title pages stood and whose stand-in warning is gone, and the contents article's",
      "main at 320e1b58 sets a page showing the title for each hooked section, ignores a hook after a section and drops a frame's label option; the guards fail there"]
    state := .guarded "320e1b58" .before .author },
  { id := "R225", date := "2026-10-18"
    what := "a table of contents was an unknown command in decks and articles: a deck's overview and its section hook's outline listed nothing, an article's contents neither its headings nor their pages, and a subsection carried no anchor a link could open"
    pins := [check% contentsChecks, check% contentsEdgeChecks, check% contentsEdgeChecks2,
      check% censusChecks, check% compatIndexChecks]
    accept := ["invented probes under lualatex: beamer's contents list the unstarred sections and subsections, a subsection 1.5em in, a fill before each section's entry and after the last sharing the frame's leftover, the currentsection option shading the other sections and their subsections; article's list the numbered headings to tocdepth under their heading, a section's bold after 1em with its folio right-aligned in 1.55em, a subsection's at 1.5em behind a 2.3em number with dotted leaders a stop and half an em apart from the line box's edge; this tree sets the same",
      "the corpus built by main's binary at f753a486 and by this tree's, past what the list and outline units this stacks on change: every PDF visually identical but the hooked deck's and the new contents article's, and every web page the same but theirs and the section gap rule each stylesheet carries",
      "main at 320e1b58 refuses the command and lists nothing; the guards fail there"]
    state := .guarded "320e1b58" .before .author },
  { id := "R226", date := "2026-10-18"
    what := "listings' inline code and file listing commands, url's path command and etoolbox's toggles and booleans were unknown commands: their arguments set as text, a path holding an underscore stopped the build, and every toggle test kept both branches"
    pins := [check% Tests.lstInlineChecks, check% pathFaceChecks,
      check% Tests.FlagCommands.flagCommandChecks]
    accept := ["main's binary at e5afdc63 on invented probes: the inline code command at three sites and the file listing command warn W0301 with their arguments set as text, the path command warns W0301 and its underscore stops the build (E0311), and each of the six toggle commands warns W0301, every test shipping both branches; the three checks fail on that tree (17, 5 and 52 assertions)",
      "lualatex on the same probes: the inline code sets as listings' inline code, braced or between two copies of a delimiter, the file listing sets the file as a listing, the path its argument whole in typewriter and unlinked, and each toggle or boolean test keeps one branch, a group's end restoring a setting and a boolean being the newif flag of its name"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R227", date := "2026-10-18"
    what := "LaTeX's boxes were missing or set unboxed: the colour box commands were unknown, their colour names set as text, a raised box set its content on the baseline and breakable, and url's lowtilde option was not honoured"
    pins := [check% Tests.InlineBoxes.inlineBoxChecks, check% censusChecks]
    accept := ["main's binary at e5afdc63 on invented probes: both colour box commands warn W0301 with their colour names set as text, the raised box warns W0104 that its lift, height and depth are not applied, and the lowtilde option warns W0104; the check fails on that tree (19 assertions)",
      "lualatex: a raised box sets its content in one box lifted by its length, a declared height and depth the line's extent; a colour box grounds its content's box padded by the box separation (3pt), the framed one frames that ground by the box rule (0.4pt) in its frame colour and the plain frame in the text's; url's lowtilde sets a URL's tilde as a script-size similar sign raised 0.2ex in a box"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R228", date := "2026-10-18"
    what := "a macro whose body takes a setting from its argument, called from an environment's code, dropped the setting silently or, for a colour, stopped the build; and a colour, language, size or shape an environment's begin code declares, the environment used inside a paragraph, set around nothing, its content outside it"
    pins := [check% Tests.EnvCode.templateCodeUseChecks, check% Tests.EnvCode.inlineEnvScopeChecks]
    accept := ["main's binary at e5afdc63 on invented probes: a colour through a macro in an environment's code stops the build (E0321, its parameter read as a colour), a language switch through one sets nothing, and a colour or language an inline environment's begin code declares leaves its content in the text's ink and language; the two checks fail on that tree (24 and 7 assertions)",
      "lualatex: each sets the environment's content in the colour or language its code gives, the setting ending with the environment",
      "a value from the environment's own arguments, which LaTeX substitutes, is named once (W0104) and set nowhere, as such a setting written in the code itself is"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R229", date := "2026-10-18"
    what := "algorithm2e's data and io words set unlike the package: a data word lost its argument's parentheses and xspace's space, an aligned io word's colon followed its own word instead of standing where the widest declared word's ends, its wrapped content returned to the margin, and io lines took line numbers"
    pins := [check% algWordChecks, check% censusChecks]
    accept := ["main's binary at e5afdc63 on an invented probe: 'left← left(x);' and 'up← lefty and up;', each aligned io line with its content after its own colon and a wrapped line back at the margin, and with lines numbered the io lines numbered 1 and 2; the check fails on that tree (6 assertions)",
      "lualatex: 'left ← left (x);' and 'up ← left(y) and up;', the y in the argument style's italic; the Input and Output colons both end at 188.50bp, each content 3.32bp past them and a wrapped line's text where its content starts; the io lines take no number, the first statement 1"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R230", date := "2026-10-18"
    what := "a page two paracol flows shared painted the page colour twice"
    pins := [check% columnGroundChecks]
    accept := ["main's binary at e5afdc63 on an invented paracol document under a page colour: two full-page grounds on each page both flows reach, one where one flow ends; the check fails on that tree",
      "the documents before and after are the same to visualdiff: the second ground covered the first exactly"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R231", date := "2026-10-18"
    what := "a figure's dropped CSS rule was named with its selector inside a second pair of quotes, 'style: the selector' read as the property"
    pins := [check% Tests.svgHtmlChecks]
    accept := ["main's binary at e5afdc63 on an invented SVG figure: W0609 names each dropped rule as its style property's 'the selector ...' inside the property's quotes; the CSS list check fails on that tree (3 assertions)"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R232", date := "2026-10-18"
    what := "report's and book's chapter command was unknown: its title set as text in the paragraph, no page opened, and the sections, equations and footnotes numbered through the document"
    pins := [check% Tests.Chapters.chapterChecks, check% Tests.Chapters.chapterReadingChecks,
      check% Tests.Chapters.chapterDeclarationChecks]
    accept := ["main's binary at e5afdc63 on an invented report: the chapter command warns W0301, every title set as text in the paragraph, the sections numbered 1 and 2 and the equations (1) and (2); the three checks fail on that tree (9, 3 and 6 assertions)",
      "lualatex on the same report: each chapter opens a page, 'Chapter 1' at the huge size 85pt below the text's top, its title at the Huge size 50pt below that and the text 52pt below the title, an unnumbered chapter's title 90pt below the top; sections 1.1 and 2.1, equations (1.1) and (2.1), footnotes from 1 in each chapter, and after the appendix 'Appendix A' with section A.1",
      "lualatex: cleveref names a chapter 'chapter 1' and an appendix chapter 'chapter A', a label in a chapter's title leads to its head, and book's front and back matter chapters stand unnumbered",
      "figures, tables, algorithms and listings still number through the document, where report and listings number them within each chapter, and book's divisions number their pages in roman numerals and from 1 again: each named once (W0110)"]
    state := .guarded "e5afdc63" .before .author },
  { id := "R233", date := "2026-10-18"
    what := "a refused redefinition of a rendered built-in whose text held a conditional drew two losses at one site; a colour only a refused hyperref key, a dropped beamer template or a refused style value named, or one whose name held a dot, was named unused, while one a word of refused prose spelled was not; a file a package's macro input at the document's call was the document's, and the document's own input of a file a package also input was the package's; listing defaults a minted definer's command or environment read were named unused; under --best-effort a missing family drew its refusal and an unused face beside it; and the face's loss stood at its declaration's first line"
    pins := [check% Tests.UnusedSettings.firesChecks, check% Tests.UnusedSettings.scopeChecks,
      check% Tests.UnusedSettings.redefinitionChecks, check% Tests.UnusedSettings.faceChecks]
    accept := ["the 18 new checks fail built against 0c3dab52's sources and pass on this tree",
      "the reviews' cases fail on the branch's first cut (bcf981a0) and pass here: a colour in a refused listing or caption key beside a font command was named unused, a winning redefinition after a refused one of the same name lost its skipped text's warning, and a length a package sets and nothing reads was named; and on the first answer, a page colour in an unknown command's argument was named unused and a redefinition a macro makes, refused where it is called, kept the skipped text's warning",
      "this tree's binary on invented probes: a redefined bold command with a conditional draws W0361 alone, a hyperref key or package option, a dropped template body and a refused style value naming a declared colour draw their refusal alone, a dotted colour painted at half strength is read, a colour a refused command's prose spells is named, a colour a package's loading macro inputs is not, a minted environment and command a definer made read the defaults before them, a missing typewriter family under --best-effort accepts E0403 alone, and an unused typewriter face is named at its entry's line"]
    state := .guarded "0c3dab52" .before .author },
  { id := "R234", date := "2026-10-18"
    what := "an edef calling a macro inside its own argument was refused; a bare length assignment, one opening a group too, set its value as text; the paragraph indent was never read, a body space of its width stopping the build; geometry's footskip of 2em stopped the build; an open dimexpr in an edef was dropped; and a length a definition sets from the strut box was named unreadable at the definition"
    pins := [check% texEdgeChecks]
    accept := ["invented probes under lualatex 1.24: the nested edef call, the bare assignments scoped to their group, a declared paragraph indent read back, a footskip of 2em as 20pt, and an open dimexpr, each set as lualatex sets it, and the paragraph indent read as the flush indent this tree's paragraphs take; this tree sets the same",
      "main at d720e3cc refuses the edef, prints the assignments' values, stops at the 2em footskip and the indent's space and drops the open dimexpr; the guards fail there",
      "the corpus built by main's binary at d720e3cc and by this tree's: every artifact and diagnostic byte-identical"]
    state := .guarded "d720e3cc" .before .author },
  { id := "R235", date := "2026-10-18"
    what := "a center, flushleft, flushright or verbatim stood off by the engine's own rhythm, one quantum over the peer gap at every list depth, and an article's verbatim by the peer gap alone, where LaTeX's trivlist spends the topsep in force (its list level's inside a list), the partopsep where it opens in vertical mode and the parskip in force on top, and nothing where it opens an item, a quotation or another trivlist; a list or quote opening such a trivlist, and a quote opening an item, took their own skips there; a heading after a center stood its peer gap further off; an environment right after a display its paragraph runs on to spent a partopsep; and the web page read a declared topsep or partopsep in CSS points, short of its own gaps"
    pins := [check% trivlistChecks, thm% Ir.TrivIn.within_declared_exact,
      thm% Ir.TrivIn.within_koma_exact, thm% Ir.trivIn_exact]
    accept := ["lualatex on 1199 invented probes: center, flushleft, flushright and verbatim at the top level and in items of levels one to three, opening and closing items, quotes, quotations and verses, after headings and each other, under article at 10, 11 and 12pt, report, book, scrartcl with parskip false, half and full, scrreprt and beamer frames, with declared topsep, partopsep, parskip, enumitem's setlist and a list's own keys; this tree's PDF sets every gap of 1157 of them as lualatex does, to a hundredth of a point past the page's own baselineskip, where main's binary at 4c717497 set 108 so and stood others up to 15pt off; the rest differ only by a heading's own space below it, after which the trivlist adds none as in lualatex, an article's peer gap between paragraphs, a level-two deck list's smaller type, and a minipage's opening",
      "two reviews' 230 further probes: a list, quote or theorem opening right after a trivlist, a trivlist closing on a nested list, a KOMA-Script list's declared topsep, a label anchor or skip before a list opening a trivlist, and an environment after a display set lualatex's distances; named: a description label alone sets on its own line above the block opening its item, where LaTeX shares the line; under KOMA-Script with enumitem loaded a list declaring no topsep leaves its trivlists its own, where enumitem's trivlist sets the class's extra again; a list body's topsep is W0104",
      "in Chromium the web page sets the same gaps as the PDF as shares of its line height, a declared topsep and partopsep included, but verbatim's own line box",
      "the corpus built by main's binary at b3abf7d0 and by this tree's: eight PDFs and seven web pages change visibly (box-sides, code-lean-prose, diagram, diagram-strokes, figures, images, layout's PDF alone, svg-figures), each only at a trivlist's boundary, by 2pt, 4pt where a trivlist holds only a picture, 6pt where a heading follows and 8pt where a float follows; every other artifact is visually identical; the typeset tier's centred fixture gains one widow (lowered, with its reason) and the rhythm tier rises by six items"]
    state := .guarded "7cf5a9f8" .before .author },
  { id := "R236", date := "2026-10-18"
    what := "a flow's contents ignored a renamed contents or references heading, printed an added contents line and hyperref's TeX-or-PDF string as text, left out a heading a macro with a parameter set, and wrapped an unnumbered entry flush left; a page reference to a label nothing numbered printed question marks; a run-in heading's and a subfloat's label named the section or float around them; a section named as a label shared its anchor; a deck's frames from such a macro repeated the frame number before them; and the web page's entries were paragraphs reading their number glued to their title"
    pins := [check% contentsGapChecks, check% contentsChecks]
    accept := ["invented probes under lualatex: the renamed headings print, a starred heading with an added contents line is listed by that line's words, also before a reference list, the TeX string alone sets, a macro's heading is listed and its frames numbered in turn, a page reference prints the label's page, a run-in heading's and a subfloat's label name their own titles, and an unnumbered entry's wrapped line stands past the number's width; this tree sets the same",
      "main at 6095f103 ignores the renamed headings, prints the added line and both strings as text, lists no macro heading, repeats the frame number, prints question marks for the page, names the section and the float, duplicates the anchor and wraps flush left; the guards fail there",
      "the corpus built by main's binary at 6095f103 and by this tree's: every PDF and diagnostic byte-identical, every web page visually identical but the contents article's, whose entries now stand at the leading as its PDF's do rather than a paragraph's gap apart"]
    state := .guarded "6095f103" .before .author },
  { id := "R237", date := "2026-10-18"
    what := "a markdown abbreviation after an ellipsis kept its breakable space, one ending in an escaped dot or a character reference joined, and one before a citation's spelling joined where no bibliography reads citations; the metadata's list heading joined none; an escaped space in a citation's note set its backslash; an attribute value whose quote no later one closed read no attribute list; a Lean docstring's defined label spelling a citation cited in its link's text, and its labels matched under CommonMark's spaces rather than md4c's"
    pins := [check% Tests.MdCiteEdges.abbrevEdgeChecks, check% Tests.MdCiteEdges.escapedSpaceChecks,
      check% Tests.MdCiteEdges.bracketTailChecks, check% Tests.DocCiteEdges.docstringChecks]
    accept := ["the new checks fail built against 6095f103's markdown reader and pass on this tree",
      "pandoc 3.12.1 on invented probes: an abbreviation after an ellipsis or an opening bracket joins; one in a word an ellipsis runs into, before an escaped dot or a character reference keeps its space, as one before an author's key, a bracketed key or a bracket of words before a key does, whether or not a bibliography reads them; the metadata's list heading joins as the text does; an escaped space in a citation's note is a non-breaking one; an attribute value opening on a quote no later one closes reads bare and the braces hold an attribute list, one with a space in it none; this tree reads each alike",
      "md4c's label rule (doc-gen4's reader): leading whitespace skipped, each later run of space, tab, line ending, vertical tab or a Zs space one space, a trailing one kept; a defined label shows as written; this tree's docstrings match so",
      "the corpus built by main's binary at 6095f103 and by this tree's: every artifact and diagnostic byte-identical"]
    state := .guarded "6095f103" .before .author },
  { id := "R238", date := "2026-10-18"
    what := "a markdown footnote's definition inside a list item or a block quote stayed its text; Pandoc's inline note was text; a note in a citation's note was dropped, and a TeX footnote in a citation's note set its text inline in the note; a TeX figure whose caption cited filled its image's alternative with a mark for each citation"
    pins := [check% Tests.MdNoteEdges.noteChecks, check% Tests.MdNoteEdges.inlineNoteChecks,
      check% Tests.MdNoteEdges.citeNoteChecks, check% Tests.MdNoteEdges.citeNoteEdgeChecks,
      check% Tests.MdNoteEdges.captionAltChecks,
      thm% Ir.captionRuns_said]
    accept := ["the new checks fail built against the tree before this commit and pass on it",
      "pandoc 3.12.1 on invented probes: a definition in an item or a quote defines its note; an inline note's content, citations included, is a note, an abbreviation before it joined; a note in a citation's prefix or suffix stands inside the citation, which this tree sets after it, named",
      "lualatex with natbib on invented probes: a footnote in a citation's note marks the note inside the brackets; this tree marks it after them, named once; a figure's caption citing sets its citations as the list does, which the image's alternative now reads"]
    state := .guarded "dfebcc96" .before .author },
  { id := "R239", date := "2026-10-18"
    what := "a deck's contents read neither beamer's pausesections, sections= nor firstsection option; a frame kept to article or handout mode shipped as a page and a handout-only specification was named not honoured; a noframenumbering frame was counted; the default section page printed no section name and number over its title, set flush left; a section hook could not call a command the preamble defined after it; a shaded entry's declared colour stood unshaded; and beamer's hyperref class option was not read"
    pins := [check% contentsDeckChecks, check% frameSpecChecks]
    accept := ["invented probes under lualatex with beamer: pausesections sets a page per section with one more entry each, sections= lists the named sections, firstsection changes no page of the default templates, an article frame ships no page, a handout:0 frame stands, noframenumbering takes no number, and the default section page sets Section N over the title, both centred; this tree sets the same, the article frame taking no number where beamer leaves a gap",
      "main at 03c2ff1d sets one overview page, lists every section, ships the article frame, names the handout specification, counts the unnumbered frame and sets the title alone; the guards fail there"]
    state := .guarded "03c2ff1d" .before .author },
  { id := "R240", date := "2026-10-18"
    what := "a colour only an unknown command's dropped options, an unsupported package's options or a beamer sub-theme package's options named was named unused; a refused redefinition after an earlier one said the built-in stands where the earlier definition did; a token only running prose spelled was taken as read; E0403 and the chapter-numbered floats' W0110 stood at no source site, and a pale ink in a box was named at an earlier box ground of its colour; a page colour inside a paragraph's text was refused as an unknown command spelled with its marker's name and left the page unchanged; and a scheme a palette colour painted on a box's own ground could not carry was blamed on the page, or dropped for a ground no text it coloured stood on"
    pins := [check% Tests.UnusedSettings.firesChecks, check% Tests.UnusedSettings.redefinitionChecks,
      check% Tests.UnusedSettings.faceChecks, check% tokensChecks,
      check% Tests.Chapters.chapterDeclarationChecks, check% Tests.InlineBoxes.boxScopeChecks,
      check% Tests.Schemes.dropChecks, check% Tests.GroupScope.groupScopeChecks]
    accept := ["main's binary at 6095f103 on invented probes: a declared colour in an unknown command's option, an unsupported package's option and a colour theme package's option each drew W0449, a refused bold redefinition after a conditional one said the built-in stands while the page set the conditional one's underline, E0403 and the floats' W0110 printed no site, a white ink in a yellow box was placed at an earlier white box ground, a page colour inside bold text drew W0301 naming ' pagecolor yellow' and left page 1 white, and a palette alert on a black box was dropped from the more-contrast light scheme on 'bg'; this tree answers each",
      "lualatex 1.24 on invented articles: a page colour inside bold text grounds page 1 yellow, a reset inside emphasis leaves page 2 white, one inside a framed box grounds page 3 blue, and one inside bold text at the head of a paragraph running over three pages grounds all three; this tree sets the same grounds",
      "the corpus built by main's binary at 03c2ff1d and by this tree's: every PDF and web page byte-identical but the trio page's and deck's, whose enquiries line now stands sep below what precedes it so that neither accepts W0104 whole; the diagnostics differ only in theme-modern, whose token 'large' only a bullet's prose spells, now named"]
    state := .guarded "6095f103" .before .author },
  { id := "R241", date := "2026-10-18"
    what := "the paginator turned a page where the next line no longer fitted, so a paragraph's first line stood alone at a page's foot and its last alone at the next page's head whatever the page held to stretch, where TeX's page builder ends the page at the least cost, its badness and LaTeX's club, widow and broken penalties; and a widow penalty of 10000 assigned in the preamble stopped the build, one in the body printing its value"
    pins := [check% Tests.PageTurns.checks]
    accept := ["lualatex on invented probes: a nine-line paragraph after a 518pt rule on an article page keeps its first line alone at the page's foot with no stretch above it, and with 40pt of stretch above the rule moves whole to the next page; this tree sets the same at its own page height, a page with no stretch keeping its club or widow as TeX does",
      "the guards' documents built by main's binary at 03c2ff1d: with 40pt of stretch on the page a club stands alone at its foot, and the preamble's widow penalty of 10000 stops the build (E0313); built here, the club moves with its paragraph and the declaration is read as the page's penalty",
      "the corpus built by main's binary at 03c2ff1d and by this tree's: every artifact byte-identical; the typeset tier's centred fixture keeps its widow back, and its report fixture splits one more row of its long table, a page turn ahead of it moved (lowered, with its reason)"]
    state := .guarded "03c2ff1d" .before .author },
  { id := "R242", date := "2026-10-18"
    what := "TeX's parameter assignments (leftskip, hsize, tolerance and their kin) printed their values; a length set mid-paragraph split the paragraph, one in inline content was ignored and leaked an internal restore name; a table cell's settings held into the cells after it; the preamble's baselineskip, textwidth and linewidth and the body's strut box, a footnote's and an abstract's size included, went unread; geometry's default layout and scale keys, a native page block's own em, the strut, the standard classes' footskip under a geometry page and a paper width alone on a KOMA class were lost; book's abstract was set as article's; a web page's box overflowed a narrow screen"
    pins := [check% texStateChecks]
    accept := ["lualatex 1.24 on invented probes: the baselineskip 12pt in the preamble, 11pt and a strut box 7.69997pt under the small size, 9.5pt in a footnote, 11pt in an article's abstract; a group's length 7pt inside and 3pt after it in one paragraph; the box separation 0pt in its cell and 3pt in the next and the next row's; geometry's default body 430.00462pt by 556.47656pt 95.39737pt from the top on letter paper, its scale keys and the a4 paper alike, a scale beside margins or a width sizing nothing; the folio 30pt below the text under a 2cm top and 4cm bottom margin, book's .35in, a footskip set before geometry standing; this tree sets each the same",
      "main's binary at a059e875 prints the assignments' values, splits the paragraph, warns W0346 with a leaked restore name, carries the cell's padding on, names the preamble lengths W0107, sets geometry's class page and the folio mid-margin; the checks fail there",
      "the corpus built by main's binary at 1e1685cb and by this tree's: every PDF byte-identical, one web page differing in a box's CSS with no visible difference; two documents' diagnostics differ, a paper option naming the class's paper now noted as changing nothing and a TeX parameter's assignment in a definition named"]
    state := .guarded "a059e875" .before .author },
  { id := "R243", date := "2026-10-19"
    what := "an item's marker was lost where its first block was a quote, a center, a flush environment, a verbatim, a display, a table or nothing, and an outer item's where an inner list's first item opened so; an empty box starting an item was dropped, its list joining the label's line; an itemize in a description took the second level's marker; an item's own label was dropped (W0110) and an enumerate counted it; the trivlist environment was unknown and its items refused the build; a center's close inside a float left no space before the caption after it; and a list in a minipage spaced its items as its outer list's next level"
    pins := [check% Tests.ItemLabels.openerChecks]
    accept := ["lualatex on invented probes: each opener sets the item's label on its first line, beside a centred line's start and at the item's place beside a quote or a list's first item; an empty item and a display opening an item set the label on a line of its own; an itemize in a description takes the bullet; an item's own label ends a labelsep before the text and steps no counter; a trivlist's labels hang a labelsep into the margin; a table's center closes 10pt above the caption after it; and a minipage's list spaces its items 20pt apart as an outermost list; this tree sets the same",
      "main's binary at 03c2ff1d on the same probes: the labels are gone, the trivlist stops the build (E0312) and the minipage's list stands 16pt apart; the guards fail there",
      "the corpus built by main's binary at 03c2ff1d and by this tree's: every PDF byte-identical, and the two web pages differ only in the stylesheet's four rules for an item's own label, visually identical"]
    state := .guarded "03c2ff1d" .before .author },
  { id := "R244", date := "2026-10-19"
    what := "pagenumbering was unknown, front matter numbered its pages on in arabic, the counters' printed values were unknown commands, a declared theequation numbered nothing, KOMA-Script's and memoir's chapters and addchap were unknown or sectioned as an article's, a class with chapters numbered its floats through the document, listings ignored firstline and lastline, and a markdown fragment's headings in a report were unnumbered sections"
    pins := [check% Tests.Chapters.numberingStateChecks, check% Tests.Chapters.chapterDeclarationChecks]
    accept := ["lualatex 1.24 on invented probes: roman, Alph and gobble folios counting from 1 where pagenumbering stands, mid-paragraph and in the preamble alike; front matter i and main matter 1 in book, scrbook and memoir; Section 1.1 of chapter 1 on page 1, equation 1.1, (1-1) under a declared theequation and (1.1) once numberwithin follows it; KOMA-Script's chapter head 67.28pt below the text's top and the text 37.07pt below it, addchap and addsec unnumbered, addsec listed by its short title; memoir numbering down to the section, its subsection unnumbered and thesubsection printing 1.1.0; Figure 1 before the first chapter, Figure 1.1, 1.2, then 2.1 and Table 2.1 in report, A.1 in the appendix, algorithms 1 and 2 through the document; a listing's lines two and three; a fragment's # a numbered chapter in report; this tree sets each the same",
      "main's binary at 1e1685cb names pagenumbering and the counters unknown, numbers book's front matter in arabic, sets KOMA-Script's chapters as sections and numbers figures 1, 2, 3; the checks fail there",
      "the corpus built by main's binary at 70096387 and by this tree's: every artifact and diagnostic byte-identical"]
    state := .guarded "1e1685cb" .before .author },
  { id := "R245", date := "2026-10-19"
    what := "a long, code-heavy markdown document's web page set every block in the paper's text width, centred between wide empty margins, its code squeezed into the prose column; and a web-only build set the document's pages it never shipped"
    pins := [check% Tests.WebMeasure.checks, check% Tests.WebMeasure.paperLossChecks]
    accept := ["an invented markdown guide of 950 code blocks and 1476 headings built by main's binary at 730c0b54 and by this tree's in Chromium at 1280, 1440 and 1920px and a 390px phone: the prose holds the same 73 characters a line; there every block stood in a 614px column, here 946 of its 950 code blocks reach their natural width up to 280px past the text, the margin holds its outline and the phone is unchanged; printed, every block keeps the measure; there an HTML-only build set 400 pages, here none",
      "invented probes from the review: a verbatim in a column, a minipage or a titled box, and a table of declared widths, keep their box; a numbered equation extends as a display does; a page with its own contents or navigation, or a résumé, carries no outline"]
    state := .guarded "730c0b54" .before .author },
  { id := "R246", date := "2026-10-19"
    what := "a box command (raisebox, fbox, colorbox, fcolorbox) whose argument held a minipage or a tabular read the environment as unknown, took its groups with it and refused the build, so a minipage raised by its own depth to stand on the page's foot shipped no page; the box's frame, ground and lift around block content were lost; and a minipage, a tabular, a center or a quote in a table cell, a note or a font command's argument refused the build or was named unknown"
    pins := [check% Tests.InlineBoxes.boxBlockChecks, check% censusChecks]
    accept := ["lualatex 1.24 on invented probes: raised by its own depth below a fill, a minipage's last line stands its depth, 2.05pt, higher, its bottom on the text area's floor; this tree stands it its own depth higher, and geometry's driver options before a geometry declaration name no loss",
      "lualatex on invented probes between two paragraphs: the next line's baseline stands 12pt below a bare minipage's last, 14.06pt raised by its depth, 10.22pt lowered by 1ex, 13.62pt framed at its bottom or top line, 13.22pt grounded and 15.16pt below a framed tabular, its first column 9.4pt in; this tree sets each to a hundredth of a point, the frame and ground fboxsep and fboxrule round the box, a framed tabular centred in a center as a framed minipage, framed minipages a fill apart side by side at their declared or relative widths, and a framed box too tall for the rest of its page moved whole to the next; named: a box's top stands where a bare minipage's does, lower than lualatex's, 3.7pt for a minipage set on its last line and more for one centred on the axis",
      "main's binary at 730c0b54 on the reported shape names the minipage an unknown environment (W0302), its groups gone with it (E0336), and its raggedright aligning nothing (W0108), and refuses the build; the guards fail there",
      "the diagnostic oracle's 18 refused cases (a minipage or a tabular inside raisebox, fbox, an l or p cell, textbf or a footnote) and its 6 unknown-environment cases (a center or a quote in a p cell, textbf or a footnote) build here, each sentinel word shipped: inside a box command as a box, elsewhere its words in the line, named once (W0451); text beside a box holding a block is named once (W0452)",
      "in Chromium the web page's box paints the same ground, frame and padding round the minipage, the tabular's frame hugging it and centring with it, the framed row side by side",
      "the corpus built by main's binary at 6714141d and by this tree's: every artifact and diagnostic byte-identical but the boxes fixture's, whose framed and raised minipages now ship"]
    state := .guarded "730c0b54" .before .author },
  { id := "R247", date := "2026-10-19"
    what := "the engine read a document's pt as a big point, so every TeX length set 0.375% wide and a 10pt length printed as 10.0375pt"
    pins := [check% pointDoorChecks]
    accept := ["lualatex 1.24 on an invented article: a length set to 10pt prints as 10.0pt; this tree prints 10.0pt",
      "main's binary at 9dd642df on the same probe prints 10.0375pt; the guard fails there",
      "the corpus built by main's binary at 9dd642df and by this tree's: 84 changed artifacts invisible, 160 visible as the intended shrink toward TeX, a 10pt font set at 9.963 bp where lualatex sets 9.96264"]
    state := .guarded "9dd642df" .before .author },
  { id := "R248", date := "2026-10-19"
    what := "a declared font family no installed face answers stopped the build with no artifact (E0403); a palette colour failing on several grounds was named on the first alone; the log's repeat fold scanned every earlier record for each record; and the help of a live macro reached through an earlier one printed its name as a literal placeholder"
    pins := [check% fontDefaultsChecks, check% Tests.UnusedSettings.faceChecks,
      check% Tests.Schemes.dropChecks, check% Tests.macroRoleChecks, check% diagVoiceChecks]
    accept := ["main's binary at 730c0b54 on invented probes: a main font declaration naming a family no host has stops the build with E0403 and no PDF, and a white palette alert on a black and a blue box is named in the dark schemes on the black ground alone; this tree ships the document byte-identical to the one without the declaration beside one W0403, and names both grounds",
      "the passes bench: folding 8000 and 32000 diagnostics in 4000 and 16000 wordings took 970 and 15294 ms on main's code, 15.8 times for four times the records, and takes 3.6 and 15.1 ms here, 4.2 times",
      "the corpus built by main's binary at 730c0b54 and by this tree's: every artifact and every diagnostic byte-identical"]
    state := .guarded "730c0b54" .before .author },
  { id := "R249", date := "2026-10-19"
    what := "an environment whose definition opens another environment in its begin code and closes it in its end code, by the environment's begin and end or by its commands, stopped the build with no artifact; the commands of trivlist, center and the lists were unknown, their items refused; and a list, not nested, in a footnote or under a bold style command stopped the build the same way"
    pins := [check% Tests.EnvCode.wrapEnvChecks, check% Tests.EnvCode.blockArgChecks]
    accept := ["lualatex 1.24 on invented probes: a wrapper of itemize, of a trivlist opening its item, of center by its commands with a size declared, and of center reading an argument each set what the environment written in place sets, 20pt below the line before it as a list opening in a paragraph does; the command form of trivlist sets as its environment; a wrapper of a wrapper sets as the environment inside; a footnote's list sets each item after its mark; this tree sets the same, but a footnote's items stand at the note's margin, where LaTeX hangs them a leftmargin in, and with the list's options unread, both named as the footnote's loss; a bold list's item sets bold, where LaTeX's bold command leaves vertical mode first and sets an empty line above the list, about 10pt, which this tree does not",
      "main's binary at 700963877 on the same probes: every one stops the build with no artifact; the guards fail there",
      "the corpus and the private references built by main's binary at 6714141d0 and by this tree's: every PDF and web page byte-identical"]
    state := .guarded "700963877" .before .author },
  { id := "R250", date := "2026-10-19"
    what := "a description label alone before a list, a quote, a verbatim or a box set on a line of its own; a table, a minipage, a parbox or a listing opening an item followed the label's own line; a declared label set alone shipped its ink as a generated marker's; the twin numbered an ordered list's labelled items in sequence; the web page broke a line at an empty box and ran in a label by its character count; and KOMA-Script's fontsize set after the class was unread"
    pins := [check% Tests.LabelLines.checks]
    accept := ["lualatex on invented probes: a description label alone sets on its list's first line at the outer margin, the line after it moved by the label's width and labelsep less the 25pt indent (10.2pt for a five-letter label, -12.3pt for one letter), an inner description's label a labelsep past the outer's end; a tabular opening an item centred on its bullet, a top-aligned minipage on its first line, a parbox centred, a listing's first code line holding the bullet; a five-character label hanging in its margin and a wide one running in; the 12pt body after KOMAoptions fontsize 12pt, its lines 24.4pt apart in a list; this tree sets each the same",
      "main's binary at 6714141d on the same probes sets every such label on a line of its own, numbers the twin's items one to four, writes an inline-block for the empty box, runs in the five-character label and sets the 11pt body; the checks fail there",
      "the corpus built by main's binary at 6714141d and by this tree's: every artifact and twin byte-identical"]
    state := .guarded "6714141d" .before .author },
  { id := "R251", date := "2026-10-19"
    what := "a deck's title frame went uncounted whatever the theme, where beamer's maketitle frame counts and only moloch's is plain and uncounted; a noframenumbering frame showed no number, where beamer's shows the one before it; beamer's plain frame option was ignored, the frame keeping its footline and logo; and a section page the document's own frame set was centred as moloch's, about 20pt below beamer's"
    pins := [check% frameCountChecks, check% contentsDeckChecks, thm% Ir.shownFrom_exact,
      thm% Ir.frameShown_numbered]
    accept := ["lualatex with beamer on invented probes: the default theme's maketitle frame and a frame holding titlepage number 1, the next frame 2, a noframenumbering frame after it 2 again and the frame after that 3; moloch's maketitle frame shows no number and its next frame 1; a plain frame sets no footline and no logo; and a frame setting only sectionpage under the default theme puts its section name 80.3pt and its title 114.5pt below the paper's top; this tree sets the numbers the same, a title page showing none, and the name and title at 79.4pt and 114.5pt",
      "main's binary at 730c0b54 on the same probes: the title frame takes no number, the noframenumbering frame shows none, the plain frame shows its number and logo, and the section page's name stands at 99.9pt; the guards fail there",
      "the corpus built by main's binary at 730c0b54 and by this tree's: the seven decks whose maketitle runs under a theme other than moloch number every frame after the title one more, and the parity deck whose plain frame sets its title page counts it the same; every other artifact is visually identical, most byte-identical"]
    state := .guarded "730c0b54" .before .author },
  { id := "R245", date := "2026-10-19"
    what := "a beamer footline template holding the frame counter alone, or after an hfill with spacing around it, stopped the build (E0111) with no artifact, and beamer's frame number footline was not read; any other footline body, and any footline set in the body, stopped the build the same way"
    pins := [check% footlineTemplateChecks]
    accept := ["lualatex with beamer on invented probes: the counter alone stands at the footline's left, after an hfill at its right, the frame number template sets the counter over the total at the right, and every probe builds; this tree sets the counter in the native band's left or right slot, the frame number template's as the fraction, and ships a deck whose footline it cannot set, or whose body sets one, with its own footer, named once (W0110)",
      "main's binary at 70096387 on the same probes: E0111 and no artifact for the bodies, W0104 for the predefined template; the guards fail there",
      "the corpus built by main's binary at 70096387 and by this tree's: no corpus document's footline changes"]
    state := .guarded "70096387" .before .author }
]

/-- The reports guarded but never seen failing, a count held in both directions. -/
def unwitnessedBaseline : Nat := 10

/-- The reports not closed, held the same way. -/
def owedBaseline : Nat := 4

def Report.unwitnessed (r : Report) : Bool := r.state matches .unwitnessed

def Report.owed (r : Report) : Bool := r.state matches .owed ..

/-- The owed guard names of a row. -/
def Report.owedGuards (r : Report) : List String :=
  match r.state with
  | .owed _ gs => gs
  | _ => []

/-- A commit named by at least eight lowercase hex digits. -/
def isSha (s : String) : Bool :=
  s.length ≥ 8 && s.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- `YYYY-MM-DD`. -/
def isDate (s : String) : Bool :=
  match s.toList with
  | [y1, y2, y3, y4, '-', m1, m2, '-', d1, d2] =>
    [y1, y2, y3, y4, m1, m2, d1, d2].all Char.isDigit
  | _ => false

/-- A description in abstract words: no path, no file, no address. -/
def isAbstract (s : String) : Bool :=
  !(["/", "\\", "@", ".tex", ".sty", ".pdf", "http"].any (hasStr s ·))

/-- What is wrong with a row: its identity, its words, and a state its pins can carry. -/
def Report.faults (r : Report) (i : Nat) : List String :=
  let name := if i + 1 < 10 then s!"R0{i + 1}" else s!"R{i + 1}"
  (if r.id == name then [] else [s!"{r.id}: ids run R01, R02, … in order; expected {name}"]) ++
  (if isDate r.date then [] else [s!"{r.id}: the date '{r.date}' is not YYYY-MM-DD"]) ++
  (if isAbstract r.what && !r.what.isEmpty then []
    else [s!"{r.id}: the description names a path, a file or an address"]) ++
  (if r.accept.all isAbstract then [] else [s!"{r.id}: an acceptance run names a path"]) ++
  match r.state with
  | .guarded sha _ _ =>
    (if isSha sha then [] else [s!"{r.id}: '{sha}' is not a commit"]) ++
    (if r.pins.isEmpty then [s!"{r.id}: a guarded report pins its guards"] else [])
  | .unwitnessed | .answered =>
    if r.pins.isEmpty then [s!"{r.id}: a closed report pins what holds it"] else []
  | .owed owner _ => if owner.isEmpty then [s!"{r.id}: an owed report names its owner"] else []

/-- Every Lean source the tree builds but this registry, stripped to code. -/
def treeText : IO String := do
  let mut text := ""
  for dir in ["LeanTex", "Tests"] do
    for f in ← System.FilePath.walkDir dir do
      if f.toString.endsWith ".lean" && f.toString != "Tests/Reports.lean" then
        text := text ++ stripNonCode (← IO.FS.readFile f)
  return text

end Reports

open Reports in
/-- Every reported breakage is a row, and every row is held. -/
def reportChecks (ref : IO.Ref (List String)) : IO Unit := do
  let t := check ref
  let suite ← suiteText
  let tree ← treeText
  let faults := (reports.zipIdx.map fun (r, i) => r.faults i).flatten
  t s!"reports: every row is well formed ({faults})" faults.isEmpty
  let mut dead : List String := []
  for r in reports do
    for p in r.pins do
      unless ← p.resolves suite do dead := s!"{r.id}: {p.name}" :: dead
  t s!"reports: every pin holds a guard ({dead.reverse})" dead.isEmpty
  let landed := reports.filterMap fun r =>
    let hit := r.owedGuards.filter (wordCount tree · ≥ 1)
    if hit.isEmpty then none else some s!"{r.id}: {hit}"
  t s!"reports: no owed guard has landed unrecorded ({landed})" landed.isEmpty
  let dates := reports.map (·.date)
  t "reports: rows run oldest first" (dates.zip (dates.drop 1) |>.all fun (a, b) => a ≤ b)
  let unw := (reports.filter (·.unwitnessed)).length
  t s!"reports: {unw} unwitnessed, the baseline {unwitnessedBaseline}"
    (unw == unwitnessedBaseline)
  let owed := (reports.filter (·.owed)).length
  t s!"reports: {owed} owed, the baseline {owedBaseline}" (owed == owedBaseline)
  t "reports: a short or cased sha is not a commit"
    (isSha "17ac92f4" && !isSha "17ac92f" && !isSha "17AC92F4")
  t "reports: a path is not an abstract description"
    (isAbstract "a picture node's bold text" && !isAbstract "a file under testdata/corpus")
  t "reports: an owed name is found once it is written, and only then"
    (wordCount "def paramSiteChecks" "paramSiteChecks" == 1 &&
      wordCount "def paramSiteChecksMore" "paramSiteChecks" == 0)
