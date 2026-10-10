import Tests.DiagAudit
import Tests.BuildGraph
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
import Tests.MarkdownCode
import Tests.Artifact
import Tests.UnderlineSpacing
import Tests.HtmlTokens
import Tests.HtmlContained
import Tests.Settings
import Tests.Redefine
import Tests.Images
import Tests.SvgImages
import Tests.SvgTools
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
import Tests.BlockFillConditionals
import Tests.BlockRegionFit
import Tests.BlockHeaderClearance
import Tests.FrameArea
import Tests.PaletteTextEpoch
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
import scripts.LandCore

/-!
# Every breakage the user reported, and what holds it closed

The user's rule: a reported breakage gets assertions, theorems or tests that
reproduce it, so the error is never seen again. A row here is one report as a
value: when it came, what broke in abstract words — the construct, never the
document — the pins to its guards, and the run that saw them fail on the
broken tree.

A pin is `DiagAudit.Pin`, so it resolves or does not compile: `thm%` carries
the proof, `check%` elaborates the block and holds only while the suite runs
it, a tier pin while the committed baseline holds its item. What no in-tree
check can see — a private document's own build, a port that invokes the
binary — is an acceptance run, named in abstract words.

A report is closed only as `guarded`, naming the tree its guards failed on
and whose record says so. What is not closed stays visible: `unwitnessed`
(guards, but no failing run on record) and `owed` (no guard yet, the owner
and the guard's name once it lands) are counts the suite holds in both
directions, and an owed guard that lands fails the suite until its row is
promoted.
-/

open LeanTex.Core
open DiagAudit (Pin suiteText)
open Tests (mintedSettingsChecks listingHighlightChecks listingPaletteContinuationChecks
  shellReplyChecks listingProviderChecks listingStyleTableChecks publicationPathChecks
  htmlContainedChecks htmlContainedRawContextChecks htmlContainedPublicationChecks htmlContainedSvgColorChecks
  htmlContainedCliChecks htmlContainedCorpusChecks
  listingPaletteAuditChecks listingRoleEpochChecks svgAssetChecks animatedGraphicsChecks
  animatedFacesChecks imageContentUrlChecks svgToolChecks markdownInputChecks overlaySetChecks overlayStyleChecks
  overlayContractChecks overlayInputChecks overlaySingletonHtmlChecks diagnosticFormatChecks diagnosticTriggerChecks diagnosticImageOriginChecks diagnosticFontScopeChecks
  diagnosticOriginChecks diagnosticContrastOriginChecks sourceAnnotationChecks inputOriginsChecks imageOriginsChecks
  tableContextChecks linkMacroLayoutChecks inputUseChecks mathAlphaEntryChecks mathAlphaRegionChecks
  mathDiagnosticOriginChecks mathDelimiterTriggerChecks mathDollarSurfaceChecks
  diagnosticProducerOriginChecks diagnosticAggregationOriginChecks diagnosticPipelineOriginChecks
  listDeclarationChecks stringConditionalChecks)
open TcolorboxChecks (tcolorboxChecks tcolorboxSourceChecks)
open TcolorboxColors (tcolorboxColorChecks)
open PictureBoundary (pictureBoundaryChecks pictureWrapperChecks pictureShipChecks)
open Tests (fontDefaultsChecks fontDefaultsOverrideChecks blockBarChecks batchChecks)

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
      thm% Ir.recolorRoles_text]
    accept := ["invented title and standout frames paint the audited role ink after direct and nested palette declarations"]
    state := .guarded "09e4aa72" .before .author },
  { id := "R57", date := "2026-09-30"
    what := "an exporter doctype identifier caused a self-contained vector drawing to become a placeholder in both artifacts"
    pins := [check% svgAssetChecks]
    accept := ["synthetic exporter-doctype inputs through the installed converters, with original browser bytes and painted native PDF pixels",
      "the private reference figure rendered from its original vector source"]
    state := .guarded "1c668735" .before .author },
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
    pins := [check% shellReplyChecks, check% listingProviderChecks,
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
    pins := [check% shellReplyChecks, check% listingProviderChecks,
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
      thm% Ir.Design.titledBody_projects, thm% HtmlDoc.titledBodyPaint_agree,
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
    what := "A proof hole in a highlighted listing shipped as a bold keyword instead of its highlighting style's error red, and every token type the style styles beyond a few coarse classes lost its colour and weight, in both artifacts"
    pins := [check% listingStyleTableChecks, check% shellReplyChecks,
      thm% Listing.paint_declared_mem, thm% Listing.paint_style_exact,
      thm% Listing.token_inline_source_exact]
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
  { id := "R128", date := "2026-10-10"
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
  { id := "R129", date := "2026-10-10"
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
  { id := "R130", date := "2026-10-10"
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
  { id := "R131", date := "2026-10-10"
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
  { id := "R132", date := "2026-10-10"
    what := "A slide of running prose read worse than the reference engine's: justified and hyphenated where the slide class sets its text ragged right"
    pins := [check% Tests.LineRhythm.raggedFrameChecks,
      check% Tests.LineRhythm.centredRuntChecks]
    accept := ["a ten-point deck's closing prose slide beside the reference engine's page in both artifacts: ragged right, unhyphenated, at its leading",
      "the same slide's thirteen lines each ending at the reference engine's word, as its ragged right fills every line first"]
    state := .guarded "2b555dcfbad3803d9ebbb3d54fdc8571b36e9ea7" .before .author }
]

/-- The reports guarded but never seen failing: a count that may fall and
never rise, and falls only when this line does. -/
def unwitnessedBaseline : Nat := 10

/-- The reports not closed, the same way. -/
def owedBaseline : Nat := 2

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

/-- What is wrong with a row, or nothing: its identity, its words, and a
state its pins can carry. -/
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

/-- Every Lean source the tree builds but this registry, stripped to code:
where an owed guard's name appears once it lands. -/
def treeText : IO String := do
  let mut text := ""
  for dir in ["LeanTex", "Tests"] do
    for f in ← System.FilePath.walkDir dir do
      if f.toString.endsWith ".lean" && f.toString != "Tests/Reports.lean" then
        text := text ++ stripNonCode (← IO.FS.readFile f)
  return text

end Reports

open Reports in
/-- **Every reported breakage is a row, and every row is held.** Rows are
well formed and in order; every pin resolves; an owed guard that has landed
fails until its row is promoted; and the unwitnessed and owed counts equal
their baselines, so closing a report and opening one are both edits here. -/
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
  -- The judges, once each way.
  t "reports: a short or cased sha is not a commit"
    (isSha "17ac92f4" && !isSha "17ac92f" && !isSha "17AC92F4")
  t "reports: a path is not an abstract description"
    (isAbstract "a picture node's bold text" && !isAbstract "a file under testdata/corpus")
  t "reports: an owed name is found once it is written, and only then"
    (wordCount "def paramSiteChecks" "paramSiteChecks" == 1 &&
      wordCount "def paramSiteChecksMore" "paramSiteChecks" == 0)
