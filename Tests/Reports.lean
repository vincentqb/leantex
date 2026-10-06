import Tests.DiagAudit
import Tests.Surface
import Tests.Regress
import Tests.Census
import Tests.Conditionals
import Tests.StringConditionals
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
import Tests.MarkdownInput
import Tests.InputUse
import Tests.MathAlphaEntry
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
import Tests.SourceAnnotations
import Tests.InputOrigins
import Tests.ImageOrigins
import Tests.SlideLabels
import Tests.PictureLabelSpacing
import Tests.PictureHtmlBaseline
import Tests.PictureMathLabels
import Tests.PictureBoundary
import Tests.FontDefaults
import Tests.Batch
import Tests.ElabFrameSources
import Tests.LayoutSources
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
  shellReplyChecks listingProviderChecks publicationPathChecks
  htmlContainedChecks htmlContainedRawContextChecks htmlContainedPublicationChecks htmlContainedSvgColorChecks
  htmlContainedCliChecks htmlContainedCorpusChecks
  listingPaletteAuditChecks listingRoleEpochChecks svgAssetChecks animatedGraphicsChecks
  animatedFacesChecks imageContentUrlChecks svgToolChecks markdownInputChecks overlaySetChecks overlayStyleChecks
  overlayContractChecks overlayInputChecks overlaySingletonHtmlChecks diagnosticFormatChecks diagnosticTriggerChecks diagnosticImageOriginChecks diagnosticFontScopeChecks
  diagnosticOriginChecks sourceAnnotationChecks inputOriginsChecks imageOriginsChecks
  tableContextChecks linkMacroLayoutChecks inputUseChecks mathAlphaEntryChecks mathAlphaRegionChecks
  listDeclarationChecks stringConditionalChecks)
open TcolorboxChecks (tcolorboxChecks tcolorboxSourceChecks)
open TcolorboxColors (tcolorboxColorChecks)
open PictureBoundary (pictureBoundaryChecks)
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
    accept := ["the card's own print check recipe — page boxes, cut marks, fonts, exact strings — against the engine's PDF"]
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
    accept := ["the card's own print check recipe, against its lualatex build"]
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
    state := .guarded "f373a48c" .before .audit }
]

/-- The reports guarded but never seen failing: a count that may fall and
never rise, and falls only when this line does. -/
def unwitnessedBaseline : Nat := 10

/-- The reports not closed, the same way. -/
def owedBaseline : Nat := 1

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
