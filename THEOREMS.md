# Verification guarantees

An index of what Lean proves, by area; each declaration states its exact hypotheses. A proof marked
by unfolding holds by unfolding the definition it names, a check on that one definition. A name
written owed (Uxx) is a guarantee that unit delivers; `scripts/cites.lean` holds every name here to
one declaration and fails an owed name once it resolves.

## Headline: nothing is lost silently

For every document and font environment leantex produces a result; the text of each artifact (the
PDF's text layer, the HTML page's text, the markdown twin) is the source's text less exactly the
pieces its diagnostics name, each named once; every artifact is well formed; and the result depends
only on the document, the fonts and the output name. Resemblance to lualatex is not part of it: the
tiers measure that. In Lean terms, over the stages `Cli.Driver.build` runs:

```lean
-- One run of file f with bytes b, font environment E (the host's faces and cfg.fontDirs) and
-- configuration cfg; the driver answers each host question the pure stages ask.
src                 ← Input.readDocument f b      -- decode, Surface.read, includes, execution
p                   := Elab.prepareExecuted f src.executed
(doc, dElab, spans) := Elab.runPrepared f p src.diags metric wd
dFront              := Bib.accountFront (dElab ++ dSty) dBib notes refs
doc'                := passes doc  -- Input.resolveBibliography, FigureAlt.titled,
                                   -- Ir.resolveMathAlphas, Ir.squeezeFrames, Layout.pdfView
fitted              := Layout.runFitted geom fs pats doc' imgs
pdf                 := Pdf.writeChecked geom fs fitted.out.pages doc'.info imgs …
(html, dHtml)       := HtmlDoc.emit cfg doc'
md                  := MarkdownDoc.emit doc' bibName
D                   := every diagnostic the run reports: each phase's batch through
                       Diag.resolveAll (Diag.forOutputs outs batch), and the refusals Ui.diag prints
-- The driver elaborates again when list notes renumber, a settled face measures a label
-- otherwise, or a picture withdraws; doc and dFront above are the run that ships.

-- A text is its characters, each with its origin: a byte of a source file, or generated.
inductive Origin | source (file : String) (offset : Nat) | generated
srcText ex : List (Char × Origin) := Parse.rawText ex.raws         -- the executed text slots
irText doc : List (Char × Origin) := Ir.foldDoc located [] doc      -- Ir.plainText's characters,
  -- each under its innermost .located span; erased, Ir.blocksText doc.body, then each
  -- Ir.furnitureInlines region's Ir.plainText
text A     : List (Char × Origin)  -- what a viewer extracts from A, with the origins A marks
lost D A   : List Diag :=
  (Diag.forOutputs #[A.output] D).filter (·.kind.loss ∈ [.dropped, .pending])
named D A  : Set Origin := ⋃ {(Diag.piece d).origins | d ∈ lost D A}
keep P t   : String := String.mk ((t.filter fun (_, o) => o ∉ P ∧ o ≠ .generated).map (·.1))

theorem compile_text_accounts (cfg : Cli.Config) (src : Document) (E : FontEnv) :
    let r := compile cfg src E      -- the stages above; src is f and every file the run reads
    ((∀ d ∈ r.D, ¬ d.kind.stopsWriter ∧ d.kind ∉ [.E0003, .E0005, .E0006, .E0606, .E0607]) →
      r.shipped = r.emitted) ∧
    (∀ A ∈ r.shipped,
      Text.norm (keep (named r.D A) (text A)) = Text.norm (keep (named r.D A) (srcText r.ex)) ∧
      ((lost r.D A).map (·.piece)).Pairwise Disjoint) ∧
    (PdfCensus.census r.pdf).isOk ∧
    HtmlDoc.scripts r.html ⊆ {HtmlDoc.deckScript} ∪ r.boundaryText ∧  -- the file read, if declared
    ∀ cfg', cfg'.output = cfg.output → cfg'.mathBoundary = cfg.mathBoundary →
      cfg'.fontDirs = cfg.fontDirs → let r' := compile cfg' src E
      ∀ A ∈ r.shipped, A ∈ r'.shipped → r'.bytes A = r.bytes A
-- A result exists because every stage is total and terminates. Only dropped and pending losses
-- excuse text: an error or a warning the default run shows, a repeat its shown line counts
-- (Diag.foldRepeats), or a loss the document accepts. srcText is read after execution, so
-- decoding, lexing, includes and execution owe the same equation from the source bytes (U111).
-- Text.norm: NFC, a white-space run as one space, TeX's ligature and quote spellings as the
-- characters they set, a line-end hyphen joined.
-- Composition, for each artifact A: surface ∘ elaboration ∘ passes gives
-- keep (named dFront A) (irText doc') = keep (named dFront A) (srcText ex); each backend gives
-- keep (named D A) (text A) = keep (named D A) (irText doc'); the accounting gives
-- src.diags ⊆ dFront ⊆ D, up to site counts and demotion, so named dFront A ⊆ named D A.
```

| Stage | Proved | Owed |
|---|---|---|
| A result | No declaration is marked partial or unsafe (`bannedWord`, `scripts/ProofAudit.lean`). | owed (U72): `partialReachChecks`; owed (U77): `lookupUser_latest_exact`, `Elab.expandUser_depth_between` |
| Ships unless stopped | tested: `machineLossChecks` | owed (U37): `DiagCode.error_iff_fatal`, its writer-stopping causes widened to the output name's and publication's refusals |
| Surface: bytes to raws | `writtenRange_source_exact`, `markMacro_source_exact`, `read_tex_exact`, `Code.segmentsOf_source_exact`, `Md.desugar_vocabulary_mem`, `elabBlocks_input_exact`, `markdownInput_blocks_text`, `rewriteCtrl_accounts` | owed (U07): `lex_verbatim_exact`; owed (U44): `MdParse.blocks_accounts`; owed (U111): `Compat.executeInputs_text_accounts` |
| Elaboration and IR passes | `Ir.mapInlines_text`, `Ir.mapBlocks_text`, `Ir.numberFloats_text`, `Ir.markDisplay_text`, `Struct.ofDoc_text`, `texGroup_scope_id` | owed (U111): `Parse.rawText`, `Diag.piece`, `Elab.runPrepared_text_accounts`, `Driver.passes_text_accounts` |
| Accounting: every loss reaches D once | `Elab.runPrepared_reports_contract`, `Elab.accountFront_reports_contract`, `Layout.runFitted_projects`, `Layout.runFitted_accounts`, `Diag.foldRepeats_shown_exact`, `Diag.foldRepeats_visible_inj`, `Diag.tallySites_sum_exact` | owed (U112): `Driver.build_reports_contract` |
| PDF text layer | `mcids_partition_covers`, `parentTree_covers`, `Layout.Census.runPost_body_exact`, `PageOut.shipped_lines_exact` | owed (U110): `Layout.runFitted_text_accounts`; owed (U21): `PdfContent.extract_text` |
| HTML page text | `escapeText_spec`, `mathml_glyphs_agree` | owed (U110): `Html.parse_render_exact`, `HtmlDoc.emit_text_accounts` |
| Markdown twin | `rowLine_cells_exact` | owed (U49): `MarkdownDoc.escape_read_id`; owed (U110): `MarkdownDoc.emit_text_accounts` |
| Well formed | `parseVal_render_id`, `objTable_inj`, `objTable_covers`, `xrefEntries_index_exact`, `WritePlan.readback_exact`, `escapeText_no_lt`, `escapeAttr_no_quote`, `rawPayload_no_terminator`, `math_boundary_contract`; tested: `htmlContainedCorpusChecks` | owed (U113): `HtmlDoc.emit_scripts_mem` |
| Document, fonts and name alone | `Host.record_replay_exact`, `Prog.runM_only_exact`; by unfolding: `artifact_flag_free`; the driver's reads, by a line scan: `undeclaredConfigRead` | owed (U112): `Driver.build_flag_free` |
| The headline | the rows above, composed | owed (U112): `compile_text_accounts` |

Three gaps keep the composition open:

- Termination: every function a run calls returns. The kernel checks each declaration's measure,
  but do-notation repeat and while loops compile to a partial combinator, and use-time macro lookup
  (X4) must expand the definition visible where a macro is used while expansion stays within a
  depth the document bounds, deeper recursion stopping as a named loss as TeX's own limit does.
  owed (U72): `partialReachChecks`, no partial constant reachable from the binary's entry, read off
  the compiled closure; owed (U77): `lookupUser_latest_exact`, `Elab.expandUser_depth_between`.
  Modules: `scripts/ProofAudit.lean`, `LeanTex/Core/Elab.lean` and the loops' own, most in
  `LeanTex/Core/Layout.lean`.
- Elaboration conservation: for each artifact A, through execution, both of Elab's knots and the
  driver's IR passes, keep (named dFront A) (irText doc') = keep (named dFront A) (srcText ex), the
  pieces of distinct diagnostics disjoint, and execution keeps the decoded source's text slots the
  same way. srcText reads the executed surface's text slots, each argument a control's registry
  signature types as text, with its offsets; a diagnostic's piece is the source range its loss
  covers, where a span holds only its start today. owed (U111): `Parse.rawText`, `Diag.piece`,
  `Compat.executeInputs_text_accounts`, `Elab.runPrepared_text_accounts`,
  `Driver.passes_text_accounts`. Modules: `LeanTex/Core/Parse.lean`, `LeanTex/Core/Compat.lean`,
  `LeanTex/Core/Elab.lean`, `LeanTex/Core/Diag.lean`, `LeanTex/Core/InputContract.lean`,
  `LeanTex/Cli/Input.lean`, `LeanTex/Cli/Driver.lean`.
- Artifact text: a model of what a viewer extracts, against which each backend's census is proved.
  For the PDF, PDF 2.0's text extraction: content-stream strings through each font's ToUnicode map
  in marked-content order, Artifact content generated, origins from the structure tree's marked
  content, and set lines carrying the IR text; owed (U21): `PdfContent.extract_text`; owed (U110):
  `Layout.runFitted_text_accounts`. For HTML, a model of the WHATWG parse over the emitted subset
  that reads the rendered bytes back as their tree, its text the text nodes in tree order outside
  style and script; owed (U110): `Html.parse_render_exact`, `HtmlDoc.emit_text_accounts`. For the
  twin, the markdown reader's text of the emitted file, whose losses need a diagnostic channel
  `MarkdownDoc.emit` lacks today; owed (U110): `MarkdownDoc.emit_text_accounts`.
  Modules: `LeanTex/Core/PdfContent.lean`, `LeanTex/Core/Layout.lean`, `LeanTex/Core/Html.lean`,
  `LeanTex/Core/HtmlDoc.lean`, `LeanTex/Core/MarkdownDoc.lean`, `LeanTex/Core/MdParse.lean`.

## Surfaces

| Area | Guarantee | Proofs |
|---|---|---|
| Source spans | Lexing, comments and macro marking keep the written source and its paragraph breaks. | `writtenRange_source_exact`, `markMacro_source_exact`; by unfolding: `blank_line_par_agree`, `scopeEnv_source_exact` |
| Surface door and includes | Each surface is read through one door, the tex door being its two stages; an include standing as its own block sequence is transparent whatever blank source stands around it, and included markdown sets the text it sets alone; the splice returns the raws the compatibility pass kept at the place standing for them, under the invocations enclosing it. | `elabBlocks_input_exact`, `markdownInput_blocks_text`; by unfolding: `read_tex_exact`, `Parse.spliceKeptList_keptRaw` |
| Lexical forms | Owed: verbatim, URL and delimited-verbatim captures are exact per table row. | owed (U07): `lex_verbatim_exact`; owed (U38): `lex_word_boundary_preserved` |
| Key=value and signatures | A list cut at its separators outside groups joins back to itself, and so do a comma list cut outside braces and a CSS list cut outside blocks, strings and escapes; no piece holds a separator outside its groups, so cut again it is itself; a CSS list is cut only between its atoms, so never inside a string, an escape or a block, and a block the reader closes ends at its opener's mirror. Owed: argument slots read a prefix and apply defaults exactly. | `KeyVal.splitTopAt_join_id`, `KeyVal.split_join_id`, `Css.splitList_join_id`, `KeyVal.splitTopAt_fixed_point`, `KeyVal.split_fixed_point`, `Css.splitList_fixed_point`, `Css.splitList_atoms_exact`, `Css.closedAtom_mirror`; owed (U52): `readArgs_prefix_exact`, `readArgs_default_exact` |
| Declarations | A string reads back from its literal whatever quotes it holds; a declaration marker reads back from its name, and no control name Lex reads, one character or a run of name characters, is a marker's; a setting's carrier (a page, tokens, palette, style, fonts, metadata, chrome or block setting) is its declaration's tokens around one word whose block, the one its translation note names, the declarations' raw entry reader reads back entry by entry as exactly the setting's kept entries, reading one word as the declaration splitter reads its text; every page and metadata key reads back from its name. Owed: PDF metadata projects one IR value; documents cannot spell engine names. | `Decl.parseValue_quote`, `Marker.read_name_exact`, `Marker.read_ctrlWord_exact`, `Native.render_parse_exact`, `Native.body_read_exact`, `Entries.read_word`, `Native.PageKey.ofName_name`, `Native.MetaKey.ofName_name`; owed (U51): `pdfmeta_projects`, `toName_unforgeable` |
| Compatibility | An empty rewrite of a control is paid for by a diagnostic or a write; the control table's names are distinct and clear of \cite, \appendix and \define; at a body cursor, or a preamble one outside a deck, a row's control its leaves do not keep consumes exactly what its signature reads, its emission in its place, and a row missing an argument that must stand, or kept by a leave, is left to elaboration; at a body cursor a quiet row of groups (a silent row, or a declaration the body ignores whose row keeps it nowhere) consumes exactly its group prefix and is paid for; between literal neighbours a document's result is the same whatever the operands of a row that reads none hold. | `rewriteCtrl_accounts`, `ctrlRows_sound`, `ctrl_rows_consumed_contract`, `argsRead_groups_exact`, `ctrlRow_operands_agree`; owed (U88): `rewriteCtrl_unknown_id` |
| Markdown | The desugaring lowers every markdown source into its declared vocabulary, at every depth, a Lean division into one request that reads back as exactly its file and attributes; a pipe-table row the twin writes reads, under the stated model of GFM's row reading, as exactly its cells. One step of the inline scan over raw HTML advances inside its stretch and either ships a token and raises nothing, names the raw HTML once at its `<`, or reads a comment that hides only itself; the tokens it ships are a hard break or an anchor, and the memoized tag reader answers as the unmemoized one. Owed: every block is accounted for; emphasis is laminar; the twin's escapes read back. | `Md.desugar_vocabulary_mem`, `Md.LeanDivision.ofRaw?_raw`, `rowLine_cells_exact`, `htmlInlineAt_accounts`, `htmlInlineAt_covers`, `htmlTagAtM_tag_exact`; owed (U44): `MdParse.blocks_accounts`, `MdParse.matchEmphasis_laminar`; owed (U49): `MarkdownDoc.escape_read_id` |
| Code files | A code file's segments hold every source character once, in order, a blank segment white space alone and the directive's one line; its code pieces, in page order, hold exactly its code segments, in source order, and its documentation comments stand in source order; the document's body is its pieces' raws under the page its plan sets, the reference list its citations call for placed among them and none on a page without a bibliography, each code piece holding more than white space exactly one listing of its code where the page shows code, and one of white space alone none; the reader lowers every file into its declared vocabulary, which admits no request a driver must fulfil and a formula only on a Lean file's page, and an inclusion every Lean file into it, inside the one input environment naming the file; every view and every code language is listed. | `Code.segmentsOf_source_exact`, `Code.segmentsOf_blank_white`, `Code.segmentsOf_directive_line`, `Code.assemble_code_exact`, `Code.assemble_prose_exact`, `Code.readPieces_body_exact`, `Code.read_body_exact`, `Code.placedBody_none`, `Code.pieceRaws_code_exact`, `Code.pieceRaws_white_exact`, `Code.read_vocabulary_mem`, `Code.read_vocabularyFor_mem`, `Code.vocabularyFor_lean`, `Code.includeLean_vocabulary_mem`, `Code.vocabulary_requests`, `Code.View.all_complete`, `Ir.CodeLang.all_complete` |
| Lean statements | A statement stands between a Lean file's code pieces and holds none of its code: the pieces still hold exactly its segments' code, in source order, which with no proof folded or removed is the file's code; a page keeps facts only where they line up with its file, and one asked for statements with none shows the file's code; the notation table's output determines the constant it was given. | `Code.withStatements_code_exact`, `Code.pagePieces_code_exact`, `Code.withFolds_nil`, `LeanFacts.judge_aligned`, `Code.planOf_unanswered_exact`, `LeanNotation.shownOf_inj` |
| Lean statements in words | A statement's tokens, the words, full stop and block bounds a page sets its sentence's lines from, read back as the statement under a well-formed lexicon whose templates it uses, so no two such statements share their tokens; every statement said in words uses only its table's templates, with their arities; the core table is well formed and a page's stays so with each phrase its directive declares, so every sentence a page sets reads back as the statement it says. | `LeanProse.parse_render_exact`, `LeanProse.render_inj`, `LeanProse.Term.parse_render_exact`, `LeanProse.Term.render_inj`, `LeanProse.stmtOf_mem`, `LeanProse.proseOf_parse_exact`, `LeanProse.coreTable_contract`, `LeanProse.tableFor_contract`, `LeanProse.page_parse_exact` |
| Bibliographies | BibTeX's and biber's inheritance are exact, as is what a parent lends under biblatex's rules; biblatex's numbered list marks each item as its citations do; cite-free content adds no citation to the census; reading a field never fails the build; every citation-setup declaration reads back from the word that carries it, so a carried setup reads back whole. | `crossref_inherit_exact`, `biberInherit_exact`, `lent_plain_exact`, `bblItems_marker_exact`, `citeFree_census`, `FieldDoor.readWith_ships_contract`, `CiteDecl.spelling_read_exact`, `Parse.citeSetupRaws_read_exact` |

## Elaboration

| Area | Guarantee | Proofs |
|---|---|---|
| Termination | Owed: elaboration terminates. No declaration is marked partial and both knots recurse on lexicographic measures the kernel checks, but do-notation repeat loops still compile to a partial combinator. | owed (U72): a semantic lint over reachable constants, the repeat loops rewritten |
| Macro visibility | Owed: a call resolves to the definition visible at that point. | owed (U77): `lookupUser_latest_exact` |
| Registry and input stack | Owed: classification comes from one table, each marker decoded once before the knot reads it; frame pushes decrease the measure; independent keys commute. | owed (U87): `Elab.classify_exact`, `Elab.push_frame_lt`, `Elab.keyed_comm` |
| Group scope | A group's end, block or inline, restores the declaration state its start held, with the global assignments logged inside replayed over it; with none logged, a group, an environment holding block content and a braced group of block content with no paragraph end inside each leave the state as they found it. | `texGroup_scope_id`, `elabBlocks_env_scope_id`, `elabBlocks_group_scope_id`; by unfolding: `texGroup_scope_exact`, `inlineGroup_scope_exact` |

## IR

| Area | Guarantee | Proofs |
|---|---|---|
| Walk census | The generic maps conserve the text census whenever their leaf function does, and the walks named here conserve theirs; the generic fold reads a reference list's marker and then each entry's content in order, so every collector over it reads a field's inlines as it reads the body's. | `Ir.mapInlines_text`, `Ir.mapBlocks_text`, `Ir.numberFloats_text`, `Ir.dimBlocks_text`, `Ir.coverInlines_text`, `Ir.anchorReferents_text`, `Ir.floorMask_id`, `Ir.foldBlock_bibliography_exact`; owed (U92): the generic walk's identity, fusion and census laws |
| Numbering | A block's floats take consecutive numbers from their kind's counter, which advances by exactly as many; by chapter, a figure or table numbers one past its chapter's count and one where its chapter began, a chapter keeping its number included, and blocks whose figures and tables all belong to the chapter the counters stand in give them the numbers after its count, one each with no gap; a deck's frame shows none where it is numberless (plain, standout, or a title page its theme leaves bare), else the count of numbered frames up to it, which is the frame's own number where the count numbers it. | `numberFloatOne_exact`, `numberFloatOne_chapter_exact`, `shownFrom_exact`, `frameShown_numbered`, `number_gapless_within`; owed (U11): `frameNumbers_keepFor_gapless` |
| Anchors and readiness | Owed: anchor rendering is injective and ids unique per view; no unresolved reference reaches a backend. | owed (U12): `Anchor.render_inj`, `Ir.anchors_nodup`; owed (U66): `Ir.resolve_ready` |
| Shared facts | A frame's foot band is a projection of one slot pair; over the shipped gap table the two backends' block gaps stand in one proportion (checked by decide); the frame title's pair is the one its palette resolves; the stylesheet's fallback for a table length spells the length the page sets an undeclared table by. | `Chrome.footBand_projects`, `backend_gaps_agree`; by unfolding: `frametitle_agree`, `table_length_agree`; owed (U09): `heading_family_agree`; owed (U41): `Ir.title_agree`, `Ir.lang_agree` |
| Leading | A run no larger than its paragraph leads between nothing and the paragraph's own leading, and a larger run never leads less; under the size file's columns a step's leading clears its type by at most the file's loosest proportion. | `runLead_between`, `runLead_monotone`, `stepLead_between` |
| Pictures | A picture lowers to one vector figure both backends emit: the PDF's operators and the SVG's typed tree read back as the same marks, each the figure's own, whatever the placements and resource naming; the print grid is a fixed point; the ink box covers every mark's ink and every label's measured box; a repaint and the grid keep the figure's words. | `backend_marks_agree`, `picture_marks_agree`, `GfxPdf.marks_projects`, `GfxSvg.marks_projects`, `Figure.quantize_fixed_point`, `Figure.inkBox_covers`, `Figure.said_text` |
| Picture geometry | A diagram's cells are a rectangle and an arrow ends on its cell's border; a clip covers what follows it, a scope's transformation runs inside the one in force, and a colour group sets only its own statements; an arc ends at its end angle and a rounded corner stays inside its corner; a shading's stops are pgf's; both artifacts paint a picture's labels in statement order, and repainting moves no mark. | `Cd.cells_rectangular`, `arrow_border_exact`, `clip_covers`, `scope_compose_exact`, `colorGroup_exact`, `arc_end_exact`, `roundedCorners_between`, `shade_stops_exact`, `picture_labelOrder_agree`, `Node.recolor_geomBox_id` |
| List spacing | A list declaring nothing spaces as its level does, and each value a list declares is its spacing's whatever its level's; a later scope's values stand over an earlier one's, and stand so applied twice; under KOMA-Script's classes a level one to three opening where the `\parskip` in force is positive takes it as its `\parsep`, with no `\topsep` and no `\itemsep`, beneath what the list declares; a quotation's own keys, quotation's `\parsep` and verse's `\itemsep`, are its spacing's wherever its lineage sets lists. | `Ir.listSpacing_undeclared_exact`, `Ir.listSpacing_declared_exact`, `Ir.ListSet.over_absorb`, `Ir.ListExtra.koma_exact`, `Ir.quoteSpacing_own_exact` |
| Trivlist spacing | A trivlist inside a list reads its level's `\topsep`, which the list's declared one does not reach, and the list's `\partopsep`, declared or its level's; under KOMA-Script's classes a list whose `\topsep` its level does not set leaves its trivlists none where that `\topsep` is not zero and its `\parsep` is positive, as enumitem's `\@list@extra` does again; outside every list it opens size10–size12.clo's `\@topsepadd` at 10pt, 11pt and 12pt and beamer's at 11pt. | `Ir.TrivIn.within_declared_exact`, `Ir.TrivIn.within_koma_exact`, `Ir.trivIn_exact` |
| Tables and highlights | Owed: tables are rectangular; installing highlights conserves text. | owed (U53): `Table.rect`; owed (U67): `installHighlights_text` |

## Dimensions and line breaking

| Area | Guarantee | Proofs |
|---|---|---|
| Arithmetic | Points, literals and local references evaluate exactly; badness is capped at 10000; a length and a ratio print, character by character, as their digits. | `toBpString_chars_exact`, `ratString_chars_exact`; by unfolding: `pt_exact`, `resolve_lit_exact`, `Affine.resolveWidth_ref_exact`, `badness_le`; owed (U42): `GlueSet.width_sum_exact`, `scaleRound_between` |
| Validity | Chosen breaks form a valid chain over the box characters, and a box's width is the exact sum of its advances and kerns. | `kpScan_valid`, `kpBack_chain`, `kp_boxChars`, `kern_measure_exact` |
| Optimality | Owed: the pruned breaker equals the reference dynamic program, which is optimal. | owed (U73): `kpRef_optimal`, `kp_eq_kpRef` |
| Setting | A code line wraps only after a unit that is no space, never inside a token, whitespace first where a space fits, each line filled to its last wrap that fits; inline code ships its source scalar for scalar. Owed: set lines stay within the measure; listing wraps conserve text. | `codeWraps_breaks_mem`, `CodeUnit.rank_mem`, `codeCut_space_mem`, `codeCut_between`, `inlineCode_source_exact`; owed (U39): `setLine_within_measure`; owed (U02): `listing_wrap_text` |
| Hyphenation | Breaks respect the language minima. | by unfolding: `hyphenate_respects_min` |

## Pages and frames

| Area | Guarantee | Proofs |
|---|---|---|
| Placement | Placement is exact and floats stay whole; a page that is not blank ships at a boundary and as the last page. | `place_exact`, `runFloat_whole`, `runFloat_frames`, `runFloat_reflows`, `brk_ships_exact`, `closeLast_ships_exact` |
| Two sides | Facing pages mirror: a verso's left margin and its recto's sum to the width the text block leaves; moving a page's ink keeps every line and picture and the ground at the medium's edge. | `Ir.PageSpec.leftMargin_mirror`, `PageOut.shiftX_keeps` |
| Frames | The overflow ladder sets a fitting frame as declared, and an overfull step's overhang is positive and within its clearance; every frame it moved is named once, by what it did, a continuing one as continuing, and what it ships is one setting of an IR document. | `frameFit_id`, `frameFit_between`, `frameFit_accounts`, `runFitted_accounts`, `frameAccount_covers`, `runFitted_projects` |
| Hidden content | Shipping a page keeps its place: a shipped segment advances as far as the one it ships, repainting one keeps its advance, a segment carrying no hidden ink ships as it stands, a shipped page stands every line where it stood, and no shipped line carries hidden ink. That a hidden step's page is the page showing its argument less the argument's ink, its fills, pictures and links included, is tested. | `Seg.shipped_advance_exact`, `Seg.hide_advance_exact`, `Seg.shipped_id`, `PageOut.shipped_lines_exact`, `Seg.shipped_hides_exact`, `PageOut.shipped_hides_exact`; tested: `overlayVisibleChecks` |
| Block rules | A rule beside a whole titled block is one rule, its title's part ending where its body's begins, and a rule its lines' half leading past them stands centred on their capitals. | `edgeLinesFrom_abuts_exact`, `edgeLinesSpan_centred_exact`, `BlockMetric.halfLeading_centred_exact` |
| Keeps and floats | Owed: float order is monotone within a kind and bounded by the next flush. | owed (U40): `float_order_monotone`, `float_page_between` |

## Fonts, shaping and math

| Area | Guarantee | Proofs |
|---|---|---|
| Face choice | Picks do not depend on scan order; the default mono companion is drawn from the sourced rows and answers every corner with its own fixed-pitch face; the platform default for an undeclared typewriter slot sets no corner it cannot serve, a family the scan serves as a typewriter family is served whole or upright, and lualatex's shapes are met where they are taken. | `leastBy_set_eq`, `pickCompanion_set_eq`, `monoCompanion_mem`, `monoCompanion_contract`, `monoDefault_contract`, `monoFor_contract`, `servesMono_contract`, `latinModernMono_contract`; owed (U10): `resolveSized_between`; owed (U35): `slotFill_mem`, `slotFill_set_eq` |
| HTML faces | The page ships the faces its uses select and the faces the document's runs ask: each use ships the face CSS font matching selects, nothing else ships, and each use selects from the shipped faces what it would from every face; every face the document's runs ask both backends for ships (that the cascade reading finds every use the page makes is tested, `faceUseChecks` and the browser runs, not proved); slots resolving to the same faces share the first one's family, which resolves them and serves itself, and every stack opens on a slot resolving a face once the body resolves one; each character the page's text asks falls back to the face it would with every face shipped, and each `@font-face` ships once. | `shipFaces_covers`, `shipFaces_used`, `shipFaces_select_exact`, `shipFaces_required`, `select?_filter`, `html_fonts_cover_pdf`, `Families.familySlot_faces`, `Families.familySlot_idem`, `Families.stackSlot_resolves`, `html_subset_covers`, `fallback_exact`, `shipFaces_nodup` |
| Font templates | A font template written from selections reads back as them, axis by axis, and a block title's font reads as its kind's own selection where it makes one and the plain block's elsewhere, as beamer's parent chain sets it. | `FontAxes.template_exact`, `blockTitleFont_axes_exact` |
| Shaping and extraction | Owed: clusters cover the text; extraction yields the IR text. | owed (U59): `shape_clusters_covers`; owed (U21): `PdfContent.extract_text` |
| Math | A formula's MathML carries exactly its own glyph text, whatever its attributes and marks, while its agreement with the PDF's coverage census is tested, not proved; it sets every text run longer than one scalar under a style keeping its line, as TeX sets a word in one box, and so does a native picture label; alphabet resolution is a fixed point over the whole document; a cancellation's ink ray lies between its bounds. | `mathml_glyphs_agree`, `MathMl.formula_linesHeld_contract`, `MathMl.formulaRow_linesHeld_contract`, `HtmlDoc.labelNodesList_linesHeld_contract`, `Ir.resolveMathAlphas_fixed_point`, `inkRayOrigin_between`; tested: `mathmlChecks`; owed (U17): `scriptShifts_between`, `Math.assemble_covers` |

## Colour and contrast

| Area | Guarantee | Proofs |
|---|---|---|
| Registry | Every default reads only shallower roles, so resolution terminates, and a role is its declaration, else its default over resolved roles; a key names one role, and no role, author colour or token name collides with another or with a layout property; the stylesheet's table, aliases chased, is the resolver, and a page's roles are closed under their aliases. | `Role.fallback_depth_monotone`, `Design.resolve_unfold_exact`, `Role.key_inj`, `CssName.ident_inj`, `CssName.ident_internal`, `role_css_projects`, `Design.cssDecl_chase_exact`, `cssRoles_closed` |
| Judging | The sites cover the registry, and the judged pairs cover its sites where they ship; a passing site leaves the report as it was; the registry's defaults meet their needs in every scheme; every site a shipped bundle paints reads, in print and on the light screen, but the roles its lineage reports, and every shipped muted ink reads with a margin. | `Design.sites_covers`, `judged_covers`, `judgeSite_id`, `default_sites_contract`, `builtin_palettes_contract`, `builtin_palette_contract_engine`, `Theme.builtin_sites_contract`, `builtin_muted_contract` |
| Declared colours | An author colour never repaints a role, and an xcolor colour declares one only by a code role's key; declared colours ship exactly in print and on their own screen, and a bundle's lineage colours as its source sets them; the document's colour outranks a generated one, and the seeds ship exactly, no binding rewriting one. | `Palette.defineColor_design_id`, `Palette.defineXcolor_design_id`, `Palette.defineXcolor_role_exact`, `Design.light_print_exact`, `moloch_lineage_exact`, `Palette.applySeedsUnder_keep_exact`, `generate_seeds_exact`, `bindings_seeds_exact` |
| Code colours | A colour shipped as declared is one the palette declares, under the key it ships under, and every other ships under the role's own key; the style decides a role only where the rule leaves it open, and a role no style reads resolves alike under every style; two types of one role paint alike; a tone clears what it was asked to on every ground it was asked for. | `resolve_declared_mem`, `resolve_derived_exact`, `derive_none_opens`, `resolve_style_exact`, `paint_role_exact`, `toneOn_contract` |
| Generated colours | Every site a generated palette creates meets its target, each ground in its band and a block's title band apart from its body, and its derived text tones keep the covered-state contract at a share that binds, its seeds as given; gamut mapping holds lightness and hue, never adds chroma, and leaves an in-gamut colour as it was. | `generated_sites_contract`, `generated_cover_contract`, `tint_between`, `blockPair_between`, `Okl.gamutMap_between`, `Okl.gamutMap_id`, `Okl.toGamut_between` |
| Schemes | An ink a scheme's view carries meets that scheme's gate on every ground it is judged on, its hue held and its chroma no more than declared; a more-contrast scheme never owes less; a dropped scheme is paid for, each colour it could not carry named on its subject. Owed: every role-coloured run is judged. | `Palette.carryOn_between`, `requiredIn_monotone`, `scheme_drop_accounts`, `sites_named`; owed (U61): `DesignRole.judged_complete` |

## HTML

| Area | Guarantee | Proofs |
|---|---|---|
| Escaping | Text, JSON and CSS strings hold no '<', attributes no quote, raw payloads no terminator; the text and attribute escapers are their character-by-character definitions, and the terminator search over a payload's bytes finds exactly what a search of its lowered characters finds. | `escapeText_no_lt`, `escapeAttr_no_quote`, `escapeJson_no_lt`, `HtmlDoc.cssString_no_lt`, `rawPayload_no_terminator`, `escapeText_spec`, `escapeAttr_spec`, `holdsTerm_exact`; owed (U62): `cssString_no_quote` |
| Captured resources | Each data URL a page carries is its resource's own, computed once for the page: base64 maps every sextet to RFC 4648's alphabet through a table that is that alphabet, a resource's cached URL is its data URL, the page's table answers every image, static face and font program as the per-use definitions do, and its resources are the page's in order. | `sextet_rfc4648`, `alphabet_rfc4648`, `Embedded.uri_exact`, `PageResources.imageHref_exact`, `PageResources.posterHref_exact`, `PageResources.fontHref_exact`, `PageResources.resources_exact` |
| Script policy | With scripting off the deck is the pure-CSS pager: no floor rule dims a step unless the script's marker gates it, no rule hides content but behind that marker, and every rule hiding a step's content opens on the marker or is a keyframe, which only rules opening on the marker run; the math renderer ships only where the run declares one, and with scripting off the page is the page without it. | `floor_covered_script_gated`, `content_hidden_behind_script`, `hidden_script_gated`, `animations_script_gated`, `math_boundary_contract`, `math_boundary_floor_exact` |
| Print agreement | The printed web page paints each role as the PDF does, and its list marker is the PDF's. | `html_print_agree`, `marker_css_agree` |
| Covering | A deck epoch's step share is the covered fraction the PDF covers by, and it hides a pending step on the web page exactly where the PDF's cover of the same palette hides it. | `HtmlDoc.Config.epochShare_projects`, `HtmlDoc.Config.epochShare_hides_agree` |
| Anchors and stage names | A claimed anchor or stage name is what probing every numbered form of its base among the names claimed before finds: the first free form, and the first holder met whose title differs; each claim adds exactly its form, which no earlier claim holds, and the memo that skips held forms is a lower bound from the empty ledger through every claim. | `NameClaim.Claims.claim_exact`, `NameClaim.Claims.claim_taken`, `NameClaim.Claims.claim_fresh`, `NameClaim.Ledger.empty_pinned`, `NameClaim.Ledger.claim_pinned` |
| Picture SVG | Element ids are injective and read back; the spelled tree wraps a picture's labels in plain SVG and nests no second math root; every shipped label baseline projects the IR's measured band. | `ids_inj`, `parseId_svgId_exact`, `spell_plain_contract`, `pictureKids_unnested_contract`, `pictureLabelBaseline_projects` |
| Layout contracts | One gap owner per boundary, kept when the rules read through overlay carriers; print lifts cover stage bounds; the deck CSS partitions by feature. | `blockGap_owner_contract`, `blockGapThrough_owner_contract`, `print_lifts_stage_bounds_covers`, `deck_css_partition` |

## PDF

| Area | Guarantee | Proofs |
|---|---|---|
| Objects and xref | Values round-trip; the object table is injective and covering; xref entries index exactly. | `parseVal_render_id`, `objTable_inj`, `objTable_covers`, `xrefEntries_index_exact` |
| Object index | A file's object index finds the entry the reader's linear search finds, so a reference resolves through it as it resolves through the entries. | `PdfCensus.Index.find?_exact`, `PdfCensus.Index.deref_exact` |
| Object streams and xref widths | Every object stream holds between one and its capacity of objects; every xref row fits the widths the writer declares, read off the rows, and the index field is one byte for every document; the subsection reader recovers every location the plan's payload encodes, and a plan within bounds reads back exactly. | `objStmChunks_between`, `writerXrefEntries_fits`, `xrefEntries_second_between`, `writerXrefWidths_second_exact`, `WritePlan.xref_locations_exact`, `WritePlan.readback_exact`, `WritePlan.native_readback_exact` |
| Compression | Inflate inverts deflate; the block stream, token blocks, dynamic headers over code lengths that are not one length throughout, code lengths and fixed-width fields each read back what was written; `mkHuff?` builds a Huffman table exactly when zlib's inflate admits its lengths (they fill the code space, or for a payload table are one one-bit code or none), and the table then decodes every symbol it codes; package-merge's lengths over two or more live symbols fill the code space, so every table the encoder writes is one zlib admits; the reader reads a field or a code word at the bits it occupies, and a match copied as one slice is the match copied byte by byte. | `inflate_deflate_id`, `bitField_bits_exact`, `huff_decode_exact`, `TokenBlock.copy_eq_copyBytes`, `BlockStream.read_write_exact`, `TokenBlock.read_write_exact`, `DynamicHeader.read_write_exact`, `CodeLengths.read_write_exact`, `FieldStream.read_write_exact`, `mkHuff?_some_exact`, `mkHuff?_decode_exact`, `PackageMerge.lengths_mass_exact`, `packageMerge_mkHuff?_exact` |
| Images | Binary encodings round-trip; an alpha PNG's planes, cut row by row, are its samples projected by index, and each unfilters to its plane of the unfiltered image. | `decodeBin_encodeBin_id`, `projectRows_exact`, `splitPredictedAlpha_exact`; owed (U19): `orientation_cm_exact`; owed (U70): `Image.resample_id` |
| Structure | Marked-content ids partition the content and the parent tree covers them; headings are tagged. | `mcids_partition_covers`, `parentTree_covers`, `pdf_headings_covers`; owed (U46): `annots_tagged_covers`; owed (U45): `outline_headings_agree` |
| Figure resources | No resource name a page or form spells dangles, one name names one resource, and a copied page's content survives the writer's compression. | `nameOps_names_covers`, `nameOps_occ_agree`, `copiedForm_inflate_id` |
| Figure import | The importer reads back what the PDF writer paints, and a covered stream as PDF means it; the content tokenizer reads back what its writer spells; a q…Q pair restores the graphics state, a shown string says its codes' text, and a Type 3 stamp paints its procedure's ink; a figure's two faces stand in its page's box; the nesting a reading reaches is bounded; a stitched function is the line between its stops; every loss of a PDF figure is named; a PNG the engine writes reads back exactly. | `PdfGfx.readback_id`, `PdfGfx.readback_exact`, `scan_render_exact`, `gsave_restore_id`, `words_exact`, `type3_marks_exact`, `Gfx.pdfHtml_box_agree`, `PdfGfx.import_box_exact`, `forms_between`, `stitch_exact`, `pdfDiags_named`, `probe_encode_exact` |
| Text placement | Marks land on their ink; runs are placed between their bounds. | `mark_ink_exact`, `place_between` |
| Destinations | A link to an in-page fragment carries an explicit destination onto a page the writer writes, resolved from the shipped anchors, or no annotation, never an action or a name the file would have to define. That every navigation of every corpus file reaches a destination the file defines, judged from its bytes alone, and that the PDF links each in-page target as often as the HTML does, is tested. | `linkEntry_page_lt`, `linkEntry_fragment_dest`, `Layout.anchorIndex_page_lt`; tested: `pdfDestinationChecks` |
| Outline | The heading tree a PDF outline bookmarks lists its first heading at the top and each next one at most one level deeper than the one before, so every nested heading has its parent before it, and no outline object is typed as a font. That the shipped outline nests as written, closed in a flow and open in a deck, keeps only the headings that land, gives way to a declared menu, and lands every item on its heading, is tested. | `Ir.outlineHeadings_depth_step`, `outlineObjects_untyped`; tested: `pdfOutlineChecks` |
| Author strings | A byte string or text string the writer spells reads back as the one string object written, and XMP character data holds no '<' and only characters XML admits. | `PdfRead.literal_representable`, `PdfRead.textString_representable`, `PdfRead.xmpText_admitted` |

## Diagnostics, driver and landing

| Area | Guarantee | Proofs |
|---|---|---|
| Diagnostic registry | The code list is complete and duplicate-free; a code's letter is its loss's severity letter, and a diagnostic's severity its code's loss's; exactly the degraded codes owe ink, and exactly the codes that ship something are censused; site tallies sum; folding repeats keeps the sum, a line counts exactly what it stands for, and every wording stays on the log exactly once; a header's token is a written construct, kept as written; pending items are named. | `DiagCode.all_complete`, `DiagCode.all_nodup`, `DiagCode.code_letter`, `DiagCode.inks_iff_degraded`, `DiagCode.censused_iff_ships`, `Diag.tallySites_sum_exact`, `pending_named`, `Diag.foldRepeats_sum_exact`, `Diag.foldRepeats_line_exact`, `Diag.foldRepeats_shown_exact`, `Diag.foldRepeats_visible_inj`, `Diag.Spelling.ofWritten?_kept_exact`; by unfolding: `Diag.of_severity`; owed (U32): `DiagCode.name_inj`; owed (U37): `DiagCode.error_iff_fatal` |
| Flags and plans | The backend plan reads the output name and --math-boundary alone, the one remainder a named hypothesis; that no backend takes the configuration is by type, and the driver's reads are held to a list by a line scan, not a proof. A batch never holds two requests with one key. | `plan_keys_nodup`; by unfolding: `artifact_flag_free` |
| Host | A program asks the host only questions, and its result through the shipped interpreter is the replay of the trace that run recorded; two interpreters that agree on every question a program can ask run it alike, and the tool lookup asks only lookup questions, which the host answers with no process, as it answers every question but a run, so finding a TeX tree's colour profile starts none; the overwrite preflight only looks. | `Host.record_replay_exact`, `Host.recordIO_fst_exact`, `Prog.runM_only_exact`, `ToolPath.located_only`, `Host.answer_runless_exact`, `Host.answer_runless_of_ask`, `TexFontTrees.colorProfile_runless_exact`, `overwrite_only` |
| Figure routes | An exact import never reaches the converter, a lossless one never asks it, a refused converter is never run, and a drawn figure is never a placeholder; the cache answers what the import answers, and every loss an import names reaches the page's diagnostics, a PDF figure's and an SVG figure's alike; only a converter absent, or a run that did not finish, is offered an install or a repair. | `Boundary.route_exact`, `asksTool_lossless_exact`, `asksTool_declared_exact`, `route_lossy_exact`, `nativeOf_exact`, `PdfGfx.import_named`, `Svg.import_named`, `Boundary.svgRouteDiags_named`, `FigureLoss.remedy_tool_exact` |
| Caches | The record decision production calls keeps a boundary run exactly when the tool exited of itself, cleanly or failing below 126 with a log: a clean exit as its drawing, or as "no PDF was produced" when it drew none, a failing one in its log's last words, else its exit code; so a budget kill, a signal, a failed spawn or a failing exit with no log is retried. Of any attempt, a converter's included, it drops an unfinished one or an empty drawing and keeps a worded refusal; what it keeps reads back from its envelope as the fresh attempt's outcome and answer, and a decoded answer replays as itself; a tool version is reused only under the witness it was recorded with, a tool that did not exit cleanly names no version, and the words an unfinished attempt's tool printed never reach a record. | `ConvCache.record?_some_exact`, `ConvCache.envelope_replay_exact`, `ConvCache.decode_encode_record_id`, `ConvCache.replay_record_exact`, `ConvCache.replay_decode_exact`, `PicCache.versionStep_remembered_exact`, `probed_present_exact`, `probed_absent_exact`, `annotate_record_exact`; by unfolding: `ConvCache.inconclusive_retried_exact`, `ConvCache.empty_retried_exact`, `ConvCache.refusal_replays_exact` |
| Landing | Main moves only to the gated tip; every write is owned, and none is foreign, so none names a member's branch or worktree; the pin invariant holds on every trace; past the run's own rebase the gated tip is the last kept rider's commit or the run's own, so a train's landed rows end at the commit main reads and its write-ahead row names that commit; a git call the harness's guard allows writes only what its run made. An ask for the lock takes it only when every waiting waiter that arrived before the asking run is dead or asks no more, with the live waiters right behind it as a train's riders, in arrival order, up to the first under another fare and a train's worth at most; the first waiter that asks waits while the lock is held and takes it once free; a refusal behind the queue names a waiter ahead that asks and comes only past a train's worth of them; entering, leaving, boarding or alighting keeps every other waiter's place and arrival, and a run takes no place a live train holds under another fare; expiry drops only a dead place riding no live train whose last run started before the cutoff, the rest in order; and the queue's operations write only what their run owns. | `step_mutates_gated`, `step_writes_owned`, `trace_writes_owned`, `step_pinned`, `trace_pinned`, `step_topped`, `trace_topped`, `step_landedRows_exact`, `step_ridingRows_exact`, `step_unheld_exact`, `step_barred_exact`, `turn_take_exact`, `turn_first_exact`, `turn_behind_mem`, `turn_free_exact`, `enter_arrivals_exact`, `enter_kept`, `leave_arrivals_exact`, `riders_mem`, `board_arrivals_exact`, `expire_exact`; by unfolding: `init_pinned`, `init_topped`, `hcall_writes_owned`, `queueOp_writes_owned` |

## Scope

- Determinism holds by construction (pure functions, membership-only hash containers), checked by
  byte-identical golden rebuilds.
- Font guarantees are relative to the font's own tables; the parsers catch a malformed font.
- External tools and the host are premises about the evidence they return, each a premise row with
  its falsifying check or the reason none exists (`premiseChecks`), never an axiom; browser and
  viewer rendering is covered by `scripts/html-oracle.lean`, not by proofs.
- Performance is measured, never proved (`scripts/bench.lean`), but for the doccost tier's growth
  bound: it accepts every peak of linearly growing phases, capacity that doubles included, and
  decides an added quadratic term exactly (`DocBench.growthWithin_doubled_covers`,
  `DocBench.growthWithin_quadratic_exact`); the size class it holds is monotone
  (`DocBench.heldClass_monotone`).
- Fuzzers and differentials are evidence, not theorems (`scripts/kp-fuzz.lean`,
  `scripts/hyphen-diff.lean`, `scripts/compose-fuzz.lean`); a claim is open until machine-checked
  and says which it has.
- Change detectors restate a definition's own body or value, so every edit fails the build until
  restated, and state no property: `document_declares_lang`, `deck_script_constant`,
  `deck_script_gated`; owed (U72): each restated over a value domain or retired.

## Naming

A theorem's suffix names its shape; a new property instantiates one, or its review says why it is a
new shape. The conservation gate reads the first three (`conservesSuffixes`).

- `_text` (census equality, a Conserves instance), `_covers` (every member of a set is reached),
  `_id` (conditional identity).
- `_inj`, `_rectangular`, `_monotone`, `_fixed_point`, `_contract`, `_set_eq`, `_between` (a value
  inside two named bounds), `_mem` (drawn from the input set).
- `_exact`: an equation or iff that determines the value completely.
- `_accounts`: an empty result is paid for by a diagnostic or a write (`rewriteCtrl_accounts`).
- `_named`: every census element has a diagnostic whose structured subject is its key, never
  matched on message text (`pending_named`).
- `_projects`: a backend value projects one IR value (`footBand_projects`); `_agree`: two
  projections of one IR value agree (`backend_gaps_agree`).
- A backend theorem with no IR statement behind it says in its docstring which it is: a fact of the
  artifact itself (placement, escaping, xref) or a mis-layered one (review).
- `_gated`: a mutating output implies a proven state (`step_mutates_gated`); `_pinned` and
  `_topped`: the landing's run invariant and its train's hold initially and after every transition
  (`init_pinned`, `trace_pinned`, `init_topped`, `trace_topped`); `_owned`: every write an action
  declares is one its state owns (`step_writes_owned`).
- `_only`: every question a host program can ask, on every path, satisfies a predicate
  (`ToolPath.located_only`), so it holds of every interpreter (`Prog.runM_only_exact`).
- A step lemma is named by its step and the field it speaks of (`pushRun_runs`, `moveTo_plainOps`),
  a registered suffix only for that shape (`step_pinned`); the assembled statement carries the
  walk's shape (`mark_ink_exact`).
- A contract over shipped bundles quantifies over `Theme.builtin`, never one bundle at a time.

## Checks

- `lake build` checks every proof under -E hasSorry; `lake lint` audits the compiled axiom closure
  (`scripts/ProofAudit.lean`) and resolves every name here and every theorem-shaped name a docstring
  cites, one with an interior underscore, qualified or not (`scripts/cites.lean`); a name without
  one is prose no gate reads.
- Owed: a pin resolves only when its theorem's statement mentions what it pins, and a per-module
  census maps where theorems exist (owed (U71)).
