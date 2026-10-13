# Verification guarantees

An index of what Lean proves, by area; each declaration states its exact hypotheses. "By unfolding"
marks a proof that only unfolds the definition it names; "owed (Uxx)" marks a guarantee that unit
delivers. `scripts/cites.lean` holds every name here to one declaration and fails an owed name once
it resolves.

## Surfaces

| Area | Guarantee | Proofs |
|---|---|---|
| Source spans | Lexing, comments and macro marking keep the source and its paragraph breaks. | `writtenRange_source_exact`, `markMacro_source_exact`; by unfolding: `blank_line_par_agree`, `scopeEnv_source_exact` |
| Surface door and includes | One door per surface; an include is transparent; included markdown sets as it does alone. | `elabBlocks_input_exact`, `markdownInput_blocks_text`; by unfolding: `read_tex_exact` |
| Lexical forms | Owed: verbatim, URL and delimited-verbatim captures are exact. | owed (U07): `lex_verbatim_exact`; owed (U38): `lex_word_boundary_preserved` |
| Key=value and signatures | Owed: unbraced-comma splits round-trip; argument slots read a prefix and apply defaults. | owed (U20): `KeyVal.parse_unbraced_comma_exact`, `KeyVal.parse_render_roundtrip`; owed (U52): `readArgs_prefix_exact`, `readArgs_default_exact` |
| Declarations | Owed: N0100 spellings are truthful; PDF metadata projects one IR value; documents cannot spell engine names. | owed (U51): `Decl.render_parse_exact`, `pdfmeta_projects`, `toName_unforgeable` |
| Compatibility | An empty control rewrite is paid for by a diagnostic or a write. | `rewriteCtrl_accounts`; owed (U88): `rewriteCtrl_unknown_id` |
| Markdown | Desugaring stays in the declared vocabulary; a twin table row reads back as its cells; the raw-HTML scan advances, ships a break or an anchor, or names the HTML once. Owed: block accounting, laminar emphasis, twin escapes. | `Md.desugar_vocabulary_mem`, `rowLine_cells_exact`, `htmlInlineAt_accounts`, `htmlInlineAt_covers`, `htmlTagAtM_tag_exact`; owed (U44): `MdParse.blocks_accounts`, `MdParse.matchEmphasis_laminar`; owed (U49): `MarkdownDoc.escape_read_id` |
| Bibliographies | BibTeX, biber and biblatex inheritance is exact; numbered labels match the citations; cite-free content adds no citation; a field read never fails the build. | `crossref_inherit_exact`, `biberInherit_exact`, `lent_plain_exact`, `bblItems_marker_exact`, `citeFree_census`, `FieldDoor.readWith_ships_contract` |

## Elaboration

| Area | Guarantee | Proofs |
|---|---|---|
| Termination | Owed: elaboration terminates; repeat loops still compile to partial. | owed (U72): a semantic lint over reachable constants, the repeat loops rewritten |
| Macro visibility | Owed: a call resolves to the definition visible at that point. | owed (U77): `lookupUser_latest_exact` |
| Registry and input stack | Owed: one classification table; frame pushes decrease the measure; independent keys commute. | owed (U87): `Elab.classify_exact`, `Elab.push_frame_lt`, `Elab.keyed_comm` |
| Group scope | A group's end restores its start's declarations, logged global assignments replayed. | `texGroup_scope_id`, `elabBlocks_env_scope_id`, `elabBlocks_group_scope_id`; by unfolding: `texGroup_scope_exact`, `inlineGroup_scope_exact` |

## IR

| Area | Guarantee | Proofs |
|---|---|---|
| Walk census | The generic maps and the walks named conserve the text census; the fold reads a reference list's entries in order. | `Ir.mapInlines_text`, `Ir.mapBlocks_text`, `Ir.numberFloats_text`, `Ir.dimBlocks_text`, `Ir.floorMask_id`, `Ir.foldBlock_bibliography_exact`; owed (U92): the generic walk's identity, fusion and census laws |
| Numbering | A block's floats number consecutively per kind. | `numberFloatOne_exact`; owed (U11): `frameNumbers_keepFor_gapless`; owed (U54): `number_gapless_within` |
| Anchors and readiness | Owed: injective anchors, unique ids, no unresolved reference at a backend. | owed (U12): `Anchor.render_inj`, `Ir.anchors_nodup`; owed (U66): `Ir.resolve_ready` |
| Shared facts | Foot band, block gaps (by decide over the shipped table), frame title and table length agree across backends. | `Chrome.footBand_projects`, `backend_gaps_agree`; by unfolding: `frametitle_agree`, `table_length_agree`; owed (U09): `heading_family_agree`; owed (U41): `Ir.title_agree`, `Ir.lang_agree` |
| Leading | A run leads between nothing and its paragraph's leading, more for a larger run; a step's leading is within the size file's proportion. | `runLead_between`, `runLead_monotone`, `stepLead_between` |
| Pictures | Both backends paint one figure's marks; the print grid is a fixed point; the ink box covers every mark and label; repainting keeps the words. | `backend_marks_agree`, `picture_marks_agree`, `GfxPdf.marks_projects`, `GfxSvg.marks_projects`, `Figure.quantize_fixed_point`, `Figure.inkBox_covers`, `Figure.said_text` |
| Picture geometry | Cells, arrow ends, clips, scopes, colour groups, arcs, rounded corners, shading stops and label order are exact. | `Cd.cells_rectangular`, `arrow_border_exact`, `clip_covers`, `scope_compose_exact`, `colorGroup_exact`, `arc_end_exact`, `roundedCorners_between`, `shade_stops_exact`, `picture_labelOrder_agree`, `Node.recolor_geomBox_id` |
| Tables and highlights | Owed: tables are rectangular; highlighting conserves text. | owed (U53): `Table.rect`; owed (U67): `installHighlights_text` |

## Dimensions and line breaking

| Area | Guarantee | Proofs |
|---|---|---|
| Arithmetic | Points, literals and references evaluate exactly; badness is capped at 10000; lengths and ratios print digit by digit. | `toPtString_chars_exact`, `ratString_chars_exact`; by unfolding: `pt_exact`, `resolve_lit_exact`, `Affine.resolveWidth_ref_exact`, `badness_le`; owed (U42): `GlueSet.width_sum_exact`, `scaleRound_between` |
| Validity | Breaks form a valid chain; a box's width is the exact sum of its advances and kerns. | `kpScan_valid`, `kpBack_chain`, `kp_boxChars`, `kern_measure_exact` |
| Optimality | Owed: the pruned breaker equals the optimal reference. | owed (U73): `kpRef_optimal`, `kp_eq_kpRef` |
| Setting | Code wraps only between units, never inside a token, each line filled; inline code ships its source. Owed: lines within the measure, wraps conserving text. | `codeWraps_breaks_mem`, `CodeUnit.rank_mem`, `codeCut_space_mem`, `codeCut_between`, `inlineCode_source_exact`; owed (U39): `setLine_within_measure`; owed (U02): `listing_wrap_text` |
| Hyphenation | Breaks respect the language minima. | by unfolding: `hyphenate_respects_min` |

## Pages and frames

| Area | Guarantee | Proofs |
|---|---|---|
| Placement | Placement is exact; floats stay whole; a non-blank page ships at a boundary and at the end. | `place_exact`, `runFloat_whole`, `runFloat_frames`, `runFloat_reflows`, `brk_ships_exact`, `closeLast_ships_exact` |
| Frames | The overflow ladder keeps a fitting frame as declared, bounds an overhang, names each frame it moved once, and ships one IR setting. | `frameFit_id`, `frameFit_between`, `frameFit_accounts`, `runFitted_accounts`, `frameAccount_covers`, `runFitted_projects` |
| Block rules | A titled block's rule is one rule, its title part abutting its body part, centred on its lines' capitals. | `edgeLinesFrom_abuts_exact`, `edgeLinesSpan_centred_exact`, `BlockMetric.halfLeading_centred_exact` |
| Keeps and floats | Owed: float order is monotone within a kind and bounded by the next flush. | owed (U40): `float_order_monotone`, `float_page_between` |

## Fonts, shaping and math

| Area | Guarantee | Proofs |
|---|---|---|
| Face choice | Picks ignore scan order; the mono companion and typewriter defaults serve every corner they claim; lualatex's shapes are met. | `leastBy_set_eq`, `pickCompanion_set_eq`, `monoCompanion_mem`, `monoCompanion_contract`, `monoDefault_contract`, `monoFor_contract`, `servesMono_contract`, `latinModernMono_contract`; owed (U10): `resolveSized_between`; owed (U35): `slotFill_mem`, `slotFill_set_eq` |
| HTML faces | Every face the PDF keeps has an @font-face rule. Owed: the page's text is covered. | `shipFaces_covers`, `html_fonts_cover_pdf`; owed (U03): `shipFaces_nodup`; owed (U36): `html_subset_covers` |
| Font templates | A template reads back as its selections; a block title's font follows beamer's parent chain. | `FontAxes.template_exact`, `blockTitleFont_axes_exact` |
| Shaping and extraction | Owed: clusters cover the text; extraction yields the IR text. | owed (U59): `shape_clusters_covers`; owed (U21): `PdfContent.extract_text` |
| Math | MathML carries exactly a formula's glyph text (its PDF coverage tested, not proved); alphabet resolution is a fixed point; a cancel ray lies within its bounds. | `mathml_glyphs_agree`, `Ir.resolveMathAlphas_fixed_point`, `inkRayOrigin_between`; tested: `mathmlChecks`; owed (U17): `scriptShifts_between`, `Math.assemble_covers` |

## Colour and contrast

| Area | Guarantee | Proofs |
|---|---|---|
| Registry | Role resolution terminates; keys, roles and CSS names are injective; the stylesheet's table is the resolver, closed under aliases. | `Role.fallback_depth_monotone`, `Design.resolve_unfold_exact`, `Role.key_inj`, `CssName.ident_inj`, `CssName.ident_internal`, `role_css_projects`, `Design.cssDecl_chase_exact`, `cssRoles_closed` |
| Judging | Judged sites cover the registry; a passing site changes no report; shipped bundles meet their contracts in every scheme. | `Design.sites_covers`, `judged_covers`, `judgeSite_id`, `default_sites_contract`, `builtin_palettes_contract`, `builtin_palette_contract_engine`, `Theme.builtin_sites_contract`, `builtin_muted_contract` |
| Declared colours | Author colours never repaint a role and ship exactly; lineages colour as their source; seeds ship as given. | `Palette.defineColor_design_id`, `Palette.defineXcolor_design_id`, `Palette.defineXcolor_role_exact`, `Design.light_print_exact`, `moloch_lineage_exact`, `Palette.applySeedsUnder_keep_exact`, `generate_seeds_exact`, `bindings_seeds_exact` |
| Code colours | A declared code colour ships under its key; a style decides only open roles; one role paints alike; tones clear their grounds. | `resolve_declared_mem`, `resolve_derived_exact`, `derive_none_opens`, `resolve_style_exact`, `paint_role_exact`, `toneOn_contract` |
| Generated colours | Generated sites meet their targets; gamut mapping keeps lightness and hue and never adds chroma. | `generated_sites_contract`, `tint_between`, `blockPair_between`, `Okl.gamutMap_between`, `Okl.gamutMap_id`, `Okl.toGamut_between` |
| Schemes | Carried inks meet each scheme's gate, hue held; more contrast never owes less; a dropped scheme names its colours. Owed: every role-coloured run judged. | `Palette.carryOn_between`, `requiredIn_monotone`, `scheme_drop_accounts`, `sites_named`; owed (U61): `DesignRole.judged_complete` |

## HTML

| Area | Guarantee | Proofs |
|---|---|---|
| Escaping | Text and JSON hold no '<', attributes no quote, raw payloads no terminator. | `escapeText_no_lt`, `escapeAttr_no_quote`, `escapeJson_no_lt`; by unfolding: `rawPayload_no_terminator`; owed (U62): `cssString_no_lt`, `cssString_no_quote` |
| Script policy | Without scripting the deck is the pure-CSS pager and hides nothing; the math renderer ships only where declared. | `floor_covered_script_gated`, `floor_hides_nothing`, `math_boundary_contract`, `math_boundary_floor_exact` |
| Print agreement | The printed page paints roles and list markers as the PDF does. | `html_print_agree`, `marker_css_agree` |
| Picture SVG | Element ids are injective and read back; labels sit in plain SVG on the IR's baselines. | `ids_inj`, `parseId_svgId_exact`, `spell_plain_contract`, `pictureKids_unnested_contract`, `pictureLabelBaseline_projects` |
| Layout contracts | One gap owner per boundary, through overlay carriers; print lifts cover stage bounds; the deck CSS partitions by feature. | `blockGap_owner_contract`, `blockGapThrough_owner_contract`, `print_lifts_stage_bounds_covers`, `deck_css_partition` |

## PDF

| Area | Guarantee | Proofs |
|---|---|---|
| Objects and xref | Values round-trip; the object table is injective and covering; xref entries index exactly. | `parseVal_render_id`, `objTable_inj`, `objTable_covers`, `xrefEntries_index_exact` |
| Object streams and xref widths | Stream sizes and xref widths fit what the writer declares; the plan reads back exactly. | `objStmChunks_between`, `writerXrefEntries_fits`, `xrefEntries_second_between`, `writerXrefWidths_second_exact`, `WritePlan.xref_locations_exact`, `WritePlan.readback_exact`, `WritePlan.native_readback_exact` |
| Compression | Inflate inverts deflate, and each stream part reads back what was written. | `inflate_deflate_id`, `BlockStream.read_write_exact`, `TokenBlock.read_write_exact`, `DynamicHeader.read_write_exact`, `CodeLengths.read_write_exact`, `FieldStream.read_write_exact` |
| Images | Binary encodings round-trip. | `decodeBin_encodeBin_id`; owed (U19): `orientation_cm_exact`; owed (U70): `Image.resample_id` |
| Structure | Marked content partitions and the parent tree covers it; headings are tagged. | `mcids_partition_covers`, `parentTree_covers`, `pdf_headings_covers`; owed (U46): `annots_tagged_covers`; owed (U45): `outline_headings_agree` |
| Figure resources | No resource name dangles, one name names one resource, and copied content survives compression. | `nameOps_names_covers`, `nameOps_occ_agree`, `copiedForm_inflate_id` |
| Figure import | Imported marks read back as written; graphics state nests; nesting is bounded; every loss is named; a written PNG reads back. | `PdfGfx.readback_id`, `PdfGfx.readback_exact`, `scan_render_exact`, `gsave_restore_id`, `words_exact`, `type3_marks_exact`, `Gfx.pdfHtml_box_agree`, `PdfGfx.import_box_exact`, `forms_between`, `stitch_exact`, `pdfDiags_named`, `probe_encode_exact` |
| Text placement | Marks land on their ink; runs are placed between their bounds. | `mark_ink_exact`, `place_between` |

## Diagnostics, driver and landing

| Area | Guarantee | Proofs |
|---|---|---|
| Diagnostic registry | The code list is complete; severity and letter derive from the loss; folding keeps counts and each wording once; pending items are named. | `DiagCode.all_complete`, `DiagCode.all_nodup`, `DiagCode.code_letter`, `DiagCode.inks_iff_degraded`, `DiagCode.censused_iff_ships`, `Diag.tallySites_sum_exact`, `pending_named`, `Diag.foldRepeats_sum_exact`, `Diag.foldRepeats_line_exact`, `Diag.foldRepeats_shown_exact`, `Diag.foldRepeats_visible_inj`, `Diag.Spelling.ofWritten?_kept_exact`; by unfolding: `Diag.of_severity`; owed (U32): `DiagCode.name_inj`; owed (U37): `DiagCode.error_iff_fatal` |
| Flags and plans | The plan reads only the output name and --math-boundary (the driver's reads held by a line scan); batch keys are unique. | `plan_keys_nodup`; by unfolding: `artifact_flag_free` |
| Host | A program asks only questions, and its result replays its trace; agreeing interpreters run it alike; tool lookup runs no process. | `Host.record_replay_exact`, `Host.recordIO_fst_exact`, `Prog.runM_only_exact`, `ToolPath.located_only`, `Host.answer_runless_exact`, `overwrite_only` |
| Figure routes | Exact and lossless imports never ask the converter; a refused converter never runs; every import loss reaches the diagnostics. | `Boundary.route_exact`, `asksTool_lossless_exact`, `asksTool_declared_exact`, `route_lossy_exact`, `nativeOf_exact`, `PdfGfx.import_named`, `Svg.import_named`, `Boundary.svgRouteDiags_named`, `FigureLoss.remedy_tool_exact` |
| Caches | A warm slot answers as the fresh attempt; refusals replay, unfinished attempts retry. Owed: the composed policy, the envelope round trip; the PicCache lemmas hold of a model no production path calls. | `ConvCache.replay_record_exact`, `ConvCache.replay_decode_exact`, `PicCache.versionStep_remembered_exact`, `probed_present_exact`, `probed_absent_exact`, `annotate_record_exact`; by unfolding: `ConvCache.inconclusive_retried_exact`, `ConvCache.empty_retried_exact`, `ConvCache.refusal_replays_exact`; owed (U68): `record?_some_exact`, `decode_encode_record_id` |
| Landing | Main moves only to the gated tip; every write is owned; the pin invariant holds on every trace. | `step_mutates_gated`, `step_writes_owned`, `trace_writes_owned`, `step_pinned`, `trace_pinned`, `step_unheld_exact`, `step_barred_exact`; by unfolding: `init_pinned`, `hcall_writes_owned` |

## Scope

- Determinism holds by construction (pure functions, membership-only hash containers), checked by
  byte-identical golden rebuilds.
- Font guarantees are relative to the font's own tables; the parsers catch a malformed font.
- External tools and the host are premises about the evidence they return, each a premise row with
  its falsifying check or the reason none exists (`premiseChecks`), never an axiom; rendering is
  covered by `scripts/html-oracle.lean`, not by proofs.
- Performance is measured (`scripts/bench.lean`); the doccost tier's growth bound is proved
  (`DocBench.growthWithin_doubled_covers`, `DocBench.growthWithin_quadratic_exact`,
  `DocBench.heldClass_monotone`).
- Fuzzers and differentials are evidence, not theorems (`scripts/kp-fuzz.lean`,
  `scripts/hyphen-diff.lean`, `scripts/compose-fuzz.lean`).
- Change detectors restate a definition's own body or value and state no property:
  `document_declares_lang`, `deck_script_constant`, `deck_script_gated`; owed (U72): each restated
  over a value domain or retired.

## Naming

A theorem's suffix names its shape; a new property instantiates one or says why it is a new shape.
The conservation gate reads the first three (`conservesSuffixes`).

- `_text` (census equality, a Conserves instance), `_covers` (every member of a set is reached),
  `_id` (conditional identity).
- `_inj`, `_rectangular`, `_monotone`, `_fixed_point`, `_contract`, `_set_eq`, `_between` (a value
  inside two named bounds), `_mem` (drawn from the input set).
- `_exact`: an equation or iff that determines the value.
- `_accounts`: an empty result is paid for by a diagnostic or a write (`rewriteCtrl_accounts`).
- `_named`: every census element has a diagnostic whose structured subject is its key
  (`pending_named`).
- `_projects`: a backend value projects one IR value (`footBand_projects`); `_agree`: two
  projections of one IR value agree (`backend_gaps_agree`).
- A backend theorem with no IR statement says in its docstring whether it is a fact of the artifact
  (placement, escaping, xref) or mis-layered.
- `_gated`: a mutating output implies a proven state (`step_mutates_gated`); `_pinned`: the
  landing's run invariant holds initially and after every transition (`init_pinned`,
  `trace_pinned`); `_owned`: every write an action declares is one its state owns
  (`step_writes_owned`).
- `_only`: every question a host program can ask, on every path, satisfies a predicate
  (`ToolPath.located_only`), so it holds of every interpreter (`Prog.runM_only_exact`).
- A step lemma is named by its step and the field it speaks of (`pushRun_runs`, `moveTo_plainOps`),
  a registered suffix only for that shape (`step_pinned`); the assembled statement carries the
  walk's shape (`mark_ink_exact`).
- A contract over shipped bundles quantifies over `Theme.builtin`.

## Checks

- `lake build` checks every proof under -E hasSorry; `lake lint` audits the compiled axiom closure
  (`scripts/ProofAudit.lean`) and resolves every name here and every theorem-shaped name a docstring
  cites (`scripts/cites.lean`).
- Owed: a pin resolves only when its theorem's statement mentions what it pins, and a per-module
  census maps where theorems exist (owed (U71)).
