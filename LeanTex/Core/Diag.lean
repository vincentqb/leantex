module

import Std.Data.HashMap
public import LeanTex.Core.DiagWords

namespace LeanTex.Core

/-- One macro invocation in the provenance of an expanded token. -/
public structure MacroOrigin where
  id : Nat
  name : String
  deriving Repr, BEq, DecidableEq

public structure Pos where
  line : Nat := 1
  col : Nat := 1
  /-- Enclosing macro invocations, outermost first. -/
  origins : List MacroOrigin := []
  /-- The exact authored token, before normalization; `none` at a synthetic position. -/
  command : Option String := none
  /-- Whether these coordinates identify a boundary in the original source. -/
  sourceMapped : Bool := true
  /-- An opening brace whose line end the lexer leaves out, which TeX reads as a space. -/
  openEol : Bool := false
  /-- A closing brace after a line end the lexer leaves out, which TeX reads as a space unless a
  control word ends the line. -/
  closeEol : Bool := false
  deriving Repr, DecidableEq

/-- Source-location identity, ignoring expansion and token provenance. -/
public instance : BEq Pos where
  beq p q := p.line == q.line && p.col == q.col

public theorem Pos.beq_eol_exact (p q : Pos) (a b c d : Bool) :
    ({ p with openEol := a, closeEol := b } == { q with openEol := c, closeEol := d }) =
      (p == q) := rfl

public theorem Pos.beq_origins_exact (p q : Pos) (xs ys : List MacroOrigin) :
    ({ p with origins := xs } == { q with origins := ys }) = (p == q) := rfl

public theorem Pos.beq_command_exact (p q : Pos) (xs ys : Option String) :
    ({ p with command := xs } == { q with command := ys }) = (p == q) := rfl

public theorem Pos.beq_sourceMapped_exact (p q : Pos) (a b : Bool) :
    ({ p with sourceMapped := a } == { q with sourceMapped := b }) = (p == q) := rfl

public def Pos.next (p : Pos) (newline : Bool) : Pos :=
  if newline then { p with line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

public structure Span where
  file : String
  pos : Pos
  deriving Repr, BEq, DecidableEq

public inductive Severity where
  | error
  | warning
  | note
  deriving Repr, BEq

public def Severity.label : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .note => "info"

/-- The class letter a severity puts on its codes: `error` codes are `E…`,
`warning` codes `W…`, `info` codes `N…`. -/
public def Severity.letter : Severity → Char
  | .error => 'E'
  | .warning => 'W'
  | .note => 'N'

/-- Is this a warning, the severity `--werror` fails on. -/
public def Severity.isWarning : Severity → Bool
  | .warning => true
  | .error | .note => false

/-- What a reader of the shipped output loses at a diagnostic's site; severity derives from it. -/
public inductive Loss where
  /-- Declared content is absent, with nothing in its place and no plan to render it. -/
  | dropped
  /-- Declared content is absent, and the engine has a plan to render it. -/
  | pending
  /-- The content is in the output, but not as declared. -/
  | degraded
  /-- The output is as declared, but falls below a standard the engine holds documents to. -/
  | standard
  /-- A skipped construct with no content operand; the content's meaning survives. -/
  | config
  /-- Translation notes and authoring advice; the output matches the intent. -/
  | info
  deriving Repr, BEq

public def Loss.severity : Loss → Severity
  | .dropped => .error
  | .pending => .warning
  | .degraded => .warning
  | .standard => .warning
  | .config => .warning
  | .info => .note

public def Loss.letter (l : Loss) : Char := l.severity.letter

/-- The declared class as a machine reader sees it, independent of demotion. -/
public def Loss.label : Loss → String
  | .dropped => "dropped"
  | .pending => "pending"
  | .degraded => "degraded"
  | .standard => "standard"
  | .config => "config"
  | .info => "info"

public theorem Loss.label_inj (a b : Loss) (h : a.label = b.label) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- What a construct's place on the page owes a reader, declared once per loss class. -/
public inductive Floor where
  /-- No floor: the content is absent, an error the exit status reports unless accepted. -/
  | refuse
  /-- The construct's place may be empty; whatever stands there is its own content. -/
  | absent
  /-- The construct's text content stands in its place: never its markup, and never nothing
  where the construct carried content. -/
  | content
  /-- Nothing is owed and nothing appears. -/
  | inert
  deriving Repr, BEq, DecidableEq

public def Loss.floor : Loss → Floor
  | .dropped => .refuse
  | .pending => .absent
  | .degraded => .content
  | .standard => .inert
  | .config => .inert
  | .info => .inert

/-- Does anything stand in the construct's place? -/
public def Floor.ships : Floor → Bool
  | .content | .absent => true
  | .refuse | .inert => false

/-- Must the construct's place carry ink whenever the construct carried content? -/
public def Floor.inks : Floor → Bool
  | .content => true
  | .refuse | .absent | .inert => false

public theorem Floor.inks_ships (f : Floor) (h : f.inks) : f.ships := by
  cases f <;> simp_all [Floor.inks, Floor.ships]

/-- Every diagnostic code the engine can emit, one constructor per code. -/
public inductive DiagCode where
  | E0001 | W0002 | E0003 | E0004 | W0004 | E0005 | E0006
  | E0101 | E0102 | E0111 | E0112 | E0113
  | E0201 | E0202 | E0205
  | E0303 | E0304 | E0305 | E0306 | E0309 | E0310 | E0311 | E0312 | E0313
  | E0316 | E0320 | E0321 | E0322 | E0324 | E0325 | E0326
  | E0328 | E0329 | E0330 | E0331 | E0333 | E0334 | E0336 | E0340
  | E0401 | E0402 | E0404 | E0405
  | E0501 | E0502
  | N0100 | N0102 | N0103 | N0104 | N0105 | N0114 | N0200
  | W0001 | W0003 | W0005 | W0006 | W0007 | W0008 | W0009 | W0010
  | W0011 | W0012 | W0013 | W0014 | W0015 | W0016
  | N0016 | N0018 | N0017 | N0019 | N0020
  | W0101 | W0102 | W0103 | W0104 | W0105 | W0106 | W0108 | W0110 | W0111
  | W0201 | W0202
  | W0301 | W0302 | W0303 | W0304 | W0307 | W0309 | W0310 | W0311
  | W0312 | W0314 | W0315 | W0316 | W0317 | W0319
  | W0320 | W0321 | W0322 | W0323 | W0325 | W0326 | W0327 | W0328
  | W0330 | W0331 | W0332 | W0333 | W0334 | W0335 | W0336 | W0338 | W0358
  | W0340 | W0345 | W0355
  | W0349 | W0350 | W0357
  | W0351 | W0352 | W0353
  | E0347
  | W0601 | W0602
  | N0359
  | W0362
  | W0363
  | W0364
  | E0365
  | W0368
  | W0369
  | E0375
  | W0370
  | W0371
  | W0374
  | N0376
  | W0377
  | N0023
  | N0025
  | W0378
  | W0379
  | W0382
  | W0380
  | W0381
  | W0701
  | W0603
  | W0604
  | W0609
  | N0024
  | N0026
  | N0027
  | W0384
  | W0386
  | W0389
  | W0390
  | E0390
  | W0392
  | W0419
  | W0435
  | W0393
  | W0394 | E0395 | W0396
  | W0398
  | W0399
  | W0400
  | E0606
  | N0029
  | W0420
  | W0421
  | W0422
  | W0423
  | W0424
  | W0425
  | W0426
  | W0427
  | N0030
  | N0031
  | W0428
  | W0429
  | W0306
  | W0411
  | W0412
  | W0413
  | W0308
  | W0414
  | W0431
  | W0432
  | W0440
  | W0441
  | W0415
  | W0416
  | W0442
  | W0443
  | W0433
  | N0032
  | W0434
  | W0436
  | W0444
  | W0445
  | W0446
  | W0447
  | N0448
  | W0107
  | W0109
  | W0449
  | W0503
  | W0450
  | W0451
  | W0452
  | W0453
  | W0454
  | W0455
  | W0457
  | W0458
  | W0471
  | W0470
  deriving Repr, BEq, DecidableEq

/-- The registry: each code's digits, its declared `Loss`, and its one meaning. -/
private def DiagCode.spec : DiagCode → String × Loss × String
  | .E0001 => ("0001", .dropped, "cannot read an input file")
  | .W0002 => ("0002", .degraded, "bytes that are not text in the file's encoding, U+0000 among them, are replaced by U+FFFD")
  | .W0004 => ("0004", .degraded, "bytes a UTF-8 file holds that UTF-8 cannot read are read in the encoding its document declares, a guess the warning names")
  | .E0003 => ("0003", .dropped, "output formats do not have independent destinations; publication is refused")
  | .E0004 => ("0004", .dropped, "an artifact could not be written to its destination")
  | .E0005 => ("0005", .dropped, "an artifact would be written over one of the build's inputs; publication is refused")
  | .E0006 => ("0006", .dropped, "an output the engine cannot write; publication is refused")
  | .E0101 => ("0101", .dropped, "lone backslash at end of input")
  | .E0102 => ("0102", .dropped, "unclosed verbatim environment")
  | .E0111 => ("0111", .dropped, "beamer template body carrying content dropped")
  | .E0112 => ("0112", .dropped, "\\titlegraphic content dropped")
  | .E0113 => ("0113", .dropped, "unrecognised \\sectionlinesformat body dropped")
  | .E0201 => ("0201", .dropped, "unclosed group or environment at end of input")
  | .E0202 => ("0202", .dropped, "unexpected closer")
  | .E0205 => ("0205", .dropped, "malformed or mismatched environment name")
  | .E0303 => ("0303", .dropped, "malformed \\define signature")
  | .E0304 => ("0304", .dropped, "missing argument for a command")
  | .E0305 => ("0305", .dropped, "parameter expects text")
  | .E0306 => ("0306", .dropped, "unknown parameter reference in a definition body")
  | .E0309 => ("0309", .dropped, "unknown document class")
  | .E0310 => ("0310", .dropped, "content before the first \\item in a list")
  | .E0311 => ("0311", .dropped, "reserved character in text")
  | .E0312 => ("0312", .dropped, "block-level command used inline")
  | .E0313 => ("0313", .dropped, "only declarations may appear before \\begin{document}")
  | .E0316 => ("0316", .dropped, "unclosed optional argument")
  | .E0320 => ("0320", .dropped, "invalid key or missing value in a declaration block")
  | .E0321 => ("0321", .dropped, "an invalid value for a declaration key")
  | .E0322 => ("0322", .dropped, "unknown key in a declaration block")
  | .E0324 => ("0324", .dropped, "unknown page size name")
  | .E0325 => ("0325", .dropped, "unreadable \\assert expression")
  | .E0326 => ("0326", .dropped, "name not in the palette where a colour is required")
  | .E0328 => ("0328", .dropped, "not a styleable element")
  | .E0329 => ("0329", .dropped, "unknown diagnostic code in \\allow")
  | .E0330 => ("0330", .dropped, "layout assertion failed against the shipped pages")
  | .E0331 => ("0331", .dropped, "unreadable length")
  | .E0401 => ("0401", .dropped, "no usable font found on the host")
  | .E0402 => ("0402", .dropped, "LEANTEX_FONT is unusable")
  | .E0404 => ("0404", .dropped, "a font file could not be used")
  | .E0501 => ("0501", .dropped, "\\input nesting too deep")
  | .N0100 => ("0100", .info, "LaTeX idiom translated to its native declaration")
  | .W0101 => ("0101", .config, "preamble keys without a native equivalent dropped")
  | .N0102 => ("0102", .info, "option ignored: it configures machinery the engine does not model")
  | .N0103 => ("0103", .info, "\\paragraph short title unused: nothing consumes it yet")
  | .N0104 => ("0104", .info, "a frame declared for another mode ships no page in this one")
  | .N0105 => ("0105", .info, "\\allow names a retired code; its successor answers")
  | .N0114 => ("0114", .info, "a TeX conditional resolved from the document's own definitions and loads")
  | .W0111 => ("0111", .config, "a styling declaration names no styleable element; ignored")
  | .N0200 => ("0200", .info, "page set short: its skips gave their shrink")
  | .W0001 => ("0001", .config, "content after \\end{document} is ignored")
  | .W0003 => ("0003", .degraded, "no math face available; math set as plain text")
  | .E0405 => ("0405", .dropped, "font has no glyph for a character; dropped")
  | .W0005 => ("0005", .degraded, "content past its measure or page, where no re-flowed declared line accounts for it")
  | .W0006 => ("0006", .degraded, "a declared face that is not installed; the nearest installed face substitutes")
  | .W0007 => ("0007", .degraded, "paged-media furniture omitted from HTML")
  | .W0008 => ("0008", .config, "\\fonts dir is not a directory")
  | .W0009 => ("0009", .degraded, "no glyph in the declared face; set from a fallback face")
  | .W0010 => ("0010", .degraded, "lists nest four levels; deeper levels reuse the fourth marker")
  | .W0011 => ("0011", .degraded, "declared math face has no OpenType MATH table")
  | .W0012 => ("0012", .degraded, "a command the engine does not render as declared; its content stands")
  | .W0013 => ("0013", .config, "an \\allow'd code never fired")
  | .W0014 => ("0014", .degraded, "a row that disagrees with its columns; padded to the grid")
  | .W0015 => ("0015", .degraded, "equation numbers not rendered yet; rows set unnumbered")
  | .W0016 => ("0016", .degraded, "math alphabet glyph absent from the covered face; a stand-in keeps the letter")
  | .N0016 => ("0016", .info, "no math face declared; the engine picked one and says which")
  | .N0018 => ("0018", .info, "math alphabet unavailable in the selected face; source glyphs stand")
  | .N0017 => ("0017", .info, "no document class declared; the article page model is assumed")
  | .N0019 => ("0019", .info, "a backend conditional in content names a class or kernel decision made by hand")
  | .N0020 => ("0020", .info, "a local style file is read as part of the preamble")
  | .W0102 => ("0102", .degraded, "unsupported colour model")
  | .W0103 => ("0103", .config, "unsupported package skipped")
  | .W0104 => ("0104", .config, "a construct the engine reads and does not apply")
  | .W0105 => ("0105", .degraded, "overlay specification does not name a step")
  | .W0106 => ("0106", .config, "expl3 code skipped")
  | .W0107 => ("0107", .degraded, "a length value the engine cannot read; the setting is skipped and the length keeps its value")
  | .W0108 => ("0108", .degraded, "\\centering is inert inside an argument")
  | .W0109 => ("0109", .degraded, "a beamer covering set at one share: a covering graded by each step's distance at its next steps' share, a share past 99% at 99%")
  | .W0110 => ("0110", .degraded, "unsupported command option; ignored")
  | .W0201 => ("0201", .standard, "measure outside the readable band")
  | .W0202 => ("0202", .standard, "heading sets more space below than above")
  | .W0301 => ("0301", .degraded, "unknown command; {...} arguments kept as text")
  | .W0302 => ("0302", .degraded, "an environment the engine does not set; its body kept")
  | .W0303 => ("0303", .config, "a redefinition of a built-in the engine does not apply; the built-in stands")
  | .W0304 => ("0304", .degraded, "colour name not in the palette; content kept uncoloured")
  | .W0307 => ("0307", .pending, "construct not implemented yet; its content is not rendered")
  | .W0309 => ("0309", .config, "\\maketitle with nothing declared")
  | .W0310 => ("0310", .degraded, "'[' never closes; not an argument")
  | .W0311 => ("0311", .degraded, "a name given a second meaning")
  | .W0312 => ("0312", .degraded, "no {...} group after a command; skipped")
  | .E0333 => ("0333", .dropped, "picture expression unreadable or unresolvable; its shape is not drawn")
  | .E0336 => ("0336", .dropped, "{...} groups went with an unknown wrapper")
  | .E0340 => ("0340", .dropped, "unknown icon name; nothing is rendered")
  | .W0314 => ("0314", .degraded, "column width is not a fraction of the text width")
  | .W0315 => ("0315", .standard, "low-contrast colour pairing (WCAG 2.2)")
  | .W0316 => ("0316", .config, "unknown option in \\palette; block skipped")
  | .W0317 => ("0317", .config, "a card carries no running head or foot; declaration dropped")
  | .W0319 => ("0319", .degraded, "unknown theme; the document is unthemed")
  | .W0320 => ("0320", .degraded, "heading levels skip a step (HTML §4.3.11, WCAG G141)")
  | .W0321 => ("0321", .degraded, "the document title follows another heading")
  | .W0322 => ("0322", .config, "a setting or command given twice; one of them stands")
  | .W0323 => ("0323", .config, "unknown backend name in \\begin{ifbackend}; ignored")
  | .E0334 => ("0334", .dropped, "\\begin{ifbackend} content addressed to no backend")
  | .W0325 => ("0325", .degraded, "more than one <nav> landmark on one page")
  | .W0326 => ("0326", .degraded, "in-page link with no target anchor on the page")
  | .W0327 => ("0327", .degraded, "two distinct section titles fold to the same anchor")
  | .W0328 => ("0328", .degraded, "one-line content wraps; only its first line is kept")
  | .W0330 => ("0330", .degraded, "declared page with a defaulted ink is illegible (WCAG 2.2)")
  | .W0331 => ("0331", .degraded, "declared marker not expressible in this backend; default substituted")
  | .W0332 => ("0332", .degraded, "footer mixes the frame and physical page sequences undeclared")
  | .W0333 => ("0333", .degraded, "a band slot past its room")
  | .W0334 => ("0334", .pending, "picture construct outside the rendered subset; not drawn")
  | .W0335 => ("0335", .degraded, "picture larger than the text area; it may overrun the page")
  | .W0336 => ("0336", .degraded, "node labels overlap; a relative placement parts centres, not text")
  | .W0338 => ("0338", .degraded, "table is wider than the measure")
  | .W0358 => ("0358", .degraded, "a float or box taller than the text block overruns its page")
  | .W0340 => ("0340", .config, "a declaration in the document body or in inline content is ignored")
  | .W0345 => ("0345", .standard, "a themed element's resolved colour pairing is illegible (WCAG 2.2)")
  | .E0347 => ("0347", .dropped, "a running head or foot declared in the body is dropped with its content")
  | .W0355 => ("0355", .config, "a theme's slides furniture cannot draw under the class in force")
  | .W0349 => ("0349", .degraded, "reference to a key no \\label numbers; set as '??'")
  | .W0350 => ("0350", .config, "a key is \\label'ed more than once; the first wins")
  | .W0357 => ("0357", .config, "a definition is expansion-time TeX; refused by design")
  | .W0351 => ("0351", .degraded, "a citation names no bibliography entry; its mark shows as ?")
  | .W0352 => ("0352", .degraded, "a malformed .bib entry is skipped; the rest of the file is kept")
  | .W0353 => ("0353", .degraded, "an unknown bibliography style; the reference list is set as unsrtnat")
  | .E0502 => ("0502", .dropped, "\\input file not found; skipped")
  | .W0601 => ("0601", .degraded, "image unreadable or not found; placeholder box placed")
  | .W0602 => ("0602", .degraded, "an image an artifact cannot use; a placeholder box marks its place")
  | .N0359 => ("0359", .info,
    "a \\note nested inside another note's frame is dropped, as beamer drops it")
  | .W0362 => ("0362", .degraded, "picture entirely outside the rendered subset; a placeholder box marks its place")
  | .W0363 => ("0363", .degraded, "a title-page template node the engine cannot pin as written; what it sets stands at the title page's default place")
  | .W0364 => ("0364", .degraded, "an unresolved data path; nothing renders in its place")
  | .E0365 => ("0365", .dropped, "\\data file not found; its records are absent")
  | .W0368 => ("0368", .degraded, "a language the engine ships no locale for; English captions and patterns stand in")
  | .W0369 => ("0369", .degraded, "a per-language font binding; one face serves every language, so the binding is dropped")
  | .E0375 => ("0375", .dropped, "\\dimexpr division rounds to nearest, not this engine's truncation, so the statement is dropped")
  | .W0370 => ("0370", .pending, "a construct not implemented yet; kept as text")
  | .W0371 => ("0371", .degraded, "a footnote is one paragraph: a paragraph break inside \\footnote is set as a space, a list's items as lines at its margin, a heading as a bold line")
  | .W0374 => ("0374", .degraded, "a footnote on a card face is kept inline; a face has no note apparatus")
  | .N0376 => ("0376", .info, "an image ships no text alternative (WCAG 2.2)")
  | .W0377 => ("0377", .degraded, "a link carries no text to name its purpose (WCAG 2.2)")
  | .N0023 => ("0023", .info, "a picture is drawn by an external tool at the boundary; the engine measures its box, and its text is not in the document's census")
  | .N0025 => ("0025", .info, "an inputenc declaration names an encoding other than UTF-8; each file it governs is listed with how it reads")
  | .W0378 => ("0378", .degraded, "a boundary picture has no checked browser face; the web page shows the rendered subset's drawing of it, or its text alternative")
  | .W0379 => ("0379", .degraded, "no boundary tool available for a picture outside the rendered subset; a placeholder box marks the picture")
  | .W0382 => ("0382", .degraded, "the boundary tool ran and drew nothing for a picture, or did not finish it; a placeholder box marks its place")
  | .W0380 => ("0380", .degraded, "a \\cref target of unknown kind; the plain number is set")
  | .W0381 => ("0381", .degraded, "a unit outside the siunitx table; set as its ASCII spelling")
  | .W0701 => ("0701", .pending, "an output contract fact this artifact does not yet realize")
  | .W0603 => ("0603", .degraded, "an image's embedded colour profile is dropped; the page reads it as device colour")
  | .W0604 => ("0604", .degraded, "an image's orientation tag is dropped; the page shows the stored orientation")
  | .W0609 => ("0609", .degraded, "a figure is drawn by the engine without a feature it does not draw; the rest of the figure is drawn")
  | .N0024 => ("0024", .info, "a figure feature the engine does not draw; an external converter draws the figure")
  | .N0026 => ("0026", .info, "an SVG's font family is not the document's; its text is set in one of the document's own faces")
  | .N0027 => ("0027", .info, "an SVG figure holds a link, which its drawing does not carry; the figure draws the link's content")
  | .W0384 => ("0384", .degraded, "a frame taller than its page continues on the next page without a declared break")
  | .W0400 => ("0400", .degraded, "a frame a little taller than its page stands past its text area, in the gap below it")
  | .W0386 => ("0386", .degraded, "a declared line break did not hold: its line did not fit the measure and re-flowed, and any line of it still past the measure is its overrun too")
  | .W0389 => ("0389", .degraded, "a math construct whose operands the floor has ruled on; its content operand sets in its place and the formula still sets as mathematics")
  | .W0390 => ("0390", .degraded, "a font slot with no installed family; another family serves it")
  | .E0390 => ("0390", .dropped, "a markdown construct this dialect refuses by design; its content is dropped")
  | .W0392 => ("0392", .degraded, "a markdown construct sets with part of its declaration dropped; its content still sets")
  | .W0419 => ("0419", .degraded, "a picture the boundary did not draw is drawn in part by the rendered subset; what it leaves out is named in the line")
  | .W0435 => ("0435", .degraded, "a \\qedhere whose QED this engine cannot set where amsthm sets it; the QED stands on a line of its own after the display")
  | .W0393 => ("0393", .degraded, "the installed syntax highlighter cannot classify a listing; its source is set as plain text")
  | .W0394 => ("0394", .degraded, "picture label has glyphs without measured outline bounds")
  | .E0395 => ("0395", .dropped, "picture label produced no line")
  | .W0396 => ("0396", .degraded, "picture label extends beyond its reserved glyph box")
  | .W0398 => ("0398", .degraded, "booktabs loads after a face is declared; its rule paddings are measured in Latin Modern, not in that face")
  | .W0399 => ("0399", .degraded, "a fill the web slide cannot grow where it stands spaces nothing; the slide sets its frame as if it were absent")
  | .E0606 => ("0606", .dropped, "the HTML page has unresolved rendering resources; publication is refused")
  | .N0029 => ("0029", .info, "a .bib field the bibliography style prints nowhere for its entry's type; the reference list is the style's own")
  | .W0420 => ("0420", .degraded, "a .bib date or month biber does not read; it prints as written")
  | .W0421 => ("0421", .degraded, "a biblatex reference list worded in a language the engine has no bibliography strings for; English ones stand in")
  | .W0422 => ("0422", .degraded, "a biblatex @set entry; its members are listed each as an entry of its own")
  | .W0423 => ("0423", .degraded, "a biblatex entry's related entries, which its style sets after it; the engine does not set them")
  | .W0424 => ("0424", .degraded, "a .bib file among the bibliography's is not there; the list holds the other files' entries")
  | .W0425 => ("0425", .degraded, "a .bib entry's crossref or xdata reference biber does not resolve: no such entry, no @xdata entry, no such field, or a cycle; the entry is set without what it would inherit")
  | .W0426 => ("0426", .degraded, "a .bib value names an @string no file defines before it; the name prints in its place")
  | .W0427 => ("0427", .degraded, "a biblatex list sorted by a locale whose collation of its script the engine does not carry; the default collation sorts it")
  | .W0428 => ("0428", .degraded, "a biblatex \\supercite sets as \\cite, in brackets on the line; the style's superscript is not carried")
  | .W0429 => ("0429", .degraded, "a .bib field the document's elaborator refuses where an entry stands; the field sets as its text")
  | .N0030 => ("0030", .info, "a character TeX reserves, in a .bib field, set as the character it is where LaTeX reads it as markup or a comment")
  | .N0031 => ("0031", .info, "the typewriter family the engine took for an undeclared slot has no italic face; italic code sets upright in it, unslanted")
  | .W0306 => ("0306", .degraded, "a palette's seeds generate no palette — a role they derive cannot meet what its sites owe, or a seed has no sRGB tones to derive from; the seeds stand as the page's text, ground and accent")
  | .W0411 => ("0411", .standard, "a listing environment written where LaTeX cannot set it — within a line of text, in an argument, or all on one line; it is set by its evident intent")
  | .W0413 => ("0413", .degraded, "minted's one-line display command written within a line of text or an argument, where LaTeX sets a display or cannot set it, is set as inline code")
  | .W0412 => ("0412", .degraded, "a listing's language names no lexer the engine or Pygments' registry has; its code is set as plain text")
  | .W0308 => ("0308", .degraded, "a colour scheme the web page offers cannot carry a colour legibly; the page ships without that scheme")
  | .W0414 => ("0414", .degraded, "a Lean declaration's statement is not set as mathematics, Lean having given no faithful one; its code is set without it")
  | .W0431 => ("0431", .degraded, "a Lean file's links reach the commit its repository holds it at, from which the file has changed since; the links show the committed text")
  | .W0432 => ("0432", .degraded, "a Lean file's link names the file's commit or path in its repository, which the host could not give; its declarations' names are set without links")
  | .W0440 => ("0440", .degraded, "a mix of an ink with a colour other than the paper or a tint of the ink; it prints as a process colour, the ink's alternate standing in for it")
  | .W0441 => ("0441", .degraded, "an ink declared again with another alternate; a colorant names one ink, and its first alternate stands")
  | .W0415 => ("0415", .degraded, "a Lean declaration's statement the prose view cannot say in words is set as mathematics")
  | .W0416 => ("0416", .degraded, "a phrase a Lean file's directive declares is refused, or used by no sentence; the page says its statements without it")
  | .W0442 => ("0442", .degraded, "a declared page box outside the page's medium or with no area there; the PDF writes it inside the medium, or not at all")
  | .W0443 => ("0443", .degraded, "a page attribute the engine does not write: an entry other than a page box, a box that is not four numbers, or text that is not literal PDF")
  | .W0433 => ("0433", .degraded, "a Lean file's facts file no longer lines up with its source, or does not read; its page sets the file's code alone")
  | .N0032 => ("0032", .info, "a Lean file whose page asks for its facts has no facts file where its project's exporter writes one, or where the document declares it; its page sets the file's code alone")
  | .W0434 => ("0434", .degraded, "leanblueprint's dependency graph is not drawn, nor the proof buttons its showmore option asks for; the web page names beside each statement what it uses and proves")
  | .W0436 => ("0436", .degraded, "a blueprint's link template names a part a Lean name alone cannot fill; its names are set without links")
  | .W0445 => ("0445", .degraded, "the file breaks a requirement of the PDF/X standard the document declares; it is written without claiming the standard")
  | .W0446 => ("0446", .degraded, "the output intent's profile is missing or is no ICC output profile; the file carries no output intent and claims no PDF/X standard")
  | .W0447 => ("0447", .degraded, "a declaration the declared PDF/X standard does not admit; the standard's value is written in its place")
  | .W0444 => ("0444", .degraded, "links on the printed sheet, which the PDF/X standard the file claims does not admit; the PDF carries none, the web page keeps them")
  | .N0448 => ("0448", .info, "a file claiming a PDF/X standard on the checks the engine makes; a print service's preflight judges what they leave")
  | .W0449 => ("0449", .config, "a setting the document declares that nothing it sets uses; every artifact is the same without it")
  | .W0503 => ("0503", .degraded, "a bibliography file is not there or not declared; its entries are absent and what cites them is unresolved")
  | .W0450 => ("0450", .degraded, "a .bib key names a second entry setting other fields; the first entry stands")
  | .W0451 => ("0451", .degraded, "a block environment inside a line of text, a table cell or a note; its words are set in the line")
  | .W0452 => ("0452", .degraded, "a box holding a block stands on a line of its own; the text beside it is set apart from it")
  | .W0453 => ("0453", .degraded, "a documentation comment's tag, command or HTML element its dialect's reader does not read; its text, if any, sets in its place")
  | .W0454 => ("0454", .degraded, "a documentation comment's cross-reference names a program element no target on the page stands for; its text sets unlinked")
  | .W0455 => ("0455", .degraded, "a list-based environment in a box command's content, which LaTeX refuses in LR mode; the box holds it as a block")
  | .W0457 => ("0457", .degraded, "a margin note where its page sets no margin beside the text (a frame or card, a float, box, table, note or display, which LaTeX refuses outside its paragraphs); its text sets where it stands")
  | .W0458 => ("0458", .degraded, "an environment definition the engine does not apply; the environment's body kept")
  | .W0471 => ("0471", .degraded, "a picture's drawing is not in the markdown twin; its labels' words stand for it")
  | .W0470 => ("0470", .degraded, "a link whose URL runs script; every artifact sets its text unlinked")

public def DiagCode.digits (c : DiagCode) : String := c.spec.1

public def DiagCode.loss (c : DiagCode) : Loss := c.spec.2.1

public def DiagCode.meaning (c : DiagCode) : String := c.spec.2.2

/-- The word each code's messages open with, fixed per code. -/
public def DiagCode.qual : DiagCode → Diag.Qual
  | .E0306 | .E0322 | .E0324 | .E0326 | .E0328 | .E0329 | .W0111 | .W0301 | .W0304 |
    .E0340 | .W0316 | .W0319 | .W0323 | .W0349 | .W0351 | .W0353 | .W0364 | .W0381 | .W0426 |
    .W0412 | .W0454 =>
    .undefined
  | .E0006 | .E0111 | .E0112 | .E0113 | .E0309 | .W0010 | .W0011 | .W0012 | .W0015 | .W0102 |
    .W0103 | .W0106 | .W0109 | .W0302 | .W0458 | .W0307 | .W0331 | .W0334 | .W0357 | .W0602 | .W0362 |
    .W0363 | .E0375 | .W0370 | .W0371 | .W0374 | .W0380 | .W0701 |
    .W0609 | .W0389 | .E0390 | .W0419 | .W0435 | .W0422 | .W0423 | .W0427 |
    .W0428 | .W0440 | .W0415 | .W0443 | .W0434 | .W0436 | .W0453 | .W0457 | .N0024 | .W0470 =>
    .unsupported
  | .W0101 | .N0102 | .N0104 | .W0001 | .W0007 | .W0104 | .W0108 | .W0110 | .W0303 | .E0336 |
    .W0317 | .E0334 | .W0340 | .E0347 | .W0355 |
    .N0359 | .W0369 | .W0603 | .W0604 | .N0027 | .W0392 |
    .W0399 | .W0445 | .W0444 =>
    .ignored
  | .N0103 | .N0105 | .W0013 | .N0029 | .W0416 | .W0449 =>
    .unused
  | .W0002 | .E0005 | .E0205 | .E0303 | .E0305 | .E0320 | .E0321 | .E0325 |
    .E0331 | .E0501 | .W0014 | .W0105 | .W0107 | .W0202 | .E0333 | .W0314 | .W0332 |
    .W0352 | .W0420 | .W0425 | .W0429 | .W0306 | .W0431 | .W0442 | .W0433 =>
    .invalid
  | .E0001 | .E0402 | .E0404 | .W0601 | .W0446 =>
    .unreadable
  | .E0304 | .E0401 | .W0003 | .E0405 | .W0008 | .N0018 | .W0309 | .W0312 | .W0320 | .W0326 |
    .E0502 | .E0365 | .N0376 | .W0377 | .W0378 | .W0379 | .W0382 | .W0390 | .W0393 | .W0394 |
    .E0395 | .E0606 | .W0424 | .N0031 | .W0414 | .W0432 | .N0032 | .W0503 =>
    .missing
  | .E0003 | .W0311 | .W0322 | .W0325 | .W0327 | .W0350 | .W0441 | .W0450 =>
    .duplicate
  | .E0102 | .E0201 | .E0316 | .W0310 =>
    .unclosed
  | .E0101 | .E0202 | .E0310 | .E0311 | .E0312 | .E0313 | .W0321 | .W0398 | .W0411 | .W0413 |
    .W0451 | .W0452 | .W0455 =>
    .unexpected
  | .W0004 | .W0006 | .W0009 | .W0016 | .W0368 | .N0026 | .W0421 | .W0447 | .W0471 =>
    .substituted
  | .W0005 | .W0328 | .W0333 | .W0335 | .W0338 | .W0358 | .W0384 | .W0400 |
    .W0386 | .W0396 =>
    .overfull
  | .W0201 | .W0315 | .W0330 | .W0345 | .W0308 | .W0336 =>
    .illegible
  | .E0004 | .E0330 =>
    .failed
  | .N0200 =>
    .tight
  | .N0100 | .N0020 | .N0023 | .N0030 =>
    .translated
  | .N0114 | .N0019 | .N0025 | .N0448 =>
    .resolved
  | .N0016 | .N0017 =>
    .default

/-- A message in the one form, opening with its code's word. -/
public def Diag.say (c : DiagCode) (noun : Diag.Noun) (name : Option Diag.Name := none)
    (obj : Option (Option Diag.Noun × Diag.Name) := none) : String :=
  { qual := c.qual, noun, name, obj : Diag.Words }.render

/-- One of TeX's or LaTeX's own texts for a cause lualatex also reports: `#1`, `#2` its name
slots, `source` the line or engine raising it. -/
public structure TexText where
  key : String
  code : DiagCode
  text : String
  source : String
  deriving Repr

/-- A TeX text with its slots filled in one pass, `#k` standing for the k-th name. -/
public def TexText.fill (t : TexText) (names : List String) : String :=
  let rec go : List Char → String → String
    | '#' :: d :: rest, acc =>
      if d.isDigit then go rest (acc ++ (names[d.toNat - '1'.toNat]?).getD "")
      else go (d :: rest) (acc.push '#')
    | c :: rest, acc => go rest (acc.push c)
    | [], acc => acc
  go t.text.toList ""

/-- The name inside a construct's last `{...}` group, when it ends with one. -/
private def Diag.groupName? (what : String) : Option String :=
  if what.endsWith "}" then
    match (what.dropEnd 1).toString.splitOn "{" with
    | [] | [_] => none
    | parts => parts.getLast?
  else none

/-- N0100's words for a written construct: a package, a class or an environment by its name, a
key by its spelling, anything else as written. -/
public def Diag.translated (what : String) : String :=
  let named (noun : Diag.Noun) : String :=
    Diag.say .N0100 noun (Diag.Name.of ((Diag.groupName? what).getD what))
  if what.startsWith "\\usepackage" || what.startsWith "\\RequirePackage" then named .package
  else if what.startsWith "\\documentclass" then named .class
  else if what.startsWith "\\begin{" then named .environment
  else if !what.startsWith "\\" && (what.splitOn "=").length > 1 then
    Diag.say .N0100 .key (Diag.Name.of what)
  else Diag.say .N0100 .command (Diag.Name.of what)

public def DiagCode.floor (c : DiagCode) : Floor := c.loss.floor

public theorem DiagCode.inks_iff_degraded (c : DiagCode) :
    c.floor.inks = (c.loss == .degraded) := by
  cases h : c.loss <;> simp only [DiagCode.floor, h, Loss.floor, Floor.inks] <;> decide


/-- A code's printed name: its declared loss's class letter, then the registry's digits. -/
public def DiagCode.code (c : DiagCode) : String :=
  String.singleton c.loss.letter ++ c.digits

public theorem DiagCode.code_letter (c : DiagCode) :
    c.code.front = c.loss.severity.letter := by
  cases c <;> rfl

/-- A number at or past the last constructor's index, where `ofNat` saturates. -/
private def DiagCode.ctorCeiling : Nat := 65536

/-- How many codes the registry holds, read off the type. -/
public def DiagCode.count : Nat := (DiagCode.ofNat DiagCode.ctorCeiling).ctorIdx + 1

/-- Every code, in declaration order, derived from the type. -/
public def DiagCode.all : List DiagCode :=
  (List.range DiagCode.count).map DiagCode.ofNat

public theorem DiagCode.all_complete (c : DiagCode) : DiagCode.all.contains c := by
  have hc : c.ctorIdx < DiagCode.count := by cases c <;> decide
  have hb : (c == c) = true := by cases c <;> rfl
  rw [List.contains_eq_any_beq, List.any_eq_true]
  exact ⟨c, List.mem_map.2 ⟨c.ctorIdx, List.mem_range.2 hc, DiagCode.ofNat_ctorIdx c⟩, hb⟩

public theorem DiagCode.all_nodup : DiagCode.all.Nodup := by decide +kernel

/-- The code a string names, for validating a document's `\allow` list. -/
public def DiagCode.ofString? (s : String) : Option DiagCode :=
  DiagCode.all.find? (·.code == s)

/-- Retired codes a document may still name, each with the code naming its loss now, or `none`
when the loss cannot occur; `\allow` of a retired code accepts nothing. -/
public def DiagCode.retired : List (String × Option String) :=
  [("W0341", some "W0301"),
   ("W0344", none),
   ("W0376", some "N0376"),
   ("N0419", some "W0419"),
   ("W0397", none),
   ("W0356", some "W0104"),
   ("N0021", none)]

/-- Codes renumbered for their class or merged into the code saying their loss in the same words;
`\allow` of the old spelling accepts the successor. -/
public def DiagCode.renumbered : List (String × String) :=
  [("E0382", "W0382"),
   ("E0002", "W0002"),
   ("E0503", "W0503"),
   ("E0403", "W0390"),
   ("E0359", "N0359"),
   ("E0327", "E0322"),
   ("E0323", "E0321"),
   ("E0332", "E0321"),
   ("E0607", "E0006"),
   ("W0366", "W0006"),
   ("W0346", "W0340"),
   ("W0318", "W0104"),
   ("W0329", "W0104"),
   ("W0348", "W0104"),
   ("W0354", "W0104"),
   ("W0367", "W0104"),
   ("W0387", "W0104"),
   ("W0391", "W0104"),
   ("W0343", "W0322"),
   ("W0342", "W0311"),
   ("W0337", "W0014"),
   ("W0403", "W0390"),
   ("W0372", "W0005"),
   ("W0388", "W0333"),
   ("W0373", "W0012"),
   ("W0385", "W0012"),
   ("W0605", "W0602"),
   ("W0383", "W0370"),
   ("W0361", "W0303")]

/-- An artifact whose diagnostics apply only when that output is requested. -/
public inductive Diag.Output where
  | pdf
  | html
  | md
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq, Hashable

public def Diag.Output.label : Diag.Output → String
  | .pdf => "pdf"
  | .html => "html"
  | .md => "md"

/-- What the engine did after a loss; a proposed action belongs in `Diag.help`. -/
public inductive Diag.Recovery where
  | ignored
  | skipped
  | replacedBy (replacement : String)
  deriving Repr, BEq, DecidableEq, Hashable

/-- Is `s` one written construct token: a control word or symbol, a math shift, or a TeX
special character? -/
@[expose] public def Diag.constructSpelling (s : String) : Bool :=
  match s.toList with
  | ['$'] | ['$', '$'] | ['&'] | ['#'] | ['^'] | ['_'] | ['~'] => true
  | ['\\', _] | ['\\', '\r', '\n'] => true
  | '\\' :: rest => !rest.isEmpty && rest.all fun x => x.isAlpha || x == '@'
  | _ => false

/-- The one written construct a diagnostic's header names after its location. -/
public structure Diag.Spelling where
  private mk ::
  text : String
  construct : Diag.constructSpelling text = true
  deriving Repr, DecidableEq

/-- The one door a spelling is made through: a construct token, or nothing. -/
public def Diag.Spelling.ofWritten? (s : String) : Option Diag.Spelling :=
  if h : Diag.constructSpelling s = true then some ⟨s, h⟩ else none

public theorem Diag.Spelling.ofWritten?_kept_exact (s : String) (t : Diag.Spelling)
    (h : Diag.Spelling.ofWritten? s = some t) : t.text = s := by
  unfold Diag.Spelling.ofWritten? at h
  split at h
  · cases h; rfl
  · cases h

public theorem Diag.Spelling.ofWritten?_exact (s : String) :
    ((Diag.Spelling.ofWritten? s).map (·.text) = some s) = (Diag.constructSpelling s = true) := by
  unfold Diag.Spelling.ofWritten?
  split <;> simp_all

/-- A diagnostic as delivered: severity and code string project from `kind`, `demoted` is its
one policy bit, `subject` its census key and `sites` its loss's site count. -/
public structure Diag where
  kind : DiagCode
  message : String
  span : Option Span := none
  help : Option String := none
  demoted : Bool := false
  subject : Option String := none
  /-- The name this diagnostic refuses, when refusing a name is what it does. -/
  refused : Option String := none
  sites : Nat := 1
  /-- The written construct the diagnostic is about, as the author spelled it. -/
  trigger : Option Diag.Spelling := none
  /-- Actual handling of this loss, distinct from a suggested action in `help`. -/
  recovery : Option Diag.Recovery := none
  /-- `none` applies to every output; a scoped loss applies only to that artifact. -/
  output : Option Diag.Output := none
  /-- Every byte offset in its span's file the diagnostic names, beyond what its message lists. -/
  offsets : Array Nat := #[]
  /-- What this site alone adds to the words; not part of the wording (`sameWords`). -/
  detail : Option String := none
  /-- Other codes' losses this record accounts for; accepting the carrier accepts them. -/
  carries : List DiagCode := []
  deriving Repr, BEq

/-- Is this loss part of the site census? -/
public def Loss.censused : Loss → Bool
  | .degraded | .pending => true
  | .dropped | .standard | .config | .info => false

public def DiagCode.censused (c : DiagCode) : Bool := c.loss.censused

public theorem DiagCode.censused_iff_ships (c : DiagCode) :
    c.censused = c.floor.ships := by
  cases h : c.loss <;>
    simp only [DiagCode.censused, DiagCode.floor, h, Loss.censused, Loss.floor, Floor.ships]

/-- Whether a code's cause stops the writer: unreadable input, a missing or too deep `\input`, no
usable font, an unwritable output, a failed `\assert`, an output name or a PDF the engine cannot
write, or a refused publication. -/
public def DiagCode.stopsWriter : DiagCode → Bool
  | .E0001 | .E0501 | .E0502 | .E0401 | .E0402 | .E0004 | .E0330 => true
  | .E0003 | .E0005 | .E0006 | .E0606 => true
  | _ => false

/-- Every cause that stops the writer is an error, so a run that writes nothing never exits 0. -/
public theorem DiagCode.stopsWriter_error (c : DiagCode) (h : c.stopsWriter = true) :
    c.loss.severity = .error := by
  unfold DiagCode.stopsWriter at h
  split at h <;> first | rfl | contradiction

/-- Is this a loss about a place, whose header names no written token? -/
public def DiagCode.namesPlace : DiagCode → Bool
  | .W0005 | .W0386 | .W0338 | .N0200 => true
  | _ => false

public def Diag.code (d : Diag) : String := d.kind.code

/-- The declared loss's severity, or a note when demoted. -/
public def Diag.severity (d : Diag) : Severity :=
  match d.demoted with
  | true => .note
  | false => d.kind.loss.severity

/-- The one door a diagnostic is made through; a trigger is kept only when it spells a construct
and the loss is not about a place. -/
public def Diag.of (c : DiagCode) (message : String) (span : Option Span := none)
    (help : Option String := none) (subject : Option String := none)
    (refused : Option String := none) (trigger : Option String := none)
    (recovery : Option Diag.Recovery := none) (output : Option Diag.Output := none)
    (detail : Option String := none) (carries : List DiagCode := []) : Diag :=
  { kind := c
    message := message
    span := span
    help := help
    subject := subject
    refused := refused
    trigger := if c.namesPlace then none else trigger.bind Diag.Spelling.ofWritten?
    recovery := recovery
    output := output
    detail := detail
    carries := carries }

public def Diag.triggerText (d : Diag) : Option String := d.trigger.map (·.text)

/-- The wording of a declared setting the engine skips, whatever surface declares it. -/
public def Diag.notHonoured (noun : Diag.Noun) (name : Diag.Name)
    (obj : Option (Option Diag.Noun × Diag.Name) := none) : String :=
  Diag.say .W0104 noun name obj

/-- Names joined for prose, the last after `word`: `a, b or c`. -/
public def Diag.prose (word : String) (names : List String) : String :=
  match names.reverse with
  | [] => ""
  | [one] => one
  | last :: rest => ", ".intercalate rest.reverse ++ s!" {word} {last}"

/-- The one wording of a declaration the document body ignores. -/
public def Diag.bodyDeclaration (name : String) : String :=
  Diag.say .W0340 .declaration (Diag.Name.of ("\\" ++ name))

/-- The help of a declaration standing where it is not read. -/
public def Diag.declareInPreamble : String := "declare it before \\begin{document}"

public theorem Diag.of_record_exact (c : DiagCode) (message : String)
    (span : Option Span) (help subject refused trigger : Option String)
    (recovery : Option Diag.Recovery) (output : Option Diag.Output) (detail : Option String)
    (carries : List DiagCode) :
    Diag.of c message span help subject refused trigger recovery output detail carries =
      { kind := c, message := message, span := span, help := help,
        subject := subject, refused := refused,
        trigger := if c.namesPlace then none else trigger.bind Diag.Spelling.ofWritten?,
        recovery := recovery, output := output, detail := detail, carries := carries } := by
  rfl

public theorem Diag.of_subject (c : DiagCode) (message : String) (span : Option Span)
    (help subject : Option String) (refused : Option String := none)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (Diag.of c message span help subject refused trigger recovery output detail).subject =
      subject := by
  rfl

public theorem Diag.of_severity (c : DiagCode) (message : String) (span : Option Span)
    (help : Option String) (subject : Option String) :
    (Diag.of c message span help subject).severity = c.loss.severity := by rfl

public theorem Diag.of_severity_full (c : DiagCode) (message : String) (span : Option Span)
    (help subject refused trigger : Option String) (recovery : Option Diag.Recovery)
    (output : Option Diag.Output) :
    (Diag.of c message span help subject refused trigger recovery output).severity =
      c.loss.severity := by rfl

public theorem DiagCode.fieldReading_ships :
    (DiagCode.W0429.loss.severity == .error) = false ∧
      (DiagCode.W0012.loss.severity == .error) = false ∧
      (DiagCode.N0030.loss.severity == .error) = false := ⟨rfl, rfl, rfl⟩

/-- An unscoped diagnostic always applies; a scoped one only when its artifact is built. -/
public def Diag.appliesTo (outputs : Array Diag.Output) (d : Diag) : Bool :=
  match d.output with
  | none => true
  | some output => outputs.contains output

/-- The diagnostics that apply to the built outputs, before acceptance. -/
-- premise: Diag.forOutputs_mem — only disabled artifacts' diagnostics are removed
public def Diag.forOutputs (outputs : Array Diag.Output) (ds : Array Diag) : Array Diag :=
  ds.filter (Diag.appliesTo outputs)

public theorem Diag.forOutputs_mem (outputs : Array Diag.Output) (ds : Array Diag) (d : Diag) :
    d ∈ Diag.forOutputs outputs ds ↔
      d ∈ ds ∧ (∀ output, d.output = some output → output ∈ outputs) := by
  simp only [Diag.forOutputs, Array.mem_filter]
  cases h : d.output <;> simp [Diag.appliesTo, h]

public theorem Diag.forOutputs_id (outputs : Array Diag.Output) (ds : Array Diag) :
    Diag.forOutputs outputs (Diag.forOutputs outputs ds) = Diag.forOutputs outputs ds := by
  simp [Diag.forOutputs, Array.filter_filter]

/-- Resolve `\allow` acceptance, delivering an accepted diagnostic as a note; returns it and
whether it was accepted. -/
public def Diag.accept (allowed : Array String) (allowAll : Bool) (d : Diag) : Diag × Bool :=
  if d.kind.loss.severity != .note && (allowAll || allowed.contains d.code) then
    ({ d with demoted := true }, true)
  else (d, false)

public theorem Diag.accept_record_exact (allowed : Array String) (allowAll : Bool) (d : Diag) :
    { (Diag.accept allowed allowAll d).1 with demoted := d.demoted } = d := by
  unfold Diag.accept
  split <;> rfl

/-- Deliver a diagnostic as a note, keeping its code and message. -/
public def Diag.demote (d : Diag) : Diag := { d with demoted := true }

public theorem Diag.demote_record_exact (d : Diag) :
    { Diag.demote d with demoted := d.demoted } = d := by rfl

/-- Two diagnostics are sites of the same loss: same code, subject and output scope. -/
public def Diag.sameLoss (a b : Diag) : Bool :=
  (decide (a.kind = b.kind) && decide (a.output = b.output)) &&
    decide (a.subject = b.subject) && a.subject.isSome

public theorem Diag.sameLoss_iff (a b : Diag) :
    Diag.sameLoss a b = true ↔
      (a.kind = b.kind ∧ a.output = b.output) ∧
        a.subject = b.subject ∧ a.subject.isSome = true := by
  simp [Diag.sameLoss, and_assoc]

private theorem Diag.sameLoss_symm {a b : Diag} (h : Diag.sameLoss a b = true) :
    Diag.sameLoss b a = true := by
  obtain ⟨hk, hs, hi⟩ := (Diag.sameLoss_iff a b).mp h
  exact (Diag.sameLoss_iff b a).mpr ⟨⟨hk.1.symm, hk.2.symm⟩, hs.symm, hs ▸ hi⟩

private theorem Diag.sameLoss_trans {a b c : Diag} (h₁ : Diag.sameLoss a b = true)
    (h₂ : Diag.sameLoss b c = true) : Diag.sameLoss a c = true := by
  obtain ⟨hk, hs, hi⟩ := (Diag.sameLoss_iff a b).mp h₁
  obtain ⟨hk', hs', _⟩ := (Diag.sameLoss_iff b c).mp h₂
  exact (Diag.sameLoss_iff a c).mpr
    ⟨⟨hk.1.trans hk'.1, hk.2.trans hk'.2⟩, hs.trans hs', hi⟩

public theorem Diag.sameLoss_output_exact (a b : Diag) (h : Diag.sameLoss a b = true) :
    a.output = b.output := ((Diag.sameLoss_iff a b).mp h).1.2

/-- The index whose line carries a diagnostic's count: the first diagnostic
of its loss, or its own index when it names no subject. -/
private def Diag.carrier (ds : List Diag) (i : Nat) (d : Diag) : Nat :=
  if d.subject.isSome then ds.findIdx (Diag.sameLoss d) else i

/-- One pass of counts: the entry at `i` is how many of `cs` are `i`. -/
private def Diag.countsOf (n : Nat) (cs : List Nat) : Array Nat :=
  cs.foldl (fun acc c => acc.modify c (· + 1)) (Array.replicate n 0)

private theorem Diag.countsOf_foldl (cs : List Nat) (acc : Array Nat) (i : Nat)
    (h : i < acc.size) :
    (cs.foldl (fun acc c => acc.modify c (· + 1)) acc)[i]?.getD 0 =
      acc[i]?.getD 0 + cs.count i := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih (acc.modify c (· + 1)) (by simpa using h), List.count_cons,
      Array.getElem?_modify]
    by_cases hc : c = i
    · subst hc
      simp [Array.getElem?_eq_getElem h]
      omega
    · have : (c == i) = false := by simpa using hc
      simp [hc, this]

private theorem Diag.countsOf_count (n : Nat) (cs : List Nat) (i : Nat) (h : i < n) :
    (Diag.countsOf n cs)[i]?.getD 0 = cs.count i := by
  unfold Diag.countsOf
  rw [Diag.countsOf_foldl cs _ i (by simpa using h)]
  simp [h]

/-- Count each loss's sites onto its first diagnostic; later sites carry 0, a subjectless one 1. -/
public def Diag.tallySites (ds : Array Diag) : Array Diag :=
  let counts := Diag.countsOf ds.size (ds.toList.mapIdx (Diag.carrier ds.toList))
  ds.mapIdx fun i d => { d with sites := counts[i]?.getD 0 }

private theorem Diag.findIdx_le_of_true {p : α → Bool} {xs : List α} {i : Nat}
    (h : i < xs.length) (hp : p xs[i] = true) : xs.findIdx p ≤ i :=
  Nat.le_of_not_lt fun hlt => by simp [List.not_of_lt_findIdx hlt] at hp

private theorem Diag.carrier_lt (ds : List Diag) (i : Nat) (h : i < ds.length) :
    Diag.carrier ds i ds[i] < ds.length := by
  unfold Diag.carrier
  split
  · rename_i hs
    have := Diag.findIdx_le_of_true h ((Diag.sameLoss_iff _ _).mpr ⟨⟨rfl, rfl⟩, rfl, hs⟩)
    omega
  · exact h

private theorem Diag.sum_count_range (os : List Nat) (n : Nat) :
    ((List.range n).map (os.count ·)).sum = (os.filter (· < n)).length := by
  induction n with
  | zero => rw [List.filter_eq_nil_iff.mpr (by simp)]; simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append_nat, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    clear ih
    induction os with
    | nil => simp
    | cons o os ih =>
      simp only [List.filter_cons, List.count_cons]
      by_cases h1 : o < n
      · have h2 : o < n + 1 := by omega
        have h3 : (o == n) = false := by simp; omega
        simp [h1, h2, h3]; omega
      · by_cases h4 : o = n
        · subst h4; simp; omega
        · have h2 : ¬ o < n + 1 := by omega
          have h3 : (o == n) = false := by simp; omega
          simp [h1, h2, h3]; omega

private theorem Diag.count_mapIdx_eq_countP {l : List α} (f : Nat → α → Nat) (p : α → Bool)
    (v : Nat) (h : ∀ j (hj : j < l.length), f j l[j] = v ↔ p l[j] = true) :
    (l.mapIdx f).count v = l.countP p := by
  induction l generalizing f with
  | nil => simp
  | cons a l ih =>
    rw [List.mapIdx_cons, List.count_cons, List.countP_cons]
    have h0 : f 0 a = v ↔ p a = true := by
      have := h 0 (by simp); rwa [List.getElem_cons_zero] at this
    rw [ih (fun i => f (i + 1)) fun j hj => by
      have := h (j + 1) (by simp; omega); rwa [List.getElem_cons_succ] at this]
    by_cases hp : p a
    · simp [hp, h0.mpr hp]
    · have : f 0 a ≠ v := fun e => hp (h0.mp e)
      simp [hp, this]

private theorem Diag.count_mapIdx_eq_one {l : List α} (f : Nat → α → Nat) (v i : Nat)
    (hi : i < l.length) (h : ∀ j (hj : j < l.length), f j l[j] = v ↔ j = i) :
    (l.mapIdx f).count v = 1 := by
  induction l generalizing f i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.mapIdx_cons, List.count_cons]
    cases i with
    | zero =>
      have h0 : f 0 a = v := by
        have := (h 0 (by simp)).mpr rfl; rwa [List.getElem_cons_zero] at this
      have hz : (l.mapIdx fun i => f (i + 1)).count v = 0 := by
        have := Diag.count_mapIdx_eq_countP (l := l) (fun i => f (i + 1)) (fun _ => false) v
          fun j hj => by
            have := h (j + 1) (by simp; omega); rw [List.getElem_cons_succ] at this
            simpa using this
        simpa using this
      simp [h0, hz]
    | succ k =>
      have h0 : f 0 a ≠ v := fun e => by
        have := h 0 (by simp); rw [List.getElem_cons_zero] at this; simpa using this.mp e
      rw [ih (fun i => f (i + 1)) k (by simpa using hi)
        fun j hj => by
          have := h (j + 1) (by simp; omega); rw [List.getElem_cons_succ] at this
          simpa using this]
      simp [h0]

private theorem Diag.carrier_eq_iff_head (l : List Diag) (i j : Nat) (hi : i < l.length)
    (hj : j < l.length) (hs : l[i].subject.isSome = true)
    (hfirst : ∀ k (hk : k < i), Diag.sameLoss l[i] l[k] = false) :
    Diag.carrier l j l[j] = i ↔ Diag.sameLoss l[i] l[j] = true := by
  unfold Diag.carrier
  constructor
  · intro h
    split at h
    · exact Diag.sameLoss_symm ((List.findIdx_eq hi).mp h).1
    · rename_i hsj
      subst h
      exact absurd hs hsj
  · intro h
    have hsj : l[j].subject.isSome = true := by
      obtain ⟨_, hsub, hsome⟩ := (Diag.sameLoss_iff _ _).mp h
      rw [← hsub]; exact hsome
    simp only [hsj, ite_true]
    rw [List.findIdx_eq hi]
    refine ⟨Diag.sameLoss_symm h, fun k hk => ?_⟩
    cases hc : Diag.sameLoss l[j] l[k]
    · rfl
    · have := Diag.sameLoss_trans h hc
      rw [hfirst k hk] at this
      exact absurd this (by simp)

private theorem Diag.carrier_ne_later (l : List Diag) (i k j : Nat) (hi : i < l.length)
    (hki : k < i) (hj : j < l.length) (hsame : Diag.sameLoss l[i] l[k] = true) :
    Diag.carrier l j l[j] ≠ i := by
  unfold Diag.carrier
  intro h
  split at h
  · have hx := (List.findIdx_eq hi).mp h
    have hjk := Diag.sameLoss_trans hx.1 hsame
    rw [hx.2 k hki] at hjk
    exact absurd hjk (by simp)
  · rename_i hsj
    subst h
    exact hsj ((Diag.sameLoss_iff _ _).mp hsame).2.2

private theorem Diag.carrier_eq_iff_self (l : List Diag) (i j : Nat) (hi : i < l.length)
    (hj : j < l.length) (hn : l[i].subject.isSome = false) :
    Diag.carrier l j l[j] = i ↔ j = i := by
  unfold Diag.carrier
  constructor
  · intro h
    split at h
    · have hx := ((List.findIdx_eq hi).mp h).1
      have := ((Diag.sameLoss_iff _ _).mp hx).2
      rw [← this.1] at hn
      simp [this.2] at hn
    · exact h
  · intro h
    subst h
    simp [hn]

private theorem Diag.tallySites_getElem? (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    (Diag.tallySites ds)[i]? =
      some { ds[i] with sites := (ds.toList.mapIdx (Diag.carrier ds.toList)).count i } := by
  simp only [Diag.tallySites, Array.getElem?_mapIdx, Array.getElem?_eq_getElem h,
    Option.map_some]
  rw [Diag.countsOf_count ds.size _ i h]

public theorem Diag.tallySites_length (ds : Array Diag) :
    (Diag.tallySites ds).size = ds.size := Array.size_mapIdx

public theorem Diag.tallySites_id (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    ∃ d, (Diag.tallySites ds)[i]? = some d ∧ d.kind = (ds[i]).kind ∧
      d.message = (ds[i]).message ∧ d.span = (ds[i]).span ∧
      d.help = (ds[i]).help ∧ d.demoted = (ds[i]).demoted ∧
      d.subject = (ds[i]).subject :=
  ⟨_, Diag.tallySites_getElem? ds i h, rfl, rfl, rfl, rfl, rfl, rfl⟩

public theorem Diag.tallySites_record_exact (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    ((Diag.tallySites ds)[i]?).map (fun d => { d with sites := ds[i].sites }) = some ds[i] := by
  rw [Diag.tallySites_getElem? ds i h]
  rfl

public theorem Diag.tallySites_sum_exact (ds : Array Diag) :
    ((Diag.tallySites ds).toList.map (·.sites)).sum = ds.size := by
  have hmap : (Diag.tallySites ds).toList.map (·.sites) =
      (List.range ds.size).map ((ds.toList.mapIdx (Diag.carrier ds.toList)).count ·) := by
    apply List.ext_getElem
    · simp [Diag.tallySites]
    · intro n hn _
      have hn' : n < ds.size := by simpa [Diag.tallySites] using hn
      have hget := Diag.tallySites_getElem? ds n hn'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [Array.getElem?_eq_getElem (by rw [Diag.tallySites_length]; exact hn')] at hget
      rw [Option.some.inj hget]
  rw [hmap, Diag.sum_count_range]
  have hall : ∀ o ∈ ds.toList.mapIdx (Diag.carrier ds.toList), o < ds.size := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp ho
    have := Diag.carrier_lt ds.toList j hj
    rwa [Array.length_toList] at this
  rw [List.filter_eq_self.mpr (by simpa using hall)]
  simp

public theorem Diag.tallySites_exact (ds : Array Diag) (i : Nat) (h : i < ds.size)
    (hs : (ds[i]).subject.isSome)
    (hfirst : ∀ k (hk : k < i), Diag.sameLoss ds[i] ds[k] = false) :
    ((Diag.tallySites ds)[i]?).map (·.sites) =
      some (ds.filter (Diag.sameLoss ds[i] ·)).size := by
  rw [Diag.tallySites_getElem? ds i h]
  simp only [Option.map_some, Option.some.injEq]
  have hl : i < ds.toList.length := by simpa using h
  rw [Diag.count_mapIdx_eq_countP (Diag.carrier ds.toList) (Diag.sameLoss ds[i]) i
    fun j hj => by
      have := Diag.carrier_eq_iff_head ds.toList i j hl hj (by simpa using hs)
        fun k hk => by simpa using hfirst k hk
      simpa using this]
  rw [List.countP_eq_length_filter, ← Array.length_toList, Array.toList_filter]

public theorem Diag.tallySites_later_exact (ds : Array Diag) (i k : Nat) (h : i < ds.size)
    (hk : k < i) (hsame : Diag.sameLoss ds[i] ds[k] = true) :
    ((Diag.tallySites ds)[i]?).map (·.sites) = some 0 := by
  rw [Diag.tallySites_getElem? ds i h]
  simp only [Option.map_some, Option.some.injEq]
  have hl : i < ds.toList.length := by simpa using h
  rw [Diag.count_mapIdx_eq_countP (Diag.carrier ds.toList) (fun _ => false) i
    fun j hj => by
      have := Diag.carrier_ne_later ds.toList i k j hl hk hj (by simpa using hsame)
      simpa using this]
  simp

public theorem Diag.tallySites_subjectless_id (ds : Array Diag) (i : Nat) (h : i < ds.size)
    (hn : (ds[i]).subject.isNone) :
    (Diag.tallySites ds)[i]? = some { ds[i] with sites := 1 } := by
  rw [Diag.tallySites_getElem? ds i h]
  have hl : i < ds.toList.length := by simpa using h
  rw [Diag.count_mapIdx_eq_one (Diag.carrier ds.toList) i i hl
    fun j hj => Diag.carrier_eq_iff_self ds.toList i j hl hj (by simpa using hn)]

/-- What a record says, apart from where it stands: its words, its advice,
what was done in its place, and the name it refuses. -/
public def Diag.sameWords (a b : Diag) : Bool :=
  (decide (a.message = b.message) && decide (a.help = b.help)) &&
    decide (a.recovery = b.recovery) && decide (a.refused = b.refused)

public theorem Diag.sameWords_iff (a b : Diag) :
    Diag.sameWords a b = true ↔
      (a.message = b.message ∧ a.help = b.help) ∧ a.recovery = b.recovery ∧
        a.refused = b.refused := by
  simp [Diag.sameWords, and_assoc]

private theorem Diag.sameWords_refl (a : Diag) : Diag.sameWords a a = true :=
  (Diag.sameWords_iff a a).mpr ⟨⟨rfl, rfl⟩, rfl, rfl⟩

private theorem Diag.sameWords_symm {a b : Diag} (h : Diag.sameWords a b = true) :
    Diag.sameWords b a = true := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (Diag.sameWords_iff a b).mp h
  exact (Diag.sameWords_iff b a).mpr ⟨⟨h1.symm, h2.symm⟩, h3.symm, h4.symm⟩

private theorem Diag.sameWords_trans {a b c : Diag} (h₁ : Diag.sameWords a b = true)
    (h₂ : Diag.sameWords b c = true) : Diag.sameWords a c = true := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (Diag.sameWords_iff a b).mp h₁
  obtain ⟨⟨h1', h2'⟩, h3', h4'⟩ := (Diag.sameWords_iff b c).mp h₂
  exact (Diag.sameWords_iff a c).mpr ⟨⟨h1.trans h1', h2.trans h2'⟩, h3.trans h3', h4.trans h4'⟩

/-- Two records print as one line: one code, one output scope, the same words. -/
public def Diag.sameLine (a b : Diag) : Bool :=
  (decide (a.kind = b.kind) && decide (a.output = b.output)) && Diag.sameWords a b

public theorem Diag.sameLine_iff (a b : Diag) :
    Diag.sameLine a b = true ↔
      (a.kind = b.kind ∧ a.output = b.output) ∧ Diag.sameWords a b = true := by
  simp [Diag.sameLine, and_assoc]

private theorem Diag.sameLine_refl (a : Diag) : Diag.sameLine a a = true :=
  (Diag.sameLine_iff a a).mpr ⟨⟨rfl, rfl⟩, Diag.sameWords_refl a⟩

private theorem Diag.sameLine_symm {a b : Diag} (h : Diag.sameLine a b = true) :
    Diag.sameLine b a = true := by
  obtain ⟨⟨hk, ho⟩, hw⟩ := (Diag.sameLine_iff a b).mp h
  exact (Diag.sameLine_iff b a).mpr ⟨⟨hk.symm, ho.symm⟩, Diag.sameWords_symm hw⟩

private theorem Diag.sameLine_trans {a b c : Diag} (h₁ : Diag.sameLine a b = true)
    (h₂ : Diag.sameLine b c = true) : Diag.sameLine a c = true := by
  obtain ⟨⟨hk, ho⟩, hw⟩ := (Diag.sameLine_iff a b).mp h₁
  obtain ⟨⟨hk', ho'⟩, hw'⟩ := (Diag.sameLine_iff b c).mp h₂
  exact (Diag.sameLine_iff a c).mpr
    ⟨⟨hk.trans hk', ho.trans ho'⟩, Diag.sameWords_trans hw hw'⟩

private theorem Diag.sameLine_congr {a b : Diag} (h : Diag.sameLine a b = true) :
    Diag.sameLine a = Diag.sameLine b := by
  funext c
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun hac => Diag.sameLine_trans (Diag.sameLine_symm h) hac,
    fun hbc => Diag.sameLine_trans h hbc⟩

/-- The line a record's words print on: the first warning in them. -/
private def Diag.lineOf (l : List Diag) (d : Diag) : Nat :=
  l.findIdx (fun e => Diag.sameLine d e && e.severity.isWarning)

private theorem Diag.lineOf_congr {a b : Diag} (l : List Diag) (h : Diag.sameLine a b = true) :
    Diag.lineOf l a = Diag.lineOf l b := by
  unfold Diag.lineOf
  rw [Diag.sameLine_congr h]

private theorem Diag.lineOf_spec (l : List Diag) (j : Nat) (hj : j < l.length)
    (hw : l[j].severity.isWarning = true) :
    ∃ hs : Diag.lineOf l l[j] < l.length, Diag.lineOf l l[j] ≤ j ∧
      Diag.sameLine l[j] l[Diag.lineOf l l[j]] = true ∧
      l[Diag.lineOf l l[j]].severity.isWarning = true ∧
      Diag.lineOf l l[Diag.lineOf l l[j]] = Diag.lineOf l l[j] := by
  have hq : (Diag.sameLine l[j] l[j] && l[j].severity.isWarning) = true := by
    simp only [Diag.sameLine_refl, hw, Bool.and_self]
  have hlt : Diag.lineOf l l[j] < l.length :=
    List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem hj, hq⟩
  have hg := List.findIdx_getElem (w := hlt)
  simp only [Bool.and_eq_true] at hg
  obtain ⟨hgs, hgw⟩ := hg
  have hle := Diag.findIdx_le_of_true
    (p := fun e => Diag.sameLine l[j] e && e.severity.isWarning) hj hq
  exact ⟨hlt, hle, hgs, hgw, (Diag.lineOf_congr l hgs).symm⟩

private theorem Diag.lineOf_eq_iff (l : List Diag) (s k : Nat) (hs : s < l.length)
    (hk : k < l.length) (hss : Diag.lineOf l l[s] = s)
    (hkw : l[k].severity.isWarning = true) :
    Diag.lineOf l l[k] = s ↔ Diag.sameLine l[s] l[k] = true := by
  constructor
  · intro hf
    obtain ⟨_, _, hsl, _, _⟩ := Diag.lineOf_spec l k hk hkw
    have : Diag.sameLine l[k] l[s] = true := by simpa [hf] using hsl
    exact Diag.sameLine_symm this
  · intro h
    rw [Diag.lineOf_congr l (Diag.sameLine_symm h)]
    exact hss

/-- The first record of a record's census loss (`sameLoss`). -/
private def Diag.opener (l : List Diag) (d : Diag) : Diag :=
  l.getD (l.findIdx (Diag.sameLoss d)) d

private theorem Diag.opener_lt (l : List Diag) (i : Nat) (h : i < l.length)
    (hs : l[i].subject.isSome = true) :
    l.findIdx (Diag.sameLoss l[i]) < l.length :=
  List.findIdx_lt_length_of_exists ⟨_, List.getElem_mem h,
    (Diag.sameLoss_iff _ _).mpr ⟨⟨rfl, rfl⟩, rfl, hs⟩⟩

private theorem Diag.opener_eq (l : List Diag) (i : Nat) (h : i < l.length)
    (hs : l[i].subject.isSome = true) :
    Diag.opener l l[i] = l[l.findIdx (Diag.sameLoss l[i])]'(Diag.opener_lt l i h hs) := by
  simp [Diag.opener, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (Diag.opener_lt l i h hs)]

/-- The index whose line counts a record: a warning's, its line; a note's or
an error's, the line of its census loss's first record where that record is a
warning, else that first record, which carries the loss's count itself; and a
record that names no subject and is no warning, its own. -/
private def Diag.repeatCarrier (l : List Diag) (i : Nat) (d : Diag) : Nat :=
  if d.severity.isWarning then Diag.lineOf l d
  else if d.subject.isSome then
    if (Diag.opener l d).severity.isWarning then Diag.lineOf l (Diag.opener l d)
    else l.findIdx (Diag.sameLoss d)
  else i

private theorem Diag.repeatCarrier_lt (l : List Diag) (i : Nat) (h : i < l.length) :
    Diag.repeatCarrier l i l[i] < l.length := by
  unfold Diag.repeatCarrier
  split
  · rename_i hw
    exact (Diag.lineOf_spec l i h hw).1
  · split
    · rename_i _ hs
      have hf := Diag.opener_lt l i h hs
      rw [Diag.opener_eq l i h hs]
      split
      · rename_i hw
        exact (Diag.lineOf_spec l _ hf hw).1
      · exact hf
    · exact h

/-- What `sameLine` compares, as one value a table keys. -/
private structure Diag.LineKey where
  kind : Nat
  output : Option Diag.Output
  message : String
  help : Option String
  recovery : Option Diag.Recovery
  refused : Option String
  deriving DecidableEq, Hashable

private def Diag.lineKey (d : Diag) : Diag.LineKey :=
  ⟨d.kind.ctorIdx, d.output, d.message, d.help, d.recovery, d.refused⟩

/-- What `sameLoss` compares of records naming a subject. -/
private def Diag.lossKey (d : Diag) : Nat × Option Diag.Output × Option String :=
  (d.kind.ctorIdx, d.output, d.subject)

private theorem Diag.kind_eq_of_ctorIdx {a b : DiagCode} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← DiagCode.ofNat_ctorIdx a, h, DiagCode.ofNat_ctorIdx]

private theorem Diag.lineKey_beq (d e : Diag) :
    (Diag.lineKey e == Diag.lineKey d) = Diag.sameLine d e := by
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, Diag.sameLine_iff, Diag.sameWords_iff]
  constructor
  · intro h
    simp only [Diag.lineKey, Diag.LineKey.mk.injEq] at h
    obtain ⟨hk, ho, hm, hh, hr, hf⟩ := h
    exact ⟨⟨(Diag.kind_eq_of_ctorIdx hk).symm, ho.symm⟩, ⟨hm.symm, hh.symm⟩, hr.symm, hf.symm⟩
  · rintro ⟨⟨hk, ho⟩, ⟨hm, hh⟩, hr, hf⟩
    simp [Diag.lineKey, hk, ho, hm, hh, hr, hf]

private theorem Diag.lossKey_beq (d e : Diag) :
    (e.subject.isSome && Diag.lossKey e == Diag.lossKey d) = Diag.sameLoss d e := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, beq_iff_eq, Diag.sameLoss_iff]
  constructor
  · rintro ⟨hs, h⟩
    simp only [Diag.lossKey, Prod.mk.injEq] at h
    obtain ⟨hk, ho, hsub⟩ := h
    exact ⟨⟨(Diag.kind_eq_of_ctorIdx hk).symm, ho.symm⟩, hsub.symm, hsub ▸ hs⟩
  · rintro ⟨⟨hk, ho⟩, hsub, hs⟩
    exact ⟨hsub ▸ hs, by simp [Diag.lossKey, hk, ho, hsub]⟩

/-- For each key, the first index from `j` at which `p` admits an element `key` names, over `m`'s
entries, in one pass. -/
private def Diag.firstByKey [BEq κ] [Hashable κ] (p : α → Bool) (key : α → κ) :
    List α → Nat → Std.HashMap κ Nat → Std.HashMap κ Nat
  | [], _, m => m
  | x :: xs, j, m => Diag.firstByKey p key xs (j + 1) (if p x then m.insertIfNew (key x) j else m)

private theorem Diag.firstByKey_getElem? [BEq κ] [Hashable κ] [LawfulBEq κ] (p : α → Bool)
    (key : α → κ) (l : List α) (j : Nat) (m : Std.HashMap κ Nat) (k : κ) :
    (Diag.firstByKey p key l j m)[k]? =
      (m[k]?).or (if l.findIdx (fun x => p x && key x == k) < l.length
        then some (j + l.findIdx (fun x => p x && key x == k)) else none) := by
  induction l generalizing j m with
  | nil => simp [Diag.firstByKey]
  | cons x xs ih =>
    rw [Diag.firstByKey, ih]
    by_cases hx : (p x && key x == k) = true
    · have hp : p x = true := ((Bool.and_eq_true _ _).mp hx).1
      have hk : key x = k := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hx).2
      subst hk
      have hfx : List.findIdx (fun y => p y && key y == key x) (x :: xs) = 0 := by
        simp [List.findIdx_cons, hp]
      simp only [hp, ↓reduceIte]
      rw [Std.HashMap.getElem?_insertIfNew, hfx]
      cases hm : m[key x]? with
      | none =>
        have hn : ¬ key x ∈ m := by
          rw [Std.HashMap.mem_iff_isSome_getElem?, hm]; simp
        simp [hn]
      | some v =>
        have hn : key x ∈ m := by
          rw [Std.HashMap.mem_iff_isSome_getElem?, hm]; simp
        simp [hn]
    · have hm' : (if p x then m.insertIfNew (key x) j else m)[k]? = m[k]? := by
        split
        · rename_i hp
          have hk : (key x == k) = false := by simpa [hp] using hx
          simp [Std.HashMap.getElem?_insertIfNew, hk]
        · rfl
      have hf : List.findIdx (fun y => p y && key y == k) (x :: xs) =
          List.findIdx (fun y => p y && key y == k) xs + 1 := by
        rw [List.findIdx_cons]
        simp only [Bool.not_eq_true] at hx
        simp [hx]
      rw [hm', hf, List.length_cons]
      congr 1
      by_cases hlt : List.findIdx (fun y => p y && key y == k) xs < xs.length
      · have hlt' : List.findIdx (fun y => p y && key y == k) xs + 1 < xs.length + 1 := by omega
        simp only [hlt, hlt', ↓reduceIte, Option.some.injEq]
        omega
      · have hlt' : ¬ List.findIdx (fun y => p y && key y == k) xs + 1 < xs.length + 1 := by omega
        simp only [hlt, hlt', ↓reduceIte]

/-- `findIdx` of a key's elements, read from the table. -/
private theorem Diag.firstByKey_findIdx [BEq κ] [Hashable κ] [LawfulBEq κ] (p : α → Bool)
    (key : α → κ) (l : List α) (k : κ) :
    ((Diag.firstByKey p key l 0 {})[k]?).getD l.length =
      l.findIdx (fun x => p x && key x == k) := by
  rw [Diag.firstByKey_getElem?]
  simp only [Std.HashMap.getElem?_empty, Option.none_or, Nat.zero_add]
  split
  · rfl
  · rename_i h
    exact (Nat.le_antisymm (List.findIdx_le_length) (Nat.not_lt.mp h)).symm

/-- `repeatCarrier`'s index for every record, from two key tables built in one pass each. -/
private def Diag.carriersOf (ds : Array Diag) : Array Nat :=
  let lines := Diag.firstByKey (·.severity.isWarning) Diag.lineKey ds.toList 0 {}
  let losses := Diag.firstByKey (·.subject.isSome) Diag.lossKey ds.toList 0 {}
  let lineAt (d : Diag) : Nat := (lines[Diag.lineKey d]?).getD ds.size
  ds.mapIdx fun i d =>
    if d.severity.isWarning then lineAt d
    else if d.subject.isSome then
      let f := (losses[Diag.lossKey d]?).getD ds.size
      if (ds[f]?.getD d).severity.isWarning then lineAt (ds[f]?.getD d) else f
    else i

private theorem Diag.carriersOf_toList (ds : Array Diag) :
    (Diag.carriersOf ds).toList = ds.toList.mapIdx (Diag.repeatCarrier ds.toList) := by
  have hline (d : Diag) :
      ((Diag.firstByKey (·.severity.isWarning) Diag.lineKey ds.toList 0 {})[Diag.lineKey d]?).getD
        ds.size = Diag.lineOf ds.toList d := by
    rw [← Array.length_toList, Diag.firstByKey_findIdx, Diag.lineOf]
    congr 1
    funext e
    rw [Diag.lineKey_beq, Bool.and_comm]
  have hloss (d : Diag) :
      ((Diag.firstByKey (·.subject.isSome) Diag.lossKey ds.toList 0 {})[Diag.lossKey d]?).getD
        ds.size = ds.toList.findIdx (Diag.sameLoss d) := by
    rw [← Array.length_toList, Diag.firstByKey_findIdx]
    congr 1
    funext e
    exact Diag.lossKey_beq d e
  rw [Diag.carriersOf, Array.toList_mapIdx]
  congr 1
  funext i d
  simp only [hline, hloss, Diag.repeatCarrier, Diag.opener, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

/-- The records a shown line counts: a warning in its words, and a note or an
error whose census loss opens on a warning in its words — the sites a
once-per-construct emitter delivers as notes beside its first warning. -/
public def Diag.countsOn (l : List Diag) (w e : Diag) : Bool :=
  if e.severity.isWarning then Diag.sameLine w e
  else e.subject.isSome &&
    ((l.getD (l.findIdx (Diag.sameLoss e)) e).severity.isWarning &&
      Diag.sameLine w (l.getD (l.findIdx (Diag.sameLoss e)) e))

private theorem Diag.repeatCarrier_eq_iff (l : List Diag) (s m : Nat) (hs : s < l.length)
    (hm : m < l.length) (hsw : l[s].severity.isWarning = true) (hss : Diag.lineOf l l[s] = s) :
    Diag.repeatCarrier l m l[m] = s ↔ Diag.countsOn l l[s] l[m] = true := by
  have hne : ∀ k (hk : k < l.length), l[k].severity.isWarning = false → k ≠ s := by
    intro k hk hkw hks
    subst hks
    rw [hsw] at hkw
    exact absurd hkw (by simp)
  cases hmw : l[m].severity.isWarning
  · cases hms : l[m].subject.isSome
    · have hc : Diag.repeatCarrier l m l[m] = m := by
        simp [Diag.repeatCarrier, hmw, hms]
      rw [hc]
      simp only [Diag.countsOn, hmw, hms, Bool.false_eq_true, ite_false, Bool.false_and]
      exact ⟨fun h => absurd h (hne m hm hmw), fun h => absurd h (by simp)⟩
    · have hf := Diag.opener_lt l m hm hms
      have ho := Diag.opener_eq l m hm hms
      have hget : l.getD (l.findIdx (Diag.sameLoss l[m])) l[m] =
          l[l.findIdx (Diag.sameLoss l[m])]'hf := ho
      cases how : (l[l.findIdx (Diag.sameLoss l[m])]'hf).severity.isWarning
      · have hc : Diag.repeatCarrier l m l[m] = l.findIdx (Diag.sameLoss l[m]) := by
          simp [Diag.repeatCarrier, hmw, hms, ho, how]
        rw [hc]
        simp only [Diag.countsOn, hmw, hms, hget, how, Bool.false_eq_true, ite_false,
          Bool.true_and, Bool.false_and]
        exact ⟨fun h => absurd h (hne _ hf how), fun h => absurd h (by simp)⟩
      · have hc : Diag.repeatCarrier l m l[m] =
            Diag.lineOf l (l[l.findIdx (Diag.sameLoss l[m])]'hf) := by
          simp [Diag.repeatCarrier, hmw, hms, ho, how]
        rw [hc]
        simp only [Diag.countsOn, hmw, hms, hget, how, Bool.false_eq_true, ite_false,
          Bool.true_and]
        exact Diag.lineOf_eq_iff l s _ hs hf hss how
  · have hc : Diag.repeatCarrier l m l[m] = Diag.lineOf l l[m] := by
      simp [Diag.repeatCarrier, hmw]
    rw [hc]
    simp only [Diag.countsOn, hmw, ite_true]
    exact Diag.lineOf_eq_iff l s m hs hm hss hmw

/-- One record as the log delivers it: its count, and a warning that is not
the first line of its words delivered as a note. -/
private def Diag.foldOne (n : Nat) (shown : Bool) (d : Diag) : Diag :=
  if d.severity.isWarning && !shown then { d with sites := n }.demote
  else { d with sites := n }

private theorem Diag.foldOne_sites (n : Nat) (s : Bool) (d : Diag) : (Diag.foldOne n s d).sites = n := by
  unfold Diag.foldOne; split <;> rfl

private theorem Diag.foldOne_severity (n : Nat) (s : Bool) (d : Diag) :
    (Diag.foldOne n s d).severity = if d.severity.isWarning && !s then .note else d.severity := by
  unfold Diag.foldOne
  split <;> rfl

private theorem Diag.foldOne_shown (n : Nat) (s : Bool) (d : Diag)
    (h : (Diag.foldOne n s d).severity.isWarning = true) :
    s = true ∧ d.severity.isWarning = true := by
  rw [Diag.foldOne_severity] at h
  cases hb : (d.severity.isWarning && !s)
  · simp only [hb, Bool.false_eq_true, ite_false] at h
    refine ⟨?_, h⟩
    simpa [h] using hb
  · simp only [hb, ite_true] at h
    exact absurd h (by simp [Severity.isWarning])

/-- Fold repeated wordings: the first warning in a wording carries the count, later ones
deliver as notes. -/
public def Diag.foldRepeats (ds : Array Diag) : Array Diag :=
  let line := Diag.carriersOf ds
  let counts := Diag.countsOf ds.size line.toList
  ds.mapIdx fun i d =>
    Diag.foldOne (counts[i]?.getD 0) (!d.severity.isWarning || line[i]?.getD i == i) d

private theorem Diag.foldRepeats_getElem? (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    (Diag.foldRepeats ds)[i]? =
      some (Diag.foldOne ((ds.toList.mapIdx (Diag.repeatCarrier ds.toList)).count i)
        (!ds[i].severity.isWarning || Diag.repeatCarrier ds.toList i ds[i] == i) ds[i]) := by
  simp only [Diag.foldRepeats, Array.getElem?_mapIdx, Array.getElem?_eq_getElem h, Option.map_some]
  rw [Diag.carriersOf_toList, Diag.countsOf_count ds.size _ i h, ← Array.getElem?_toList,
    Diag.carriersOf_toList]
  simp [List.getElem?_mapIdx, Array.getElem?_eq_getElem h]

public theorem Diag.foldRepeats_size_exact (ds : Array Diag) : (Diag.foldRepeats ds).size = ds.size :=
  Array.size_mapIdx

public theorem Diag.foldRepeats_record_exact (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    ((Diag.foldRepeats ds)[i]?).map
      (fun d => { d with sites := ds[i].sites, demoted := ds[i].demoted }) = some ds[i] := by
  rw [Diag.foldRepeats_getElem? ds i h]
  simp only [Option.map_some, Option.some.injEq]
  unfold Diag.foldOne
  split <;> rfl

public theorem Diag.foldRepeats_sum_exact (ds : Array Diag) :
    ((Diag.foldRepeats ds).toList.map (·.sites)).sum = ds.size := by
  have hmap : (Diag.foldRepeats ds).toList.map (·.sites) =
      (List.range ds.size).map ((ds.toList.mapIdx (Diag.repeatCarrier ds.toList)).count ·) := by
    apply List.ext_getElem
    · simp [Diag.foldRepeats]
    · intro n hn _
      have hn' : n < ds.size := by simpa [Diag.foldRepeats] using hn
      have hget := Diag.foldRepeats_getElem? ds n hn'
      rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [Array.getElem?_eq_getElem (by rw [Diag.foldRepeats_size_exact]; exact hn')] at hget
      rw [Option.some.inj hget, Diag.foldOne_sites]
  rw [hmap, Diag.sum_count_range]
  have hall : ∀ o ∈ ds.toList.mapIdx (Diag.repeatCarrier ds.toList), o < ds.size := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp ho
    have := Diag.repeatCarrier_lt ds.toList j hj
    rwa [Array.length_toList] at this
  rw [List.filter_eq_self.mpr (by simpa using hall)]
  simp

public theorem Diag.foldRepeats_kept_exact (ds : Array Diag) (i : Nat) (h : i < ds.size)
    (hw : ds[i].severity.isWarning = false) :
    ((Diag.foldRepeats ds)[i]?).map (·.severity) = some ds[i].severity := by
  rw [Diag.foldRepeats_getElem? ds i h]
  simp [Diag.foldOne_severity, hw]

public theorem Diag.foldRepeats_error_exact (ds : Array Diag) (i : Nat) (h : i < ds.size)
    (he : ds[i].severity = .error) :
    ((Diag.foldRepeats ds)[i]?).map (·.severity) = some .error := by
  rw [Diag.foldRepeats_kept_exact ds i h (by rw [he]; rfl), he]

private theorem Diag.foldRepeats_shown_at (ds : Array Diag) (s : Nat) (hs : s < ds.size)
    (hw : ds[s].severity.isWarning = true) (hsh : Diag.lineOf ds.toList ds[s] = s) :
    ((Diag.foldRepeats ds)[s]?).map (·.severity.isWarning) = some true := by
  rw [Diag.foldRepeats_getElem? ds s hs]
  simp only [Option.map_some, Option.some.injEq]
  have hc : Diag.repeatCarrier ds.toList s ds[s] = s := by simp [Diag.repeatCarrier, hw, hsh]
  rw [Diag.foldOne_severity]
  simp [hc, hw]

public theorem Diag.foldRepeats_shown_exact (ds : Array Diag) (j : Nat) (hj : j < ds.size)
    (hw : ds[j].severity.isWarning = true) :
    ∃ i, ∃ hi : i < ds.size, i ≤ j ∧ Diag.sameLine ds[j] ds[i] = true ∧
      ((Diag.foldRepeats ds)[i]?).map (·.severity.isWarning) = some true := by
  have hjl : j < ds.toList.length := by simpa using hj
  obtain ⟨hs, hle, hsl, hsW, hss⟩ := Diag.lineOf_spec ds.toList j hjl (by simpa using hw)
  have hs' : Diag.lineOf ds.toList ds.toList[j] < ds.size := by simpa using hs
  refine ⟨_, hs', hle, by simpa using hsl, ?_⟩
  exact Diag.foldRepeats_shown_at ds _ hs' (by simpa using hsW) (by simpa using hss)

public theorem Diag.foldRepeats_visible_inj (ds : Array Diag) (i j : Nat) (hi : i < ds.size)
    (hj : j < ds.size)
    (hvi : ((Diag.foldRepeats ds)[i]?).map (·.severity.isWarning) = some true)
    (hvj : ((Diag.foldRepeats ds)[j]?).map (·.severity.isWarning) = some true)
    (h : Diag.sameLine ds[i] ds[j] = true) : i = j := by
  rw [Diag.foldRepeats_getElem? ds i hi] at hvi
  rw [Diag.foldRepeats_getElem? ds j hj] at hvj
  simp only [Option.map_some, Option.some.injEq] at hvi hvj
  obtain ⟨si, wi⟩ := Diag.foldOne_shown _ _ _ hvi
  obtain ⟨sj, wj⟩ := Diag.foldOne_shown _ _ _ hvj
  simp only [wi, wj, Bool.not_true, Bool.false_or, beq_iff_eq] at si sj
  simp only [Diag.repeatCarrier, wi, wj, ite_true] at si sj
  rw [← si, ← sj]
  exact Diag.lineOf_congr ds.toList h

private theorem Diag.countP_or_le {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun e => p e || q e) ≤ l.countP p + l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    cases p a <;> cases q a <;> simp <;> omega

private theorem Diag.filter_size_countP (ds : Array Diag) (p : Diag → Bool) :
    (ds.filter p).size = ds.toList.countP p := by
  rw [List.countP_eq_length_filter, ← Array.length_toList, Array.toList_filter]

private theorem Diag.foldRepeats_line_count (ds : Array Diag) (s : Nat) (hs : s < ds.size)
    (hw : ds[s].severity.isWarning = true) (hss : Diag.lineOf ds.toList ds[s] = s) :
    ((Diag.foldRepeats ds)[s]?).map (·.sites) =
      some (ds.filter (Diag.countsOn ds.toList ds[s])).size := by
  have hsl : s < ds.toList.length := by simpa using hs
  have hcount := Diag.count_mapIdx_eq_countP (Diag.repeatCarrier ds.toList)
    (Diag.countsOn ds.toList ds.toList[s]) s
    fun m hm => Diag.repeatCarrier_eq_iff ds.toList s m hsl hm (by simpa using hw)
      (by simpa using hss)
  rw [Diag.foldRepeats_getElem? ds s hs]
  simp only [Option.map_some, Option.some.injEq, Diag.foldOne_sites]
  rw [hcount, Diag.filter_size_countP]
  simp

public theorem Diag.foldRepeats_line_exact (ds : Array Diag) (s : Nat) (hs : s < ds.size)
    (hw : ds[s].severity.isWarning = true)
    (hfirst : ∀ k (hk : k < s),
      (Diag.sameLine ds[s] ds[k] && ds[k].severity.isWarning) = false) :
    ((Diag.foldRepeats ds)[s]?).map (·.sites) =
      some (ds.filter (Diag.countsOn ds.toList ds[s])).size := by
  have hsl : s < ds.toList.length := by simpa using hs
  have hss : Diag.lineOf ds.toList ds[s] = s := by
    unfold Diag.lineOf
    rw [List.findIdx_eq hsl]
    refine ⟨by simp [Diag.sameLine_refl, hw], fun k hk => ?_⟩
    simpa using hfirst k hk
  exact Diag.foldRepeats_line_count ds s hs hw hss

public theorem Diag.foldRepeats_wording_between (ds : Array Diag) (j : Nat) (hj : j < ds.size)
    (hw : ds[j].severity.isWarning = true) :
    ∃ i d, i ≤ j ∧ (Diag.foldRepeats ds)[i]? = some d ∧ d.severity.isWarning = true ∧
      (∃ hi : i < ds.size, Diag.sameLine ds[j] ds[i] = true) ∧
      (ds.filter fun e => e.severity.isWarning && Diag.sameLine ds[j] e).size ≤ d.sites ∧
      d.sites ≤ (ds.filter fun e => e.severity.isWarning && Diag.sameLine ds[j] e).size +
        (ds.filter fun e => !e.severity.isWarning &&
          Diag.countsOn ds.toList ds[j] e).size := by
  have hjl : j < ds.toList.length := by simpa using hj
  have hwl : ds.toList[j].severity.isWarning = true := by simpa using hw
  obtain ⟨hs, hle, hsl, hsW, hss⟩ := Diag.lineOf_spec ds.toList j hjl hwl
  generalize Diag.lineOf ds.toList ds.toList[j] = s at hs hle hsl hsW hss
  have hs' : s < ds.size := by simpa using hs
  have hsW' : ds[s].severity.isWarning = true := by simpa using hsW
  have hss' : Diag.lineOf ds.toList ds[s] = s := by simpa using hss
  have hcount := Diag.foldRepeats_line_count ds s hs' hsW' hss'
  have hshow := Diag.foldRepeats_shown_at ds s hs' hsW' hss'
  have hjs : Diag.sameLine ds[j] ds[s] = true := by simpa using hsl
  have hcongr : Diag.sameLine ds[s] = Diag.sameLine ds[j] :=
    (Diag.sameLine_congr hjs).symm
  cases hget : (Diag.foldRepeats ds)[s]? with
  | none => rw [hget] at hshow; exact absurd hshow (by simp)
  | some d =>
    rw [hget] at hshow hcount
    simp only [Option.map_some, Option.some.injEq] at hshow hcount
    refine ⟨s, d, hle, hget, hshow, ⟨hs', hjs⟩, ?_, ?_⟩
    · rw [hcount, Diag.filter_size_countP, Diag.filter_size_countP]
      apply List.countP_mono_left
      intro e _ he
      simp only [Bool.and_eq_true] at he
      simp [Diag.countsOn, he.1, hcongr, he.2]
    · rw [hcount, Diag.filter_size_countP, Diag.filter_size_countP, Diag.filter_size_countP]
      refine Nat.le_trans (List.countP_mono_left ?_) (Diag.countP_or_le _ _ _)
      intro e _ he
      have hc : Diag.countsOn ds.toList ds[j] e = true := by
        simpa only [Diag.countsOn, hcongr] using he
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      cases hew : e.severity.isWarning
      · exact Or.inr ⟨rfl, hc⟩
      · simp only [Diag.countsOn, hew, ite_true] at hc
        exact Or.inl ⟨rfl, hc⟩

/-- One accepted record and the loss it is a site of. -/
public structure Diag.Accepted where
  code : String
  output : Option Diag.Output
  loss : String
  deriving Repr, BEq

/-- An optional text spelled so distinct values spell distinct keys. -/
private def optKey : Option String → String
  | none => "none"
  | some s => "some " ++ s.quote

private def Diag.Recovery.key : Diag.Recovery → String
  | .ignored => "ignored"
  | .skipped => "skipped"
  | .replacedBy r => "replacedBy " ++ r.quote

/-- A span with every field of its position, so distinct spans spell distinct keys. -/
public def Diag.spanKey : Option Span → String
  | none => "none"
  | some s =>
    let origins := ",".intercalate (s.pos.origins.map fun o => s!"{o.id}:{o.name.quote}")
    s!"{s.file.quote}|{s.pos.line}|{s.pos.col}|{origins}|{optKey s.pos.command}|\
{s.pos.sourceMapped}|{s.pos.openEol}|{s.pos.closeEol}"

/-- The output a record is scoped to, `all` where it applies to every one. -/
public def Diag.outputKey (o : Option Diag.Output) : String := (o.map (·.label)).getD "all"

public def Diag.Accepted.of (d : Diag) : Diag.Accepted :=
  { code := d.code, output := d.output
    loss := match d.subject with
      | some s => "subject\x00" ++ s
      | none => s!"words\x00{d.message}\x00{optKey d.help}\x00{(d.recovery.map (·.key)).getD "none"}\x00{optKey d.refused}" }

/-- The accepted codes, one per loss, first acceptance first. -/
public def Diag.acceptedLosses (accepted : Array Diag.Accepted) : Array String :=
  let keyed := accepted.mapIdx fun i a => (s!"{a.code}\x00{Diag.outputKey a.output}\x00{a.loss}", i, a.code)
  let sorted := keyed.qsort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 < y.2.1)
  let firsts := sorted.zipIdx.filterMap fun (x, k) =>
    if k > 0 && (sorted[k - 1]?.map (·.1)) == some x.1 then none else some x.2
  (firsts.qsort fun x y => x.1 < y.1).map (·.2)

/-- Diagnostics resolved against the document's acceptance, with each phase's counts. -/
public structure Resolution where
  diags : Array Diag := #[]
  fired : Array String := #[]
  accepted : Array Diag.Accepted := #[]
  errors : Nat := 0
  /-- The errors among them whose cause stops the writer. -/
  stops : Nat := 0
  warnings : Nat := 0
  notes : Nat := 0
  deriving Repr, BEq

public def Resolution.append (a b : Resolution) : Resolution :=
  { diags := a.diags ++ b.diags
    fired := a.fired ++ b.fired
    accepted := a.accepted ++ b.accepted
    errors := a.errors + b.errors
    stops := a.stops + b.stops
    warnings := a.warnings + b.warnings
    notes := a.notes + b.notes }

@[simp] theorem Resolution.empty_append_id (r : Resolution) :
    ({} : Resolution).append r = r := by
  cases r
  simp [append]

@[simp] theorem Resolution.append_empty_id (r : Resolution) :
    r.append {} = r := by
  cases r
  simp [append]

private def Resolution.record (r : Resolution) (d : Diag) (accepted : Bool) : Resolution :=
  { diags := r.diags.push d
    fired := r.fired.push d.code ++ (d.carries.map (·.code)).toArray
    accepted := if accepted then r.accepted.push (Diag.Accepted.of d) else r.accepted
    errors := r.errors + (if d.severity == .error then 1 else 0)
    stops := r.stops + (if d.severity == .error && d.kind.stopsWriter then 1 else 0)
    warnings := r.warnings + (if d.severity == .warning then 1 else 0)
    notes := r.notes + (if d.severity == .note && !accepted then 1 else 0) }

private theorem Resolution.record_append (a b : Resolution) (d : Diag) (accepted : Bool) :
    (a.append b).record d accepted = a.append (b.record d accepted) := by
  cases accepted <;> simp [record, append, -Array.push_append, Array.append_push, Nat.add_assoc,
    Array.append_assoc]

public def Diag.resolveAll (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) : Resolution := Id.run do
  let mut r : Resolution := {}
  for d0 in ds do
    let (d, acc) := Diag.accept allowed allowAll d0
    r := r.record d acc
  return r

private theorem Diag.resolveAll_fold (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) :
    Diag.resolveAll allowed allowAll ds = ds.foldl (fun r d0 =>
      let (d, acc) := Diag.accept allowed allowAll d0
      r.record d acc) {} := by
  simp [resolveAll]

public theorem Diag.resolveAll_append_exact (allowed : Array String) (allowAll : Bool)
    (xs ys : Array Diag) :
    Diag.resolveAll allowed allowAll (xs ++ ys) =
      (Diag.resolveAll allowed allowAll xs).append (Diag.resolveAll allowed allowAll ys) := by
  rw [resolveAll_fold, Array.foldl_append, resolveAll_fold, resolveAll_fold]
  let step (r : Resolution) (d0 : Diag) : Resolution :=
    let (d, acc) := Diag.accept allowed allowAll d0
    r.record d acc
  have h := Array.foldl_hom (Resolution.append (xs.foldl step {}))
    (g₁ := step) (g₂ := step) (xs := ys) (init := ({} : Resolution))
    (fun r d0 => Resolution.record_append _ r
      (Diag.accept allowed allowAll d0).1 (Diag.accept allowed allowAll d0).2)
  simpa [step] using h

private theorem Resolution.record_stops_zero (r : Resolution) (d : Diag) (accepted : Bool) :
    (r.record d accepted).stops = 0 ↔
      r.stops = 0 ∧ (d.severity == .error && d.kind.stopsWriter) = false := by
  simp only [record]
  cases (d.severity == .error && d.kind.stopsWriter) <;> simp

private theorem Diag.accept_stops_false (allowed : Array String) (allowAll : Bool) (d : Diag) :
    ((Diag.accept allowed allowAll d).1.severity == .error && d.kind.stopsWriter) = false ↔
      (d.kind.stopsWriter = true →
        d.demoted = true ∨ allowAll = true ∨ allowed.contains d.code = true) := by
  cases hs : d.kind.stopsWriter
  · simp
  · have he := DiagCode.stopsWriter_error d.kind hs
    have e1 : (Severity.error != Severity.note) = true := rfl
    have e2 : (Severity.error == Severity.error) = true := rfl
    have e3 : (Severity.note == Severity.error) = false := rfl
    unfold Diag.accept Diag.severity
    cases hd : d.demoted <;> cases ha : allowAll <;> cases hc : allowed.contains d.code <;>
      simp [he, hd, e1, e2, e3]

/-- A resolution stops the writer exactly when a diagnostic whose cause stops it stands unaccepted:
neither delivered demoted, nor accepted by `\allow` or `--best-effort`. -/
public theorem Diag.resolveAll_stops_exact (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) :
    (Diag.resolveAll allowed allowAll ds).stops = 0 ↔
      ∀ d ∈ ds, d.kind.stopsWriter = true →
        d.demoted = true ∨ allowAll = true ∨ allowed.contains d.code = true := by
  rw [resolveAll_fold, ← Array.foldl_toList]
  have go : ∀ (l : List Diag) (r : Resolution),
      (l.foldl (fun r d0 => let (d, acc) := Diag.accept allowed allowAll d0
        r.record d acc) r).stops = 0 ↔
        r.stops = 0 ∧ ∀ d ∈ l, d.kind.stopsWriter = true →
          d.demoted = true ∨ allowAll = true ∨ allowed.contains d.code = true := by
    intro l
    induction l with
    | nil => intro r; simp
    | cons d rest ih =>
      intro r
      rw [List.foldl_cons, ih]
      have hk : (Diag.accept allowed allowAll d).1.kind = d.kind := by
        unfold Diag.accept; split <;> rfl
      rw [Resolution.record_stops_zero, hk, Diag.accept_stops_false]
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · intro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, h2⟩
      · intro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, h2⟩
  exact (go ds.toList {}).trans (by simp)

/-- The `\allow` entries no emitted or carried diagnostic matched. -/
public def Diag.unfired (allowed : Array String) (fired : Array String) : Array String :=
  allowed.filter (!fired.contains ·)

public theorem Loss.degraded_floor_ships_exact :
    Loss.degraded.floor.ships = true := by
  rfl

public theorem Diag.of_code_exact (c : DiagCode) (message : String) (span : Option Span)
    (help subject : Option String) (refused : Option String := none)
    (trigger : Option String := none) (recovery : Option Diag.Recovery := none)
    (output : Option Diag.Output := none) (detail : Option String := none) :
    (Diag.of c message span help subject refused trigger recovery output detail).code =
      c.code := by
  rfl

public theorem DiagCode.w0320_code_exact : DiagCode.W0320.code = "W0320" := by
  rfl

end LeanTex.Core
