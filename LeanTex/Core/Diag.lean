module

namespace LeanTex.Core

/-- One macro invocation in the provenance of an expanded token. The id
distinguishes separate invocations of the same name. -/
public structure MacroOrigin where
  id : Nat
  name : String
  deriving Repr, BEq, DecidableEq

public structure Pos where
  line : Nat := 1
  col : Nat := 1
  /-- Enclosing macro invocations, outermost first. -/
  origins : List MacroOrigin := []
  /-- The exact control token read by the TeX lexer, including its backslash.
  Desugared or otherwise synthetic positions have no written command. -/
  command : Option String := none
  deriving Repr, DecidableEq

/-- Source-location identity ignores expansion and token provenance. Consumers that
need macro ancestry read `Pos.origins` explicitly. -/
public instance : BEq Pos where
  beq p q := p.line == q.line && p.col == q.col

public theorem Pos.beq_origins_exact (p q : Pos) (xs ys : List MacroOrigin) :
    ({ p with origins := xs } == { q with origins := ys }) = (p == q) := rfl

/-- Source-token evidence, like macro ancestry, is presentation metadata:
changing it cannot change source-location identity. -/
public theorem Pos.beq_command_exact (p q : Pos) (xs ys : Option String) :
    ({ p with command := xs } == { q with command := ys }) = (p == q) := rfl

public def Pos.next (p : Pos) (newline : Bool) : Pos :=
  if newline then { p with line := p.line + 1, col := 1 }
  else { p with col := p.col + 1 }

public theorem Pos.next_origins_exact (p : Pos) (newline : Bool) :
    (p.next newline).origins = p.origins := by
  cases newline <;> rfl

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
  | .note => "note"

/-- The class letter a severity puts on its codes: `error` codes are `E…`,
`warning` codes `W…`, `note` codes `N…`. -/
public def Severity.letter : Severity → Char
  | .error => 'E'
  | .warning => 'W'
  | .note => 'N' 

/-- What a reader of the shipped output loses at the site that emits a
diagnostic. Severity is a function of one question — can the reader recover
what the document declared? — so it is derived from this classification,
never chosen at a call site. -/
public inductive Loss where
  /-- Declared content is absent with nothing in its place, and the engine has
  no plan to render it: a value it cannot interpret, a construct it will not
  support. Test: deleting the construct from the source leaves the output
  identical AND the construct carried content AND no milestone owns it. -/
  | dropped
  /-- Declared content is absent, but the engine has published a plan to
  render it: a construct owned by a milestone. The reader loses it today and
  gets it later, so refusing to emit the document is the wrong trade — the
  loss is reported and the rest of the document is still produced. -/
  | pending
  /-- The content is in the output but not as declared (unstyled, set as
  source text, a placeholder box, a substituted face): the reader sees
  *something stands here*. -/
  | degraded
  /-- The output is exactly what the document declared, and the declaration
  falls below a standard the engine holds documents to: a readable measure,
  a heading nearer its text than what precedes it, a WCAG contrast ratio.
  Nothing was lost in translation; the remedy is the author's, so the engine
  has nothing to recover in its place. -/
  | standard
  /-- A skipped construct with no content operand (packages, templating,
  TeX conditionals): the meaning of the content survives. -/
  | config
  /-- Translation notes and authoring advice, including missing image alternatives;
  the output matches the intent. -/
  | info
  deriving Repr, BEq

/-- The policy: a dropped loss is an error, everything else is a warning or a
note. `pending` is a warning by design — the engine renders as much as it can
and says what it could not, because a document is more useful than a refusal
when the gap is one the project has committed to closing. `--werror` makes
any remaining warning fail the exit code for a caller who wants the strict
reading, and `\allow` in a document accepts named codes, downgrading them to
notes (see `Diag.accept`) — an accepted loss is neither an error nor a
warning. -/
public def Loss.severity : Loss → Severity
  | .dropped => .error
  | .pending => .warning
  | .degraded => .warning
  | .standard => .warning
  | .config => .warning
  | .info => .note

/-- The class letter of a loss is its declared severity's letter. An error
code cannot acquire a warning letter at construction; accepting a loss
changes its effective severity later, without changing this letter. -/
public def Loss.letter (l : Loss) : Char := l.severity.letter

/-- The declared class as a machine reader sees it. A census bands on this,
never on the rendered severity: demotion (`Diag.accept`, `Diag.demote`, a
repeat site's note) changes what a line says it is, and never what was lost. -/
public def Loss.label : Loss → String
  | .dropped => "dropped"
  | .pending => "pending"
  | .degraded => "degraded"
  | .standard => "standard"
  | .config => "config"
  | .info => "info"

/-- Two classes never share a label, so banding on the label is banding on
the loss. -/
public theorem Loss.label_inj (a b : Loss) (h : a.label = b.label) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **What the construct's place on the page owes a reader.** The recovery
floor, declared once per loss class and derived at a salvage site exactly as
severity and the code letter already are.

It is declared here because it was being *rediscovered*. In one session
three salvage paths — math the parser could not model, an unknown command's
braced arguments, a diagram node whose body held one unreadable token — each
independently arrived at the same law, and two of them arrived at it by
first shipping the wrong thing: LaTeX source as body ink on five slides, a
length beside a label, and a whole label dropped so three pages shipped an
empty diagram frame. The law is not a property of math, or of pictures, or
of unknown commands. It is a property of the loss class, so it belongs to
the loss class. -/
public inductive Floor where
  /-- No floor exists, because no artifact does: a `dropped` loss fails the
  run, so there is no page for a recovery to stand on. -/
  | refuse
  /-- The construct's place may legitimately be empty. That is what
  `pending` *means* — the content is gone today and arrives with the
  milestone that owns it — so a blank there is the declared state and not a
  silent loss. Whatever does stand there is still the construct's own
  content. -/
  | absent
  /-- The construct's text content stands in its place: never its markup,
  and never nothing where the construct carried content — an empty salvage
  is paid for by a declared placeholder. This is the floor the three sites
  derived, and `degraded`'s own definition is why it is this one: the reader
  is promised that *something stands here*. -/
  | content
  /-- Nothing is owed and nothing appears: a `config` or `info` loss has no
  content operand, so ink in its place would be invention rather than
  recovery, and a `standard` loss's construct already stands as declared,
  so there is nothing to recover. -/
  | inert
  deriving Repr, BEq, DecidableEq

/-- The floor is a function of the declared loss and of nothing else — one
decision, one place, the same shape `Loss.severity` has. A new diagnostic
code inherits its floor from the class it declares; there is no site at
which a floor is chosen. -/
public def Loss.floor : Loss → Floor
  | .dropped => .refuse
  | .pending => .absent
  | .degraded => .content
  | .standard => .inert
  | .config => .inert
  | .info => .inert

/-- Does anything at all stand in the construct's place? A floor that ships
nothing is not a recovery, and routing a salvage to a code whose floor does
not ship puts ink where no content was lost. -/
public def Floor.ships : Floor → Bool
  | .content | .absent => true
  | .refuse | .inert => false

/-- Must the construct's place carry ink whenever the construct carried
content? Only `.content` owes that, and `inks_iff_degraded` says the
converse: no other loss class quietly acquires the obligation. -/
public def Floor.inks : Floor → Bool
  | .content => true
  | .refuse | .absent | .inert => false

/-- A floor that owes ink ships: the two questions are ordered, so no code
can be asked for ink in a place nothing stands in. -/
public theorem Floor.inks_ships (f : Floor) (h : f.inks) : f.ships := by
  cases f <;> simp_all [Floor.inks, Floor.ships]

/-- Every diagnostic code the engine can emit: one constructor per code, so
an unregistered code is unrepresentable and every walk over the codes is
compiler-exhaustive. The constructor names spell the rendered codes; the
letter itself is derived from the declared `Loss` at the one construction
site (`DiagCode.code`), and `DiagCode.code_letter` holds the two spellings
equal. -/
public inductive DiagCode where
  | E0001 | E0002 | E0003
  | E0101 | E0102 | E0111 | E0112 | E0113
  | E0201 | E0202 | E0205
  | E0303 | E0304 | E0305 | E0306 | E0309 | E0310 | E0311 | E0312 | E0313
  | E0316 | E0320 | E0321 | E0322 | E0323 | E0324 | E0325 | E0326 | E0327
  | E0328 | E0329 | E0330 | E0331 | E0332 | E0333 | E0334 | E0336 | E0340
  | E0401 | E0402 | E0403 | E0404 | E0405
  | E0501 | E0502 | E0503
  | N0100 | N0102 | N0103 | N0104 | N0105 | N0114 | N0200
  | W0001 | W0003 | W0005 | W0006 | W0007 | W0008 | W0009 | W0010
  | W0011 | W0012 | W0013 | W0014 | W0015 | W0016
  | N0016 | N0018 | N0017 | N0019 | N0020
  | W0101 | W0102 | W0103 | W0104 | W0105 | W0106 | W0108 | W0110 | W0111
  | W0201 | W0202
  | W0301 | W0302 | W0303 | W0304 | W0307 | W0309 | W0310 | W0311
  | W0312 | W0314 | W0315 | W0316 | W0317 | W0318 | W0319
  | W0320 | W0321 | W0322 | W0323 | W0325 | W0326 | W0327 | W0328
  | W0329 | W0330 | W0331 | W0332 | W0333 | W0334 | W0335 | W0336 | W0337 | W0338 | W0358
  | W0340 | W0342 | W0343 | W0345 | W0346 | W0348 | W0354 | W0355
  | W0349 | W0350 | W0356 | W0357
  | W0351 | W0352 | W0353
  | E0347
  | W0601 | W0602
  | E0359
  | W0361
  | W0362
  | W0363
  | W0364
  | E0365
  | W0366
  | N0021
  | W0367
  | W0368
  | W0369
  | E0375
  | W0370
  | W0371
  | W0372
  | W0373
  | W0374
  | N0376
  | N0022
  | W0377
  | N0023
  | W0378
  | W0379
  | E0382
  | W0380
  | W0381
  | W0383
  | W0387
  | W0701
  | W0603
  | W0604
  | W0605
  | W0384
  | W0385
  | W0386
  | W0388
  | W0389
  | W0390
  | W0391
  | E0390
  | W0392
  | N0419
  | W0435
  | W0393
  | W0394 | E0395 | W0396
  | E0606
  | E0607
  deriving Repr, BEq, DecidableEq

/-- The registry: each code's digits, its declared `Loss`, and its one
meaning. One code, one meaning — a new code is forced through this match,
where a collision with an existing number is visible before it ships, and
the compiler holds every projection exhaustive. The class letter is not
written here: `DiagCode.code` derives it from the loss. -/
private def DiagCode.spec : DiagCode → String × Loss × String
  | .E0001 => ("0001", .dropped, "cannot read an input file")
  | .E0002 => ("0002", .dropped, "input is not valid UTF-8")
  | .E0003 => ("0003", .dropped, "output formats do not have independent destinations; publication is refused")
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
  | .E0321 => ("0321", .dropped, "unreadable value for a declaration key")
  | .E0322 => ("0322", .dropped, "unknown key in a declaration block")
  | .E0323 => ("0323", .dropped, "declaration key value has the wrong type")
  | .E0324 => ("0324", .dropped, "unknown page size name")
  | .E0325 => ("0325", .dropped, "unreadable \\assert expression")
  | .E0326 => ("0326", .dropped, "name not in the palette where a colour is required")
  | .E0327 => ("0327", .dropped, "not a \\page key")
  | .E0328 => ("0328", .dropped, "not a styleable element")
  | .E0329 => ("0329", .dropped, "unknown diagnostic code in \\allow")
  | .E0330 => ("0330", .dropped, "layout assertion failed against the shipped pages")
  | .E0331 => ("0331", .dropped, "unreadable length")
  | .E0332 => ("0332", .dropped, "covered fraction outside 1–99 percent")
  | .E0401 => ("0401", .dropped, "no usable font found on the host")
  | .E0402 => ("0402", .dropped, "LEANTEX_FONT is unusable")
  | .E0403 => ("0403", .dropped, "no installed font family by that name")
  | .E0404 => ("0404", .dropped, "a font file could not be used")
  | .E0501 => ("0501", .dropped, "\\input nesting too deep")
  | .N0100 => ("0100", .info, "LaTeX idiom translated to its native declaration")
  | .W0101 => ("0101", .config, "preamble keys without a native equivalent dropped")
  | .N0102 => ("0102", .info, "option ignored: it configures machinery the engine does not model")
  | .N0103 => ("0103", .info, "\\section short title unused: nothing consumes it yet")
  | .N0104 => ("0104", .info, "a frame declared for another mode ships no page in this one")
  | .N0105 => ("0105", .info, "\\allow names a retired code; its successor answers")
  | .N0114 => ("0114", .info, "a TeX conditional resolved from the document's own definitions and loads")
  | .W0111 => ("0111", .config, "a styling declaration names no styleable element; ignored")
  | .N0200 => ("0200", .info, "page set short: its skips gave their shrink")
  | .W0001 => ("0001", .config, "content after \\end{document} is ignored")
  | .W0003 => ("0003", .degraded, "no math face available; math set as plain text")
  | .E0405 => ("0405", .dropped, "font has no glyph for a character; dropped")
  | .W0005 => ("0005", .degraded, "overfull line, no feasible break")
  | .W0006 => ("0006", .degraded, "declared face variant missing; another face substitutes")
  | .W0007 => ("0007", .degraded, "paged-media furniture omitted from HTML")
  | .W0008 => ("0008", .config, "\\fonts dir is not a directory")
  | .W0009 => ("0009", .degraded, "no glyph in the declared face; set from a fallback face")
  | .W0010 => ("0010", .degraded, "lists nest four levels; deeper levels reuse the fourth marker")
  | .W0011 => ("0011", .degraded, "declared math face has no OpenType MATH table")
  | .W0012 => ("0012", .degraded, "math construct not rendered yet; set as its text content")
  | .W0013 => ("0013", .config, "an \\allow'd code never fired")
  | .W0014 => ("0014", .degraded, "alignment row disagrees with its grid's columns; padded")
  | .W0015 => ("0015", .degraded, "equation numbers not rendered yet; rows set unnumbered")
  | .W0016 => ("0016", .degraded, "math alphabet glyph absent from the covered face; a stand-in keeps the letter")
  | .N0016 => ("0016", .info, "no math face declared; the engine picked one and says which")
  | .N0018 => ("0018", .info, "math alphabet unavailable in the selected face; source glyphs stand")
  | .N0017 => ("0017", .info, "no document class declared; the article page model is assumed")
  | .N0019 => ("0019", .info, "a backend conditional in content names a class or kernel decision made by hand")
  | .N0020 => ("0020", .info, "a local style file is read as part of the preamble")
  | .W0102 => ("0102", .degraded, "unsupported colour model")
  | .W0103 => ("0103", .config, "unsupported package skipped")
  | .W0104 => ("0104", .config, "unsupported TeX construct skipped")
  | .W0105 => ("0105", .degraded, "overlay specification does not name a step")
  | .W0106 => ("0106", .config, "expl3 code skipped")
  | .W0108 => ("0108", .degraded, "\\centering is inert inside an argument")
  | .W0110 => ("0110", .degraded, "unsupported command option; ignored")
  | .W0201 => ("0201", .standard, "measure outside the readable band")
  | .W0202 => ("0202", .standard, "heading sets more space below than above")
  | .W0301 => ("0301", .degraded, "unknown command; {...} arguments kept as text")
  | .W0302 => ("0302", .degraded, "unknown environment; body kept")
  | .W0303 => ("0303", .config, "built-in name cannot be redefined")
  | .W0304 => ("0304", .degraded, "colour name not in the palette; content kept uncoloured")
  | .W0307 => ("0307", .pending, "construct not implemented yet; its content is not rendered")
  | .W0309 => ("0309", .config, "\\maketitle with nothing declared")
  | .W0310 => ("0310", .degraded, "'[' never closes; not an argument")
  | .W0311 => ("0311", .degraded, "a second \\frametitle replaces the first")
  | .W0312 => ("0312", .degraded, "no {...} group after a command; skipped")
  | .E0333 => ("0333", .dropped, "picture expression unreadable or unresolvable; its shape is not drawn")
  | .E0336 => ("0336", .dropped, "{...} groups went with an unknown wrapper")
  | .E0340 => ("0340", .dropped, "unknown icon name; nothing is rendered")
  | .W0314 => ("0314", .degraded, "column width is not a fraction of the text width")
  | .W0315 => ("0315", .degraded, "low-contrast colour pairing (WCAG 2.2)")
  | .W0316 => ("0316", .config, "unknown option in \\palette; block skipped")
  | .W0317 => ("0317", .config, "a card carries no running head or foot; declaration dropped")
  | .W0318 => ("0318", .config, "\\chrome outside the slides class; ignored")
  | .W0319 => ("0319", .degraded, "unknown theme; the document is unthemed")
  | .W0320 => ("0320", .degraded, "heading levels skip a step (HTML §4.3.11, WCAG G141)")
  | .W0321 => ("0321", .degraded, "the document title follows another heading")
  | .W0322 => ("0322", .config, "a second \\maketitle is ignored; the title is typeset once")
  | .W0323 => ("0323", .config, "unknown backend name in \\begin{ifbackend}; ignored")
  | .E0334 => ("0334", .dropped, "\\begin{ifbackend} content addressed to no backend")
  | .W0325 => ("0325", .degraded, "more than one <nav> landmark on one page")
  | .W0326 => ("0326", .degraded, "in-page link with no target anchor on the page")
  | .W0327 => ("0327", .degraded, "two distinct section titles fold to the same anchor")
  | .W0328 => ("0328", .degraded, "one-line content wraps; only its first line is kept")
  | .W0329 => ("0329", .config, "reserved layout-only construct skipped; no content is affected")
  | .W0330 => ("0330", .degraded, "declared page with a defaulted ink is illegible (WCAG 2.2)")
  | .W0331 => ("0331", .degraded, "declared marker not expressible in this backend; default substituted")
  | .W0332 => ("0332", .degraded, "footer mixes the frame and physical page sequences undeclared")
  | .W0333 => ("0333", .degraded, "band slots collide; the lower-priority slot is painted over")
  | .W0334 => ("0334", .pending, "picture construct outside the rendered subset; not drawn")
  | .W0335 => ("0335", .degraded, "picture larger than the text area; it may overrun the page")
  | .W0336 => ("0336", .degraded, "node labels overlap; a relative placement parts centres, not text")
  | .W0337 => ("0337", .degraded, "table row disagrees with its column spec; padded to the grid")
  | .W0338 => ("0338", .degraded, "table is wider than the measure")
  | .W0358 => ("0358", .degraded, "a float taller than the text block overruns its page")
  | .W0340 => ("0340", .config, "a declaration in the document body is ignored")
  | .W0342 => ("0342", .degraded, "a definition shadows a palette role; the role is frozen where it is used")
  | .W0343 => ("0343", .config, "one setting is given two different values; the later declaration wins")
  | .W0345 => ("0345", .standard, "a themed element's resolved colour pairing is illegible (WCAG 2.2)")
  | .W0346 => ("0346", .config, "a declaration inside inline content is ignored")
  | .E0347 => ("0347", .dropped, "a running head or foot declared in the body is dropped with its content")
  | .W0348 => ("0348", .config, "a theme replaces a key the document already declared; the theme wins")
  | .W0354 => ("0354", .config, "a caption option the engine does not honour; named and ignored")
  | .W0355 => ("0355", .config, "a theme's slides furniture cannot draw under the class in force")
  | .W0349 => ("0349", .degraded, "reference to a key no \\label numbers; set as '??'")
  | .W0350 => ("0350", .config, "a key is \\label'ed more than once; the first wins")
  | .W0356 => ("0356", .degraded, "document class option refused by name; the document renders without it")
  | .W0357 => ("0357", .config, "a definition is expansion-time TeX; refused by design")
  | .W0351 => ("0351", .degraded, "a citation names no bibliography entry; its mark shows as ?")
  | .W0352 => ("0352", .degraded, "a malformed .bib entry is skipped; the rest of the file is kept")
  | .W0353 => ("0353", .degraded, "an unknown bibliography style; the reference list is set as unsrtnat")
  | .E0502 => ("0502", .dropped, "\\input file not found; skipped")
  | .E0503 => ("0503", .dropped, "\\bibliography file not found; the reference list is empty")
  | .W0601 => ("0601", .degraded, "image unreadable or not found; placeholder box placed")
  | .W0602 => ("0602", .degraded, "image format unusable; placeholder box placed")
  | .E0359 => ("0359", .dropped, "a \\note nested inside another note's frame is dropped")
  | .W0361 => ("0361", .config, "a built-in is not replaced by a redefinition the engine cannot run")
  | .W0362 => ("0362", .degraded, "picture entirely outside the rendered subset; a placeholder box marks its place")
  | .W0363 => ("0363", .degraded, "a title-page template node the engine cannot pin as written; what it sets stands at the title page's default place")
  | .W0364 => ("0364", .degraded, "an unresolved data path; nothing renders in its place")
  | .E0365 => ("0365", .dropped, "\\data file not found; its records are absent")
  | .W0366 => ("0366", .degraded, "a named font weight is not installed; the nearest installed weight substitutes")
  | .N0021 => ("0021", .info, "header and footer gaps differ as declared; equal gaps are the default")
  | .W0367 => ("0367", .config, "a beamerposter option outside the poster model; named and ignored")
  | .W0368 => ("0368", .degraded, "a language the engine ships no locale for; English captions and patterns stand in")
  | .W0369 => ("0369", .degraded, "a per-language font binding; one face serves every language, so the binding is dropped")
  | .E0375 => ("0375", .dropped, "\\dimexpr division rounds to nearest, not this engine's truncation, so the statement is dropped")
  | .W0370 => ("0370", .pending, "\\footnotemark and \\footnotetext are not paired yet; kept as text")
  | .W0371 => ("0371", .degraded, "a paragraph break inside \\footnote is set as a space")
  | .W0372 => ("0372", .degraded, "a footnote taller than the text block overruns its page")
  | .W0373 => ("0373", .degraded, "\\thanks is kept inline in the title block")
  | .W0374 => ("0374", .degraded, "a footnote on a card face is kept inline; a face has no note apparatus")
  | .N0376 => ("0376", .info, "an image ships no text alternative (WCAG 2.2)")
  | .N0022 => ("0022", .info, "a palette role, or a mix of two named colours, is realized on one ground to meet its contrast requirement (WCAG 2.2)")
  | .W0377 => ("0377", .degraded, "a link carries no text to name its purpose (WCAG 2.2)")
  | .N0023 => ("0023", .info, "a picture is drawn by an external tool at the boundary; the engine measures its box, and its text is not in the document's census")
  | .W0378 => ("0378", .degraded, "the PDF-to-SVG converter for boundary pictures is not runnable; the page shows their text alternatives")
  | .W0379 => ("0379", .degraded, "no boundary tool available for a picture outside the rendered subset; a placeholder box marks the picture")
  | .E0382 => ("0382", .dropped, "the boundary tool ran and drew nothing for a picture; the page would carry an empty box")
  | .W0380 => ("0380", .degraded, "a \\cref target of unknown kind; the plain number is set")
  | .W0381 => ("0381", .degraded, "a unit outside the siunitx table; set as its ASCII spelling")
  | .W0383 => ("0383", .pending, "algorithm construct outside the modeled subset; kept as a plain line")
  | .W0387 => ("0387", .config, "a known construct was read and had no effect")
  | .W0701 => ("0701", .pending, "an output contract fact this artifact does not yet realize")
  | .W0603 => ("0603", .degraded, "an image's embedded colour profile is dropped; the page reads it as device colour")
  | .W0604 => ("0604", .degraded, "an image's orientation tag is dropped; the page shows the stored orientation")
  | .W0605 => ("0605", .degraded, "an image has no usable browser face; the web page shows a placeholder instead")
  | .W0384 => ("0384", .degraded, "a frame taller than its page continues on the next page without a declared break")
  | .W0385 => ("0385", .degraded, "a colour or font change inside math is not carried; its content sets in the surrounding style")
  | .W0386 => ("0386", .degraded, "a declared line break did not hold: its line did not fit the measure and re-flowed")
  | .W0388 => ("0388", .degraded, "ink is painted off the medium; a viewer clips to the page and cannot show it")
  | .W0389 => ("0389", .degraded, "a math construct whose operands the floor has ruled on; its content operand sets in its place and the formula still sets as mathematics")
  | .W0390 => ("0390", .degraded, "no family is declared for a font slot the document sets in; the body face serves it")
  | .W0391 => ("0391", .config, "an unknown LaTeX internal ('@' in its name) in package code is skipped with its [...] and {...} arguments instead of setting them as text")
  | .E0390 => ("0390", .dropped, "a markdown construct this dialect refuses by design; its content is dropped")
  | .W0392 => ("0392", .degraded, "a markdown construct sets with part of its declaration dropped; its content still sets")
  | .N0419 => ("0419", .info, "a boundary picture no tool drew is drawn by the rendered subset instead; what the subset leaves out is named beside it")
  | .W0435 => ("0435", .degraded, "a \\qedhere whose QED this engine cannot set where amsthm sets it; the QED stands on a line of its own after the display")
  | .W0393 => ("0393", .degraded, "the installed syntax highlighter cannot classify a listing; its source is set as plain text")
  | .W0394 => ("0394", .degraded, "picture label has glyphs without measured outline bounds")
  | .E0395 => ("0395", .dropped, "picture label produced no line")
  | .W0396 => ("0396", .degraded, "picture label extends beyond its reserved glyph box")
  | .E0606 => ("0606", .dropped, "the HTML page has unresolved rendering resources; publication is refused")
  | .E0607 => ("0607", .dropped, "the PDF exceeds a supported storage bound; publication is refused")

public def DiagCode.digits (c : DiagCode) : String := c.spec.1

public def DiagCode.loss (c : DiagCode) : Loss := c.spec.2.1

public def DiagCode.meaning (c : DiagCode) : String := c.spec.2.2

/-- The floor a code's declared loss demands, the projection every salvage
site reads. Beside `DiagCode.code` and `Diag.severity`: a code has no floor
field to disagree with its class, so a new code inherits a correct recovery
rather than choosing one. -/
public def DiagCode.floor (c : DiagCode) : Floor := c.loss.floor

/-- **Exactly the degraded codes owe ink.** The obligation table's rule — a
`degraded` loss ships the construct's text content — is not one reading of
the registry among several: it is the whole of the ink obligation, for every
registered code. A future loss class cannot inherit the obligation by
looking similar to `degraded`, and a `degraded` code cannot escape it by
being routed somewhere quiet. -/
public theorem DiagCode.inks_iff_degraded (c : DiagCode) :
    c.floor.inks = (c.loss == .degraded) := by
  cases h : c.loss <;> simp only [DiagCode.floor, h, Loss.floor, Floor.inks] <;> decide


/-- The one place a code's printed name is spelled: the class letter comes
from the declared loss, the digits from the registry. A code whose letter
disagrees with its declared severity cannot be written. -/
public def DiagCode.code (c : DiagCode) : String :=
  String.singleton c.loss.letter ++ c.digits

/-- Every code's letter agrees with its declared severity. This is a fact
of the record, independent of the terminal format or later acceptance. -/
public theorem DiagCode.code_letter (c : DiagCode) :
    c.code.front = c.loss.severity.letter := by
  cases c <;> rfl

/-- A number at or past the last constructor's index. `ofNat` saturates —
every index beyond the last constructor answers with the last constructor —
so applying it here names that constructor without naming it by hand, which
is what makes `count` derivable. It is a *ceiling*, not a count: it never
needs touching as codes are added, and a value too small is a build failure
rather than a wrong answer (`all_complete` stops holding). -/
private def DiagCode.ctorCeiling : Nat := 65536

/-- How many codes the registry holds: read off the type, not maintained by
hand. Four agents adding a code in one session collided on the literal this
replaces and merged it to a number one short of the truth; the count is
derived now, so registering a code is one constructor and one `spec` arm and
nothing else.

Derived through the two helpers `deriving DecidableEq` synthesises for an
enum: `ofNat` saturates at the last constructor, so `ofNat ctorCeiling` *is*
that constructor, and `ctorIdx` reads its index. If either helper ever
changed shape the value would move, and the two theorems below would stop
holding — `all_complete` makes an undercount a build failure, `all_nodup` an
overcount (`ofNat` clamps out of range, so an overcount duplicates the last
constructor), so the derivation is checked in both directions rather than
trusted. -/
public def DiagCode.count : Nat := (DiagCode.ofNat DiagCode.ctorCeiling).ctorIdx + 1

/-- Every code, for the registry checks in Tests.lean — derived from the
type through the `ofNat` that `deriving DecidableEq` synthesises, never
hand-maintained: constructor declaration order, complete and duplicate-free
by the two theorems below, so the list cannot drift from the inductive. -/
public def DiagCode.all : List DiagCode :=
  (List.range DiagCode.count).map DiagCode.ofNat

public theorem DiagCode.all_complete (c : DiagCode) : DiagCode.all.contains c := by
  cases c <;> rfl

public theorem DiagCode.all_nodup : DiagCode.all.Nodup := by decide +kernel

/-- The code a string names, for validating a document's `\allow` list. -/
public def DiagCode.ofString? (s : String) : Option DiagCode :=
  DiagCode.all.find? (·.code == s)

/-- **A code a document can name is a surface, so retiring one is a
migration.** `\allow{<code>}` is written in documents this repository cannot
see, exactly as a CLI flag is invoked from build recipes it cannot see, and
the same rule applies: the old spelling keeps answering, with a note saying
what answers it now. Without this row a retirement turned a building document
into a hard error (`E0329`, a `dropped` loss: exit 1, no PDF) for a change
that took nothing away.

`some succ` means the fact is still named by another diagnostic. The
successor may report a broader loss, or be informational and need no
acceptance. `\allow` of the old spelling accepts *nothing*: accepting `succ`
in its place would accept every loss `succ` names, and a document that accepted dropped option runs
would silently accept every unknown command with them (measured: `--werror`
went from 1 to 0 on such a document). The note says which code names the
loss now, and the document widens its acceptance only by writing that code
itself if acceptance is needed. `none` means the loss cannot occur any more —
the engine's rule changed — so there is nothing to accept and nothing to fail
over. A pure
renumbering, whose successor names exactly the retired loss, would accept
its successor; no row is one, so the table does not carry that case.

A row leaves this list only when a document naming the old code is
implausible, which is a judgement about the world and not about this tree, so
in practice rows stay. -/
public def DiagCode.retired : List (String × Option String) :=
  [-- A refused command's leading `[...]` run was named by its own code at
   -- the same span as the command's refusal. Its fate is a clause of that
   -- refusal's message now, and W0301 names every unknown command, so the
   -- old spelling accepts nothing.
   ("W0341", some "W0301"),
   -- `\scshape` means uniform small caps, so a casing lie in the source is
   -- no longer how the canonical form is reached: the loss this named cannot
   -- occur.
   ("W0344", none),
   -- A missing alternative is authoring advice; no acceptance is needed.
   ("W0376", some "N0376")]

/-- An artifact whose diagnostics apply only when that output is requested. -/
public inductive Diag.Output where
  | pdf
  | html
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

public def Diag.Output.label : Diag.Output → String
  | .pdf => "pdf"
  | .html => "html"

/-- What the engine actually did after a loss. A proposed action belongs in
`Diag.help`; neither field is reconstructed from message prose. -/
public inductive Diag.Recovery where
  | ignored
  | skipped
  | replacedBy (replacement : String)
  deriving Repr, BEq, DecidableEq

/-- A diagnostic as delivered: `kind` is the registered code, and both the
rendered code string and the severity are its projections — no free
severity or code field exists, so a diagnostic disagreeing with its
code's declared `Loss` is unrepresentable rather than merely
unconstructed. `demoted` is the one policy bit (`accept`/`demote`): an
accepted or demoted diagnostic delivers as a note, whatever its loss.
`subject` is the key or source of the unresolved node a diagnostic names —
a `\ref` key, a `\cite` key, an image source — structured so that "this
loss is named" is a lookup, never a search of the message text
(`Ir.Diag.mentions`, the resolution gate `pending_named`). `sites` is how
many times this loss occurs in the document: a once-per-document warning
carries the total so the default log states it, and each further site rides
beside it as a note. One writer, `tallySites`, and its default is the
honest one for a diagnostic nothing else counted. -/
public structure Diag where
  kind : DiagCode
  message : String
  span : Option Span := none
  help : Option String := none
  demoted : Bool := false
  subject : Option String := none
  /-- The name this diagnostic refuses, when refusing a name is what it does:
  an unsupported package, an unknown theme, an unknown font theme slot.

  Separate from `subject`, which is the dedup key and is namespaced — an
  unknown command's key is `"ctrl:\<name>"`, not the bare name, so a consumer
  reading the name off `subject` reads it correctly for some codes and not
  others. The distinction was not academic: `\usetheme` was refusable without
  being enumerable, and the invariant that a name-refusal must first ask the
  input path for a file that would define it could only be *stated* against
  `subject`, where two of its codes set nothing at all and the statement was
  vacuously true.

  A structured field rather than a reading of the message, for the reason
  every `_named` claim in this tree gives: prose rots, and a claim that
  parses a sentence holds only until the sentence is reworded. -/
  refused : Option String := none
  sites : Nat := 1
  /-- Literal source spelling supplied by the emitter, independent of the census key. -/
  trigger : Option String := none
  /-- Actual handling of this loss, distinct from a suggested action in `help`. -/
  recovery : Option Diag.Recovery := none
  /-- `none` applies to every output; a scoped loss applies only to that artifact. -/
  output : Option Diag.Output := none
  deriving Repr, BEq

/-- **Is this code's loss part of the site census?** A `degraded` or
`pending` diagnostic says content did not reach the page as declared, so a
reader sizing the damage counts its sites — which `Diag.tallySites` can only
do through `subject`. A `config` or `info` loss has no content operand and
nothing to count, and a `standard` loss's content reached the page as
declared.

Declared here, beside `Loss.severity` and `Loss.floor`, and for the same
reason: it is a function of the loss class and of nothing else, so no call
site chooses it. A code since retired is why it is written down: it named a
fragment of an unknown command's arguments with no subject at all, which put
it outside the census entirely — `tallySites` returned a subjectless
diagnostic untouched, so it fired once per site, repeated its help at each,
and billed every site to `--werror`, while `W0301`, the same loss at the same
site, reported `(2 sites)` on one line. Neither arm chose that; one reached
for `warnOnce` and the other for `diag`, and nothing gated the choice. The
run's fate is a clause of `W0301`'s own message now
(`Elab.warnUnknownCmd_push_exact` is the emitter fact: one push per call,
carrying the construct's code and the subject `ctrl:<name>`), and
`subjectCensusChecks` is the gate. -/
public def Loss.censused : Loss → Bool
  | .degraded | .pending => true
  | .dropped | .standard | .config | .info => false

/-- The census question, per code — the projection a witness check reads. -/
public def DiagCode.censused (c : DiagCode) : Bool := c.loss.censused

/-- **Exactly the codes that owe ink are the codes that are counted.** The
census obligation and the recovery obligation do not drift apart: a code
whose place on the page must carry something is a code whose sites a reader
can count, and `pending` joins it because a declared absence is still a
number the reader is owed. Stated against `Floor.ships` rather than against
the loss list twice, so a future loss class cannot acquire one half of the
pair by looking similar. -/
public theorem DiagCode.censused_iff_ships (c : DiagCode) :
    c.censused = c.floor.ships := by
  cases h : c.loss <;>
    simp only [DiagCode.censused, DiagCode.floor, h, Loss.censused, Loss.floor, Floor.ships]

/-- The rendered code string: the kind's own spelling, derived. -/
public def Diag.code (d : Diag) : String := d.kind.code

/-- Severity is a projection, never a stored field: the declared loss's
severity, demoted to a note by policy alone. -/
public def Diag.severity (d : Diag) : Severity :=
  match d.demoted with
  | true => .note
  | false => d.kind.loss.severity

/-- The one door a diagnostic is made through. -/
public def Diag.of (c : DiagCode) (message : String) (span : Option Span := none)
    (help : Option String := none) (subject : Option String := none)
    (refused : Option String := none) (trigger : Option String := none)
    (recovery : Option Diag.Recovery := none) (output : Option Diag.Output := none) : Diag :=
  { kind := c
    message := message
    span := span
    help := help
    subject := subject
    refused := refused
    trigger := trigger
    recovery := recovery
    output := output }

/-- A refusal carries the name it refuses structurally, never as a reading of
its own words: what the door was handed is what comes back out. The fact the
name-refusal registry rests on — a consumer enumerating refusals reads a
field, so rewording a message cannot silently empty the registry. -/
public theorem Diag.of_refused (c : DiagCode) (message : String) (span : Option Span)
    (help subject refused : Option String) :
    (Diag.of c message span help subject refused).refused = refused := by rfl

/-- Severity derives from the declared loss — structurally now: `severity`
is a projection of the stored `kind`, so this is `rfl` and a call site
cannot make it false anywhere, not only at construction. -/
public theorem Diag.of_severity (c : DiagCode) (message : String) (span : Option Span)
    (help : Option String) (subject : Option String) :
    (Diag.of c message span help subject).severity = c.loss.severity := by rfl

/-- At construction, severity and code letter both come from the code's
`Loss`. A caller cannot choose them independently. -/
public theorem Diag.of_code_letter (c : DiagCode) (message : String) (span : Option Span)
    (help : Option String) (subject : Option String) :
    (Diag.of c message span help subject).code.front =
      (Diag.of c message span help subject).severity.letter :=
  c.code_letter

/-- Unscoped diagnostics always apply. A scoped diagnostic requires its artifact. -/
public def Diag.appliesTo (outputs : Array Diag.Output) (d : Diag) : Bool :=
  match d.output with
  | none => true
  | some output => outputs.contains output

/-- Stable projection for the driver, before acceptance and exit accounting.
An empty output set still retains common diagnostics. -/
-- premise: Diag.forOutputs_mem — only diagnostics of disabled artifacts are removed.
public def Diag.forOutputs (outputs : Array Diag.Output) (ds : Array Diag) : Array Diag :=
  ds.filter (Diag.appliesTo outputs)

/-- Projection retains exactly the original records whose scope applies. -/
public theorem Diag.forOutputs_mem (outputs : Array Diag.Output) (ds : Array Diag) (d : Diag) :
    d ∈ Diag.forOutputs outputs ds ↔
      d ∈ ds ∧ (∀ output, d.output = some output → output ∈ outputs) := by
  simp only [Diag.forOutputs, Array.mem_filter]
  cases h : d.output <;> simp [Diag.appliesTo, h]

/-- Repeated projection cannot duplicate or further change a diagnostic. -/
public theorem Diag.forOutputs_id (outputs : Array Diag.Output) (ds : Array Diag) :
    Diag.forOutputs outputs (Diag.forOutputs outputs ds) = Diag.forOutputs outputs ds := by
  simp [Diag.forOutputs, Array.filter_filter]

/-- The escape hatch: `\allow{W0307, ...}` in a document's preamble accepts
the named losses for that document alone; `--best-effort` (`allowAll`)
accepts every loss — port mode. Rust's lint levels (allow/warn/deny per
scope, deny wins in CI) are the tested prior art: acceptance is declared
and scoped, never ambient. An accepted diagnostic is downgraded to a note,
so a document that declares its intent emits nothing at default verbosity
— and the build summary always prints what was accepted, which is how
acceptance stays visible rather than silent. An accepted loss is not a
warning, so it never trips `--werror`: that is the point of accepting it.
Returns the resolved diagnostic and whether it was accepted. -/
public def Diag.accept (allowed : Array String) (allowAll : Bool) (d : Diag) : Diag × Bool :=
  if d.severity != .note && (allowAll || allowed.contains d.code) then
    ({ d with demoted := true }, true)
  else (d, false)

/-- Acceptance changes only the policy bit, preserving the entire record,
including present and future structured fields. -/
public theorem Diag.accept_record_exact (allowed : Array String) (allowAll : Bool) (d : Diag) :
    { (Diag.accept allowed allowAll d).1 with demoted := d.demoted } = d := by
  unfold Diag.accept
  split <;> rfl

/-- The spliced-`.sty` demotion: a TeX internal the engine correctly
refuses inside a style file the author did not write is per-line correct
and per-line unactionable — "'\\z@' is unknown" helps nobody holding only
their own document. The diagnostic keeps its code and message but is
delivered as a note (listed under `-v`), and N0020's "TeX internals
refused" count carries it at default verbosity. The demotion bit is
written here beside `Diag.accept`, the other policy door: severity is a
function of the declared loss and of policy declared in this module,
never of a call site. -/
public def Diag.demote (d : Diag) : Diag := { d with demoted := true }

/-- Explicit policy demotion preserves the entire record apart from its policy bit. -/
public theorem Diag.demote_record_exact (d : Diag) :
    { Diag.demote d with demoted := d.demoted } = d := by rfl

/-- Two diagnostics are sites of the *same* loss when they carry the same
code, structured subject and output scope. A PDF loss and an HTML loss
must remain distinct even when they name the same construct, so filtering
one artifact cannot inherit the other's count. -/
public def Diag.sameLoss (a b : Diag) : Bool :=
  (decide (a.kind = b.kind) && decide (a.output = b.output)) &&
    decide (a.subject = b.subject) && a.subject.isSome

private theorem Diag.sameLoss_iff (a b : Diag) :
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

/-- A census group cannot cross output scopes. -/
public theorem Diag.sameLoss_output_exact (a b : Diag) (h : Diag.sameLoss a b = true) :
    a.output = b.output := ((Diag.sameLoss_iff a b).mp h).1.2

/-- The index whose line carries a diagnostic's count: the first diagnostic
of its loss, or its own index when it names no subject. -/
private def Diag.carrier (ds : List Diag) (i : Nat) (d : Diag) : Nat :=
  if d.subject.isSome then ds.findIdx (Diag.sameLoss d) else i

/-- **The losses add up.** A once-per-document diagnostic names its
construct at the first site and delivers every later site as a note, so
the default log shows one line where the document has many. That line
therefore has to carry the total, or a reader sizing the damage from it
undercounts — ten lines standing for fifty losses is how a document full of
silent drops reads as nearly clean.

This is the one writer of `sites`: the first diagnostic of each loss carries
the number of diagnostics sharing its code, subject and output, every later one
carries 0, and a diagnostic with no subject is its own one site — so the
counts on a log add up to its length (`tallySites_sum_exact`). Stamping the
total on every site squared it for any reader who summed them. Nothing else
moves — no diagnostic is added, removed, reordered, demoted or reworded — so
counting cannot change what was lost, only what the reader is told about it. -/
public def Diag.tallySites (ds : Array Diag) : Array Diag :=
  let carriers := ds.toList.mapIdx (Diag.carrier ds.toList)
  ds.mapIdx fun i d => { d with sites := carriers.count i }

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

/-- Counting a list of indices over the first `n` counts the entries below
`n`: the fibres of a map into `[0, n)` partition its domain. -/
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
  simp [Diag.tallySites, h]

/-- Counting is not filtering: the tally holds every diagnostic it was
given, in order. -/
public theorem Diag.tallySites_length (ds : Array Diag) :
    (Diag.tallySites ds).size = ds.size := Array.size_mapIdx

/-- Counting changes only the count: each diagnostic keeps its code,
message, span, help, demotion and subject, so no loss is created,
silenced or reworded by being counted. -/
public theorem Diag.tallySites_id (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    ∃ d, (Diag.tallySites ds)[i]? = some d ∧ d.kind = (ds[i]).kind ∧
      d.message = (ds[i]).message ∧ d.span = (ds[i]).span ∧
      d.help = (ds[i]).help ∧ d.demoted = (ds[i]).demoted ∧
      d.subject = (ds[i]).subject :=
  ⟨_, Diag.tallySites_getElem? ds i h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Counting preserves the entire record except `sites`, including all
structured fields; this remains true when the record gains another field. -/
public theorem Diag.tallySites_record_exact (ds : Array Diag) (i : Nat) (h : i < ds.size) :
    ((Diag.tallySites ds)[i]?).map (fun d => { d with sites := ds[i].sites }) = some ds[i] := by
  rw [Diag.tallySites_getElem? ds i h]
  rfl

/-- **The counts on a log add up to its length.** Summing `sites` over every
record of a run gives the number of records, whatever the run — the claim a
reader sizing the damage makes when they add the numbers up. Each record
counts once, on its carrier's line. -/
public theorem Diag.tallySites_sum_exact (ds : Array Diag) :
    ((Diag.tallySites ds).toList.map (·.sites)).sum = ds.size := by
  have hmap : (Diag.tallySites ds).toList.map (·.sites) =
      (List.range ds.size).map ((ds.toList.mapIdx (Diag.carrier ds.toList)).count ·) := by
    apply List.ext_getElem
    · simp [Diag.tallySites]
    · intro n _ _
      simp [Diag.tallySites]
  rw [hmap, Diag.sum_count_range]
  have hall : ∀ o ∈ ds.toList.mapIdx (Diag.carrier ds.toList), o < ds.size := by
    intro o ho
    obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp ho
    have := Diag.carrier_lt ds.toList j hj
    rwa [Array.length_toList] at this
  rw [List.filter_eq_self.mpr (by simpa using hall)]
  simp

/-- **The number on the line is the number of sites in the log.** The first
diagnostic of a loss — the line the default log shows — carries the count
of diagnostics sharing that loss, so a reader who trusts the default line's
total and a reader who counts the `-v` sites by hand reach the same number. -/
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

/-- **A later site rides on the first.** Every diagnostic after the first of
its loss carries 0, so its note adds nothing to a sum the first line already
holds. -/
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

/-- **A diagnostic with no subject is its own one site.** `tallySites`
returns it with the count 1 and nothing else changed, whatever it carried.
This is the mechanism behind the census gate in Tests.lean: a `censused`
code emitted without a subject is invisible to the grouping, and the reader
sees one line per site instead of one line carrying the total. Nothing here
fixes that; it says precisely what is lost, so the gate over `DiagCode.all`
has a statement to rest on rather than a comment. -/
public theorem Diag.tallySites_subjectless_id (ds : Array Diag) (i : Nat) (h : i < ds.size)
    (hn : (ds[i]).subject.isNone) :
    (Diag.tallySites ds)[i]? = some { ds[i] with sites := 1 } := by
  rw [Diag.tallySites_getElem? ds i h]
  have hl : i < ds.toList.length := by simpa using h
  rw [Diag.count_mapIdx_eq_one (Diag.carrier ds.toList) i i hl
    fun j hj => Diag.carrier_eq_iff_self ds.toList i j hl hj (by simpa using hn)]

/-- Diagnostics resolved against the document's acceptance, with the counts
of every resolved phase. Counts follow acceptance, so an accepted loss is
neither an error nor a warning. -/
public structure Resolution where
  diags : Array Diag := #[]
  fired : Array String := #[]
  accepted : Array String := #[]
  errors : Nat := 0
  warnings : Nat := 0
  deriving Repr, BEq

/-- Phase accounting keeps the rendered records, acceptance and exit counts
in one value. `resolveAll_append_exact` holds this operation to resolving the
same stream at once, including its order and repeated diagnostic codes. -/
public def Resolution.append (a b : Resolution) : Resolution :=
  { diags := a.diags ++ b.diags
    fired := a.fired ++ b.fired
    accepted := a.accepted ++ b.accepted
    errors := a.errors + b.errors
    warnings := a.warnings + b.warnings }

@[simp] theorem Resolution.empty_append_id (r : Resolution) :
    ({} : Resolution).append r = r := by
  cases r
  simp [append]

@[simp] theorem Resolution.append_empty_id (r : Resolution) :
    r.append {} = r := by
  cases r
  simp [append]

/-- Grouping phases never changes their diagnostic records or verdict. -/
public theorem Resolution.append_assoc_exact (a b c : Resolution) :
    (a.append b).append c = a.append (b.append c) := by
  simp [append, Array.append_assoc, Nat.add_assoc]

private def Resolution.record (r : Resolution) (d : Diag) (accepted : Bool) : Resolution :=
  { diags := r.diags.push d
    fired := r.fired.push d.code
    accepted := if accepted then r.accepted.push d.code else r.accepted
    errors := r.errors + (if d.severity == .error then 1 else 0)
    warnings := r.warnings + (if d.severity == .warning then 1 else 0) }

private theorem Resolution.record_append (a b : Resolution) (d : Diag) (accepted : Bool) :
    (a.append b).record d accepted = a.append (b.record d accepted) := by
  cases accepted <;> simp [record, append, -Array.push_append, Array.append_push, Nat.add_assoc]

public def Diag.resolveAll (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) : Resolution := Id.run do
  let mut r : Resolution := {}
  for d0 in ds do
    let (d, acc) := Diag.accept allowed allowAll d0
    r := r.record d acc
  return r

/-- The actual imperative resolver's fold reading; no second runtime walk. -/
private theorem Diag.resolveAll_fold (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) :
    Diag.resolveAll allowed allowAll ds = ds.foldl (fun r d0 =>
      let (d, acc) := Diag.accept allowed allowAll d0
      r.record d acc) {} := by
  simp [resolveAll]

/-- Resolving consecutive phases equals resolving their combined stream.
The record equality covers diagnostic order, fired and accepted codes, and
both exit counts under the same acceptance policy. -/
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

/-- The `\allow` entries no emitted diagnostic ever matched: each is stale
acceptance the document no longer needs, and warning about it is one of the
hatch's teeth — an allow that silences nothing today may silence something
real tomorrow. -/
public def Diag.unfired (allowed : Array String) (fired : Array String) : Array String :=
  allowed.filter (!fired.contains ·)

end LeanTex.Core
