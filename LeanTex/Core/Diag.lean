namespace LeanTex.Core

structure Pos where
  line : Nat := 1
  col : Nat := 1
  deriving Repr, BEq

def Pos.next (p : Pos) (newline : Bool) : Pos :=
  if newline then ⟨p.line + 1, 1⟩ else ⟨p.line, p.col + 1⟩

structure Span where
  file : String
  pos : Pos
  deriving Repr, BEq

inductive Severity where
  | error
  | warning
  | note
  deriving Repr, BEq

def Severity.label : Severity → String
  | .error => "error"
  | .warning => "warning"
  | .note => "note"

/-- What a reader of the shipped output loses at the site that emits a
diagnostic. Severity is a function of one question — can the reader recover
what the document declared? — so it is derived from this classification,
never chosen at a call site. -/
inductive Loss where
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
  /-- A skipped construct with no content operand (packages, templating,
  TeX conditionals): the meaning of the content survives. -/
  | config
  /-- Translation notes and advice; the output matches the intent. -/
  | info
  deriving Repr, BEq

/-- The policy: a dropped loss is an error, everything else is a warning or a
note. `pending` is a warning by design — the engine renders as much as it can
and says what it could not, because a document is more useful than a refusal
when the gap is one the project has committed to closing. `--werror` turns
every warning fatal for a caller who wants the strict reading, and `\allow`
in a document downgrades named dropped-loss codes to warnings (see
`Diag.accept`). -/
def Loss.severity : Loss → Severity
  | .dropped => .error
  | .pending => .warning
  | .degraded => .warning
  | .config => .warning
  | .info => .note

/-- Every diagnostic code the engine can emit: one constructor per code, so
an unregistered code is unrepresentable and every walk over the codes is
compiler-exhaustive. The letter prefix is the code's history, not its
severity — severity comes from the declared `Loss` alone. -/
inductive DiagCode where
  | E0001 | E0002
  | E0101 | E0102 | E0111 | E0112 | E0113
  | E0201 | E0202 | E0205
  | E0303 | E0304 | E0305 | E0306 | E0309 | E0310 | E0311 | E0312 | E0313
  | E0316 | E0320 | E0321 | E0322 | E0323 | E0324 | E0325 | E0326 | E0327
  | E0328 | E0329 | E0330 | E0331 | E0332
  | E0401 | E0402 | E0403 | E0404
  | E0501
  | N0100 | N0101 | N0102 | N0103 | N0105 | N0200
  | W0001 | W0003 | W0004 | W0005 | W0006 | W0007 | W0008 | W0009 | W0010
  | W0011 | W0012 | W0013 | W0014 | W0015
  | W0102 | W0103 | W0104 | W0105 | W0106 | W0108 | W0110
  | W0201 | W0202
  | W0301 | W0302 | W0303 | W0304 | W0307 | W0308 | W0309 | W0310 | W0311
  | W0312 | W0313 | W0314 | W0315 | W0316 | W0317 | W0318 | W0319
  | W0320 | W0321 | W0322 | W0323 | W0324 | W0325 | W0326 | W0327 | W0328
  | W0329 | W0330 | W0331 | W0332
  | W0501
  | W0601 | W0602
  deriving Repr, BEq, DecidableEq

/-- The registry: each code's printed name, its declared `Loss`, and its one
meaning. One code, one meaning — a new code is forced through this match,
where a collision with an existing number is visible before it ships, and
the compiler holds every projection exhaustive. -/
def DiagCode.spec : DiagCode → String × Loss × String
  | .E0001 => ("E0001", .dropped, "cannot read an input file")
  | .E0002 => ("E0002", .dropped, "input is not valid UTF-8")
  | .E0101 => ("E0101", .dropped, "lone backslash at end of input")
  | .E0102 => ("E0102", .dropped, "unclosed verbatim environment")
  | .E0111 => ("E0111", .dropped, "beamer template body carrying content dropped")
  | .E0112 => ("E0112", .dropped, "\\titlegraphic content dropped")
  | .E0113 => ("E0113", .dropped, "unrecognised \\sectionlinesformat body dropped")
  | .E0201 => ("E0201", .dropped, "unclosed group or environment at end of input")
  | .E0202 => ("E0202", .dropped, "unexpected closer")
  | .E0205 => ("E0205", .dropped, "malformed or mismatched environment name")
  | .E0303 => ("E0303", .dropped, "malformed \\define signature")
  | .E0304 => ("E0304", .dropped, "missing argument for a command")
  | .E0305 => ("E0305", .dropped, "parameter expects text")
  | .E0306 => ("E0306", .dropped, "unknown parameter reference in a definition body")
  | .E0309 => ("E0309", .dropped, "unknown document class")
  | .E0310 => ("E0310", .dropped, "content before the first \\item in a list")
  | .E0311 => ("E0311", .dropped, "reserved character in text")
  | .E0312 => ("E0312", .dropped, "block-level command used inline")
  | .E0313 => ("E0313", .dropped, "only declarations may appear before \\begin{document}")
  | .E0316 => ("E0316", .dropped, "unclosed optional argument")
  | .E0320 => ("E0320", .dropped, "invalid key or missing value in a declaration block")
  | .E0321 => ("E0321", .dropped, "unreadable value for a declaration key")
  | .E0322 => ("E0322", .dropped, "unknown key in a declaration block")
  | .E0323 => ("E0323", .dropped, "declaration key value has the wrong type")
  | .E0324 => ("E0324", .dropped, "unknown page size name")
  | .E0325 => ("E0325", .dropped, "unreadable \\assert expression")
  | .E0326 => ("E0326", .dropped, "name not in the palette where a colour is required")
  | .E0327 => ("E0327", .dropped, "not a \\page key")
  | .E0328 => ("E0328", .dropped, "not a styleable element")
  | .E0329 => ("E0329", .dropped, "unknown diagnostic code in \\allow")
  | .E0330 => ("E0330", .dropped, "layout assertion failed against the shipped pages")
  | .E0331 => ("E0331", .dropped, "unreadable length")
  | .E0332 => ("E0332", .dropped, "covered fraction outside 1–99 percent")
  | .E0401 => ("E0401", .dropped, "no usable font found on the host")
  | .E0402 => ("E0402", .dropped, "LEANTEX_FONT is unusable")
  | .E0403 => ("E0403", .dropped, "no installed font family by that name")
  | .E0404 => ("E0404", .dropped, "a font file could not be used")
  | .E0501 => ("E0501", .dropped, "\\input nesting too deep")
  | .N0100 => ("N0100", .info, "LaTeX idiom translated to its native declaration")
  | .N0101 => ("N0101", .config, "geometry keys without a native equivalent dropped")
  | .N0102 => ("N0102", .info, "option ignored: it configures machinery the engine does not model")
  | .N0103 => ("N0103", .info, "\\section short title unused: nothing consumes it yet")
  | .N0105 => ("N0105", .config, "\\setkomafont on a non-styleable element ignored")
  | .N0200 => ("N0200", .info, "page set short: its skips gave their shrink")
  | .W0001 => ("W0001", .config, "content after \\end{document} is ignored")
  | .W0003 => ("W0003", .degraded, "math is typeset as plain text until M6")
  | .W0004 => ("W0004", .dropped, "font has no glyph for a character; dropped")
  | .W0005 => ("W0005", .degraded, "overfull line, no feasible break")
  | .W0006 => ("W0006", .degraded, "declared face variant missing; another face substitutes")
  | .W0007 => ("W0007", .degraded, "paged-media furniture omitted from HTML")
  | .W0008 => ("W0008", .config, "\\fonts dir is not a directory")
  | .W0009 => ("W0009", .degraded, "no glyph in the declared face; set from a fallback face")
  | .W0010 => ("W0010", .degraded, "lists nest four levels; deeper levels reuse the fourth marker")
  | .W0011 => ("W0011", .degraded, "declared math face has no OpenType MATH table")
  | .W0012 => ("W0012", .degraded, "math construct not rendered yet; set as source text")
  | .W0013 => ("W0013", .config, "an \\allow'd code never fired")
  | .W0014 => ("W0014", .degraded, "alignment row disagrees with its grid's columns; padded")
  | .W0015 => ("W0015", .degraded, "equation numbers not rendered yet; rows set unnumbered")
  | .W0102 => ("W0102", .degraded, "unsupported colour model")
  | .W0103 => ("W0103", .config, "unsupported package skipped")
  | .W0104 => ("W0104", .config, "unsupported TeX construct skipped")
  | .W0105 => ("W0105", .degraded, "overlay specification does not name a step")
  | .W0106 => ("W0106", .config, "expl3 code skipped")
  | .W0108 => ("W0108", .degraded, "\\centering is inert inside an argument")
  | .W0110 => ("W0110", .degraded, "unsupported \\includegraphics option; ignored")
  | .W0201 => ("W0201", .degraded, "measure outside the readable band")
  | .W0202 => ("W0202", .degraded, "heading sets more space below than above")
  | .W0301 => ("W0301", .degraded, "unknown command; arguments kept as text")
  | .W0302 => ("W0302", .degraded, "unknown environment; body kept")
  | .W0303 => ("W0303", .config, "built-in name cannot be redefined")
  | .W0304 => ("W0304", .degraded, "colour name not in the palette; content kept uncoloured")
  | .W0307 => ("W0307", .pending, "construct not implemented yet; its content is not rendered")
  | .W0308 => ("W0308", .degraded, "tables are not laid out yet; rows set as plain lines")
  | .W0309 => ("W0309", .config, "\\maketitle with nothing declared")
  | .W0310 => ("W0310", .degraded, "'[' never closes; not an argument")
  | .W0311 => ("W0311", .degraded, "a second \\frametitle replaces the first")
  | .W0312 => ("W0312", .degraded, "no {...} group after a command; skipped")
  | .W0313 => ("W0313", .dropped, "{...} groups went with an unknown wrapper")
  | .W0314 => ("W0314", .degraded, "column width is not a fraction of the text width")
  | .W0315 => ("W0315", .degraded, "low-contrast colour pairing (WCAG 2.2)")
  | .W0316 => ("W0316", .config, "unknown option in \\palette; block skipped")
  | .W0317 => ("W0317", .config, "a card carries no running head or foot; declaration dropped")
  | .W0318 => ("W0318", .config, "\\chrome outside the slides class; ignored")
  | .W0319 => ("W0319", .degraded, "unknown theme; the document is unthemed")
  | .W0320 => ("W0320", .degraded, "heading levels skip a step (HTML §4.3.11, WCAG G141)")
  | .W0321 => ("W0321", .degraded, "the document title follows another heading")
  | .W0322 => ("W0322", .config, "a second \\maketitle is ignored; the title is typeset once")
  | .W0323 => ("W0323", .config, "unknown backend name in \\begin{ifbackend}; ignored")
  | .W0324 => ("W0324", .dropped, "\\begin{ifbackend} content addressed to no backend")
  | .W0325 => ("W0325", .degraded, "more than one <nav> landmark on one page")
  | .W0326 => ("W0326", .degraded, "in-page link with no target anchor on the page")
  | .W0327 => ("W0327", .degraded, "two distinct section titles fold to the same anchor")
  | .W0328 => ("W0328", .degraded, "running content wraps; only its first line is kept")
  | .W0329 => ("W0329", .config, "reserved layout-only construct skipped; no content is affected")
  | .W0330 => ("W0330", .degraded, "declared page with a defaulted ink is illegible (WCAG 2.2)")
  | .W0331 => ("W0331", .degraded, "declared marker not expressible in this backend; default substituted")
  | .W0332 => ("W0332", .degraded, "footer mixes the frame and physical page sequences undeclared")
  | .W0501 => ("W0501", .dropped, "\\input file not found; skipped")
  | .W0601 => ("W0601", .degraded, "image unreadable or not found; placeholder box placed")
  | .W0602 => ("W0602", .degraded, "image format unusable; placeholder box placed")

def DiagCode.code (c : DiagCode) : String := c.spec.1

def DiagCode.loss (c : DiagCode) : Loss := c.spec.2.1

def DiagCode.meaning (c : DiagCode) : String := c.spec.2.2

/-- Every code, for the registry checks in Tests.lean; `all_complete` holds
the list to the type. -/
def DiagCode.all : List DiagCode :=
  [.E0001, .E0002, .E0101, .E0102, .E0111, .E0112, .E0113, .E0201, .E0202, .E0205, .E0303, .E0304,
   .E0305, .E0306, .E0309, .E0310, .E0311, .E0312, .E0313, .E0316, .E0320,
   .E0321, .E0322, .E0323, .E0324, .E0325, .E0326, .E0327, .E0328, .E0329,
   .E0330, .E0331, .E0332, .E0401, .E0402, .E0403, .E0404, .E0501, .N0100, .N0101,
   .N0102, .N0103, .N0105, .N0200, .W0001, .W0003, .W0004, .W0005, .W0006, .W0007, .W0008,
   .W0009, .W0010, .W0011, .W0012, .W0013, .W0014, .W0015, .W0102, .W0103, .W0104, .W0105, .W0106, .W0108,
   .W0110, .W0201, .W0202, .W0301, .W0302, .W0303, .W0304, .W0307, .W0308,
   .W0309, .W0310, .W0311, .W0312, .W0313, .W0314, .W0315, .W0316, .W0317,
   .W0318, .W0319, .W0320, .W0321, .W0322, .W0323, .W0324, .W0325, .W0326,
   .W0327, .W0328, .W0329, .W0330, .W0331, .W0332, .W0501, .W0601,
   .W0602]

theorem DiagCode.all_complete (c : DiagCode) : DiagCode.all.contains c := by
  cases c <;> rfl

/-- The code a string names, for validating a document's `\allow` list. -/
def DiagCode.ofString? (s : String) : Option DiagCode :=
  DiagCode.all.find? (·.code == s)

structure Diag where
  severity : Severity
  code : String
  message : String
  span : Option Span := none
  help : Option String := none
  deriving Repr, BEq

/-- The one door a diagnostic is made through: the severity is the declared
loss's, so a free severity is unrepresentable at the call sites. -/
def Diag.of (c : DiagCode) (message : String) (span : Option Span := none)
    (help : Option String := none) : Diag :=
  { severity := c.loss.severity
    code := c.code
    message := message
    span := span
    help := help }

/-- Severity derives from the declared loss — definitionally: `Diag.of`
copies `c.loss.severity` into the field, so this is `rfl`, not a proof
with content. Its value is that the statement compiles at all: a call
site cannot make it false. -/
theorem Diag.of_severity (c : DiagCode) (message : String) (span : Option Span)
    (help : Option String) :
    (Diag.of c message span help).severity = c.loss.severity := rfl

/-- The escape hatch: `\allow{W0307, ...}` in a document's preamble accepts
the named losses, downgrading those errors to warnings for that document
alone; `--best-effort` (`allowAll`) accepts every loss — port mode. Rust's
lint levels (allow/warn/deny per scope, deny wins in CI) are the tested
prior art: acceptance is declared and scoped, never ambient — the build
summary prints what was accepted. Returns the resolved diagnostic and
whether it was accepted. -/
def Diag.accept (allowed : Array String) (allowAll : Bool) (d : Diag) : Diag × Bool :=
  if d.severity == .error && (allowAll || allowed.contains d.code) then
    ({ d with severity := .warning }, true)
  else (d, false)

/-- The `\allow` entries no emitted diagnostic ever matched: each is stale
acceptance the document no longer needs, and warning about it is one of the
hatch's teeth — an allow that silences nothing today may silence something
real tomorrow. -/
def Diag.unfired (allowed : Array String) (fired : Array String) : Array String :=
  allowed.filter (!fired.contains ·)

end LeanTex.Core
