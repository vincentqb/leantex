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

/-- The class letter a severity puts on its codes: `error` codes are `E…`,
`warning` codes `W…`, `note` codes `N…`. -/
def Severity.letter : Severity → Char
  | .error => 'E'
  | .warning => 'W'
  | .note => 'N' 

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
when the gap is one the project has committed to closing. `--werror` makes
any remaining warning fail the exit code for a caller who wants the strict
reading, and `\allow` in a document accepts named codes, downgrading them to
notes (see `Diag.accept`) — an accepted loss is neither an error nor a
warning. -/
def Loss.severity : Loss → Severity
  | .dropped => .error
  | .pending => .warning
  | .degraded => .warning
  | .config => .warning
  | .info => .note

/-- The class letter of a loss is its severity's letter — both halves of a
rendered `error[E0333]` prefix come from the one declared `Loss`, so a
prefix like `error[W…]` is unrepresentable. -/
def Loss.letter (l : Loss) : Char := l.severity.letter

/-- Every diagnostic code the engine can emit: one constructor per code, so
an unregistered code is unrepresentable and every walk over the codes is
compiler-exhaustive. The constructor names spell the rendered codes; the
letter itself is derived from the declared `Loss` at the one construction
site (`DiagCode.code`), and `DiagCode.code_letter` holds the two spellings
equal. -/
inductive DiagCode where
  | E0001 | E0002
  | E0101 | E0102 | E0111 | E0112 | E0113
  | E0201 | E0202 | E0205
  | E0303 | E0304 | E0305 | E0306 | E0309 | E0310 | E0311 | E0312 | E0313
  | E0316 | E0320 | E0321 | E0322 | E0323 | E0324 | E0325 | E0326 | E0327
  | E0328 | E0329 | E0330 | E0331 | E0332 | E0333 | E0334 | E0336 | E0340
  | E0401 | E0402 | E0403 | E0404 | E0405
  | E0501 | E0502 | E0503
  | N0100 | N0102 | N0103 | N0114 | N0200
  | W0001 | W0003 | W0005 | W0006 | W0007 | W0008 | W0009 | W0010
  | W0011 | W0012 | W0013 | W0014 | W0015
  | N0016 | N0018 | N0017 | N0019 | N0020
  | W0101 | W0102 | W0103 | W0104 | W0105 | W0106 | W0108 | W0110 | W0111
  | W0201 | W0202
  | W0301 | W0302 | W0303 | W0304 | W0307 | W0309 | W0310 | W0311
  | W0312 | W0314 | W0315 | W0316 | W0317 | W0318 | W0319
  | W0320 | W0321 | W0322 | W0323 | W0325 | W0326 | W0327 | W0328
  | W0329 | W0330 | W0331 | W0332 | W0333 | W0334 | W0335 | W0337 | W0338 | W0358
  | W0340 | W0341 | W0342 | W0343 | W0345 | W0346 | W0348 | W0354 | W0355
  | W0349 | W0350 | W0356 | W0357
  | W0351 | W0352 | W0353
  | E0347
  | W0601 | W0602
  | E0359
  | W0361
  | W0362
  | W0364
  | E0365
  | W0366
  | N0021
  deriving Repr, BEq, DecidableEq

/-- The registry: each code's digits, its declared `Loss`, and its one
meaning. One code, one meaning — a new code is forced through this match,
where a collision with an existing number is visible before it ships, and
the compiler holds every projection exhaustive. The class letter is not
written here: `DiagCode.code` derives it from the loss. -/
def DiagCode.spec : DiagCode → String × Loss × String
  | .E0001 => ("0001", .dropped, "cannot read an input file")
  | .E0002 => ("0002", .dropped, "input is not valid UTF-8")
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
  | .W0101 => ("0101", .config, "geometry keys without a native equivalent dropped")
  | .N0102 => ("0102", .info, "option ignored: it configures machinery the engine does not model")
  | .N0103 => ("0103", .info, "\\section short title unused: nothing consumes it yet")
  | .N0114 => ("0114", .info, "TeX '\\ifdefined' resolved from the document's own definitions")
  | .W0111 => ("0111", .config, "\\setkomafont on a non-styleable element ignored")
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
  | .W0012 => ("0012", .degraded, "math construct not rendered yet; set as source text")
  | .W0013 => ("0013", .config, "an \\allow'd code never fired")
  | .W0014 => ("0014", .degraded, "alignment row disagrees with its grid's columns; padded")
  | .W0015 => ("0015", .degraded, "equation numbers not rendered yet; rows set unnumbered")
  | .N0016 => ("0016", .info, "no math face declared; the engine picked one and says which")
  | .N0018 => ("0018", .info, "math alphabet glyph missing everywhere; a stand-in letter sets, the styling difference named")
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
  | .W0201 => ("0201", .degraded, "measure outside the readable band")
  | .W0202 => ("0202", .degraded, "heading sets more space below than above")
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
  | .W0328 => ("0328", .degraded, "running content wraps; only its first line is kept")
  | .W0329 => ("0329", .config, "reserved layout-only construct skipped; no content is affected")
  | .W0330 => ("0330", .degraded, "declared page with a defaulted ink is illegible (WCAG 2.2)")
  | .W0331 => ("0331", .degraded, "declared marker not expressible in this backend; default substituted")
  | .W0332 => ("0332", .degraded, "footer mixes the frame and physical page sequences undeclared")
  | .W0333 => ("0333", .degraded, "band slots collide; the lower-priority slot is painted over")
  | .W0334 => ("0334", .pending, "picture construct outside the rendered subset; not drawn")
  | .W0335 => ("0335", .degraded, "picture larger than the text area; it may overrun the page")
  | .W0337 => ("0337", .degraded, "table row disagrees with its column spec; padded to the grid")
  | .W0338 => ("0338", .degraded, "table is wider than the measure")
  | .W0358 => ("0358", .degraded, "a float taller than the text block overruns its page")
  | .W0340 => ("0340", .config, "a declaration in the document body is ignored")
  | .W0341 => ("0341", .degraded, "an unknown command's [...] options went with it, never onto the page")
  | .W0342 => ("0342", .degraded, "a definition shadows a palette role; the role is frozen where it is used")
  | .W0343 => ("0343", .config, "one setting is given two different values; the later declaration wins")
  | .W0345 => ("0345", .degraded, "a themed element's resolved colour pairing is illegible (WCAG 2.2)")
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
  | .W0364 => ("0364", .degraded, "an unresolved data path; nothing renders in its place")
  | .E0365 => ("0365", .dropped, "\\data file not found; its records are absent")
  | .W0366 => ("0366", .degraded, "a named font weight is not installed; the nearest installed weight substitutes")
  | .N0021 => ("0021", .info, "header and footer gaps differ as declared; equal gaps are the default")

def DiagCode.digits (c : DiagCode) : String := c.spec.1

def DiagCode.loss (c : DiagCode) : Loss := c.spec.2.1

def DiagCode.meaning (c : DiagCode) : String := c.spec.2.2

/-- The one place a code's printed name is spelled: the class letter comes
from the declared loss, the digits from the registry. A code whose letter
disagrees with its severity cannot be written. -/
def DiagCode.code (c : DiagCode) : String :=
  String.singleton c.loss.letter ++ c.digits

/-- The rendered prefix agrees with the severity: the letter inside
`error[E0333]` is the severity's own letter, for every code. `error[W0307]`
was real output once; this statement is what made it unrepresentable. -/
theorem DiagCode.code_letter (c : DiagCode) :
    c.code.front = c.loss.severity.letter := by
  cases c <;> rfl

/-- How many codes the registry holds: the one number a new code bumps.
`all_complete` makes an undercount a build failure; `all_nodup` an
overcount (`ofNat` clamps out of range, so an overcount duplicates the
last constructor). -/
def DiagCode.count : Nat := 138

/-- Every code, for the registry checks in Tests.lean — derived from the
type through the `ofNat` that `deriving DecidableEq` synthesises, never
hand-maintained: constructor declaration order, complete and duplicate-free
by the two theorems below, so the list cannot drift from the inductive. -/
def DiagCode.all : List DiagCode :=
  (List.range DiagCode.count).map DiagCode.ofNat

theorem DiagCode.all_complete (c : DiagCode) : DiagCode.all.contains c := by
  cases c <;> rfl

theorem DiagCode.all_nodup : DiagCode.all.Nodup := by decide +kernel

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

/-- The whole rendered prefix is one declaration: the severity label and the
code letter of a constructed diagnostic both come from the code's `Loss`,
so `error[W…]` and `warning[E…]` cannot be constructed. -/
theorem Diag.of_code_letter (c : DiagCode) (message : String) (span : Option Span)
    (help : Option String) :
    (Diag.of c message span help).code.front =
      (Diag.of c message span help).severity.letter :=
  c.code_letter

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
def Diag.accept (allowed : Array String) (allowAll : Bool) (d : Diag) : Diag × Bool :=
  if d.severity != .note && (allowAll || allowed.contains d.code) then
    ({ d with severity := .note }, true)
  else (d, false)

/-- The spliced-`.sty` demotion: a TeX internal the engine correctly
refuses inside a style file the author did not write is per-line correct
and per-line unactionable — "'\\z@' is unknown" helps nobody holding only
their own document. The diagnostic keeps its code and message but is
delivered as a note (listed under `-v`), and N0020's "TeX internals
refused" count carries it at default verbosity. The severity write lives
here beside `Diag.accept`, the other policy door: severity is a function
of policy declared in this module, never of a call site. -/
def Diag.demote (d : Diag) : Diag := { d with severity := .note }

/-- One phase's diagnostics resolved against the document's acceptance,
with the counts the driver's exit contract reads: errors and warnings are
counted after acceptance, so an accepted loss is neither. -/
structure Resolution where
  diags : Array Diag := #[]
  fired : Array String := #[]
  accepted : Array String := #[]
  errors : Nat := 0
  warnings : Nat := 0
  deriving Repr, BEq

def Diag.resolveAll (allowed : Array String) (allowAll : Bool)
    (ds : Array Diag) : Resolution := Id.run do
  let mut r : Resolution := {}
  for d0 in ds do
    let (d, acc) := Diag.accept allowed allowAll d0
    r := { r with
      diags := r.diags.push d
      fired := r.fired.push d.code
      accepted := if acc then r.accepted.push d.code else r.accepted
      errors := r.errors + (if d.severity == .error then 1 else 0)
      warnings := r.warnings + (if d.severity == .warning then 1 else 0) }
  return r

/-- The `\allow` entries no emitted diagnostic ever matched: each is stale
acceptance the document no longer needs, and warning about it is one of the
hatch's teeth — an allow that silences nothing today may silence something
real tomorrow. -/
def Diag.unfired (allowed : Array String) (fired : Array String) : Array String :=
  allowed.filter (!fired.contains ·)

end LeanTex.Core
