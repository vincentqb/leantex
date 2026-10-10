module

public import LeanTex.Core.Diag
public import LeanTex.Core.FontDb
public import LeanTex.Core.PdfWriteContract
public import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.Args
import LeanTex.Core.PdfRead

/-! The driver's diagnostics, as pure builders: every message the CLI can
emit for a file, font, or image the host failed to provide is constructed
here, IO-free, so the registry golden and the message lint in Tests.lean
reach the same text the user sees. Driver.lean supplies the arguments; a
message written inline in the driver would be invisible to both. -/

namespace LeanTex.Cli.DriverDiag

open LeanTex.Core

/-- Supply the first executed image request only when the producer has no
location of its own. Missing provenance remains absent. -/
public def atImageRequest (imageSpans : Array (String × Span)) (src : String) (d : Diag) : Diag :=
  { d with span := d.span <|> (imageSpans.find? (·.1 == src)).map (·.2) }

/-- A producer's source evidence preserves its complete diagnostic record,
including macro ancestry, accepted loss and census count. -/
public theorem atImageRequest_located_exact (imageSpans : Array (String × Span))
    (src : String) (d : Diag) (span : Span) :
    atImageRequest imageSpans src { d with span := some span } = { d with span := some span } := by
  rfl

/-- E0001: the input file itself could not be read. -/
public def unreadableInput (file err : String) : Diag :=
  Diag.of .E0001 s!"cannot read '{file}': {err}"

/-- E0004: an artifact the build made could not be written where it was
asked for; `err` is the system's reason. The other artifacts are written. -/
public def outputUnwritable (path err : String) : Diag :=
  Diag.of .E0004 s!"cannot write '{path}': {err}"
    (help := "choose a destination this user can write with -o, or the markdown twin's with \\output{ md = ... }")
    (subject := some path)

/-- E0006: `-o` names a file whose extension names no format the engine
writes, so nothing is built; the help lists the extensions `emitOfPath`
reads (`Emit.all`). -/
public def outputFormatUnknown (name : String) : Diag :=
  Diag.of .E0006 s!"cannot tell the output format of '{name}'"
    (help := s!"name an output file ending in {Emit.extensions} with -o, or a directory ending in '/'")
    (subject := some name)

/-- E0003: distinct artifacts would overwrite the same file. -/
public def outputPathsConflict (detail : String) : Diag :=
  Diag.of .E0003 s!"cannot publish output: {detail}"
    (help := "choose separate files with -o and \\output{ md = ... }; use destinations without hard links")

/-- E0005: an artifact would be written over one of the build's inputs —
the document, an include, its bibliography, an image, a face, the
stylesheet or icon it declares — so nothing is written. The subject is the
destination. -/
public def outputOverwritesInput : PublicationPaths.Overwrite → Diag
  | .same format dest input => overwrite dest
    s!"the {format} destination '{dest}' is '{input}', one of the build's inputs"
  | .linked format dest input => overwrite dest
    s!"the {format} destination '{dest}' may be a hard link to '{input}', one of the build's inputs"
where
  overwrite (dest detail : String) : Diag :=
    Diag.of .E0005 s!"cannot publish output: {detail}"
      (help := "name another destination with -o, or the markdown twin with \\output{ md = ... }")
      (subject := some dest)

/-- A whole-artifact representation refusal. Aggregate storage limits and
font metadata do not identify a source command, so no span is invented. -/
public def pdfWriteRefused (error : Pdf.WriteError) : Diag :=
  let message := match error with
    | .byteOffset bytes =>
      s!"the PDF body needs {bytes} bytes; offsets must be below {2 ^ 64}"
    | .objectStreamSize bytes =>
      s!"the largest PDF object stream needs {bytes} decoded bytes; the supported limit is {PdfRead.maxDecoded}"
    | .xrefStreamSize bytes =>
      s!"the PDF cross-reference stream needs {bytes} decoded bytes; the supported limit is {PdfRead.maxDecoded}"
    | .objectSpelling id =>
      s!"the PDF object {id} contains a spelling the writer cannot represent"
    | .inkRaster page =>
      s!"a picture on page {page + 1} paints a raster image the PDF writer cannot place"
  let split := "split the document into smaller files and compile each with `leantex <file>.tex`"
  let help := match error with
    | .objectSpelling _ =>
      "use nonempty Latin-1 font and PDF resource names, such as 'ExampleFont'"
    | .objectStreamSize _ => "objects that index the whole document grow with it: " ++ split
    | .byteOffset _ | .xrefStreamSize _ => split
    | .inkRaster _ => "draw the picture without an embedded raster, or include the image with \\includegraphics"
  Diag.of .E0607 message
    (help := help)

/-- E0402: `LEANTEX_FONT` names a file that does not parse as a font. -/
public def envFontUnusable (path err : String) : Diag :=
  Diag.of .E0402 s!"cannot use LEANTEX_FONT '{path}': {err}"

/-- E0402: `LEANTEX_FONT` names a file that is not there. -/
public def envFontMissing (path : String) : Diag :=
  Diag.of .E0402 s!"LEANTEX_FONT '{path}' does not exist"

/-- E0401: the scan produced nothing usable at all. -/
public def noFont : Diag :=
  Diag.of .E0401 "no usable font found"
    (help := "install any TrueType/OpenType font, pass --font-dir, or set LEANTEX_FONT")

/-- W0008: the document's `\fonts{ dir = ... }` is not a directory. -/
public def fontsDirMissing (decl resolved : String) : Diag :=
  Diag.of .W0008 s!"'\\fonts' dir '{decl}' is not a directory ({resolved}); looking elsewhere"

/-- E0403: a named family is not installed; `near` are the closest installed
names, `installed` the family count when nothing is close. -/
public def familyMissing (family : String) (near : List String) (installed : Nat) : Diag :=
  let hint := if near.isEmpty then s!"{installed} families are installed"
    else s!"did you mean: {String.intercalate ", " near}?"
  Diag.of .E0403 s!"no installed font family named '{family}'"
    (help := s!"{hint} — `leantex fonts` lists every family")

/-- E0404: a font file that exists but does not parse. -/
public def fontFileUnusable (path err : String) : Diag :=
  Diag.of .E0404 s!"cannot use '{path}': {err}"

/-- W0366: a name asked for a weight the family does not ship; the nearest
installed weight substitutes, both weights named. -/
public def weightSubstituted (asked : String) (requested : Nat) (face : FontDb.Face) : Diag :=
  Diag.of .W0366
    (s!"'{asked}' asks for a weight that is not installed; " ++
      s!"'{face.family} {face.subfamily}' is the nearest")
    (detail := some s!"weight {requested} asked, weight {face.weight} the nearest")
    (help := "install the named weight, or name the face to use \
(\\fonts{ sans.upright = \"...\" } and siblings)")

/-- **W0390: a family slot the document declared nothing for, set in a face
that is not of its kind.** A distinct axis from W0006 and W0366, which is
why it is a distinct code. Those two are within a family the document
named: a variant missing (W0006) or a weight missing (W0366), with "install
the face" as the remedy. This is the family slot itself never named: its
remedy is a declaration — `\fonts{ mono = "..." }` — or, for the typewriter
slot, whose default is a monospace served at its upright corners
(`FontDb.monoPick`) — a platform monospace (`FontDb.monoDefaults`), or for a
tex document lualatex's Latin Modern Mono — one of those families installed
with its bold and both its italics or neither (a family holding one italic
of the two is passed over), or put in its font directory by a document that
ships its fonts, which its default reads before the host's. A markdown
source can declare nothing, so its help offers no declaration.
One code, one meaning, and `\allow{W0390}` accepts this loss without also
accepting every future bold substitution.

`key` is the `\fonts` key that would declare the slot, `runs` the runs the
loss is about, `served` what set them — the body face, or the body family
where the text is set in another — and `note` what is honestly known about
the substitute. `only` names the artifact that lost when not every artifact
the build emits carries the face: a PDF beside a page under its own
stylesheet. The substitute face is not named: which family fills an
undeclared slot is the host's answer, and a message that varies by host
cannot be witnessed. The subject is the slot, so the loss is counted once
however many runs set it. -/
public def slotCollapsed (key runs served note : String) (only : Option String)
    (declarable : Bool := true) (shipsFonts : Bool := false) : Diag :=
  let whereLost := match only with
    | some a => s!"in {a}, "
    | none => ""
  let declare := s!"\\fonts\{ {key} = \"<family>\" }"
  let families := match FontDb.monoDefaults.reverse with
    | last :: rest@(_ :: _) => String.intercalate ", " rest.reverse ++ " or " ++ last
    | _ => String.intercalate ", " FontDb.monoDefaults
  -- A tex document's default reads lualatex's own typewriter shapes too
  -- (`FontDb.latinModernMonoServed`), which every TeX distribution installs.
  let listed := if declarable then s!"Latin Modern Mono, {families}" else families
  let declared := if declarable then s!", or declare one: {declare}" else ""
  let help := if key == "mono" then
      if shipsFonts then
        s!"install one of {listed}, its bold and both or no italics, or put it in the document's \
font directory{declared}"
      else s!"install one of {listed}, its bold and both or no italics{declared}; `leantex fonts` \
lists the installed families"
    else s!"{declare} gives the slot its own face; `leantex fonts` lists the installed families"
  Diag.of .W0390
    s!"nothing declares a '{key}' family; {whereLost}{runs} set in {served}, {note}"
    (subject := some s!"slot:{key}") (help := help)

/-- **N0031: the engine's typewriter default has no italic face.** A
default holding no italic — a listed monospace served at its upright
corners (`FontDb.servesMono`), or Latin Modern Mono without its italic files
(`FontDb.latinModernMonoServed`) — fills an undeclared slot; its italic
corners set upright in it, unslanted — both backends never fake a slant —
named once per build where the document sets italic code, rather than as a
substitution warning per corner (W0006), which is about a family the
document named. `declarable` is whether the source can declare a face;
`own` whether the family is one the document ships, whose italic corners
are read from its own faces alone, so what it lacks is in its font
directory, whatever the host holds. A family whose project ships no italic
at all (`FontDb.monoUprightOnly`) has none to install or put there, so its
note offers the declaration alone, and none where the source can declare
nothing. -/
public def monoUpright (family : String) (declarable : Bool := true) (own : Bool := false) : Diag :=
  let declare := "declare a typewriter family that has them: \\fonts{ mono = \"<family>\" }"
  let remedy := if own then "put the family's italic faces in the document's font directory"
    else "install the family's italic faces"
  let shipsNone := FontDb.monoUprightOnly.contains family
  Diag.of .N0031
    (if own then s!"'{family}' in the document's font directory has no italic face; italic code \
sets upright in it"
      else s!"'{family}' has no italic face; italic code sets upright in it")
    (subject := some "slot:mono:italic")
    (help := if shipsNone then (if declarable then some declare else none)
      else if declarable then some s!"{remedy}, or {declare}" else some remedy)

/-- The two substitution codes off one resolution result: a missing
variant is W0006, a missing weight W0366 — the one door
`FontDb.Substituted` is rendered through. -/
public def substituted : FontDb.Substituted → Diag
  | .variant msg => Diag.of .W0006 msg
  | .weight asked requested face => weightSubstituted asked requested face

/-- W0011: the declared math face has no OpenType MATH table. -/
public def mathFaceNoTable (family path : String) : Diag :=
  Diag.of .W0011
    s!"'{family}' ({path}) has no OpenType MATH table; math is set as plain text"
    (help := "\\fonts{ math = \"STIX Two Math\" } names a math face; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and the body family's designed
companion is installed, so the engine set math in it. -/
public def mathFaceCompanion (mathFamily bodyFamily : String) : Diag :=
  Diag.of .N0016
    s!"math is set in '{mathFamily}', the designed companion of '{bodyFamily}'"
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and no companion is installed, so the
engine set math in the first installed face with an OpenType MATH table. -/
public def mathFaceFirst (mathFamily : String) : Diag :=
  Diag.of .N0016
    s!"math is set in '{mathFamily}', the first installed face with an \
OpenType MATH table"
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- W0379: a picture outside the rendered subset states a boundary request,
and no tool on this machine can fulfil it — nothing pinned is runnable and
the cache holds no earlier render. The placeholder box ships; one per
picture, at its span, so the census gate can match each to its loss. `why`
is how the tool's version question ended, the detail of a message that says
the version was not read, so a tool that is installed but did not answer, or
could not be asked, is not reported as missing. -/
public def boundaryToolUnavailable (tool : String) (span : Option Span := none)
    (why : String := "") : Diag :=
  Diag.of .W0379
    (if why.isEmpty then "no boundary tool is available for this picture outside the rendered subset"
      else s!"no boundary tool is available for this picture: {tool}'s version was not read")
    span
    (detail := if why.isEmpty then none else some why)
    (help := s!"install {tool} if it is missing, or \\pictures\{ tool = none } accepts the \
placeholder; a warm cache needs no tool")
    (recovery := some (.replacedBy "a placeholder box"))

/-- **W0382: a boundary render that failed ships its placeholder.** A
picture the rendered subset draws nothing of has nothing to fall back to,
so its place on the page is the placeholder box an image that did not load
leaves — the box marks it, the loss is named here once, under the picture's
source, and the run goes on to write both artifacts, the HTML page holding
the labelled placeholder `Boundary.markFaceless` gives a picture with no
face. A picture the subset draws in part never reaches this code on an
answer: its request is withdrawn and the subset's
drawing ships, named by W0419 (`Boundary.withdraw`). `logTail` is the tool's
own last words, `span` where the picture stands and `src` its image source.
The code once failed the run as a dropped loss, so one picture the tool
could not draw cost the whole document. -/
public def boundaryFailed (tool logTail src : String) (span : Option Span := none) : Diag :=
  Diag.of .W0382
    s!"'{tool}' drew nothing for this picture; a placeholder box marks its place"
    span
    (help := if logTail.isEmpty then
        s!"{tool}'s log says nothing usable; \\allow\{W0382} accepts the placeholder"
      else s!"{tool} says: {logTail}")
    (subject := some src)
    (recovery := some (.replacedBy "a placeholder box"))

/-- **W0382, for an attempt that never finished.** The tool was asked and
reached no answer — a budget kill, a spawn that raised, a nonzero exit that
left no log (`PicCache.outcome`) — which is a fact about the machine, not
the request: nothing is remembered (`ConvCache.inconclusive_retried_exact`), and
nothing is withdrawn to the rendered subset's drawing
(`Boundary.withdrawStep_unfinished_exact`), so the page carries the
placeholder a failed render leaves, never a different drawing. `why` is how
the attempt ended, and a rebuild asks again. -/
public def boundaryUnfinished (tool why src : String) (span : Option Span := none) : Diag :=
  Diag.of .W0382
    s!"'{tool}' did not finish this picture; a placeholder box marks its place"
    span
    (help := s!"{why}; nothing is remembered, so a rebuild asks {tool} again; \
\\allow\{W0382} accepts the placeholder")
    (subject := some src)
    (recovery := some (.replacedBy "a placeholder box"))

/-- The help of a withdrawn picture's one line (W0419, which
`Boundary.fold` states with every construct the rendered subset leaves
out): why the boundary drew nothing, in the tool's own last words where it
ran (`said`), or that no tool was there to ask. -/
public def withdrawnHelp (tool : String) (said : Option String) : String :=
  let direct := "\\pictures{ tool = none } draws every picture this way, asking no tool"
  match said with
  | some w =>
    if w.isEmpty then s!"{tool} drew nothing and its log says nothing usable; " ++ direct
    else s!"{tool} drew nothing and says: {w} — fix what {tool} reports, or " ++ direct
  | none => s!"install {tool} to draw it whole, and a warm cache needs no tool; " ++ direct

/-- The help of the line that names a withdrawn picture standing in a line
of text, which the rendered subset never draws: why the boundary drew
nothing there, and where the subset would draw it. -/
public def withdrawnInlineHelp (tool : String) (said : Option String) : String :=
  let block := "standing in a paragraph of its own, the rendered subset draws it"
  match said with
  | some w =>
    if w.isEmpty then s!"{tool} drew nothing and its log says nothing usable; " ++ block
    else s!"{tool} drew nothing and says: {w} — " ++ block
  | none => s!"install {tool} to draw it in its line, and a warm cache needs no tool; " ++ block

/-- The help of a declined picture's one line (W0419, `Boundary.foldLines`):
the document's `\pictures{ tool = none }` keeps every picture to the
rendered subset, and without it a boundary tool would draw this one whole. -/
public def declinedHelp : String :=
  "\\pictures{ tool = none } keeps every picture to the rendered subset; without it, \
lualatex draws this one whole"

/-- Why a boundary picture has no checked SVG face for the HTML artifact:
each reason has its own words and its own remedy, so two pictures fold to
one line only where one remedy serves both. -/
public inductive SvgFaceLoss where
  /-- Its text is in a font the engine does not draw, and no converter drew
  it: none was installed, it was interrupted, or its face was refused. -/
  | textless
  /-- As `textless`, the document having declined the converter
  (`\figures{ convert = none }`). -/
  | textlessDeclined
  /-- Its PDF→SVG conversion failed, or the check its SVG must pass did not
  finish, in the tool's words. -/
  | unconverted (why : String)
  /-- The check its SVG must pass finished when it was converted and not when
  the page was published, in the check's words. -/
  | unchecked (why : String)

/-- W0378: a boundary picture has no checked SVG face for the HTML artifact
(`Boundary.htmlFace`), so the page shows the rendered subset's drawing where
the subset draws the picture in part (`Boundary.htmlWithdraw`), and
otherwise a placeholder labelled with the picture's text alternative. One
per picture, under its image source; the tool's words are its detail. -/
public def boundarySvgMissing (src : String) (loss : SvgFaceLoss) : Diag :=
  let (message, detail, help) : String × Option String × String := match loss with
    | .textless =>
      ("this boundary picture has no browser face: its text is in a font the engine does not \
draw, and no converter drew it", none,
        "install poppler's pdftocairo, which draws the picture whole, rebuild if a conversion \
was interrupted, or \\allow{W0378} accepts the loss")
    | .textlessDeclined =>
      ("this boundary picture has no browser face: its text is in a font the engine does not \
draw, and the converter is declined", none,
        "\\figures{ convert = none } declines the converter; without it, pdftocairo draws the \
picture whole, or \\allow{W0378} accepts the loss")
    | .unconverted why =>
      ("this boundary picture has no browser face: its conversion to SVG failed, or the check \
its SVG must pass did not finish", some why,
        "install the tool the reason names (poppler's pdftocairo, libxml2's xmllint, \
librsvg's rsvg-convert), rebuild if it was interrupted, or \\allow{W0378} accepts the loss")
    | .unchecked why =>
      ("this boundary picture has no browser face: the check its SVG must pass did not finish \
when the page was published", some why,
        "rebuild to run the check again, install libxml2's xmllint if the reason says it is \
missing, or \\allow{W0378} accepts the loss")
  Diag.of .W0378 message (subject := some src) (detail := detail) (help := help)
    (output := some .html)

public theorem boundarySvgMissing_subject (src : String) (loss : SvgFaceLoss) :
    (boundarySvgMissing src loss).kind = .W0378 ∧
      (boundarySvgMissing src loss).subject = some src := by
  cases loss <;> simp [boundarySvgMissing, Diag.of_record_exact]

/-- W0605: the declared page icon is an SVG whose check did not finish on
this machine, so the page ships without the icon instead of refusing. -/
public def pageIconOmitted (name why : String) : Diag :=
  Diag.of .W0605
    s!"favicon '{name}' could not be checked for the web page: {why}; \
the page ships without it"
    (help := "install the tool the reason names, rebuild if it was interrupted, or \
\\pdfmeta{ favicon = \"icon.png\" } declares a PNG icon, which needs no tool")
    (subject := some name)
    (output := some .html)

public theorem pageIconOmitted_subject (name why : String) :
    (pageIconOmitted name why).kind = .W0605 ∧ (pageIconOmitted name why).subject = some name := by
  simp [pageIconOmitted, Diag.of_record_exact]

/-- W0393: the external classifier supplied no usable answer. The source
still ships, and the language is the key for counting repeated refusals. -/
public def listingHighlightUnavailable (language reason : String) : Diag :=
  Diag.of .W0393
    s!"cannot highlight '{language}'; the listing is set as plain text"
    (subject := some ("listing-language:" ++ language))
    (help := s!"check `python3 -m pygments -L lexers`, or install Pygments for `python3` ({reason})")

/-- E0606: the page failed the resource-closure check. This names a failed
publication, never an instruction to write the unchecked page anyway. -/
public def htmlResourceUnavailable (detail : String) : Diag :=
  Diag.of .E0606 s!"cannot publish self-contained HTML: {detail}"
    (help := "use readable local image, font, stylesheet and math renderer files; remove CSS `@import` and external `url(...)` dependencies")
    (output := some .html)

/-- E0502: an included source file is not there; its content is absent. -/
public def inputMissing (name : String) (span : Option Span) (command : String := "input") : Diag :=
  Diag.of .E0502 s!"'\\{command}' file '{name}' is not there; its content is absent" span
    (help := "\\allow{E0502} accepts the loss")

/-- E0503: a `.bib` file named by `\bibliography` is not there; the
reference list stays empty and every citation shows `?`. The `\input`
shape (E0502), its own code: one code, one meaning. -/
public def bibMissing (name looked : String) (span : Option Span) : Diag :=
  Diag.of .E0503 s!"'\\bibliography' file '{name}' is not there; the reference list is empty"
    span (help := s!"looked at: {looked}; \\allow\{E0503} accepts the loss")

/-- W0424: one `.bib` file of several a bibliography names is not there;
the list holds the entries of the files that are, and every citation of
an entry only the missing file holds shows `?`, named (W0351). -/
public def bibMissingAmong (name looked : String) (span : Option Span) : Diag :=
  Diag.of .W0424 s!"'\\bibliography' file '{name}' is not there; the reference list holds the \
entries of the other files" span
    (help := s!"put the file at {looked}, or drop '{name}' from the list of files")
    (subject := some ("bibfile:" ++ name))

/-- E0365: a `.bib` file named by `\data` is not there; its records are
absent, and every read of them stays unresolved. The `\input` shape
(E0502), its own code: one code, one meaning. -/
public def dataMissing (name looked : String) (span : Option Span) : Diag :=
  Diag.of .E0365 s!"'\\data' file '{name}' is not there; its records are absent"
    span (help := s!"looked at: {looked}; \\allow\{E0365} accepts the loss")

/-- E0501: the `\input` stack never emptied. -/
public def inputTooDeep : Diag :=
  Diag.of .E0501 "'\\input' nesting deeper than 8 files; is a file including itself?"

/-- W0013: an `\allow` entry no diagnostic matched. -/
public def allowUnfired (code : String) : Diag :=
  Diag.of .W0013 s!"'\\allow' lists {code}, which never fired"
    (help := "the document no longer needs it; drop the entry from \\allow")

end LeanTex.Cli.DriverDiag
