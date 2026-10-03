import LeanTex.Core.Diag
import LeanTex.Core.FontDb

/-! The driver's diagnostics, as pure builders: every message the CLI can
emit for a file, font, or image the host failed to provide is constructed
here, IO-free, so the registry golden and the message lint in Tests.lean
reach the same text the user sees. Main.lean supplies the arguments; a
message written inline in the driver would be invisible to both. -/

namespace LeanTex.Cli.DriverDiag

open LeanTex.Core

/-- Supply the first executed image request only when the producer has no
location of its own. Missing provenance remains absent. -/
def atImageRequest (imageSpans : Array (String × Span)) (src : String) (d : Diag) : Diag :=
  { d with span := d.span <|> (imageSpans.find? (·.1 == src)).map (·.2) }

/-- A producer's source evidence preserves its complete diagnostic record,
including macro ancestry, accepted loss and census count. -/
theorem atImageRequest_located_exact (imageSpans : Array (String × Span))
    (src : String) (d : Diag) (span : Span) :
    atImageRequest imageSpans src { d with span := some span } = { d with span := some span } := rfl

/-- E0001: the input file itself could not be read. -/
def unreadableInput (file err : String) : Diag :=
  Diag.of .E0001 s!"cannot read '{file}': {err}"

/-- E0003: distinct artifacts would overwrite the same file. -/
def outputPathsConflict (detail : String) : Diag :=
  Diag.of .E0003 s!"cannot publish output: {detail}"
    (help := "choose separate files with -o and \\output{ md = ... }; use destinations without hard links")

/-- E0402: `LEANTEX_FONT` names a file that does not parse as a font. -/
def envFontUnusable (path err : String) : Diag :=
  Diag.of .E0402 s!"cannot use LEANTEX_FONT '{path}': {err}"

/-- E0402: `LEANTEX_FONT` names a file that is not there. -/
def envFontMissing (path : String) : Diag :=
  Diag.of .E0402 s!"LEANTEX_FONT '{path}' does not exist"

/-- E0401: the scan produced nothing usable at all. -/
def noFont : Diag :=
  Diag.of .E0401 "no usable font found"
    (help := "install any TrueType/OpenType font, pass --font-dir, or set LEANTEX_FONT")

/-- W0008: the document's `\fonts{ dir = ... }` is not a directory. -/
def fontsDirMissing (decl resolved : String) : Diag :=
  Diag.of .W0008 s!"'\\fonts' dir '{decl}' is not a directory ({resolved}); looking elsewhere"

/-- E0403: a named family is not installed; `near` are the closest installed
names, `installed` the family count when nothing is close. -/
def familyMissing (family : String) (near : List String) (installed : Nat) : Diag :=
  let hint := if near.isEmpty then s!"{installed} families are installed"
    else s!"did you mean: {String.intercalate ", " near}?"
  Diag.of .E0403 s!"no installed font family named '{family}'"
    (help := s!"{hint} — `leantex fonts` lists every family")

/-- E0404: a font file that exists but does not parse. -/
def fontFileUnusable (path err : String) : Diag :=
  Diag.of .E0404 s!"cannot use '{path}': {err}"

/-- W0366: a name asked for a weight the family does not ship; the nearest
installed weight substitutes, both weights named. -/
def weightSubstituted (asked : String) (requested : Nat) (face : FontDb.Face) : Diag :=
  Diag.of .W0366
    (s!"'{asked}' asks for weight {requested}, which is not installed; " ++
      s!"'{face.family} {face.subfamily}' (weight {face.weight}) is the nearest")
    (help := "install the named weight, or name the face to use \
(\\fonts{ sans.upright = \"...\" } and siblings)")

/-- **W0390: a family slot the document declared nothing for, set in a face
that is not of its kind.** A distinct axis from W0006 and W0366, which is
why it is a distinct code. Those two are within a family the document
named: a variant missing (W0006) or a weight missing (W0366), with "install
the face" as the remedy. This is the family slot itself never named, and
the remedy is a declaration — `\fonts{ mono = "..." }` — not an install.
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
def slotCollapsed (key runs served note : String) (only : Option String) : Diag :=
  let whereLost := match only with
    | some a => s!"in {a}, "
    | none => ""
  Diag.of .W0390
    s!"nothing declares a '{key}' family; {whereLost}{runs} set in {served}, {note}"
    (subject := some s!"slot:{key}")
    (help := s!"\\fonts\{ {key} = \"<family>\" } gives the slot its own face; \
`leantex fonts` lists the installed families")

/-- The two substitution codes off one resolution result: a missing
variant is W0006, a missing weight W0366 — the one door
`FontDb.Substituted` is rendered through. -/
def substituted : FontDb.Substituted → Diag
  | .variant msg => Diag.of .W0006 msg
  | .weight asked requested face => weightSubstituted asked requested face

/-- W0011: the declared math face has no OpenType MATH table. -/
def mathFaceNoTable (family path : String) : Diag :=
  Diag.of .W0011
    s!"'{family}' ({path}) has no OpenType MATH table; math is set as plain text"
    (help := "\\fonts{ math = \"STIX Two Math\" } names a math face; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and the body family's designed
companion is installed, so the engine set math in it. -/
def mathFaceCompanion (mathFamily bodyFamily : String) : Diag :=
  Diag.of .N0016
    s!"math is set in '{mathFamily}', the designed companion of '{bodyFamily}'"
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and no companion is installed, so the
engine set math in the first installed face with an OpenType MATH table. -/
def mathFaceFirst (mathFamily : String) : Diag :=
  Diag.of .N0016
    s!"math is set in '{mathFamily}', the first installed face with an \
OpenType MATH table"
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- W0379: a picture outside the rendered subset states a boundary request,
and no tool on this machine can fulfil it — nothing pinned is runnable and
the cache holds no earlier render. The placeholder box ships; one per
picture, at its span, so the census gate can match each to its loss. -/
def boundaryToolUnavailable (tool : String) (span : Option Span := none) : Diag :=
  Diag.of .W0379
    "no boundary tool is available for this picture outside the rendered subset"
    span
    (help := s!"install {tool}, or \\pictures\{ tool = none } accepts the \
placeholder; a warm cache needs no tool")
    (recovery := some (.replacedBy "a placeholder box"))

/-- **E0382: a boundary render that failed is a dropped loss, not a
degraded one** — where nothing else can stand in its place. `degraded` is
declared as *the reader sees "something stands here"* — a substituted face,
source text, a box carrying its code — and that is the one thing a failed
boundary picture does not do: the box it leaves is empty and unlabelled, so
the page reads as intentional while a whole diagram is gone. A picture the
rendered subset draws in part never reaches this code on an answer: its
request is withdrawn and the subset's drawing ships (N0419,
`Boundary.withdraw`). So E0382 is left for a picture the engine drew nothing
of, where there is nothing to fall back to and nothing honest to put in the
box that the engine did not invent, and for an attempt that never finished
(`boundaryUnfinished`). So the loss is loud where it can be loud without
inventing ink — the run fails, and no artifact is written, which is the
engine's standing contract for a dropped loss. `\allow{E0382}` is the
declared door for a document that accepts the empty box. `logTail` is the
tool's own last words, and `span` is where the picture stands. -/
def boundaryFailed (tool : String) (logTail : String) (span : Option Span := none) : Diag :=
  Diag.of .E0382
    s!"'{tool}' drew nothing for this picture; the page would carry an empty box"
    span
    (help := if logTail.isEmpty then
        s!"{tool}'s log says nothing usable; \\allow\{E0382} accepts the empty box"
      else s!"{tool} says: {logTail}")

/-- **E0382, for an attempt that never finished.** The tool was asked and
reached no answer — a budget kill, a spawn that raised, a nonzero exit that
left no log (`PicCache.outcome`) — which is a fact about the machine, not
the request: nothing is remembered (`PicCache.remembers_verdict_exact`), and
nothing is withdrawn to the rendered subset's drawing
(`Boundary.withdrawStep_unfinished_exact`), so the artifact never changes on
it. The run fails as a failed render does, and says so in the machine's
terms: `why` is how the attempt ended, and a rebuild asks again. -/
def boundaryUnfinished (tool why : String) (span : Option Span := none) : Diag :=
  Diag.of .E0382
    s!"'{tool}' did not finish this picture; the page would carry an empty box"
    span
    (help := s!"{why}; nothing is remembered, so a rebuild asks {tool} again; \
\\allow\{E0382} accepts the empty box")

/-- N0419: a boundary request no tool drew, for a picture the rendered
subset draws in part. The request is withdrawn and the subset's drawing
ships, its refusals named beside it exactly as `\pictures{ tool = none }`
names them — so this is a note, not a loss: the losses are those refusals.
`said` is the tool's own last words where it ran and drew nothing, and
absent where no tool ran at all. -/
def boundaryWithdrawn (tool : String) (said : Option String) (src : String)
    (span : Option Span := none) : Diag :=
  let direct := "\\pictures{ tool = none } draws every picture this way, asking no tool"
  Diag.of .N0419
    ((match said with
      | some _ => s!"'{tool}' drew nothing for this picture"
      | none => "no boundary tool drew this picture") ++
      ", so the rendered subset draws it; what the subset leaves out is named beside it")
    span
    (help := some (match said with
      | some w => (if w.isEmpty then s!"{tool}'s log says nothing usable" else s!"{tool} says: {w}") ++
          "; " ++ direct
      | none => s!"install {tool} to draw it whole, and a warm cache needs no tool; " ++ direct))
    (subject := some src)

/-- W0378: the PDF→SVG converter for the HTML artifact is not runnable;
the page shows the rendered subset's drawing of each picture the subset
draws in part (`Boundary.htmlWithdraw`), and every other picture's text
alternative. -/
def boundarySvgMissing (err : String) : Diag :=
  Diag.of .W0378
    s!"cannot run 'pdftocairo' to convert boundary pictures for the HTML \
artifact: {err}"
    (help := "install poppler's pdftocairo, or \\allow{W0378} accepts the \
loss")
    (output := some .html)

/-- W0393: the external classifier supplied no usable answer. The source
still ships, and the language is the key for counting repeated refusals. -/
def listingHighlightUnavailable (language reason : String) : Diag :=
  Diag.of .W0393
    s!"cannot highlight '{language}'; the listing is set as plain text"
    (subject := some ("listing-language:" ++ language))
    (help := s!"check `python3 -m pygments -L lexers`, or install Pygments for `python3` ({reason})")

/-- E0606: the page failed the resource-closure check. This names a failed
publication, never an instruction to write the unchecked page anyway. -/
def htmlResourceUnavailable (detail : String) : Diag :=
  Diag.of .E0606 s!"cannot publish self-contained HTML: {detail}"
    (help := "use readable local image, font and stylesheet files; remove CSS `@import` and external `url(...)` dependencies")
    (output := some .html)

/-- E0502: an included source file is not there; its content is absent. -/
def inputMissing (name : String) (span : Option Span) (command : String := "input") : Diag :=
  Diag.of .E0502 s!"'\\{command}' file '{name}' is not there; its content is absent" span
    (help := "\\allow{E0502} accepts the loss")

/-- E0503: a `.bib` file named by `\bibliography` is not there; the
reference list stays empty and every citation shows `?`. The `\input`
shape (E0502), its own code: one code, one meaning. -/
def bibMissing (name looked : String) (span : Option Span) : Diag :=
  Diag.of .E0503 s!"'\\bibliography' file '{name}' is not there; the reference list is empty"
    span (help := s!"looked at: {looked}; \\allow\{E0503} accepts the loss")

/-- E0365: a `.bib` file named by `\data` is not there; its records are
absent, and every read of them stays unresolved. The `\input` shape
(E0502), its own code: one code, one meaning. -/
def dataMissing (name looked : String) (span : Option Span) : Diag :=
  Diag.of .E0365 s!"'\\data' file '{name}' is not there; its records are absent"
    span (help := s!"looked at: {looked}; \\allow\{E0365} accepts the loss")

/-- E0501: the `\input` stack never emptied. -/
def inputTooDeep : Diag :=
  Diag.of .E0501 "'\\input' nesting deeper than 8 files; is a file including itself?"

/-- W0013: an `\allow` entry no diagnostic matched. -/
def allowUnfired (code : String) : Diag :=
  Diag.of .W0013 s!"'\\allow' lists {code}, which never fired"
    (help := "the document no longer needs it; drop the entry from \\allow")

end LeanTex.Cli.DriverDiag
