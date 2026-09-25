import LeanTex.Core.Diag
import LeanTex.Core.FontDb

/-! The driver's diagnostics, as pure builders: every message the CLI can
emit for a file, font, or image the host failed to provide is constructed
here, IO-free, so the registry golden and the message lint in Tests.lean
reach the same text the user sees. Main.lean supplies the arguments; a
message written inline in the driver would be invisible to both. -/

namespace LeanTex.Cli.DriverDiag

open LeanTex.Core

/-- E0001: the input file itself could not be read. -/
def unreadableInput (file err : String) : Diag :=
  Diag.of .E0001 s!"cannot read '{file}': {err}"

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

/-- **W0390: a family slot the document declared nothing for, resolved onto
the body face.** A distinct axis from W0006 and W0366, which is why it is a
distinct code. Those two are within a family the document named: a variant
missing (W0006) or a weight missing (W0366), with "install the face" as the
remedy. This is the family slot itself never named, and the remedy is a
declaration — `\fonts{ mono = "..." }` — not an install. One code, one
meaning, and `\allow{W0390}` accepts this loss without also accepting every
future bold substitution.

`key` is the `\fonts` key that would declare the slot, `runs` the runs the
loss is about, and `note` what is honestly known about the substitute. The
substitute face is not named: which family fills an undeclared slot is the
host's answer, and a message that varies by host cannot be witnessed. The
subject is the slot, so the loss is counted once however many runs set it. -/
def slotCollapsed (key runs note : String) : Diag :=
  Diag.of .W0390
    s!"nothing declares a '{key}' family; {runs} set in the body face, {note}"
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
    s!"no boundary tool is available for this picture outside the rendered \
subset; a placeholder box marks its place"
    span
    (help := s!"install {tool}, or \\pictures\{ tool = none } accepts the \
placeholder; a warm cache needs no tool")

/-- **E0382: a boundary render that failed is a dropped loss, not a
degraded one.** `degraded` is declared as *the reader sees "something
stands here"* — a substituted face, source text, a box carrying its
code — and that is the one thing a failed boundary picture does not do:
the box it leaves is empty and unlabelled, so the page reads as
intentional while a whole diagram is gone. The native subset is tried
first now, so a picture reaches the boundary only when the engine drew
nothing of it: no part of it was drawn, so there is nothing to fall back
to, and nothing honest to put in the box that the engine did not invent. So
the loss is loud where it can be loud without inventing ink — the run fails,
and no artifact is written, which is the engine's standing contract for a
dropped loss. `\allow{E0382}` is the declared door for a document that
accepts the empty box. `logTail` is the tool's own last words, and `span`
is where the picture stands. -/
def boundaryFailed (tool : String) (logTail : String) (span : Option Span := none) : Diag :=
  Diag.of .E0382
    s!"'{tool}' drew nothing for this picture; the page would carry an empty box"
    span
    (help := if logTail.isEmpty then
        s!"{tool}'s log says nothing usable; \\allow\{E0382} accepts the empty box"
      else s!"{tool} says: {logTail}")

/-- W0378: the PDF→SVG converter for the HTML artifact is not runnable;
the page shows each picture's text alternative instead. -/
def boundarySvgMissing (err : String) : Diag :=
  Diag.of .W0378
    s!"cannot run 'pdftocairo' to convert boundary pictures for the HTML \
artifact: {err}"
    (help := "install poppler's pdftocairo, or \\allow{W0378} accepts the \
loss; the PDF artifact is unaffected")

/-- E0502: an `\input` file is not there; its content is absent. -/
def inputMissing (name : String) (span : Option Span) : Diag :=
  Diag.of .E0502 s!"'\\input' file '{name}' is not there; its content is absent" span
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
