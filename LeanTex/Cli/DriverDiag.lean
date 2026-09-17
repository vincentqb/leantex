import LeanTex.Core.Diag

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
  Diag.of .W0008 s!"\\fonts dir '{decl}' is not a directory ({resolved}); looking elsewhere"

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

/-- W0011: the declared math face has no OpenType MATH table. -/
def mathFaceNoTable (family path : String) : Diag :=
  Diag.of .W0011
    s!"'{family}' ({path}) has no OpenType MATH table; math is set as plain text"
    (help := "name a math face (Latin Modern Math, STIX Two Math, \
TeX Gyre Pagella Math, Fira Math, ...) — its MATH table is where the engine \
reads math spacing from")

/-- W0601: the image file exists but reading it failed. -/
def imageUnreadable (src err : String) : Diag :=
  Diag.of .W0601 s!"cannot read image '{src}': {err}"
    (help := "a placeholder box of the requested size is placed")

/-- W0601: no file answers the image source. -/
def imageMissing (src looked : String) : Diag :=
  Diag.of .W0601 s!"image file not found: '{src}'"
    (help := s!"looked at {looked} (also with .png/.jpg/.jpeg added); \
a placeholder box of the requested size is placed")

/-- W0602: the image bytes are not a format the engine embeds. -/
def imageUndecodable (src err : String) : Diag :=
  Diag.of .W0602 s!"cannot use image '{src}': {err}"
    (help := "PNG and JPEG embed natively; a placeholder box is placed")

/-- E0502: an `\input` file is not there; its content is absent. -/
def inputMissing (name : String) (span : Option Span) : Diag :=
  Diag.of .E0502 s!"\\input file not found: '{name}'; skipped" span
    (help := "an entire file's content is absent; \\allow{E0502} accepts the loss")

/-- E0501: the `\input` stack never emptied. -/
def inputTooDeep : Diag :=
  Diag.of .E0501 "\\input nesting deeper than 8 files; is a file including itself?"

/-- W0013: an `\allow` entry no diagnostic matched. -/
def allowUnfired (code : String) : Diag :=
  Diag.of .W0013 s!"\\allow'd code {code} never fired"
    (help := "the document no longer needs to accept it; drop it from \\allow")

end LeanTex.Cli.DriverDiag
