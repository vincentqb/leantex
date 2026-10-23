module

public import LeanTex.Core.Diag
public import LeanTex.Core.FontDb
public import LeanTex.Core.PdfWriteContract
public import LeanTex.Cli.PublicationPaths
import LeanTex.Cli.Args
import LeanTex.Core.PdfRead
import LeanTex.Core.TexText

/-! The driver's diagnostics as pure builders, so the registry golden and the message lint
read the text the user sees. -/

namespace LeanTex.Cli.DriverDiag

open LeanTex.Core

/-- Supply the first executed image request's location only when the producer has none. -/
public def atImageRequest (imageSpans : Array (String × Span)) (src : String) (d : Diag) : Diag :=
  { d with span := d.span <|> (imageSpans.find? (·.1 == src)).map (·.2) }

public theorem atImageRequest_located_exact (imageSpans : Array (String × Span))
    (src : String) (d : Diag) (span : Span) :
    atImageRequest imageSpans src { d with span := some span } = { d with span := some span } := by
  rfl

/-- E0001: the input file itself could not be read. -/
public def unreadableInput (file err : String) : Diag :=
  Diag.of .E0001 (Diag.say .E0001 .file file) (detail := some err)

/-- E0004: an artifact could not be written where asked; `err` is the system's reason, and
the other artifacts are written. -/
public def outputUnwritable (path err : String) : Diag :=
  Diag.of .E0004 (Diag.say .E0004 .output path) (detail := some err)
    (help := "choose a destination this user can write with -o, or the markdown twin's with \\output{ md = ... }")
    (subject := some path)

/-- E0006: `-o` names an extension no format writes, so nothing is built. -/
public def outputFormatUnknown (name : String) : Diag :=
  Diag.of .E0006 (Diag.say .E0006 .output name)
    (help := s!"name an output file ending in {Emit.extensions} with -o, or a directory ending in '/'")
    (subject := some name)

/-- E0003: distinct artifacts would overwrite the same file. -/
public def outputPathsConflict (detail : String) : Diag :=
  Diag.of .E0003 (Diag.say .E0003 .output) (detail := some detail)
    (help := "choose separate files with -o and \\output{ md = ... }; use destinations without hard links")

/-- E0005: an artifact would be written over one of the build's inputs, so nothing is
written; the subject is the destination. -/
public def outputOverwritesInput : PublicationPaths.Overwrite → Diag
  | .same format dest input => overwrite dest
    s!"the {format} output is the input '{input}'"
  | .linked format dest input => overwrite dest
    s!"the {format} output may be a hard link to the input '{input}'"
where
  overwrite (dest detail : String) : Diag :=
    Diag.of .E0005 (Diag.say .E0005 .output dest) (detail := some detail)
      (help := "name another destination with -o, or the markdown twin with \\output{ md = ... }")
      (subject := some dest)

/-- A whole-artifact PDF representation refusal, with no span, since no source command is
identified. -/
public def pdfWriteRefused (error : Pdf.WriteError) : Diag :=
  let (message, detail) := match error with
    | .byteOffset bytes =>
      (Diag.say .E0006 .output,
        s!"the PDF body needs {bytes} bytes; offsets stay below {2 ^ 64}")
    | .objectStreamSize bytes =>
      (Diag.say .E0006 .output,
        s!"the largest object stream needs {bytes} decoded bytes; the limit is \
{PdfRead.maxDecoded}")
    | .xrefStreamSize bytes =>
      (Diag.say .E0006 .output,
        s!"the cross-reference stream needs {bytes} decoded bytes; the limit is \
{PdfRead.maxDecoded}")
    | .objectSpelling id =>
      (Diag.say .E0006 .object (Diag.Name.of (toString id)),
        "a spelling the writer cannot represent")
    | .inkRaster page =>
      (Diag.say .E0006 .image,
        s!"a picture on page {page + 1} paints a raster image")
  let split := "split the document into smaller files and compile each with `leantex <file>.tex`"
  let help := match error with
    | .objectSpelling _ =>
      "use nonempty Latin-1 font and PDF resource names, such as 'ExampleFont'"
    | .objectStreamSize _ => "objects that index the whole document grow with it: " ++ split
    | .byteOffset _ | .xrefStreamSize _ => split
    | .inkRaster _ => "draw the picture without an embedded raster, or include the image with \\includegraphics"
  Diag.of .E0006 message
    (help := help) (detail := some detail)

/-- E0402: `LEANTEX_FONT` names a file that does not parse as a font. -/
public def envFontUnusable (path err : String) : Diag :=
  Diag.of .E0402 (Diag.say .E0402 .font path) (detail := some s!"LEANTEX_FONT: {err}")

/-- E0402: `LEANTEX_FONT` names a file that is not there. -/
public def envFontMissing (path : String) : Diag :=
  Diag.of .E0402 (Diag.say .E0402 .font path) (detail := some "LEANTEX_FONT names no file")

/-- E0401: the scan produced nothing usable at all. -/
public def noFont : Diag :=
  Diag.of .E0401 (Diag.say .E0401 .font)
    (help := "install any TrueType/OpenType font, pass --font-dir, or set LEANTEX_FONT")

/-- W0008: the document's `\fonts{ dir = ... }` is not a directory. -/
public def fontsDirMissing (decl resolved : String) : Diag :=
  Diag.of .W0008 (Diag.say .W0008 .directory decl) (detail := some s!"resolves to {resolved}")
    (subject := some "param:\\fonts:dir")

/-- W0390: a named family is not installed, at the declaration naming it; `near` are the closest
installed names, `installed` the family count when nothing is close. -/
public def familyMissing (family : String) (near : List String) (installed : Nat)
    (span : Option Span := none) : Diag :=
  let hint := if near.isEmpty then s!"{installed} families are installed"
    else s!"did you mean: {String.intercalate ", " near}?"
  Diag.of .W0390 (Diag.say .W0390 .family family) span
    (subject := some ("family:" ++ family))
    (help := s!"{hint} — `leantex fonts` lists every family")

/-- E0404: a font file that exists but does not parse. -/
public def fontFileUnusable (path err : String) : Diag :=
  Diag.of .E0404 (Diag.say .E0404 .font path) (detail := some err)

/-- W0006: a name asked for a weight the family does not ship; the nearest
installed weight substitutes, both weights named. -/
public def weightSubstituted (asked : String) (requested : Nat) (face : FontDb.Face) : Diag :=
  Diag.of .W0006
    (Diag.say .W0006 .face s!"{face.family} {face.subfamily}" (some (none, asked)))
    (detail := some s!"weight {requested} asked, weight {face.weight} the nearest")
    (help := "install the named weight, or name the face to use \
(\\fonts{ sans.upright = \"...\" } and siblings)")

/-- W0390: a family slot the document declared nothing for, set in a face not of its kind;
the subject is the slot, and `only` names the artifact that lost when not every artifact
carries the face. -/
public def slotCollapsed (key runs served note : String) (only : Option String)
    (declarable : Bool := true) (shipsFonts : Bool := false) : Diag :=
  let whereLost := match only with
    | some a => s!"in {a}, "
    | none => ""
  let declare := s!"\\fonts\{ {key} = \"<family>\" }"
  let families := match FontDb.monoDefaults.reverse with
    | last :: rest@(_ :: _) => String.intercalate ", " rest.reverse ++ " or " ++ last
    | _ => String.intercalate ", " FontDb.monoDefaults
  -- A tex document's default also reads lualatex's typewriter shapes, which every TeX
  -- distribution installs.
  let listed := if declarable then s!"Latin Modern Mono, {families}" else families
  let declared := if declarable then s!", or declare one: {declare}" else ""
  let help := if key == "mono" then
      if shipsFonts then
        s!"install one of {listed}, its bold and both or no italics, or put it in the document's \
font directory{declared}"
      else s!"install one of {listed}, its bold and both or no italics{declared}; `leantex fonts` \
lists the installed families"
    else s!"{declare} gives the slot its own face; `leantex fonts` lists the installed families"
  Diag.of .W0390 (Diag.say .W0390 .family key)
    (detail := some s!"{whereLost}{runs} set in {served}, {note}")
    (subject := some s!"slot:{key}") (help := help)

/-- N0031: the engine's typewriter default has no italic face, so its italic corners set
upright; `declarable` says whether the source can declare a face, `own` whether the
document ships the family. -/
public def monoUpright (family : String) (declarable : Bool := true) (own : Bool := false) : Diag :=
  let declare := "declare a typewriter family that has them: \\fonts{ mono = \"<family>\" }"
  let remedy := if own then "put the family's italic faces in the document's font directory"
    else "install the family's italic faces"
  let shipsNone := FontDb.monoUprightOnly.contains family
  Diag.of .N0031 (Diag.say .N0031 .face "italic" (some (some .family, family)))
    (detail := if own then some "in the document's font directory" else none)
    (subject := some "slot:mono:italic")
    (help := if shipsNone then (if declarable then some declare else none)
      else if declarable then some s!"{remedy}, or {declare}" else some remedy)

/-- The two substitution codes of one resolution result: a missing variant is W0006, a
missing weight W0006. -/
public def substituted : FontDb.Substituted → Diag
  | .variant asked declared face =>
    Diag.of .W0006 (Diag.say .W0006 .face s!"{face.family} {face.subfamily}" (some (none, asked)))
      (detail := declared.map (s!"'{·}' is not installed"))
  | .weight asked requested face => weightSubstituted asked requested face

/-- W0011: the declared math face has no OpenType MATH table. -/
public def mathFaceNoTable (family path : String) : Diag :=
  Diag.of .W0011 (Diag.say .W0011 .mathFont family)
    (detail := some s!"{path} has no OpenType MATH table")
    (help := "\\fonts{ math = \"STIX Two Math\" } names a math face; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and the body family's designed
companion is installed, so the engine set math in it. -/
public def mathFaceCompanion (mathFamily bodyFamily : String) : Diag :=
  Diag.of .N0016 (Diag.say .N0016 .mathFont mathFamily)
    (detail := some s!"the designed companion of '{bodyFamily}'")
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- N0016: no math face was declared and no companion is installed, so the
engine set math in the first installed face with an OpenType MATH table. -/
public def mathFaceFirst (mathFamily : String) : Diag :=
  Diag.of .N0016 (Diag.say .N0016 .mathFont mathFamily)
    (detail := some "the first installed face with an OpenType MATH table")
    (help := "\\fonts{ math = \"...\" } chooses a face yourself; \
`leantex fonts` lists the installed families")

/-- W0379: no tool on this machine can fulfil a picture's boundary request and the cache
holds no earlier render, so its placeholder ships; `why` is how the version question
ended. -/
public def boundaryToolUnavailable (tool : String) (span : Option Span := none)
    (why : String := "") : Diag :=
  Diag.of .W0379 (Diag.say .W0379 .tool tool) span
    (detail := if why.isEmpty then none else some s!"its version was not read: {why}")
    (help := s!"install {tool} if it is missing, or \\pictures\{ tool = none } accepts the \
placeholder; a warm cache needs no tool")
    (recovery := some (.replacedBy "a placeholder box"))

/-- W0382: a boundary render that failed ships its placeholder, named once under the
picture's source with the tool's last words. -/
public def boundaryFailed (tool logTail src : String) (span : Option Span := none) : Diag :=
  Diag.of .W0382 (Diag.say .W0382 .drawing (obj := some (some .tool, tool)))
    span
    (help := if logTail.isEmpty then
        s!"{tool}'s log says nothing usable; \\allow\{W0382} accepts the placeholder"
      else s!"{tool} says: {logTail}")
    (subject := some src)
    (recovery := some (.replacedBy "a placeholder box"))

/-- W0382 for an attempt that never finished: nothing is remembered or withdrawn, the
placeholder ships, and `why` is how the attempt ended. -/
public def boundaryUnfinished (tool why src : String) (span : Option Span := none) : Diag :=
  Diag.of .W0382 (Diag.say .W0382 .drawing (obj := some (some .tool, tool)))
    span (detail := some why)
    (help := s!"{why}; nothing is remembered, so a rebuild asks {tool} again; \
\\allow\{W0382} accepts the placeholder")
    (subject := some src)
    (recovery := some (.replacedBy "a placeholder box"))

/-- The help of a withdrawn picture's W0419 line: why the boundary drew nothing, in the
tool's last words where it ran, or that no tool was there. -/
public def withdrawnHelp (tool : String) (said : Option String) : String :=
  let direct := "\\pictures{ tool = none } draws every picture this way, asking no tool"
  match said with
  | some w =>
    if w.isEmpty then s!"{tool} drew nothing and its log says nothing usable; " ++ direct
    else s!"{tool} drew nothing and says: {w} — fix what {tool} reports, or " ++ direct
  | none => s!"install {tool} to draw it whole, and a warm cache needs no tool; " ++ direct

/-- The help of the line naming a withdrawn picture inside a line of text, which the
rendered subset never draws. -/
public def withdrawnInlineHelp (tool : String) (said : Option String) : String :=
  let block := "standing in a paragraph of its own, the rendered subset draws it"
  match said with
  | some w =>
    if w.isEmpty then s!"{tool} drew nothing and its log says nothing usable; " ++ block
    else s!"{tool} drew nothing and says: {w} — " ++ block
  | none => s!"install {tool} to draw it in its line, and a warm cache needs no tool; " ++ block

/-- The help of a declined picture's W0419 line. -/
public def declinedHelp : String :=
  "\\pictures{ tool = none } keeps every picture to the rendered subset; without it, \
lualatex draws this one whole"

/-- Why a boundary picture has no SVG face for the HTML artifact; each reason carries its
own words and remedy. -/
public inductive SvgFaceLoss where
  /-- Its text is in a font the engine does not draw, and no converter drew it. -/
  | textless
  /-- As `textless`, the document having declined the converter
  (`\figures{ convert = none }`). -/
  | textlessDeclined
  /-- Its PDF→SVG conversion failed or did not finish, in the tool's
  words. -/
  | unconverted (why : String)

/-- W0378: a boundary picture has no SVG face for the HTML artifact, so the page shows the
rendered subset's drawing or a labelled placeholder; one per picture, under its image
source. -/
public def boundarySvgMissing (src : String) (loss : SvgFaceLoss) : Diag :=
  let (detail, help) : String × String := match loss with
    | .textless =>
      ("its text is in a font the engine does not draw, and no converter drew it",
        "install poppler's pdftocairo, which draws the picture whole, rebuild if a conversion \
was interrupted, or \\allow{W0378} accepts the loss")
    | .textlessDeclined =>
      ("its text is in a font the engine does not draw, and the converter is declined",
        "\\figures{ convert = none } declines the converter; without it, pdftocairo draws the \
picture whole, or \\allow{W0378} accepts the loss")
    | .unconverted why =>
      (s!"its conversion to SVG failed or did not finish: {why}",
        "install poppler's pdftocairo if the reason says it is missing, rebuild if it was \
interrupted, or \\allow{W0378} accepts the loss")
  Diag.of .W0378 (Diag.say .W0378 .drawing (obj := some (none, "HTML"))) (subject := some src)
    (detail := some detail) (help := help)
    (output := some .html)

public theorem boundarySvgMissing_subject (src : String) (loss : SvgFaceLoss) :
    (boundarySvgMissing src loss).kind = .W0378 ∧
      (boundarySvgMissing src loss).subject = some src := by
  cases loss <;> simp [boundarySvgMissing, Diag.of_record_exact]

/-- W0393: the external classifier supplied no usable answer; the listing ships as plain
text, keyed by its language. -/
public def listingHighlightUnavailable (language reason : String) : Diag :=
  Diag.of .W0393 (Diag.say .W0393 .highlighter (obj := some (some .language, language)))
    (detail := some reason)
    (subject := some ("listing-language:" ++ language))
    (help := s!"check `python3 -m pygments -L lexers`, or install Pygments for `python3` ({reason})")

/-- E0606: the page failed the resource-closure check and is not published. -/
public def htmlResourceUnavailable (detail : String) : Diag :=
  Diag.of .E0606 (Diag.say .E0606 .resource) (detail := some detail)
    (help := "use readable local image, font, stylesheet and math renderer files; remove CSS `@import` and external `url(...)` dependencies")
    (output := some .html)

/-- W0104: an `\input` of a file the run itself writes under `\jobname`, which the engine writes
none of, read as empty. -/
public def runFileUnread (name : String) (span : Option Span) : Diag :=
  Diag.of .W0104 (Diag.say .W0104 .file name (some (none, "\\input"))) span
    (detail := some "the run writes it under \\jobname, and the engine writes no such file")
    (subject := some ("input:" ++ name))

/-- E0502: an included source file is not there; its content is absent. -/
public def inputMissing (name : String) (span : Option Span) (command : String := "input")
    (spelled : Option String := none) : Diag :=
  Diag.of .E0502 (if command == "input" && spelled.isNone then Diag.tex .inputMissing [name]
      else Diag.say .E0502 .file name) span
    (detail := some s!"named by {spelled.getD s!"\\{command}"}")
    (help := "\\allow{E0502} accepts the loss")

/-- What names a missing `.bib` file: the `\bibliography` command that requested it, else
biblatex's resource. -/
private def bibNamed (command : Option String) : String :=
  match command with
  | some c => s!"correct its name in {c}"
  | none => "correct the resource's name"

/-- W0503: a `.bib` file the list's `command` names is not there; the reference list stays empty
and, where `shows`, every citation shows `?`, unless the document lists entries of its own. -/
public def bibMissing (name looked : String) (span : Option Span)
    (command : Option String := some "\\bibliography") (own : Bool := false)
    (shows : Bool := true) : Diag :=
  let fix := bibNamed command
  Diag.of .W0503 (Diag.say .W0503 .file name)
    span (help := s!"put the file at {looked}, or {fix}")
    (subject := some ("bibfile:" ++ name)) (carries := if own || !shows then [] else [.W0351])

/-- W0424: one `.bib` file of several a bibliography names is not there;
the list holds the entries of the files that are, and every citation of
an entry only the missing file holds shows `?`, named (W0351). -/
public def bibMissingAmong (name looked : String) (span : Option Span)
    (command : Option String := some "\\bibliography") : Diag :=
  let drop := if command.isSome then s!"drop '{name}' from the list of files"
    else "drop the resource"
  Diag.of .W0424 (Diag.say .W0424 .file name) span
    (help := s!"put the file at {looked}, or {drop}")
    (subject := some ("bibfile:" ++ name))

/-- W0503 as a code file's documentation names its bibliography, on its page or under the inclusion
`entry` names: the file is not there, so its documentation's citations stay as written. -/
public def bibMissingLean (name looked : String) (span : Span) (_entry : Option String) : Diag :=
  Diag.of .W0503 (Diag.say .W0503 .file name) (some span)
    (help := s!"put the file at {looked}")
    (subject := some ("bibfile:" ++ name))

/-- W0503 as a code file's documentation cites entries of its project's bibliography, `name` from the
file, and declares none in `home`, where the line `spelled` would. -/
public def bibUndeclared (name home spelled : String) (keys : Array String) (span : Span) : Diag :=
  Diag.of .W0503 (Diag.say .W0503 .declaration (obj := some (some .file, name))) (some span)
    (help := s!"declare it on a line of {home}: `{spelled}`")
    (subject := some ("bibfile:" ++ name)) (detail := some (", ".intercalate keys.toList))

/-- W0503 or W0424 as a markdown document's metadata names its bibliography. -/
public def bibMissingMarkdown (among : Bool) (name looked : String) (span : Option Span)
    (shows : Bool := true) : Diag :=
  if among then
    Diag.of .W0424 (Diag.say .W0424 .file name) span
      (help := s!"put the file at {looked}, or drop '{name}' from 'bibliography:'")
      (subject := some ("bibfile:" ++ name))
  else
    Diag.of .W0503 (Diag.say .W0503 .file name)
      span (help := s!"put the file at {looked}, or correct its name in 'bibliography:'")
      (subject := some ("bibfile:" ++ name)) (carries := if shows then [.W0351] else [])

/-- E0365: a `.bib` file `\data` names is not there; its records are absent and every read
of them stays unresolved. -/
public def dataMissing (name looked : String) (span : Option Span) : Diag :=
  Diag.of .E0365 (Diag.say .E0365 .file name)
    span (help := s!"looked at: {looked}; \\allow\{E0365} accepts the loss")

/-- E0501: the `\input` stack never emptied. -/
public def inputTooDeep : Diag :=
  Diag.of .E0501 (Diag.say .E0501 .nesting (obj := some (none, "\\input")))
    (detail := some "deeper than 8 files")

/-- W0013: an `\allow` entry no diagnostic matched. -/
public def allowUnfired (code : String) : Diag :=
  Diag.of .W0013 (Diag.say .W0013 .code code)
    (help := "the document no longer needs it; drop the entry from \\allow")

end LeanTex.Cli.DriverDiag
