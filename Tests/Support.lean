module

public import LeanTex.Cli.FontDiscovery
public import LeanTex
public import LeanTex.Core.HtmlDoc

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def failures : IO.Ref (List String) → String → IO Unit :=
  fun ref name => ref.modify (name :: ·)

def check (ref : IO.Ref (List String)) (name : String) (ok : Bool) : IO Unit := do
  unless ok do failures ref name

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def svgDocument (body : String) (width : Nat := 20) (height : Nat := 20) : ByteArray :=
  (s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">" ++
    body ++ "</svg>").toUTF8

def svgBoundaryError (result : Except String α) : Bool :=
  match result with
  | .error err => (err.splitOn "SVG resource boundary").length > 1
  | .ok _ => false

/-- An independent encoder for captured resource checks. The command reads
only synthetic bytes or the repository's test assets. -/
def htmlDataOracle (mime : String) (data : ByteArray) : IO String :=
  IO.FS.withTempDir fun dir => do
    let path := dir / "payload"
    IO.FS.writeBinFile path data
    let out ← IO.Process.output { cmd := "base64", args := #["-w0", path.toString] }
    unless out.exitCode == 0 do
      throw <| IO.userError "the HTML containment byte oracle requires base64"
    return "data:" ++ mime ++ ";base64," ++ out.stdout

/-- Independently read an artifact's captured bytes, including binary font
programs. The pipe stays binary: decoding through a `String` would replace
invalid UTF-8 and corrupt the very program whose metadata the tests inspect. -/
def htmlDataDecode (href : String) : IO (String × ByteArray) := do
  let [header, payload] := href.splitOn "," |
    throw <| IO.userError "expected one embedded resource"
  let [media, "base64"] := header.splitOn ";" |
    throw <| IO.userError "expected a base64 resource"
  let ["data", mime] := media.splitOn ":" |
    throw <| IO.userError "expected a data resource"
  IO.FS.withTempDir fun dir => do
    let file := dir / "payload"
    IO.FS.writeFile file payload
    let child ← IO.Process.spawn {
      cmd := "base64", args := #["-d", file.toString],
      stdin := .null, stdout := .piped, stderr := .null }
    let data ← child.stdout.readBinToEnd
    unless (← child.wait) == 0 do
      throw <| IO.userError "the published resource contains invalid base64"
    return (mime, data)

/-- Follow the emitted inline SVG reference and independently decode its
bytes. These synthetic pages have one image per role; no sidecar can supply it. -/
def svgPublishedAsset (html : String) (_output : System.FilePath)
    (tag attr : String) : IO (String × ByteArray) := do
  let [_, tail] := html.splitOn ("<" ++ tag ++ " ") |
    throw <| IO.userError s!"expected exactly one <{tag}> in the emitted page"
  let attrs :: _ :: _ := tail.splitOn ">" |
    throw <| IO.userError s!"unclosed <{tag}> in the emitted page"
  let [_, value] := (" " ++ attrs).splitOn (" " ++ attr ++ "=\"") |
    throw <| IO.userError s!"expected exactly one {attr} on <{tag}>"
  let href :: _ :: _ := value.splitOn "\"" |
    throw <| IO.userError s!"unclosed {attr} on <{tag}>"
  let (mime, data) ← htmlDataDecode href
  unless mime == "image/svg+xml" do
    throw <| IO.userError "expected an embedded SVG reference"
  return (href, data)

/-- A synthetic two-page sequence: a wide blue first frame and a tall red
poster. No fonts or outside resources participate in its conversion. -/
def svgCanvasPdf : ByteArray := Id.run do
  let stream (ink : String) :=
    s!"<< /Length {ink.utf8ByteSize} >>\nstream\n{ink}\nendstream"
  let objects := #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R 5 0 R] /Count 2 /Resources << >> >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 120 80] /Contents 4 0 R >>",
    stream "0 0 1 rg 0 0 120 80 re f",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 60 120] /Contents 6 0 R >>",
    stream "1 0 0 rg 0 0 60 120 re f"]
  let mut text := "%PDF-1.7\n"
  let mut offsets : Array Nat := #[]
  for (object, i) in objects.zipIdx do
    offsets := offsets.push text.utf8ByteSize
    text := text ++ s!"{i + 1} 0 obj\n{object}\nendobj\n"
  let xref := text.utf8ByteSize
  text := text ++ s!"xref\n0 {objects.size + 1}\n0000000000 65535 f \n"
  for offset in offsets do
    let digits := toString offset
    text := text ++ "".pushn '0' (10 - digits.length) ++ digits ++ " 00000 n \n"
  return (text ++ s!"trailer\n<< /Size {objects.size + 1} /Root 1 0 R >>\n\
    startxref\n{xref}\n%%EOF\n").toUTF8

/-- The PNG row filters forward (ISO/IEC 15948 §9.2), one type per row via
`ft`: the synthesizer that hands the engine's unfilter and residual split
every filter, every geometry, so their statements can be exercised on
inputs the engine never wrote itself. -/
def pngFilter (px : ByteArray) (pxH rowBytes bpp : Nat) (ft : Nat → Nat) : ByteArray := Id.run do
  let sample (r i : Nat) : Nat := (px[r * rowBytes + i]?.getD 0).toNat
  let mut out := ByteArray.emptyWithCapacity (px.size + pxH)
  for r in [0:pxH] do
    let f := ft r
    out := out.push (UInt8.ofNat f)
    for i in [0:rowBytes] do
      let left := if bpp ≤ i then sample r (i - bpp) else 0
      let up := if 1 ≤ r then sample (r - 1) i else 0
      let upLeft := if 1 ≤ r ∧ bpp ≤ i then sample (r - 1) (i - bpp) else 0
      let pred :=
        if f == 0 then 0 else if f == 1 then left else if f == 2 then up
        else if f == 3 then (left + up) / 2
        else
          let p : Int := (left : Int) + up - upLeft
          let pa := (p - left).natAbs
          let pb := (p - up).natAbs
          let pc := (p - upLeft).natAbs
          if pa ≤ pb && pa ≤ pc then left else if pb ≤ pc then up else upLeft
      out := out.push (UInt8.ofNat ((sample r i + 256 - pred) % 256))
  return out

/-! Synthetic PNGs, byte by byte: the decoder reads structure, not CRCs or
pixel data, so CRC slots are zero and an IDAT payload may be arbitrary. -/

def be32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

def pngChunk (tag : String) (data : List UInt8) : List UInt8 :=
  be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++ [0, 0, 0, 0]

def pngIhdr (w h bd ct interlace : Nat) : List UInt8 :=
  be32 w ++ be32 h ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, UInt8.ofNat interlace]

def pngSigBytes : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]

def mkPng (chunks : List UInt8) : ByteArray := bytes (pngSigBytes ++ chunks)

/-- Does `needle` occur verbatim inside `hay`? The pass-through witness: a
source stream reaching the artifact byte for byte. -/
def containsBytes (hay needle : ByteArray) : Bool := Id.run do
  if needle.size == 0 || hay.size < needle.size then return false
  for i in [0:hay.size - needle.size + 1] do
    let mut ok := true
    for j in [0:needle.size] do
      if hay[i + j]! != needle[j]! then
        ok := false
        break
    if ok then return true
  return false

/-- xorshift64*: deterministic, dependency-free (as in scripts/kp-fuzz.lean).
Returns the new state and the output value. -/
def nextRand (s : UInt64) : UInt64 × UInt64 :=
  let x := s ^^^ (s >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x, x * 2685821657736338717)

/-- Draw a value below `bound`, threading the state. -/
def rand (s : UInt64) (bound : Nat) : Nat × UInt64 :=
  let (s', v) := nextRand s
  ((v % UInt64.ofNat bound).toNat, s')

def toks (s : String) : List Lex.Tok :=
  ((Lex.lex "t" s).1.map (·.tok)).toList

def elabStr (s : String) : Ir.Doc × Array Diag :=
  Elab.run "t" s

/-- The first elaborated formula in a document's paragraphs, equations,
and centred display blocks (a display alignment sets under `.center`):
enough reach for a one-formula snippet. -/
def blockFormula (b : Ir.Block) : Option Math.MList :=
  let inls := match b with
    | .para content => content
    | .equation _ content => content
    | _ => #[]
  inls.findSome? fun x => match x with
    | .formula _ _ body => some body
    | _ => none

/-- A block with any display context it rides in (`Ir.DisplayCtx`) taken
off: the display itself. -/
def unwrapDisplay (b : Ir.Block) : Ir.Block := (Ir.displayCtxOf b).2

def firstFormula (d : Ir.Doc) : Option Math.MList :=
  d.body.findSome? fun b => match unwrapDisplay b with
    | .center bs => bs.findSome? blockFormula
    | b => blockFormula b

/-- A *markdown* source through the one elaborator: the markdown door
(`Surface.read`), then `Elab.runRaws` — the same path `leantex doc.md`
takes. -/
def elabMd (s : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .markdown "t.md" s
  Elab.runRaws "t.md" raws ds

/-- Diagnostics of a markdown source. -/
def dvMd (s : String) : Array Diag := (elabMd s).2

/-! ## The markdown doors

Two ways a markdown file reaches the one elaborator: alone, as a document,
and included in a tex host through `\markdownInput`. The door checks
(`Tests/MarkdownDoors.lean`) and the CommonMark classifier
(`scripts/commonmark.lean`) read these builders, one copy. -/

/-- A reader that answers no request. -/
def nullReader : Compat.InputReader Id := fun _ context => (none, context)

/-- A markdown file as a document of its own: its door, then execution and
elaboration as the driver runs a document. The null reader is exact here:
a markdown file's raws lie in a vocabulary that holds no input or package
request (`Md.desugar_vocabulary_mem`), so no request reaches a reader. -/
def standaloneDoc (f t : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .markdown f t
  Elab.runExecuted f (Elab.executeInputs nullReader f raws) ds

/-- The included door's reader, pure: `\markdownInput{name}` is answered
with the markdown door's fragment of the file `files` maps the name to,
resumed in the requesting context as the driver resumes it; every other
request is left unanswered. The fragment's own diagnostics accumulate in
the state, where the driver's input log keeps them. -/
def mdFileReader (files : List (String × String × String)) :
    Compat.InputReader (StateM (Array Diag)) := fun request context => do
  if request.command != "markdownInput" then return (none, context)
  match files.find? (·.1 == request.name.trimAscii.toString) with
  | none => return (none, context)
  | some (_, path, text) =>
    let (sub, ds) := Surface.fragment .markdown path text request.pos
    modify (· ++ ds)
    let (answer, context) := Elab.resumeInput nullReader context request.file sub
    return (some answer, context)

/-- A tex host through its door, executed with the included door's reader:
the host's reading diagnostics, then the reader's, the driver's order. -/
def includedDoc (hostFile host : String) (files : List (String × String × String)) :
    Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (executed, readDs) := (Elab.executeInputs (mdFileReader files) hostFile raws).run #[]
  Elab.runExecuted hostFile executed (ds ++ readDs)

/-- A markdown file alone as a document named `docFile`: its door's
fragment and nothing else — no preamble, no host, no reader. Named as a
host, it is the file alone under that host's surface, the document the
neutral host's is held to; named as the file itself, it is the markdown
door's own document with its raws wrapped as the file they came from. -/
def aloneDoc (docFile f t : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.fragment .markdown f t {}
  Elab.runExecuted docFile (Elab.executeInputs nullReader docFile raws) ds

/-- The neutral host: an article whose body is one `\markdownInput` and
nothing else, so the include stands as the body's block sequence. -/
def neutralHost (name : String) : String :=
  "\\documentclass{article}\\usepackage{markdown}\\begin{document}\\markdownInput{" ++ name ++
    "}\\end{document}"

/-- The neutral host as a source is usually written: each command on a line
of its own and a blank line either side of the include, so the include
stands among the blank source the include theorems allow
(`Elab.sourceBlank`). -/
def spacedNeutralHost (name : String) : String :=
  "\\documentclass{article}\n\\usepackage{markdown}\n\n\\begin{document}\n\n\\markdownInput{" ++
    name ++ "}\n\n\\end{document}\n"

mutual

/-- One node as its tag, attributes and text, flattened — with its closing
tag, so the string states *nesting* and not only presence. Without the
closing tags a row could only ask whether a tag appeared anywhere: the
weakest row here passed on the letter `h` occurring in the tree, while the
heading it was about shipped inside the list item above it. The accumulator
threads so the walk is linear. -/
def mdFlattenOne (acc : String) (n : Html.Node) : String :=
  match n with
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    let as := attrs.foldl (fun s a => s ++ " " ++ a.1 ++ "=" ++ a.2) ""
    if Html.voidTags.contains tag then acc ++ "<" ++ tag ++ as ++ ">"
    else mdFlatten (acc ++ "<" ++ tag ++ as ++ ">") kids.toList ++ "</" ++ tag ++ ">"

def mdFlatten (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => mdFlatten (mdFlattenOne acc n) rest

end

/-- A page's HTML body as the typed tree. -/
def docNodesOf (doc : Ir.Doc) : Array Html.Node := (HtmlDoc.emitTree {} doc).2.1

/-- The tags and text a document's page carries, in order, flattened as
`mdFlatten` flattens: what a row comparing two documents' pages — or one
document reached two ways — reads. -/
def docTreeOf (doc : Ir.Doc) : String := mdFlatten "" (docNodesOf doc).toList

/-- The tags and text a markdown source's page carries, in order: enough to
state what shipped and where, which is what every defect below was about. -/
def mdTreeOf (src : String) : String := docTreeOf (elabMd src).1

/-- A page's HTML body rendered, its text escaped: what tells a hard break
(`<br>`) from the text `<br>` (`&lt;br&gt;`), which the flattened tree spells
alike. -/
def docHtmlOf (doc : Ir.Doc) : String := Html.render (Html.elem "div" (docNodesOf doc)) 0

/-- How many times a build writing `outs` names a markdown disclosure's lost
collapse: the `W0392`s under `md:disclosure` the driver's projection
(`Diag.forOutputs`) keeps. -/
def collapseNamed (outs : Array Diag.Output) (ds : Array Diag) : Nat :=
  ((Diag.forOutputs outs ds).filter fun d =>
    d.kind == .W0392 && d.subject == some "md:disclosure").size

/-- The sites the raw-HTML family places a construct at: inside a paragraph,
opening a paragraph's line, as its own block, inside each container, and
inside a heading. -/
def mdHtmlSites : List (String × (String → String)) :=
  [("mid-paragraph", fun s => s!"Alder {s} Birch\n"),
   ("line start", fun s => s!"{s} Alder\n"),
   ("own block", fun s => s!"Alder\n\n{s}\n\nBirch\n"),
   ("quote", fun s => s!"> {s}\n"),
   ("list item", fun s => s!"- {s}\n"),
   ("disclosure body", fun s => s!"<details>\n<summary>Wren</summary>\n\n{s}\n\n</details>\n"),
   ("heading", fun s => s!"# Alder {s} Birch\n")]

mutual

/-- Every `<pre>` of a tree, in document order, the accumulator threaded. -/
def mdPresOne (acc : Array Html.Node) (n : Html.Node) : Array Html.Node :=
  match n with
  | .elem "pre" _ _ => acc.push n
  | .elem _ _ kids => mdPresList acc kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def mdPresList (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => mdPresList (mdPresOne acc n) rest

end

/-- The attributes of an unconfigured fence's `<pre>`: the verbatim size,
leading, tab and wrapping settings, and a tab stop so a keyboard can reach
and scroll it (`HtmlDoc.a11yFacts`). Named once, so a backend change fails
the fence rows at this line rather than at four literals. The exact
attribute check also rejects leaked language text or an attribute hiding
the code. A markdown fence sets as its surface's code does
(`Ir.Surface.listing`): at `\footnotesize`, `0.8em`, on that size's own
leading (9.5 pt over 8, `Ir.stepSkip`), wrapping its long lines with their
continuations hung 20 pt in. -/
def mdCodeBlockPreAttrs : Array (String × String) :=
  #[("style", "font-size: 0.8em; line-height: 1.187; tab-size: 8; white-space: pre-wrap; \
text-indent: 20pt hanging each-line;"),
    ("tabindex", "0")]

/-- The page's code blocks, in order, each as the one text its `<code>`
holds — when the block is exactly a `<pre>` carrying `mdCodeBlockPreAttrs`
whose only child is a `<code>` with no attribute holding one text node, and
`none` for any other shape: a node before or after the `<code>`, an
attribute leaked onto either element, content split or nested. A needle
anchored at `</code></pre>` passed a page whose every `<pre>` opened with
leaked text. -/
def mdCodeBlocks (src : String) : Array (Option String) :=
  let (doc, _) := elabMd src
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (mdPresList #[] body.toList).map fun n =>
    match n with
    | .elem "pre" attrs #[.elem "code" cattrs #[.text s]] =>
      if attrs == mdCodeBlockPreAttrs && cattrs.isEmpty then some s else none
    | _ => none

def errCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .error)).toList.map (·.code)

def warnCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .warning)).toList.map (·.code)

def noteCodes (s : String) : List String :=
  ((elabStr s).2.filter (·.severity == .note)).toList.map (·.code)

def dvDoc (pre body : String) : String :=
  "\\documentclass{article}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def dvDeck (pre body : String) : String :=
  "\\documentclass{slides}\n" ++ pre ++ "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169 (pre body : String) : String :=
  "\\documentclass[aspectratio=169]{slides}\n" ++ pre ++
    "\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169Body (body : String) : String :=
  "\\documentclass[aspectratio=169]{slides}\n\\theme{default}\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169Frame (body : String) : String :=
  deck169Body ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}")

/-- The golden set's markdown fixtures: `testdata/corpus/<n>.md`, read by the
markdown reader as `leantex doc.md` reads them, and held to every check the
golden set is. -/
def mdGoldenNames : List String :=
  ["md-code", "md-emphasis", "md-headings", "md-images", "md-links", "md-lists",
   "md-quotes", "md-readme", "md-rules", "md-table"]

/-- The golden set: every fixture `runGoldens` elaborates and every name
`censusTable` must carry a row for. Written out rather than globbed so a
golden run's membership is visible here, and held to `testdata/corpus` by
`corpusCoverageChecks` — a fixture on disk is in this list or its own header
says why not. -/
def goldenNames : List String :=
  ["affine-lengths", "paragraphs", "layout", "declared", "fonts", "palette", "tokens", "fill",
   "links", "resume", "talk", "deck", "deck1610", "themed", "latex-idioms", "wrapper",
   "centering", "columns", "overlays", "overlays-blocks", "overprint", "notes", "furniture",
   "chrome", "footer-left", "footer-mixed", "footer-collide", "lists",
   "lists-styled", "lists-deck", "headroom",
   "marker-styled", "marker-content",
   "trio-page", "trio-deck", "trio-card", "valign", "images", "figures", "math",
   "webpage", "quotes", "quote-deck", "outline", "outline-gap", "webnav", "nav-directory",
   "bibliography", "resume-data",
   "icons",
   "diagram", "diagram-boundary", "diagram-overflow", "diagram-refused", "diagram-shapes",
   "diagram-tikzset",
   "tables", "tables-ragged", "tables-deck", "subfigures", "float-center", "box-sides",
   "math-companion", "math-first", "math-text", "math-alpha", "math-cancel", "greek-literal", "abstract", "crossref", "eqnum", "footnotes",
   "redefine", "titlebars", "titleground", "daylight", "blocks", "poster", "poster-headline", "listings",
   "algorithm", "lineno", "lineno-modulo",
   "cond-newif", "cond-ifdefined", "cond-ifx", "cond-ifnum", "cond-loaded",
   "md-include", "md-include-deck"] ++
  mdGoldenNames

-- KP test helpers: word/glue/forced-break item builders and a brute-force
-- optimum to cross-check the DP against.

/-- The fonts the repository ships, beside the fixtures that name them. Every
font-dependent check runs on these and only these, so `lake test` sees the
same faces on every host — a Mac with nothing installed included. -/
def testFonts : String := "testdata/corpus/fonts"

def findFont : IO (Option ByteArray) := do
  let p := testFonts ++ "/OpenSans-Regular.ttf"
  if ← System.FilePath.pathExists p then
    return some (← IO.FS.readBinFile p)
  return none

/-- A script fixture its owner may run, or with `exec := false` one no one
may: the same regular file with no execute bit. -/
def writeScript (path : System.FilePath) (body : String) (exec : Bool := true) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path body
  IO.setAccessRights path { user := ⟨true, true, exec⟩ }

/-- A symbolic link at `link` naming `target`: Lean has no call that makes one. -/
def symlink (target link : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  unless out.exitCode == 0 do throw <| IO.userError s!"ln -s failed: {out.stderr}"

/-- The Lean interpreter on PATH, and the `LEAN_PATH` under which a child
`lean --run` imports this build's modules: how the checks that need a
process of their own run their drivers. `what` names those checks. -/
def leanChild (what : String) : IO (System.FilePath × String) := do
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError s!"{what} require the Lean interpreter on PATH"
  let libraries ← IO.FS.realPath ".lake/build/lib/lean"
  return (lean, libraries.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD "")

/-- `text` quoted as one word for `/bin/sh`. -/
def shQuote (text : String) : String :=
  "'" ++ text.replace "'" "'\\''" ++ "'"

/-- One of the suite's shipped faces by file name, parsed; `none` when the
file is missing or does not parse. -/
def loadTestFont (file : String) : IO (Option Font.Font) := do
  let p := testFonts ++ "/" ++ file
  unless ← System.FilePath.pathExists p do return none
  match Font.parse (← IO.FS.readBinFile p) with
  | .ok f => return some f
  | .error _ => return none

/-- Does a produced file contain this ASCII run? PDF content streams are the
only witness that a face or a size reached the output, and the file as a whole
is not valid UTF-8, so the search is over bytes. -/
def bytesContain (hay : ByteArray) (needle : String) : Bool := Id.run do
  let n := needle.toUTF8
  if n.size == 0 || hay.size < n.size then return false
  for i in [0:hay.size - n.size + 1] do
    let mut ok := true
    for j in [0:n.size] do
      if hay[i + j]! != n[j]! then
        ok := false
        break
    if ok then return true
  return false

/-- The written PDF with every `/FlateDecode` stream the writer emitted
inflated and appended: the view a `bytesContain` assertion reads now that
content, object and metadata streams really compress. Raw facts (header,
xref spelling, filter names) stay visible — the raw bytes lead — and
every compressed stream's plain text follows. The writer's own spelling
(`/Length {n} >>\nstream\n`) is the anchor; a stream whose dictionary
names no flate filter is skipped as already plain. -/
def pdfText (pdf : ByteArray) : ByteArray := Id.run do
  let pat := " >>\nstream\n".toUTF8
  let mut out := pdf
  let mut i := 0
  for _ in [0:pdf.size] do
    if i + pat.size > pdf.size then break
    let mut ok := true
    for k in [0:pat.size] do
      if pdf[i + k]! != pat[k]! then
        ok := false
        break
    if !ok then
      i := i + 1
    else
      -- Walk back over the dictionary to `obj` for the filter and length.
      let dictStart := if i > 400 then i - 400 else 0
      let head := String.ofList (((pdf.extract dictStart i).toList).map fun v =>
        Char.ofNat (min v.toNat 127))
      let dataOff := i + pat.size
      let len? := do
        let part ← (head.splitOn " /Length ").getLast?
        (part.splitOn " ").head?.bind (·.toNat?)
      match len? with
      | none => i := i + 1
      | some len =>
        if (head.splitOn "/FlateDecode").length ≥ 2 then
          let z := pdf.extract dataOff (dataOff + len)
          if let .ok plain := LeanTex.Core.Flate.inflate z (len * 400 + 65536) then
            out := out ++ plain
        i := dataOff + len
  return out

/-- Re-verify a produced PDF through the engine's own reader
(`PdfRead.objects`): the cross-reference followed, every listed object
fetched and checked against the number the file spells for it
(`objects_num_covers` — direct offsets and object-stream headers alike,
where the earlier byte walk read type-1 rows only), and every stream the
reader can decode inflated. Returns the number of objects verified at a
direct offset — the count the byte walk returned. -/
def checkXref (pdf : ByteArray) : Except String Nat := do
  let es ← PdfRead.objects pdf
  let mut verified := 0
  for e in es.val do
    if let .direct _ := e.loc then
      verified := verified + 1
    -- Streams under the filters the reader owns decode, or the file is
    -- refused where the byte walk would have read past the fault. Foreign
    -- filters (an image's DCT) are data the census records, not decodes.
    let fs := PdfCensus.filtersOf e.val
    if fs.all (· == "FlateDecode") then
      if let .error err := e.decoded then
        throw s!"object {e.num}: {err}"
  return verified

/-- A fixture file's text as the driver's decoding door reads it: a
byte-order mark skipped, a byte that is not text replaced, a line ended at
CR as at LF, and a tex file's own preamble declaration of its encoding
honoured. A fixture the suite reads past the door would read differently
from the binary the moment it carried any of them. -/
def fixtureText (path : String) : IO String := do
  let bytes ← IO.FS.readBinFile path
  return if path.endsWith ".md" then (Encoding.readMarkdown path bytes).text
    else (Encoding.readDocument path bytes).1.text

/-- A source whose file includes are fulfilled before elaboration. The
filename establishes the input directory even when the source itself is
held in memory, so synthetic probes and file fixtures use the same path. -/
def elabInputSrc (file src : String) : IO (Ir.Doc × Array Diag) := do
  let (raws, readDs) := Surface.read .tex file src
  let (executed, inputDs, _) ← Input.expandInputs file raws
  return Elab.runExecuted file executed (readDs ++ inputDs)

/-- A `testdata/corpus/sty-parity` fixture run the way the driver runs it: the
input execution (`Input.expandInputs`) first, so a local `.sty` beside the
fixture is read at its use, then elaboration, then the N0020 records built from the
splice records exactly as `Main.frontend` builds them — the counts do not
exist before elaboration. Shared because two blocks drive this directory:
the `\input`-parity cases and the theme-loading family. -/
def runStyParity (name : String) :
    IO (Ir.Doc × Array Diag × Array (String × Option String × Pos)) := do
  let path := s!"testdata/corpus/sty-parity/{name}.tex"
  let src ← fixtureText path
  let (raws, _) := Parse.parse path (Lex.lex path src).1
  let (executed, inputDs, spliced) ← Input.expandInputs path raws
  let (doc, ds) := Elab.runExecuted path executed
  let ds := ds ++ spliced.map fun (sty, srcF, pos) =>
    Compat.styRead (srcF.getD path) sty pos ds
  return (doc, inputDs ++ ds, spliced)

/-- A fixture elaborated the way the driver builds it: its includes
fulfilled from the corpus directory at their use (`Input.expandInputs`), the
`\data` effect fulfilled before elaboration (the expansion needs the records
where `\begin{foreach}` stands), then elaboration, then the `.bib`
bibliography effect — the same fulfilments `Main` performs, so an include,
data or bibliography fixture exercises the pipeline the documents run.
Fixtures that request none pass through untouched. -/
def elabFixture (n src : String) : IO (Ir.Doc × Array Diag) := do
  let file := s!"{n}.tex"
  let (raws, readDiags) := Surface.read .tex file src
  let (executed, inputDiags, _) ← Input.expandInputs file raws (dir := "testdata/corpus")
  let mut dataSources : Array (String × String) := #[]
  for (srcName, _) in Data.fileRefs executed.raws do
    let name := Data.sourceName srcName
    let path := s!"testdata/corpus/{name}"
    if ← System.FilePath.pathExists path then
      dataSources := dataSources.push (srcName, ← fixtureText path)
  let (raws, dataDiags) := Data.expandData file dataSources executed.raws
  let (doc, diags) := Elab.runExecuted file (executed.withRaws raws)
    (readDiags ++ inputDiags ++ dataDiags)
  let requested := Ir.bibRefs doc
  if requested.isEmpty then return (doc, diags)
  let mut sources : Array (String × String) := #[]
  for srcName in requested do
    let name := Bib.sourceName srcName
    let path := s!"testdata/corpus/{name}"
    if ← System.FilePath.pathExists path then
      sources := sources.push (srcName, ← fixtureText path)
  let (doc, bibDiags) := Bib.apply sources doc
  return (doc, diags ++ bibDiags)

/-- A golden fixture's source file: its surface's extension under
`testdata/corpus`. -/
def goldenFile (n : String) : String :=
  s!"testdata/corpus/{n}.{if mdGoldenNames.contains n then "md" else "tex"}"

/-- A golden fixture elaborated through its own surface's reader: the
markdown reader for a markdown fixture, which requests no data and no
bibliography; `elabFixture`'s fulfilments for a `.tex` one. -/
def goldenDoc (n : String) : IO (Ir.Doc × Array Diag) := do
  let src ← fixtureText (goldenFile n)
  if mdGoldenNames.contains n then
    let file := s!"{n}.md"
    let (raws, ds) := Md.read file src
    return Elab.runRaws file raws ds
  else elabFixture n src

/-- The corpus documents a markdown twin is measured over, each as the
driver elaborates it, by path: every tex fixture with its includes, data
and bibliography fulfilled (`elabFixture`), and every markdown fixture of
the golden set through its door (`goldenDoc`). The twin tier and the reader
hop read this one list. -/
def corpusTwinDocs : IO (Array (String × Ir.Doc)) := do
  let mut names : Array String := #[]
  for f in ← System.FilePath.readDir "testdata/corpus" do
    if f.fileName.endsWith ".tex" then names := names.push (f.fileName.dropEnd 4).toString
  let mut out := #[]
  for n in names.qsort (· < ·) do
    let (d, _) ← elabFixture n (← fixtureText s!"testdata/corpus/{n}.tex")
    out := out.push (s!"testdata/corpus/{n}.tex", d)
  for n in mdGoldenNames do
    let (d, _) ← goldenDoc n
    out := out.push (s!"testdata/corpus/{n}.md", d)
  return out

def firstDiff (expected actual : String) : String := Id.run do
  let e := expected.splitOn "\n"
  let a := actual.splitOn "\n"
  for i in [0:max e.length a.length] do
    let el := e[i]?.getD "<missing>"
    let al := a[i]?.getD "<missing>"
    if el != al then
      return s!"line {i + 1}:\n  expected: {el.quote}\n  actual:   {al.quote}"
  return "no difference"

def runGoldens (update : Bool) (fail : String → IO Unit) : IO Unit := do
  if update then
    IO.FS.createDirAll "testdata/golden"
  for n in goldenNames do
    let (doc, diags) ← goldenDoc n
    let out := Ir.dump doc diags -- ir tier: goldens witness elaboration, not the artifact
    let path := s!"testdata/golden/{n}.txt"
    if update then
      IO.FS.writeFile path out
      IO.println s!"updated {path}"
    else
      let golden ← try
        pure (some (← IO.FS.readFile path))
      catch _ =>
        pure none
      match golden with
      | none => fail s!"golden {n}: missing {path} (run: lake exe Tests --update)"
      | some g =>
        unless g == out do
          fail s!"golden {n}: mismatch, {firstDiff g out} (if intended, run: lake exe Tests --update)"

/-- The shipped-page census over `Layout.Out`: the observable facts a page
claim may cite (AGENTS.md, the page-claim rule). Chars come from the set
glyph runs — gaps become single spaces and lines join with one space, so a
phrase survives a line break but not a hyphenation. `covered` collects the
runs painted in one of the document's own covered colours
(`coveredColorsOf`: the plain cover plus the per-colour cover of every
palette entry). Deliberately thin: it grows toward
the role census `Check.Shipped` is heading for; what `censusChecks`
enforces today is coverage — no fixture enters the golden set witnessed by
its IR dump alone. -/
structure CensusLine where
  x : Dim.Sp
  /-- The line's baseline, in layout coordinates (y grows downward): what a
  fact about vertical order or a declared gap reads. -/
  y : Dim.Sp
  /-- The largest set size among the line's glyph runs (0 on a glyphless
  line): what a fact about a declared display size reads. -/
  size : Dim.Sp
  /-- The line's set width, so a fact can judge its right edge — where a
  footer's right slot must sit whatever the left slot holds. -/
  width : Dim.Sp
  text : String
  /-- The line stands in the reserved margin band by design
  (`Layout.LineOut.furniture`): running head and foot, chrome slots, the
  logo — and the margin line numbers. -/
  furniture : Bool := false
  /-- A counted body line (`Layout.LineOut.counted`): a galley text line
  the line-number census counts — what a margin number attaches to. -/
  counted : Bool := false
  /-- The face every glyph run on the line sets in, in run order: the
  `FontSet` index the layout resolved. What a fact about *which family*
  ink sets in reads — a picture's node label must set in the face the
  body sets in, and only the shipped run can say which face that was
  (`Picture.labelFace_agree`'s page side). Under a one-face set every
  entry is 0 and the channel says nothing; `twoSlotOf` is the set that
  distinguishes the slots. -/
  runFonts : Array Nat := #[]

structure CensusPage where
  lines : Array CensusLine
  covered : String
  rules : Nat
  /-- Every rule segment shipped on the page, in line order: its line's
  baseline and its thickness — what the title-bar facts read (a bar at its
  declared weight, above or below the title's line). -/
  ruleSegs : Array (Dim.Sp × Dim.Sp) := #[]
  /-- Typed decoration segments in line order: kind, baseline, width,
  thickness, raise, and colour. -/
  decorations : Array (Ir.Decoration × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) := #[]
  fills : Nat
  /-- Every fill rectangle shipped on the page, in paint order — what the
  cut-mark facts read (marks inside the bleed strip, none in the gap,
  duplex-symmetric). -/
  fillRects : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- Picture paths shipped on the page: node outlines and edges. -/
  paths : Nat
  /-- Every shipped path's stroke, in paint order: its colour and width.
  What a fact about an inherited picture-level key reads — a key set on
  the picture and again on the path must leave the path's own value on the
  page (`Picture.inherit_inner_exact`), and only the artifact can say so.
  An unstroked path (a node's fill alone) contributes nothing. -/
  pathStrokes : Array (Ir.Color × Dim.Sp) := #[]
  /-- Every shipped path's extent, in paint order: a circle's diameter, a
  rectangle's own width and height, a segment chain's or a tip's bounding
  box. What a fact about a size key set at more than one level reads — a
  node whose `minimum size` is declared by the picture, by `every node`,
  and by its own bracket ships exactly one of the three
  (`Picture.merge_own_exact`, `Picture.merge_every_exact`), and only the
  page can say which. -/
  pathSpans : Array (Dim.Sp × Dim.Sp) := #[]
  /-- Every shipped path's bounding box, in paint order: `(x, y, w, h)` in
  page coordinates. `pathSpans` is its extent half; this adds *where* the
  path stands, which is what a fact about relative node placement reads —
  `left=of` and `right=of` are claims about position, and a node's
  resolved centre is only visible on the page
  (`Picture.placeRel_exact`, `Picture.place_order_agree`). -/
  pathBoxes : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- Image boxes shipped on the page: an embedded figure, or a boundary
  request's box (fulfilled or placeholder) — what the diagram-boundary
  row reads to pin that the request ships ink where the picture stood. -/
  images : Nat := 0
  /-- Filled polygons shipped in the page's lines — a formula's cancel
  strikes and arrowheads — as their points in page coordinates (y down):
  what the cancel facts read, the strike's corners and the arrowhead's
  tip against the struck ink. -/
  polys : Array (Array (Dim.Sp × Dim.Sp)) := #[]

def CensusPage.text (p : CensusPage) : String :=
  String.intercalate " " (p.lines.toList.map (·.text))

/-- The colours covering can paint in a document: the plain cover (runs
with no colour of their own) and the per-colour cover of every palette
entry — computed from the same `Design.cover` layout reads. A fixed point
(`cov.of c == c`, e.g. the page colour itself: covering toward `bg` moves
nothing) is excluded: it covers nothing, and keeping it would read active
ink painted in that colour as covered. -/
def coveredColorsOf (doc : Ir.Doc) : Array Ir.Color :=
  let cov := (Ir.Design.ofDoc doc).cover
  (doc.palette.entries.filterMap fun (_, c) =>
    let covered := cov.of c
    if covered == c then none else some covered).push cov.plain

def censusOf (coveredColors : Array Ir.Color) (out : Layout.Out) :
    Array CensusPage := Id.run do
  let mut pages : Array CensusPage := #[]
  for p in out.pages do
    let mut lines : Array CensusLine := #[]
    let mut covered := ""
    let mut rules := 0
    let mut ruleSegs : Array (Dim.Sp × Dim.Sp) := #[]
    let mut decorations :
        Array (Ir.Decoration × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) := #[]
    let mut images := 0
    let mut polys : Array (Array (Dim.Sp × Dim.Sp)) := #[]
    for l in p.lines do
      let mut px := l.x
      let mut chars := ""
      let mut runSize : Dim.Sp := 0
      let mut runFonts : Array Nat := #[]
      for seg in l.segs do
        match seg with
        | .run idx color _ w glyphs size _ _ _ _ _ =>
          px := px + w
          runSize := max runSize size
          runFonts := runFonts.push idx
          if coveredColors.contains color then
            for (_, c, _) in glyphs do
              chars := chars.push c
              covered := covered.push c
          else
            for (_, c, _) in glyphs do
              chars := chars.push c
            covered := covered.push ' '
        | .gap w _ | .decoratedGap w _ _ =>
          px := px + w
          chars := chars.push ' '
          covered := covered.push ' '
        | .rule w th _ _ =>
          px := px + w
          rules := rules + 1
          ruleSegs := ruleSegs.push (l.y, th)
        | .decoration kind w th raise color =>
          px := px + w
          rules := rules + 1
          ruleSegs := ruleSegs.push (l.y, th)
          decorations := decorations.push (kind, l.y, w, th, raise, color)
        -- an image is decorative ink to the text census, like a rule
        | .image _ w _ =>
          px := px + w
          images := images + 1
        | .poly pts _ => polys := polys.push (pts.map fun (x, y) => (px + x, l.y - y))
      -- The census asks where the text block stands, so a protruded
      -- line reports its measure edge: the ink deliberately hangs
      -- `l.hang` left of it (`Layout.protrudeLeft`).
      lines := lines.push { x := l.x + l.hang, y := l.y, size := runSize
                            width := l.setWidth, text := chars
                            furniture := l.furniture, counted := l.counted
                            runFonts := runFonts }
      covered := covered.push ' '
    pages := pages.push { lines := lines
                          covered := covered
                          rules := rules
                          ruleSegs := ruleSegs
                          decorations := decorations
                          polys := polys
                          fills := p.fills.size
                          fillRects := p.fills.map fun f => (f.x, f.y, f.w, f.h)
                          paths := p.paths.size
                          pathStrokes := p.paths.filterMap fun q =>
                            q.stroke.map fun s => (s.color, s.width)
                          pathSpans := p.paths.map fun q =>
                            match q.path with
                            | .circle _ _ r => (2 * r, 2 * r)
                            | .rect _ _ w h => (w, h)
                            | .tri x1 y1 x2 y2 x3 y3 =>
                              (max x1 (max x2 x3) - min x1 (min x2 x3),
                               max y1 (max y2 y3) - min y1 (min y2 y3))
                            | .segs segs =>
                              let xs := segs.flatMap fun s => match s with
                                | .line x1 _ x2 _ => #[x1, x2]
                                | .cubic x1 _ _ _ _ _ x2 _ => #[x1, x2]
                              let ys := segs.flatMap fun s => match s with
                                | .line _ y1 _ y2 => #[y1, y2]
                                | .cubic _ y1 _ _ _ _ _ y2 => #[y1, y2]
                              (xs.foldl max (xs[0]?.getD 0) - xs.foldl min (xs[0]?.getD 0),
                               ys.foldl max (ys[0]?.getD 0) - ys.foldl min (ys[0]?.getD 0))
                          pathBoxes := p.paths.map fun q =>
                            match q.path with
                            | .circle x y r =>
                              let r := max r (-r)
                              (x - r, y - r, 2 * r, 2 * r)
                            | .rect x y w h => (x, y, w, h)
                            | .tri x1 y1 x2 y2 x3 y3 =>
                              let lo := (min x1 (min x2 x3), min y1 (min y2 y3))
                              (lo.1, lo.2, max x1 (max x2 x3) - lo.1,
                                max y1 (max y2 y3) - lo.2)
                            | .segs segs =>
                              let xs := segs.flatMap fun s => match s with
                                | .line x1 _ x2 _ => #[x1, x2]
                                | .cubic x1 _ _ _ _ _ x2 _ => #[x1, x2]
                              let ys := segs.flatMap fun s => match s with
                                | .line _ y1 _ y2 => #[y1, y2]
                                | .cubic _ y1 _ _ _ _ _ y2 => #[y1, y2]
                              let x0 := xs.foldl min (xs[0]?.getD 0)
                              let y0 := ys.foldl min (ys[0]?.getD 0)
                              (x0, y0, xs.foldl max (xs[0]?.getD 0) - x0,
                                ys.foldl max (ys[0]?.getD 0) - y0)
                          images := images }
  return pages

def hasStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The opening tags of a page's failed-face placeholders: the spans that
carry `data-image-src`. -/
def placeholderTags (html : String) : List String :=
  ((html.splitOn "<span ").drop 1).filterMap fun rest =>
    let tag := (rest.splitOn ">").headD ""
    if hasStr tag "data-image-src=" then some tag else none

/-- An attribute's value in one opening tag, as the serializer writes it. -/
def attrIn (tag name : String) : Option String :=
  match (" " ++ tag).splitOn (" " ++ name ++ "=\"") with
  | _ :: rest :: _ => some ((rest.splitOn "\"").headD "")
  | _ => none

/-- Does an opening tag carry a non-empty accessible name? -/
def labelled (tag : String) : Bool :=
  (attrIn tag "aria-label").any (!·.isEmpty)

/-- Does a compat-index row's call load the row's own package? Then the
scaffold does not load it a second time: a duplicate load puts the call's
whole effect in the baseline as well, and a `\usepackage{times}` row could
not witness anything. The decision is read off the row's own text — never a
list of package names here, which would drift from the directory. -/
def compatRowSelfLoads (pkg call : String) : Bool :=
  hasStr call "\\usepackage" && hasStr call ("{" ++ pkg ++ "}")

/-- The document a compat-index row elaborates as: the call at its declared
place, with the package loaded unless the call loads it itself. A frame
uses a presentation class and loads an ordinary package in its preamble. -/
def compatRowSrc (pkg place call : String) : String :=
  let load := if compatRowSelfLoads pkg call then "" else s!"\\usepackage\{{pkg}}\n"
  if place == "pre" then
    s!"\\documentclass\{article}\n{load}{call}\n\\begin\{document}\nx\n\\end\{document}"
  else if place == "frame" then
    let isClass := Compat.presentationClasses.contains pkg
    let cls := if isClass then pkg else "beamer"
    let load := if isClass then "" else load
    s!"\\documentclass\{{cls}}\n{load}\\begin\{document}\n\\begin\{frame}\n{call}\n\\end\{frame}\n\\end\{document}"
  else
    s!"\\documentclass\{article}\n{load}\\begin\{document}\n{call}\n\\end\{document}"

/-- Count whole names whose preceding source passes `keep`. A name inside
a longer identifier or following a dot is never a separate occurrence. -/
def wordCountWhere (text word : String) (keep : String → Bool) : Nat := Id.run do
  let parts := (text.splitOn word).toArray
  let nameChar (c : Char) : Bool :=
    c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || c == '.'
  let mut n := 0
  for i in [0:parts.size - 1] do
    let before := parts[i]?.getD ""
    let after := parts[i + 1]?.getD ""
    let leftOk := if before.isEmpty then i == 0 else !nameChar before.back
    let rightOk := if after.isEmpty then i + 2 == parts.size else !nameChar after.front
    if leftOk && rightOk && keep before then n := n + 1
  return n

/-- How many times `word` stands in `text` as a whole name: not inside a
longer identifier, and not as a field after a dot — a call to
`pdfStreamChecks` is no call to `StreamChecks`. -/
def wordCount (text word : String) : Nat :=
  wordCountWhere text word fun _ => true

def censusText (c : Array CensusPage) : String :=
  String.intercalate " " (c.toList.map (·.text))

def pageHas (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.text needle).getD false

/-- How many times `needle` is inked on page `i`. The census counts what
shipped, so a construct that put its content on the page twice reads as 2
here — `pageHas` cannot tell one copy from two. -/
def pageOccurs (c : Array CensusPage) (i : Nat) (needle : String) : Nat :=
  (c[i]?.map fun p => (p.text.splitOn needle).length - 1).getD 0

def pageCovered (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.covered needle).getD false

def pageAllRevealed (c : Array CensusPage) (i : Nat) : Bool :=
  (c[i]?.map fun p => (p.covered.trimAscii.toString).isEmpty).getD false

/-- The x of the first shipped line on page `i` containing `needle`. -/
def lineXOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.x)

/-- The baseline of the first shipped line on page `i` containing `needle`. -/
def lineYOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.y)

/-- The largest run size of the first shipped line on page `i` containing
`needle`: what a declared display size sets. -/
def lineSizeOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.size)

/-- The rule segments shipped on page `i`, in line order: (baseline,
thickness) pairs. -/
def pageRuleSegs (c : Array CensusPage) (i : Nat) : Array (Dim.Sp × Dim.Sp) :=
  (c[i]?.map (·.ruleSegs)).getD #[]

/-- The right edge (x plus set width) of the first shipped line on page `i`
containing `needle`: where a footer's right slot must end. -/
def lineRightOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map
    fun l => l.x + l.width

/-- The glyph text of one shipped line: each run's characters in order,
a gap as one space (`gapAsSpace := false` reads the bare glyphs — a page
number's centring gaps are not its text). -/
def lineText (l : Layout.LineOut) (gapAsSpace : Bool := true) : String :=
  l.segs.foldl (fun s seg => match seg with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.foldl (fun s (_, c, _) => s.push c) s
    | .gap _ _ | .decoratedGap _ _ _ => if gapAsSpace then s.push ' ' else s
    | _ => s) ""

/-- A shipped line's runs, left to right: the face index, the glyphs, and the
run's left edge and width on the page. -/
def lineRuns (l : Layout.LineOut) : Array (Nat × String × Dim.Sp × Dim.Sp) := Id.run do
  let mut out := #[]
  let mut x := l.x
  for seg in l.segs do
    match seg with
    | .run idx _ _ w gs _ _ _ _ _ _ =>
      out := out.push (idx, String.ofList (gs.map (·.2.1)).toList, x, w)
      x := x + w
    | .gap w _ | .decoratedGap w _ _ => x := x + w
    | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
    | .poly _ _ => pure ()
    | .image _ w _ => x := x + w
  return out

/-- Whether a shipped line sets any glyph: a link's underline or a rule ships
as a line of its own that sets none. -/
def hasGlyphRun (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
    | _ => false

/-- Reject diagnostics that would make a placement comparison lose its text. -/
def noDroppedGlyph (out : Layout.Out) : Bool :=
  !out.diags.any fun d => d.kind == .E0405 || d.kind == .W0009

/-- A line's text as a reader sees it: `lineText`, but a glyphless run — a
tie, which ships as a box a space wide (Layout's no-break-space arm) —
reads as the space the page shows. -/
def lineInk (l : Layout.LineOut) : String := l.segs.foldl (fun s seg => match seg with
  | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
    if glyphs.isEmpty then s.push ' ' else glyphs.foldl (fun s (_, c, _) => s.push c) s
  | .gap _ _ | .decoratedGap _ _ _ => s.push ' '
  | _ => s) ""

/-- The furniture baselines (head y, foot y) a geometry owes under `font`'s
ink and a declared gap: functions of the geometry alone
(`furnHeadY`/`furnFootY` take no content) — what the shipped furniture
lines must stand at (`furniture_symmetric`'s realisation). -/
def furnYs (font : Font.Font) (geom : Layout.Geom)
    (gap : Option Dim.Sp := none) : Dim.Sp × Dim.Sp :=
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let band := Layout.furnitureBand geom.vmargin
    (scale font.ascent + scale (-font.descent)) gap
  (Layout.furnHeadY band (scale font.ascent),
   Layout.furnFootY band geom.pageH (scale (-font.descent)))

mutual

/-- The text content of an emitted HTML node, for the agreement census: the
typed tree's characters with the markup stripped — the HTML side of what
`censusOf` reads off the PDF's shipped lines. -/
def nodeTextOne (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ _ kids => nodeTextList acc kids.toList

def nodeTextList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => nodeTextList (nodeTextOne acc k) rest

end

mutual

/-- The first `mathvariant` attribute an emitted tree declares, in document
order: the MathML `.styled` arm sets `("mathvariant", style.mathvariant)` on
the `mi`/`mn` leaf, so this pulls the semantic variant a resolved text-style
scalar carries (the twin of the PDF face-slot selection). `none` when no node
declares one. -/
def mathvariantOne : Html.Node → Option String
  | .text _ => none
  | .style _ => none
  | .script _ _ => none
  | .elem _ attrs kids =>
    match attrs.find? (fun (k, _) => k == "mathvariant") with
    | some (_, v) => some v
    | none => mathvariantList kids.toList

def mathvariantList : List Html.Node → Option String
  | [] => none
  | k :: rest => match mathvariantOne k with
    | some v => some v
    | none => mathvariantList rest

end

mutual

/-- The first `style` attribute an emitted tree declares, in document order:
the MathML `.styled` arm sets `("style", style.css)` on the leaf, so this
pulls the CSS a resolved text-style scalar carries (the browser-honoured
twin of the PDF face-slot selection). `none` when no node declares one. -/
def styleOne : Html.Node → Option String
  | .text _ => none
  | .style _ => none
  | .script _ _ => none
  | .elem _ attrs kids =>
    match attrs.find? (fun (k, _) => k == "style") with
    | some (_, v) => some v
    | none => styleList kids.toList

def styleList : List Html.Node → Option String
  | [] => none
  | k :: rest => match styleOne k with
    | some v => some v
    | none => styleList rest

end

mutual

/-- The text an emitted page *shows*, as the artifact itself says it: the
typed tree's characters with every `hidden` subtree dropped — what the UA
stylesheet's `[hidden] { display: none }` removes, and so the HTML twin of
a shipped PDF page's ink. `nodeTextOne` reads the whole tree, which is the
declaration; this reads what a reader with no snap state sees, which is
step 1. The distinction is what the census could not make when overlay
alternation put both groups inside one visible wrapper. -/
def shownTextOne (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ attrs kids =>
    if attrs.any (fun (k, _) => k == "hidden") then acc
    else shownTextList acc kids.toList

def shownTextList (acc : String) : List Html.Node → String
  | [] => acc
  | k :: rest => shownTextList (shownTextOne acc k) rest

end

/-- How many times `needle` is declared in an emitted tree: `pageOccurs`'s
twin over the HTML artifact. -/
def treeOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((nodeTextList "" nodes.toList).splitOn needle).length - 1

/-- How many times `needle` is *shown* by an emitted tree, hidden subtrees
excluded: the HTML side of `pageOccurs`, and the check that was missing
when an alternation shipped both its groups on one page. -/
def treeShownOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((shownTextList "" nodes.toList).splitOn needle).length - 1

mutual

/-- Every chrome footer in the emitted deck, in document order, as its two
slots' text: the HTML side of the footline fact. The spans carry their
declared side as a class (`Ir.Chrome.footBand` through `emitTree`), and the
stylesheet pins each to its edge. -/
def slideFootsOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem tag attrs kids =>
    if tag == "footer" &&
        attrs.any (fun (k, v) => k == "class" && (v.splitOn "slide-foot").length > 1) then
      let slotText (cls : String) : String :=
        kids.foldl (fun s k => match k with
          | .elem _ kattrs _ =>
            if kattrs.any (fun (a, v) => a == "class" && v == cls) then
              nodeTextOne s k
            else s
          | _ => s) ""
      acc.push ((slotText "band-left").trimAscii.toString,
        (slotText "band-right").trimAscii.toString)
    else slideFootsList acc kids.toList

def slideFootsList (acc : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => slideFootsList (slideFootsOne acc k) rest

end

/-- Every chrome footer the PDF ships, in page order, as its two slots' text:
`PageOut.foot` is the one footline declaration resolved per page
(`Ir.Chrome.footBand`), each slot naming its side, and the physical pass
applied exactly as the final layout pass applies it. -/
def pdfFoots (out : Layout.Out) : Array (String × String) := Id.run do
  let mut res : Array (String × String) := #[]
  let total := out.pages.size
  for h : i in [0:out.pages.size] do
    if let some band := out.pages[i].foot then
      let text (side : Ir.BandSide) : String :=
        (band.filter (·.side == side)).foldl (fun acc s =>
          acc ++ (Ir.plainText (Layout.substPage (i + 1) total s.content))) ""
      res := res.push ((text .left).trimAscii.toString,
        (text .right).trimAscii.toString)
  return res

/-- Adjacent equal pairs collapsed: the pages of one stepped frame share
their footer, and the HTML has one section per frame. -/
def dedupConsecutive (xs : Array (String × String)) : Array (String × String) :=
  xs.foldl (fun acc p => if acc.back? == some p then acc else acc.push p) #[]

mutual

/-- Every element of an emitted tree with its subtree text and its own
style attribute, for the epoch checks: which node carries a redefinition
is a fact of the typed tree, never of a rendered string. -/
def elemStylesOne (acc : Array (String × String)) : Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let acc := acc.push (nodeTextOne "" (.elem t attrs kids),
      (((attrs.find? (·.1 == "style")).map (·.2)).getD ""))
    elemStylesList acc kids.toList

def elemStylesList (acc : Array (String × String)) : List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => elemStylesList (elemStylesOne acc k) rest

end

/-- The source with string literals, char literals, and comments blanked, so
the emission scan below reads code proper: a code named in a docstring or a
help text is a mention, not an emission. Line comments, nested block
comments, `\"` escapes, and char literals (whose `'\"'` would otherwise read
as opening a string) are tracked. -/
def stripNonCode (src : String) : String := Id.run do
  let cs := src.toList.toArray
  let mut out := ""
  let mut i := 0
  let mut depth := 0
  let mut inStr := false
  let mut inLine := false
  let mut esc := false
  for _ in [0:cs.size] do
    if h : i < cs.size then
      let c := cs[i]
      if inStr then
        if esc then esc := false
        else if c == '\\' then esc := true
        else if c == '"' then inStr := false
        out := out.push ' '
        i := i + 1
      else if inLine then
        if c == '\n' then
          inLine := false
          out := out.push '\n'
        else
          out := out.push ' '
        i := i + 1
      else if depth > 0 then
        if c == '-' && cs[i + 1]? == some '/' then
          depth := depth - 1
          i := i + 2
        else if c == '/' && cs[i + 1]? == some '-' then
          depth := depth + 1
          i := i + 2
        else
          out := out.push (if c == '\n' then '\n' else ' ')
          i := i + 1
      else if c == '/' && cs[i + 1]? == some '-' then
        depth := 1
        i := i + 2
      else if c == '-' && cs[i + 1]? == some '-' then
        inLine := true
        i := i + 2
      else if c == '\'' && cs[i + 1]? == some '\\' then
        -- an escaped char literal ('\n', '\\', '\"', '\u00a0'): skip to its
        -- closing quote
        let mut j := i + 2
        for _ in [0:8] do
          if cs[j]? == some '\'' then break
          j := j + 1
        for _ in [i:j+1] do
          out := out.push ' '
        i := j + 1
      else if c == '\'' && cs[i + 2]? == some '\'' && cs[i + 1]? != some '\'' then
        -- a plain char literal ('x')
        out := out ++ "   "
        i := i + 3
      else if c == '"' then
        inStr := true
        out := out.push ' '
        i := i + 1
      else
        out := out.push c
        i := i + 1
    else break
  return out

/-- Is this token one diagnostic code (`E0330`)? -/
def isDiagCode (s : String) : Bool :=
  match s.toList with
  | [k, a, b, c, d] =>
    (k == 'E' || k == 'W' || k == 'N') && [a, b, c, d].all Char.isDigit
  | _ => false

/-- The `DiagCode` constructors a stripped source applies: every dot-applied
code-shaped token (`.E0304`, `DiagCode.E0502`). -/
def appliedCodes (stripped : String) : List String := Id.run do
  let mut out : List String := []
  for part in (stripped.splitOn ".").drop 1 do
    let tok := String.ofList (part.toList.takeWhile Char.isAlphanum)
    if isDiagCode tok && !out.contains tok then
      out := tok :: out
  return out

/-- The engine's sources as the emission scans read them: every `LeanTex/`
module and the driver, path-sorted, with the codes each applies. The
registry itself (`Diag.lean`) names every code and emits none, so it is
left out. -/
def codeSources : IO (Array (String × List String)) := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  let mut out : Array (String × List String) := #[]
  for f in files.qsort (·.toString < ·.toString) do
    if f.toString == "LeanTex/Core/Diag.lean" then continue
    out := out.push (f.toString, appliedCodes (stripNonCode (← IO.FS.readFile f)))
  return out

/-- A document laid out as the driver hands it to the backends: math
alphabet scopes resolve against the selected face before the fallback census
or layout sees their scalars. Resolution diagnostics lead layout diagnostics,
as they do in the driver. -/
def layoutOf (fonts : Font.FontSet) (doc : Ir.Doc)
    (geom : Layout.Geom := Layout.Geom.ofPage doc.page)
    (pats : Option Hyphen.Patterns := none)
    (imgs : Image.Store := {}) : Layout.Out :=
  let family := fonts.math.bind (fonts.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (doc, alphaDiags) := Ir.resolveMathAlphas fonts.mathAlphabets family doc
  let out := Layout.run geom fonts pats doc imgs
  { out with diags := alphaDiags ++ out.diags }

/-- The font set a golden fixture lays out under in the suite: `oneFace`,
plus the math face a build would resolve — `mathSet` (the shipped Fira
Math) when the fixture declares a math face, else `FontDiscovery.pickMathFace`
over the shipped corpus faces when the document reaches math — plus a
fallback face per Private Use Area scalar an icon needs, found the way a
build finds it (the scan over the shipped corpus). Everything else keeps
the deliberately minimal set: the stand-in degradations are themselves
under test (`listChecks`), and a broader map would silently upgrade them.
The census and the attribution checks both lay out the corpus through
this one resolution. -/
def fixtureFontSet (oneFace mathSet : Font.FontSet) (shipped : Array FontDb.Face)
    (doc : Ir.Doc) : IO Font.FontSet := do
  let fs ← if doc.fonts.math.isSome then pure mathSet
    else if (Layout.docMathScalars doc).isEmpty then pure oneFace
    else do
      match ← FontDiscovery.pickMathFace shipped (doc.fonts.body.getD "") with
      | some (face, _) =>
        match Font.parse (← IO.FS.readBinFile face.path) with
        | .ok f => pure { oneFace with
            fonts := oneFace.fonts.push f
            math := some oneFace.fonts.size }
        | .error _ => pure oneFace
      | none => pure oneFace
  let fs := match fs.math.bind (fs.fonts[·]?) with
    | some f => { fs with mathAlphabets := f.mathAlphabetCoverage doc.fonts.mathSources }
    | none => fs
  let uncovered := (Layout.docScalars doc).filter fun ch =>
    0xE000 ≤ ch.toNat && ch.toNat ≤ 0xF8FF &&
      fs.fonts.all fun f => (f.gid ch).isNone
  if uncovered.isEmpty then return fs
  let mut fs := fs
  for (ch, path) in ← FontDiscovery.fallbackPicks shipped uncovered do
    match Font.parse (← IO.FS.readBinFile path) with
    | .ok f =>
      let idx := match fs.fonts.zipIdx.find? (fun p => p.1.family == f.family) with
        | some (_, i) => i
        | none => fs.fonts.size
      let fs' := if idx == fs.fonts.size then
          { fs with fonts := fs.fonts.push f } else fs
      fs := { fs' with fallback := fs'.fallback.push (ch, idx) }
    | .error _ => pure ()
  return fs

/-- The shipped Fira Math beside `oneFace` in the math slot: what a fixture
that declares a math face lays out under. -/
def mathSetOf (oneFace : Font.FontSet) : IO Font.FontSet := do
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"fixture fonts: FiraMath unparsable: {e}")
  return { oneFace with
    fonts := oneFace.fonts.push fira
    math := some oneFace.fonts.size
    mathAlphabets := fira.mathAlphabetCoverage {} }

/-- The four shipped Source Serif faces in every slot — regular 0, bold 1,
italic 2, bold italic 3 — and Fira Math as the math face, 4: a set in which
a run's face index says its weight, its slant, and whether it is maths.
`none` when a face does not load. -/
def serifFacesSet : IO (Option Font.FontSet) := do
  let mut loaded : Array Font.Font := #[]
  for n in #["SourceSerifPro-Regular.otf", "SourceSerifPro-Bold.otf",
      "SourceSerifPro-RegularIt.otf", "SourceSerifPro-BoldIt.otf", "FiraMath-Regular.otf"] do
    let p := testFonts ++ "/" ++ n
    unless ← System.FilePath.pathExists p do return none
    match Font.parse (← IO.FS.readBinFile p) with
    | .ok f => loaded := loaded.push f
    | .error _ => return none
  return some {
    fonts := loaded
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 1),
       ((slot, 400, true), 2), ((slot, 700, true), 3)]).toArray
    math := some 4
    mathAlphabets := loaded[4]!.mathAlphabetCoverage {} }

/-- Every shipped line, furniture included, in page order: what a claim
about absolute placement (a fil sandwich, a frame's vertical distribution)
reads. `bodyLines` is this with the furniture filtered out. -/
def allLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines)

/-- The document's own flow lines, shipped: every line except engine-placed
furniture (`LineOut.furniture` — running content, the plain page number).
What a claim about the body's setting means; a furniture claim reads the
flag this filters out. -/
def bodyLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines.filter (!·.furniture))

/-- The distances between consecutive body baselines, in page order: the
line pitches a page shipped. -/
def baselinePitches (out : Layout.Out) : Array Dim.Sp :=
  let lines := bodyLines out
  (lines.zip (lines.extract 1 lines.size)).map fun (a, b) => b.y - a.y

/-- Every shipped line's position, size and text, furniture included, in
page order: what "two documents set the same page" means to a row that
compares them. -/
def shippedLinesOf (fonts : Font.FontSet) (doc : Ir.Doc) :
    Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (allLines (layoutOf fonts doc)).map fun l => (l.x, l.y, l.size, lineText l)

/-- Face indices and character scalars of shipped body glyphs, in paint order. -/
def bodyGlyphs (out : Layout.Out) : Array (Nat × Char) :=
  (bodyLines out).flatMap fun line => line.segs.flatMap fun seg => match seg with
    | .run f _ _ _ gs _ _ _ _ _ _ => gs.map fun g => (f, g.2.1)
    | _ => #[]

/-- The x each glyph run of a shipped line starts at, with its text. -/
def metricRunsAt (l : Layout.LineOut) : Array (String × Dim.Sp) := Id.run do
  let mut x := l.x
  let mut out : Array (String × Dim.Sp) := #[]
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      unless glyphs.isEmpty do
        out := out.push (String.ofList (glyphs.toList.map (·.2.1)), x)
      x := x + w
    | .gap w _ | .decoratedGap w _ _ => x := x + w
    | .rule w _ _ _ | .decoration _ w _ _ _ => x := x + w
    | .poly _ _ => pure ()
    | .image _ w _ => x := x + w
  return out

/-- A body glyph's shipped position and paint, independent of run segmentation
and structure-leaf numbering. Positions and unexpanded advances are exact sp
values; x excludes page bleed, y includes the run's raise, and line numbers
count only body lines within each page. -/
structure ShippedGlyph where
  page : Nat
  line : Nat
  face : Nat
  glyph : Nat
  scalar : Char
  x : Dim.Sp
  y : Dim.Sp
  advance : Dim.Sp
  size : Dim.Sp
  expand : Int
  color : Ir.Color
  link : Option String
  leading : Option Dim.Sp
  decorations : Layout.Decorations
  ground : Option Ir.Color
  deriving BEq, Repr

/-- Body glyphs in paint order, retaining every field of `ShippedGlyph`.
RoleShaping holds this coordinate arithmetic to the existing artifact pen
model and checks the emitted PDF with that model's unchanged spelling bound. -/
def shippedBodyGlyphs (out : Layout.Out) : Array ShippedGlyph := Id.run do
  let mut acc := #[]
  for (page, p) in out.pages.zipIdx do
    for (line, l) in (page.lines.filter (!·.furniture)).zipIdx do
      let mut x := line.x
      for seg in line.segs do
        match seg with
        | .run face color link width gs size metrics decorations raise ground _ =>
          let mut dx := 0
          for (glyph, scalar, advance) in gs do
            acc := acc.push {
              page := p, line := l, face, glyph, scalar
              x := x + dx * (1000 + line.expand) / 1000
              y := line.y - raise, advance, size, expand := line.expand
              color, link, leading := metrics.leading, decorations, ground }
            dx := dx + advance
          x := x + width
        | .gap width _ | .decoratedGap width _ _ | .rule width _ _ _
          | .decoration _ width _ _ _ | .image _ width _ => x := x + width
        | .poly _ _ => pure ()
  return acc

namespace ShippedInk

/-- Outline hull in page coordinates with y pointing upward. Control
points are included; these are measured bounds, not raster extrema.
Neither baseline zero nor logical advance belongs to the hull. -/
structure InkBounds where
  left : Dim.Sp
  bottom : Dim.Sp
  right : Dim.Sp
  top : Dim.Sp
  deriving BEq, Repr

def InkBounds.shift (b : InkBounds) (dx dy : Dim.Sp) : InkBounds :=
  { left := b.left + dx, right := b.right + dx
    bottom := b.bottom + dy, top := b.top + dy }

def outlinePoints : Ink.Cmd → Array (Int × Int)
  | .move x y | .line x y => #[(x, y)]
  | .quad cx cy x y => #[(cx, cy), (x, y)]
  | .cube x₁ y₁ x₂ y₂ x y => #[(x₁, y₁), (x₂, y₂), (x, y)]

def InkBounds.union (a b : InkBounds) : InkBounds :=
  { left := min a.left b.left, bottom := min a.bottom b.bottom
    right := max a.right b.right, top := max a.top b.top }

/-- Disjoint interiors of quantized outline hulls. This is a conservative
ink-separation check, not a claim that intersecting hulls imply raster contact. -/
def InkBounds.disjoint (a b : InkBounds) : Bool :=
  a.right ≤ b.left || b.right ≤ a.left || a.top ≤ b.bottom || b.top ≤ a.bottom

def InkBounds.inRoom (b : InkBounds) (left right : Dim.Sp) : Bool :=
  left ≤ b.left && b.right ≤ right

def polygonHull (points : Array (Dim.Sp × Dim.Sp)) : Option InkBounds := do
  let (x, y) ← points[0]?
  return points.foldl (fun b (px, py) => b.union ⟨px, py, px, py⟩) ⟨x, y, x, y⟩

/-- Decode the shipped glyph independently of the layout's bounds helper.
Every point uses its actual pen position, size and baseline. Missing
outline evidence fails; an empty or zero-area hull contributes no ink. -/
def glyphInk (fonts : Font.FontSet) (g : ShippedGlyph) :
    Except String (Option InkBounds) := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  if font.unitsPerEm == 0 then throw "target face has zero units per em"
  if g.expand != 0 then throw "target glyph unexpectedly expands"
  let some cmds := font.inkSrc.get.cmdsAt g.glyph | throw "target outline is missing"
  let upem : Int := font.unitsPerEm
  let mut bounds : Option InkBounds := none
  for cmd in cmds do
    for (x, y) in outlinePoints cmd do
      let px := g.x + x * g.size / upem
      let py := -g.y + y * g.size / upem
      let point : InkBounds := ⟨px, py, px, py⟩
      bounds := some (match bounds with | none => point | some b => b.union point)
  return bounds.filter fun b => b.left < b.right && b.bottom < b.top

/-- Whether a shipped glyph has outline commands. Empty-outline spaces
still belong to the source census and advance the pen, but paint no ink.
An undecodable outline is a failed measurement rather than an empty one. -/
def glyphPaints (fonts : Font.FontSet) (g : ShippedGlyph) : Except String Bool := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  let some cmds := font.inkSrc.get.cmdsAt g.glyph | throw "target outline is missing"
  return !cmds.isEmpty

/-- Union only the target glyphs' ink, ignoring decoded empty outlines.
Starting from the first painted glyph is essential for an annotation whose
entire visible contents are raised; a space's baseline must not join it. -/
def targetInk (fonts : Font.FontSet) (glyphs : Array ShippedGlyph) :
    Except String InkBounds := do
  let mut bounds : Option InkBounds := none
  for g in glyphs do
    if let some b ← glyphInk fonts g then
      bounds := some (match bounds with
        | none => b
        | some old => old.union b)
  let some ink := bounds | throw "target has no painted glyphs"
  return ink

/-- Polygon origins from the actual line pen, advancing through every
width-bearing segment, including rules. Vertices stay relative to that pen. -/
def polygonPens (line : Layout.LineOut) : Array (Dim.Sp × Array (Dim.Sp × Dim.Sp)) := Id.run do
  let mut pen := line.x
  let mut polys := #[]
  for seg in line.segs do
    match seg with
    | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
    | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ =>
      pen := pen + w
    | .poly points _ => polys := polys.push (pen, points)
  return polys

/-- Shipped polygons in the same upward page coordinates as `glyphInk`. -/
def polygonsAt (line : Layout.LineOut) : Array (Array (Dim.Sp × Dim.Sp)) :=
  (polygonPens line).map fun (pen, points) =>
    points.map fun (x, y) => (pen + x, y - line.y)

end ShippedInk

/-- Gaps that stand before glyph ink, excluding a paragraph's closing fill. -/
def metricInnerGaps (l : Layout.LineOut) : Array Dim.Sp := Id.run do
  let mut out : Array Dim.Sp := #[]
  let mut pending : Array Dim.Sp := #[]
  for s in l.segs do
    match s with
    | .gap w _ | .decoratedGap w _ _ => pending := pending.push w
    | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
      unless glyphs.isEmpty do
        out := out ++ pending
        pending := #[]
    | .rule _ _ _ _ | .decoration _ _ _ _ _ | .poly _ _ | .image _ _ _ => pure ()
  return out

/-- Painted inline rules on shipped body pages. -/
def metricRuleSegs (out : Layout.Out) : Array (Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .rule w h raise color => some (w, h, raise, color)
    | _ => none

def metricDecorationSegs (out : Layout.Out) :
    Array (Ir.Decoration × Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .decoration kind w h raise color => some (kind, w, h, raise, color)
    | _ => none

/-- Sizes of glyph runs on shipped body pages. -/
def metricRunSizes (out : Layout.Out) : Array Dim.Sp :=
  (bodyLines out).flatMap fun l => l.segs.filterMap fun s => match s with
    | .run _ _ _ _ glyphs size _ _ _ _ _ => if glyphs.isEmpty then none else some size
    | _ => none

/-- A compact article wrapper for metric command checks. -/
def metricDoc (body : String) : String :=
  "\\documentclass{article}\n\\begin{document}\n" ++ body ++ "\n\\end{document}"

/-- A metric check's source through elaboration and shipped layout. -/
def metricOut (oneFace : Font.FontSet) (body : String) : Layout.Out :=
  layoutOf oneFace (elabStr (metricDoc body)).1

/-- Every scalar a laid-out document inks, and its layout diagnostics. -/
def inkedScalars (fs : Font.FontSet) (src : String) : Array Char × Array Diag :=
  let out := layoutOf fs (elabStr src).1
  let ink := out.pages.flatMap fun p => p.lines.flatMap fun l => l.segs.flatMap fun s =>
    match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.map (·.2.1)
    | _ => #[]
  (ink, out.diags)

/-- The glyphs a source's body lines ship, in page order — the instrument for
a claim about what a page shows, read off `Layout.Out` rather than an IR
dump. `geom` defaults to the document's own page; pass one to judge a source
against a fixed measure. -/
def pageTextOf (fonts : Font.FontSet) (src : String)
    (geom : Option Layout.Geom := none) : String :=
  let (d, _) := elabStr src
  String.join ((bodyLines (layoutOf fonts d (geom.getD (Layout.Geom.ofPage d.page)))).toList.map
    (lineText ·))

/-- The same over *every* line, furniture included: what a title bar or a
running foot ships is on the page too, so an absence claim belongs here
rather than in `pageTextOf`. -/
def allTextOf (fonts : Font.FontSet) (src : String)
    (geom : Option Layout.Geom := none) : String :=
  let (d, _) := elabStr src
  String.join ((allLines (layoutOf fonts d (geom.getD (Layout.Geom.ofPage d.page)))).toList.map
    (lineText ·))

/-- Both complete artifacts of a synthetic source, with their diagnostics
and visible HTML text. Comparing the pages and serialized typed tree keeps
positions, paragraph boundaries, attributes and whitespace observable. -/
def sourceArtifacts (fonts : Font.FontSet) (source : String) :
    Array Diag × Layout.Out × String × String :=
  let (doc, ds) := elabStr source
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  (ds ++ out.diags ++ hds, out, Html.document "en" head tree,
    shownTextList "" tree.toList)

mutual
/-- A control's `{block}`s spelled as the box a tcolorbox lowers to
(`Tcolorbox.boxEnv`): the native block surface, in the environment only the
lowering opens, so a lowered box compares against the block it is written
as. -/
-- conserves: none — renames an environment in a test's control raws.
def boxedRaw : Parse.Raw → Parse.Raw
  | .env n body p =>
    .env (if n == "block" then Tcolorbox.boxEnv else n) (boxedRaws #[] body.toList) p
  | .group body p => .group (boxedRaws #[] body.toList) p
  | .math d body p => .math d (boxedRaws #[] body.toList) p
  | .word s p => .word s p
  | .space => .space
  | .par p => .par p
  | .ctrl n p => .ctrl n p
  | .sym c p => .sym c p
  | .verb e s p => .verb e s p

def boxedRaws (acc : Array Parse.Raw) : List Parse.Raw → Array Parse.Raw
  | [] => acc
  | r :: rest => boxedRaws (acc.push (boxedRaw r)) rest
end

/-- `sourceArtifacts` of a control whose `{block}`s stand for lowered boxes
(`boxedRaw`). -/
def boxedSourceArtifacts (fonts : Font.FontSet) (source : String) :
    Array Diag × Layout.Out × String × String :=
  let (toks, lexDiags) := Lex.lex "t" source
  let (raws, parseDiags) := Parse.parse "t" toks
  let (doc, ds) := Elab.runRaws "t" (boxedRaws #[] raws.toList) (lexDiags ++ parseDiags)
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  (ds ++ out.diags ++ hds, out, Html.document "en" head tree,
    shownTextList "" tree.toList)

/-- A source and its literal control must ship the same visible text in
both artifacts, without losing a construct. Whitespace is ignored here:
these checks judge argument and branch selection, not line breaking. -/
def sourceTextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label source control : String) : IO Unit := do
  let ink (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let (doc, ds) := elabStr source
  let (_, tree, hds) := HtmlDoc.emitTree {} doc
  let (_, expectedTree, _) := HtmlDoc.emitTree {} (elabStr control).1
  check ref (label ++ ": no loss") ((ds ++ hds).all (·.severity == .note))
  check ref (label ++ ": shipped layout")
    (ink (allTextOf fonts source) == ink (allTextOf fonts control))
  check ref (label ++ ": typed HTML")
    (ink (shownTextList "" tree.toList) == ink (shownTextList "" expectedTree.toList))

/-- Elaboration diagnostics of a source. -/
def dvE (src : String) : Array Diag := (elabStr src).2

/-- Spans carrying more than one diagnostic, as `(code, code)` pairs with the
count — the mechanical first cut the user asked for, needing no judgement
about any rule: group every diagnostic by its cause site and look at the
groups larger than one. -/
def siteCollisions (ds : Array Diag) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for d in ds do
    for e in ds do
      if d.span.isSome && d.span == e.span && d.code < e.code then
        let pair := (d.code, e.code)
        unless out.contains pair do out := out.push pair
  return out

/-- The shipped-page census of a source laid out with `fonts`: which ink
each page carries, the artifact a claim about a branch or a label reads. -/
def censusOfSrc (fonts : Font.FontSet) (src : String) : Array CensusPage :=
  let (doc, _) := elabStr src
  censusOf (coveredColorsOf doc) (layoutOf fonts doc)

/-- The laid-out lines of a source, baseline and text: what a claim that two
spellings set one page reads. -/
def pageLines (fonts : Font.FontSet) (src : String) : Array (Array (Dim.Sp × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.text))

/-- Every shipped line of a source, position, size and text: what a claim
that two spellings ship one page reads, horizontal placement included. -/
def shippedLines (fonts : Font.FontSet) (src : String) :
    Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (censusOfSrc fonts src).flatMap fun p => p.lines.map fun l => (l.x, l.y, l.size, l.text)

/-- A source elaborated as the driver elaborates it: against the label
measurement layout sets with (`Layout.labelMetric`), so a node's extent is
measured from its letters rather than taken as nothing. -/
def elabMeasured (fonts : Font.FontSet) (s : String) : Ir.Doc × Array Diag :=
  let (toks, lds) := Lex.lex "t" s
  let (raws, pds) := Parse.parse "t" toks
  Elab.runRaws "t" raws (lds ++ pds)
    (Layout.labelMetric (Layout.Geom.ofPage (Elab.run "t" s).1.page) fonts)

/-- Does a block of the document's title block satisfy `p`? The block may
stand inside its alignment wrapper, so the probe looks one level into
`.center`. -/
def inTitleBlock (doc : Ir.Doc) (p : Ir.Block → Bool) : Bool :=
  doc.body.any fun b => p b ||
    (match b with | .center xs => xs.any p | _ => false)

/-- Diagnostics after layout too, through the same pre-layout alphabet
resolution as every test artifact. -/
def dvL (fonts : Font.FontSet) (src : String) : Array Diag :=
  let (doc, ds) := elabStr src
  ds ++ (layoutOf fonts doc).diags

/-- Diagnostics after the HTML backend. -/
def dvH (src : String) : Array Diag :=
  let (doc, ds) := elabStr src
  ds ++ (HtmlDoc.emit {} doc).2

/-- A one-face set: every slot and variant maps to index 0. Both
fontSuiteChecks and the layout dispatch build their set through this one
def, so the two can never drift. -/
def oneFaceOf (font : Font.Font) : Font.FontSet := {
  fonts := #[font]
  index := ((List.range 3).flatMap fun slot =>
    [((slot, 400, false), 0), ((slot, 700, false), 0),
     ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray
}

/-- The shipped Fira Sans as a one-face set (`oneFaceOf`): the face the
frame and footline checks lay their invented decks out in, as their
lualatex measurements loaded it for every face; `none` where it does not
parse. -/
def shippedFira : IO (Option Font.FontSet) := do
  match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
  | .ok f => pure (some (oneFaceOf f))
  | .error _ => pure none

/-- The shipped Fira Sans as the one face it is, for a check that builds its
own set from it; `none` where it does not parse. -/
def shippedFiraFont : IO (Option Font.Font) := do
  match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
  | .ok f => pure (some f)
  | .error _ => pure none

/-- A measurement in thousandths of a point, as the frame checks write
lualatex's baselines and their tolerances. -/
def ptMilli (milli : Int) : Dim.Sp := Dim.pt 1 * milli / 1000

/-- Two lengths within `slack` of each other. -/
def withinSp (slack a b : Dim.Sp) : Bool := a - b ≤ slack && b - a ≤ slack

/-- Two faces in two slots: the roman slot (0) and the sans slot (1) hold
different files, so a claim about *which family* ink set in has something
to read. `oneFaceOf` maps every slot to one file and cannot tell a serif
run from a sans one — the set a font-role fact needs is this one.
`CensusLine.runFonts` is the channel. -/
def twoSlotOf (roman sans : Font.Font) : Font.FontSet := {
  fonts := #[roman, sans]
  index := ((List.range 3).flatMap fun slot =>
    let f := if slot == 1 then 1 else 0
    [((slot, 400, false), f), ((slot, 700, false), f),
     ((slot, 400, true), f), ((slot, 700, true), f)]).toArray
}

/-- Two faces: the text slots (0 and 1) one file and the typewriter slot
(2) another, so code and prose are told apart by the face a run sets in. -/
def monoSlotOf (text mono : Font.Font) : Font.FontSet := {
  fonts := #[text, mono]
  index := ((List.range 3).flatMap fun slot =>
    let f := if slot == 2 then 1 else 0
    [((slot, 400, false), f), ((slot, 700, false), f),
     ((slot, 400, true), f), ((slot, 700, true), f)]).toArray
}

mutual

/-- The stylesheet text the typed tree ships, in tree order. -/
def treeCssList (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => treeCssList (treeCssOne acc n) rest

def treeCssOne (acc : String) : Html.Node → String
  | .style css => acc.append css
  | .elem _ _ kids => treeCssList acc kids.toList
  | .text _ => acc
  | .script _ _ => acc

end

/-- The declarations of every stylesheet rule whose selector is `sel`
exactly, in order: the texts between their braces. -/
def cssRulesOf (css sel : String) : List String :=
  (css.splitOn "}").filterMap fun chunk =>
    match chunk.splitOn "{" with
    | [s, decls] =>
      if (s.splitOn "\n").getLast!.trimAscii.toString == sel then some decls else none
    | _ => none

/-- The declarations of the first stylesheet rule whose selector is `sel`
exactly: the text between its braces. -/
def cssRuleOf (css sel : String) : Option String := (cssRulesOf css sel).head?

/-- A length in sp as thousandths of a point, rounded to nearest: what the
layout checks print and compare against a reference's three decimals. -/
def spMilli (d : Dim.Sp) : Int := (d * 1000 + 32768) / 65536

/-- A selector list's parts, split at its top-level commas (a comma inside
`:is(…)` or `:has(…)` belongs to its part). -/
def cssSelParts (sel : String) : List String := Id.run do
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in sel.toList do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if c == ',' && depth == 0 then
      parts := parts.push cur.trimAscii.toString
      cur := ""
    else cur := cur.push c
  return (parts.push cur.trimAscii.toString).toList

/-- A CSS length in `rem` as thousandths of a rem — the unit every boundary
of the gap sheet is written in (`HtmlDoc.screenMilli`) — or nothing for any
other spelling. -/
def remMilliOf (value : String) : Option Int := do
  let value := value.trimAscii.toString
  guard (value.endsWith "rem")
  let (m, sc) ← Decl.parseDecimal (value.dropEnd 3).toString
  return m * 1000 / (sc : Int)

/-- Read a CSS stage length and compare its share to the shipped PDF
length. One printed milli-percent is the rounding bound, independently of
viewport height. -/
def cssStageLength (style key : String) (length height : Dim.Sp) : Bool :=
  ((style.splitOn ";").findSome? fun decl => do
    let [name, value] := decl.splitOn ":" | none
    if name.trimAscii.toString != key then none else
    let value := value.trimAscii.toString
    if !value.endsWith "vh" then none else
    let (m, sc) ← Decl.parseDecimal (value.dropEnd 2).toString
    return m * 1000 / (sc : Int)).any fun m =>
      m * height ≤ length * 100000 && length * 100000 < (m + 1) * height

/-- The read-side census of produced PDF bytes, for a claim about what a
file carries (fonts embedded, filters, page count) — `PdfCensus.census`
with its refusal surfaced as the test's own failure text. -/
def pdfCensusOf (pdf : ByteArray) : Except String PdfCensus.Census :=
  PdfCensus.census pdf


mutual

/-- Every element of a tree whose tag `want` accepts, in document order.
Keep the typed node so guards can inspect child order as well as attributes. -/
def elemNodesOne (want : String → Bool) (acc : Array Html.Node) :
    Html.Node → Array Html.Node
  | .elem tag attrs kids =>
    elemNodesList want (if want tag then acc.push (.elem tag attrs kids) else acc) kids.toList
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc

def elemNodesList (want : String → Bool) (acc : Array Html.Node) :
    List Html.Node → Array Html.Node
  | [] => acc
  | k :: rest => elemNodesList want (elemNodesOne want acc k) rest

end

/-- Attribute guards are a projection of the same element census. -/
def elemAttrsList (want : String → Bool) (acc : Array (String × Array (String × String)))
    (nodes : List Html.Node) : Array (String × Array (String × String)) :=
  (elemNodesList want #[] nodes).foldl (fun a n => match n with
    | .elem tag attrs _ => a.push (tag, attrs)
    | _ => a) acc

def elemAttrsOne (want : String → Bool) (acc : Array (String × Array (String × String)))
    (node : Html.Node) : Array (String × Array (String × String)) :=
  elemAttrsList want acc [node]

/-- The formulas of an emitted tree, in document order: the elements that
carry their source in `data-tex` — a paragraph's `math` root, a picture
label's row inside its carrier. -/
def formulaElems (body : Array Html.Node) : Array Html.Node :=
  (elemNodesList (fun _ => true) #[] body.toList).filter fun n =>
    match n with
    | .elem _ attrs _ => (HtmlDoc.attrOf? attrs "data-tex").isSome
    | _ => false

/-- The pictures a document's body draws natively, in document order. -/
def docPictures (doc : Ir.Doc) : Array Ir.Pic.Picture :=
  Ir.foldBlocks (fun acc b => match b with
    | .picture p => acc.push p
    | _ => acc) (fun acc _ => acc) #[] doc.body

/-- An article whose one picture, drawn by the engine, holds a node at
(-1,1) labelled `label` under the node options `opts`. -/
def mathLabelSource (label opts : String) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "\\begin{tikzpicture}\n\\node[" ++ opts ++ "] at (-1,1) {" ++ label ++
  "};\n\\end{tikzpicture}\n\\end{document}"

/-- An article whose one picture, drawn by the engine, is a drawn node around
`content`. -/
def drawnNodeSource (content : String) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "\\begin{tikzpicture}\n\\node[draw] at (0,0) {" ++ content ++
  "};\n\\end{tikzpicture}\n\\end{document}"

/-- Every value the elements `want` accepts declare for attribute `key`, in
document order: `elemAttrsOne`'s elements, read for one attribute. -/
def attrValuesOf (want : String → Bool) (key : String) (n : Html.Node) : Array String :=
  (elemAttrsOne want #[] n).filterMap fun (_, attrs) => (attrs.find? (·.1 == key)).map (·.2)


/-- Every innermost declaration block a stylesheet carries, as its selector
text paired with its declarations. Brace-depth scanned rather than split on
`}`, so a nested at-rule's inner blocks come out under their own selectors
(the backend writes the paged deck's bar inside `@media screen`) and the
at-rule's prelude never reads as one. Total by construction: the loop is
bounded by the length and every step advances the position. -/
def artCssBlocks (css : String) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  let mut sels : Array String := #[]
  let mut cur := ""
  for c in css.toList do
    if c == '{' then
      sels := sels.push cur.trimAscii.toString
      cur := ""
    else if c == '}' then
      let decls := cur.trimAscii.toString
      if decls.contains ':' then
        out := out.push ((sels.back?.getD "").trimAscii.toString, decls)
      sels := sels.pop
      cur := ""
    else
      cur := cur.push c
  return out

/-- The declarations of every innermost block a stylesheet carries for the
selector `sel` exactly, nested at-rule blocks included (`artCssBlocks`). -/
def cssBlocksFor (css sel : String) : List String :=
  ((artCssBlocks css).toList.filter (·.1 == sel)).map (·.2)

/-- The value the first declaration of `key` in a declaration list gives,
if one does; a value may hold a colon of its own (`url(data:…)`). -/
def cssDeclOf (decls key : String) : Option String :=
  (decls.splitOn ";").findSome? fun d =>
    match d.splitOn ":" with
    | name :: rest =>
      if name.trimAscii.toString == key then some (":".intercalate rest).trimAscii.toString
      else none
    | [] => none

/-- A selector list's top-level parts, a comma inside a parenthesized
argument (`:is(h1, h2)`) kept in its part. -/
def cssSelectorParts (sel : String) : List String := Id.run do
  let mut parts : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in sel.toList do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if c == ',' && depth == 0 then
      parts := parts.push cur.trimAscii.toString
      cur := ""
    else cur := cur.push c
  return (parts.push cur.trimAscii.toString).toList


/-! ### The natbib fixtures the bibliography check blocks share -/

/-- The synthetic bibliography natbib's rows cite: invented people and
venues, one entry per name shape a citation prints differently — three
authors (`et al.`, and all three starred), one, two, and a lowercase
particle (`\Citet` capitalizes it). -/
def natbibBib : String :=
  "@article{alpha2019, author = {Ann Alpha and Bob Beta and Cy Gamma},\n\
    title = {A study of invented widgets}, journal = {Journal of Examples},\n\
    year = {2019}, volume = {3}, number = {2}, pages = {10--20}}\n\
  @book{delta2021, author = {Dee Delta}, title = {Placeholder Methods},\n\
    publisher = {Example Press}, year = {2021}}\n\
  @inproceedings{eps2020, author = {Eve Epsilon and Finn Zeta},\n\
    title = {On synthetic benchmarks},\n\
    booktitle = {Proceedings of the Example Workshop}, year = {2020}, pages = {1--8}}\n\
  @article{pome2018, author = {Quill de Pome}, title = {Lowercase particles},\n\
    journal = {Example Letters}, year = {2018}}\n"

/-- Entries whose label names and year coincide, so plainnat.bst's
`forward.pass`/`reverse.pass` give them letters, one more year by the same
names, one other author, and two entries the `\nocite` rows name:
invented people and titles. -/
def natbibLabelBib : String :=
  "@article{gam2019a, author = {Gil Gamma and Hal Eta}, title = {An early invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2019b, author = {Gil Gamma and Hal Eta}, title = {A later invented result},\n\
    journal = {Journal of Examples}, year = {2019}}\n\
  @article{gam2020, author = {Gil Gamma and Hal Eta}, title = {A third invented result},\n\
    journal = {Journal of Examples}, year = {2020}}\n\
  @book{iota2018, author = {Ivy Iota}, title = {An Invented Book}, publisher = {Example Press},\n\
    year = {2018}}\n\
  @misc{kap2017, author = {Kai Kappa}, title = {An invented note}, year = {2017}}\n\
  @misc{lam2016, author = {Lu Lambda}, title = {An entry no citation names}, year = {2016}}\n"

/-- The calls as one document, each in its own paragraph `Lk <call> end.`;
the style is declared in the preamble, where natbib reads it back at
`\begin{document}`. -/
def natbibSrc (pre style : String) (calls : List String) : String := Id.run do
  let mut body := ""
  for call in calls, k in [1:calls.length + 1] do
    body := body ++ s!"L{k} {call} end.\n\n"
  return s!"\\documentclass\{article}\n{pre}\n\\bibliographystyle\{{style}}\n\
    \\begin\{document}\n{body}\\bibliography\{refs}\n\\end\{document}\n"

/-- An HTML page's text as a reader gets it: tags dropped, the entities
the escaper writes read back, a no-break space a space. -/
def htmlVisibleText (page : String) : String := Id.run do
  let mut out := ""
  let mut inTag := false
  for c in page.toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return ((((out.replace "&lt;" "<").replace "&gt;" ">").replace "&nbsp;" " ").replace
    "&amp;" "&").replace "\u00A0" " "

/-- The reference list's shipped lines, one array per entry: the lines after
the References heading that set glyphs (a link's underline ships as a
sibling line of rules), split where the leaf changes. -/
def bibEntryLines (lines : Array Layout.LineOut) : Array (Array Layout.LineOut) := Id.run do
  let start := ((lines.findIdx? (lineText · == "References")).map (· + 1)).getD lines.size
  let mut out : Array (Array Layout.LineOut) := #[]
  let mut cur : Array Layout.LineOut := #[]
  for l in (lines.extract start lines.size).filter hasGlyphRun do
    if !cur.isEmpty && cur.back?.map (·.leaf) != some l.leaf then
      out := out.push cur
      cur := #[]
    cur := cur.push l
  return if cur.isEmpty then out else out.push cur

namespace Tests.World

open LeanTex.Cli.World

/-- A world read off a trace, `dflt` answering every question the trace
does not hold. -/
def traceWorld (tr : List Fact) (dflt : (q : Ask) → Reply q) : (q : Ask) → Reply q :=
  fun q => match tr.find? (·.1 == q) with
    | some ⟨q', r⟩ => if h : q' = q then h ▸ r else dflt q
    | none => dflt q

def quiet : (q : Ask) → Reply q
  | .env _ => none
  | .cwd => .error .absent
  | .stat _ => .error .absent
  | .readFile _ => .error .absent
  | .listDir _ => .error .absent
  | .run _ => { ran := .unstarted "unasked", out := "", err := "", complete := false, outputs := #[] }
  | .writeAtomic .. => .error .absent
  | .createDirAll _ => .error .absent

/-- The host with PATH and the working directory replaced: every other
question is the machine's. -/
def hybrid (path : Option String) (cwd : Except Failure String) : (q : Ask) → BaseIO (Reply q)
  | .env "PATH" => pure path
  | .cwd => pure cwd
  | q => Host.answer q

def under {α : Type} (path : String) (cwd : Except Failure String) (p : Prog α) : BaseIO α :=
  p.runM (hybrid (some path) cwd)

end Tests.World
