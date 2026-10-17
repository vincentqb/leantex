module

public import LeanTex.Cli.FontDiscovery
public import LeanTex.Cli.RunBounded
public import LeanTex
public import LeanTex.Core.Flate.BitWriter
public import LeanTex.Core.Flate.Huffman
public import LeanTex.Core.HtmlDoc
public import Lean.Data.Json.Parser
public import Lean.Data.Json.FromToJson.Basic
public import Tests.LightCss
public import Tests.Support.Check
public import Tests.Support.Rand

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

/-- The one paint every glyph of a run shares, where they share one. -/
def onePaint {α : Type} [BEq α] (paint : Option (Array α)) : Option α :=
  paint.bind fun p => p[0]?.bind fun first => if p.all (· == first) then some first else none

def bytes (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- A zlib stream of one final dynamic block over these code lengths, each written in its canonical
code, then `data`'s literal/length symbols `(0, s, _)`, distance symbols `(1, s, _)` and raw bits
`(2, bits, width)`, with no Adler-32. -/
def zlibDynamic (cl lit dist : Array Nat) (data : Array (Nat × Nat × Nat)) : ByteArray := Id.run do
  let order := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
  let ordered : Array Nat := order.map fun s => cl[s]?.getD 0
  let mut n := ordered.size
  for _ in [0:15] do
    if n > 4 && ordered[n - 1]?.getD 0 == 0 then n := n - 1
  let mut w : Flate.Bw := { out := ByteArray.empty, bits := 0, nbits := 0 }
  w := ((((w.push 1 1).push 2 2).push (lit.size - 257) 5).push (dist.size - 1) 5).push (n - 4) 4
  for v in ordered.extract 0 n do w := w.push v 3
  let clCodes := Flate.canonCodes cl
  for v in lit ++ dist do w := w.push (clCodes[v]?.getD 0) (cl[v]?.getD 0)
  let litCodes := Flate.canonCodes lit
  let distCodes := Flate.canonCodes dist
  for (kind, v, k) in data do
    w := if kind == 0 then w.push (litCodes[v]?.getD 0) (lit[v]?.getD 0)
      else if kind == 1 then w.push (distCodes[v]?.getD 0) (dist[v]?.getD 0)
      else w.push v k
  return bytes [0x78, 0x01] ++ w.flush

/-- Lengths over `n` symbols, each listed symbol its length and the rest none. -/
def lengthsOf (n : Nat) (assign : List (Nat × Nat)) : Array Nat :=
  (Array.range n).map fun s => ((assign.find? (·.1 == s)).map (·.2)).getD 0

/-- A zlib stream that inflates to zeros past `PdfRead.maxDecoded`: one literal, then length-258
matches one byte back, each two bits. -/
def overBudgetZeros (_ : Unit) : ByteArray :=
  let runs := PdfRead.maxDecoded / 258 + 1
  let data : Array (Nat × Nat × Nat) :=
    #[(0, 0, 0)] ++ (Array.replicate runs #[(0, 285, 0), (1, 0, 0)]).flatten ++ #[(0, 256, 0)]
  zlibDynamic (Array.replicate 16 4 ++ #[0, 0, 0]) (lengthsOf 286 [(0, 2), (256, 2), (285, 1)])
    #[1] data

def svgDocument (body : String) (width : Nat := 20) (height : Nat := 20) : ByteArray :=
  (s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\">" ++
    body ++ "</svg>").toUTF8

def svgBoundaryError (result : Except String α) : Bool :=
  match result with
  | .error err => (err.splitOn "SVG resource boundary").length > 1
  | .ok _ => false

/-- An independent encoder of `data` as a `data:` URL of type `mime`, for captured resource
checks. -/
def htmlDataOracle (mime : String) (data : ByteArray) : IO String :=
  IO.FS.withTempDir fun dir => do
    let path := dir / "payload"
    IO.FS.writeBinFile path data
    let out ← IO.Process.output { cmd := "base64", args := #["-w0", path.toString] }
    unless out.exitCode == 0 do
      throw <| IO.userError "the HTML containment byte oracle requires base64"
    return "data:" ++ mime ++ ";base64," ++ out.stdout

/-- An artifact's `data:` URL decoded to its type and bytes, kept binary. -/
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

/-- The bytes of the page's inline SVG reference, decoded independently. -/
def svgPublishedAsset (html tag attr : String) : IO (String × ByteArray) := do
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

/-- The invented figures under `testdata/svg` and `testdata/corpus/figures`, in name order. -/
def svgFixtureFiles : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for dir in ["testdata/svg", "testdata/corpus/figures"] do
    for e in (← System.FilePath.readDir dir).qsort (·.fileName < ·.fileName) do
      if e.fileName.endsWith ".svg" then out := out.push e.path
  return out

/-- A PDF of the given objects' bytes, numbered from 1 with the first the catalog, each at the
generation `gens` gives it or zero, under a classic cross-reference table. -/
def syntheticPdfBin (objects : Array ByteArray) (trailerExtra : String := "") (gens : Array Nat := #[]) :
    ByteArray := Id.run do
  let mut out := "%PDF-1.7\n".toUTF8
  let mut offsets : Array Nat := #[]
  for (object, i) in objects.zipIdx do
    offsets := offsets.push out.size
    out := out ++ s!"{i + 1} {gens[i]?.getD 0} obj\n".toUTF8 ++ object ++ "\nendobj\n".toUTF8
  let xref := out.size
  out := out ++ s!"xref\n0 {objects.size + 1}\n0000000000 65535 f \n".toUTF8
  for (offset, i) in offsets.zipIdx do
    let digits := toString offset
    let gen := toString (gens[i]?.getD 0)
    out := out ++ ("".pushn '0' (10 - digits.length) ++ digits ++ " " ++ "".pushn '0' (5 - gen.length) ++
      gen ++ " n \n").toUTF8
  return out ++ s!"trailer\n<< /Size {objects.size + 1} /Root 1 0 R {trailerExtra}>>\n\
    startxref\n{xref}\n%%EOF\n".toUTF8

/-- `syntheticPdfBin` over the objects' spellings. -/
def syntheticPdf (objects : Array String) (trailerExtra : String := "") (gens : Array Nat := #[]) :
    ByteArray :=
  syntheticPdfBin (objects.map String.toUTF8) trailerExtra gens

/-- A stream object over bytes, `dict` its dictionary's other entries. -/
def streamObjBin (body : ByteArray) (dict : String := "") : ByteArray :=
  s!"<< /Length {body.size} {dict}>>\nstream\n".toUTF8 ++ body ++ "\nendstream".toUTF8

/-- A stream object's spelling. -/
def streamObj (body : String) (dict : String := "") : String :=
  s!"<< /Length {body.utf8ByteSize} {dict}>>\nstream\n{body}\nendstream"

/-- A one-page figure whose text is in an embedded Type 1 program, which the importer names a
loss. -/
def type1FigurePdf : ByteArray := syntheticPdf #[
  "<< /Type /Catalog /Pages 2 0 R >>",
  "<< /Type /Pages /Kids [3 0 R] /Count 1 >>",
  "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 100 50] /Contents 4 0 R \
    /Resources << /Font << /F1 5 0 R >> >> >>",
  streamObj "0 0 1 rg 10 10 30 20 re f BT /F1 12 Tf 50 20 Td (x) Tj ET",
  "<< /Type /Font /Subtype /Type1 /BaseFont /Placeholder /FirstChar 120 /LastChar 120 \
    /Widths [500] /FontDescriptor 6 0 R >>",
  "<< /Type /FontDescriptor /FontName /Placeholder /Flags 32 /FontFile 7 0 R >>",
  streamObj "%!PS-AdobeFont-1.0: Placeholder" "/Length1 31 /Length2 0 /Length3 0 "]

/-- `svgCanvasPdf`'s pages under a trailer declaring encryption, which the figure importer
refuses. -/
def encryptedCanvasPdf : ByteArray :=
  let stream (ink : String) := s!"<< /Length {ink.utf8ByteSize} >>\nstream\n{ink}\nendstream"
  syntheticPdf #[
    "<< /Type /Catalog /Pages 2 0 R >>",
    "<< /Type /Pages /Kids [3 0 R 5 0 R] /Count 2 /Resources << >> >>",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 120 80] /Contents 4 0 R >>",
    stream "0 0 1 rg 0 0 120 80 re f",
    "<< /Type /Page /Parent 2 0 R /MediaBox [0 0 60 120] /Contents 6 0 R >>",
    stream "1 0 0 rg 0 0 60 120 re f",
    "<< /Filter /Standard /V 1 /R 2 /O <00> /U <00> /P -4 >>"] "/Encrypt 7 0 R "

/-- A two-page sequence: a wide blue first frame and a tall red poster. -/
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

/-- PNG row filters applied forward (ISO/IEC 15948 §9.2), one type per row by `ft`. -/
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

/-! Synthetic PNGs, byte by byte: the decoder reads structure, not CRCs or pixel data, so CRC slots
are zero. -/

def be32 (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

def pngChunk (tag : String) (data : List UInt8) : List UInt8 :=
  be32 data.length ++ (tag.toList.map fun c => UInt8.ofNat c.toNat) ++ data ++ [0, 0, 0, 0]

def pngIhdr (w h bd ct interlace : Nat) : List UInt8 :=
  be32 w ++ be32 h ++ [UInt8.ofNat bd, UInt8.ofNat ct, 0, 0, UInt8.ofNat interlace]

def pngSigBytes : List UInt8 := [137, 80, 78, 71, 13, 10, 26, 10]

def mkPng (chunks : List UInt8) : ByteArray := bytes (pngSigBytes ++ chunks)

/-- The colour-key ranges a plan carries, empty when none. -/
def planKey (pl : Image.Plan) : Array Nat :=
  match pl.alpha with
  | .colorKey ks => ks
  | .opaque => #[]
  | .soft _ _ => #[]

/-- Does `needle` occur verbatim inside `hay`? -/
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

def toks (s : String) : List Lex.Tok :=
  ((Lex.lex "t" s).1.map (·.tok)).toList

def elabStr (s : String) : Ir.Doc × Array Diag :=
  Elab.run "t" s

/-- A source elaborated with its locations kept, as a build lays it out. -/
def elabLocated (file src : String) : Ir.Doc × Array Diag :=
  let prepared := Elab.prepare file (Parse.parse file (Lex.lex file src).1).1
  let (doc, ds, _) := Elab.runPrepared file prepared
  (doc, ds)

/-- The first elaborated formula in a block's paragraphs, equations or centred displays. -/
def blockFormula (b : Ir.Block) : Option Math.MList :=
  let inls := match b with
    | .para content => content
    | .equation _ content => content
    | _ => #[]
  inls.findSome? fun x => match x with
    | .formula _ _ body => some body
    | _ => none

/-- A block without the display context it rides in (`Ir.DisplayCtx`). -/
def unwrapDisplay (b : Ir.Block) : Ir.Block := (Ir.displayCtxOf b).2

def firstFormula (d : Ir.Doc) : Option Math.MList :=
  d.body.findSome? fun b => match unwrapDisplay b with
    | .center bs => bs.findSome? blockFormula
    | b => blockFormula b

/-- A markdown source through the markdown door and the one elaborator, as `leantex doc.md` runs
it. -/
def elabMd (s : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .markdown "t.md" s
  Elab.runKept "t.md" raws ds

/-- A code file's source elaborated as `leantex <file>` reads it, its language from `file`'s
extension. -/
def elabCode (file src : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read (Ir.Surface.ofPath file) file src
  Elab.runKept file raws ds

/-- How a witness runs: its source as written or transformed (`rep`), with or without its locations
(`located`). -/
structure WitnessRun where
  rep : String → String := id
  located : Bool := false

/-- A tex source elaborated as `w` runs it. -/
def WitnessRun.elab (w : WitnessRun) (src : String) : Ir.Doc × Array Diag :=
  if w.located then
    let (toks, lexDs) := Lex.lex "t" (w.rep src)
    let (raws, parseDs) := Parse.parse "t" toks
    let (doc, ds, _) := Elab.runRawsSpanned "t" raws (lexDs ++ parseDs)
    (doc, ds)
  else elabStr (w.rep src)

/-- A markdown source elaborated as `w` runs it. -/
def WitnessRun.elabMarkdown (w : WitnessRun) (src : String) : Ir.Doc × Array Diag :=
  if w.located then
    let (raws, ds) := Md.read "t.md" (w.rep src)
    let (doc, ds, _) := Elab.runRawsSpanned "t.md" raws ds
    (doc, ds)
  else elabMd (w.rep src)

/-- Diagnostics of a markdown source. -/
def dvMd (s : String) (w : WitnessRun := {}) : Array Diag := (w.elabMarkdown s).2

/-- A reader that answers no request. -/
def nullReader : Compat.InputReader Id := fun _ context => (none, context)

/-- A markdown file as a document of its own, elaborated as the driver runs one: nothing executes. -/
def standaloneDoc (f t : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .markdown f t
  Elab.runKept f raws ds

/-- The included door's reader: `\markdownInput{name}` answered with the markdown fragment of the
file `files` maps it to, read and answered as the driver reads and answers it. -/
def mdFileReader (files : List (String × String × String)) :
    Compat.InputReader (StateM (Array Diag)) := fun request context => do
  if request.packageCalls.any (·.1 == "markdown") then
    return (none, context.loadMarkdown request.options)
  if request.command != "markdownInput" then return (none, context)
  match files.find? (·.1 == request.name.trimAscii.toString) with
  | none => return (none, context)
  | some (_, path, text) =>
    let (cites, hybrid, note) := context.markdownFor request.options ⟨request.file, request.pos⟩
    let (sub, ds) := Surface.fragment .markdown path text request.pos cites hybrid
    modify (· ++ ds ++ note)
    let (answer, context) :=
      Elab.markdownAnswer (m := Id) nullReader context request.file sub hybrid request.pos
    return (some answer, context)

/-- A tex host through its door, executed with the included door's reader. -/
def includedDoc (hostFile host : String) (files : List (String × String × String)) :
    Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.read .tex hostFile host
  let (executed, readDs) := (Elab.executeInputs (mdFileReader files) hostFile raws).run #[]
  Elab.runExecuted hostFile executed (ds ++ readDs)

/-- A markdown file alone as a document named `docFile`: its fragment and nothing else. -/
def aloneDoc (docFile f t : String) : Ir.Doc × Array Diag :=
  let (raws, ds) := Surface.fragment .markdown f t {}
  Elab.runKept docFile raws ds

/-- An article whose body is one `\markdownInput` and nothing else. -/
def neutralHost (name : String) : String :=
  "\\documentclass{article}\\usepackage{markdown}\\begin{document}\\markdownInput{" ++ name ++
    "}\\end{document}"

/-- The neutral host with each command on a line of its own and blank lines around the include
(`Elab.sourceBlank`). -/
def spacedNeutralHost (name : String) : String :=
  "\\documentclass{article}\n\\usepackage{markdown}\n\n\\begin{document}\n\n\\markdownInput{" ++
    name ++ "}\n\n\\end{document}\n"

mutual

/-- One node as its tag, attributes, text and closing tag, flattened so the string states
nesting. -/
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

/-- The tags and text a document's page carries, in order, flattened. -/
def docTreeOf (doc : Ir.Doc) : String := mdFlatten "" (docNodesOf doc).toList

/-- The tags and text a markdown source's page carries, in order. -/
def mdTreeOf (src : String) : String := docTreeOf (elabMd src).1

/-- A page's HTML body rendered, its text escaped, telling a `<br>` from the text `<br>`. -/
def docHtmlOf (doc : Ir.Doc) : String := Html.render (Html.elem "div" (docNodesOf doc)) 0

/-- The control table's rows read to nothing whose arguments are all groups: each name, its group
count and the key its note names, none where the dispatcher's guard names it. -/
def nothingRows : List (String × Nat × Option String) :=
  Compat.ctrlRows.filterMap fun row =>
    if row.sig.all (fun k => k == .group || k == .needed) then
      match row.action with
      | .discard _ key => some (row.name, row.sig.length, some key)
      | .inert => some (row.name, row.sig.length, none)
      | .tokens .. | .native _ | .skip _ | .refuse .. => none
    else none

/-- The sites the raw-HTML family places a construct at: in a paragraph, opening a line, as a block,
in each container and in a heading. -/
def mdHtmlSites : List (String × (String → String)) :=
  [("mid-paragraph", fun s => s!"Alder {s} Birch\n"),
   ("line start", fun s => s!"{s} Alder\n"),
   ("own block", fun s => s!"Alder\n\n{s}\n\nBirch\n"),
   ("quote", fun s => s!"> {s}\n"),
   ("list item", fun s => s!"- {s}\n"),
   ("disclosure body", fun s => s!"<details>\n<summary>Wren</summary>\n\n{s}\n\n</details>\n"),
   ("heading", fun s => s!"# Alder {s} Birch\n")]

mutual

/-- Every `<pre>` of a tree, in document order. -/
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

/-- The exact attributes of an unconfigured fence's `<pre>`. -/
def mdCodeBlockPreAttrs : Array (String × String) :=
  #[("style", "font-size: 0.8em; line-height: 1.187; tab-size: 8; white-space: pre-wrap; \
overflow-wrap: break-word; text-indent: 20pt hanging each-line;"),
    ("tabindex", "0")]

/-- A plain code block's text read through its held atoms, `none` where it carries any other
element. -/
def plainCodeText (kids : Array Html.Node) : Option String :=
  kids.foldl (fun acc k => acc.bind fun t => match k with
    | .text s => some (t ++ s)
    | .elem "span" #[("class", c)] #[.text s] =>
      if c == HtmlDoc.codeTokClass || c == HtmlDoc.codeTokClass ++ " " ++ HtmlDoc.codeLongTokClass
      then some (t ++ s) else none
    | _ => none) (some "")

/-- The page's code blocks in order, each its text when the block is exactly a plain `<pre>` holding
one bare `<code>`, else `none`. -/
def mdCodeBlocks (src : String) : Array (Option String) :=
  let (doc, _) := elabMd src
  let (_, body, _) := HtmlDoc.emitTree {} doc
  (mdPresList #[] body.toList).map fun n =>
    match n with
    | .elem "pre" attrs #[.elem "code" cattrs kids] =>
      if attrs == mdCodeBlockPreAttrs && cattrs.isEmpty then plainCodeText kids else none
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
  "\\documentclass[aspectratio=169]{slides}\n\\theme{default}\n\\palette{ covered = 38\\% }\n" ++
    "\\begin{document}\n" ++ body ++ "\n\\end{document}"

def deck169Frame (body : String) : String :=
  deck169Body ("\\begin{frame}\n" ++ body ++ "\n\\end{frame}")

/-- The golden set's markdown fixtures, `testdata/corpus/<n>.md`. -/
def mdGoldenNames : List String :=
  ["md-cite", "md-code", "md-emphasis", "md-headings", "md-images", "md-links", "md-lists",
   "md-quotes", "md-readme", "md-rules", "md-table"]

/-- The golden set's code fixtures: `testdata/corpus/<n>.<ext>`, read by the code-file reader
their extension selects. -/
def codeGoldenNames : List (String × Ir.CodeLang) :=
  [("code-lean", .lean), ("code-python", .python), ("code-bash", .bash), ("lean-cite", .lean)]

/-- Fixtures allowed to ship a named markup character as ink, per character, each with its reason. -/
def inkMarkupExempt : List (String × List Char) :=
  -- Code ships as written: an f-string's or an expansion's braces and a raw docstring's backslash.
  [("code-python", ['{', '}', '\\']), ("code-bash", ['{', '}'])]

/-- The markup characters a fixture may ship as ink (`inkMarkupExempt`). -/
def inkMarkupAllowed (n : String) : List Char :=
  ((inkMarkupExempt.find? (·.1 == n)).map (·.2)).getD []

/-- The golden set: every fixture `runGoldens` elaborates and `censusTable` must carry a row for. -/
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
   "icons", "svg-figures",
   "diagram", "diagram-boundary", "diagram-overflow", "diagram-refused", "diagram-shapes",
   "diagram-tikzset", "diagram-strokes", "diagram-tree", "diagram-scope", "diagram-cd",
   "diagram-longtail",
   "tables", "tables-ragged", "tables-deck", "subfigures", "float-center", "box-sides",
   "math-companion", "math-first", "math-text", "math-alpha", "math-cancel", "greek-literal", "abstract", "crossref", "eqnum", "footnotes",
   "redefine", "titlebars", "titleground", "daylight", "blocks", "poster", "poster-headline", "listings",
   "algorithm", "lineno", "lineno-modulo",
   "cond-newif", "cond-ifdefined", "cond-ifx", "cond-ifnum", "cond-loaded",
   "md-include", "md-include-deck", "md-cite-include", "lean-cite-include", "palette-seeds",
   "alert-mark", "deck-sections", "deck-hooks"] ++
  mdGoldenNames ++ codeGoldenNames.map (·.1)

/-- A TikZ picture of `body`, its environment on lines of their own. -/
def tikzPicture (body : String) : String :=
  "\\begin{tikzpicture}\n" ++ body ++ "\n\\end{tikzpicture}"

/-- The fonts the repository ships, which every font-dependent check uses, so every host sees the
same faces. -/
def testFonts : String := "testdata/corpus/fonts"

/-- The environment of a sealed run under `dir`: its own cache and home, a `PATH` reaching no tool,
and no outside face. -/
def sealedRunEnv (dir : System.FilePath) : Array (String × Option String) :=
  #[("XDG_CACHE_HOME", some (dir / "cache").toString),
    ("HOME", some (dir / "home").toString), ("PATH", some (dir / "no-tools").toString),
    ("LEANTEX_FONT", none), ("LEANTEX_FONT_PATH", none)]

/-- The next summary record a watcher writes on `h`, or `none` at its end or after `budgetMs`
without one. -/
def watcherSummary (h : IO.FS.Handle) (budgetMs : Nat := 60000) : IO (Option String) := do
  let task ← IO.asTask (prio := .dedicated) do
    repeat
      let line ← h.getLine
      if line.isEmpty then return none
      if (line.splitOn "\"event\":\"summary\"").length > 1 then return some line
    return none
  let start ← IO.monoMsNow
  while !(← IO.hasFinished task) && (← IO.monoMsNow) - start < budgetMs do
    IO.sleep 10
  if !(← IO.hasFinished task) then return none
  return match ← IO.wait task with
    | .ok line => line
    | .error _ => none

/-- The peak (`rssKiB`) the first porcelain summary in `stdout` states. -/
def summaryPeak (stdout : String) : Option Nat :=
  (stdout.splitOn "\n").findSome? fun line =>
    match Lean.Json.parse line with
    | .ok j => if (j.getObjValAs? String "event").toOption == some "summary" then
        (j.getObjValAs? Nat "rssKiB").toOption else none
    | .error _ => none

def findFont : IO (Option ByteArray) := do
  let p := testFonts ++ "/OpenSans-Regular.ttf"
  if ← System.FilePath.pathExists p then
    return some (← IO.FS.readBinFile p)
  return none

/-- A script fixture its owner may run, or with `exec := false` one no one may. -/
def writeScript (path : System.FilePath) (body : String) (exec : Bool := true) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path body
  IO.setAccessRights path { user := ⟨true, true, exec⟩ }

/-- What a loaded host may add to a bounded run's declared budget and grace,
spawning it and making and removing its scratch directory, before a check
reads the run as one its budget did not end. -/
def hostMarginMs : Nat := 60000

/-- A wall-clock bound only a hang exceeds: twenty times a run's typical time, and `hostMarginMs`
beside it. -/
def hangGuardMs (typicalMs : Nat) : Nat := 20 * typicalMs + hostMarginMs

/-- A test's child run, held to a hang guard over the time a run typically takes. -/
def childRun (typicalMs : Nat) (cmd : String) (args : Array String) (cwd : System.FilePath)
    (env : Array (String × Option String) := #[]) : IO RunBounded.Ended :=
  RunBounded.runBounded cmd args cwd (hangGuardMs typicalMs) 100 (env := env)

/-- How long a fixture that only its kill should end sleeps: two margins. -/
def hangSeconds : Nat := 2 * hostMarginMs / 1000

/-- A shell command that records its process id in `pidFile`, then sleeps
`hangSeconds`. -/
def hangCommand (pidFile : System.FilePath) : String :=
  s!"echo $$ > '{pidFile}' && exec sleep {hangSeconds}"

/-- The process id a `hangCommand` recorded in `pidFile`; empty before it has. -/
def recordedPid (pidFile : System.FilePath) : IO String := do
  return ((← (IO.FS.readFile pidFile).toBaseIO).toOption.getD "").trimAscii.toString

/-- Whether process `pid` has ended, as `ps` reads it beside this process:
gone, or a zombie its parent has not reaped; never when `ps` cannot say. -/
def processEnded (pid : String) : IO Bool := do
  let me := toString (← IO.Process.getPID)
  let r ← (IO.Process.output
    { cmd := "ps", args := #["-o", "pid=", "-o", "stat=", "-p", s!"{pid},{me}"] }).toBaseIO
  let rows : List (String × String) := match r with
    | .ok o => (o.stdout.splitOn "\n").filterMap fun (l : String) =>
        match (l.splitOn " ").filter (!·.isEmpty) with
        | [p, st] => some (p, st)
        | _ => none
    | .error _ => []
  return rows.any (·.1 == me) && (rows.find? (·.1 == pid)).all (·.2.startsWith "Z")

/-- Whether the `hangCommand` that records its process id in `pidFile` ends
within `ms`: the process it names ends, or it was ended before it named one. -/
def endsWithin (pidFile : System.FilePath) (ms : Nat) : IO Bool := do
  let start ← IO.monoMsNow
  let mut pid := ""
  for _ in [0:ms / 50 + 1] do
    pid ← recordedPid pidFile
    if !pid.isEmpty && (← processEnded pid) then return true
    if (← IO.monoMsNow) - start ≥ ms then break
    IO.sleep 50
  return pid.isEmpty

/-- This build's engine run in `dir` over `args`, sealed as `sealedRunEnv` seals a run, with `font`
its face and `cache` its caches. -/
def engineRun (dir : System.FilePath) (args : Array String) (font cache : System.FilePath) :
    IO IO.Process.Output := do
  let binary ← IO.FS.realPath ".lake/build/bin/leantex"
  IO.Process.output {
    cmd := binary.toString, cwd := some dir, args,
    env := #[("LEANTEX_FONT", some font.toString), ("XDG_CACHE_HOME", some cache.toString),
      ("HOME", some (cache / "home").toString), ("PATH", some (cache / "no-tools").toString),
      ("LEANTEX_FONT_PATH", none)] }

/-- A symbolic link at `link` naming `target`. -/
def symlink (target link : System.FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
  unless out.exitCode == 0 do throw <| IO.userError s!"ln -s failed: {out.stderr}"

/-- The Lean interpreter on PATH and the `LEAN_PATH` under which a child `lean --run` imports this
build; `what` names the caller. -/
def leanChild (what : String) : IO (System.FilePath × String) := do
  let some lean ← ToolProbe.onPath "lean" |
    throw <| IO.userError s!"{what} require the Lean interpreter on PATH"
  let libraries ← IO.FS.realPath ".lake/build/lib/lean"
  return (lean, libraries.toString ++ ":" ++ (← IO.getEnv "LEAN_PATH").getD "")

/-- `scripts/palette.lean` run with `args` as a bounded child of this build, in the repository's
root. -/
def paletteScript (args : Array String) : IO RunBounded.Ended := do
  let (lean, leanPath) ← leanChild "the palette script's checks"
  let dir ← IO.FS.realPath (← IO.currentDir)
  childRun 2400 lean.toString (#["--run", "scripts/palette.lean"] ++ args) dir
    (env := #[("LEAN_PATH", some leanPath)])

/-- The most chroma the gamut holds at a colour's own lightness and hue, at
`labOf`'s scale. -/
def edgeChroma (c : Ir.Color) : Nat :=
  let l := Oklab.labOf c
  let dir := Oklab.ofLch 0 (4 * 10 ^ 17) (Oklab.hueMilli l.a l.b)
  let e := Oklab.Okl.toGamut { L := l.L, a := dir.a, b := dir.b, f := Oklab.fracOne }
  Nat.sqrt (Oklab.chromaSq e.lab).toNat

/-- `text` quoted as one word for `/bin/sh`. -/
def shQuote (text : String) : String :=
  "'" ++ text.replace "'" "'\\''" ++ "'"

/-- A boundary renderer that names its version and draws by copying `pdf` beside a log, using shell
builtins and `/bin/cp` alone. -/
def fakeRenderer (pdf : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = --version ]; then\n" ++
  "  printf '%s\\n' 'synthetic boundary renderer 1'\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuote pdf.toString ++ " pic.pdf || exit 3\n" ++
  "printf '%s\\n' 'Output written on pic.pdf (1 page).' > pic.log\n"

/-- A build's diagnostics as its porcelain records them: code and severity. -/
def porcelainCodes (stdout : String) : Array (String × String) :=
  (((stdout.splitOn "\n").filter (!·.isEmpty)).filterMap fun l =>
    (Lean.Json.parse l).toOption.bind fun j =>
      if j.getObjValAs? String "event" != .ok "diagnostic" then none
      else some ((j.getObjValAs? String "code").toOption.getD "",
        (j.getObjValAs? String "severity").toOption.getD "")).toArray

/-- A PDF-to-SVG converter that names its version and converts by copying `svg` to its output. -/
def fakeConverter (svg : System.FilePath) : String :=
  "#!/bin/sh\n" ++
  "if [ \"$1\" = -v ]; then\n" ++
  "  printf '%s\\n' 'synthetic converter 1' >&2\n" ++
  "  exit 0\n" ++
  "fi\n" ++
  "/bin/cp " ++ shQuote svg.toString ++ " \"$3\" || exit 3\n"

/-- One of the suite's shipped faces by file name, parsed, or `none`. -/
def loadTestFont (file : String) : IO (Option Font) := do
  let p := testFonts ++ "/" ++ file
  unless ← System.FilePath.pathExists p do return none
  match Font.parse (← IO.FS.readBinFile p) with
  | .ok f => return some f
  | .error _ => return none

/-- Does a produced file contain this ASCII run, searched over bytes? -/
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

/-- The written PDF with every `/FlateDecode` stream inflated and appended after the raw bytes. -/
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

/-- A produced PDF re-read through `PdfRead.objects`, every listed object checked and every
decodable stream inflated; the count verified at a direct offset. -/
def checkXref (pdf : ByteArray) : Except String Nat := do
  let es ← PdfRead.objects pdf
  let mut verified := 0
  for e in es.val do
    if let .direct _ := e.loc then
      verified := verified + 1
    -- Streams under the reader's filters decode or the file is refused; a foreign filter is data.
    let fs := PdfCensus.filtersOf e.val
    if fs.all (· == "FlateDecode") then
      if let .error err := e.decoded then
        throw s!"object {e.num}: {err}"
  return verified

/-- An object with a reference resolved against the read entries, nothing for a dangling one. -/
def entryResolve (es : Array PdfRead.Entry) (obj : PdfRead.Obj) : Option PdfRead.Obj :=
  match obj with
  | .ref n _ => (es.find? (·.num == n)).map (·.val)
  | other => some other

/-- A fixture file's text as the driver's decoding door reads it. -/
def fixtureText (path : String) : IO String := do
  let bytes ← IO.FS.readBinFile path
  return if Ir.Surface.ofPath path == .tex then (Encoding.readDocument path bytes).1.text
    else (Encoding.readMarkdown path bytes).text

/-- A source whose file includes are fulfilled before elaboration, `file` setting the input
directory. -/
def elabInputSrc (file src : String) : IO (Ir.Doc × Array Diag) := do
  let (raws, readDs) := Surface.read .tex file src
  let (executed, inputDs, _) ← Input.expandInputs file raws
  return Elab.runExecuted file executed (readDs ++ inputDs)

/-- A `sty-parity` fixture run as the driver runs it: inputs expanded, elaborated, and its N0020
records built as `Main.frontend` builds them. -/
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

/-- A fixture elaborated as the driver builds it: includes, `\data` and the bibliography fulfilled
where `Main` fulfils them. -/
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
  let prepared := Elab.prepareExecuted file (executed.withRaws raws)
  let (doc, diags) := Elab.runPreparedFinal file prepared
    (readDiags ++ inputDiags ++ dataDiags) (fun _ _ => {})
  let requested := Ir.bibRefs doc
  if requested.isEmpty then return (doc, diags)
  let mut sources : Array (String × String) := #[]
  for srcName in requested do
    let name := Bib.sourceName srcName
    let path := s!"testdata/corpus/{name}"
    if ← System.FilePath.pathExists path then
      sources := sources.push (srcName, ← fixtureText path)
  let (doc, bibDiags) := Bib.resolve file prepared sources doc
  -- The source-free view `runPreparedFinal` returns, reference entries included.
  return (Ir.eraseLocations doc, diags ++ bibDiags)

/-- A document elaborated and its bibliography resolved as a build resolves them
(`Cli.Driver.elaborate`), in the driver's four parts. -/
def bibBuildRun (src : String) (bibs : Array (String × String)) (surface : Ir.Surface := .tex)
    (file : String := "t.tex") : Ir.Doc × Array Diag × Array Diag × Array Diag :=
  let (raws, readDs) := Surface.read surface file src
  let prepared := Elab.prepareExecuted file
    (if surface == .tex then Elab.executeInputs nullReader file raws else Compat.kept file raws)
  let pass (prepared : Elab.Prepared) : Ir.Doc × Array Diag × Array Diag × Array Diag :=
    let (doc, ds, spans) := Elab.runPrepared file prepared readDs (fun _ _ => {})
    let sources := (Ir.bibRefs doc).filterMap fun r => bibs.find? (·.1 == r)
    let (doc, bds) := Bib.resolve file prepared sources doc
    let doc := Bib.resolveListRefs spans.labels doc
    (doc, ds, bds, Bib.refJudge spans doc)
  let first := pass prepared
  let counts := first.1.listNotes.map (·.2)
  let (doc, ds, bds, refs) := if counts.all (· == 0) then first
    else pass { prepared with listNotes := counts }
  (Ir.eraseLocations doc, ds, bds, refs)

/-- `bibBuildRun` with the reference judge's diagnostics among the
document's, and the reference list's apart. -/
def bibBuildParts (src : String) (bibs : Array (String × String)) :
    Ir.Doc × Array Diag × Array Diag :=
  let (doc, ds, bds, refs) := bibBuildRun src bibs
  (doc, ds ++ refs, bds)

/-- `bibBuildParts` with the document's diagnostics tallied, as `elabStr`
reports them, and the reference list's apart, as `Bib.apply` reports them. -/
def bibResolve (src : String) (bibs : Array (String × String)) :
    Ir.Doc × Array Diag × Array Diag :=
  let (doc, ds, bds) := bibBuildParts src bibs
  (doc, Diag.tallySites ds, bds)

/-- `bibBuildRun` with the run's losses accounted once by the driver's own accounting
(`Bib.accountFront`). -/
def bibBuild (src : String) (bibs : Array (String × String)) : Ir.Doc × Array Diag :=
  let (doc, ds, bds, refs) := bibBuildRun src bibs
  (doc, Bib.accountFront ds bds #[] refs)

/-- A body's text as its pages show it, each reference-list entry after its marker. -/
def inkText (blocks : Array Ir.Block) : String :=
  blocks.foldl (init := "") fun acc b => match b with
    | .bibliography _ _ items => items.foldl (init := acc) fun acc it =>
      acc ++ ((it.marker.map fun m => s!"[{m}] ").getD "") ++ Ir.plainText it.content
    | _ => acc ++ Ir.blocksText #[b]

/-- A body's text as its pages show it, each reference-list entry after its marker, where its blocks
break aside. -/
def inkFlat (blocks : Array Ir.Block) : String :=
  String.ofList ((inkText blocks).toList.filter (· != '\n'))

/-- A world holding files by path, `/work` its working directory, and nothing to run. -/
def factsWorld (files : List (String × ByteArray)) : (q : World.Ask) → World.Reply q
  | .env _ => none
  | .cwd => .ok "/work"
  | .stat path =>
    if files.any (·.1 == path) then
      .ok { kind := .file, size := 0, mtimeSec := 0, mtimeNsec := 0, real := path }
    else .error .absent
  | .metadata _ => .error .absent
  | .readFile path => match files.lookup path with
    | some b => .ok b
    | none => .error .absent
  | .listDir _ => .error .absent
  | .run _ => { ran := .exited 1, out := "", err := "", complete := true, outputs := #[] }
  | .writeAtomic _ _ => .ok ()
  | .createDirAll _ => .ok ()

/-- The citation nodes of an elaborated body in order, resolved or not: their forms and keys. -/
def citesOf (doc : Ir.Doc) : Array (Ir.CiteForm × Array String) :=
  Ir.foldBlocks (fun out _ => out) (fun out x => match x with
    | .cite f ks => out.push (f, ks)
    | .cited f ks _ => out.push (f, ks)
    | _ => out) #[] doc.body

/-- The keys of an elaborated body's citations, in order. -/
def keysOf (doc : Ir.Doc) : List String := (citesOf doc).toList.flatMap fun (_, ks) => ks.toList

/-- A markdown document built as `bibBuild` builds a TeX one, its bibliography from `.bib` texts by
the names its metadata gives them. -/
def mdBibBuild (src : String) (bibs : Array (String × String)) (file : String := "t.md") :
    Ir.Doc × Array Diag :=
  let (doc, ds, bds, refs) := bibBuildRun src bibs .markdown file
  (doc, Bib.accountFront ds bds #[] refs)

/-- Invented entries, keys `a`, `b` and `roe2020`, placeholder names. -/
def worksBib : String :=
  "@book{a, author = {Ash, Ada}, title = {Alpha Notes}, publisher = {Example Press}, year = {2001}}\n\
@book{b, author = {Birch, Bo}, title = {Beta Notes}, publisher = {Example Press}, year = {2002}}\n\
@misc{roe2020, author = {Roe, Sam}, title = {Placeholder Text}, year = {2020}}\n"

/-- The metadata block that declares `works.bib`, which a markdown document reads citations under. -/
def worksMeta : String := "---\nbibliography: works.bib\n---\n\n"

/-- The `.bib` texts beside the corpus a document's bibliography names, by those names and by their
files', as a twin names them. -/
def corpusBibs (doc : Ir.Doc) : IO (Array (String × String)) := do
  let mut out : Array (String × String) := #[]
  for name in Ir.bibRefs doc do
    let path := s!"testdata/corpus/{Bib.sourceName name}"
    if ← System.FilePath.pathExists path then
      let text ← fixtureText path
      out := out.push (name, text)
      if Bib.sourceName name != name then out := out.push (Bib.sourceName name, text)
  return out

/-- A golden fixture's source file under `testdata/corpus`, with its surface's extension. -/
def goldenFile (n : String) : String :=
  let ext := match codeGoldenNames.lookup n with
    | some lang => lang.extension
    | none => if mdGoldenNames.contains n then "md" else "tex"
  s!"testdata/corpus/{n}.{ext}"

/-- Markdown citations in Pandoc's syntax, read under `worksMeta`, each with what the markdown twin
spells it as. -/
def mdCiteTwinCases : List (String × String) :=
  [("[@a]", "[@a]"), ("[see @a, p. 33]", "[see @a, p. 33]"), ("[@a; @b, p. 2]", "[@a; @b, p. 2]"),
   ("[see @a, pp. 1-3; @b]", "[see @a, pp. 1-3; @b]"), ("@a says", "@a says"),
   ("@a [p. 4] says", "@a [p. 4] says"), ("@a [p. 4; @b] says", "@a [p. 4; @b] says"),
   ("@a [@b] says", "@a [@b] says"), ("[-@a, p. 3]", "[-@a, p. 3]"),
   ("[@a; -@b]", "[@a; -@b]"), ("@Foo_bar.baz. ends", "@{Foo_bar.baz}. ends"),
   ("@{a;b} ends", "@{a;b} ends"), ("[@a, x\\; y]", "[@a, x\\; y]"),
   ("[@a, x \\@b]", "[@a, x \\@b]")]

/-- A markdown fixture elaborated as the driver builds it: its bibliography read beside it. -/
def elabMdFixture (n src : String) : IO (Ir.Doc × Array Diag) := do
  let file := s!"{n}.md"
  let (raws, ds) := Md.read file src
  let (doc, diags) := Elab.runKept file raws ds
  if (Ir.bibRefs doc).isEmpty then return (doc, diags)
  let prepared := Elab.prepareExecuted file (Compat.kept file raws)
  let (doc, diags) := Elab.runPreparedFinal file prepared ds (fun _ _ => {})
  let mut sources : Array (String × String) := #[]
  for srcName in Ir.bibRefs doc do
    let path := s!"testdata/corpus/{Bib.sourceName srcName}"
    if ← System.FilePath.pathExists path then
      sources := sources.push (srcName, ← fixtureText path)
  let (doc, bibDiags) := Bib.resolve file prepared sources doc
  return (Ir.eraseLocations doc, diags ++ bibDiags)

/-- A Lean page's documentation reading citations into the bibliography files `sources` name,
elaborated and resolved as the driver builds it. -/
def leanCiteBuild (file src : String) (sources : Array (String × String)) : Ir.Doc × Array Diag :=
  let refs : Code.Refs := { path := ",".intercalate (sources.map (·.1)).toList
                            keys := sources.foldl (init := {}) fun ks (_, bib) =>
                              (Bib.keysOf bib).foldl (·.insert ·) ks }
  let (raws, ds) := Surface.readCode .lean file src none {} (some refs)
  let prepared := Elab.prepareExecuted file (Compat.kept file raws)
  let (doc, diags) := Elab.runPreparedFinal file prepared ds (fun _ _ => {})
  let (doc, bibDiags) := Bib.resolve file prepared sources doc
  (Ir.eraseLocations doc, diags ++ bibDiags)

/-- A code fixture elaborated as the driver builds it, a Lean page declaring its bibliography read
through the front door beside it and its citations resolved against the files it names. -/
def elabCodeFixture (n : String) (lang : Ir.CodeLang) (src : String) : IO (Ir.Doc × Array Diag) := do
  let file := s!"{n}.{lang.extension}"
  if lang != .lean || (Code.showingOf lang src.toList.toArray).bibliography.isEmpty then
    return elabCode file src
  let path := s!"testdata/corpus/{file}"
  let read ← Input.readDocument path src.toUTF8
  let prepared := Elab.prepareExecuted path read.executed
  let (doc, diags) := Elab.runPreparedFinal path prepared read.diags (fun _ _ => {})
  let mut sources : Array (String × String) := #[]
  for srcName in Ir.bibRefs doc do
    let bib := Input.besideDocument path (Bib.sourceName srcName)
    if ← bib.pathExists then sources := sources.push (srcName, ← fixtureText bib.toString)
  let (doc, bibDiags) := Bib.resolve path prepared sources doc
  return (Ir.eraseLocations doc, diags ++ bibDiags)

/-- A golden fixture elaborated through its own surface's reader. -/
def goldenDoc (n : String) : IO (Ir.Doc × Array Diag) := do
  let src ← fixtureText (goldenFile n)
  if let some lang := codeGoldenNames.lookup n then elabCodeFixture n lang src
  else if mdGoldenNames.contains n then elabMdFixture n src
  else elabFixture n src

/-- The corpus documents a markdown twin is measured over, each as the driver elaborates it, by
path. -/
def corpusTwinDocs : IO (Array (String × Ir.Doc)) := do
  let mut names : Array String := #[]
  for f in ← System.FilePath.readDir "testdata/corpus" do
    if f.fileName.endsWith ".tex" then names := names.push (f.fileName.dropEnd 4).toString
  let mut out := #[]
  for n in names.qsort (· < ·) do
    let (d, _) ← elabFixture n (← fixtureText s!"testdata/corpus/{n}.tex")
    out := out.push (s!"testdata/corpus/{n}.tex", d)
  for n in mdGoldenNames ++ codeGoldenNames.map (·.1) do
    let (d, _) ← goldenDoc n
    out := out.push (goldenFile n, d)
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

/-- One shipped line of the page census over `Layout.Out`: the observable facts a page claim may
cite. -/
structure CensusLine where
  x : Dim.Sp
  /-- The line's baseline, in layout coordinates (y down). -/
  y : Dim.Sp
  /-- The largest set size among the line's glyph runs (0 on a glyphless line). -/
  size : Dim.Sp
  /-- The line's set width. -/
  width : Dim.Sp
  text : String
  /-- The line stands in the reserved margin band by design (`Layout.LineOut.furniture`). -/
  furniture : Bool := false
  /-- A counted body line (`Layout.LineOut.counted`). -/
  counted : Bool := false
  /-- The face each glyph run sets in, in run order: the page side of `Picture.labelFace_agree`. -/
  runFonts : Array Nat := #[]

structure CensusPage where
  lines : Array CensusLine
  covered : String
  rules : Nat
  /-- Every rule segment on the page, in line order: baseline and thickness. -/
  ruleSegs : Array (Dim.Sp × Dim.Sp) := #[]
  /-- Typed decoration segments in line order: kind, baseline, width,
  thickness, raise, and colour. -/
  decorations : Array (Ir.Decoration × Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp × Ir.Color) := #[]
  fills : Nat
  /-- Every fill rectangle on the page, in paint order. -/
  fillRects : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- The picture paths on the page, every mark of every picture's ink, in paint order. -/
  paths : Nat
  /-- Every shipped path's stroke colour and width, in paint order; an unstroked path contributes
  none. -/
  pathStrokes : Array (Ir.Color × Dim.Sp) := #[]
  /-- Every shipped path's extent, in paint order. -/
  pathSpans : Array (Dim.Sp × Dim.Sp) := #[]
  /-- Every shipped path's bounding box `(x, y, w, h)` in page coordinates, in paint order, where
  `Picture.placeRel_exact` and `Picture.place_order_agree` are read. -/
  pathBoxes : Array (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp) := #[]
  /-- The drawn figures the page places, and their text run by run, in placement order. -/
  figures : Nat := 0
  figureText : String := ""
  /-- Every shipped path's subpaths in paint order, each its segment count and whether it is
  dashed. -/
  pathRuns : Array (Array Nat × Bool) := #[]
  /-- Image boxes shipped on the page: embedded figures and boundary request boxes. -/
  images : Nat := 0
  /-- Filled polygons in the page's lines, as points in page coordinates (y down). -/
  polys : Array (Array (Dim.Sp × Dim.Sp)) := #[]

def CensusPage.text (p : CensusPage) : String :=
  String.intercalate " " (p.lines.toList.map (·.text))

/-- The colours covering can paint in a document (`Design.cover`), fixed points excluded. -/
def coveredColorsOf (doc : Ir.Doc) : Array Ir.Color :=
  let cov := (Ir.Design.ofDoc doc).cover
  (doc.palette.entries.filterMap fun (_, c) =>
    let covered := cov.of c
    if covered == c then none else some covered).push cov.plain

/-- A page's picture marks in layout coordinates, in paint order, each placed by its ink's
placement. -/
def pageInkMarks (p : Layout.PageOut) :
    Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke) :=
  p.inks.flatMap fun k => k.fig.marks.filterMap fun mk => match mk with
    | .paint _ g fl st _ _ => some (g.mapIso k.place, fl, st)
    | .raster _ _ _ _ => none
    | .shading _ _ _ => none

mutual

/-- A node's draws onto `acc`, at any depth, as the figure states them. -/
def nodeDrawsOne {L : Type} (acc : Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke)) :
    Gfx.Node L → Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke)
  | .draw g fl st => acc.push (g, fl, st)
  | .group _ _ _ kids => nodeDrawsList acc kids.toList
  | .use _ _ | .stamp _ _ _ _ | .image _ _ | .label _ | .words _ => acc

def nodeDrawsList {L : Type} (acc : Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke)) :
    List (Gfx.Node L) → Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke)
  | [] => acc
  | n :: rest => nodeDrawsList (nodeDrawsOne acc n) rest

end

/-- A page's picture draws in layout coordinates, in paint order, each geometry as the figure states
it. -/
def pageDraws (p : Layout.PageOut) : Array (Gfx.Geom × Option Gfx.Fill × Option Gfx.Stroke) :=
  p.inks.flatMap fun k =>
    (nodeDrawsList #[] k.fig.nodes.toList).map fun (g, fl, st) => (g.mapIso k.place, fl, st)

/-- A paint's colour, when it paints with one. -/
def paintColor? : Gfx.Paint → Option Ir.Color
  | .solid c => some c
  | .gradient _ => none

/-- A path's segments with their start points, in layout coordinates. -/
def subpathSegs (subs : Array Gfx.Subpath) : Array Ir.Pic.PathSeg :=
  subs.flatMap fun sp => Id.run do
    let mut out : Array Ir.Pic.PathSeg := #[]
    let mut cur := sp.start
    for sg in sp.segs do
      match sg with
      | .line q => out := out.push (.line cur.1 cur.2 q.1 q.2)
      | .cubic c1 c2 q => out := out.push (.cubic cur.1 cur.2 c1.1 c1.2 c2.1 c2.2 q.1 q.2)
      cur := sg.endPt
    return out

/-- A shape's ink read back as a circle: centre, radius, stroke, fill. -/
def shapeCircle? : Ir.Pic.Shape →
    Option (Dim.Sp × Dim.Sp × Dim.Sp × Option Gfx.Stroke × Option Gfx.Fill)
  | .ink (.draw (.ellipse x y rx _) fl st) => some (x, y, rx, st, fl)
  | _ => none

/-- A shape's ink read back as a frame or fill: min corner, extents, stroke, fill. -/
def shapeFrame? : Ir.Pic.Shape →
    Option (Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp × Option Gfx.Stroke × Option Gfx.Fill)
  | .ink (.draw (.rect x y w h) fl st) => some (x, y, w, h, st, fl)
  | _ => none

/-- Is a draw an arrow tip's mark, filled or round-capped, rather than a path's butt-capped
stroke? -/
def isTipDraw (fl : Option Gfx.Fill) (st : Option Gfx.Stroke) : Bool :=
  fl.isSome || (st.map (·.cap != .butt)).getD false

/-- A shape's ink read back as an edge: segments, stroke, and whether a tip ends it. -/
def shapeEdge? : Ir.Pic.Shape → Option (Array Ir.Pic.PathSeg × Gfx.Stroke × Bool)
  | .ink (.group _ _ _ kids) =>
    match kids.toList with
    | [.draw (.path subs) none (some st)] => some (subpathSegs subs, st, false)
    | [.draw (.path subs) none (some st), .draw _ fl tst] =>
      if isTipDraw fl tst then some (subpathSegs subs, st, true) else none
    | _ => none
  | _ => none

/-- The segments of a page's stroked picture paths, in paint order, in layout coordinates. -/
def edgeSegs (p : Layout.PageOut) : Array Ir.Pic.PathSeg :=
  (pageDraws p).foldl (fun acc (g, fl, st) => match g, st with
    | .path subs, some _ => if isTipDraw fl st then acc else acc ++ (subpathSegs subs)
    | _, _ => acc) #[]

/-- A placed mark's extent as the census reads it: a rectangle's box, a path's box over its
endpoints. -/
def markExtent : Gfx.Geom → Dim.Sp × Dim.Sp × Dim.Sp × Dim.Sp
  | .rect x y w h => (x, y, w, h)
  | .ellipse cx cy rx ry => (cx - rx, cy - ry, 2 * rx, 2 * ry)
  | .path subs =>
    let pts := subs.flatMap fun sp => #[sp.start] ++ sp.segs.map Gfx.Seg.endPt
    let xs := pts.map (·.1)
    let ys := pts.map (·.2)
    let x0 := xs.foldl min (xs[0]?.getD 0)
    let y0 := ys.foldl min (ys[0]?.getD 0)
    (x0, y0, xs.foldl max (xs[0]?.getD 0) - x0, ys.foldl max (ys[0]?.getD 0) - y0)

def censusOf (coveredColors : Array Ir.Color) (out : Layout.Out) (imgs : Image.Store := {}) :
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
    let mut figures := 0
    let mut figureText := ""
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
        | .image k w _ _ =>
          px := px + w
          images := images + 1
          if let some fig := k.bind fun i => (imgs.shaped[i]?).join then
            figures := figures + 1
            for (_, r) in fig.labels do
              figureText := figureText ++ r.text ++ " "
        | .poly pts _ => polys := polys.push (pts.map fun (x, y) => (px + x, l.y - y))
      -- A protruded line reports its measure edge; its ink hangs `l.hang` left of it.
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
                          paths := (pageInkMarks p).size
                          pathStrokes := (pageInkMarks p).filterMap fun (_, _, st) =>
                            st.bind fun s => match s.paint with
                              | .solid c => some (c, s.width)
                              | .gradient _ => none
                          pathSpans := (pageInkMarks p).map fun (g, _, _) =>
                            let (_, _, w, h) := markExtent g
                            (w, h)
                          pathBoxes := (pageInkMarks p).map fun (g, _, _) => markExtent g
                          pathRuns := (pageInkMarks p).map fun (g, _, st) =>
                            let dashed := (st.map fun s => !s.dash.isEmpty).getD false
                            match g with
                            | .path subs => (subs.map (·.segs.size), dashed)
                            | .rect _ _ _ _ => (#[], dashed)
                            | .ellipse _ _ _ _ => (#[], dashed)
                          images := images
                          figures := figures
                          figureText := figureText }
  return pages

def hasStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The animations a stylesheet's step rules run: each name an `animation:` lists in a rule whose
selector names a step, `none` aside. -/
def stepAnimations (css : String) : List String :=
  ((css.splitOn "\n").flatMap fun l =>
    if !hasStr ((l.splitOn "{").headD "") ".step" then []
    else match (l.splitOn "animation: ").drop 1 with
      | rest :: _ =>
        (((rest.splitOn ";").headD "").splitOn ",").filterMap fun item =>
          let n := (item.trimAscii.toString.takeWhile fun c => c.isAlphanum || c == '-').toString
          if n.isEmpty || n == "none" then none else some n
      | [] => []).eraseDups

/-- The declarations a stylesheet's `@keyframes` block of that name sets, frame by frame in order. -/
def keyframeDecls (css name : String) : Option (List (String × String)) := do
  let rest ← ((css.splitOn s!"@keyframes {name} ").drop 1).head?
  let (_, body, _) := rest.toList.foldl (init := ((0 : Nat), "", false)) fun (depth, acc, done) c =>
    if done then (depth, acc, done)
    else if c == '{' then (depth + 1, acc.push c, false)
    else if c == '}' then (depth - 1, acc.push c, depth == 1)
    else (depth, acc.push c, false)
  let (segs, last) := body.toList.foldl (init := (([] : List String), "")) fun (out, cur) c =>
    if c == '{' || c == '}' || c == ';' then (cur :: out, "") else (out, cur.push c)
  pure ((last :: segs).reverse.filterMap fun seg =>
    match seg.splitOn ":" with
    | p :: v :: _ => some (p.trimAscii.toString, v.trimAscii.toString)
    | _ => none)

/-- The properties a stylesheet's `@keyframes` block of that name sets, in order. -/
def keyframeProps (css name : String) : Option (List String) :=
  (keyframeDecls css name).map (·.map (·.1))

/-- Whether every keyframes a stylesheet's steps run sets only `props`. -/
def stepKeyframesSet (css : String) (props : List String) : Bool :=
  (stepAnimations css).all fun n =>
    (keyframeProps css n).any fun ps => !ps.isEmpty && ps.all props.contains

/-- Whether no keyframes a stylesheet's steps run moves content: each fades or reaches, nothing
else, the fades setting opacity alone and the reaches visibility alone. -/
def stepsStandStill (css : String) : Bool :=
  stepKeyframesSet css ["opacity", "visibility"] &&
    ["ltx-uncover", "ltx-recover"].all (fun n =>
      (keyframeProps css n).all fun ps => ps.all (· == "opacity")) &&
    ["ltx-unhide", "ltx-rehide"].all fun n =>
      (keyframeProps css n).all fun ps => ps.all (· == "visibility")

/-- Whether a stylesheet's steps fade from nothing, as a deck hiding its pending steps covers. -/
def stepsFadeFromNothing (css : String) : Bool :=
  (keyframeDecls css "ltx-uncover").any (·.contains ("opacity", "0%"))

/-- Whether a stylesheet keeps a step out of reach while it is pending: where `view()` timelines
run, its reveal opens on a hidden step and its recover closes on one, and every rule outside a
keyframe that covers a step from nothing hides it too. -/
def pendingStepsOutOfReach (css : String) : Bool :=
  let runs := stepAnimations css
  runs.contains "ltx-unhide" && runs.contains "ltx-rehide" &&
    (keyframeDecls css "ltx-unhide").any (·.contains ("visibility", "hidden")) &&
    (keyframeDecls css "ltx-rehide").any (·.contains ("visibility", "hidden")) &&
    (css.splitOn "\n").all fun l =>
      l.trimAscii.toString.startsWith "@keyframes" || !hasStr l "opacity: 0%" ||
        hasStr l "visibility: hidden"

/-- Span equality with the provenance `==` ignores: the macro origins and the authored token. -/
def exactSpan (a b : Span) : Bool :=
  a == b && a.pos.origins == b.pos.origins && a.pos.command == b.pos.command

/-- Whether a site is exactly `expected`, provenance included. -/
def sameSource (actual : Option Span) (expected : Span) : Bool := actual.any (exactSpan · expected)

/-- How many of a raw RGB raster's pixels, Poppler's PPM, are exactly each colour, read on pixel
boundaries. -/
def ppmCounts (file : System.FilePath) (colours : Array (UInt8 × UInt8 × UInt8)) :
    IO (Array Nat) := do
  let bytes ← IO.FS.readBinFile file
  let mut start := 0
  let mut lines := 0
  for i in [:bytes.size] do
    if bytes[i]?.getD 0 == 10 then lines := lines + 1
    if lines == 3 then
      start := i + 1
      break
  let header := (String.fromUTF8? (bytes.extract 0 start)).getD ""
  unless header.startsWith "P6\n" && header.endsWith "\n255\n" &&
      start > 0 && (bytes.size - start) % 3 == 0 do
    throw <| IO.userError "the raster oracle requires Poppler's raw RGB PPM"
  let mut counts := colours.map fun _ => 0
  for i in [start:bytes.size:3] do
    let px := (bytes[i]?.getD 0, bytes[i + 1]?.getD 0, bytes[i + 2]?.getD 0)
    for (c, k) in colours.zipIdx do
      if px == c then counts := counts.modify k (· + 1)
  return counts

/-- A diagnostic's words and its site's particulars, as its log line shows them. -/
def diagWords (d : Diag) : String := d.message ++ (d.detail.map ("\n" ++ ·)).getD ""

/-- The opening tags of a page's failed-face placeholders, those carrying `data-image-src`. -/
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

/-- Does a compat-index row's call load the row's own package, read off the row's text? -/
def compatRowSelfLoads (pkg call : String) : Bool :=
  hasStr call "\\usepackage" && hasStr call ("{" ++ pkg ++ "}")

/-- The scaffold a compat-index row's call stands in at its place, its package loaded where `load`;
a `statement` call stands in an amsthm lemma labelled `lem:probe`. -/
def compatRowScaffold (load : Bool) (pkg place call : String) : String :=
  let load := if load then s!"\\usepackage\{{pkg}}\n" else ""
  if place == "statement" then
    s!"\\documentclass\{article}\n\\usepackage\{amsthm}\n{load}\\newtheorem\{lemma}\{Lemma}\n\
\\begin\{document}\n\\begin\{lemma}\\label\{lem:probe}\n{call}\nx\n\\end\{lemma}\n\\end\{document}"
  else if place == "pre" then
    s!"\\documentclass\{article}\n{load}{call}\n\\begin\{document}\nx\n\\end\{document}"
  else if place == "frame" then
    let isClass := Compat.presentationClasses.contains pkg
    let cls := if isClass then pkg else "beamer"
    let load := if isClass then "" else load
    s!"\\documentclass\{{cls}}\n{load}\\begin\{document}\n\\begin\{frame}\n{call}\n\\end\{frame}\n\\end\{document}"
  else
    s!"\\documentclass\{article}\n{load}\\begin\{document}\n{call}\n\\end\{document}"

/-- The document a compat-index row elaborates as: the call at its place, its package loaded unless
the call loads it. -/
def compatRowSrc (pkg place call : String) : String :=
  compatRowScaffold (!compatRowSelfLoads pkg call) pkg place call

/-- The document a compat-index row elaborates as with its call taken out, its package's load with
it where the call was the load. -/
def compatRowBase (pkg place call : String) : String :=
  compatRowScaffold (!compatRowSelfLoads pkg call) pkg place ""

/-- Whole-name occurrences of `word` whose preceding source passes `keep`. -/
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

/-- How many times `word` stands in `text` as a whole name, not inside an identifier or after a
dot. -/
def wordCount (text word : String) : Nat :=
  wordCountWhere text word fun _ => true

def censusText (c : Array CensusPage) : String :=
  String.intercalate " " (c.toList.map (·.text))

/-- Markup characters no page may ship as ink: in prose `$`, `&`, `^`, `_` and `~` are content, a
backslash or a brace never. -/
def inkMarkupWatch : List Char := ['\\', '{', '}']

def pageHas (c : Array CensusPage) (i : Nat) (needle : String) : Bool :=
  (c[i]?.map fun p => hasStr p.text needle).getD false

/-- How many times `needle` is inked on page `i`. -/
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

/-- The largest run size of the first shipped line on page `i` containing `needle`. -/
def lineSizeOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map (·.size)

/-- The rule segments shipped on page `i`, in line order: (baseline, thickness). -/
def pageRuleSegs (c : Array CensusPage) (i : Nat) : Array (Dim.Sp × Dim.Sp) :=
  (c[i]?.map (·.ruleSegs)).getD #[]

/-- The right edge of the first shipped line on page `i` containing `needle`. -/
def lineRightOf (c : Array CensusPage) (i : Nat) (needle : String) : Option Dim.Sp :=
  (c[i]?.bind fun p => p.lines.find? fun l => hasStr l.text needle).map
    fun l => l.x + l.width

/-- The glyph text of one shipped line, a gap as one space unless `gapAsSpace := false`. -/
def lineText (l : Layout.LineOut) (gapAsSpace : Bool := true) : String :=
  l.segs.foldl (fun s seg => match seg with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => glyphs.foldl (fun s (_, c, _) => s.push c) s
    | .gap _ _ | .decoratedGap _ _ _ => if gapAsSpace then s.push ' ' else s
    | _ => s) ""

/-- Word spaces ship as gaps, not glyphs: a line is found by its letters. -/
def letters (text : String) : String := text.replace " " ""

/-- The baseline of a page's first body line whose text opens with `word`, any case, past a list's
marker. -/
def openingLineY (page : Layout.PageOut) (word : String) : Option Dim.Sp :=
  (page.lines.find? fun l =>
    !l.furniture &&
      (String.ofList ((lineText l).toLower.toList.dropWhile (!·.isAlpha))).startsWith
        word.toLower).map (·.y)

/-- The distance from a probe page's `Alpha` line down to its `Omega` line. -/
def probeSpan (page : Layout.PageOut) : Option Dim.Sp := do
  pure ((← openingLineY page "omega") - (← openingLineY page "alpha"))

/-- Where a character first stands on a shipped line. -/
def glyphX (l : Layout.LineOut) (wanted : Char) : Option Dim.Sp := Id.run do
  let mut x := l.x
  for s in l.segs do
    match s with
    | .run _ _ _ w glyphs _ _ _ _ _ _ =>
      let mut pen := x
      for (_, c, advance) in glyphs do
        if c == wanted then return some pen
        pen := pen + advance
      x := x + w
    | .gap w _ | .decoratedGap w _ _ | .decoration _ w _ _ _
    | .rule w _ _ _ | .image _ w _ _ => x := x + w
    | .poly _ _ => pure ()
  return none

/-- A shipped line's runs, left to right: face index, glyphs, left edge and width. -/
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
    | .image _ w _ _ => x := x + w
  return out

/-- Material 3's disliked region as the box `scripts/dislike-oracle.lean` holds it in, stated here so
a guard does not read the predicate it guards. -/
def dislikedBox (c : Ir.Color) : Bool :=
  let l := Oklab.labOf c
  let h := Oklab.hueMilli l.a l.b
  decide (86700 ≤ h) && decide (h ≤ 110400) &&
    decide ((36 * 10 ^ 15) * (36 * 10 ^ 15) ≤ Oklab.chromaSq l) && decide (Contrast.luminance c ≤ 3343000)

/-- A colour `pct`% over a ground per 8-bit sRGB channel, rounded, as a browser composites opacity
and xcolor mixes, restated here. -/
def srgbOver (pct : Nat) (ground c : Ir.Color) : Ir.Color :=
  let ch (x y : UInt8) : UInt8 := UInt8.ofNat ((x.toNat * pct + y.toNat * (100 - pct) + 50) / 100)
  { r := ch c.r ground.r, g := ch c.g ground.g, b := ch c.b ground.b }

/-- A text colour's covered forms at a share on a page: mixed toward it in Oklab and in sRGB. -/
def coverForms (share : Nat) (page c : Ir.Color) : List Ir.Color :=
  [Oklab.cover share page c, srgbOver share page c]

/-- The colour of the run setting exactly `word`, with the ground it stands on. -/
def wordRun (lines : Array Layout.LineOut) (word : String) : Option (Ir.Color × Option Ir.Color) :=
  lines.findSome? fun l => l.segs.findSome? fun s => match s with
    | .run _ c _ _ gs _ _ _ _ ground _ =>
      if String.ofList (gs.map (·.2.1)).toList == word then some (c, ground) else none
    | _ => none

/-- Whether a shipped line sets any glyph. -/
def hasGlyphRun (l : Layout.LineOut) : Bool :=
  l.segs.any fun s => match s with
    | .run _ _ _ _ glyphs _ _ _ _ _ _ => !glyphs.isEmpty
    | _ => false

/-- Reject diagnostics that would make a placement comparison lose its text. -/
def noDroppedGlyph (out : Layout.Out) : Bool :=
  !out.diags.any fun d => d.kind == .E0405 || d.kind == .W0009

/-- A line's text as a reader sees it: `lineText`, a glyphless tie read as a space. -/
def lineInk (l : Layout.LineOut) : String := l.segs.foldl (fun s seg => match seg with
  | .run _ _ _ _ glyphs _ _ _ _ _ _ =>
    if glyphs.isEmpty then s.push ' ' else glyphs.foldl (fun s (_, c, _) => s.push c) s
  | .gap _ _ | .decoratedGap _ _ _ => s.push ' '
  | _ => s) ""

/-- The head and foot furniture baselines a geometry owes under `font`'s ink and a declared gap. -/
def furnYs (font : Font) (geom : Layout.Geom)
    (gap : Option Dim.Sp := none) : Dim.Sp × Dim.Sp :=
  let scale (u : Int) : Dim.Sp := u * geom.fontSize / (font.unitsPerEm : Int)
  let band := Layout.furnitureBand geom.vmargin
    (scale font.ascent + scale (-font.descent)) gap
  (Layout.furnHeadY band (scale font.ascent),
   Layout.furnFootY band geom.pageH (scale (-font.descent)))

mutual

/-- The text content of an emitted HTML node, markup stripped. -/
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

/-- The first attribute `key` an emitted tree declares, in document order. -/
def firstAttrOne (key : String) : Html.Node → Option String
  | .text _ => none
  | .style _ => none
  | .script _ _ => none
  | .elem _ attrs kids =>
    match attrs.find? (fun (k, _) => k == key) with
    | some (_, v) => some v
    | none => firstAttrList key kids.toList

def firstAttrList (key : String) : List Html.Node → Option String
  | [] => none
  | k :: rest => match firstAttrOne key k with
    | some v => some v
    | none => firstAttrList key rest

end

mutual

/-- The text an emitted page shows a reader with no snap state (`HtmlDoc.altPairNodes`), every
`hidden` subtree dropped. -/
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

/-- An emitted attribute's value, or nothing. -/
def snapAttr (attrs : Array (String × String)) (key : String) : String :=
  ((attrs.find? (·.1 == key)).map (·.2)).getD ""

/-- Does snap `k` select an element's steps, read off its emitted attributes alone? -/
def snapActive (attrs : Array (String × String)) (k : Nat) : Bool :=
  if attrs.any (·.1 == "data-steps") then
    (snapAttr attrs "data-steps").splitOn " " |>.contains (toString k)
  else
    let lo := (snapAttr attrs "data-step").toNat?.getD 1
    let hi := (snapAttr attrs "data-step-last").toNat?
    lo ≤ k && (hi.map fun u => decide (k ≤ u)).getD true

/-- Does an element show at snap `k`: an alternative where its steps select
it, anything else unless it is `hidden`. -/
def snapShows (attrs : Array (String × String)) (k : Nat) : Bool :=
  let classes := (snapAttr attrs "class").splitOn " "
  if classes.contains "alt-set" then snapActive attrs k
  else if classes.contains "alt-crisp" then snapActive attrs k
  else if classes.contains "alt-pending" then !snapActive attrs k
  else !(attrs.any (·.1 == "hidden"))

mutual

/-- The text an emitted tree shows at snap `k`, every alternative its snap
does not select left out. -/
def snapTextOne (k : Nat) (acc : String) : Html.Node → String
  | .text s => acc ++ s
  | .style _ | .script _ _ => acc
  | .elem _ attrs kids => if snapShows attrs k then snapTextList k acc kids.toList else acc

def snapTextList (k : Nat) (acc : String) : List Html.Node → String
  | [] => acc
  | n :: rest => snapTextList k (snapTextOne k acc n) rest

end

/-- How many times `needle` is declared in an emitted tree. -/
def treeOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((nodeTextList "" nodes.toList).splitOn needle).length - 1

/-- How many times `needle` is shown by an emitted tree, hidden subtrees excluded. -/
def treeShownOccurs (nodes : Array Html.Node) (needle : String) : Nat :=
  ((shownTextList "" nodes.toList).splitOn needle).length - 1

mutual

/-- Every chrome footer in the emitted deck, in document order, as its two slots' text. -/
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

/-- Every chrome footer the PDF ships, in page order, as its two slots' text. -/
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

/-- Adjacent equal pairs collapsed, as a stepped frame's pages share one footer. -/
def dedupConsecutive (xs : Array (String × String)) : Array (String × String) :=
  xs.foldl (fun acc p => if acc.back? == some p then acc else acc.push p) #[]

mutual

/-- Every character a tree's text holds, in order, with the styles and preorder indices of the
elements around it. -/
def shownCharsOne (styles : List (String × Nat)) (acc : Array (Char × List (String × Nat)) × Nat) :
    Html.Node → Array (Char × List (String × Nat)) × Nat
  | .text s => (s.toList.foldl (fun a c => a.push (c, styles)) acc.1, acc.2)
  | .style _ => acc
  | .script _ _ => acc
  | .elem _ attrs kids =>
    let styles := match attrs.find? (·.1 == "style") with
      | some (_, v) => styles ++ [(v, acc.2)]
      | none => styles
    shownCharsList styles (acc.1, acc.2 + 1) kids.toList

def shownCharsList (styles : List (String × Nat)) (acc : Array (Char × List (String × Nat)) × Nat) :
    List Html.Node → Array (Char × List (String × Nat)) × Nat
  | [] => acc
  | k :: rest => shownCharsList styles (shownCharsOne styles acc k) rest

/-- Every element with its subtree text and its style as the light screen reads it against the
properties in scope. -/
def elemStylesIn (vars : List (String × String)) (acc : Array (String × String)) :
    Html.Node → Array (String × String)
  | .text _ => acc
  | .style _ => acc
  | .script _ _ => acc
  | .elem t attrs kids =>
    let raw := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let vars := styleVars raw ++ vars
    let acc := acc.push (nodeTextOne "" (.elem t attrs kids), lightStyle vars raw)
    elemStylesListIn vars acc kids.toList

def elemStylesListIn (vars : List (String × String)) (acc : Array (String × String)) :
    List Html.Node → Array (String × String)
  | [] => acc
  | k :: rest => elemStylesListIn vars (elemStylesIn vars acc k) rest

end

mutual

/-- Every element with its subtree text and its own style as written. -/
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

/-- Is a diagnostic a contrast report a bundle's lineage owes (`Theme.reported`)? -/
def reportedContrast (d : Diag) : Bool :=
  (d.kind == .W0315 || d.kind == .W0345) && d.subject.any fun k =>
    Theme.builtin.any fun th => th.reported.any fun r =>
      let key := (Ir.ColorRef.role r).key
      k.startsWith (key ++ ":") || k == "covered:" ++ key

/-- Every character a list of nodes holds, with its elements' styles. -/
def shownChars (nodes : List Html.Node) : Array (Char × List (String × Nat)) :=
  (shownCharsList [] (#[], 0) nodes).1

/-- Every element with its style as the light screen reads it, from no property in scope. -/
def elemLightStyles (nodes : List Html.Node) : Array (String × String) :=
  elemStylesListIn [] #[] nodes

/-- The source with string literals, char literals and comments blanked, so a scan reads code
proper. -/
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
        let mut j := i + 2
        for _ in [0:8] do
          if cs[j]? == some '\'' then break
          j := j + 1
        for _ in [i:j+1] do
          out := out.push ' '
        i := j + 1
      else if c == '\'' && cs[i + 2]? == some '\'' && cs[i + 1]? != some '\'' then
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

/-- The `DiagCode` constructors a stripped source applies, by dot-applied code-shaped tokens. -/
def appliedCodes (stripped : String) : List String := Id.run do
  let mut out : List String := []
  for part in (stripped.splitOn ".").drop 1 do
    let tok := String.ofList (part.toList.takeWhile Char.isAlphanum)
    if isDiagCode tok && !out.contains tok then
      out := tok :: out
  return out

/-- The engine's sources, path-sorted, with the codes each applies; `Diag.lean`, which names every
code, left out. -/
def codeSources : IO (Array (String × List String)) := do
  let mut files := (← System.FilePath.walkDir "LeanTex").filter
    (·.toString.endsWith ".lean")
  files := files.push "Main.lean"
  let mut out : Array (String × List String) := #[]
  for f in files.qsort (·.toString < ·.toString) do
    if f.toString == "LeanTex/Core/Diag.lean" then continue
    out := out.push (f.toString, appliedCodes (stripNonCode (← IO.FS.readFile f)))
  return out

/-- Bytes written big-endian, as a font file's fields are. -/
def pushBe16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v / 256 % 256).toUInt8).push (v % 256).toUInt8

def pushBe32 (b : ByteArray) (v : Nat) : ByteArray :=
  pushBe16 (pushBe16 b (v / 65536 % 65536)) (v % 65536)

/-- A standalone font's tables in directory order: tag, checksum and bytes. -/
def fontTables (f : ByteArray) : Array (Nat × Nat × ByteArray) :=
  (Array.range (Ink.u16 f 4)).map fun k =>
    let e := 12 + 16 * k
    let off := Ink.u32 f (e + 8)
    (Ink.u32 f e, Ink.u32 f (e + 4), f.extract off (off + Ink.u32 f (e + 12)))

/-- A font collection packed from standalone fonts as the OpenType spec lays one out, by an encoder
independent of the engine. -/
def packCollection (fonts : Array ByteArray) : ByteArray := Id.run do
  let faces := fonts.map fontTables
  let mut pos := 12 + 4 * fonts.size
  let mut dirAt : Array Nat := #[]
  for ts in faces do
    dirAt := dirAt.push pos
    pos := pos + 12 + 16 * ts.size
  let mut tableAt : Array (Array Nat) := #[]
  for ts in faces do
    let mut row : Array Nat := #[]
    for (_, _, b) in ts do
      row := row.push pos
      pos := (pos + b.size + 3) / 4 * 4
    tableAt := tableAt.push row
  let mut out := pushBe32 (pushBe32 (pushBe32 ByteArray.empty 0x74746366) 0x00010000) fonts.size
  for d in dirAt do
    out := pushBe32 out d
  for (f, ts, row) in fonts.zip (faces.zip tableAt) do
    out := out ++ f.extract 0 12
    for ((tag, sum, b), place) in ts.zip row do
      out := pushBe32 (pushBe32 (pushBe32 (pushBe32 out tag) sum) place) b.size
  for ts in faces do
    for (_, _, b) in ts do
      out := out ++ b
      for _ in [0:(b.size + 3) / 4 * 4 - b.size] do
        out := out.push 0
  return out

/-- A document laid out as the driver hands it to the backends, math alphabet scopes resolved
first. -/
def layoutOf (fonts : Font.FontSet) (doc : Ir.Doc)
    (geom : Layout.Geom := Layout.Geom.ofPage doc.page)
    (pats : Option Hyphen.Patterns := none)
    (imgs : Image.Store := {}) (ship : Bool := true) : Layout.Out :=
  let family := fonts.math.bind (fonts.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (doc, alphaDiags) := Ir.resolveMathAlphas fonts.mathAlphabets family doc
  let out := Layout.run geom fonts pats doc imgs
  { out with pages := if ship then out.pages.map Layout.PageOut.shipped else out.pages
             diags := alphaDiags ++ out.diags }

/-- A document set through the overflow ladder (`Layout.runFitted`), resolved as `layoutOf` resolves
it. -/
def fittedOf (fonts : Font.FontSet) (doc : Ir.Doc)
    (geom : Layout.Geom := Layout.Geom.ofPage doc.page)
    (pats : Option Hyphen.Patterns := none)
    (imgs : Image.Store := {}) : Layout.Fitted :=
  let family := fonts.math.bind (fonts.fonts[·]?) |>.map (·.family) |>.getD "math face"
  let (doc, alphaDiags) := Ir.resolveMathAlphas fonts.mathAlphabets family doc
  let f := Layout.runFitted geom fonts pats doc imgs
  { f with out := { f.out with diags := alphaDiags ++ f.out.diags } }

/-- A source's elaboration and overflow-ladder diagnostics as a build names them, each frame at the
site its environment opens. -/
def sitedFitDiags (fonts : Font.FontSet) (src : String) : Array Diag :=
  let prepared := Elab.prepare "t" (Parse.parse "t" (Lex.lex "t" src).1).1
  let (doc, ds, sites) := Elab.runPrepared "t" prepared
  ds ++ (Layout.runFitted (Layout.Geom.ofPage doc.page) fonts none doc {}
    (Layout.frameSpansForPdf doc sites.frames)).out.diags

/-- The font set a golden fixture lays out under: `oneFace`, the math face a build would resolve,
and fallback faces for icon scalars. -/
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

/-- The shipped Fira Math beside `oneFace` in the math slot. -/
def mathSetOf (oneFace : Font.FontSet) : IO Font.FontSet := do
  let fira ← match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraMath-Regular.otf")) with
    | .ok f => pure f
    | .error e => throw (IO.userError s!"fixture fonts: FiraMath unparsable: {e}")
  return { oneFace with
    fonts := oneFace.fonts.push fira
    math := some oneFace.fonts.size
    mathAlphabets := fira.mathAlphabetCoverage {} }

/-- The four shipped Source Serif faces in slots 0–3 and Fira Math in 4, so a run's face index says
its weight, slant and whether it is maths. -/
def serifFacesSet : IO (Option Font.FontSet) := do
  let mut loaded : Array Font := #[]
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

/-- The structure leaves of a deck's top-level sections that stand on no page of their own
(`Ir.Doc.outside`), whose titles ship no ink. -/
def navSectionLeaves (doc : Ir.Doc) : Array Nat := Id.run do
  if doc.docClass.record.model != .frame then return #[]
  let mut next := 0
  let mut out : Array Nat := #[]
  for b in doc.body do
    let n := Struct.leafCountBlocks #[b]
    if b matches .section .. && doc.outside b == .none then
      out := out ++ (Array.range n).map (next + ·)
    next := next + n
  return out

/-- Every shipped line, furniture included, in page order. -/
def allLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines)

/-- Every shipped line but engine-placed furniture, in page order. -/
def bodyLines (out : Layout.Out) : Array Layout.LineOut :=
  out.pages.flatMap (·.lines.filter (!·.furniture))

/-- The inks of every glyph run on a line whose text `keep` accepts. -/
def inksOn (out : Layout.Out) (keep : String → Bool) : Array Ir.Color :=
  (allLines out).filter (fun l => keep (lineText l)) |>.flatMap fun l =>
    l.segs.filterMap fun
      | .run _ ink _ _ glyphs .. => if glyphs.isEmpty then none else some ink
      | _ => none

/-- A markdown code fence's shipped lines, `lang` its info string. -/
def codeFenceLines (fonts : Font.FontSet) (lang code : String) : Array Layout.LineOut :=
  bodyLines (layoutOf fonts (elabMd ("```" ++ lang ++ "\n" ++ code ++ "\n```\n")).1)

/-- The distances between consecutive body baselines, in page order. -/
def baselinePitches (out : Layout.Out) : Array Dim.Sp :=
  let lines := bodyLines out
  (lines.zip (lines.extract 1 lines.size)).map fun (a, b) => b.y - a.y

/-- Every shipped line's position, size and text, furniture included, in page order. -/
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
    | .image _ w _ _ => x := x + w
  return out

/-- A body glyph's shipped position and paint, independent of run segmentation and leaf
numbering. -/
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

/-- Body glyphs in paint order, every `ShippedGlyph` field kept. -/
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
          | .decoration _ width _ _ _ | .image _ width _ _ => x := x + width
        | .poly _ _ => pure ()
  return acc

namespace ShippedInk

/-- An outline hull in page coordinates, y up, control points included. -/
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

/-- Disjoint interiors of quantized outline hulls: a conservative ink-separation check. -/
def InkBounds.disjoint (a b : InkBounds) : Bool :=
  a.right ≤ b.left || b.right ≤ a.left || a.top ≤ b.bottom || b.top ≤ a.bottom

def InkBounds.inRoom (b : InkBounds) (left right : Dim.Sp) : Bool :=
  left ≤ b.left && b.right ≤ right

def polygonHull (points : Array (Dim.Sp × Dim.Sp)) : Option InkBounds := do
  let (x, y) ← points[0]?
  return points.foldl (fun b (px, py) => b.union ⟨px, py, px, py⟩) ⟨x, y, x, y⟩

/-- A shipped glyph's outline hull at its pen, size and baseline; missing outlines fail. -/
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

/-- Whether a shipped glyph has outline commands; an undecodable outline fails. -/
def glyphPaints (fonts : Font.FontSet) (g : ShippedGlyph) : Except String Bool := do
  let some font := fonts.fonts[g.face]? | throw "target face is missing"
  let some cmds := font.inkSrc.get.cmdsAt g.glyph | throw "target outline is missing"
  return !cmds.isEmpty

/-- The union of the target glyphs' ink, empty outlines ignored. -/
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

/-- Polygon origins from the line pen, advancing through every width-bearing segment. -/
def polygonPens (line : Layout.LineOut) : Array (Dim.Sp × Array (Dim.Sp × Dim.Sp)) := Id.run do
  let mut pen := line.x
  let mut polys := #[]
  for seg in line.segs do
    match seg with
    | .run _ _ _ w _ _ _ _ _ _ _ | .gap w _ | .decoratedGap w _ _
    | .rule w _ _ _ | .decoration _ w _ _ _ | .image _ w _ _ =>
      pen := pen + w
    | .poly points _ => polys := polys.push (pen, points)
  return polys

/-- Shipped polygons in `glyphInk`'s upward page coordinates. -/
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
    | .rule _ _ _ _ | .decoration _ _ _ _ _ | .poly _ _ | .image _ _ _ _ => pure ()
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

/-- The glyphs a source's `lines` ship, in page order: its body lines unless `lines` says otherwise;
`geom` defaults to the document's own page. -/
def pageTextOf (fonts : Font.FontSet) (src : String) (geom : Option Layout.Geom := none)
    (lines : Layout.Out → Array Layout.LineOut := bodyLines) : String :=
  let (d, _) := elabStr src
  String.join ((lines (layoutOf fonts d (geom.getD (Layout.Geom.ofPage d.page)))).toList.map
    (lineText ·))

/-- Both complete artifacts of a source, with diagnostics and visible HTML text. -/
def sourceArtifacts (fonts : Font.FontSet) (source : String) :
    Array Diag × Layout.Out × String × String :=
  let (doc, ds) := elabStr source
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  (ds ++ out.diags ++ hds, out, Html.document "en" head tree,
    shownTextList "" tree.toList)

mutual
/-- A control's `{block}`s renamed to the box a tcolorbox lowers to (`Tcolorbox.boxEnv`). -/
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

/-- `sourceArtifacts` of a control whose `{block}`s stand for lowered boxes. -/
def boxedSourceArtifacts (fonts : Font.FontSet) (source : String) :
    Array Diag × Layout.Out × String × String :=
  let (toks, lexDiags) := Lex.lex "t" source
  let (raws, parseDiags) := Parse.parse "t" toks
  let (doc, ds) := Elab.runRaws "t" (boxedRaws #[] raws.toList) (lexDiags ++ parseDiags)
  let out := layoutOf fonts doc
  let (head, tree, hds) := HtmlDoc.emitTree {} doc
  (ds ++ out.diags ++ hds, out, Html.document "en" head tree,
    shownTextList "" tree.toList)

/-- A source and its literal control ship the same visible text in both artifacts, whitespace
aside. -/
def sourceTextChecks (ref : IO.Ref (List String)) (fonts : Font.FontSet)
    (label source control : String) : IO Unit := do
  let ink (s : String) := String.ofList (s.toList.filter (!·.isWhitespace))
  let (doc, ds) := elabStr source
  let (_, tree, hds) := HtmlDoc.emitTree {} doc
  let (_, expectedTree, _) := HtmlDoc.emitTree {} (elabStr control).1
  check ref (label ++ ": no loss") ((ds ++ hds).all (·.severity == .note))
  check ref (label ++ ": shipped layout")
    (ink (pageTextOf fonts source (lines := allLines)) ==
      ink (pageTextOf fonts control (lines := allLines)))
  check ref (label ++ ": typed HTML")
    (ink (shownTextList "" tree.toList) == ink (shownTextList "" expectedTree.toList))

/-- Elaboration diagnostics of a source. -/
def dvE (src : String) (w : WitnessRun := {}) : Array Diag := (w.elab src).2

/-- Spans carrying more than one diagnostic, as code pairs with their count. -/
def siteCollisions (ds : Array Diag) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for d in ds do
    for e in ds do
      if d.span.isSome && d.span == e.span && d.code < e.code then
        let pair := (d.code, e.code)
        unless out.contains pair do out := out.push pair
  return out

/-- The shipped-page census of a source laid out with `fonts`. -/
def censusOfSrc (fonts : Font.FontSet) (src : String) : Array CensusPage :=
  let (doc, _) := elabStr src
  censusOf (coveredColorsOf doc) (layoutOf fonts doc)

/-- The laid-out lines of a source: baseline and text. -/
def pageLines (fonts : Font.FontSet) (src : String) : Array (Array (Dim.Sp × String)) :=
  (censusOfSrc fonts src).map (·.lines.map fun l => (l.y, l.text))

/-- Every shipped line of a source: position, size and text. -/
def shippedLines (fonts : Font.FontSet) (src : String) :
    Array (Dim.Sp × Dim.Sp × Dim.Sp × String) :=
  (censusOfSrc fonts src).flatMap fun p => p.lines.map fun l => (l.x, l.y, l.size, l.text)

/-- A source elaborated as the driver elaborates it, against the label measurement layout sets
with. -/
def elabMeasured (fonts : Font.FontSet) (s : String) : Ir.Doc × Array Diag :=
  let (toks, lds) := Lex.lex "t" s
  let (raws, pds) := Parse.parse "t" toks
  Elab.runRaws "t" raws (lds ++ pds)
    (Layout.labelMetric (Layout.Geom.ofPage (Elab.run "t" s).1.page) fonts)

/-- Does a block of the document's title block, or one inside its `.center` wrapper, satisfy `p`? -/
def inTitleBlock (doc : Ir.Doc) (p : Ir.Block → Bool) : Bool :=
  doc.body.any fun b => p b ||
    (match b with | .center xs => xs.any p | _ => false)

/-- Diagnostics after layout too, through the same alphabet resolution. -/
def dvL (fonts : Font.FontSet) (src : String) (w : WitnessRun := {}) : Array Diag :=
  let (doc, ds) := w.elab src
  ds ++ (layoutOf fonts doc).diags

/-- Diagnostics after layout through the overflow ladder (`fittedOf`). -/
def dvF (fonts : Font.FontSet) (src : String) (w : WitnessRun := {}) : Array Diag :=
  let (doc, ds) := w.elab src
  ds ++ (fittedOf fonts doc).out.diags

/-- Diagnostics after the HTML backend. -/
def dvH (src : String) (w : WitnessRun := {}) : Array Diag :=
  let (doc, ds) := w.elab src
  ds ++ (HtmlDoc.emit {} doc).2

/-- A one-face set: every slot and variant maps to index 0. -/
def oneFaceOf (font : Font) : Font.FontSet := Font.FontSet.ofFace font

/-- The shipped Fira Sans as a one-face set, or `none`. -/
def shippedFira : IO (Option Font.FontSet) := do
  match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
  | .ok f => pure (some (oneFaceOf f))
  | .error _ => pure none

/-- The shipped Fira Sans as a face, or `none`. -/
def shippedFiraFont : IO (Option Font) := do
  match Font.parse (← IO.FS.readBinFile (testFonts ++ "/FiraSans-Regular.otf")) with
  | .ok f => pure (some f)
  | .error _ => pure none

/-- A measurement in thousandths of a point. -/
def ptMilli (milli : Int) : Dim.Sp := Dim.pt 1 * milli / 1000

/-- A 10 pt beamer deck under `theme`, each frame its options and body. -/
def beamerDeck (theme : String) (frames : List (String × String)) : String :=
  s!"\\documentclass[10pt]\{beamer}\n{theme}\\begin\{document}\n" ++
  String.join (frames.map fun (opt, body) =>
    s!"\\begin\{frame}[{opt}]\n{body}\n\\end\{frame}\n") ++
  "\\end{document}\n"

/-- The baseline of the first body line holding `word` on page `page`. -/
def bodyLineY (out : Layout.Out) (page : Nat) (word : String) : Option Dim.Sp :=
  (out.pages[page]?.bind fun p => p.lines.find? fun l =>
    !l.furniture && hasStr (lineText l) word).map (·.y)

/-- A CSS length in `em` as thousandths of the em. -/
def cssEmMilli (v : String) : Option Int := do
  guard (v.endsWith "em")
  let (m, sc) ← Decl.parseDecimal (v.dropEnd 2).toString
  return m * 1000 / (sc : Int)

/-- Two lengths within `slack` of each other. -/
def withinSp (slack a b : Dim.Sp) : Bool := a - b ≤ slack && b - a ≤ slack

/-- Two faces over the three slots (roman 0, sans 1, typewriter 2): `other` in slot `slot` and
`base` in the rest, so a run's face says which (`CensusLine.runFonts`). -/
def slotPairOf (slot : Nat) (base other : Font) : Font.FontSet := {
  fonts := #[base, other]
  index := ((List.range 3).flatMap fun s =>
    let f := if s == slot then 1 else 0
    [((s, 400, false), f), ((s, 700, false), f),
     ((s, 400, true), f), ((s, 700, true), f)]).toArray
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

/-- A colour's Oklab chroma (at `Oklab.labOf`'s scale) and hue in
millidegrees. -/
def lchOf (c : Ir.Color) : Int × Int :=
  let l := Oklab.labOf c
  (Nat.sqrt (Oklab.chromaSq l).toNat, Oklab.hueMilli l.a l.b)

/-- A colour's Oklab hue in millidegrees. -/
def hueOf (c : Ir.Color) : Int := (lchOf c).2

/-- Millidegrees between two hues, the short way round. -/
def hueGap (h h' : Int) : Int :=
  let d := (h - h' + 540000) % 360000 - 180000
  if d < 0 then -d else d

/-- A shipped bundle's palette as a deck installs it (`Theme.realize`). -/
def deckBundle (th : Theme) : Ir.Palette := th.realize .decks

/-- moloch's progress bar as a deck installs it: its fill and its track. -/
def molochProgress (_ : Unit) : Ir.Color × Ir.Color :=
  match (Ir.Design.ofPalette (deckBundle Theme.moloch)).progress with
  | some p => (p.fg, p.bg)
  | none => (Ir.Color.black, Ir.Color.black)

/-- A registry role's undeclared colour in one scheme (`Ir.Role.row`'s columns). -/
def screenColor (s : Ir.Scheme) (r : Ir.Role) : Ir.Color :=
  (Ir.Design.at {} s r).getD Ir.Color.black

/-- The stylesheets a page carries in its `<style>` elements, or the text itself when it carries
none. -/
def pageSheets (page : String) : String :=
  match page.splitOn "<style" with
  | _ :: parts@(_ :: _) =>
    String.join (parts.map fun p =>
      (((">".intercalate ((p.splitOn ">").drop 1)).splitOn "</style>").headD "") ++ "\n")
  | _ => page

/-- Every innermost declaration block of a stylesheet: its at-rule depth, selector and
declarations. -/
def artCssRules (css : String) : Array (Nat × String × String) :=
  (sheetRules css).filterMap fun (conds, sel, decls) =>
    if decls.contains ':' then some (conds.length, sel, decls) else none

/-- Every innermost declaration block, as its selector and declarations. -/
def artCssBlocks (css : String) : Array (String × String) := (artCssRules css).map (·.2)

/-- The blocks outside every at-rule. -/
def artTopCssBlocks (css : String) : Array (String × String) :=
  (artCssRules css).filterMap fun (d, b) => if d == 0 then some b else none

/-- The declarations of every innermost block for selector `sel` exactly, nested at-rules
included. -/
def cssBlocksFor (css sel : String) : List String :=
  ((artCssBlocks css).toList.filter (·.1 == sel)).map (·.2)

/-- The value of the last declaration of `key` in a declaration list, `!important` unread. -/
def cssProperty (decls key : String) : Option String := lastDecl (cssDecls decls) key

/-- A selector list's top-level parts, a comma inside parentheses kept in its part. -/
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

/-- The declarations of every rule for selector `sel` exactly that `holdsIn .light` keeps, in order,
from a stylesheet or a page carrying one. -/
def screenRulesOf (css sel : String) : List String :=
  ((sheetRules (pageSheets css)).toList.filter fun (conds, s, _) =>
    s == sel && conds.all (holdsIn .light ·)).map (·.2.2)

/-- The first of `screenRulesOf`'s rules. -/
def screenRuleOf (css sel : String) : Option String := (screenRulesOf css sel).head?

/-- A length in sp as thousandths of a point, rounded to nearest. -/
def spMilli (d : Dim.Sp) : Int := (d * 1000 + 32768) / 65536

/-- 2 thousandths of a point: the rounding a lualatex probe's printed decimals carry into TeX
points. -/
def probeTolerance : Int := 2

/-- A CSS length in `rem` as thousandths of a rem, or nothing for any other spelling. -/
def remMilliOf (value : String) : Option Int := do
  let value := value.trimAscii.toString
  guard (value.endsWith "rem")
  let (m, sc) ← Decl.parseDecimal (value.dropEnd 3).toString
  return m * 1000 / (sc : Int)

/-- The custom properties the light screen's `:root` rules declare in a stylesheet or a page carrying
one, newest first, each value read on its light side. -/
def screenRootVars (css : String) : List (String × String) :=
  (schemeRoot (pageSheets css) .light).1.map fun (k, v) => (k, lightSide v)

/-- The colour each token class's rule reads (`HtmlDoc.tokenRules`). -/
def tokenClassColors (css : String) : List (String × String) :=
  (sheetRules css).toList.flatMap fun (conds, sel, decls) =>
    if !conds.isEmpty || !sel.startsWith ":is(.tok-" then [] else
    match cssProperty decls "color" with
    | some v => (((sel.drop 4).dropEnd 1).toString.splitOn ",").map fun c =>
        ((c.trimAscii.toString.drop 1).toString, v)
    | none => []

/-- A style with each ordinary declaration read on one side of its `light-dark()` pairs against
`vars`. -/
def sideStyle (dark : Bool) (vars : List (String × String)) (style : String) : String :=
  "; ".intercalate ((style.splitOn ";").filterMap fun decl =>
    match decl.splitOn ":" with
    | k :: rest@(_ :: _) =>
      let key := k.trimAscii.toString
      let v := (":".intercalate rest).trimAscii.toString
      some s!"{key}: {if key.startsWith "--" then v else schemeRead dark vars v}"
    | _ => if decl.trimAscii.isEmpty then none else some decl.trimAscii.toString)

mutual

/-- An element with its style as one scheme reads it, and a token's class colour written first as
its own. -/
def schemeTreeOne (dark : Bool) (classes : List (String × String)) (vars : List (String × String)) :
    Html.Node → Html.Node
  | .elem t attrs kids =>
    let raw := ((attrs.find? (·.1 == "style")).map (·.2)).getD ""
    let vars := styleVars raw ++ vars
    let cls := ((attrs.find? (·.1 == "class")).map (·.2)).getD ""
    let token := ((cls.splitOn " ").findSome? (classes.lookup ·)).map (schemeRead dark vars)
    let own := sideStyle dark vars raw
    let style := match token with
      | some c => if c.startsWith "#" then
          "color: " ++ c ++ (if own.isEmpty then "" else "; " ++ own) else own
      | none => own
    let attrs := (attrs.filter (·.1 != "style")) ++
      (if style.isEmpty && raw.isEmpty then #[] else #[("style", style)])
    .elem t attrs (schemeTreeList dark classes vars #[] kids.toList)
  | .text x => .text x
  | .style css => .style css
  | .script a js => .script a js

def schemeTreeList (dark : Bool) (classes : List (String × String)) (vars : List (String × String))
    (acc : Array Html.Node) : List Html.Node → Array Html.Node
  | [] => acc
  | n :: rest => schemeTreeList dark classes vars (acc.push (schemeTreeOne dark classes vars n)) rest

end

/-- A typed tree as one scheme paints it (`schemeRoot`, `schemeTreeOne`). -/
def schemeTree (head body : Array Html.Node) (s : Ir.Scheme) : Array Html.Node :=
  let css := treeCssList "" head.toList
  let (root, dark) := schemeRoot css s
  schemeTreeList dark (tokenClassColors css) root #[] body.toList

/-- `HtmlDoc.emitTree`, its body as one scheme paints it (`schemeTree`). -/
def emitIn (cfg : HtmlDoc.Config) (doc : Ir.Doc) (s : Ir.Scheme) :
    Array Html.Node × Array Html.Node × Array Diag :=
  let (head, body, ds) := HtmlDoc.emitTree cfg doc
  (head, schemeTree head body s, ds)

/-- A CSS value with its `var()` references chased through a property table, eight deep; `none`
where one dangles. -/
def chaseCssValue (vars : List (String × String)) (value : String) : Option String :=
  (List.range 8).foldl (fun acc _ => acc.bind fun v =>
    if v.startsWith "var(" && v.endsWith ")" then
      match ((v.drop 4).dropEnd 1).toString.splitOn "," with
      | [] => none
      | key :: rest =>
        match vars.lookup key.trimAscii.toString with
        | some w => some w
        | none =>
          if rest.isEmpty then none else some (String.intercalate "," rest).trimAscii.toString
    else some v) (some value)

/-- Whether a CSS stage length's share matches the shipped PDF length, within one printed
milli-percent. -/
def cssStageLength (style key : String) (length height : Dim.Sp) : Bool :=
  ((style.splitOn ";").findSome? fun decl => do
    let [name, value] := decl.splitOn ":" | none
    if name.trimAscii.toString != key then none else
    let value := value.trimAscii.toString
    if !value.endsWith "vh" then none else
    let (m, sc) ← Decl.parseDecimal (value.dropEnd 2).toString
    return m * 1000 / (sc : Int)).any fun m =>
      m * height ≤ length * 100000 && length * 100000 < (m + 1) * height

/-- The read-side census of produced PDF bytes (`PdfCensus.census`), its refusal as the test's
failure text. -/
def pdfCensusOf (pdf : ByteArray) : Except String PdfCensus.Census :=
  PdfCensus.census pdf

mutual

/-- Every element of a tree whose tag `want` accepts, in document order, as typed nodes. -/
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

/-- The slide stages of an emitted body, in document order. -/
def slideStages (body : Array Html.Node) : Array Html.Node :=
  (elemNodesList (· == "section") #[] body.toList).filter fun n => match n with
    | .elem _ attrs _ => ((HtmlDoc.attrOf? attrs "class").getD "").splitOn " " |>.contains "slide"
    | .text _ | .style _ | .script .. => false

/-- The `flex-grow` a stage's direct children declare, in document order. -/
def stageGrows (stage : Html.Node) : Array String :=
  match stage with
  | .elem _ _ kids => kids.filterMap fun node => match node with
    | .elem _ attrs _ => cssProperty ((HtmlDoc.attrOf? attrs "style").getD "") "flex-grow"
    | .text _ | .style _ | .script .. => none
  | .text _ | .style _ | .script .. => #[]

/-- Each accepted element's tag and attributes, in document order. -/
def elemAttrsList (want : String → Bool) (acc : Array (String × Array (String × String)))
    (nodes : List Html.Node) : Array (String × Array (String × String)) :=
  (elemNodesList want #[] nodes).foldl (fun a n => match n with
    | .elem tag attrs _ => a.push (tag, attrs)
    | _ => a) acc

def elemAttrsOne (want : String → Bool) (acc : Array (String × Array (String × String)))
    (node : Html.Node) : Array (String × Array (String × String)) :=
  elemAttrsList want acc [node]

/-- The formulas of an emitted tree, in document order: the elements carrying `data-tex`. -/
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

/-- An article whose one picture holds a node at (-1,1) labelled `label` under the options
`opts`. -/
def mathLabelSource (label opts : String) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "\\begin{tikzpicture}\n\\node[" ++ opts ++ "] at (-1,1) {" ++ label ++
  "};\n\\end{tikzpicture}\n\\end{document}"

/-- An article whose one picture is a drawn node around `content`. -/
def drawnNodeSource (content : String) : String :=
  "\\documentclass{article}\\pictures{tool=none}\\begin{document}\n" ++
  "\\begin{tikzpicture}\n\\node[draw] at (0,0) {" ++ content ++
  "};\n\\end{tikzpicture}\n\\end{document}"

/-- An element's own attribute `key`, empty where it declares none. -/
def nodeAttr (key : String) : Html.Node → String
  | .elem _ attrs _ => (attrs.find? (·.1 == key)).map (·.2) |>.getD ""
  | _ => ""

def nodeKids : Html.Node → Array Html.Node
  | .elem _ _ kids => kids
  | _ => #[]

/-- An element's own inline declaration of CSS property `key`, empty where it declares none. -/
def nodeCss (key : String) (node : Html.Node) : String :=
  (cssProperty (nodeAttr "style" node) key).getD ""

/-- A CSS `em` length scaled to an em of `em` units, rounded after its decimal is read; a unitless
zero reads, any other unit does not. -/
def readEm (em : Int) (s : String) : Option Int := do
  if s == "0" then return 0
  if !s.endsWith "em" then none else do
    let (n, d) ← Decl.parseDecimal (s.dropEnd 2).toString
    return (n * em + (d : Int) / 2) / d

/-- A node's offset in units of `em`, its MathML `lspace` plus its left margin; none when either is
absent or not an em length, `lspace` is negative or the margins do not balance. -/
def readOffset (em : Int) (node : Html.Node) : Option Int := do
  let space ← readEm em (nodeAttr "lspace" node)
  let left ← readEm em (nodeCss "margin-left" node)
  let right ← readEm em (nodeCss "margin-right" node)
  if space < 0 || left + right != 0 then none else some (space + left)

/-- Every value the accepted elements declare for attribute `key`, in document order. -/
def attrValuesOf (want : String → Bool) (key : String) (n : Html.Node) : Array String :=
  (elemAttrsOne want #[] n).filterMap fun (_, attrs) => (attrs.find? (·.1 == key)).map (·.2)

/-- The bibliography natbib's rows cite, one entry per name shape a citation prints differently. -/
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

/-- Entries whose label names and year coincide, so plainnat.bst gives them letters, plus the
`\nocite` rows' entries. -/
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

/-- The calls as one document, each in its own paragraph, the style declared in the preamble. -/
def natbibSrc (pre style : String) (calls : List String) : String := Id.run do
  let mut body := ""
  for call in calls, k in [1:calls.length + 1] do
    body := body ++ s!"L{k} {call} end.\n\n"
  return s!"\\documentclass\{article}\n{pre}\n\\bibliographystyle\{{style}}\n\
    \\begin\{document}\n{body}\\bibliography\{refs}\n\\end\{document}\n"

/-- An HTML page's text as a reader gets it: tags dropped, escaped entities read back. -/
def htmlVisibleText (page : String) : String := Id.run do
  let mut out := ""
  let mut inTag := false
  for c in page.toList do
    if c == '<' then inTag := true
    else if c == '>' then inTag := false
    else if !inTag then out := out.push c
  return ((((out.replace "&lt;" "<").replace "&gt;" ">").replace "&nbsp;" " ").replace
    "&amp;" "&").replace "\u00A0" " "

/-- The reference list's shipped lines, one array per entry. -/
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

/-- A world read off a trace, `dflt` answering every other question. -/
def traceWorld (tr : List Fact) (dflt : (q : Ask) → Reply q) : (q : Ask) → Reply q :=
  fun q => match tr.find? (·.1 == q) with
    | some ⟨q', r⟩ => if h : q' = q then h ▸ r else dflt q
    | none => dflt q

def quiet : (q : Ask) → Reply q
  | .env _ => none
  | .cwd => .error .absent
  | .stat _ => .error .absent
  | .metadata _ => .error .absent
  | .readFile _ => .error .absent
  | .listDir _ => .error .absent
  | .run _ => { ran := .unstarted "unasked", out := "", err := "", complete := false, outputs := #[] }
  | .writeAtomic .. => .error .absent
  | .createDirAll _ => .error .absent

/-- The host with PATH and the working directory replaced. -/
def hybrid (path : Option String) (cwd : Except Failure String) : (q : Ask) → BaseIO (Reply q)
  | .env "PATH" => pure path
  | .cwd => pure cwd
  | q => Host.answer q

def under {α : Type} (path : String) (cwd : Except Failure String) (p : Prog α) : BaseIO α :=
  p.runM (hybrid (some path) cwd)

/-- Whether a run its budget ended was answered after that budget and before
its grace and `hostMarginMs` end, `spent` ms after it was asked. -/
def answeredAtBudget (call : ToolCall) (spent : Nat) : Bool :=
  call.budgetMs ≤ spent && spent < call.budgetMs + call.graceMs + hostMarginMs

end Tests.World

namespace FontScan

/-- A scan record: a family, a corner and its pitch at a path, read from no file. -/
def face (family : String) (fixed : Bool) (bold italic : Bool := false)
    (path : String := family ++ ".otf") : FontDb.Face :=
  { path, family, subfamily := "Regular", bold, italic, fixedPitch := fixed
    weight := if bold then 700 else 400 }

/-- A family's four corners, all at one path. -/
def family4 (family path : String) (fixed : Bool) : Array FontDb.Face :=
  #[face family fixed (path := path), face family fixed (bold := true) (path := path),
    face family fixed (italic := true) (path := path),
    face family fixed (bold := true) (italic := true) (path := path)]

/-- The face index a shipped run holding `needle` sets in, if one does. -/
def runFace (out : Layout.Out) (needle : String) : Option Nat :=
  (bodyLines out).findSome? fun l =>
    (lineRuns l).findSome? fun (f, s, _, _) => if hasStr s needle then some f else none

end FontScan
/-! The SVG boundary's matrices, shared by the suite and the external parity oracle. -/

/-- The red square the refusal bodies stand beside. -/
def svgRedSquare : String := "<rect width=\"20\" height=\"20\" fill=\"red\"/>"

/-- A one-pixel opaque PNG, its bytes spelled out. -/
def tinyPng : ByteArray := bytes [
  0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0x00, 0x00, 0x00, 0x0D, 0x49, 0x48, 0x44, 0x52,
  0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x01, 0x08, 0x02, 0x00, 0x00, 0x00, 0x90, 0x77, 0x53,
  0xDE, 0x00, 0x00, 0x00, 0x0C, 0x49, 0x44, 0x41, 0x54, 0x08, 0xD7, 0x63, 0xF8, 0xCF, 0xC0, 0x00,
  0x00, 0x03, 0x01, 0x01, 0x00, 0x18, 0xDD, 0x8D, 0xB0, 0x00, 0x00, 0x00, 0x00, 0x49, 0x45, 0x4E,
  0x44, 0xAE, 0x42, 0x60, 0x82]

/-- Bodies the boundary admits; `svgBoundaryWidened` names those libxml2's XPath refused. -/
def svgBoundaryAdmitted : List (String × String) :=
  let rect := svgRedSquare
  let moving := "<rect width=\"20\" height=\"20\" fill=\"red\"><animate attributeName=\"opacity\" values=\"0;1;0\" dur=\"2s\" repeatCount=\"indefinite\"/></rect>"
  [
    ("shape", rect),
    ("SMIL", moving),
    ("fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use href=\"#p\"/>"),
    ("fragment paint", "<defs><linearGradient id=\"paint\"><stop stop-color=\"red\"/></linearGradient></defs><rect width=\"20\" height=\"20\" fill=\"url(#paint)\"/>"),
    ("aliased fragment", "<defs><path id=\"p\" d=\"M0 0h20v20z\"/></defs><use xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"&#35;p\"/>"),
    ("predefined and numeric references", "<title>&quot;&apos;&amp;&lt;&gt;&#65;&#x42;</title><rect aria-label=\"&quot;&apos;&amp;&lt;&gt;&#65;&#x42;\" width=\"20\" height=\"20\" fill=\"red\"/>"),
    ("plain style CDATA", "<style><![CDATA[rect { fill: red }]]></style>" ++ rect),
    ("XML comments and prose", "<!-- <image href=\"outside.png\"/> --><title>url(outside.png)</title>" ++ rect),
    ("data PNG image", s!"<image href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\" width=\"20\" height=\"20\"/>"),
    ("data JPEG image", "<image href=\"data:image/jpeg;base64,/9j/4AAQ\" width=\"20\" height=\"20\"/>"),
    ("data image of no declared type", s!"<image href=\"data:;base64,{HtmlResource.base64 tinyPng}\"/>"),
    -- pdftocairo's spelling of a raster a boundary picture draws.
    ("data PNG image by an aliased reference",
      "<image width=\"1\" height=\"1\" xmlns:l=\"http://www.w3.org/1999/xlink\" " ++
      s!"l:href=\"data:image/png;base64,{HtmlResource.base64 tinyPng}\"/>"),
    ("data image unencoded", "<image href=\"data:image/png,raw\"/>"),
    ("data image as a source", "<image src=\"data:image/png;base64,iVBORw0KGgo=\"/>"),
    ("data image outside the base64 alphabet", "<image href=\"data:image/png;base64,iVBOR!w0KGgo=\"/>"),
    ("fragment with a figure id",
      "<defs><clipPath id=\"f0~c0\"><rect width=\"20\" height=\"20\"/></clipPath></defs>" ++
      "<g clip-path=\"url(#f0~c0)\">" ++ rect ++ "</g>"),
    ("fragment paint in a style attribute",
      "<defs><linearGradient id=\"paint\"><stop stop-color=\"red\"/></linearGradient></defs>" ++
      "<rect width=\"20\" height=\"20\" style=\"fill:url(#paint)\"/>"),
    ("numeric colour in a style sheet", "<style>rect { fill: rgb(255, 0, 0) }</style>" ++ rect),
    ("numeric colour with alpha in a style attribute",
      "<rect width=\"20\" height=\"20\" style=\"fill: rgba(255, 0, 0, 0.5)\"/>")]

/-- Whether an admitted body is a native widening of the libxml2 XPath boundary: a broader `data:`
image, a local id holding `~`, or a fetch-free CSS function. -/
def svgBoundaryWidened (name : String) : Bool :=
  ["data image of no declared type", "data image unencoded", "data image as a source",
    "data image outside the base64 alphabet",
    "fragment with a figure id", "fragment paint in a style attribute",
    "numeric colour in a style sheet", "numeric colour with alpha in a style attribute"].contains name

/-- Bodies the boundary refuses, each beside `svgRedSquare`. -/
def svgBoundaryRefused : List (String × String) :=
  [
    ("network image", "<image href=\"https://example.invalid/tile.png\"/>"),
    ("protocol-relative image", "<image href=\"//example.invalid/tile.png\"/>"),
    ("absolute image", "<image href=\"/tile.png\"/>"),
    ("empty href", "<image href=\"\"/>"),
    ("character-encoded image", "<image href=\"&#x74;&#105;le.png\"/>"),
    ("aliased image", "<image xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"tile.png\"/>"),
    ("base URI", "<g xml:base=\"https://example.invalid/\"><use href=\"#p\"/></g>"),
    ("paint-server fallback", "<defs><linearGradient id=\"paint\"/></defs><rect fill=\"url(#paint) red\"/>"),
    ("CSS escaped URL", "<style>rect { fill: u\\72l(tile.svg#p) }</style>"),
    ("CSS import", "<style>@import 'outside.css';</style>"),
    ("CSS string image", "<style>rect { fill: image-set('tile.png' 1x) }</style>"),
    ("split style text", "<style>u<!--comment--><![CDATA[rl(tile.png)]]></style>"),
    ("animated href", "<image><set attributeName=\"l:href\" to=\"tile.png\"/></image>"),
    ("animated style", "<rect><set attributeName=\"style\" to=\"fill:red\"/></rect>"),
    ("embedded SVG", "<image href=\"data:image/svg+xml,%3Csvg/%3E\"/>"),
    ("data image on a use", "<use href=\"data:image/png;base64,iVBORw0KGgo=\"/>"),
    ("embedded base64 SVG", "<image href=\"data:image/svg+xml;base64,PHN2Zy8+\"/>"),
    ("data image spelling a parenthesis", "<image href=\"data:image/png;base64,iVBOR(w0KGgo=\"/>"),
    ("foreign object", "<foreignObject><img src=\"tile.png\"/></foreignObject>"),
    ("script", "<script>fetch('tile.png')</script>"),
    ("event handler", "<rect onload=\"fetch('tile.png')\"/>")]

/-- A string's characters as an ASCII-compatible single-byte encoding writes them, `high` giving
each non-ASCII byte. -/
def singleBytes (s : String) (high : Char → UInt8) : ByteArray :=
  ⟨s.toList.toArray.map fun c => if c.toNat < 128 then c.toNat.toUInt8 else high c⟩

/-- A string as UTF-16 code units in `be` order, after a byte-order mark when `bom`. -/
def utf16Bytes (s : String) (be bom : Bool) : ByteArray := Id.run do
  let mut out : ByteArray := if !bom then .empty else if be then ⟨#[0xFE, 0xFF]⟩ else ⟨#[0xFF, 0xFE]⟩
  for c in s.toList do
    let n := c.toNat
    let units := if n < 0x10000 then [n] else [0xD800 + (n - 0x10000) / 1024, 0xDC00 + (n - 0x10000) % 1024]
    for u in units do
      let (a, b) := ((u / 256).toUInt8, (u % 256).toUInt8)
      out := if be then (out.push a).push b else (out.push b).push a
  return out

/-- A string as UTF-32 big-endian code units, after a byte-order mark when `bom`. -/
def utf32Bytes (s : String) (bom : Bool) : ByteArray := Id.run do
  let mut out : ByteArray := if bom then ⟨#[0x00, 0x00, 0xFE, 0xFF]⟩ else .empty
  for c in s.toList do
    let n := c.toNat
    out := (((out.push (n / 16777216).toUInt8).push ((n / 65536) % 256).toUInt8).push
      ((n / 256) % 256).toUInt8).push (n % 256).toUInt8
  return out

/-- An invented drawing with a line of text, declared in `encoding`. -/
def svgDeclared (encoding text : String) : String :=
  s!"<?xml version=\"1.0\" encoding=\"{encoding}\"?>" ++
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"60\" height=\"20\">" ++
    s!"<text x=\"2\" y=\"15\">{text}</text></svg>"

/-- Whole sources in the encodings an SVG is written in, with whether the reader admits each and the
text it sets. -/
def svgBoundaryEncodings : List (String × ByteArray × Option String) :=
  let curly : Char → UInt8 := fun c => if c == '“' then 0x93 else if c == '”' then 0x94 else 0x3F
  [("windows-1252", singleBytes (svgDeclared "windows-1252" "“quoted”") curly,
      some "“quoted”"),
   ("a Latin-1 label read as windows-1252", singleBytes (svgDeclared "ISO-8859-1" "café “ok”")
      (fun c => if c == 'é' then 0xE9 else curly c), some "café “ok”"),
   ("windows-1251", singleBytes (svgDeclared "windows-1251" "АБ")
      (fun c => if c == 'А' then 0xC0 else 0xC1), some "АБ"),
   ("KOI8-R", singleBytes (svgDeclared "koi8-r" "а")
      (fun _ => 0xC1), some "а"),
   ("UTF-16LE with a byte-order mark", utf16Bytes (svgDeclared "UTF-16" "naïve ✓") false true,
      some "naïve ✓"),
   ("UTF-16BE with a byte-order mark", utf16Bytes (svgDeclared "UTF-16" "naïve ✓") true true,
      some "naïve ✓"),
   ("UTF-16LE with no byte-order mark", utf16Bytes (svgDeclared "UTF-16LE" "plain") false false,
      some "plain"),
   ("UTF-8 with a byte-order mark", ⟨#[0xEF, 0xBB, 0xBF]⟩ ++ (svgDeclared "UTF-8" "été").toUTF8,
      some "été"),
   ("Shift_JIS", (svgDeclared "Shift_JIS" "plain").toUTF8, none),
   ("UTF-32", utf32Bytes (svgDeclared "UTF-32" "plain") false, none),
   ("UTF-32 with a byte-order mark", utf32Bytes (svgDeclared "UTF-32" "plain") true, none),
   ("an encoding no standard names", (svgDeclared "x-invented-8bit" "plain").toUTF8, none),
   ("a byte windows-874 does not map", singleBytes (svgDeclared "windows-874" "ÿ")
      (fun _ => 0xDB), none),
   ("a lone UTF-16 surrogate", utf16Bytes (svgDeclared "UTF-16" "a") false true ++ ⟨#[0x00, 0xD8]⟩, none)]

/-- The encoded sources the native reader refuses and libxml2 reads: the multi-byte encodings and
declared UTF-32. -/
def svgBoundaryNarrowed (name : String) : Bool := ["Shift_JIS", "UTF-32"].contains name

/-- Whole sources the reader refuses, around `drawing`. -/
def svgBoundaryMalformed (drawing : String) : List (String × String) :=
  let rect := svgRedSquare
  [
    ("empty", ""), ("whitespace", " \n\t "), ("foreign root", "<html/>"),
    ("truncated", "<svg href=\""), ("mismatched", "<svg><g></svg>"),
    ("extra root", "<svg/><svg/>"), ("unclosed", "<svg>"),
    ("unquoted attribute", "<svg width=20/>"),
    ("DTD attribute", "<!DOCTYPE svg [<!ATTLIST rect fill CDATA 'green'>]>" ++ drawing),
    ("DTD element", "<!DOCTYPE svg [<!ELEMENT svg ANY>]>" ++ drawing),
    ("entity declaration", "<!DOCTYPE svg [<!ENTITY x 'tile.png'>]>" ++
      String.fromUTF8! (svgDocument (rect ++ "<image href=\"&x;\"/>"))),
    ("parameter entity", "<!DOCTYPE svg [%outside;]>" ++ drawing),
    ("stylesheet PI", "<?xml-stylesheet href=\"outside.css\"?>" ++ drawing),
    ("undeclared prefix", "<svg xmlns=\"http://www.w3.org/2000/svg\"><use l:href=\"#p\"/></svg>"),
    ("named entity", String.fromUTF8! (svgDocument "<text>&outside;</text>")),
    ("double hyphen in a comment", String.fromUTF8! (svgDocument "<!-- a -- b -->")),
    ("control character", String.fromUTF8! (svgDocument "<text>\x01</text>")),
    ("attribute named twice", "<svg xmlns=\"http://www.w3.org/2000/svg\" a=\"1\" a=\"2\"/>")]

/-- Timelines the terminal-pose projection refuses, on a 32×16 document. -/
def svgTerminalRefused : List (String × String) :=
  let track (attr values timing : String) :=
    s!"<animate attributeName=\"{attr}\" values=\"{values}\" {timing}/>"
  let square (attrs animation : String) :=
    s!"<rect width=\"16\" height=\"16\" fill=\"red\" {attrs}>{animation}</rect>"
  let clock := "dur=\"2s\" repeatCount=\"indefinite\" "
  let linear := clock ++ "calcMode=\"linear\" keyTimes=\"0;1\""
  let three := clock ++ "calcMode=\"linear\" keyTimes=\"0;0.5;1\""
  let x := track "x" "0;16" linear
  let opacity := track "opacity" "0;1" linear
  let pathStart := "M0,0L16,0L16,16L0,16"
  let pathEnd := "M16,0L32,0L32,16L16,16"
  let path (animation : String) :=
    s!"<path fill=\"red\" d=\"{pathStart}\">{animation}</path>"
  [
    ("discrete keyTime one is not the pre-end pose",
      square "x=\"0\"" (track "x" "0;16" (clock ++ "calcMode=\"discrete\" keyTimes=\"0;1\""))),
    ("malformed middle scalar", square "x=\"0\"" (track "x" "0;nope;16" three)),
    ("malformed middle opacity", square "opacity=\"0\"" (track "opacity" "0;0.5oops;1" three)),
    ("empty middle scalar", square "x=\"0\"" (track "x" "0;;16" three)),
    ("nonfinite middle scalar", square "x=\"0\"" (track "x" "0;Infinity;16" three)),
    ("NaN middle scalar", square "x=\"0\"" (track "x" "0;NaN;16" three)),
    ("unit-bearing middle scalar", square "x=\"0\"" (track "x" "0;8px;16" three)),
    ("singleton values track", square "x=\"0\"" (track "x" "16" clock)),
    ("invalid middle M/L path number", path (track "d" (pathStart ++ ";M0,0Lbad,16;" ++ pathEnd) three)),
    ("invalid final M/L path pair", path (track "d" (pathStart ++ ";M16,0L32,") linear)),
    ("mismatched linear path length", path (track "d" (pathStart ++ ";M16,0L32,0L32,16") linear)),
    ("extra M command in path", path (track "d" (pathStart ++ ";M16,0M32,0L32,16L16,16") linear)),
    ("duplicate target attribute", square "x=\"0\"" (x ++ x)),
    ("geometry attribute on the wrong target",
      "<circle cx=\"8\" cy=\"8\" r=\"8\" fill=\"red\">" ++ x ++ "</circle>"),
    ("opacity on a nongraphical target", "<defs>" ++ opacity ++ "</defs>" ++ square "" ""),
    ("href fragment target",
      square "id=\"target\" x=\"0\"" (track "x" "0;16" (linear ++ " href=\"#target\""))),
    ("aliased xlink fragment target",
      square "id=\"target\" x=\"0\"" (track "x" "0;16"
        (linear ++ " xmlns:l=\"http://www.w3.org/1999/xlink\" l:href=\"#target\""))),
    ("sibling fragment target",
      square "id=\"target\" x=\"0\"" "" ++ track "x" "0;16" (linear ++ " href=\"#target\"")),
    ("inline CSS overrides opacity", square "style=\"opacity:0\"" opacity),
    ("stylesheet overrides opacity", "<style>rect { opacity: 0 }</style>" ++ square "" opacity),
    ("unequal durations", square "x=\"0\" opacity=\"0\"" (x ++ track "opacity" "0;1" "dur=\"3s\"")),
    ("exponent duration", square "x=\"0\"" (track "x" "0;16" "dur=\"2e0s\"")),
    ("space before duration unit", square "x=\"0\"" (track "x" "0;16" "dur=\"2 s\"")),
    ("delayed begin", square "x=\"0\"" (track "x" "0;16" (linear ++ " begin=\"1s\""))),
    ("early end", square "x=\"0\"" (track "x" "0;16" (linear ++ " end=\"1s\""))),
    ("additive track", square "x=\"0\"" (track "x" "0;16" (linear ++ " additive=\"sum\""))),
    ("accumulating track", square "x=\"0\"" (track "x" "0;16" (linear ++ " accumulate=\"sum\""))),
    ("partial repeat", square "x=\"0\"" (track "x" "0;16" "dur=\"2s\" repeatCount=\"1.5\"")),
    ("set element", square "opacity=\"0\"" "<set attributeName=\"opacity\" to=\"1\" begin=\"1s\"/>"),
    ("motion element", square "" "<animateMotion path=\"M 0 0 L 16 0\" dur=\"2s\"/>"),
    ("transform element", square ""
      "<animateTransform attributeName=\"transform\" type=\"translate\" from=\"0 0\" to=\"16 0\" dur=\"2s\"/>"),
    ("colour animation element", square "" "<animateColor attributeName=\"fill\" values=\"red;blue\" dur=\"2s\"/>")]

/-- Timelines the projection reads, each with the static pose it ends in. -/
def svgTerminalAccepted : List (String × String × String) :=
  let track (attr values timing : String) :=
    s!"<animate attributeName=\"{attr}\" values=\"{values}\" {timing}/>"
  let square (attrs animation : String) :=
    s!"<rect width=\"16\" height=\"16\" fill=\"red\" {attrs}>{animation}</rect>"
  let clock := "dur=\"2s\" repeatCount=\"indefinite\" "
  let linear := clock ++ "calcMode=\"linear\" keyTimes=\"0;1\""
  let three := clock ++ "calcMode=\"linear\" keyTimes=\"0;0.5;1\""
  let x := track "x" "0;16" linear
  let pathStart := "M0,0L16,0L16,16L0,16"
  let pathEnd := "M16,0L32,0L32,16L16,16"
  let path (animation : String) :=
    s!"<path fill=\"red\" d=\"{pathStart}\">{animation}</path>"
  let finalSquare := square "x=\"16\" opacity=\"1\"" ""
  [
    ("linear scalar and fractional opacity",
      square "x=\"0\" opacity=\"0\"" (track "x" "-8;4;16" three ++ track "opacity" "0;0.25;0.5" three),
      square "x=\"16\" opacity=\"0.5\"" ""),
    ("discrete last keyTime below one",
      square "x=\"0\"" (track "x" "0;8;16" (clock ++ "calcMode=\"discrete\" keyTimes=\"0;0.25;0.75\"")),
      finalSquare),
    ("default linear keyTimes",
      square "x=\"0\" opacity=\"0\"" (track "x" "0;8;16" clock ++ track "opacity" "0;0.5;1" clock),
      finalSquare),
    ("default discrete keyTimes",
      square "x=\"0\"" (track "x" "0;8;16" (clock ++ "calcMode=\"discrete\"")), finalSquare),
    ("absent base x attribute", square "" x, finalSquare),
    ("empty base x attribute", square "x=\"\"" x, finalSquare),
    ("matching M/L path structure", path (track "d" (pathStart ++ ";" ++ pathEnd) linear),
      s!"<path fill=\"red\" d=\"{pathEnd}\"/>"),
    ("whitespace around M/L coordinates",
      path (track "d" (pathStart ++ ";M 16 , 0 L 32 , 0 L 32 , 16 L 16 , 16") linear),
      s!"<path fill=\"red\" d=\"{pathEnd}\"/>")]

/-- The listings a document's body holds, in order: their language and their content. -/
def listings (doc : Ir.Doc) : Array (Option String × String) :=
  doc.body.filterMap fun b => match b with
    | .verbatim _ content spec => some (spec.langToken, content)
    | _ => none

/-- Whether a shipped line is set in the typewriter face alone, as a listing's lines are. -/
def monoLine (l : Layout.LineOut) : Bool :=
  let runs := lineRuns l
  !runs.isEmpty && runs.all (·.1 == 1)

/-- The invented Lean file the statement views read, and the facts its exporter wrote of it. -/
def leanFixture : String := "testdata/codedoc/lean/statements.lean"
def leanFacts : String := "testdata/codedoc/lean/statements.facts"

/-- The source line a statement stands just before: the line its declaration's command opens on,
or past the docstring that line opens. -/
def headLine (src : String) (line : Nat) : String :=
  let ls := (src.splitOn "\n").drop (line - 1)
  match ls with
  | first :: _ =>
    if first.trimAscii.toString.startsWith "/--" then
      let rest := ls.dropWhile fun l => (l.splitOn "-/").length < 2
      (rest.drop 1).headD ""
    else first
  | [] => ""

/-- A page's shipped lines: whether each is set in the typewriter face alone, and its ink. -/
def codePageLines (fonts : Font.FontSet) (doc : Ir.Doc) : Array (Bool × String) :=
  (bodyLines (layoutOf fonts doc)).map fun l => (monoLine l, lineInk l)
