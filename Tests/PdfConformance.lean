import Tests.Backends

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj Entry)

/-! # The PDF conformance gate

Three judgements over the bytes `Pdf.write` emits, none of them a reading
of the writer's intent. The reference walk follows every edge of the
written graph — trailer `/Root` and `/Info`, catalog, page tree, contents,
fonts down to their programs, XObjects and their soft masks, a form's own
resources, metadata, outlines, annotations — through `PdfRead.objects`, so
an id the cross-reference does not list, or one at or past the trailer's
`/Size`, is refused by name. The determinism row is the one checker behind
"the artifact is a function of the document": the same inputs write the
same bytes, and no date or absolute path is among them. The matrix gate
reads `tests/oracles/reader-matrix.txt` the way a golden is read: the
file's own `target:` line names the readers a feature must `pass` on, and
`untested` or `fail:*` in a target column fails; a column off the target
line gates nothing, and what this host has installed is never asked. The
features a fixture reaches come from the writer's own typed census
(`Pdf.features`, over the inputs `write` reads — `features_mem` closes
the row set), checked here against a parsed reading of the written
objects, so a feature the writer starts emitting enters the matrix as a
row with no `pass`, and the fixture that reaches it fails by name. -/

/-- What a reference is expected to name, so the walk knows which keys to
follow from the object it reaches. -/
inductive Role where
  | catalog
  | pagesNode
  | font
  | fontDescriptor
  | xobject
  | outlineNode
  | annot
  /-- A structure tree node: the root or an element (ISO 32000-2 §14.7.2). -/
  | structNode
  /-- The parent tree's number tree (§14.7.5.4). -/
  | parentTree
  | leaf
  deriving BEq, Repr

def Role.name : Role → String
  | .catalog => "catalog"
  | .pagesNode => "page tree"
  | .font => "font"
  | .fontDescriptor => "font descriptor"
  | .xobject => "XObject"
  | .outlineNode => "outline"
  | .annot => "annotation"
  | .structNode => "structure element"
  | .parentTree => "parent tree"
  | .leaf => "stream"

/-- The references a resources dictionary names, one level: its `/Font`
and `/XObject` entries (each a direct dictionary or one hop). -/
def resourceRefs (es : Array Entry) (res : Obj) : Array (Role × Nat) := Id.run do
  let res := PdfCensus.deref es res
  let mut out : Array (Role × Nat) := #[]
  for (key, role) in [("Font", Role.font), ("XObject", Role.xobject)] do
    match PdfCensus.deref es ((res.get? key).getD .null) with
    | .dict kvs =>
      for (_, v) in kvs do
        if let .ref n _ := v then out := out.push (role, n)
    | _ => pure ()
  return out

/-- The references one object names under its role. Direct values are
descended here, eagerly, so only references enter the worklist. -/
def edgesOf (es : Array Entry) (role : Role) (o : Obj) : Array (Role × Nat) := Id.run do
  let mut out : Array (Role × Nat) := #[]
  let push (r : Role) (v : Option Obj) : Array (Role × Nat) → Array (Role × Nat) :=
    fun acc => match v with
      | some (.ref n _) => acc.push (r, n)
      | _ => acc
  let pushAll (r : Role) (v : Option Obj) : Array (Role × Nat) → Array (Role × Nat) :=
    fun acc => match v with
      | some (.ref n _) => acc.push (r, n)
      | some (.arr xs) => xs.foldl (fun acc x => push r (some x) acc) acc
      | _ => acc
  match role with
  | .catalog =>
    out := push .pagesNode (o.get? "Pages") out
    out := push .leaf (o.get? "Metadata") out
    out := push .outlineNode (o.get? "Outlines") out
    out := push .structNode (o.get? "StructTreeRoot") out
  | .pagesNode =>
    out := pushAll .pagesNode (o.get? "Kids") out
    out := push .pagesNode (o.get? "Parent") out
    out := pushAll .leaf (o.get? "Contents") out
    if let some res := o.get? "Resources" then
      out := out ++ resourceRefs es res
    match PdfCensus.deref es ((o.get? "Annots").getD .null) with
    | .arr xs => for x in xs do out := push .annot (some x) out
    | _ => pure ()
  | .font =>
    out := pushAll .font (o.get? "DescendantFonts") out
    out := push .fontDescriptor (o.get? "FontDescriptor") out
    out := push .leaf (o.get? "ToUnicode") out
  | .fontDescriptor =>
    for k in ["FontFile", "FontFile2", "FontFile3"] do
      out := push .leaf (o.get? k) out
  | .xobject =>
    out := push .xobject (o.get? "SMask") out
    if let some res := o.get? "Resources" then
      out := out ++ resourceRefs es res
  | .outlineNode =>
    for k in ["First", "Last", "Next", "Prev", "Parent"] do
      out := push .outlineNode (o.get? k) out
    if let some (.arr xs) := o.get? "Dest" then
      out := push .pagesNode xs[0]? out
  | .annot =>
    if let some (.arr xs) := o.get? "Dest" then
      out := push .pagesNode xs[0]? out
  | .structNode =>
    -- Kids: element references, or marked-content references naming a page.
    match o.get? "K" with
    | some (.arr xs) =>
      for x in xs do
        match x with
        | .ref n _ => out := out.push (.structNode, n)
        | .dict _ => out := push .pagesNode (x.get? "Pg") out
        | _ => pure ()
    | some k => out := push .structNode (some k) out
    | none => pure ()
    out := push .structNode (o.get? "P") out
    out := push .pagesNode (o.get? "Pg") out
    out := push .leaf (o.get? "NS") out
    out := push .parentTree (o.get? "ParentTree") out
    out := pushAll .leaf (o.get? "Namespaces") out
  | .parentTree =>
    match o.get? "Nums" with
    | some (.arr xs) =>
      for x in xs do
        match x with
        | .arr refs => for r in refs do out := push .structNode (some r) out
        | .ref n _ => out := out.push (.structNode, n)
        | _ => pure ()
    | _ => pure ()
    out := pushAll .parentTree (o.get? "Kids") out
  | .leaf => pure ()
  return out

/-- What the walk found: every object id reached from the trailer, in
visiting order, and every listed object it never reached that is not the
file's own bookkeeping (an object or cross-reference stream). -/
structure Walk where
  visited : Array Nat
  unreached : Array Nat
  deriving Repr

/-- The reference walk over a read file: from the trailer's `/Root` and
`/Info`, every edge `edgesOf` names, each reference checked to land on a
listed object below `/Size`. A visited set over the ids makes back-edges
(`/Parent`, `/Prev`) no-ops; the loop is bounded by the entry count, and
a worklist still holding work past it can only be naming ids the table
does not list. -/
def refWalk (trailer : Obj) (es : Array Entry) : Except String Walk := Id.run do
  let size? := ((trailer.get? "Size").bind Obj.int?).map (·.toNat)
  let mut work : Array (Role × Nat × String) := #[]
  let mut seen : Std.HashSet Nat := {}
  let mut visited : Array Nat := #[]
  let enqueue (w : Array (Role × Nat × String)) (s : Std.HashSet Nat)
      (r : Role) (n : Nat) (via : String) :
      Array (Role × Nat × String) × Std.HashSet Nat :=
    if s.contains n then (w, s) else (w.push (r, n, via), s.insert n)
  match trailer.get? "Root" with
  | some (.ref n _) =>
    let (w, s) := enqueue work seen .catalog n "trailer /Root"
    work := w
    seen := s
  | _ => return .error "reference walk: the trailer names no /Root"
  if let some (.ref n _) := trailer.get? "Info" then
    let (w, s) := enqueue work seen .leaf n "trailer /Info"
    work := w
    seen := s
  for _ in [0:es.size + 2] do
    let some (role, n, via) := work.back? | break
    work := work.pop
    if let some size := size? then
      if n ≥ size then
        return .error s!"reference walk: {via} names object {n}, at or past the trailer's /Size {size}"
    let some e := es.find? (·.num == n)
      | return .error s!"reference walk: {via} names object {n}, which the cross-reference does not list"
    -- A reached stream under the filters the reader owns decodes, or the
    -- reference resolves to bytes no reader can use; a foreign filter (an
    -- image's DCT) is data the census records, not a decode.
    if (PdfCensus.filtersOf e.val).all (· == "FlateDecode") then
      if let .error err := e.decoded then
        return .error s!"reference walk: object {n} ({via}): {err}"
    visited := visited.push n
    for (r, m) in edgesOf es role e.val do
      let (w, s) := enqueue work seen r m s!"object {n} ({role.name})"
      work := w
      seen := s
  unless work.isEmpty do
    return .error "reference walk: more references than objects"
  let unreached := es.filterMap fun e =>
    if seen.contains e.num then none
    else match PdfCensus.kindOf e.val with
      | .objStm => none
      | .xref => none
      | _ => some e.num
  return .ok { visited, unreached }

/-- The walk over a file's bytes: `PdfRead.objects` first (every object
under its spelled number, `objects_num_covers`), then the graph. -/
def walkPdf (pdf : ByteArray) : Except String Walk := do
  let es ← PdfRead.objects pdf
  let trailer ← PdfRead.trailer pdf
  refWalk trailer es.val

-- ## The reader matrix

/-- One matrix cell: `pass`, `fail:<reason>`, or `untested`. -/
inductive Verdict where
  | pass
  | fail (reason : String)
  | untested
  deriving BEq, Repr

def Verdict.parse (s : String) : Option Verdict :=
  if s == "pass" then some .pass
  else if s == "untested" then some .untested
  else if s.startsWith "fail:" then some (.fail ((s.drop 5).toString))
  else none

def Verdict.render : Verdict → String
  | .pass => "pass"
  | .untested => "untested"
  | .fail r => s!"fail:{r}"

/-- `tests/oracles/reader-matrix.txt`, parsed: the target readers, the
reader columns of the `[feature]` section, its rows, and the `[profile]`
rows keyed by (profile, fixture). `tools:` and `date:` are not read. -/
structure Matrix where
  target : Array String
  readers : Array String
  features : Array (String × Array Verdict)
  profiles : Array (String × String × Verdict)
  deriving Repr

def Matrix.cell (m : Matrix) (feature reader : String) : Option Verdict := do
  let k ← m.readers.findIdx? (· == reader)
  let (_, cells) ← m.features.find? (·.1 == feature)
  cells[k]?

private def fields (l : String) : Array String :=
  ((l.splitOn " ").filter (!·.isEmpty)).toArray

def readMatrix (text : String) : Except String Matrix := do
  let mut target : Array String := #[]
  let mut readers : Array String := #[]
  let mut features : Array (String × Array Verdict) := #[]
  let mut profiles : Array (String × String × Verdict) := #[]
  let mut part := ""
  for raw in text.splitOn "\n" do
    let l := raw.trimAscii.toString
    if l.isEmpty then continue
    if l.startsWith "# feature" then
      readers := (fields l).extract 2 (fields l).size
      continue
    if l.startsWith "#" then continue
    if l.startsWith "target:" then
      target := (fields l).extract 1 (fields l).size
      continue
    if l.startsWith "tools:" || l.startsWith "date:" then continue
    if l == "[feature]" || l == "[profile]" then
      part := l
      continue
    let fs := fields l
    if part == "[feature]" then
      let some name := fs[0]? | throw s!"reader matrix: empty feature row"
      let cells := (fs.extract 1 fs.size).map Verdict.parse
      if cells.size != readers.size then
        throw s!"reader matrix: feature {name} has {cells.size} cells for {readers.size} readers"
      let mut vs : Array Verdict := #[]
      for c in cells do
        match c with
        | some v => vs := vs.push v
        | none => throw s!"reader matrix: feature {name} carries an unreadable cell"
      features := features.push (name, vs)
    else if part == "[profile]" then
      match fs[0]?, fs[1]?, fs[2]?.bind Verdict.parse with
      | some p, some f, some v => profiles := profiles.push (p, f, v)
      | _, _, _ => throw s!"reader matrix: unreadable profile row '{l}'"
    else
      throw s!"reader matrix: a row outside any section: '{l}'"
  if target.isEmpty then throw "reader matrix: no target: line"
  if readers.isEmpty then throw "reader matrix: no reader columns"
  return { target, readers, features, profiles }

/-- The matrix gate: every feature named must be `pass` on every reader
the file's `target:` line names. Each failure names the feature, the
reader, and the cell; a reader off the target line is never consulted. -/
def featureGate (m : Matrix) (features : List String) : Array String := Id.run do
  let mut out : Array String := #[]
  for f in features do
    for r in m.target do
      match m.cell f r with
      | some .pass => pure ()
      | some v => out := out.push s!"{f} on {r}: {v.render}"
      | none => out := out.push s!"{f} on {r}: no cell"
  return out

/-- The `[profile]` cell for a profile on a fixture. -/
def Matrix.profile (m : Matrix) (profile fixture : String) : Option Verdict :=
  (m.profiles.find? fun (p, f, _) => p == profile && f == fixture).map (·.2.2)

/-- The features a produced file spells for itself (raw bytes with every
flate stream inflated beside them, `pdfText`): the spelled oracle of the
typed census. `copiedGraph` has no spelling of its own — its objects are
another producer's — and the four the writer never emits (`tabs`,
`transparencyGroup`, `brotli`, `jpx`) have none yet; `emittedFeatures`
covers what is listed here, and the parsed reading below the rest. -/
def featureSpellings : List (Pdf.Feature × String) := [
  (.xrefStream, "/Type /XRef"),
  (.objStm, "/Type /ObjStm"),
  (.flatePredictor15, "/Predictor 15"),
  (.dct, "/DCTDecode"),
  (.smask, "/SMask"),
  (.formXObject, "/Subtype /Form"),
  (.cidFontType0, "/CIDFontType0"),
  (.cidFontType2, "/CIDFontType2"),
  (.linkURI, "/S /URI"),
  (.outlines, "/Type /Outlines"),
  (.xmp, "/Type /Metadata"),
  (.trimBox, "/TrimBox"),
  (.markedContent, "\nEMC"),
  (.structTree, "/Type /StructTreeRoot")]

/-- The features a produced PDF reaches, by spelling. -/
def emittedFeatures (pdf : ByteArray) : List Pdf.Feature :=
  let text := pdfText pdf
  featureSpellings.filterMap fun (f, spelling) =>
    if bytesContain text spelling then some f else none

mutual

/-- Does a value name any indirect object? A copied resource graph is
non-empty exactly when the form's `/Resources` does. -/
def objHasRef : Obj → Bool
  | .ref _ _ => true
  | .arr xs => objsHaveRef xs.toList
  | .dict es => kvsHaveRef es.toList
  | .null => false
  | .bool _ => false
  | .int _ => false
  | .real _ => false
  | .str _ => false
  | .name _ => false

def objsHaveRef : List Obj → Bool
  | [] => false
  | o :: rest => objHasRef o || objsHaveRef rest

def kvsHaveRef : List (String × Obj) → Bool
  | [] => false
  | (_, o) :: rest => objHasRef o || kvsHaveRef rest

end

/-- The features read off the parsed objects (`PdfRead.objects`): the
artifact-side reading of every feature the writer can emit today, what
the suite holds the typed census (`Pdf.features`, computed from `write`'s
inputs) against on every fixture. -/
def featuresOfEntries (es : Array Entry) : List Pdf.Feature := Id.run do
  let kinds := es.map fun e => PdfCensus.kindOf e.val
  let has (k : PdfCensus.Kind) : Bool := kinds.contains k
  let anyVal (p : Obj → Bool) : Bool := es.any fun e => p e.val
  let nameIs (o : Option Obj) (s : String) : Bool :=
    match o with
    | some (.name n) => n == s
    | _ => false
  let pred15 (d : Obj) : Bool :=
    match d.get? "Predictor" with
    | some (.int 15) => true
    | _ => false
  let predictor15 (o : Obj) : Bool :=
    match PdfCensus.deref es ((o.get? "DecodeParms").getD .null) with
    | d@(.dict _) => pred15 d
    | .arr xs => xs.any pred15
    | _ => false
  let subtype (o : Obj) (s : String) : Bool := nameIs (o.get? "Subtype") s
  let uriAction (o : Obj) : Bool :=
    nameIs ((PdfCensus.deref es ((o.get? "A").getD .null)).get? "S") "URI"
  let annotsUri (o : Obj) : Bool :=
    match PdfCensus.deref es ((o.get? "Annots").getD .null) with
    | .arr xs => xs.any fun a => uriAction (PdfCensus.deref es a)
    | _ => false
  let copiedGraph : Bool := es.any fun e =>
    PdfCensus.kindOf e.val == .form && objHasRef ((e.val.get? "Resources").getD .null)
  -- A page's content, decoded, opens a marked sequence.
  let markedContent : Bool := es.any fun e =>
    PdfCensus.kindOf e.val == .page &&
      (match e.val.get? "Contents" with
        | some (.ref n _) =>
          match es.find? (·.num == n) with
          | some c => match c.decoded with
            | .ok (some data) => bytesContain data "\nEMC"
            | _ => false
          | none => false
        | _ => false)
  let feats : List (Pdf.Feature × Bool) := [
    (.xrefStream, has .xref),
    (.objStm, has .objStm),
    (.flatePredictor15, anyVal predictor15),
    (.dct, es.any fun e => (PdfCensus.filtersOf e.val).contains "DCTDecode"),
    (.smask, anyVal fun o => (o.get? "SMask").isSome),
    (.formXObject, has .form),
    (.copiedGraph, copiedGraph),
    (.cidFontType0, anyVal (subtype · "CIDFontType0")),
    (.cidFontType2, anyVal (subtype · "CIDFontType2")),
    (.linkURI, anyVal fun o => annotsUri o || uriAction o),
    (.outlines, has .outlines),
    (.xmp, has .metadata),
    (.trimBox, anyVal fun o => (o.get? "TrimBox").isSome),
    (.markedContent, markedContent),
    (.structTree, anyVal fun o => nameIs (o.get? "Type") "StructTreeRoot")]
  return feats.filterMap fun (f, b) => if b then some f else none

/-- The parsed reading of a file's bytes, as matrix row names. -/
def parsedFeatureNames (pdf : ByteArray) : Except String (List String) :=
  (PdfRead.objects pdf).map fun es => (featuresOfEntries es.val).map Pdf.Feature.name

/-- Every feature the census can name, as matrix rows: each has a row, and
a mutated row is what breaks the gate once. -/
def writerFeatures : List String := Pdf.Feature.all.map Pdf.Feature.name

/-- The five readers the matrix's `target:` line must name: the three host
readers of the first slice and the two browser engines. -/
def targetReaders : Array String := #["poppler", "ghostscript", "pypdf", "pdfium", "pdfjs"]

/-- The strings a deterministic artifact never carries: dates, and the
metadata keys whose values are dates or instance ids. -/
def volatileSpellings : List String :=
  ["/CreationDate", "/ModDate", "xmp:CreateDate", "xmp:ModifyDate", "xmpMM:"]

/-- Six mutants of a written file, each breaking one thing the walk
reads: truncated at 60 %, `startxref` off by one, one cross-reference row
byte flipped, a stream's `/Length` one short, one byte of a content
stream's deflate corrupted, and an object stream whose header pairs are
swapped (the hand-built `objStmPdf`, the file on which the swap moves no
offset). -/
def walkMutants (pdf : ByteArray) : Option (Array (String × ByteArray)) := do
  let sx ← findBytes pdf "startxref\n"
  let x ← (PdfRead.readXref pdf).toOption
  let es ← (PdfRead.objects pdf).toOption
  let xrefData ← (findBytes pdf "stream\n" x.start).map (· + 7)
  let lenE ← es.val.find? fun e =>
    e.stream.isSome && (match e.val.get? "Length" with
      | some (.int n) => n ≥ 11 && n % 10 != 0
      | _ => false)
  let len ← match lenE.val.get? "Length" with
    | some (.int n) => some n
    | _ => none
  let lenAt ← findBytes pdf s!"/Length {len} >>"
  let cE ← es.val.reverse.find? fun e =>
    e.stream.isSome && (e.val.get? "Type").isNone && (e.val.get? "Subtype").isNone &&
      (e.val.get? "Length1").isNone &&
      PdfCensus.filtersOf e.val == #["FlateDecode"] &&
      (match e.loc with | .direct _ => true | _ => false)
  let cOff := match cE.loc with | .direct o => o | _ => 0
  let cData ← (findBytes pdf "stream\n" cOff).map (· + 7)
  return #[
    ("truncated at 60 %", pdf.extract 0 (pdf.size * 3 / 5)),
    ("startxref off by one", spliceBytes pdf (sx + 10) (toString x.start) (toString (x.start + 1))),
    ("xref row byte flipped", flipByte pdf (xrefData + 10)),
    ("/Length one short", spliceBytes pdf lenAt s!"/Length {len} >>" s!"/Length {len - 1} >>"),
    ("content deflate byte corrupted", flipByte pdf (cData + 5)),
    ("object stream ids swapped", objStmPdf true)]

/-- The three judgements over the written bytes: the reference walk over
every golden fixture and the six mutants it refuses by name; the artifact
as a function of the document (twice-written equality, no dates, no
absolute path); the reader matrix read as data, the gate broken once on a
mutated copy, and the per-fixture feature table complete over the golden
set and consistent with the file's spellings. -/
def pdfConformanceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet) : IO Unit := do
  let t := check ref
  let cwd ← IO.currentDir
  -- The matrix, read once; its gate over every writer feature.
  let matrixText ← try IO.FS.readFile "tests/oracles/reader-matrix.txt" catch _ => pure ""
  t "reader matrix present (run: lake env lean --run scripts/pdf-oracles.lean)"
    (!matrixText.isEmpty)
  let matrix? := readMatrix matrixText
  t s!"reader matrix parses: {match matrix? with | .ok _ => "ok" | .error e => e}" matrix?.isOk
  if let .ok m := matrix? then
    t "reader matrix: target names the three host readers and both browser engines"
      (m.target == targetReaders)
    t "reader matrix: verapdf is not a target (no profile claim exists)"
      (!m.target.contains "verapdf")
    t "reader matrix: every target is a column" (m.target.all m.readers.contains)
    t "reader matrix: every feature the census can name has a row"
      (writerFeatures.all fun f => m.features.any (·.1 == f))
    t "reader matrix: every row names a feature the census can name"
      (m.features.all fun (f, _) => (Pdf.Feature.ofName? f).isSome)
    t "reader matrix: the browser and validator columns are recorded"
      (["verapdf", "pdfium", "pdfjs", "qpdf", "arlington"].all m.readers.contains)
    t "reader matrix: profile rows carry measured failures, never a claim"
      (!m.profiles.isEmpty && m.profiles.all fun (_, _, v) => v != .pass)
    t "reader matrix: pdf/a-4 and pdf/ua-2 rows exist for the four reference fixtures"
      (["deck", "resume", "trio-card", "images"].all fun f =>
        (m.profile "pdf/a-4" f).isSome && (m.profile "pdf/ua-2" f).isSome)
    -- The gate breaks once: one target cell set to `untested` in memory.
    let mutated := (matrixText.splitOn "\n").map fun l =>
      if l.startsWith "xref-stream " then
        String.intercalate " " ((fields l).toList.map fun w => if w == "pass" then "untested" else w)
      else l
    match readMatrix (String.intercalate "\n" mutated) with
    | .ok m' =>
      let gaps := featureGate m' ["xref-stream"]
      t s!"reader matrix gate breaks on untested in a target column: {gaps}"
        (gaps.size == m.target.size && gaps.all fun g => hasStr g "xref-stream" && hasStr g "untested")
    | .error e => t s!"mutated matrix parses: {e}" false
    -- A column off the target line gates nothing, whatever it says.
    let offTarget : Matrix := { m with target := #["qpdf"] }
    t "reader matrix: an off-target column is never demanded"
      (!(featureGate offTarget ["xref-stream"]).isEmpty)
    let noTarget : Matrix := { m with target := #[] }
    t "reader matrix: with no target nothing is gated" (featureGate noTarget writerFeatures).isEmpty
  -- Every fixture: the walk, the typed census against the bytes, the
  -- gate over what it reaches, determinism.
  let mut reached : Array String := #[]
  for n in goldenNames do
    let src ← IO.FS.readFile s!"tests/corpus/{n}.tex"
    let (doc, _) ← elabFixture n src
    let geom := Layout.Geom.ofPage doc.page
    let store ← corpusStore doc
    let out := layoutOf oneFace doc geom none store
    let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline
    match walkPdf pdf with
    | .error e => t s!"pdf walk {n}: {e}" false
    | .ok w =>
      t s!"pdf walk {n}: every listed object is reached: {w.unreached}" w.unreached.isEmpty
      t s!"pdf walk {n}: reaches the page count"
        (w.visited.size ≥ out.pages.size + 2)
    -- The typed census (the writer's inputs) and the parsed reading (the
    -- written objects) name the same features; the spelled reading agrees
    -- on every feature it can spell.
    let typed := (Pdf.features geom oneFace out.pages store out.outline).map Pdf.Feature.name
    let parsed := (parsedFeatureNames pdf).toOption.getD []
    t s!"pdf features {n}: typed census {typed} = parsed bytes {parsed}"
      (typed.all parsed.contains && parsed.all typed.contains)
    let spelled := (emittedFeatures pdf).map Pdf.Feature.name
    t s!"pdf features {n}: the spelled reading {spelled} agrees on every spelling"
      (featureSpellings.all fun (f, _) => spelled.contains f.name == typed.contains f.name)
    for f in typed do
      unless reached.contains f do reached := reached.push f
    if let .ok m := matrix? then
      t s!"pdf features {n}: no feature reached without a pass on every target"
        (featureGate m typed.toList).isEmpty
    let pdf2 := Pdf.write geom oneFace out.pages doc.info store out.outline
    t s!"pdf deterministic {n}: written twice, equal" (pdf == pdf2)
    let text := pdfText pdf
    for v in volatileSpellings do
      t s!"pdf deterministic {n}: no {v}" (!bytesContain text v)
    t s!"pdf deterministic {n}: no absolute source path"
      (!bytesContain text (cwd / "tests/corpus" / s!"{n}.tex").toString)
  -- The gate over every feature the golden set reaches, as one statement.
  if let .ok m := matrix? then
    let gaps := featureGate m reached.toList
    t s!"reader matrix gate: every feature the golden set reaches passes every target reader: {gaps}"
      gaps.isEmpty
  t s!"pdf features: the golden set reaches marked content, a soft mask, a copied graph, a DCT image"
    (["marked-content", "smask", "copied-graph", "dct"].all reached.contains)
  -- The mutants, through the walk: one corpus document with images.
  let src ← IO.FS.readFile "tests/corpus/images.tex"
  let (doc, _) ← elabFixture "images" src
  let geom := Layout.Geom.ofPage doc.page
  let store ← corpusStore doc
  let out := layoutOf oneFace doc geom none store
  let pdf := Pdf.write geom oneFace out.pages doc.info store out.outline
  match walkMutants pdf with
  | none => t "walk mutants built" false
  | some ms =>
    t "six walk mutants built" (ms.size == 6)
    let mut msgs : Array String := #[]
    for (name, m) in ms do
      match walkPdf m with
      | .ok w => t s!"walk mutant {name} refused (accepted, visited {w.visited.size})" false
      | .error e =>
        t s!"walk mutant {name} refused" true
        msgs := msgs.push e
    t s!"the six walk refusals are six messages: {msgs}"
      ((msgs.qsort (· < ·)).toList.eraseDups.length == 6)
    t "walk: the swapped object stream is refused naming the stream"
      (match walkPdf (objStmPdf true) with
       | .error e => hasStr e "object stream 4"
       | .ok _ => false)
    t "walk: the unswapped object stream reaches its three objects"
      (match walkPdf (objStmPdf false) with
       | .ok w => w.visited.size == 4 && w.unreached.isEmpty
       | .error _ => false)
  -- The walk itself breaks once: a dangling reference, and one past /Size.
  let dangling : Array Entry := #[
    { num := 1, loc := .direct 0, header := 1, val := .dict #[("Type", .name "Catalog"),
        ("Pages", .ref 2 0)], stream := none }]
  t "walk: a dangling /Pages reference is refused naming it"
    (match refWalk (.dict #[("Root", .ref 1 0), ("Size", .int 3)]) dangling with
     | .error e => hasStr e "object 2" && hasStr e "does not list"
     | .ok _ => false)
  t "walk: a reference at /Size is refused by the size"
    (match refWalk (.dict #[("Root", .ref 1 0), ("Size", .int 2)]) dangling with
     | .error e => hasStr e "object 2" && hasStr e "/Size 2"
     | .ok _ => false)
  t "walk: a trailer without /Root is refused"
    (match refWalk (.dict #[("Size", .int 2)]) dangling with
     | .error e => hasStr e "/Root"
     | .ok _ => false)
