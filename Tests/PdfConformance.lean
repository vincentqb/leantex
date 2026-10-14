module

public import Tests.Backends
public import Tests.GfxMatrix

public section

open LeanTex.Core LeanTex.Core.Utf8 LeanTex.Cli
open LeanTex.Core.PdfRead (Obj Entry)

/-! The PDF conformance gate: the reference walk, determinism and the reader matrix, over the
written bytes. -/

/-- What a reference is expected to name, which selects the keys the walk follows. -/
inductive Role where
  | catalog
  | pagesNode
  | font
  | fontDescriptor
  | xobject
  | outlineNode
  | annot
  | structNode
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

/-- The references a resources dictionary names, one level deep. -/
def resourceRefs (es : Array Entry) (res : Obj) : Array (Role × Nat) := Id.run do
  let mut out : Array (Role × Nat) := match res with
    | .ref n _ => #[(.leaf, n)]
    | _ => #[]
  let res := PdfCensus.deref es res
  for (key, role) in [("Font", Role.font), ("XObject", Role.xobject), ("ExtGState", Role.leaf),
      ("Pattern", Role.leaf), ("Shading", Role.leaf)] do
    match PdfCensus.deref es ((res.get? key).getD .null) with
    | .dict kvs =>
      for (_, v) in kvs do
        if let .ref n _ := v then out := out.push (role, n)
    | _ => pure ()
  return out

/-- The references one object names under its role, direct values descended eagerly. -/
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

/-- Every object id reached from the trailer, in visiting order, and every listed non-bookkeeping
object never reached. -/
structure Walk where
  visited : Array Nat
  unreached : Array Nat
  deriving Repr

/-- The reference walk from the trailer's `/Root` and `/Info`, each reference checked to land on a
listed object below `/Size`. -/
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

def walkPdf (pdf : ByteArray) : Except String Walk := do
  let es ← PdfRead.objects pdf
  let trailer ← PdfRead.trailer pdf
  refWalk trailer es.val

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

/-- The parsed reader matrix: target readers, feature columns and rows, and `[profile]` rows keyed
by profile and fixture. -/
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

/-- Every named feature must be `pass` on every reader the `target:` line names; each failure names
feature, reader and cell. -/
def featureGate (m : Matrix) (features : List String) : Array String := Id.run do
  let mut out : Array String := #[]
  for f in features do
    for r in m.target do
      match m.cell f r with
      | some .pass => pure ()
      | some v => out := out.push s!"{f} on {r}: {v.render}"
      | none => out := out.push s!"{f} on {r}: no cell"
  return out

def Matrix.profile (m : Matrix) (profile fixture : String) : Option Verdict :=
  (m.profiles.find? fun (p, f, _) => p == profile && f == fixture).map (·.2.2)

/-- The features a produced file spells for itself: the spelled oracle of the typed census. -/
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

def emittedFeaturesOf (text : ByteArray) : List Pdf.Feature :=
  featureSpellings.filterMap fun (f, spelling) =>
    if bytesContain text spelling then some f else none

mutual

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

/-- The features read off the parsed objects: the artifact-side reading the typed census is held
against. -/
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
  let pageRes : Option Obj := (es.find? fun e => PdfCensus.kindOf e.val == .page).bind
    (·.val.get? "Resources")
  let copiedGraph : Bool := es.any fun e =>
    PdfCensus.kindOf e.val == .form && e.val.get? "Resources" != pageRes &&
      objHasRef ((e.val.get? "Resources").getD .null)
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
  let transparencyGroup : Bool := es.any fun e =>
    PdfCensus.kindOf e.val == .form && pageRes.isSome && e.val.get? "Resources" == pageRes &&
      nameIs ((PdfCensus.deref es ((e.val.get? "Group").getD .null)).get? "S") "Transparency"
  let feats : List (Pdf.Feature × Bool) := [
    (.xrefStream, has .xref),
    (.objStm, has .objStm),
    (.objStmMulti, (kinds.filter (· == .objStm)).size > 1),
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
    (.structTree, anyVal fun o => nameIs (o.get? "Type") "StructTreeRoot"),
    (.transparencyGroup, transparencyGroup)]
  return feats.filterMap fun (f, b) => if b then some f else none

def parsedFeatureNames (pdf : ByteArray) : Except String (List String) :=
  (PdfRead.objects pdf).map fun es => (featuresOfEntries es.val).map Pdf.Feature.name

def writerFeatures : List String := Pdf.Feature.all.map Pdf.Feature.name

def targetReaders : Array String := #["poppler", "ghostscript", "pypdf", "pdfium", "pdfjs"]

/-- The strings a deterministic artifact never carries: dates, and metadata keys whose values are
dates or instance ids. -/
def volatileSpellings : List String :=
  ["/CreationDate", "/ModDate", "xmp:CreateDate", "xmp:ModifyDate", "xmpMM:"]

/-- Six mutants of a written file, each breaking one thing the walk reads. -/
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

/-- The reference walk, determinism and the reader matrix, held over the written bytes of every
golden fixture. -/
def pdfConformanceChecks (ref : IO.Ref (List String)) (oneFace : Font.FontSet)
    (arts : Array GoldenArt) : IO Unit := do
  let t := check ref
  let cwd ← IO.currentDir
  let matrixText ← try IO.FS.readFile "testdata/oracles/reader-matrix.txt" catch _ => pure ""
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
    let offTarget : Matrix := { m with target := #["qpdf"] }
    t "reader matrix: an off-target column is never demanded"
      (!(featureGate offTarget ["xref-stream"]).isEmpty)
    let noTarget : Matrix := { m with target := #[] }
    t "reader matrix: with no target nothing is gated" (featureGate noTarget writerFeatures).isEmpty
  let mut reached : Array String := #[]
  for a in arts do
    let n := a.name
    let doc := a.doc
    let geom := a.geom
    let store := a.store
    let out := a.out
    let pdf := a.pdf
    match a.objs.bind fun es => (PdfRead.trailer pdf).bind fun tr => refWalk tr es with
    | .error e => t s!"pdf walk {n}: {e}" false
    | .ok w =>
      t s!"pdf walk {n}: every listed object is reached: {w.unreached}" w.unreached.isEmpty
      t s!"pdf walk {n}: reaches the page count"
        (w.visited.size ≥ out.pages.size + 2)
    let typed := (Pdf.features geom oneFace out.pages store out.outline).map Pdf.Feature.name
    let parsed := (a.objs.map fun es => (featuresOfEntries es).map Pdf.Feature.name).toOption.getD []
    t s!"pdf features {n}: typed census {typed} = parsed bytes {parsed}"
      (typed.all parsed.contains && parsed.all typed.contains)
    let spelled := (emittedFeaturesOf a.text).map Pdf.Feature.name
    t s!"pdf features {n}: the spelled reading {spelled} agrees on every spelling"
      (featureSpellings.all fun (f, _) => spelled.contains f.name == typed.contains f.name)
    for f in typed do
      unless reached.contains f do reached := reached.push f
    if let .ok m := matrix? then
      t s!"pdf features {n}: no feature reached without a pass on every target"
        (featureGate m typed.toList).isEmpty
    let pdf2 := Pdf.write geom oneFace out.pages doc.info store out.outline
    t s!"pdf deterministic {n}: written twice, equal" (pdf == pdf2)
    let text := a.text
    for v in volatileSpellings do
      t s!"pdf deterministic {n}: no {v}" (!bytesContain text v)
    t s!"pdf deterministic {n}: no absolute source path"
      (!bytesContain text (cwd / goldenFile n).toString)
  if let .ok m := matrix? then
    let gaps := featureGate m reached.toList
    t s!"reader matrix gate: every golden-set feature passes every target reader: {gaps}"
      gaps.isEmpty
  t s!"pdf features: the golden set reaches marked content, soft masks, copied graphs, DCT and object streams"
    (["marked-content", "smask", "copied-graph", "dct", "objstm-multi"].all reached.contains)
  let figInks : Array Layout.InkOut := #[4, 5].filterMap fun i =>
    (Tests.GfxMatrix.cases[i]?).map fun c =>
      { fig := c.2.lift, place := { flipY := true, dx := Dim.pt 50, dy := Dim.pt 300 }, leaf := none }
  let figPages : Array Layout.PageOut := #[{ inks := figInks }]
  let figGeom : Layout.Geom := {}
  let figTyped := (Pdf.features figGeom oneFace figPages).map Pdf.Feature.name
  let figParsed := ((PdfRead.objects (Pdf.write figGeom oneFace figPages)).map fun es =>
    (featuresOfEntries es.val).map Pdf.Feature.name).toOption.getD []
  t s!"pdf features figures: the census names the figure forms: {figTyped}"
    (figTyped.contains "form-xobject" && figTyped.contains "transparency-group" &&
      !figTyped.contains "copied-graph")
  t s!"pdf features figures: typed census {figTyped} = parsed bytes {figParsed}"
    (figTyped.all figParsed.contains && figParsed.all figTyped.contains)
  let src ← IO.FS.readFile "testdata/corpus/images.tex"
  let (doc, _) ← elabFixture "images" src
  let geom := Layout.Geom.ofPage doc.page
  let store ← corpusStore doc (some oneFace)
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
