module

public import LeanTex.Core.PdfCensus
public import LeanTex.Core.Icc
public import LeanTex.Core.Diag
import LeanTex.Core.PdfContentLex
import LeanTex.Core.PdfDate

namespace LeanTex.Core.PdfX

open LeanTex.Core.PdfRead LeanTex.Core.PdfCensus

/-! What PDF/X-4 (ISO 15930-7:2010) demands of a file, judged over the file's own bytes. -/

/-- A rectangle in default user space, its corners ordered. -/
public structure Rect where
  x0 : Rat
  y0 : Rat
  x1 : Rat
  y1 : Rat
  deriving Repr, BEq, Inhabited

/-- A page's boxes as written. -/
public structure Boxes where
  media : Option Rect := none
  crop : Option Rect := none
  bleed : Option Rect := none
  trim : Option Rect := none
  art : Option Rect := none
  deriving Repr, BEq, Inhabited

/-- One output intent: its subtype, its condition fields, and its destination profile's header
beside the channel count the stream declares. -/
public structure Intent where
  subtype : Option String := none
  condition : Option String := none
  info : Option String := none
  profile : Option Icc.Header := none
  declaredN : Option Nat := none
  embedded : Bool := false
  deriving Repr, BEq, Inhabited

/-- The facts the rules read. -/
public structure Facts where
  version : String := ""
  encrypted : Bool := false
  intents : Array Intent := #[]
  xmpVersion : Option String := none
  xmpTrapped : Option String := none
  xmpCreated : Option String := none
  xmpModified : Option String := none
  xmpTitle : Bool := false
  xmpDocumentId : Option String := none
  xmpVersionId : Option String := none
  xmpRendition : Option String := none
  infoTrapped : Option String := none
  infoCreated : Option String := none
  infoModified : Option String := none
  pages : Array Boxes := #[]
  /-- Each printable annotation's page, subtype and rectangle. -/
  annots : Array (Nat × String × Rect) := #[]
  /-- The device colour families content or resources paint in. -/
  devices : Array String := #[]
  /-- Each device family beside where the file paints in it. -/
  devicePlaces : Array (String × String) := #[]
  fontsEmbedded : Bool := true
  /-- The fonts whose programs the file does not carry, by name. -/
  unembedded : Array String := #[]
  /-- The versions of the ICC profiles colour spaces carry, `none` for one the reader cannot read. -/
  iccSpaces : Array (Option (Nat × Nat)) := #[]
  /-- The constructs the standard does not admit, by what they are. -/
  forbidden : Array String := #[]
  deriving Repr, Inhabited

/-- One rule a file breaks: the requirement, and what the file carries instead. -/
public structure Breach where
  rule : String
  actual : String
  deriving Repr, BEq, Inhabited

private def nameOf (o : Option Obj) : Option String :=
  match o with
  | some (.name n) => some n
  | _ => none

/-- A text string's characters: UTF-16BE behind its byte-order mark, else one character per byte. -/
public def textOf (o : Obj) : Option String := do
  let b ← PdfContentLex.strBytes? o
  if b.size ≥ 2 && b[0]? == some 0xFE && b[1]? == some 0xFF then
    let units := (List.range ((b.size - 2) / 2)).map fun k =>
      ((b[2 + 2 * k]?.map UInt8.toNat).getD 0) * 256 + ((b[3 + 2 * k]?.map UInt8.toNat).getD 0)
    return String.ofList (units.map Char.ofNat)
  else return String.ofList (b.toList.map fun v => Char.ofNat v.toNat)

private def rectOf (t : Index) (o : Option Obj) : Option Rect := do
  let .arr xs := t.deref (← o) | none
  match xs.toList.map PdfContentLex.numRat? with
  | [some a, some b, some c, some d] => some ⟨if a ≤ c then a else c, if b ≤ d then b else d, if a ≤ c then c else a, if b ≤ d then d else b⟩
  | _ => none

/-- An attribute a page inherits through its page tree (ISO 32000-2 §7.7.3.4). -/
private def inherited (t : Index) (page : Obj) (k : String) : Option Obj := Id.run do
  let mut o := page
  for _ in [0:t.entries.size + 1] do
    match o.get? k with
    | some v => return some v
    | none => match o.get? "Parent" with
      | some p => o := t.deref p
      | none => return none
  return none

/-- The device family a colour space name spells. -/
private def familyOfName : String → Array String
  | "DeviceRGB" | "RGB" => #["DeviceRGB"]
  | "DeviceCMYK" | "CMYK" => #["DeviceCMYK"]
  | "DeviceGray" | "G" => #["DeviceGray"]
  | _ => #[]

/-- How deep the judge reads a colour space built on others; one deeper is unread, so no claim. -/
private def spaceDepth : Nat := 8

/-- The device families a colour space spells at most `depth` spaces down: a separation's or a
DeviceN's alternate, a DeviceN's colorants and process space, and an indexed or pattern space's
base; `Unread` past the depth. -/
private def familiesAt (t : Index) : Nat → Obj → Array String
  | 0, _ => #["Unread"]
  | d + 1, o =>
    match t.deref o with
    | .name n => familyOfName n
    | .arr xs =>
      match (xs[0]? : Option Obj) with
      | some (.name "Separation") => (xs[2]?.map (familiesAt t d)).getD #[]
      | some (.name "DeviceN") =>
        let attrs := match xs[4]?.map t.deref with
          | some a@(.dict _) =>
            let colorants := match (a.get? "Colorants").map t.deref with
              | some (.dict cs) => cs.foldl (fun acc (_, v) => acc ++ familiesAt t d v) #[]
              | _ => #[]
            let process := match (a.get? "Process").map t.deref with
              | some p@(.dict _) => ((p.get? "ColorSpace").map (familiesAt t d)).getD #[]
              | _ => #[]
            colorants ++ process
          | _ => #[]
        (xs[2]?.map (familiesAt t d)).getD #[] ++ attrs
      | some (.name "Indexed") | some (.name "I") | some (.name "Pattern") =>
        (xs[1]?.map (familiesAt t d)).getD #[]
      | _ => #[]
    | _ => #[]

/-- The device families a colour space spells, the spaces it is built on included. -/
private def families (t : Index) (o : Obj) : Array String := familiesAt t spaceDepth o

/-- A content stream's device colour operators, resolving named spaces in `spaces`. -/
private def streamFamilies (t : Index) (spaces : Obj) (data : ByteArray) : Array String :=
  let toks := PdfContentLex.scan data
  (List.range toks.size).foldl (init := #[]) fun acc i =>
    match (toks[i]? : Option PdfContentLex.Tok) with
    | some (.op "rg") | some (.op "RG") => acc.push "DeviceRGB"
    | some (.op "k") | some (.op "K") => acc.push "DeviceCMYK"
    | some (.op "g") | some (.op "G") => acc.push "DeviceGray"
    | some (.op "cs") | some (.op "CS") =>
      match (if i == 0 then none else toks[i - 1]? : Option PdfContentLex.Tok) with
      | some (.val (.name n)) =>
        let named := match t.deref spaces with
          | d@(.dict _) => (d.get? n).getD (.name n)
          | _ => .name n
        let found := families t named
        acc ++ found
      | _ => acc
    | some (.inline d _) =>
      acc ++ ((PdfContentLex.inlineGet d "ColorSpace" "CS").map (families t)).getD #[]
    | _ => acc

private def decodedOf (t : Index) (o : Obj) : Option ByteArray :=
  match o with
  | .ref n _ => (t.find? n).bind fun e => match e.decoded with
    | .ok d => d
    | .error _ => none
  | _ => none

private def spacesOf (t : Index) (owner : Obj) : Obj :=
  match t.deref ((owner.get? "Resources").getD .null) with
  | r@(.dict _) => (r.get? "ColorSpace").getD .null
  | _ => .null

mutual

/-- The values a dictionary holds under `/ColorSpace` or `/CS` at any depth, references unfollowed. -/
private def spaceValues (acc : Array (String × Obj)) : Obj → Array (String × Obj)
  | .dict es => spaceEntries acc es.toList
  | .arr xs => spaceList acc xs.toList
  | .null | .bool _ | .int _ | .real _ | .str _ | .name _ | .ref _ _ => acc

private def spaceEntries (acc : Array (String × Obj)) : List (String × Obj) → Array (String × Obj)
  | [] => acc
  | (k, v) :: rest =>
    let acc := if k == "ColorSpace" || k == "CS" then acc.push (k, v) else acc
    spaceEntries (spaceValues acc v) rest

private def spaceList (acc : Array (String × Obj)) : List Obj → Array (String × Obj)
  | [] => acc
  | o :: rest => spaceList (spaceValues acc o) rest

end

mutual

/-- Each value `visit` finds under a key at any depth, references unfollowed. -/
private def keyFinds (visit : String → Obj → Option String) (acc : Array String) :
    Obj → Array String
  | .dict es => keyEntries visit acc es.toList
  | .arr xs => keyList visit acc xs.toList
  | .null | .bool _ | .int _ | .real _ | .str _ | .name _ | .ref _ _ => acc

private def keyEntries (visit : String → Obj → Option String) (acc : Array String) :
    List (String × Obj) → Array String
  | [] => acc
  | (k, v) :: rest =>
    let acc := match visit k v with
      | some w => acc.push w
      | none => acc
    keyEntries visit (keyFinds visit acc v) rest

private def keyList (visit : String → Obj → Option String) (acc : Array String) :
    List Obj → Array String
  | [] => acc
  | o :: rest => keyList visit (keyFinds visit acc o) rest

end


/-- Every content stream the file paints with, beside the colour spaces its names resolve in and
where it stands: page and form contents, tiling pattern cells and Type 3 glyph procedures. -/
private def contentStreams (t : Index) : Array (String × Obj × ByteArray) := Id.run do
  let mut out : Array (String × Obj × ByteArray) := #[]
  let mut page := 0
  for e in t.entries do
    let o := e.val
    match kindOf o with
    | .page =>
      page := page + 1
      let spaces := (inherited t o "Resources").map (fun r => match t.deref r with
        | d@(.dict _) => (d.get? "ColorSpace").getD .null
        | _ => .null) |>.getD .null
      let contents := match o.get? "Contents" with
        | some (.arr xs) => xs
        | some r => #[r]
        | none => #[]
      for c in contents do
        if let some d := decodedOf t c then out := out.push (s!"page {page}'s content", spaces, d)
    | .form =>
      if let .ok (some d) := e.decoded then out := out.push ("a form", spacesOf t o, d)
    | _ =>
      if (o.get? "PatternType").bind Obj.int? == some 1 then
        if let .ok (some d) := e.decoded then out := out.push ("a pattern", spacesOf t o, d)
  for f in fontDicts t do
    if nameOf (f.get? "Subtype") == some "Type3" then
      if let .dict procs := t.deref ((f.get? "CharProcs").getD .null) then
        for (_, p) in procs do
          if let some d := decodedOf t p then out := out.push ("a Type 3 glyph", spacesOf t f, d)
  return out

mutual

/-- The profile of each `[/ICCBased …]` array at any depth, references unfollowed. -/
private def iccRefs (acc : Array Obj) : Obj → Array Obj
  | .dict es => iccEntries acc es.toList
  | .arr xs =>
    let acc := match xs[0]?, xs[1]? with
      | some (.name "ICCBased"), some x => acc.push x
      | _, _ => acc
    iccList acc xs.toList
  | .null | .bool _ | .int _ | .real _ | .str _ | .name _ | .ref _ _ => acc

private def iccEntries (acc : Array Obj) : List (String × Obj) → Array Obj
  | [] => acc
  | (_, v) :: rest => iccEntries (iccRefs acc v) rest

private def iccList (acc : Array Obj) : List Obj → Array Obj
  | [] => acc
  | o :: rest => iccList (iccRefs acc o) rest

end

/-- The ICC version each ICCBased colour space's profile carries, `none` where it is unreadable. -/
private def iccSpacesOf (t : Index) : Array (Option (Nat × Nat)) :=
  (t.entries.foldl (fun acc e => iccRefs acc e.val) #[]).map fun x =>
    ((decodedOf t x).bind Icc.header?).map (·.version)

/-- The action types (ISO 32000-2 Table 201), which an action dictionary names under `/S`. -/
private def actionTypes : List String :=
  ["GoTo", "GoToR", "GoToE", "GoToDp", "Launch", "Thread", "URI", "Sound", "Movie", "Hide",
   "Named", "SubmitForm", "ResetForm", "ImportData", "JavaScript", "SetOCGState", "Rendition",
   "Trans", "GoTo3DView", "RichMediaExecute"]

/-- What a key and its value hold that PDF/X does not admit (ISO 15930-7 §6): a transfer function,
a halftone named for a device, an OPI link, an image's alternates, PostScript, a reference to
another file's page, an action or JavaScript. -/
private def forbiddenAt (k : String) (v : Obj) : Option String :=
  match k, v with
  | "TR", .name "Identity" | "TR", .name "Default" | "TR2", .name "Identity"
  | "TR2", .name "Default" | "TransferFunction", .name "Identity" => none
  | "TR", _ | "TR2", _ | "TransferFunction", _ => some "a transfer function"
  | "HalftoneName", _ => some "a named halftone"
  | "OPI", _ => some "an OPI link"
  | "Alternates", _ => some "an image's alternates"
  | "Subtype", .name "PS" | "Subtype2", .name "PS" | "PS", _ => some "a PostScript XObject"
  | "Ref", .dict _ | "Ref", .ref _ _ => some "a reference to another file's page"
  | "S", .name t => if actionTypes.contains t then some "an action" else none
  | "JS", _ | "JavaScript", _ => some "JavaScript"
  | _, _ => none

/-- Every device colour family the file paints in, beside where: content streams wherever they
stand, images, shadings, transparency groups and the spaces resources declare. -/
private def devicesOf (t : Index) : Array (String × String) := Id.run do
  let mut out : Array (String × String) := #[]
  for (place, spaces, d) in contentStreams t do
    for f in streamFamilies t spaces d do out := out.push (f, place)
  for e in t.entries do
    let o := e.val
    let place := match kindOf o with
      | .image => "an image"
      | .form => "a form's resources"
      | _ => "a colour space the file declares"
    for (k, cs) in spaceValues #[] o do
      match t.deref cs with
      | .dict entries =>
        -- A resources `/ColorSpace` maps names to spaces.
        if k == "ColorSpace" then
          for (_, v) in entries do
            for f in families t v do out := out.push (f, place)
      | v => for f in families t v do out := out.push (f, place)
  return (out.foldl (fun (acc, seen) f =>
    if seen.contains f then (acc, seen) else (acc.push f, seen.insert f))
    ((#[], {}) : Array (String × String) × Std.HashSet (String × String))).1

/-- What the file holds that PDF/X does not admit, each named once: its keys at any depth, and the
`PS` operator in any content stream. -/
private def forbiddenOf (t : Index) : Array String :=
  let keys := t.entries.foldl (fun acc e => keyFinds forbiddenAt acc e.val) #[]
  let ps := (contentStreams t).any fun (_, _, d) =>
    (PdfContentLex.scan d).any (· matches .op "PS")
  let all := if ps then keys.push "the PostScript operator" else keys
  all.foldl (fun acc f => if acc.contains f then acc else acc.push f) #[]

/-- XMP's simple element text between `<tag>` and `</tag>`, or an `rdf:li` inside it. -/
private def xmpText (x : String) (tag : String) : Option String :=
  (x.splitOn s!"<{tag}>")[1]?.map fun rest =>
    let inner := ((rest.splitOn s!"</{tag}>").headD "").trimAscii.toString
    if inner.startsWith "<" then
      match (inner.splitOn "<rdf:li")[1]? with
      | some li => ((li.splitOn ">")[1]?.getD "").splitOn "<" |>.headD ""
      | none => ""
    else inner

/-- The facts of a file, read with the engine's own reader. -/
public def read (b : ByteArray) : Except String Facts := do
  unless b.size ≥ 8 && b[0]? == some 37 && b[1]? == some 80 do throw "not a PDF file"
  let version := String.ofList ((b.extract 5 8).toList.map fun v => Char.ofNat v.toNat)
  let es := (← PdfRead.objects b).val
  let t := Index.of es
  let tr ← PdfRead.trailer b
  let cat := catalogOf es tr
  let info := t.deref ((tr.get? "Info").getD .null)
  let intents := match t.deref ((cat.get? "OutputIntents").getD .null) with
    | .arr xs => xs.map fun i =>
      let d := t.deref i
      let prof := (d.get? "DestOutputProfile").bind (decodedOf t)
      let n := ((d.get? "DestOutputProfile").map t.deref).bind fun s =>
        ((s.get? "N").bind Obj.int?).map (·.toNat)
      { subtype := nameOf (d.get? "S"), condition := (d.get? "OutputConditionIdentifier").bind textOf
        info := (d.get? "Info").bind textOf, profile := prof.bind Icc.header?, declaredN := n
        embedded := prof.isSome : Intent }
    | _ => #[]
  let xmp := match (cat.get? "Metadata").bind (decodedOf t) with
    | some d => String.fromUTF8? d |>.getD ""
    | none => ""
  -- Only the media and crop boxes inherit through the page tree (ISO 32000-2 Table 31).
  let pages := (es.filter fun e => kindOf e.val == .page).map fun e =>
    let up (k : String) := rectOf t (inherited t e.val k)
    let own (k : String) := rectOf t (e.val.get? k)
    { media := up "MediaBox", crop := up "CropBox", bleed := own "BleedBox"
      trim := own "TrimBox", art := own "ArtBox" : Boxes }
  let pageEntries := es.filter fun e => kindOf e.val == .page
  let annots := pageEntries.zipIdx.flatMap fun (e, p) =>
    match t.deref ((e.val.get? "Annots").getD .null) with
    | .arr xs => xs.filterMap fun a =>
      let d := t.deref a
      let flags := ((d.get? "F").bind Obj.int?).getD 0
      let printable := flags % 8 / 4 == 1 && flags % 4 / 2 == 0
      match nameOf (d.get? "Subtype"), rectOf t (d.get? "Rect") with
      | some s, some r => if printable then some (p, s, r) else none
      | _, _ => none
    | _ => #[]
  let unembedded := unembeddedFonts t
  let places := devicesOf t
  return { version, encrypted := (tr.get? "Encrypt").isSome, intents
           xmpVersion := xmpText xmp "pdfxid:GTS_PDFXVersion", xmpTrapped := xmpText xmp "pdf:Trapped"
           xmpCreated := xmpText xmp "xmp:CreateDate", xmpModified := xmpText xmp "xmp:ModifyDate"
           xmpTitle := (xmpText xmp "dc:title").any (!·.isEmpty)
           xmpDocumentId := xmpText xmp "xmpMM:DocumentID", xmpVersionId := xmpText xmp "xmpMM:VersionID"
           xmpRendition := xmpText xmp "xmpMM:RenditionClass"
           infoTrapped := nameOf (info.get? "Trapped") |>.orElse fun _ =>
             (info.get? "Trapped").bind textOf
           infoCreated := (info.get? "CreationDate").bind textOf
           infoModified := (info.get? "ModDate").bind textOf
           pages, annots
           devices := places.foldl (fun acc (f, _) => if acc.contains f then acc else acc.push f) #[]
           devicePlaces := places, fontsEmbedded := unembedded.isEmpty, unembedded
           iccSpaces := iccSpacesOf t, forbidden := forbiddenOf t }

private def within (inner outer : Rect) : Bool :=
  outer.x0 ≤ inner.x0 && outer.y0 ≤ inner.y0 && inner.x1 ≤ outer.x1 && inner.y1 ≤ outer.y1

private def overlaps (a b : Rect) : Bool :=
  a.x0 < b.x1 && b.x0 < a.x1 && a.y0 < b.y1 && b.y0 < a.y1

private def rectText (r : Rect) : String :=
  "[" ++ " ".intercalate ([r.x0, r.y0, r.x1, r.y1].map fun v => Dim.ratString v.num v.den) ++ "]"

/-- The PDF version a PDF/X-4 file is written in: the PDF 1.6 it is defined on. -/
public def versions : List String := ["1.6"]

/-- The ICC versions a destination profile may carry: version 2, or version 4 up to 4.2, the
ISO 15076-1:2005 edition ISO 15930-7 references. -/
public def iccAdmitted (v : Nat × Nat) : Bool := v.1 == 2 || (v.1 == 4 && v.2 ≤ 2)

/-- The same date in the Info dictionary's spelling and the metadata's. -/
private def sameDate (info xmp : String) : Bool :=
  match PdfDate.parseInfo? info, PdfDate.parseIso? xmp with
  | some x, some y => x == y
  | _, _ => false

/-- Every PDF/X-4 requirement the facts break, in clause order. -/
public def breaches (f : Facts) : Array Breach := Id.run do
  let mut out : Array Breach := #[]
  let bad (rule actual : String) (acc : Array Breach) : Array Breach := acc.push ⟨rule, actual⟩
  unless versions.contains f.version do
    out := bad "version" s!"the file header is PDF {f.version}, not 1.6" out
  if f.encrypted then out := bad "encryption" "the file is encrypted" out
  let x := f.intents.filter (·.subtype == some "GTS_PDFX")
  let space : Option String := match x.toList with
    | [i] => i.profile.map (·.colorSpace)
    | _ => none
  match x.toList with
  | [i] =>
    if !i.embedded then out := bad "output-intent" "the output intent embeds no destination profile" out
    match i.profile with
    | none => out := bad "output-intent" "the destination profile is no readable ICC profile" out
    | some h =>
      if h.deviceClass != "prtr" then
        out := bad "output-intent" s!"the destination profile's class is '{h.deviceClass}', not an output profile" out
      if (Icc.components h.colorSpace).isNone then
        out := bad "output-intent" s!"the destination profile's colour space '{h.colorSpace}' is not CMYK, RGB or gray" out
      if !iccAdmitted h.version then
        out := bad "output-intent" s!"the destination profile is ICC {h.version.1}.{h.version.2}, past 4.2" out
      if i.declaredN != Icc.components h.colorSpace then
        out := bad "output-intent" "the profile stream's /N disagrees with the profile's colour space" out
    if (i.condition.getD "").isEmpty then
      out := bad "output-intent" "the output intent names no OutputConditionIdentifier" out
    if i.condition == some "Custom" && (i.info.getD "").isEmpty then
      out := bad "output-intent" "the output intent's condition is Custom with no /Info describing it" out
  | [] => out := bad "output-intent" "the file carries no GTS_PDFX output intent" out
  | _ => out := bad "output-intent" s!"the file carries {x.size} GTS_PDFX output intents" out
  if f.xmpVersion != some "PDF/X-4" then
    out := bad "metadata" s!"the metadata's pdfxid:GTS_PDFXVersion is {f.xmpVersion.getD "absent"}" out
  if !f.xmpTitle then out := bad "metadata" "the metadata carries no dc:title" out
  if [f.xmpDocumentId, f.xmpVersionId, f.xmpRendition].any (·.all String.isEmpty) then
    out := bad "metadata" "the metadata lacks xmpMM:DocumentID, xmpMM:VersionID or xmpMM:RenditionClass" out
  match f.xmpCreated, f.xmpModified with
  | some c, some m =>
    if (PdfDate.parseIso? c).isNone || (PdfDate.parseIso? m).isNone then
      out := bad "metadata" "the metadata's dates are not ISO 8601" out
  | _, _ => out := bad "metadata" "the metadata lacks xmp:CreateDate or xmp:ModifyDate" out
  match f.infoCreated, f.xmpCreated with
  | some i, some m => if !sameDate i m then out := bad "metadata" "/CreationDate and xmp:CreateDate differ" out
  | _, _ => pure ()
  match f.infoModified, f.xmpModified with
  | some i, some m => if !sameDate i m then out := bad "metadata" "/ModDate and xmp:ModifyDate differ" out
  | _, _ => pure ()
  match f.infoTrapped, f.xmpTrapped with
  | some t, some m =>
    if !(t == "True" || t == "False") then
      out := bad "trapped" s!"/Trapped is {t}, not True or False" out
    else if t != m then out := bad "trapped" s!"/Trapped is {t} and pdf:Trapped {m}" out
  | some _, none => out := bad "trapped" "/Trapped stands in the Info dictionary without pdf:Trapped" out
  | none, some _ => out := bad "trapped" "pdf:Trapped stands in the metadata without /Trapped" out
  | none, none => out := bad "trapped" "the file states neither /Trapped nor pdf:Trapped" out
  for (p, k) in f.pages.zipIdx do
    match p.media with
    | none => out := bad "boxes" s!"page {k + 1} has no /MediaBox" out
    | some media =>
      match p.trim, p.art with
      | some _, some _ => out := bad "boxes" s!"page {k + 1} declares both /TrimBox and /ArtBox" out
      | none, none => out := bad "boxes" s!"page {k + 1} declares neither /TrimBox nor /ArtBox" out
      | _, _ => pure ()
      let crop := p.crop.getD media
      let bleed := p.bleed.getD crop
      if !within crop media then out := bad "boxes" s!"page {k + 1}'s /CropBox {rectText crop} leaves its /MediaBox {rectText media}" out
      if !within bleed crop then out := bad "boxes" s!"page {k + 1}'s /BleedBox {rectText bleed} leaves its /CropBox {rectText crop}" out
      for t in [p.trim, p.art] do
        if let some t := t then
          if !within t bleed then out := bad "boxes" s!"page {k + 1}'s trim {rectText t} leaves its /BleedBox {rectText bleed}" out
  for (k, s, r) in f.annots do
    if s != "PrinterMark" && s != "TrapNet" then
      let area := f.pages[k]?.bind fun p => (p.bleed.orElse fun _ => p.crop).orElse fun _ => p.media
      if area.all (overlaps r) then
        out := bad "annotations" s!"a printable {s} annotation stands on page {k + 1}'s printed area" out
  let forbidden : List String := "Unread" :: match space with
    | some "CMYK" => ["DeviceRGB"]
    | some "RGB " => ["DeviceCMYK"]
    | some "GRAY" => ["DeviceRGB", "DeviceCMYK"]
    | _ => []
  for d in forbidden do
    if f.devices.contains d then
      let places := f.devicePlaces.filterMap fun (g, p) => if g == d then some p else none
      let pages := places.filter (·.startsWith "page ")
      let shown := if pages.size ≤ 3 then places
        else (places.filter (!·.startsWith "page ")).push s!"the content of {pages.size} pages"
      let what := if d == "Unread" then "a colour space built on more than the judge reads"
        else s!"{d}, which the output intent does not characterize"
      out := bad "colour" s!"the file paints in {what}: in {", ".intercalate shown.toList}" out
  for v in f.iccSpaces do
    match v with
    | none => out := bad "colour" "an ICCBased colour space carries no readable ICC profile" out
    | some v =>
      if !iccAdmitted v then
        out := bad "colour" s!"an ICCBased colour space carries an ICC {v.1}.{v.2} profile, past 4.2" out
  for name in f.unembedded do
    out := bad "fonts" s!"the font {name} is not embedded" out
  for c in f.forbidden do out := bad "constructs" s!"the file holds {c}" out
  return out

/-- Why a file is no destination profile for an output intent, or `none` when it is one: an ICC
output profile in CMYK, RGB or gray, its channels the ones a declared count names. -/
public def profileFault (b : ByteArray) (declared : Option Nat) : Option String :=
  match Icc.header? b with
  | none => some "is no ICC profile"
  | some h =>
    if h.deviceClass != "prtr" then some s!"is a '{h.deviceClass}' profile, not an output profile"
    else match Icc.components h.colorSpace with
      | none => some s!"characterizes '{h.colorSpace}', not CMYK, RGB or gray"
      | some n =>
        if declared.all (· == n) then none
        else some s!"has {n} channels where the document declares {declared.getD n}"

/-- W0446 for an output intent's profile the file cannot carry, the file and why in its detail. -/
public def profileRefused (file why : String) (span : Option Span := none) : Diag :=
  Diag.of .W0446 (Diag.say .W0446 .profile file) span (output := some .pdf)
    (help := some "name an ICC output profile beside the document: \\DocumentMetadata{ colorprofiles = { X = name.icc } }")
    (subject := some s!"intent:{file}") (detail := some s!"it {why}")

/-- What a breach of one rule costs, in words free of the site's particulars. -/
private def ruleWords : String → String
  | "version" => "its PDF version is one the standard does not admit"
  | "encryption" => "it is encrypted"
  | "output-intent" => "it has no output intent the standard admits"
  | "metadata" => "its metadata lacks or contradicts what the standard asks"
  | "trapped" => "its trapping is missing, unknown or stated two ways"
  | "boxes" => "a page's boxes break the standard's trim and bleed rules"
  | "annotations" => "a printable annotation stands on a printed area"
  | "colour" => "it paints a device colour its intent does not cover"
  | "fonts" => "a font program is not embedded"
  | "constructs" => "it holds a construct the standard does not admit"
  | _ => "the engine's reader cannot read it back"

private def ruleHelp : String → String
  | "metadata" => "declare the file's title and dates: \\hypersetup{ pdftitle = {Title}, pdfcreationdate = D:20260131090000Z }"
  | "colour" => "the detail names where: give the document's colours and figures CMYK, gray or spot data (\\definecolor{name}{cmyk}{c,m,y,k})"
  | "fonts" => "embed the font the detail names where it is used: export the figure that holds it with its fonts embedded"
  | "constructs" => "a figure's transfer functions, named halftones, OPI links, PostScript, references and actions break the standard: export the figure as PDF/X"
  | "output-intent" => "name the output profile: \\DocumentMetadata{ colorprofiles = { X = name.icc } }"
  | "boxes" => "declare the bleed past the trim, which writes the trim box: \\page{ bleed = 3mm }"
  | "trapped" => "state the trapping as True or False: \\hypersetup{ pdftrapped = False }"
  | "version" => "declare the version the standard is written on: \\DocumentMetadata{ pdfversion = 1.6 }"
  | _ => "declare what the standard asks, as the detail reads: \\pdfmeta{ standard = \"X-4\" } holds the claim"

/-- What a claim that stands still owes: W0444 for the `links` the file leaves out, and N0448 naming
what only a print service's preflight judges, an ICC version 4 output profile among it. -/
public def claimDiags (x : String) (f : Facts) (links : Nat) : Array Diag :=
  let v4 := f.intents.any fun i => i.profile.any (·.version.1 == 4)
  let rgb := f.intents.any fun i => i.profile.any (·.colorSpace == "RGB ")
  let unjudged := ["ink coverage", "line weights", "image resolution", "overprint"] ++
    (if v4 then ["the press's acceptance of an ICC version 4 output profile"] else []) ++
    (if rgb && f.devices.contains "DeviceGray" then ["DeviceGray under an RGB output intent"] else [])
  (if links == 0 then #[] else #[Diag.of .W0444
    (Diag.say .W0444 .link (obj := some (some .standard, (Diag.Name.value s!"PDF/{x}")))) (help := some "the web page keeps them: \\output{ formats = pdf, html }")
    (subject := some "pdfx:links") (output := some .pdf)
    (detail := some s!"{links} link {if links == 1 then "area" else "areas"} left out")]) ++
  #[Diag.of .N0448 (Diag.say .N0448 .standard (Diag.Name.value s!"PDF/{x}")) (subject := some "pdfx:preflight") (output := some .pdf)
    (detail := some ("left to a print service's preflight: " ++ ", ".intercalate unjudged))]

/-- W0445, one per requirement the file breaks, naming what it carries instead in its detail. -/
public def breachDiags (x : String) (bs : Array Breach) : Array Diag :=
  let rules := bs.foldl (fun acc b => if acc.contains b.rule then acc else acc.push b.rule) #[]
  rules.map fun r =>
    Diag.of .W0445 (Diag.say .W0445 .standard (Diag.Name.value s!"PDF/{x}"))
      (help := some (ruleHelp r)) (subject := some s!"pdfx:{r}") (output := some .pdf)
      (detail := some (s!"{ruleWords r}: " ++
        String.intercalate "; " ((bs.filter (·.rule == r)).map (·.actual)).toList))

end LeanTex.Core.PdfX
