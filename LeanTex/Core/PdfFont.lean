module

public import LeanTex.Core.Gfx
public import LeanTex.Core.PdfRead
public import LeanTex.Core.Ink
public import Std.Data.HashMap
import LeanTex.Core.GlyphList
import LeanTex.Core.PdfContentLex
import LeanTex.Core.PdfFilters
import LeanTex.Core.Font

/-! A PDF figure's fonts read for drawing (ISO 32000-2 §9.5–9.10): codes, glyphs, advances and text. -/

namespace LeanTex.Core.PdfFont

open LeanTex.Core LeanTex.Core.PdfRead LeanTex.Core.PdfContentLex

/-- Where a code's glyph lives: a glyph of the embedded program, or a
Type 3 glyph procedure by name. -/
public inductive GlyphRef where
  | gid (n : Nat)
  | proc (name : String)
  deriving Repr, BEq, Hashable, Inhabited

/-- A font's glyph program: an `Ink` source with its glyph-to-text-space matrix, a Type 3 font's
procedures, or nothing to draw with. -/
public inductive Program where
  | ink (src : Ink.Src) (matrix : Array Rat)
  | type3 (procs : Array (String × Obj)) (matrix : Array Rat) (resources : Option Obj)
  | missing
  deriving Inhabited

/-- One code of a string: its value, byte length, glyph, advance in glyph-space thousandths, and text. -/
public structure Code where
  code : Nat
  bytes : Nat
  glyph : Option GlyphRef
  width : Rat
  text : String
  deriving Inhabited

/-- How a font reads its strings: a simple font one byte per code, a composite font by its
codespace ranges and CIDs. -/
public inductive Codes where
  | simple (glyphs : Array (Option GlyphRef)) (widths : Array Rat) (text : Array String)
  | composite (codespace : Array (Nat × Nat × Nat)) (cids : Array (Nat × Nat × Nat))
      (gidOf : Option ByteArray) (cff : Bool) (widths : Std.HashMap Nat Rat) (dw : Rat)
      (text : Std.HashMap Nat String) (vertical : Bool)
  deriving Inhabited

/-- A font read for drawing, `losses` naming what it cannot draw. -/
public structure Loaded where
  program : Program
  codes : Codes
  losses : Array Gfx.Loss
  deriving Inhabited

/-- A number object as an exact rational. -/
public def num? (o : Obj) : Option Rat := PdfContentLex.numRat? o

/-- A stream's decoded bytes, or `none`. -/
public def streamBytes (d : Doc) (o : Obj) : Option ByteArray :=
  match d.stream o with
  | .ok (some (dict, raw)) =>
    match PdfFilters.decode dict raw with
    | .ok (.bytes b) => some b
    | _ => none
  | _ => none

/-- A dictionary's entry as written, the dictionary itself followed one reference. -/
public def entry (d : Doc) (o : Obj) (k : String) : Option Obj :=
  (d.deref o).toOption.bind (·.get? k)

private def codeOf (o : Obj) : Option (Nat × Nat) := do
  let b ← strBytes? o
  return (b.foldl (fun a x => a * 256 + x.toNat) 0, b.size)

/-- UTF-16BE bytes as text; an unpaired surrogate as U+FFFD. -/
public def utf16 (b : ByteArray) : String := Id.run do
  let mut out := ""
  let mut i := 0
  for _ in [0:b.size] do
    if i + 1 ≥ b.size then break
    let u := (b[i]?.getD 0).toNat * 256 + (b[i + 1]?.getD 0).toNat
    i := i + 2
    if 0xD800 ≤ u && u < 0xDC00 && i + 1 < b.size then
      let l := (b[i]?.getD 0).toNat * 256 + (b[i + 1]?.getD 0).toNat
      if 0xDC00 ≤ l && l < 0xE000 then
        out := out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (l - 0xDC00)))
        i := i + 2
      else out := out.push '�'
    else if 0xD800 ≤ u && u < 0xE000 then out := out.push '�'
    else out := out.push (Char.ofNat u)
  return out

private def bumpText (b : ByteArray) (k : Nat) : String :=
  if b.size == 0 then "" else
  let last := (b[b.size - 1]?.getD 0).toNat + (b[b.size - 2]?.getD 0).toNat * 256
  let v := last + k
  let head := b.extract 0 (b.size - 2)
  utf16 (head.push (UInt8.ofNat (v / 256 % 256)) |>.push (UInt8.ofNat (v % 256)))

/-- A ToUnicode CMap's mappings (§9.10.3), code to text. -/
public def toUnicode (cmap : ByteArray) : Std.HashMap Nat String := Id.run do
  let toks := scan cmap
  let mut m : Std.HashMap Nat String := {}
  let mut mode := 0
  let mut args : Array Obj := #[]
  for t in toks do
    match t with
    | .val o => if mode != 0 then args := args.push o
    | .op "beginbfchar" => mode := 1; args := #[]
    | .op "beginbfrange" => mode := 2; args := #[]
    | .op "endbfchar" =>
      for k in [0:args.size / 2] do
        match codeOf (args[2 * k]?.getD .null), strBytes? (args[2 * k + 1]?.getD .null) with
        | some (c, _), some dst => m := m.insert c (utf16 dst)
        | _, _ => pure ()
      mode := 0
    | .op "endbfrange" =>
      for k in [0:args.size / 3] do
        match codeOf (args[3 * k]?.getD .null), codeOf (args[3 * k + 1]?.getD .null) with
        | some (lo, _), some (hi, _) =>
          if lo ≤ hi && hi - lo < 65536 then
            match args[3 * k + 2]?.getD .null with
            | .arr dsts =>
              for i in [0:hi - lo + 1] do
                if let some dst := (dsts[i]?).bind strBytes? then m := m.insert (lo + i) (utf16 dst)
            | o =>
              if let some dst := strBytes? o then
                for i in [0:hi - lo + 1] do m := m.insert (lo + i) (bumpText dst i)
        | _, _ => pure ()
      mode := 0
    | _ => pure ()
  return m

/-- An embedded CMap's codespace ranges and CID mappings (§9.7.6.1). -/
public def cmapRanges (cmap : ByteArray) : Array (Nat × Nat × Nat) × Array (Nat × Nat × Nat) := Id.run do
  let toks := scan cmap
  let mut space : Array (Nat × Nat × Nat) := #[]
  let mut cids : Array (Nat × Nat × Nat) := #[]
  let mut mode := 0
  let mut args : Array Obj := #[]
  for t in toks do
    match t with
    | .val o => if mode != 0 then args := args.push o
    | .op "begincodespacerange" => mode := 1; args := #[]
    | .op "begincidrange" => mode := 2; args := #[]
    | .op "begincidchar" => mode := 3; args := #[]
    | .op "endcodespacerange" =>
      for k in [0:args.size / 2] do
        match codeOf (args[2 * k]?.getD .null), codeOf (args[2 * k + 1]?.getD .null) with
        | some (lo, n), some (hi, _) => space := space.push (n, lo, hi)
        | _, _ => pure ()
      mode := 0
    | .op "endcidrange" =>
      for k in [0:args.size / 3] do
        match codeOf (args[3 * k]?.getD .null), codeOf (args[3 * k + 1]?.getD .null),
            (args[3 * k + 2]?.getD .null).int? with
        | some (lo, _), some (hi, _), some c => cids := cids.push (lo, hi, c.toNat)
        | _, _, _ => pure ()
      mode := 0
    | .op "endcidchar" =>
      for k in [0:args.size / 2] do
        match codeOf (args[2 * k]?.getD .null), (args[2 * k + 1]?.getD .null).int? with
        | some (c, _), some cid => cids := cids.push (c, c, cid.toNat)
        | _, _ => pure ()
      mode := 0
    | _ => pure ()
  return (space, cids)

/-- One cmap subtable, read in place: its bytes, where it starts and its format (0, 4 or 6). -/
public structure Cmap where
  bytes : ByteArray
  offset : Nat
  format : Nat

/-- A font's cmap subtable for `(platform, encoding)`. -/
public def cmapSub (b : ByteArray) (platform encoding : Nat) : Option Cmap := do
  let t ← Ink.findTable b "cmap"
  let n := Ink.u16 b (t.offset + 2)
  let k ← (List.range (min n (b.size / 8))).find? fun k =>
    let e := t.offset + 4 + 8 * k
    Ink.u16 b e == platform && Ink.u16 b (e + 2) == encoding
  let off := t.offset + Ink.u32 b (t.offset + 4 + 8 * k + 4)
  let fmt := Ink.u16 b off
  guard (fmt == 0 || fmt == 4 || fmt == 6)
  return { bytes := b, offset := off, format := fmt }

/-- A code's glyph in a cmap subtable of format 0, 4 or 6; `none` for glyph 0 or an unmapped code. -/
public def Cmap.glyph? (m : Cmap) (c : Nat) : Option Nat :=
  let b := m.bytes
  let off := m.offset
  let g : Nat :=
    if m.format == 0 then (if c < 256 then Ink.u8 b (off + 6 + c) else 0)
    else if m.format == 6 then
      let first := Ink.u16 b (off + 6)
      let count := Ink.u16 b (off + 8)
      if first ≤ c && c < first + count then Ink.u16 b (off + 10 + 2 * (c - first)) else 0
    else
      let segX2 := Ink.u16 b (off + 6)
      let seg := min (segX2 / 2) (b.size / 8)
      let endBase := off + 14
      let startBase := endBase + 2 * seg + 2
      let deltaBase := startBase + 2 * seg
      let rangeBase := deltaBase + 2 * seg
      match (List.range seg).find? (fun k => c ≤ Ink.u16 b (endBase + 2 * k)) with
      | none => 0
      | some k =>
        let startC := Ink.u16 b (startBase + 2 * k)
        let delta := Ink.u16 b (deltaBase + 2 * k)
        let rangeOff := Ink.u16 b (rangeBase + 2 * k)
        if c < startC then 0
        else if rangeOff == 0 then (c + delta) % 65536
        else
          let g0 := Ink.u16 b (rangeBase + 2 * k + rangeOff + 2 * (c - startC))
          if g0 == 0 then 0 else (g0 + delta) % 65536
  if g == 0 then none else some g

/-- An `sfnt`'s glyph count (`maxp`). -/
public def glyphCount (b : ByteArray) : Nat :=
  match Ink.findTable b "maxp" with
  | some t => Ink.u16 b (t.offset + 4)
  | none => 0

/-- An `sfnt`'s units per em (`head`), 1000 when unreadable. -/
public def unitsPerEm (b : ByteArray) : Nat :=
  match Ink.findTable b "head" with
  | some t => let u := Ink.u16 b (t.offset + 18); if u == 0 then 1000 else u
  | none => 1000

/-- An `sfnt` program's outline source and its matrix: a `CFF ` table read
as CFF, else `glyf`. -/
public def sfntProgram (b : ByteArray) : Program :=
  match Ink.findTable b "CFF " with
  | some _ =>
    let src := Ink.Src.make b true 0
    .ink src ((src.cffMatrix 0).getD #[mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0])
  | none =>
    let upem := unitsPerEm b
    .ink (Ink.Src.make b false (glyphCount b)) #[mkRat 1 upem, 0, 0, mkRat 1 upem, 0, 0]

private def encodingOf (d : Doc) (font : Obj) : Option GlyphList.Base × Array (Nat × String) :=
  match (d.field font "Encoding").toOption.getD none with
  | some (.name n) => (GlyphList.Base.ofName? n, #[])
  | some (.dict es) =>
    let enc := Obj.dict es
    let base := match enc.get? "BaseEncoding" with
      | some (.name n) => GlyphList.Base.ofName? n
      | _ => none
    let diffs := match (d.deref ((enc.get? "Differences").getD .null)).toOption with
      | some (.arr xs) => Id.run do
        let mut out : Array (Nat × String) := #[]
        let mut code := 0
        for x in xs do
          match x with
          | .int n => code := n.toNat
          | .name nm =>
            out := out.push (code, nm)
            code := code + 1
          | _ => pure ()
        return out
      | _ => #[]
    (base, diffs)
  | _ => (none, #[])

private def symbolic (d : Doc) (desc : Option Obj) : Bool :=
  match desc.bind fun ds => ((d.field ds "Flags").toOption.getD none).bind Obj.int? with
  | some f => (f / 4) % 2 == 1
  | none => false

private def programOf (d : Doc) (desc : Option Obj) : Program × Option Gfx.Loss × Option ByteArray :=
  let file (k : String) : Option Obj := desc.bind fun ds =>
    match ds with
    | .dict es => (es.find? (·.1 == k)).map (·.2)
    | _ => none
  match file "FontFile2" with
  | some f =>
    match streamBytes d f with
    | some b => (sfntProgram b, none, some b)
    | none => (.missing, some (.font "unreadable"), none)
  | none =>
    match file "FontFile3" with
    | some f =>
      match streamBytes d f, (d.stream f).toOption.getD none with
      | some b, some (dict, _) =>
        match dict.get? "Subtype" with
        | some (.name "OpenType") => (sfntProgram b, none, some b)
        | _ =>
          let src := Ink.Src.ofCff b
          (.ink src ((src.cffMatrix 0).getD #[mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0]), none, none)
      | _, _ => (.missing, some (.font "unreadable"), none)
    | none =>
      match file "FontFile" with
      | some _ => (.missing, some (.font "type1"), none)
      | none => (.missing, some (.font "nonembedded"), none)

/-- A TrueType program's glyphs by name from its 'post' table, each name to the first glyph it names. -/
public def postGlyphs (b : ByteArray) : Std.HashMap String Nat := Id.run do
  let some t := Ink.findTable b "post" | return {}
  if !(Ink.fits b t) || t.length < 32 then return {}
  let version := Ink.u32 b t.offset
  let mut m : Std.HashMap String Nat := {}
  if version == 0x00010000 then
    for i in [0:258] do
      if let some n := GlyphList.macGlyphName i then
        if !m.contains n then m := m.insert n i
    return m
  if version != 0x00020000 || t.length < 34 then return m
  let numGlyphs := Ink.u16 b (t.offset + 32)
  let indices := t.offset + 34
  let tableEnd := t.offset + t.length
  if indices + 2 * numGlyphs > tableEnd then return m
  let mut names : Array String := #[]
  let mut p := indices + 2 * numGlyphs
  for _ in [0:t.length] do
    if p ≥ tableEnd then break
    let len := Ink.u8 b p
    if p + 1 + len > tableEnd then break
    names := names.push (String.ofList ((b.extract (p + 1) (p + 1 + len)).toList.map Char.ofUInt8))
    p := p + 1 + len
  for g in [0:numGlyphs] do
    let i := Ink.u16 b (indices + 2 * g)
    let n := if i < 258 then GlyphList.macGlyphName i else names[i - 258]?
    if let some n := n then
      if !n.isEmpty && !m.contains n then m := m.insert n g
  return m

private def simpleWidths (d : Doc) (font : Obj) (desc : Option Obj) : Array Rat :=
  let first := (((d.field font "FirstChar").toOption.getD none).bind Obj.int?).getD 0
  let missing := ((desc.bind fun ds => (d.field ds "MissingWidth").toOption.getD none).bind num?).getD 0
  let ws : Array Rat := match (d.field font "Widths").toOption.getD none with
    | some (.arr xs) => xs.map fun x => ((d.deref x).toOption.bind num?).getD missing
    | _ => #[]
  (Array.range 256).map fun (c : Nat) =>
    if (c : Int) ≥ first then (ws[c - first.toNat]?).getD missing else missing

/-- A glyph name's glyph in a name-keyed CFF: the name itself, else the `uniXXXX` or `uXXXX`
spelling of its scalar. -/
public def cffNameGlyph (src : Ink.Src) (n : String) : Option Nat :=
  (src.nameGlyph n).orElse fun _ =>
    match (GlyphList.nameText n).map String.toList with
    | some [ch] =>
      let hex := String.ofList ((Nat.toDigits 16 ch.toNat).map Char.toUpper)
      let hex4 := "".pushn '0' (4 - hex.length) ++ hex
      (if ch.toNat < 0x10000 then src.nameGlyph ("uni" ++ hex4) else none).orElse fun _ =>
        src.nameGlyph ("u" ++ hex4)
    | _ => none

/-- A simple font read for drawing (§9.6): each code's glyph, width and text. -/
public def loadSimple (d : Doc) (font : Obj) : Loaded := Id.run do
  let subtype := match (d.field font "Subtype").toOption.getD none with
    | some (.name n) => n
    | _ => ""
  let desc := (d.field font "FontDescriptor").toOption.getD none
  let (base, diffs) := encodingOf d font
  let isSym := symbolic d desc
  let explicit (c : Nat) : Option String :=
    match diffs.findRev? (·.1 == c) with
    | some (_, n) => some n
    | none => base.map (·.name c)
  let uni : Std.HashMap Nat String := match entry d font "ToUnicode" with
    | some o => match streamBytes d o with
      | some b => toUnicode b
      | none => {}
    | none => {}
  let widths := simpleWidths d font desc
  let textOf (named : Nat → Option String) (c : Nat) : String :=
    match uni.get? c with
    | some t => t
    | none =>
      let fromName (n : String) : Option String := if n.isEmpty then none else GlyphList.nameText n
      let t : Option String := match diffs.findRev? (·.1 == c), base with
        | some (_, n), _ => fromName n
        | none, some e => (e.scalar? c).map String.singleton
        | none, none => (named c).bind fromName
      t.getD ""
  if subtype == "Type3" then
    let procs : Array (String × Obj) := match (d.field font "CharProcs").toOption.getD none with
      | some (.dict es) => es
      | _ => #[]
    let matrix : Array Rat := match (d.field font "FontMatrix").toOption.getD none with
      | some (.arr xs) =>
        let ms := xs.filterMap fun x => (d.deref x).toOption.bind num?
        if ms.size == 6 then ms else #[mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0]
      | _ => #[mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0]
    let res := (d.field font "Resources").toOption.getD none
    let named (c : Nat) : Option String :=
      (explicit c).orElse fun _ => if isSym then none else some (GlyphList.standardName c)
    let glyphs := (Array.range 256).map fun c =>
      (named c).bind fun n => if procs.any (·.1 == n) then some (GlyphRef.proc n) else none
    return { program := .type3 procs matrix res, codes := .simple glyphs widths ((Array.range 256).map (textOf named))
             losses := #[] }
  let (program, loss, sfnt?) := programOf d desc
  match program, sfnt? with
  | .ink _ _, some b =>
    let named (c : Nat) : Option String :=
      (explicit c).orElse fun _ => if isSym then none else some (GlyphList.standardName c)
    let scalarOf (c : Nat) : Option Char :=
      match diffs.findRev? (·.1 == c) with
      | some (_, n) => GlyphList.nameScalar n
      | none =>
        match base with
        | some e => e.scalar? c
        | none => if isSym then none else GlyphList.Base.standard.scalar? c
    let uniRows := cmapSub b 3 1
    let symRows := cmapSub b 3 0
    let macRows := cmapSub b 1 0
    let look (m : Option Cmap) (c : Nat) : Option Nat := m.bind (·.glyph? c)
    let post := postGlyphs b
    let postName (c : Nat) : Option String :=
      (explicit c).orElse fun _ => some (GlyphList.Base.winAnsi.name c)
    let glyphs := (Array.range 256).map fun c =>
      let byUnicode := (scalarOf c).bind fun ch => look uniRows ch.toNat
      let bySymbol := (look symRows (0xF000 + c)).orElse fun _ => look symRows c
      let byMac := look macRows c
      let g := if isSym || (uniRows.isNone && symRows.isSome) then
          bySymbol.orElse fun _ => byMac.orElse fun _ => byUnicode
        else byUnicode.orElse fun _ => bySymbol.orElse fun _ => byMac
      let g := g.orElse fun _ => (postName c).bind fun n => if n.isEmpty then none else post.get? n
      some (GlyphRef.gid (g.getD 0))
    return { program, codes := .simple glyphs widths ((Array.range 256).map (textOf named)), losses := loss.toArray }
  | .ink src _, none =>
    let glyph (c : Nat) : Option Nat :=
      match explicit c with
      | some n => if n.isEmpty then none else cffNameGlyph src n
      | none => src.builtinGlyph c
    let named (c : Nat) : Option String :=
      (explicit c).orElse fun _ => (glyph c).bind src.glyphName
    let glyphs := (Array.range 256).map fun c => (glyph c).map GlyphRef.gid
    return { program, codes := .simple glyphs widths ((Array.range 256).map (textOf named)), losses := loss.toArray }
  | _, _ =>
    let named (c : Nat) : Option String :=
      (explicit c).orElse fun _ => if isSym then none else some (GlyphList.standardName c)
    return { program, codes := .simple (Array.replicate 256 none) widths ((Array.range 256).map (textOf named))
             losses := loss.toArray }

private def cidWidths (d : Doc) (cidFont : Obj) : Std.HashMap Nat Rat := Id.run do
  let mut m : Std.HashMap Nat Rat := {}
  let xs := match (d.field cidFont "W").toOption.getD none with
    | some (.arr xs) => xs
    | _ => #[]
  let mut i := 0
  for _ in [0:xs.size + 1] do
    if i ≥ xs.size then break
    let first := ((xs[i]?).bind fun x => (d.deref x).toOption.bind Obj.int?).getD 0
    match (xs[i + 1]?).bind fun x => (d.deref x).toOption with
    | some (.arr ws) =>
      for h : k in [0:ws.size] do
        if let some w := num? ws[k] then m := m.insert (first.toNat + k) w
      i := i + 2
    | some o =>
      let last := (o.int?).getD first
      let w := ((xs[i + 2]?).bind fun x => (d.deref x).toOption.bind num?).getD 0
      if first ≤ last && last - first < 65536 then
        for k in [0:(last - first).toNat + 1] do m := m.insert (first.toNat + k) w
      i := i + 3
    | none => i := i + 1
  return m

/-- A composite font read for drawing (§9.7); a predefined CMap other than the identities is a loss. -/
public def loadComposite (d : Doc) (font : Obj) : Loaded := Id.run do
  let desc0 := match (d.field font "DescendantFonts").toOption.getD none with
    | some (.arr xs) => (xs[0]?).bind fun x => (d.deref x).toOption
    | _ => none
  let cidFont := desc0.getD .null
  let desc := (d.field cidFont "FontDescriptor").toOption.getD none
  let (program, loss, _) := programOf d desc
  let identity : Array (Nat × Nat × Nat) := #[(2, 0, 0xFFFF)]
  let (space, cids, vertical, cmapLoss) : Array (Nat × Nat × Nat) × Array (Nat × Nat × Nat) × Bool ×
      Option Gfx.Loss :=
    match entry d font "Encoding" with
    | some (.name "Identity-H") => (identity, #[(0, 0xFFFF, 0)], false, none)
    | some (.name "Identity-V") => (identity, #[(0, 0xFFFF, 0)], true, none)
    | some (.name n) => (identity, #[(0, 0xFFFF, 0)], false, some (.font s!"cmap-{n}"))
    | some o =>
      match streamBytes d o with
      | some b =>
        let (sp, cs) := cmapRanges b
        let vert := match (d.stream o).toOption.getD none with
          | some (dict, _) => dict.get? "WMode" == some (.int 1)
          | none => false
        (if sp.isEmpty then identity else sp, cs, vert, none)
      | none => (identity, #[(0, 0xFFFF, 0)], false, some (.font "cmap-unreadable"))
    | none => (identity, #[(0, 0xFFFF, 0)], false, some (.font "cmap-missing"))
  let gidOf : Option ByteArray := (entry d cidFont "CIDToGIDMap").bind fun o => match o with
    | .name _ => none
    | o => streamBytes d o
  let isCff := match program with
    | .ink src _ => src.isCidCff
    | _ => false
  let dw := (((d.field cidFont "DW").toOption.getD none).bind num?).getD 1000
  let text : Std.HashMap Nat String := match entry d font "ToUnicode" with
    | some o => match streamBytes d o with
      | some b => toUnicode b
      | none => {}
    | none => {}
  return { program, codes := .composite space cids gidOf isCff (cidWidths d cidFont) dw text vertical
           losses := loss.toArray ++ cmapLoss.toArray ++ (if vertical then #[.font "vertical"] else #[]) }

/-- A font dictionary read for drawing, by its subtype. -/
public def load (d : Doc) (font : Obj) : Loaded :=
  match (d.field font "Subtype").toOption.getD none with
  | some (.name "Type0") => loadComposite d font
  | _ => loadSimple d font

/-- A string's codes (§9.4.3, §9.7.6.2), each with its CID, glyph, width and text. -/
public def Loaded.codes? (f : Loaded) (s : ByteArray) : Array Code := Id.run do
  match f.codes with
  | .simple glyphs widths text =>
    return s.foldl (fun acc b =>
      let c := b.toNat
      acc.push { code := c, bytes := 1, glyph := (glyphs[c]?).getD none
                 width := (widths[c]?).getD 0, text := (text[c]?).getD "" }) #[]
  | .composite space cids gidOf cff widths dw text _ =>
    let mut out : Array Code := #[]
    let mut i := 0
    for _ in [0:s.size + 1] do
      if i ≥ s.size then break
      let mut len := 1
      let mut found := false
      for n in [1:5] do
        if !found && i + n ≤ s.size then
          let v := (s.extract i (i + n)).foldl (fun a x => a * 256 + x.toNat) 0
          if space.any fun (bn, lo, hi) => bn == n && lo ≤ v && v ≤ hi then
            len := n
            found := true
      let code := (s.extract i (i + len)).foldl (fun a x => a * 256 + x.toNat) 0
      i := i + len
      let cid := ((cids.find? fun (lo, hi, _) => lo ≤ code && code ≤ hi).map
        fun (lo, _, c0) => c0 + (code - lo)).getD 0
      let glyph : Option GlyphRef :=
        match f.program with
        | .ink src _ =>
          if cff then (src.cidGlyph cid).map GlyphRef.gid
          else match gidOf with
            | some m => some (.gid ((m[2 * cid]?.getD 0).toNat * 256 + (m[2 * cid + 1]?.getD 0).toNat))
            | none => some (.gid cid)
        | _ => none
      out := out.push { code, bytes := len, glyph, width := (widths.get? cid).getD dw
                        text := (text.get? code).getD "" }
    return out

end LeanTex.Core.PdfFont
