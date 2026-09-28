import LeanTex.Core.Font

namespace LeanTex.Core.FontSubset

open LeanTex.Core.Ink

/-! The font program a PDF embeds: the face's own file with the glyphs its
pages never paint dropped, as LuaTeX and every other PDF engine embeds a
subset. Glyph ids stay where they are — `Identity-H` and `/W` name glyphs
by the face's own ids — so a dropped glyph is an empty one: a bare
`endchar` in CFF, a zero-length entry in `glyf`. The text-layout tables go
too: the file positions every glyph itself, and no viewer shapes an
embedded program. Anything this does not read with certainty keeps the
face's own bytes for that part — a CID-keyed or seac-composed CFF, a
variable face — so a dropped glyph can only ever be one no page paints. -/

/-- Tables no PDF viewer reads from an embedded program: the OpenType
layout tables, the legacy kern table, and a signature the subset would
invalidate. -/
def droppedTables : List String :=
  ["GSUB", "GPOS", "GDEF", "BASE", "JSTF", "MATH", "kern", "DSIG"]

private def pushU16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v / 256 % 256).toUInt8).push (v % 256).toUInt8

private def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  pushU16 (pushU16 b (v / 65536 % 65536)) (v % 65536)

private def setU32 (b : ByteArray) (i v : Nat) : ByteArray :=
  (((b.set! i (v / 16777216 % 256).toUInt8).set! (i + 1) (v / 65536 % 256).toUInt8).set!
    (i + 2) (v / 256 % 256).toUInt8).set! (i + 3) (v % 256).toUInt8

/-- The sfnt checksum: the sum of the big-endian words, the tail zero-padded. -/
private def checksum (b : ByteArray) : Nat := Id.run do
  let mut s : UInt32 := 0
  for i in [0:(b.size + 3) / 4] do
    s := s + (u32 b (4 * i)).toUInt32
  return s.toNat

/-- An sfnt of these tables: the directory sorted by tag, each table on a
4-byte boundary with its checksum, and `head.checkSumAdjustment` set over
the whole file (OpenType, "Font file" and `head`). -/
def assemble (flavor : Nat) (tables : Array (String × ByteArray)) : ByteArray := Id.run do
  let ts := (tables.qsort fun a b => a.1 < b.1).map fun (tag, d) =>
    (tag, if tag == "head" && d.size ≥ 12 then setU32 d 8 0 else d)
  let n := ts.size
  let mut sel := 0
  for k in [0:16] do
    if 2 ^ (k + 1) ≤ n then sel := k + 1
  let range := 2 ^ sel * 16
  let mut out := pushU32 ByteArray.empty flavor
  out := pushU16 (pushU16 (pushU16 (pushU16 out n) range) sel) (n * 16 - range)
  let mut off := 12 + 16 * n
  let mut headAt : Option Nat := none
  for (tag, d) in ts do
    out := out ++ tag.toUTF8
    out := pushU32 (pushU32 (pushU32 out (checksum d)) off) d.size
    if tag == "head" && d.size ≥ 12 then headAt := some off
    off := off + (d.size + 3) / 4 * 4
  for (_, d) in ts do
    out := out ++ d
    for _ in [0:(4 - d.size % 4) % 4] do
      out := out.push 0
  match headAt with
  | some h => return setU32 out (h + 8) ((0xB1B0AFBA + 0x100000000 - checksum out) % 0x100000000)
  | none => return out

/-- A CFF DICT's integer operands, each with where it is spelled:
`(operator, start, length, value)`, a two-byte operator as `1200 + b1`.
Reals are skipped: no offset is ever spelled as one. -/
private def dictOperands (b : ByteArray) (s e : Nat) : Array (Nat × Nat × Nat × Int) := Id.run do
  let mut pend : Array (Nat × Nat × Int) := #[]
  let mut out : Array (Nat × Nat × Nat × Int) := #[]
  let mut p := s
  for _ in [0:e - s + 1] do
    if p ≥ e then break
    let b0 := u8 b p
    if b0 ≥ 32 && b0 ≤ 246 then
      pend := pend.push (p, 1, (b0 : Int) - 139)
      p := p + 1
    else if b0 ≥ 247 && b0 ≤ 250 then
      pend := pend.push (p, 2, ((b0 : Int) - 247) * 256 + u8 b (p + 1) + 108)
      p := p + 2
    else if b0 ≥ 251 && b0 ≤ 254 then
      pend := pend.push (p, 2, -((b0 : Int) - 251) * 256 - u8 b (p + 1) - 108)
      p := p + 2
    else if b0 == 28 then
      pend := pend.push (p, 3, i16 b (p + 1))
      p := p + 3
    else if b0 == 29 then
      pend := pend.push (p, 5, i32 b (p + 1))
      p := p + 5
    else if b0 == 30 then
      p := p + 1
      for _ in [0:e - p + 1] do
        let x := u8 b p
        p := p + 1
        if x % 16 == 15 || x / 16 == 15 then break
    else
      let op := if b0 == 12 then 1200 + u8 b (p + 1) else b0
      for (ps, l, x) in pend do
        out := out.push (op, ps, l, x)
      pend := #[]
      p := p + (if b0 == 12 then 2 else 1)
  return out

/-- `v` in exactly `len` bytes of CFF DICT integer spelling, if it has one. -/
private def respell (v : Int) (len : Nat) : Option ByteArray :=
  if len == 1 && -107 ≤ v && v ≤ 107 then
    some (ByteArray.mk #[(v + 139).toNat.toUInt8])
  else if len == 2 && 108 ≤ v && v ≤ 1131 then
    some (ByteArray.mk #[((v - 108) / 256 + 247).toNat.toUInt8, ((v - 108) % 256).toNat.toUInt8])
  else if len == 3 && -32768 ≤ v && v ≤ 32767 then
    some (pushU16 (ByteArray.mk #[28]) ((v + 65536) % 65536).toNat)
  else if len == 5 && -2147483648 ≤ v && v ≤ 2147483647 then
    some (pushU32 (ByteArray.mk #[29]) ((v + 4294967296) % 4294967296).toNat)
  else none

/-- A CFF INDEX of these entries, its offsets as narrow as they fit. -/
private def indexOf (entries : Array ByteArray) : ByteArray := Id.run do
  let total := entries.foldl (fun n e => n + e.size) 0 + 1
  let osz := if total < 0x100 then 1 else if total < 0x10000 then 2
    else if total < 0x1000000 then 3 else 4
  let mut out := (pushU16 ByteArray.empty entries.size).push osz.toUInt8
  let mut o := 1
  for i in [0:entries.size + 1] do
    for k in [0:osz] do
      out := out.push (o / 256 ^ (osz - 1 - k) % 256).toUInt8
    o := o + ((entries[i]?).map (·.size)).getD 0
  for e in entries do
    out := out ++ e
  return out

/-- The `CFF ` table at `t` with every glyph outside `keep` reduced to a
bare `endchar`: the CharStrings INDEX rewritten in place, and every Top
DICT offset past it moved back by what it shrank, each in its own
spelling's width. `none` — keep the table as it is — for anything outside
what this reads with certainty: a CID-keyed face, a kept glyph the outline
decoder cannot read whole (a seac glyph composes from two others), an
offset into the old INDEX, or one that no longer fits its spelling — and
when there is nothing to drop. `src` is the face's prepared outline source
and `decodes g` whether glyph `g`'s outline reads whole under it: the
face's own (`Font.inkSrc`, `Font.yExtent`), which its layout has mostly
asked already, so embedding parses and decodes nothing twice. -/
def cffDrop (b : ByteArray) (t : Table) (keep : Array Bool) (src : Src) (decodes : Nat → Bool) :
    Option ByteArray := do
  guard (fits b t)
  let .cffSrc .. := src | failure
  for h : g in [0:keep.size] do
    if keep[g] then guard (decodes g)
  let base := t.offset
  let (_, p1) ← parseIndex b (base + u8 b (base + 2))
  let (tops, p2) ← parseIndex b p1
  let (_, p3) ← parseIndex b p2
  let (_, p4) ← parseIndex b p3
  let (ts, te) ← tops[0]?
  let ops := dictOperands b ts te
  let (_, _, _, csRel) ← ops.find? (·.1 == 17)
  let csStart := base + csRel.toNat
  guard (p4 ≤ csStart)
  let (cs, csEnd) ← parseIndex b csStart
  guard (cs.size == keep.size && csEnd ≤ base + t.length)
  guard ((cs.zip keep).any fun ((s, e), k) => !k && e - s > 1)
  let idx := indexOf ((cs.zip keep).map fun ((s, e), k) =>
    if k then b.extract s e else ByteArray.mk #[14])
  guard (idx.size ≤ csEnd - csStart)
  let shrink : Int := ((csEnd - csStart - idx.size : Nat) : Int)
  let privAt := ((ops.filter (·.1 == 18)).back?).map (·.2.1)
  let mut head := b.extract base csStart
  for (op, ps, len, v) in ops do
    let isOffset := (op == 15 && v > 2) || (op == 16 && v > 1) || (op == 18 && privAt == some ps)
    if isOffset && base + v.toNat ≥ csEnd then
      let sp ← respell (v - shrink) len
      head := sp.copySlice 0 head (ps - base) len
    else if isOffset && base + v.toNat > csStart then
      failure
  return head ++ idx ++ b.extract csEnd (base + t.length)

/-- The glyph ids a TrueType composite glyph's data names as components. -/
private def components (b : ByteArray) (s e : Nat) : Array Nat := Id.run do
  if s + 10 > e || i16 b s ≥ 0 then return #[]
  let mut out : Array Nat := #[]
  let mut p := s + 10
  for _ in [0:(e - s) / 4 + 1] do
    if p + 4 > e then break
    let flags := u16 b p
    out := out.push (u16 b (p + 2))
    p := p + 4 + (if flags &&& 1 != 0 then 4 else 2) +
      (if flags &&& 8 != 0 then 2 else if flags &&& 64 != 0 then 4
       else if flags &&& 128 != 0 then 8 else 0)
    if flags &&& 32 == 0 then break
  return out

/-- `glyf`, `loca` and `head` with every glyph outside `keep` — closed
under composite components — emptied: a zero-length `loca` entry, the
spec's own empty glyph. `loca` is written long, and `head` says so. `none`
for tables this cannot read, and when there is nothing to drop. -/
def glyfDrop (b : ByteArray) (keep : Array Bool) :
    Option (ByteArray × ByteArray × ByteArray) := do
  let head ← findTable b "head"
  let loca ← findTable b "loca"
  let glyf ← findTable b "glyf"
  guard (fits b head && fits b loca && fits b glyf && head.length ≥ 54)
  let n := keep.size
  let long := u16 b (head.offset + 50) == 1
  guard ((n + 1) * (if long then 4 else 2) ≤ loca.length)
  let offAt (i : Nat) : Nat :=
    if long then u32 b (loca.offset + 4 * i) else 2 * u16 b (loca.offset + 2 * i)
  for i in [0:n] do
    guard (offAt i ≤ offAt (i + 1) && offAt (i + 1) ≤ glyf.length)
  let mut kept := keep
  let mut work := keep.zipIdx.filterMap fun (k, g) => if k then some g else none
  for _ in [0:n + 1] do
    match work.back? with
    | none => break
    | some g =>
      work := work.pop
      for c in components b (glyf.offset + offAt g) (glyf.offset + offAt (g + 1)) do
        if kept[c]? == some false then
          kept := kept.set! c true
          work := work.push c
  guard (kept.zipIdx.any fun (k, i) => !k && offAt i < offAt (i + 1))
  let mut g' := ByteArray.empty
  let mut l' := ByteArray.empty
  for (k, i) in kept.zipIdx do
    l' := pushU32 l' g'.size
    if k then
      g' := g' ++ b.extract (glyf.offset + offAt i) (glyf.offset + offAt (i + 1))
      for _ in [0:(4 - g'.size % 4) % 4] do
        g' := g'.push 0
  l' := pushU32 l' g'.size
  let h' := ((b.extract head.offset (head.offset + head.length)).set! 50 0).set! 51 1
  return (g', l', h')

/-- The program a PDF embeds for a face whose pages paint the glyphs
`used`, and whether it is a subset (so the file names it with a tag): the
face's tables minus `droppedTables`, its outlines minus every glyph `used`
does not reach (`.notdef` always kept). A variable face, a table directory
this cannot read, or a result the face parser would not read back embeds
the face's own bytes. -/
def program (font : Font.Font) (used : Array Nat) : ByteArray × Bool := Id.run do
  let data := font.data
  if data.size < 12 || (findTable data "fvar").isSome || (findTable data "CFF2").isSome then
    return (data, false)
  let n := match findTable data "maxp" with
    | some m => u16 data (m.offset + 4)
    | none => 0
  if n == 0 then return (data, false)
  let mut keep := (Array.replicate n false).set! 0 true
  for g in used do
    if g < n then keep := keep.set! g true
  let mut out : Array (String × ByteArray) := #[]
  let mut cffAt : Option Table := none
  for k in [0:u16 data 4] do
    let e := 12 + 16 * k
    let t : Table := ⟨u32 data (e + 8), u32 data (e + 12)⟩
    let some tag := String.fromUTF8? (data.extract e (e + 4)) | return (data, false)
    unless tag.utf8ByteSize == 4 && fits data t do return (data, false)
    if tag == "CFF " then cffAt := some t
    unless droppedTables.contains tag do
      out := out.push (tag, data.extract t.offset (t.offset + t.length))
  let mut dropped := false
  if font.isCff then
    if let some cff := cffAt.bind fun t =>
        cffDrop data t keep font.inkSrc.get (font.yExtent · |>.isSome) then
      out := out.map fun (tag, d) => (tag, if tag == "CFF " then cff else d)
      dropped := true
  else
    if let some (g, l, h) := glyfDrop data keep then
      out := out.map fun (tag, d) =>
        (tag, if tag == "glyf" then g else if tag == "loca" then l
              else if tag == "head" then h else d)
      dropped := true
  let prog := assemble (u32 data 0) out
  match Font.parse prog with
  | .ok _ => return (prog, dropped)
  | .error _ => return (data, false)

end LeanTex.Core.FontSubset
