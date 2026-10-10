module

public import LeanTex.Core.WhatwgEncodingData

/-!
# Bytes in the encodings the web reads

The WHATWG Encoding Standard's labels and the decoders an XML document's
bytes need: UTF-16 in either byte order, the legacy single-byte encodings —
`windows-1252` among them, which the standard reads for the labels
`iso-8859-1`, `latin1` and `us-ascii` too, as every browser does — and
`x-user-defined`. UTF-8 needs no decoder: the reader validates it as it
stands. The tables are the standard's own (`WhatwgEncodingData`, generated
from its vendored indexes); this module reads them, and states what they
must hold (`dataFaults`, which the suite holds empty).
-/

namespace LeanTex.Core.WhatwgEncoding

/-- **The encoding a label names** (§4.2, "get an encoding"): the label with
ASCII white space trimmed and ASCII lower-cased, looked up; none for a
label the standard does not list. -/
public def lookup (label : String) : Option String :=
  let l := label.trimAscii.toString.map Char.toLower
  (WhatwgEncodingData.labels.find? (·.1 == l)).map (·.2)

/-- A legacy single-byte encoding's index, when `name` names one. -/
public def singleByteIndex? (name : String) : Option String :=
  (WhatwgEncodingData.singleByte.find? (·.1 == name)).map (·.2)

/-- A hexadecimal digit's value. -/
@[inline] private def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else 0

/-- An index's 128 scalars, byte 0x80 first; 0 where the index has no
pointer. -/
public def scalarsOf (index : String) : Array UInt32 := Id.run do
  let cs := index.toList.toArray
  let mut out : Array UInt32 := Array.mkEmpty 128
  for k in [0:128] do
    let v := (List.range 4).foldl (fun acc j => acc * 16 + hexVal (cs[4 * k + j]?.getD '0')) 0
    out := out.push v.toUInt32
  return out

/-- A scalar onto UTF-8 bytes (RFC 3629 §3). -/
@[inline] public def pushUtf8 (out : ByteArray) (c : UInt32) : ByteArray :=
  let cont (v : UInt32) : UInt8 := ((0x80 : UInt32) ||| (v &&& 0x3F)).toUInt8
  if c < 0x80 then out.push c.toUInt8
  else if c < 0x800 then (out.push ((0xC0 : UInt32) ||| (c >>> 6)).toUInt8).push (cont c)
  else if c < 0x10000 then
    ((out.push ((0xE0 : UInt32) ||| (c >>> 12)).toUInt8).push (cont (c >>> 6))).push (cont c)
  else
    (((out.push ((0xF0 : UInt32) ||| (c >>> 18)).toUInt8).push (cont (c >>> 12))).push
      (cont (c >>> 6))).push (cont c)

/-- **A single-byte encoding's bytes as UTF-8** (§9.1's decoder), from
`start`: an ASCII byte is itself, any other its index's scalar. The offset
of the first byte the index does not map is the error. -/
public def decodeSingle (scalars : Array UInt32) (b : ByteArray) (start : Nat) :
    Except Nat ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size + b.size / 2)
  for h : i in [start:b.size] do
    let c := b[i]'(Membership.get_elem_helper h rfl)
    if c < 0x80 then out := out.push c
    else
      let s := scalars[(c - 0x80).toNat]?.getD 0
      if s == 0 then return .error i
      out := pushUtf8 out s
  return .ok out

/-- **`x-user-defined` as UTF-8** (§14.4), from `start`: an ASCII byte is
itself, any other U+F780 plus its distance past 0x80. -/
public def decodeUserDefined (b : ByteArray) (start : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size * 2)
  for h : i in [start:b.size] do
    let c := b[i]'(Membership.get_elem_helper h rfl)
    out := if c < 0x80 then out.push c else pushUtf8 out (0xF780 + (c - 0x80).toUInt32)
  return out

/-- **UTF-16 as UTF-8** (§14.2's shared decoder), from `start`, its code
units in the order `be` says: a surrogate pair is one scalar. A lone
surrogate, and a final odd byte, are the error, at their offset. -/
public def decodeUtf16 (be : Bool) (b : ByteArray) (start : Nat) : Except Nat ByteArray := Id.run do
  let unit (i : Nat) : Nat :=
    let hi := (b[i]?.getD 0).toNat
    let lo := (b[i + 1]?.getD 0).toNat
    if be then hi * 256 + lo else lo * 256 + hi
  let mut out := ByteArray.emptyWithCapacity (b.size + b.size / 2)
  let mut i := start
  for _ in [0:b.size + 1] do
    if b.size ≤ i then break
    if b.size ≤ i + 1 then return .error i
    let u := unit i
    if 0xD800 ≤ u && u ≤ 0xDBFF then
      if b.size ≤ i + 3 then return .error i
      let v := unit (i + 2)
      unless 0xDC00 ≤ v && v ≤ 0xDFFF do return .error i
      out := pushUtf8 out (0x10000 + (u - 0xD800) * 1024 + (v - 0xDC00)).toUInt32
      i := i + 4
    else if 0xDC00 ≤ u && u ≤ 0xDFFF then return .error i
    else
      out := pushUtf8 out u.toUInt32
      i := i + 2
  return .ok out

/-- The encodings the standard names, from its labels. It takes `Unit`, so
the table is read when it is asked for, never when the module initializes
in every process. -/
public def names (_ : Unit) : Array String :=
  WhatwgEncodingData.labels.foldl (fun acc (_, n) => if acc.contains n then acc else acc.push n) #[]

/-- **What the tables must hold**, as the faults they would show: every
index is 128 four-digit scalars, none a surrogate; every label lower case
and trimmed, in strictly increasing order, so named once; every single-byte encoding one the labels name;
and the names the decoders here read — `windows-1252` for the labels a
browser reads as it — among them. The suite holds this empty; it takes
`Unit`, so no process pays for it at initialization. -/
public def dataFaults (_ : Unit) : Array String := Id.run do
  let mut out : Array String := #[]
  for (n, idx) in WhatwgEncodingData.singleByte do
    unless idx.length == 512 && idx.all fun c => c.isDigit || ('A' ≤ c && c ≤ 'F') do
      out := out.push s!"{n}: an index of {idx.length} characters, not 128 scalars"
    if (scalarsOf idx).any fun s => 0xD800 ≤ s && s ≤ 0xDFFF then
      out := out.push s!"{n}: an index maps a byte to a surrogate"
    unless (names ()).contains n do out := out.push s!"{n}: an index no label names"
  let labels := WhatwgEncodingData.labels
  for h : k in [0:labels.size] do
    let (l, _) := labels[k]
    unless l == (l.trimAscii.toString.map Char.toLower) do out := out.push s!"label '{l}' is not folded"
    if 0 < k && !((labels[k - 1]?.map (·.1)).getD "" < l) then out := out.push s!"label '{l}' out of order"
  for (l, n) in [("iso-8859-1", "windows-1252"), ("latin1", "windows-1252"),
      ("us-ascii", "windows-1252"), ("utf-8", "UTF-8"), ("utf-16", "UTF-16LE"),
      ("utf-16be", "UTF-16BE"), ("x-user-defined", "x-user-defined")] do
    unless lookup l == some n do out := out.push s!"label '{l}' does not name {n}"
  return out

end LeanTex.Core.WhatwgEncoding
