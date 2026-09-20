import Std.Data.HashMap
import LeanTex.Core.NfcData

/-!
Canonical normalization to NFC (UAX #15). The engine normalizes text at
input: composed forms are what font cmaps carry (HarfBuzz normalizes
before shaping for the same reason, `_hb_ot_shape_normalize`), so an
NFD-spelled accent (`e` + U+0301) reaches every corpus face as the one
glyph `é` instead of an unanchored mark, and two spellings of one word
make one slug, one hyphenation-cache key, one search hit.

The algorithm is UAX #15 §9's: canonical decomposition (the generated
table is fully expanded; Hangul is arithmetic, Unicode §3.12), canonical
reordering of nonzero-combining-class runs, then canonical composition
over the primary composites. Tables come from `NfcData` (generated from
UnicodeData.txt; see `scripts/gen-nfc-data.lean`).
-/

namespace LeanTex.Core.Nfc

open Std

structure Tables where
  ccc : HashMap UInt32 Nat
  decomp : HashMap UInt32 (Array Char)
  comp : HashMap UInt64 Char
  /-- Merged codepoint ranges of general category L*, sorted. -/
  letters : Array (UInt32 × UInt32)
  lower : HashMap UInt32 Char

def load : Tables := Id.run do
  let mut ccc : HashMap UInt32 Nat := {}
  for entry in NfcData.ccc.splitOn " " do
    if let [k, v] := entry.splitOn ":" then
      ccc := ccc.insert (UInt32.ofNat (k.toNat?.getD 0)) (v.toNat?.getD 0)
  let mut decomp : HashMap UInt32 (Array Char) := {}
  for entry in NfcData.decomp.splitOn " " do
    if let [k, v] := entry.splitOn ":" then
      let parts := (v.splitOn ",").foldl
        (fun a p => a.push (Char.ofNat (p.toNat?.getD 0))) #[]
      decomp := decomp.insert (UInt32.ofNat (k.toNat?.getD 0)) parts
  let mut comp : HashMap UInt64 Char := {}
  for entry in NfcData.comp.splitOn " " do
    if let [k, v] := entry.splitOn ":" then
      if let [a, b] := k.splitOn "," then
        let key := UInt64.ofNat (a.toNat?.getD 0) * 0x100000000
          + UInt64.ofNat (b.toNat?.getD 0)
        comp := comp.insert key (Char.ofNat (v.toNat?.getD 0))
  let mut letters : Array (UInt32 × UInt32) := #[]
  for entry in NfcData.letters.splitOn " " do
    if let [a, b] := entry.splitOn ":" then
      letters := letters.push
        (UInt32.ofNat (a.toNat?.getD 0), UInt32.ofNat (b.toNat?.getD 0))
  let mut lower : HashMap UInt32 Char := {}
  for entry in NfcData.lower.splitOn " " do
    if let [a, b] := entry.splitOn ":" then
      lower := lower.insert (UInt32.ofNat (a.toNat?.getD 0))
        (Char.ofNat (b.toNat?.getD 0))
  return { ccc, decomp, comp, letters, lower }

/-- The tables, built once per process. -/
def tables : Tables := load

-- Hangul syllable composition is arithmetic (Unicode §3.12).
private def sBase : Nat := 0xAC00
private def lBase : Nat := 0x1100
private def vBase : Nat := 0x1161
private def tBase : Nat := 0x11A7
private def lCount : Nat := 19
private def vCount : Nat := 21
private def tCount : Nat := 28
private def sCount : Nat := 11172

private def cccOf (t : Tables) (c : Char) : Nat :=
  t.ccc.getD c.val 0

/-- One character's full canonical decomposition, pushed onto `out`. -/
private def decomposeInto (t : Tables) (out : Array Char) (c : Char) : Array Char := Id.run do
  let n := c.toNat
  if sBase ≤ n && n < sBase + sCount then
    let sIndex := n - sBase
    let mut out := out.push (Char.ofNat (lBase + sIndex / (vCount * tCount)))
    out := out.push (Char.ofNat (vBase + (sIndex % (vCount * tCount)) / tCount))
    let ti := sIndex % tCount
    if ti != 0 then
      out := out.push (Char.ofNat (tBase + ti))
    return out
  match t.decomp[c.val]? with
  | some parts => return out ++ parts
  | none => return out.push c

/-- Canonical reordering (UAX #15): each maximal run of nonzero-class
characters is stably sorted by combining class. Runs are short (a base
letter carries a handful of marks), so the bubble is bounded by the run. -/
private def reorder (t : Tables) (cs : Array Char) : Array Char := Id.run do
  let mut cs := cs
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if h : i < cs.size then
      if cccOf t cs[i] == 0 then
        i := i + 1
      else
        let mut j := i
        for _ in [i:cs.size] do
          if h' : j < cs.size then
            if cccOf t cs[j] != 0 then j := j + 1 else break
          else break
        -- bubble [i, j): j - i passes settle it
        for _ in [i:j] do
          for k in [i:j-1] do
            if h' : k + 1 < cs.size then
              let a := cs[k]'(by omega)
              let b := cs[k+1]
              if cccOf t a > cccOf t b then
                cs := (cs.set! k b).set! (k+1) a
        i := j
    else
      break
  return cs

private def composePair (t : Tables) (a b : Char) : Option Char := Id.run do
  let an := a.toNat
  let bn := b.toNat
  if lBase ≤ an && an < lBase + lCount && vBase ≤ bn && bn < vBase + vCount then
    return some (Char.ofNat (sBase + ((an - lBase) * vCount + (bn - vBase)) * tCount))
  if sBase ≤ an && an < sBase + sCount && (an - sBase) % tCount == 0
      && tBase < bn && bn < tBase + tCount then
    return some (Char.ofNat (an + (bn - tBase)))
  return t.comp[UInt64.ofNat an * 0x100000000 + UInt64.ofNat bn]?

/-- Canonical composition (UAX #15 §9, step 2): each character combines
into the last starter when nothing of equal or higher class blocks it. -/
private def compose (t : Tables) (cs : Array Char) : Array Char := Id.run do
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut starter : Option Nat := none
  let mut lastCcc : Nat := 0
  for c in cs do
    let cc := cccOf t c
    let combined := Id.run do
      if let some si := starter then
        if h : si < out.size then
          if out.size == si + 1 || (lastCcc != 0 && lastCcc < cc) then
            if let some comp := composePair t out[si] c then
              return some (si, comp)
      return none
    match combined with
    | some (si, comp) =>
      out := out.set! si comp
    | none =>
      out := out.push c
      if cc == 0 then
        starter := some (out.size - 1)
      lastCcc := cc
  return out

/-- NFC over a character array. Text whose scalars all sit below U+00C0
has nothing to decompose, reorder, or compose, and passes through whole. -/
def normalizeChars (cs : Array Char) : Array Char := Id.run do
  if cs.all (·.toNat < 0xC0) then
    return cs
  let t := tables
  let mut work : Array Char := Array.mkEmpty cs.size
  for c in cs do
    work := decomposeInto t work c
  compose t (reorder t work)

/-- NFC over a string. -/
def normalize (s : String) : String := Id.run do
  let cs := s.foldl (fun a c => a.push c) (Array.mkEmpty s.utf8ByteSize)
  let out := normalizeChars cs
  let mut r := ""
  for c in out do
    r := r.push c
  return r

/-- A letter by Unicode's general category (L*), by binary search over the
generated ranges. `Char.isAlpha` is ASCII-only: under it a word boundary
excludes é, so an accented word neither hyphenates nor stays one box.
ASCII answers without the search. -/
def isLetter (c : Char) : Bool := Id.run do
  if c.toNat < 0x80 then
    return c.isAlpha
  let rs := tables.letters
  let mut lo := 0
  let mut hi := rs.size
  for _ in [0:rs.size + 1] do
    if h : lo < hi ∧ hi ≤ rs.size then
      let mid := (lo + hi) / 2
      let (a, b) := rs[mid]'(by omega)
      if c.val < a then hi := mid
      else if b < c.val then lo := mid + 1
      else return true
    else
      break
  return false

/-- Unicode simple lowercase (UnicodeData field 13): what pattern matching
against lowercase hyphenation patterns needs — `Char.toLower` is
ASCII-only and leaves É beside é. -/
def toLower (c : Char) : Char :=
  if c.toNat < 0x80 then c.toLower
  else tables.lower.getD c.val c

end LeanTex.Core.Nfc
