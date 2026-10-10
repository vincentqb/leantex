module

public import LeanTex.Core.GlyphListData
public import Std.Data.HashMap

/-!
# Glyph names and the PDF's standard encodings

The reading a simple font's codes need (ISO 32000-2 §9.6.5–9.6.6): a code
to a glyph name through StandardEncoding, or to the scalar it means
through WinAnsiEncoding or MacRomanEncoding, and a glyph name to its
scalars through the Adobe Glyph List and its naming conventions (`uniXXXX`,
`uXXXX`, a suffix after a period, ligature components joined by `_`).
The tables are `GlyphListData`, generated; this module owns how they are
read.
-/

namespace LeanTex.Core.GlyphList

/-- The glyph list as a map from name to its scalars, built once, on the
first lookup. -/
public def aglMap : Thunk (Std.HashMap String (Array Char)) := Thunk.mk fun _ => Id.run do
  let mut m : Std.HashMap String (Array Char) := {}
  for row in GlyphListData.agl.splitOn "\n" do
    match row.splitOn ";" with
    | [name, scalars] =>
      let cs := (scalars.splitOn " ").filterMap fun h =>
        (h.toList.foldl (fun acc c => acc.bind fun a =>
          (if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
           else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
           else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87) else none).map (a * 16 + ·))
          (some 0)).map Char.ofNat
      unless m.contains name do m := m.insert name cs.toArray
    | _ => pure ()
  return m

/-- `n` hexadecimal digits as a number, or `none`. Uppercase only, as the
glyph-naming convention spells them. -/
private def upperHex (s : List Char) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun a =>
    (if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
     else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none).map (a * 16 + ·)) (some 0)

/-- A scalar a `uni`/`u` name may spell: not a surrogate, inside Unicode. -/
private def scalarOk (v : Nat) : Bool := v < 0xD800 || (0xDFFF < v && v ≤ 0x10FFFF)

/-- One component of a glyph name (no period, no underscore) as scalars:
the glyph list's entry, then `uni` followed by groups of four uppercase
hex digits, then `u` followed by four to six. -/
private def componentScalars (c : String) : Option (Array Char) :=
  match aglMap.get.get? c with
  | some cs => some cs
  | none =>
    let cs := c.toList
    match cs with
    | 'u' :: 'n' :: 'i' :: rest =>
      if rest.length > 0 && rest.length % 4 == 0 then Id.run do
        let mut out : Array Char := #[]
        let mut r := rest
        for _ in [0:rest.length / 4] do
          match upperHex (r.take 4) with
          | some v => if scalarOk v then out := out.push (Char.ofNat v) else return none
          | none => return none
          r := r.drop 4
        return some out
      else none
    | 'u' :: rest =>
      if 4 ≤ rest.length && rest.length ≤ 6 then
        (upperHex rest).bind fun v => if scalarOk v then some #[Char.ofNat v] else none
      else none
    | _ => none

/-- **A glyph name's text** (the Adobe Glyph List specification's mapping):
the part before the first period, its `_`-separated components each read
by `componentScalars`; `none` when no component reads. -/
public def nameText (name : String) : Option String :=
  let base := (name.splitOn ".").headD ""
  if base.isEmpty then none else
  let parts := (base.splitOn "_").map componentScalars
  if parts.all Option.isNone then none
  else some (String.ofList (parts.flatMap fun p => (p.getD #[]).toList))

/-- The first scalar a glyph name reads as. -/
public def nameScalar (name : String) : Option Char :=
  (nameText name).bind fun s => s.toList.head?

/-- The base encodings a simple font may name (§9.6.5, Table 112), and the
font's own encoding. -/
public inductive Base where
  | standard
  | winAnsi
  | macRoman
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A base encoding by its PDF name. -/
public def Base.ofName? : String → Option Base
  | "StandardEncoding" => some .standard
  | "WinAnsiEncoding" => some .winAnsi
  | "MacRomanEncoding" => some .macRoman
  | _ => none

/-- StandardEncoding's name for a code; empty for `.notdef`. -/
public def standardName (code : Nat) : String := GlyphListData.standardEncoding[code]?.getD ""

/-- The scalar a code means in a base encoding, `none` where it means
nothing. StandardEncoding reads through its glyph names. -/
public def Base.scalar? (e : Base) (code : Nat) : Option Char :=
  match e with
  | .standard => nameScalar (standardName code)
  | .winAnsi => (GlyphListData.winAnsiEncoding[code]?).bind fun v =>
    if v == 0 then none else some (Char.ofNat v)
  | .macRoman => (GlyphListData.macRomanEncoding[code]?).bind fun v =>
    if v == 0 then none else some (Char.ofNat v)

/-- The glyph name a code selects in a base encoding (ISO 32000-2 Annex
D); empty for none. -/
public def Base.name (e : Base) (code : Nat) : String :=
  match e with
  | .standard => standardName code
  | .winAnsi => GlyphListData.winAnsiNames[code]?.getD ""
  | .macRoman => GlyphListData.macRomanNames[code]?.getD ""

/-- The CFF Expert encoding's glyph name for a code (Technical Note #5176,
Appendix C); empty for none. -/
public def expertName (code : Nat) : String := GlyphListData.expertNames[code]?.getD ""

/-- The CFF standard strings by name, built once, on the first lookup. -/
public def cffSids : Thunk (Std.HashMap String Nat) := Thunk.mk fun _ =>
  GlyphListData.cffStandardStrings.zipIdx.foldl
    (fun m (n, i) => if m.contains n then m else m.insert n i) {}

/-- A glyph name's CFF standard string identifier, if it has one. -/
public def cffSid? (name : String) : Option Nat := cffSids.get.get? name

/-- The standard Macintosh glyph name a TrueType 'post' table gives index
`i` (0 to 257). -/
public def macGlyphName (i : Nat) : Option String := GlyphListData.macGlyphNames[i]?

/-- A CFF standard string by its identifier. -/
public def cffString? (sid : Nat) : Option String := GlyphListData.cffStandardStrings[sid]?

/-- The CFF string identifier of a StandardEncoding code (Adobe Technical
Note #5176, Appendix B): the standard strings 1–149 are StandardEncoding's
names in code order, so a code's identifier is its rank among the codes
that name a glyph. `none` for an unencoded code. -/
public def standardSid (code : Nat) : Option Nat :=
  if code ≥ 256 || (standardName code).isEmpty then none else
  some (((List.range code).filter fun c => !(standardName c).isEmpty).length + 1)

end LeanTex.Core.GlyphList
