module

public import LeanTex.Core.GlyphListData
public import Std.Data.HashMap
import LeanTex.Core.Hex

/-! Glyph names and the PDF's standard encodings (ISO 32000-2 §9.6.5–9.6.6): codes to names or
scalars, and names to scalars through the Adobe Glyph List, read from `GlyphListData`. -/

namespace LeanTex.Core.GlyphList

/-- The glyph list as a map from name to its scalars, built on first lookup. -/
public def aglMap : Thunk (Std.HashMap String (Array Char)) := Thunk.mk fun _ => Id.run do
  let mut m : Std.HashMap String (Array Char) := {}
  for row in GlyphListData.agl.splitOn "\n" do
    match row.splitOn ";" with
    | [name, scalars] =>
      let cs := (scalars.splitOn " ").filterMap fun h => (Hex.value? h.toList).map Char.ofNat
      unless m.contains name do m := m.insert name cs.toArray
    | _ => pure ()
  return m

/-- Upper-case hexadecimal digits as a number, as a `uni` or `u` name must spell them. -/
private def upperHex (s : List Char) : Option Nat :=
  if s.any Char.isLower then none else Hex.value? s

/-- A scalar a `uni`/`u` name may spell: not a surrogate, inside Unicode. -/
private def scalarOk (v : Nat) : Bool := v < 0xD800 || (0xDFFF < v && v ≤ 0x10FFFF)

/-- One component of a glyph name as scalars: the glyph list's entry, else `uniXXXX…`, else
`uXXXX` to `uXXXXXX`. -/
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

/-- A glyph name's text by the Adobe Glyph List specification; `none` when no component reads. -/
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

/-- The scalar a code means in a base encoding, `none` where it means nothing. -/
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

/-- The CFF standard strings by name, built on first lookup. -/
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

/-- The CFF string identifier of a StandardEncoding code (Technical Note #5176 Appendix B), `none`
for an unencoded code. -/
public def standardSid (code : Nat) : Option Nat :=
  if code ≥ 256 || (standardName code).isEmpty then none else
  some (((List.range code).filter fun c => !(standardName c).isEmpty).length + 1)

end LeanTex.Core.GlyphList
