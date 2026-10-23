module

public import LeanTex.Core.PdfContentLex
public import LeanTex.Core.PdfText
public import LeanTex.Core.Layout

/-! The glyphs each face paints and the ToUnicode CMap the writer embeds for it (ISO 32000-2
§9.10.3): one `bfchar` entry per glyph its pages paint, the glyph's code to the character it was
first painted for. -/

namespace LeanTex.Core.Pdf

open LeanTex.Core LeanTex.Core.Layout LeanTex.Core.Font
open LeanTex.Core.PdfContentLex (Tok)
open LeanTex.Core.PdfRead (Obj)

/-- A drawn figure's glyphs, each with its face and character: its labels, then each symbol's
labels once. -/
@[expose] public def figurePainted (fig : Gfx.Figure Gfx.Shaped) : List (Nat × Nat × Char) :=
  let runs := fig.symbols.foldl (fun acc b => Gfx.Node.labelsList Gfx.Affine.unit acc b.toList)
    (Gfx.Node.labelsList Gfx.Affine.unit #[] fig.nodes.toList)
  runs.toList.flatMap fun (_, r) => r.glyphs.toList.map fun (face, g, c, _) => (face, g, c)

/-- The glyphs a segment paints, each with its face and character: a run's own, and a drawn
figure's, whose text sets in the document's faces. -/
@[expose] public def segPainted (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) :
    Seg → List (Nat × Nat × Char)
  | .run idx _ _ _ glyphs _ _ _ _ _ _ => glyphs.toList.map fun (g, c, _) => (idx, g, c)
  | .image (some k) _ _ _ _ _ => match (shaped[k]?).join with
    | some fig => figurePainted fig
    | none => []
  | .image none .. | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .poly .. => []

/-- Every glyph the pages set, each with its face and character: line by line, a figure's after
its line's earlier runs. -/
@[expose] public def painted (pages : Array PageOut) (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) :
    List (Nat × Nat × Char) :=
  pages.toList.flatMap fun p => p.lines.toList.flatMap fun l => l.segs.toList.flatMap (segPainted shaped)

/-- One painted glyph marked with its character, unless its face's glyph is marked already or out
of range. -/
@[expose] public def markOne (seen : Array (Array (Option Char))) (p : Nat × Nat × Char) :
    Array (Array (Option Char)) :=
  seen.modify p.1 fun marks =>
    if h : p.2.1 < marks.size then
      if marks[p.2.1].isNone then marks.set p.2.1 (some p.2.2) else marks
    else marks

/-- A segment's glyphs marked, in paint order. -/
@[expose] public def markSeg (shaped : Array (Option (Gfx.Figure Gfx.Shaped)))
    (seen : Array (Array (Option Char))) : Seg → Array (Array (Option Char))
  | .run idx _ _ _ glyphs _ _ _ _ _ _ => glyphs.foldl (fun seen (g, c, _) => markOne seen (idx, g, c)) seen
  | .image (some k) _ _ _ _ _ => match (shaped[k]?).join with
    | some fig => (figurePainted fig).foldl markOne seen
    | none => seen
  | .image none .. | .gap .. | .decoratedGap .. | .decoration .. | .rule .. | .poly .. => seen

/-- Each face's glyphs marked with the character each was first painted for. -/
@[expose] public def markUsed (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) : Array (Array (Option Char)) :=
  pages.foldl (fun seen p => p.lines.foldl (fun seen l => l.segs.foldl (markSeg shaped) seen) seen)
    (fs.fonts.map fun f => Array.replicate f.numGlyphs none)

/-- Used glyphs per face, one char witness per gid in ascending order: the census embedding reads. -/
@[expose] public def usedAll (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped)) := #[]) : Array (Array (Nat × Char)) :=
  let seen := markUsed fs pages shaped
  (Array.range fs.fonts.size).map fun k =>
    ((seen[k]?.getD #[]).zipIdx.filterMap fun (c?, g) => c?.map (g, ·))

public theorem usedAll_size_exact (fs : FontSet) (pages : Array PageOut)
    (shaped : Array (Option (Gfx.Figure Gfx.Shaped))) :
    (usedAll fs pages shaped).size = fs.fonts.size := by
  simp [usedAll]

/-- Hexadecimal digits as a hex string. -/
@[expose] public def hexObj (digits : String) : Obj :=
  PdfRead.strOf (60 :: digits.toList.map Char.toNat ++ [62])

/-- A list cut into runs of `n`, at least one, the last possibly shorter. -/
@[expose] public def chunksOf {α : Type} (n : Nat) : List α → List (List α)
  | [] => []
  | x :: xs => (x :: xs).take (max n 1) :: chunksOf n ((x :: xs).drop (max n 1))
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-- The CMap's header: its resource, system information, name, type and one two-byte codespace. -/
@[expose] public def cmapHead : List (Tok × UInt8) :=
  [(.val (.name "CIDInit"), 32), (.val (.name "ProcSet"), 32), (.op "findresource", 32),
   (.op "begin", 10), (.val (.int 12), 32), (.op "dict", 32), (.op "begin", 10),
   (.op "begincmap", 10),
   (.val (.name "CIDSystemInfo"), 32),
   (.val (.dict #[("Registry", PdfRead.literal "Adobe".toUTF8),
     ("Ordering", PdfRead.literal "UCS".toUTF8), ("Supplement", .int 0)]), 32), (.op "def", 10),
   (.val (.name "CMapName"), 32), (.val (.name "Adobe-Identity-UCS"), 32), (.op "def", 10),
   (.val (.name "CMapType"), 32), (.val (.int 2), 32), (.op "def", 10),
   (.val (.int 1), 32), (.op "begincodespacerange", 10),
   (.val (hexObj "0000"), 32), (.val (hexObj "FFFF"), 10), (.op "endcodespacerange", 10)]

/-- The CMap's trailer, defining the resource. -/
@[expose] public def cmapTail : List (Tok × UInt8) :=
  [(.op "endcmap", 10), (.op "CMapName", 32), (.op "currentdict", 32), (.val (.name "CMap"), 32),
   (.op "defineresource", 32), (.op "pop", 10), (.op "end", 10), (.op "end", 10)]

/-- One glyph's code and its character's UTF-16BE units, a line each. -/
@[expose] public def bfcharPair (p : Nat × Char) : List (Tok × UInt8) :=
  [(.val (hexObj (Hex.digits true 4 p.1)), 32), (.val (hexObj (PdfRead.utf16Hex p.2)), 10)]

/-- One `bfchar` section. -/
@[expose] public def bfcharSection (chunk : List (Nat × Char)) : List (Tok × UInt8) :=
  [(.val (.int chunk.length), 32), (.op "beginbfchar", 10)] ++ chunk.flatMap bfcharPair ++
    [(.op "endbfchar", 10)]

/-- The CMap's tokens, each followed by its separator: the glyphs in sections of a hundred, the
most a section may hold (§9.7.5.3). -/
@[expose] public def cmapToks (used : List (Nat × Char)) : List (Tok × UInt8) :=
  cmapHead ++ (chunksOf 100 used).flatMap bfcharSection ++ cmapTail

/-- The ToUnicode CMap for a face's painted glyphs, each glyph with the character it was first
painted for. -/
public def toUnicodeCMap (used : Array (Nat × Char)) : ByteArray :=
  PdfContentLex.renderSep false (cmapToks used.toList)

/-- The ToUnicode CMap the file embeds for face `k`, from every face's used glyphs. -/
@[expose] public def faceCMap (used : Array (Array (Nat × Char))) (k : Nat) : ByteArray :=
  toUnicodeCMap (used[k]?.getD #[])

end LeanTex.Core.Pdf
