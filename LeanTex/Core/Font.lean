module

public import LeanTex.Core.Ink
public import LeanTex.Core.Math

namespace LeanTex.Core.Font

open LeanTex.Core.Ink

/-- The OpenType `MATH` table's MathConstants the engine reads, in font design units. -/
public structure MathConsts where
  scales : Math.ScriptScales
  axisHeight : Int
  /-- The height an accent is designed to sit at (TeXbook Appendix G rule 12). -/
  accentBaseHeight : Int
  subscriptShiftDown : Int
  superscriptShiftUp : Int
  superscriptShiftUpCramped : Int
  /-- TeX's rules 18c and 18a for a superscript, in OpenType's names. -/
  superscriptBottomMin : Int
  superscriptBaselineDropMax : Int
  spaceAfterScript : Int
  displayOperatorMinHeight : Int
  upperLimitGapMin : Int
  upperLimitBaselineRiseMin : Int
  lowerLimitGapMin : Int
  lowerLimitBaselineDropMin : Int
  /-- The stack constants place a rule-less fraction's parts (TeXbook Appendix G rule 15). -/
  stackTopShiftUp : Int
  stackTopDisplayStyleShiftUp : Int
  stackBottomShiftDown : Int
  stackBottomDisplayStyleShiftDown : Int
  stackGapMin : Int
  stackDisplayStyleGapMin : Int
  fractionNumeratorShiftUp : Int
  fractionNumeratorDisplayStyleShiftUp : Int
  fractionDenominatorShiftDown : Int
  fractionDenominatorDisplayStyleShiftDown : Int
  fractionNumeratorGapMin : Int
  fractionNumDisplayStyleGapMin : Int
  fractionRuleThickness : Int
  fractionDenominatorGapMin : Int
  fractionDenomDisplayStyleGapMin : Int
  /-- The overbar constants position `\overline`'s rule (TeXbook Appendix G rule 9). -/
  overbarVerticalGap : Int
  overbarRuleThickness : Int
  overbarExtraAscender : Int
  radicalVerticalGap : Int
  radicalDisplayStyleVerticalGap : Int
  radicalRuleThickness : Int
  radicalExtraAscender : Int
  radicalKernBeforeDegree : Int
  radicalKernAfterDegree : Int
  radicalDegreeBottomRaisePercent : Int
  deriving Repr, BEq, Inhabited

/-- The MathConstants of a `MATH` table, or `none` when the face has no readable table. -/
private def parseMath (b : ByteArray) : Option MathConsts := do
  let t ← findTable b "MATH"
  unless fits b t do failure
  unless t.length ≥ 10 do failure
  let cOff := t.offset + u16 b (t.offset + 4)
  unless cOff + 214 ≤ b.size do failure
  let value (rec : Nat) : Int := i16 b (cOff + rec)
  return {
    scales := Math.ScriptScales.clamp (value 0) (value 2)
    axisHeight := value 12
    accentBaseHeight := value 16
    subscriptShiftDown := value 24
    superscriptShiftUp := value 36
    superscriptShiftUpCramped := value 40
    superscriptBottomMin := value 44
    superscriptBaselineDropMax := value 48
    spaceAfterScript := value 60
    displayOperatorMinHeight := u16 b (cOff + 6)
    upperLimitGapMin := value 64
    upperLimitBaselineRiseMin := value 68
    lowerLimitGapMin := value 72
    lowerLimitBaselineDropMin := value 76
    stackTopShiftUp := value 80
    stackTopDisplayStyleShiftUp := value 84
    stackBottomShiftDown := value 88
    stackBottomDisplayStyleShiftDown := value 92
    stackGapMin := value 96
    stackDisplayStyleGapMin := value 100
    fractionNumeratorShiftUp := value 120
    fractionNumeratorDisplayStyleShiftUp := value 124
    fractionDenominatorShiftDown := value 128
    fractionDenominatorDisplayStyleShiftDown := value 132
    fractionNumeratorGapMin := value 136
    fractionNumDisplayStyleGapMin := value 140
    fractionRuleThickness := value 144
    fractionDenominatorGapMin := value 148
    fractionDenomDisplayStyleGapMin := value 152
    overbarVerticalGap := value 164
    overbarRuleThickness := value 168
    overbarExtraAscender := value 172
    radicalVerticalGap := value 188
    radicalDisplayStyleVerticalGap := value 192
    radicalRuleThickness := value 196
    radicalExtraAscender := value 200
    radicalKernBeforeDegree := value 204
    radicalKernAfterDegree := value 208
    radicalDegreeBottomRaisePercent := value 212
  }

/-- A coverage table's glyph list (formats 1 and 2), in coverage order. -/
private def parseCoverage (b : ByteArray) (off : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  match u16 b off with
  | 1 =>
    let n := u16 b (off + 2)
    for i in [0:n] do
      out := out.push (u16 b (off + 4 + 2 * i))
  | 2 =>
    let n := u16 b (off + 2)
    for i in [0:n] do
      -- No coverage lists more glyphs than the 16-bit glyph space holds.
      if out.size ≥ 0x10000 then break
      let s := u16 b (off + 4 + 6 * i)
      let e := u16 b (off + 6 + 6 * i)
      -- Bounded: a malformed range never expands past the glyph space.
      for g in [s : min (e + 1) 0x10000] do
        out := out.push g
  | _ => pure ()
  return out

/-- A `MATH` table's glyph variants per base glyph, `(glyph id, advance)` in increasing size:
heights, or widths when `horiz`. -/
private def parseVariants (horiz : Bool) (b : ByteArray) :
    Array (Nat × Array (Nat × Int)) := Id.run do
  let some t := findTable b "MATH" | return #[]
  unless fits b t && t.length ≥ 10 do return #[]
  let mv := t.offset + u16 b (t.offset + 8)
  unless mv + 10 ≤ b.size do return #[]
  let covOff := u16 b (mv + (if horiz then 4 else 2))
  unless covOff > 0 do return #[]
  let covered := parseCoverage b (mv + covOff)
  let vertCount := u16 b (mv + 6)
  let count := if horiz then u16 b (mv + 8) else vertCount
  let base := if horiz then mv + 10 + 2 * vertCount else mv + 10
  let mut out : Array (Nat × Array (Nat × Int)) := #[]
  for i in [0:min count covered.size] do
    let some cov := covered[i]? | break
    let cons := mv + u16 b (base + 2 * i)
    let n := u16 b (cons + 2)
    let mut vs : Array (Nat × Int) := #[]
    for k in [0:n] do
      vs := vs.push (u16 b (cons + 4 + 4 * k), (u16 b (cons + 6 + 4 * k) : Int))
    out := out.push (cov, vs)
  return out

/-- The MathTopAccentAttachment positions per covered glyph, in design units from the origin. -/
private def parseTopAccent (b : ByteArray) : Array (Nat × Int) := Id.run do
  let some t := findTable b "MATH" | return #[]
  unless fits b t && t.length ≥ 10 do return #[]
  let giOff := u16 b (t.offset + 6)
  unless giOff > 0 do return #[]
  let gi := t.offset + giOff
  unless gi + 8 ≤ b.size do return #[]
  let taOff := u16 b (gi + 2)
  unless taOff > 0 do return #[]
  let ta := gi + taOff
  unless ta + 4 ≤ b.size do return #[]
  let covered := parseCoverage b (ta + u16 b ta)
  let count := u16 b (ta + 2)
  let mut out : Array (Nat × Int) := #[]
  for i in [0:min count covered.size] do
    let some cov := covered[i]? | break
    out := out.push (cov, i16 b (ta + 4 + 4 * i))
  return out

/-- A stable sort by a `Nat` key in worst-case `n·log n`, for tables a file claims. -/
private def sortByKey (xs : Array α) (key : α → Nat) : Array α :=
  (xs.toList.mergeSort fun x y => key x ≤ key y).toArray

/-- A 4-byte OpenType tag as a string, for script and feature records. -/
private def tag4 (b : ByteArray) (off : Nat) : String :=
  String.ofList ((b.extract off (off + 4)).toList.map fun v => Char.ofNat v.toNat)

/-- Exact-key binary search over `xs`, sorted ascending by `key` without duplicates. -/
def bsearch (xs : Array α) (key : α → Nat) (k : Nat) : Option (Nat × α) :=
  go 0 xs.size
where
  go (lo hi : Nat) : Option (Nat × α) :=
    if _h : lo < hi then
      if let some x := xs[(lo + hi) / 2]? then
        if k < key x then go lo ((lo + hi) / 2)
        else if k > key x then go ((lo + hi) / 2 + 1) hi
        else some ((lo + hi) / 2, x)
      else none
    else none
  termination_by hi - lo
  decreasing_by all_goals omega

theorem bsearch_mem (xs : Array α) (key : α → Nat) (k i : Nat) (x : α)
    (h : bsearch xs key k = some (i, x)) : xs[i]? = some x ∧ key x = k := by
  unfold bsearch at h
  revert h
  fun_induction bsearch.go xs key k 0 xs.size
  all_goals intro h
  all_goals first
    | (rename_i ih; exact ih h)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       rename_i hx hklt hkgt
       exact ⟨hx, by omega⟩)
    | simp at h

/-- The image of `g` under a gid→gid map sorted by source gid, or `g` when not covered. -/
def substGid (map : Array (Nat × Nat)) (g : Nat) : Nat :=
  match bsearch map (·.1) g with
  | some (_, _, dst) => dst
  | none => g

/-- The lookup indices one GSUB feature tag selects for `latn`, else `DFLT`, in the default
language system. -/
private def gsubFeatureLookups (b : ByteArray) (scriptList featList : Nat)
    (tag : String) : Array Nat := Id.run do
  let nScripts := u16 b scriptList
  let mut latn : Option Nat := none
  let mut dflt : Option Nat := none
  for i in [0:nScripts] do
    let r := scriptList + 2 + 6 * i
    let off := u16 b (r + 4)
    if off != 0 then
      if tag4 b r == "latn" then latn := some (scriptList + off)
      else if tag4 b r == "DFLT" then dflt := some (scriptList + off)
  let some script := latn <|> dflt | return #[]
  let dls := u16 b script
  if dls == 0 then return #[]
  let ls := script + dls
  let featCount := u16 b (ls + 4)
  let nFeat := u16 b featList
  let mut lookups : Array Nat := #[]
  for k in [0:featCount] do
    let fi := u16 b (ls + 6 + 2 * k)
    if fi < nFeat then
      let r := featList + 2 + 6 * fi
      if tag4 b r == tag then
        let fo := featList + u16 b (r + 4)
        let n := u16 b (fo + 2)
        for j in [0:n] do
          lookups := lookups.push (u16 b (fo + 4 + 2 * j))
  return lookups

/-- One GSUB single-substitution lookup as a gid→gid map sorted by source gid; other lookup
types read as empty. -/
private def singleSubMap (b : ByteArray) (lookupList lookupIdx : Nat) :
    Array (Nat × Nat) := Id.run do
  unless lookupIdx < u16 b lookupList do return #[]
  let lo := lookupList + u16 b (lookupList + 2 + 2 * lookupIdx)
  unless u16 b lo == 1 do return #[]
  let nSub := u16 b (lo + 4)
  let mut out : Array (Nat × Nat) := #[]
  for s in [0:nSub] do
    let so := lo + u16 b (lo + 6 + 2 * s)
    let cov := parseCoverage b (so + u16 b (so + 2))
    match u16 b so with
    | 1 =>
      let delta := u16 b (so + 4)
      for g in cov do
        out := out.push (g, (g + delta) % 0x10000)
    | 2 =>
      let n := u16 b (so + 4)
      for (g, i) in cov.zipIdx do
        if i < n then
          out := out.push (g, u16 b (so + 6 + 2 * i))
    | _ => pure ()
  return sortByKey out (·.1)

/-- Whether GSUB carries `smcp` and `c2sc`, and their composed map, built only when both are
present. -/
private def parseGsubSmallCaps (b : ByteArray) : Bool × Bool × Array (Nat × Nat) := Id.run do
  let some t := findTable b "GSUB" | return (false, false, #[])
  unless fits b t && t.length ≥ 10 do return (false, false, #[])
  let g := t.offset
  let scriptList := g + u16 b (g + 4)
  let featList := g + u16 b (g + 6)
  let lookupList := g + u16 b (g + 8)
  let smcpLookups := gsubFeatureLookups b scriptList featList "smcp"
  let c2scLookups := gsubFeatureLookups b scriptList featList "c2sc"
  let hasSmcp := !smcpLookups.isEmpty
  let hasC2sc := !c2scLookups.isEmpty
  unless hasSmcp && hasC2sc do return (hasSmcp, hasC2sc, #[])
  let dedup (xs : Array Nat) : Array Nat :=
    (sortByKey xs id).foldl
      (fun acc i => if acc.back? == some i then acc else acc.push i) #[]
  let lookups := dedup (smcpLookups ++ c2scLookups)
  let maps := lookups.map (singleSubMap b lookupList)
  let mut dom : Array Nat := #[]
  for m in maps do
    for (src, _) in m do
      dom := dom.push src
  let mut out : Array (Nat × Nat) := #[]
  for gid in dedup dom do
    let cur := maps.foldl (fun cur m => substGid m cur) gid
    if cur != gid then
      out := out.push (gid, cur)
  return (hasSmcp, hasC2sc, out)

/-- A ClassDef table as `(gid, class)` pairs sorted by gid; an unlisted glyph is class 0. -/
private def parseClassDef (b : ByteArray) (off : Nat) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  match u16 b off with
  | 1 =>
    let start := u16 b (off + 2)
    let n := u16 b (off + 4)
    for i in [0:n] do
      out := out.push (start + i, u16 b (off + 6 + 2 * i))
  | 2 =>
    let n := u16 b (off + 2)
    for i in [0:n] do
      -- No class table lists more glyphs than the 16-bit glyph space holds.
      if out.size ≥ 0x10000 then break
      let s := u16 b (off + 4 + 6 * i)
      let e := u16 b (off + 6 + 6 * i)
      let cls := u16 b (off + 8 + 6 * i)
      -- Bounded: a malformed range never expands past the glyph space.
      for g in [s : min (e + 1) 0x10000] do
        out := out.push (g, cls)
  | _ => pure ()
  return sortByKey out (·.1)

/-- Binary search over sorted `(gid, v)` pairs: the value, or `none`. -/
private def sortedFind (pairs : Array (Nat × Nat)) (g : Nat) : Option Nat :=
  (bsearch pairs (·.1) g).map (·.2.2)

/-- A GPOS ValueRecord's size in bytes under a value format, and its XAdvance offset. -/
private def valueRecord (vf : Nat) : Nat × Option Nat :=
  let bits (n : Nat) : Nat := (List.range 16).foldl
    (fun acc i => acc + (n >>> i) % 2) 0
  (2 * bits (vf % 0x10000),
   if vf % 8 ≥ 4 then some (2 * bits (vf % 4)) else none)

/-- One GPOS PairPos subtable's skeleton; its value matrix stays in the font bytes. -/
public structure KernSub where
  private fmt : Nat
  private off : Nat
  /-- Coverage gids in coverage order (ascending): index = coverage index. -/
  private cov : Array Nat
  private size1 : Nat
  private size2 : Nat
  /-- Byte offset of XAdvance inside the first value record. -/
  private xAdv : Nat
  private cd1 : Array (Nat × Nat) := #[]
  private cd2 : Array (Nat × Nat) := #[]
  private c1Count : Nat := 0
  private c2Count : Nat := 0
  deriving Inhabited

/-- The PairPos subtables of GPOS `kern` for `latn`/`DFLT`, formats 1 and 2, the first glyph's
XAdvance only, read through one extension hop. -/
private def parseKernSubs (b : ByteArray) : Array KernSub := Id.run do
  let some t := findTable b "GPOS" | return #[]
  unless fits b t && t.length ≥ 10 do return #[]
  let g := t.offset
  let scriptList := g + u16 b (g + 4)
  let featList := g + u16 b (g + 6)
  let lookupList := g + u16 b (g + 8)
  let lookups := gsubFeatureLookups b scriptList featList "kern"
  let mut out : Array KernSub := #[]
  for li in lookups do
    if li ≥ u16 b lookupList then continue
    let lo := lookupList + u16 b (lookupList + 2 + 2 * li)
    let ty := u16 b lo
    unless ty == 2 || ty == 9 do continue
    let nSub := u16 b (lo + 4)
    for s in [0:nSub] do
      let so0 := lo + u16 b (lo + 6 + 2 * s)
      if ty == 9 && !(u16 b so0 == 1 && u16 b (so0 + 2) == 2) then continue
      let so := if ty == 9 then so0 + u32 b (so0 + 4) else so0
      let fmt := u16 b so
      unless fmt == 1 || fmt == 2 do continue
      let cov := parseCoverage b (so + u16 b (so + 2))
      let (size1, xa1) := valueRecord (u16 b (so + 4))
      let (size2, _) := valueRecord (u16 b (so + 6))
      let some xAdv := xa1 | continue
      if fmt == 1 then
        out := out.push { fmt, off := so, cov, size1, size2, xAdv }
      else
        out := out.push { fmt, off := so, cov, size1, size2, xAdv
                          cd1 := parseClassDef b (so + u16 b (so + 8))
                          cd2 := parseClassDef b (so + u16 b (so + 10))
                          c1Count := u16 b (so + 12)
                          c2Count := u16 b (so + 14) }
  return out

/-- The coverage index of `g` (coverage arrays are ascending). -/
private def covIndex (cov : Array Nat) (g : Nat) : Option Nat :=
  (bsearch cov id g).map (·.1)

/-- The legacy `kern` table's format 0 horizontal pairs, sorted by `g1 * 0x10000 + g2`. -/
private def parseLegacyKern (b : ByteArray) : Array (Nat × Int) := Id.run do
  let some t := findTable b "kern" | return #[]
  unless fits b t && t.length ≥ 4 do return #[]
  let k := t.offset
  let nTables := u16 b (k + 2)
  let mut off := k + 4
  let mut out : Array (Nat × Int) := #[]
  for _ in [0:nTables] do
    let len := u16 b (off + 2)
    let cov := u16 b (off + 4)
    -- horizontal (bit 0), format 0 (high byte), not cross-stream
    if cov % 2 == 1 && cov / 256 == 0 && cov % 8 < 4 then
      let n := u16 b (off + 6)
      for i in [0:n] do
        let r := off + 14 + 6 * i
        let v := i16 b (r + 4)
        if v != 0 then
          out := out.push (u16 b r * 0x10000 + u16 b (r + 2), v)
    off := off + max len 6
  return (sortByKey out (·.1)).foldl
    (fun acc p => if acc.back?.map (·.1) == some p.1 then acc else acc.push p) #[]

/-- The pair kern between glyphs `g1` and `g2` from a face's parsed kern data. -/
private def pairAdv (b : ByteArray) (kd : Array KernSub × Array (Nat × Int)) (g1 g2 : Nat) :
    Int := Id.run do
  let (subs, pairs) := kd
  for sub in subs do
    match covIndex sub.cov g1 with
    | none => pure ()
    | some ci =>
      if sub.fmt == 1 then
        if ci < u16 b (sub.off + 8) then
          let ps := sub.off + u16 b (sub.off + 10 + 2 * ci)
          let n := u16 b ps
          let rec2 := 2 + sub.size1 + sub.size2
          for k in [0:n] do
            let r := ps + 2 + rec2 * k
            if u16 b r == g2 then
              return i16 b (r + 2 + sub.xAdv)
      else
        let c1 := (sortedFind sub.cd1 g1).getD 0
        let c2 := (sortedFind sub.cd2 g2).getD 0
        if c1 < sub.c1Count && c2 < sub.c2Count then
          let r := sub.off + 16 + (sub.size1 + sub.size2) * (c1 * sub.c2Count + c2)
          let v := i16 b (r + sub.xAdv)
          if v != 0 then
            return v
  match bsearch pairs (·.1) (g1 * 0x10000 + g2) with
  | some (_, _, v) => return v
  | none => return 0

/-- A demand-lazy memo tree of a face's `(glyph, space)` and `(space, glyph)` kern pairs. -/
inductive SpaceKernTree where
  | leaf (pair : Int × Int)
  | branch (split : Nat) (left right : Thunk SpaceKernTree)
  deriving Inhabited

/-- The bounded index around a space-kern memo tree; a hit visits `depth + 1` nodes. -/
public structure SpaceKernCache where
  size : Nat
  private space : Nat
  depth : Nat
  private root : Thunk SpaceKernTree
  deriving Inhabited

/-- Tree depth for `numGlyphs` leaves, at most 16 for an sfnt. -/
public def spaceKernDepth (numGlyphs : Nat) : Nat :=
  if numGlyphs == 0 then 0 else Nat.log2 numGlyphs + 1

private def makeSpaceKernTree (data : ByteArray)
    (kd : Array KernSub × Array (Nat × Int)) (space base span : Nat) :
    (depth : Nat) → Thunk SpaceKernTree
  | 0 => Thunk.mk fun _ => .leaf (pairAdv data kd base space, pairAdv data kd space base)
  | depth + 1 => Thunk.mk fun _ =>
    let half := span / 2
    .branch half
      (makeSpaceKernTree data kd space base half depth)
      (makeSpaceKernTree data kd space (base + half) half depth)

private def spaceKernLookup : Nat → Thunk SpaceKernTree → Nat → (Int × Int) × Nat
  | 0, tree, _ =>
    match tree.get with
    | .leaf pair => (pair, 1)
    | .branch _ _ _ => ((0, 0), 1)
  | depth + 1, tree, g =>
    match tree.get with
    | .leaf pair => (pair, 1)
    | .branch split left right =>
      let hit := if g < split then spaceKernLookup depth left g
        else spaceKernLookup depth right (g - split)
      (hit.1, hit.2 + 1)

/-- A cached pair and the memo-tree nodes visited, or `none` for a gid outside the face. -/
public def SpaceKernCache.lookup? (cache : SpaceKernCache) (g : Nat) :
    Option ((Int × Int) × Nat) :=
  if g < cache.size then some (spaceKernLookup cache.depth cache.root g) else none

/-- A parsed sfnt font: the layout metrics, the char→glyph map, and the raw bytes to embed. -/
public structure _root_.LeanTex.Core.Font where
  data : ByteArray
  isCff : Bool
  unitsPerEm : Nat
  ascent : Int
  descent : Int
  lineGap : Int
  psName : String
  family : String
  subfamily : String
  isBold : Bool
  isItalic : Bool
  isFixedPitch : Bool
  weight : Nat
  /-- OS/2 sFamilyClass's class ID (high byte), 0 when the face declares none. -/
  familyClass : Nat := 0
  /-- OS/2 fsType embedding-licensing bits, as declared. -/
  fsType : Nat := 0
  xHeight : Int
  /-- OS/2 sCapHeight, the height a line of text measures from its glyphs. -/
  capHeight : Int
  cmap : Array (UInt32 × UInt32 × UInt32)  -- (startChar, endChar, startGid), sorted
  widths : Array Nat                        -- advance width per gid, font units
  numGlyphs : Nat
  /-- `post` underline metrics in font units; zero when the font declares none. -/
  underlinePosition : Int
  underlineThickness : Int
  /-- `post` italicAngle in whole degrees, negative for a right-leaning italic; zero when none. -/
  italicAngle : Int
  /-- Per gid, lazily: the merged x-intervals of ink inside the underline band, in font units. -/
  underlineInk : Thunk (Array (Thunk (Array (Int × Int))))
  /-- The `MATH` constants, when the face carries the table. -/
  math : Option MathConsts
  /-- The `MATH` table's vertical glyph variants per base glyph; empty when none. -/
  mathVariants : Array (Nat × Array (Nat × Int))
  /-- The `MATH` table's horizontal glyph variants per base glyph; empty when none. -/
  mathHorizVariants : Array (Nat × Array (Nat × Int))
  /-- The `MATH` table's top-accent attachment positions, in design units from the origin. -/
  mathTopAccent : Array (Nat × Int)
  /-- Per gid, lazily: the glyph's control-point ink hull in font units; `none` if undecodable. -/
  inkExtent : Thunk (Array (Thunk (Option Ink.Bounds)))
  /-- The face's outline source, prepared once and lazily, shared by ink decoding and subsets. -/
  inkSrc : Thunk Ink.Src
  /-- Lazily: the ink top of the face's own 'x' in font units; `none` when undecodable. -/
  xInkTop : Thunk (Option Int)
  /-- GSUB carries `smcp` (lowercase to small capitals) for `latn`/`DFLT`. -/
  hasSmcp : Bool
  /-- GSUB carries `c2sc` (capitals to small capitals) for `latn`/`DFLT`. -/
  hasC2sc : Bool
  /-- The composed `smcp`+`c2sc` substitution sorted by source gid; empty unless both exist. -/
  smallCaps : Array (Nat × Nat)
  /-- Pair kerning, lazily: GPOS `kern` subtables, and legacy `kern` pairs when GPOS has none. -/
  kernData : Thunk (Array KernSub × Array (Nat × Int))
  /-- Each glyph's kerns with the space glyph, `(kern (g, space), kern (space, g))`, memoized. -/
  spaceKerns : Thunk (Option SpaceKernCache)
  deriving Inhabited

private def parseCmap4 (b : ByteArray) (off : Nat) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  let segX2 := u16 b (off + 6)
  let seg := segX2 / 2
  let endBase := off + 14
  let startBase := endBase + segX2 + 2
  let deltaBase := startBase + segX2
  let rangeBase := deltaBase + segX2
  let mut out : Array (UInt32 × UInt32 × UInt32) := #[]
  for k in [0:seg] do
    let endC := u16 b (endBase + 2 * k)
    let startC := u16 b (startBase + 2 * k)
    let delta := u16 b (deltaBase + 2 * k)
    let rangeOff := u16 b (rangeBase + 2 * k)
    if startC == 0xFFFF then
      continue
    if rangeOff == 0 then
      let gid := (startC + delta) % 0x10000
      out := out.push (UInt32.ofNat startC, UInt32.ofNat endC, UInt32.ofNat gid)
    else
      for c in [startC:endC+1] do
        let idx := rangeBase + 2 * k + rangeOff + 2 * (c - startC)
        if idx + 1 < b.size then
          let g := u16 b idx
          if g != 0 then
            let gid := (g + delta) % 0x10000
            out := out.push (UInt32.ofNat c, UInt32.ofNat c, UInt32.ofNat gid)
  return out

private def parseCmap12 (b : ByteArray) (off : Nat) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  -- Clamp the file's group count by the bytes actually present.
  let n := min (u32 b (off + 12)) ((b.size - off) / 12)
  let mut out : Array (UInt32 × UInt32 × UInt32) := #[]
  for k in [0:n] do
    let g := off + 16 + 12 * k
    out := out.push (UInt32.ofNat (u32 b g), UInt32.ofNat (u32 b (g + 4)),
      UInt32.ofNat (u32 b (g + 8)))
  return out

private def parseCmap (b : ByteArray) (t : Table) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  let n := u16 b (t.offset + 2)
  let mut best4 : Option Nat := none
  let mut best12 : Option Nat := none
  for k in [0:n] do
    let entry := t.offset + 4 + 8 * k
    let platform := u16 b entry
    let encoding := u16 b (entry + 2)
    let sub := t.offset + u32 b (entry + 4)
    let unicodeish := platform == 0 || (platform == 3 && (encoding == 1 || encoding == 10))
    if unicodeish && sub + 2 ≤ b.size then
      match u16 b sub with
      | 4 => best4 := best4 <|> some sub
      | 12 => best12 := best12 <|> some sub
      | _ => pure ()
  match best12 with
  | some off => return parseCmap12 b off
  | none =>
    match best4 with
    | some off => return parseCmap4 b off
    | none => return #[]

/-- Read one `name` table record, preferring the typographic name (id 16/17) over id 1/2. -/
private def parseNameId (b : ByteArray) (t : Table) (wanted : Nat) : Option String := Id.run do
  let n := u16 b (t.offset + 2)
  let strBase := t.offset + u16 b (t.offset + 4)
  let mut best : Option String := none
  for k in [0:n] do
    let entry := t.offset + 6 + 12 * k
    if u16 b (entry + 6) == wanted then
      let len := u16 b (entry + 8)
      let off := strBase + u16 b (entry + 10)
      let platform := u16 b entry
      if off + len ≤ b.size then
        let s :=
          if platform == 1 then
            String.ofList ((b.extract off (off + len)).toList.map fun c => Char.ofNat c.toNat)
          else Id.run do
            -- UTF-16BE; font names here are effectively Latin-1
            let mut acc := ""
            for j in [0:len / 2] do
              let cp := u16 b (off + 2 * j)
              if cp != 0 then
                acc := acc.push (Char.ofNat cp)
            return acc
        if best.isNone then
          best := some s
  return best

private def nameOf (b : ByteArray) (t : Option Table) (ids : List Nat)
    (fallback : String) : String :=
  match t with
  | none => fallback
  | some tbl =>
    match ids.findSome? (parseNameId b tbl) with
    | some s => if s.isEmpty then fallback else s
    | none => fallback

/-- A face's identity and style, from its metadata tables only. -/
public structure Class where
  psName : String
  family : String
  subfamily : String
  isBold : Bool
  isItalic : Bool
  isFixedPitch : Bool
  weight : Nat
  deriving Repr, Inhabited

/-- Classify a face from `head`, refined by `name`, `OS/2` and `post`. -/
public def classify (data : ByteArray) : Except String Class := do
  if data.size < 12 then
    throw "not a font file"
  let tag := u32 data 0
  if tag != 0x4F54544F && tag != 0x00010000 then
    throw "unsupported font format (need TrueType or CFF OpenType)"
  let some head := findTable data "head" | throw "font has no 'head' table"
  unless fits data head do
    throw "font table 'head' extends past the end of the file"
  let nameT := findTable data "name"
  let psName := nameOf data nameT [6] "Embedded"
  let family := nameOf data nameT [16, 1] psName
  let subfamily := nameOf data nameT [17, 2] "Regular"
  let lowerSub := subfamily.toLower
  -- OS/2 fsSelection is authoritative; the subfamily string is the fallback.
  let fsSelection := match findTable data "OS/2" with
    | some t => if t.offset + 64 ≤ data.size then some (u16 data (t.offset + 62)) else none
    | none => none
  let macStyle := u16 data (head.offset + 44)
  let isBold := match fsSelection with
    | some fs => fs % 64 ≥ 32 || macStyle % 2 == 1
    | none => (lowerSub.splitOn "bold").length > 1 || macStyle % 2 == 1
  let isItalic := match fsSelection with
    | some fs => fs % 2 == 1 || macStyle / 2 % 2 == 1
    | none =>
      (lowerSub.splitOn "italic").length > 1 || (lowerSub.splitOn "oblique").length > 1
        || macStyle / 2 % 2 == 1
  -- `post` isFixedPitch is at offset 12, after version, italicAngle and the underline metrics.
  let isFixedPitch := match findTable data "post" with
    | some t => if t.offset + 16 ≤ data.size then u32 data (t.offset + 12) != 0 else false
    | none => false
  -- OS/2 usWeightClass (100–900), not the BOLD bit, decides the weight.
  let weight := match findTable data "OS/2" with
    | some t =>
      if t.offset + 6 ≤ data.size then
        let w := u16 data (t.offset + 4)
        if w == 0 then (if isBold then 700 else 400) else w
      else if isBold then 700 else 400
    | none => if isBold then 700 else 400
  return { psName, family, subfamily, isBold, isItalic, isFixedPitch, weight }

/-- The version of `classify`'s answer, moved whenever the answer changes for some bytes. -/
public def classifierVersion : Nat := 2

/-- The number of faces a font collection holds, when `data` is one whose offsets it holds. -/
public def collectionCount (data : ByteArray) : Option Nat :=
  let n := u32 data 8
  if 12 ≤ data.size && u32 data 0 == 0x74746366 && 0 < n && n ≤ 4096 &&
      12 + 4 * n ≤ data.size then some n else none

private def pushU16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v / 256 % 256).toUInt8).push (v % 256).toUInt8

private def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  pushU16 (pushU16 b (v / 65536 % 65536)) (v % 65536)

/-- Round up to the four-byte boundary a table starts on. -/
private def pad4 (n : Nat) : Nat := (n + 3) / 4 * 4

/-- A standalone font file of the given tables, each at its four-byte boundary. -/
public def assembleSfnt (version : Nat) (tables : Array (Nat × Nat × ByteArray)) : ByteArray := Id.run do
  let n := tables.size
  let mut pow := 1
  let mut log := 0
  for _ in [0:16] do
    if pow * 2 ≤ n then
      pow := pow * 2
      log := log + 1
  let mut out := pushU32 ByteArray.empty version
  out := pushU16 (pushU16 (pushU16 (pushU16 out n) (pow * 16)) log) (n * 16 - pow * 16)
  let mut next := 12 + 16 * n
  for (tag, sum, bytes) in tables do
    out := pushU32 (pushU32 (pushU32 (pushU32 out tag) sum) next) bytes.size
    next := pad4 (next + bytes.size)
  for (_, _, bytes) in tables do
    out := out ++ bytes
    for _ in [0:pad4 bytes.size - bytes.size] do
      out := out.push 0
  return out

/-- Face `index` of a font collection as a standalone font file, or an error naming what is
malformed. -/
public def collectionMember (data : ByteArray) (index : Nat) : Except String ByteArray := do
  let some count := collectionCount data | throw "not a font collection"
  unless index < count do
    throw s!"the collection holds {count} faces, so it has no face {index}"
  let base := u32 data (12 + 4 * index)
  let numTables := u16 data (base + 4)
  unless 0 < numTables && numTables ≤ 512 && base + 12 + 16 * numTables ≤ data.size do
    throw s!"face {index} of the collection has no readable table directory"
  let mut tables : Array (Nat × Nat × ByteArray) := #[]
  let mut total := 0
  for k in [0:numTables] do
    let entry := base + 12 + 16 * k
    let offset := u32 data (entry + 8)
    let length := u32 data (entry + 12)
    unless offset + length ≤ data.size do
      throw s!"a table of face {index} of the collection runs past the end of the file"
    total := total + length
    unless total ≤ data.size do
      throw s!"the tables of face {index} of the collection hold more bytes than the file"
    tables := tables.push (u32 data entry, u32 data (entry + 4), data.extract offset (offset + length))
  let version := if u32 data base == 0x74727565 then 0x00010000 else u32 data base
  return assembleSfnt version tables

/-- The face's underline band `(position, thickness)` in font units; each value falls back to
the Type 1 convention when implausible. -/
public def underlineBand (upem descent pos thick : Int) : Int × Int :=
  let mag := if descent < 0 then -descent else descent
  let p := if pos < 0 && -(min (upem / 2) mag) ≤ pos then pos else -(upem / 10)
  let t := if 0 < thick && thick ≤ upem / 4 then thick else max 1 (upem / 20)
  (p, t)

public theorem underline_in_descent (upem descent pos thick : Int)
    (h : upem / 10 ≤ -descent) :
    descent ≤ (underlineBand upem descent pos thick).1 := by
  unfold underlineBand
  dsimp only
  repeat' split
  all_goals simp_all only [Bool.and_eq_true, decide_eq_true_eq]
  all_goals omega

/-- Glyph id for a scalar in sorted cmap ranges, or `none`. -/
public def gidIn (cmap : Array (UInt32 × UInt32 × UInt32)) (c : Char) : Option Nat := Id.run do
  let x := UInt32.ofNat c.toNat
  let mut lo := 0
  let mut hi := cmap.size
  for _ in [0:cmap.size + 1] do
    if lo >= hi then
      break
    let mid := (lo + hi) / 2
    match cmap[mid]? with
    | none => break
    | some (s, e, g) =>
      if x < s then
        hi := mid
      else if x > e then
        lo := mid + 1
      else
        return some ((g + (x - s)).toNat % 0x10000)
  return none

public def parse (data : ByteArray) : Except String Font := do
  if data.size < 12 then
    throw "not a font file"
  let tag := u32 data 0
  let isCff := tag == 0x4F54544F  -- 'OTTO'
  if !isCff && tag != 0x00010000 then
    throw "unsupported font format (need TrueType or CFF OpenType)"
  let some head := findTable data "head" | throw "font has no 'head' table"
  let some hhea := findTable data "hhea" | throw "font has no 'hhea' table"
  let some maxp := findTable data "maxp" | throw "font has no 'maxp' table"
  let some hmtx := findTable data "hmtx" | throw "font has no 'hmtx' table"
  let some cmapT := findTable data "cmap" | throw "font has no 'cmap' table"
  for (name, t) in [("head", head), ("hhea", hhea), ("maxp", maxp),
                    ("hmtx", hmtx), ("cmap", cmapT)] do
    unless fits data t do
      throw s!"font table '{name}' extends past the end of the file"
  let unitsPerEm := u16 data (head.offset + 18)
  let ascent := i16 data (hhea.offset + 4)
  let descent := i16 data (hhea.offset + 6)
  let lineGap := i16 data (hhea.offset + 8)
  let numH := u16 data (hhea.offset + 34)
  let numGlyphs := u16 data (maxp.offset + 4)
  let widths : Array Nat := Id.run do
    let mut w : Array Nat := Array.mkEmpty numGlyphs
    let mut last := 0
    for g in [0:numGlyphs] do
      if g < numH then
        last := u16 data (hmtx.offset + 4 * g)
      w := w.push last
    return w
  let cmap := parseCmap data cmapT
  let cmap := sortByKey cmap (·.1.toNat)
  let cls ← classify data
  let psName := cls.psName
  let family := cls.family
  let subfamily := cls.subfamily
  let isBold := cls.isBold
  let isItalic := cls.isItalic
  let isFixedPitch := cls.isFixedPitch
  let weight := cls.weight
  -- OS/2 sxHeight (version 2+), else half the em.
  let os2Metric (off : Nat) (fallback : Int) : Int := match findTable data "OS/2" with
    | some t =>
      let version := if t.offset + 2 ≤ data.size then u16 data t.offset else 0
      if version ≥ 2 && t.offset + off + 2 ≤ data.size then
        let v := i16 data (t.offset + off)
        if v > 0 then v else fallback
      else fallback
    | none => fallback
  let xHeight := os2Metric 86 ((unitsPerEm : Int) / 2)
  -- Seven tenths of the em is where capitals top out in most text faces.
  let capHeight := os2Metric 88 ((unitsPerEm : Int) * 7 / 10)
  -- OS/2 version-0 fields: sFamilyClass (offset 30) and fsType (offset 8).
  let os2U16 (off : Nat) : Nat := match findTable data "OS/2" with
    | some t => if t.offset + off + 2 ≤ data.size then u16 data (t.offset + off) else 0
    | none => 0
  let familyClass := os2U16 30 / 256
  let fsType := os2U16 8
  let upem := if unitsPerEm == 0 then 1000 else unitsPerEm
  -- `post`: underline FWords at offsets 8 and 10, italicAngle a 16.16 Fixed at offset 4.
  let (upos, uthick, italicAngle) := match findTable data "post" with
    | some t =>
      if t.offset + 12 ≤ data.size then
        let raw : Int := u32 data (t.offset + 4)
        let fixed := if raw ≥ 2147483648 then raw - 4294967296 else raw
        (i16 data (t.offset + 8), i16 data (t.offset + 10), fixed / 65536)
      else ((0 : Int), (0 : Int), (0 : Int))
    | none => (0, 0, 0)
  -- A glyph the decoder cannot answer for obstructs its whole advance.
  let (bandPos, bandThick) := underlineBand (upem : Int) descent upos uthick
  let bandHi := bandPos
  let bandLo := bandPos - bandThick
  let src : Thunk Ink.Src := Thunk.mk fun _ => Ink.Src.make data isCff numGlyphs
  let underlineInk : Thunk (Array (Thunk (Array (Int × Int)))) := Thunk.mk fun _ => Id.run do
    let mut ink : Array (Thunk (Array (Int × Int))) := Array.mkEmpty numGlyphs
    for g in [0:numGlyphs] do
      ink := ink.push (Thunk.mk fun _ =>
        match src.get.inkAt g bandLo bandHi with
        | some iv => iv
        | none => #[(0, (widths[g]?.getD 0 : Int))])
    return ink
  let inkExtent : Thunk (Array (Thunk (Option Ink.Bounds))) := Thunk.mk fun _ => Id.run do
    let mut ext : Array (Thunk (Option Ink.Bounds)) := Array.mkEmpty numGlyphs
    for g in [0:numGlyphs] do
      ext := ext.push (Thunk.mk fun _ => src.get.boundsAt g)
    return ext
  let sc := parseGsubSmallCaps data
  let kernData : Thunk (Array KernSub × Array (Nat × Int)) := Thunk.mk fun _ =>
    let subs := parseKernSubs data
    (subs, if subs.isEmpty then parseLegacyKern data else #[])
  let spaceKerns : Thunk (Option SpaceKernCache) := Thunk.mk fun _ =>
    let kd := kernData.get
    if numGlyphs == 0 || (kd.1.isEmpty && kd.2.isEmpty) then none
    else (gidIn cmap ' ').map fun space =>
      let depth := spaceKernDepth numGlyphs
      { size := numGlyphs
        space := space
        depth := depth
        root := makeSpaceKernTree data kd space 0 (2 ^ depth) depth }
  return {
    data := data
    isCff := isCff
    unitsPerEm := upem
    ascent := ascent
    descent := descent
    lineGap := lineGap
    psName := psName
    family := family
    subfamily := subfamily
    isBold := isBold
    isItalic := isItalic
    isFixedPitch := isFixedPitch
    weight := weight
    familyClass := familyClass
    fsType := fsType
    xHeight := xHeight
    capHeight := capHeight
    cmap := cmap
    widths := widths
    numGlyphs := numGlyphs
    underlinePosition := upos
    underlineThickness := uthick
    italicAngle := italicAngle
    underlineInk := underlineInk
    math := parseMath data
    mathVariants := parseVariants false data
    mathHorizVariants := parseVariants true data
    mathTopAccent := parseTopAccent data
    inkExtent := inkExtent
    inkSrc := src
    xInkTop := Thunk.mk fun _ =>
      (gidIn cmap 'x').bind fun g => (src.get.yExtentAt g).map (·.2)
    hasSmcp := sc.1
    hasC2sc := sc.2.1
    smallCaps := sc.2.2
    kernData := kernData
    spaceKerns := spaceKerns
  }

/-- A face's ink above the baseline in font units: its cap height, else its ascent. -/
public def inkAscent (f : Font) : Int :=
  if f.capHeight > 0 then f.capHeight else f.ascent

/-- Glyph id for a scalar, or `none` (missing glyph). -/
public def gid (f : Font) (c : Char) : Option Nat :=
  gidIn f.cmap c

/-- The math face's alphabet-range coverage, read at each range's first scalar as unicode-math
does. -/
public def mathAlphabetCoverage (f : Font)
    (sources : Math.MathAlphabetSources) : Math.MathAlphabetCoverage :=
  { sources
    covered := (Math.allAlphabets.flatMap fun a =>
      a.ranges.filterMap fun r =>
        if (f.gid (a.apply r.anchor)).isSome then some (a, r) else none).toArray }

/-- The small-caps form of glyph `g`, or `g` when the face maps it nowhere. -/
public def smallCapGid (f : Font) (g : Nat) : Nat :=
  substGid f.smallCaps g

/-- The pair kern between two adjacent glyphs in font units, 0 when the face has none. -/
public def kernAdv (f : Font) (g1 g2 : Nat) : Int :=
  pairAdv f.data f.kernData.get g1 g2

/-- Glyph `g`'s kern with the space glyph in font units: `(g, space)` when `after`, else
`(space, g)`. -/
public def spaceKernAdv (f : Font) (after : Bool) (g : Nat) : Int :=
  match f.spaceKerns.get with
  | none => 0
  | some cache =>
    match cache.lookup? g with
    | some (pair, _) => if after then pair.1 else pair.2
    | none =>
      if after then pairAdv f.data f.kernData.get g cache.space
      else pairAdv f.data f.kernData.get cache.space g

/-- The sorted char→glyph ranges of a font image, without parsing the rest of it. -/
public def cmapRanges (data : ByteArray) : Array (UInt32 × UInt32 × UInt32) :=
  match findTable data "cmap" with
  | some t => if fits data t then sortByKey (parseCmap data t) (·.1.toNat) else #[]
  | none => #[]

/-- Advance width of a scalar in font units (0 when the glyph is missing). -/
public def advance (f : Font) (c : Char) : Nat :=
  match f.gid c with
  | some g => f.widths[g]?.getD 0
  | none => 0

/-- The interword space in font units: the space glyph's advance, as LuaTeX's `\fontdimen2`,
else half the em dash, else half the em (LuaTeX's fallbacks less its `averagewidth` step). -/
public def spaceAdvance (f : Font) : Nat :=
  let sp := f.advance ' '
  if sp > 0 then sp
  else
    let em := f.advance '—'
    if em > 0 then em / 2 else f.unitsPerEm / 2

/-- The x-intervals in font units where glyph `g`'s ink crosses the underline band. -/
public def inkAt (f : Font) (g : Nat) : Array (Int × Int) :=
  match f.underlineInk.get[g]? with
  | some t => t.get
  | none => #[]

/-- Glyph `g`'s ink hull in font units; `none` when undecodable or past the table. -/
public def bounds (f : Font) (g : Nat) : Option Ink.Bounds :=
  (f.inkExtent.get[g]?).bind (·.get)

/-- The height of the glyph for `c` in font units, as `\fontcharht` reads its ink hull. -/
public def charHeight (f : Font) (c : Char) : Int :=
  match f.gid c with
  | none => 0
  | some g =>
    match f.bounds g with
    | some b => max 0 b.top
    | none => f.capHeight

/-- The depth of the glyph for `c` in font units, as `\fontchardp` reads its ink hull. -/
public def charDepth (f : Font) (c : Char) : Int :=
  match f.gid c with
  | none => 0
  | some g =>
    match f.bounds g with
    | some b => max 0 (-b.bottom)
    | none => 0

public def yExtent (f : Font) (g : Nat) : Option (Int × Int) :=
  (f.bounds g).map fun b => (b.bottom, b.top)

/-- The x-height optical size matching trusts: the measured 'x' ink top, else `xHeight`, in
`(0, upem]`. -/
public def xHeightOptical (f : Font) : Nat :=
  let declared := f.xHeight.toNat
  let measured := match f.xInkTop.get with
    | some hi => if 0 < hi then hi.toNat else declared
    | none => declared
  (measured.min f.unitsPerEm).max 1

/-- The vertical size variants of glyph `g`, in increasing size; empty when none. -/
public def vertVariants (f : Font) (g : Nat) : Array (Nat × Int) :=
  match f.mathVariants.find? (·.1 == g) with
  | some (_, vs) => vs
  | none => #[]

/-- The horizontal size variants of glyph `g`, in increasing size; empty when none. -/
public def horizVariants (f : Font) (g : Nat) : Array (Nat × Int) :=
  match f.mathHorizVariants.find? (·.1 == g) with
  | some (_, vs) => vs
  | none => #[]

/-- Where a top accent attaches on glyph `g`, in design units clamped into its advance: the
bound `Math.accentAttach_covers` quantifies over. -/
public def topAccentX (f : Font) (g : Nat) : Int :=
  let w : Int := f.widths[g]?.getD 0
  match f.mathTopAccent.find? (·.1 == g) with
  | some (_, x) => min (max x 0) w
  | none => w / 2

public theorem topAccentX_covers (f : Font) (g : Nat) :
    0 ≤ f.topAccentX g ∧ f.topAccentX g ≤ (f.widths[g]?.getD 0 : Int) := by
  unfold Font.topAccentX
  dsimp only
  split <;> omega

/-- The accent mark's own attachment x, unclamped; half the advance where uncovered. -/
public def markAttachX (f : Font) (g : Nat) : Int :=
  match f.mathTopAccent.find? (·.1 == g) with
  | some (_, x) => x
  | none => (f.widths[g]?.getD 0 : Int) / 2

/-- This face's normalized underline band `(position, thickness)`, in font units. -/
public def band (f : Font) : Int × Int :=
  underlineBand (f.unitsPerEm : Int) f.descent f.underlinePosition
    f.underlineThickness

/-- The faces a document typesets with; index 0 is the body regular face. -/
public structure FontSet where
  fonts : Array Font
  /-- (family slot, CSS weight, italic) → index into `fonts`. -/
  index : Array ((Nat × Nat × Bool) × Nat) := #[]
  /-- Per-scalar fallback face for a glyph the styled face lacks. -/
  fallback : Array (Char × Nat) := #[]
  /-- The document's math face, carrying a `MATH` table; `none` sets formulas as text. -/
  math : Option Nat := none
  /-- Alphabet range anchors derived once from `math`, with the unicode-math source policy. -/
  mathAlphabets : Math.MathAlphabetCoverage := {}
  /-- Per-face deflated program bytes from the driver's cache; empty means the writer compresses. -/
  zdata : Array (Option ByteArray) := #[]
  deriving Inhabited

namespace FontSet

public def body (fs : FontSet) : Font := fs.fonts[0]!

public def get (fs : FontSet) (i : Nat) : Font := fs.fonts[i]?.getD fs.body

/-- The set of one face, every slot and variant mapped to it. -/
public def ofFace (f : Font) : FontSet :=
  { fonts := #[f]
    index := ((List.range 3).flatMap fun slot =>
      [((slot, 400, false), 0), ((slot, 700, false), 0),
       ((slot, 400, true), 0), ((slot, 700, true), 0)]).toArray }

/-- The math face and its constants, when the document has a usable one. -/
public def mathFont? (fs : FontSet) : Option (Nat × Font × MathConsts) := do
  let i ← fs.math
  let f ← fs.fonts[i]?
  let c ← f.math
  pure (i, f, c)

/-- The face for a slot (0 body, 1 sans, 2 mono), CSS weight and italic, falling back to the
slot's regular and then face 0. -/
public def lookup (fs : FontSet) (slot : Nat) (weight : Nat) (italic : Bool) : Nat :=
  match fs.index.find? fun e => e.1 == (slot, weight, italic) with
  | some (_, i) => i
  | none =>
    match fs.index.find? fun e => e.1 == (slot, 400, false) with
    | some (_, i) => i
    | none => 0

public theorem index_total (fs : FontSet) (h0 : 0 < fs.fonts.size)
    (hwf : ∀ e ∈ fs.index, e.2 < fs.fonts.size) (slot weight : Nat)
    (italic : Bool) : fs.lookup slot weight italic < fs.fonts.size := by
  unfold lookup
  split
  next heq => exact hwf _ (Array.mem_of_find?_eq_some heq)
  next =>
    split
    next heq => exact hwf _ (Array.mem_of_find?_eq_some heq)
    next => exact h0

/-- Does this slot resolve to the body face? -/
public def slotCollapsed (fs : FontSet) (slot : Nat) : Bool :=
  slot != 0 && fs.lookup slot 400 false == fs.lookup 0 400 false

public theorem slotCollapsed_body (fs : FontSet) : fs.slotCollapsed 0 = false := by
  simp [slotCollapsed]

public theorem slotCollapsed_exact (fs : FontSet) (slot : Nat) (h : slot != 0) :
    fs.slotCollapsed slot = (fs.lookup slot 400 false == fs.lookup 0 400 false) := by
  simp [slotCollapsed, h]

/-- Is the face this slot resolves to fixed-pitch, by its own `post` flag? -/
public def slotIsFixedPitch (fs : FontSet) (slot : Nat) : Bool :=
  match fs.fonts[fs.lookup slot 400 false]? with
  | some f => f.isFixedPitch
  | none => false

public theorem slotIsFixedPitch_exact (fs : FontSet) (slot : Nat)
    (h : fs.lookup slot 400 false < fs.fonts.size) :
    fs.slotIsFixedPitch slot = (fs.fonts[fs.lookup slot 400 false]).isFixedPitch := by
  simp [slotIsFixedPitch, Array.getElem?_eq_getElem h]

/-- The font that sets a glyph the styled face lacks, if any face can. -/
public def fallbackFor (fs : FontSet) (c : Char) : Option Nat :=
  (fs.fallback.find? (·.1 == c)).map (·.2)

end FontSet
end LeanTex.Core.Font
