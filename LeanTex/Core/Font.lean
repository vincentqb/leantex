import LeanTex.Core.Diag
import LeanTex.Core.Ink
import LeanTex.Core.Math

namespace LeanTex.Core.Font

open LeanTex.Core.Ink

/-- The constants this slice reads from an OpenType `MATH` table's
MathConstants (learn.microsoft.com/typography/opentype/spec/math), in font
design units: the script scale percentages (sanitized, see
`Math.ScriptScales.clamp`), the script-attachment shifts, and the
fraction, radical, limit, and delimiter constants the M6 constructions
position from. Per the spec, attachment constants are read from the font
of the base and scale with the base's size. -/
structure MathConsts where
  scales : Math.ScriptScales
  axisHeight : Int
  /-- "Height of the bottom of a math accent above the baseline" — the
  height an accent glyph is designed to sit at; a taller base pushes the
  accent up by the difference (MATH spec, MathConstants; TeXbook Appendix
  G rule 12's χ). -/
  accentBaseHeight : Int
  subscriptShiftDown : Int
  superscriptShiftUp : Int
  superscriptShiftUpCramped : Int
  spaceAfterScript : Int
  /-- "Minimum height of n-ary operators (such as integral and summation)
  for formulas in display mode" (MATH spec, MathConstants). -/
  displayOperatorMinHeight : Int
  upperLimitGapMin : Int
  upperLimitBaselineRiseMin : Int
  lowerLimitGapMin : Int
  lowerLimitBaselineDropMin : Int
  /-- The stack constants place a rule-less fraction's parts (`\binom`,
  `\genfrac` with a zero thickness): TeXbook Appendix G rule 15's
  `\atop` case, in OpenType's names (MATH spec, MathConstants). -/
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
  /-- The overbar constants position `\overline`'s rule (MATH spec,
  MathConstants; TeXbook Appendix G rule 9 is the same construction over
  `default_rule_thickness`). -/
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

/-- Parse the MathConstants this slice uses out of a `MATH` table, or
`none` when the face has no readable table — the caller's diagnostic names
the face; constants are never invented (PLAN, M6 design entry). Layout:
header (version, three Offset16s), then MathConstants with two int16
percentages, two UFWORDs, MathValueRecords (FWORD value + device offset)
from offset 8 through radicalKernAfterDegree at 208, and a final int16
percentage at 212 — 214 bytes, the spec's full fixed-size record. -/
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

/-- A coverage table's glyph list (OpenType spec, coverage formats 1 and 2):
the base glyphs a MathVariants construction list covers, in coverage order —
the order the construction offsets follow. -/
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
      -- Total cap: the per-range clamp still lets n overlapping garbage
      -- ranges push n·0x10000 entries; no coverage lists more glyphs than
      -- the 16-bit glyph space holds.
      if out.size ≥ 0x10000 then break
      let s := u16 b (off + 4 + 6 * i)
      let e := u16 b (off + 6 + 6 * i)
      -- Bounded: a malformed range never expands past the glyph space.
      for g in [s : min (e + 1) 0x10000] do
        out := out.push g
  | _ => pure ()
  return out

/-- The glyph variants of a `MATH` table's MathVariants
(learn.microsoft.com/typography/opentype/spec/math): per base glyph, its
size variants as `(glyph id, advance measurement in design units)`, "in
order of increasing size" per the spec — height for the vertical list
(what grows a delimiter, a radical, or a display operator over its
content), width for the horizontal one (what stretches `\widehat` over
its base). Glyph assemblies (building past the largest variant from
parts) are not read in this slice; the largest variant is the ceiling,
recorded in PLAN. Empty when the face has none. -/
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

/-- The MathTopAccentAttachment table of a `MATH` table's MathGlyphInfo
(MATH spec §6.3, "MathTopAccentAttachment"): per covered glyph, the
horizontal position for attaching a top accent, in design units from the
glyph origin. Empty when the face carries none; a glyph outside the
coverage takes half its advance, the spec's own default. -/
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

/-- Sort a file-derived table by a `Nat` key in worst-case `n·log n`.
`Array.qsort` degrades to quadratic when many keys compare equal, and a
malformed font manufactures exactly that input: a lying cmap-12 group
count reading zeros past the end of its file yields a run of identical
groups, and the quadratic sort — not the bounded reads — turned one
doctored 2M-group face into an hour-long parse. Every sort over bytes a
file claims goes through here, so parse cost stays `n·log n` in the bytes
present whatever they say. Stable, so equal keys keep file order. -/
private def sortByKey (xs : Array α) (key : α → Nat) : Array α :=
  (xs.toList.mergeSort fun x y => key x ≤ key y).toArray

/-- A 4-byte OpenType tag as a string, for script and feature records. -/
private def tag4 (b : ByteArray) (off : Nat) : String :=
  String.ofList ((b.extract off (off + 4)).toList.map fun v => Char.ofNat v.toNat)

/-- Exact-key binary search over `xs`, sorted ascending by `key` with no
duplicate keys: the index and element whose key equals `k`, or `none`.
The one search the sorted-table readers share (substitution maps,
ClassDefs, coverage arrays, legacy kern pairs). -/
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

/-- A hit names a real element with the searched key: `bsearch`'s answer
is an index into `xs` whose element the key function maps to `k`. -/
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

/-- The image of `g` under a sorted gid→gid substitution map: the mapped
gid, or `g` itself when the map does not cover it. Binary search; the map
is sorted by source gid. -/
def substGid (map : Array (Nat × Nat)) (g : Nat) : Nat :=
  match bsearch map (·.1) g with
  | some (_, _, dst) => dst
  | none => g

/-- The lookup indices one GSUB feature tag selects, resolved for `latn`
falling back to `DFLT` and the default language system (OpenType spec,
GSUB header → ScriptList → LangSys → FeatureList chain). Empty when the
script, language system, or feature is absent; a script's non-default
language systems are not read in this slice. -/
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

/-- One GSUB LookupType 1 (single substitution) lookup as a gid→gid map,
subtable formats 1 (delta) and 2 (explicit list), sorted by source gid.
Any other lookup type reads as empty: contextual, alternate, ligature,
and extension lookups are outside this slice. -/
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

/-- The small-caps substitution a face offers: whether GSUB carries `smcp`
(lowercase to small capitals) and `c2sc` (capitals to small capitals) for
`latn`/`DFLT`, and their composed gid→gid map. The map is built only when
BOTH features are present — uniform small caps over mixed case needs both,
and half a mechanism would set neighbouring words at two different
small-cap shapes — by threading every covered gid through the features'
lookups in LookupList order, the application order the spec prescribes.
Sorted by source gid for `substGid`. -/
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

/-- A ClassDef table (OpenType spec, class definition formats 1 and 2) as
`(gid, class)` pairs sorted by gid, listed glyphs only — an unlisted glyph
is class 0, the spec's default. -/
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
      -- Total cap: as in `parseCoverage`, overlapping garbage ranges must
      -- not multiply the per-range clamp by the range count.
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

/-- The size in bytes of a GPOS ValueRecord under a value format, and the
byte offset of its XAdvance field: one 16-bit word per set bit, XAdvance
(0x0004) after XPlacement (0x0001) and YPlacement (0x0002) when those are
set (GPOS spec §"ValueRecord"). -/
private def valueRecord (vf : Nat) : Nat × Option Nat :=
  let bits (n : Nat) : Nat := (List.range 16).foldl
    (fun acc i => acc + (n >>> i) % 2) 0
  (2 * bits (vf % 0x10000),
   if vf % 8 ≥ 4 then some (2 * bits (vf % 4)) else none)

/-- One GPOS PairPos subtable, parsed to its skeleton: coverage and class
definitions up front (they answer per-pair queries by binary search), the
value matrix left in the font bytes and indexed on demand — enumerating a
class-based subtable into explicit pairs costs ~30 ms per Source Serif
face (178k pairs) at every parse, for pairs mostly never asked for. -/
private structure KernSub where
  fmt : Nat
  off : Nat
  /-- Coverage gids in coverage order (ascending): index = coverage index. -/
  cov : Array Nat
  size1 : Nat
  size2 : Nat
  /-- Byte offset of XAdvance inside the first value record. -/
  xAdv : Nat
  cd1 : Array (Nat × Nat) := #[]
  cd2 : Array (Nat × Nat) := #[]
  c1Count : Nat := 0
  c2Count : Nat := 0
  deriving Inhabited

/-- The PairPos subtables one GPOS `kern` feature carries for
`latn`/`DFLT`, formats 1 and 2, XAdvance of the first glyph only — the
one value horizontal Latin kerning uses. A PairPos subtable behind an
extension lookup (type 9, `ExtensionPosFormat1`: its type at +2, a 32-bit
offset at +4) is read through its one hop — the spec forbids a second,
and a face compiled with extensions (Fira Sans, Inter) keeps all or most of
its pairs there. Contextual positioning is outside this slice; a font with
no GPOS kern reads as empty (Open Sans) and the legacy `kern` table
answers instead. -/
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

/-- The legacy `kern` table, format 0 horizontal subtables (TrueType):
HarfBuzz's own fallback when GPOS carries no `kern` feature. Sorted
`(g1 * 0x10000 + g2, value)` pairs. -/
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

/-- The pair kern between glyphs `g1` and `g2` over a face's bytes and its
parsed kern data (`Font.kernAdv` reads it; `parse` fills each glyph's
space pairs from it). -/
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
  -- legacy pairs
  match bsearch pairs (·.1) (g1 * 0x10000 + g2) with
  | some (_, _, v) => return v
  | none => return 0

/-- A parsed sfnt font: the metrics the layout engine needs, the char→glyph
map, and the raw bytes for embedding. Pure data; loading the file is the
driver's job. -/
structure Font where
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
  /-- OS/2 sFamilyClass, class ID (high byte): the IBM font class the face
  itself declares — 8 is Sans Serif, 1–7 the serif classes (OpenType spec,
  OS/2 table, sFamilyClass). 0 when the face declares none, which many do
  (Fira Sans, Source Code Pro); the consumer falls back to the slot's own
  declaration then, never to a guess from the family name. -/
  familyClass : Nat := 0
  /-- OS/2 fsType embedding-licensing bits, recorded as declared (OpenType
  spec, OS/2 table, fsType; bit 2 = preview & print only). Nothing gates on
  them yet: the PDF path embeds without reading them either, and gating is
  a design decision this record keeps honest when it arrives. -/
  fsType : Nat := 0
  xHeight : Int
  /-- OS/2 sCapHeight: how tall a line of text is, as TeX measures it from the
  glyphs. `ascent` is the room the font reserves for accents, not that. -/
  capHeight : Int
  cmap : Array (UInt32 × UInt32 × UInt32)  -- (startChar, endChar, startGid), sorted
  widths : Array Nat                        -- advance width per gid, font units
  numGlyphs : Nat
  /-- `post` underline metrics, font units. Zero means the font said nothing;
  the consumer supplies a fallback. -/
  underlinePosition : Int
  underlineThickness : Int
  /-- `post` italicAngle in whole degrees, counter-clockwise from vertical
  (so a right-leaning italic is negative). Zero means the face declared
  none; the PDF descriptor supplies its convention then. -/
  italicAngle : Int
  /-- Per-gid, lazily: merged x-intervals (font units) of glyph ink inside
  the band the underline rule occupies, from the glyph's own outline. Empty
  means the rule runs unbroken under the glyph. Decoding happens on first
  use and is memoized (`Thunk` is call-by-need), so a document with no
  underline never pays for it and a repeated glyph decodes once; malformed
  or truncated outline data obstructs its whole advance, never panics and
  never leaves a rule through ink it could not read. -/
  underlineInk : Thunk (Array (Thunk (Array (Int × Int))))
  /-- OpenType MATH constants, when the face carries the table: what makes
  a face usable as a document's math font. -/
  math : Option MathConsts
  /-- The MATH table's vertical glyph variants: per base glyph, the size
  variants that grow a delimiter, radical, or display operator. Empty when
  the face carries none. -/
  mathVariants : Array (Nat × Array (Nat × Int))
  /-- The MATH table's horizontal glyph variants: what stretches a wide
  accent (`\widehat`) over its base. Empty when the face carries none. -/
  mathHorizVariants : Array (Nat × Array (Nat × Int))
  /-- The MATH table's top-accent attachment positions, per covered glyph,
  in design units from the glyph origin. A glyph outside the coverage
  attaches at half its advance, the spec's own default. -/
  mathTopAccent : Array (Nat × Int)
  /-- Per-gid, lazily: the glyph's vertical ink extent `(minY, maxY)` in
  font units, from its own outline — control-point hull, so the true ink is
  inside it. `none` where the outline could not be decoded; the consumer
  falls back to nominal metrics. Memoized like `underlineInk` (only math
  layout asks, so a text face never builds the array), and only
  glyphs math actually measures ever decode. -/
  inkExtent : Thunk (Array (Thunk (Option (Int × Int))))
  /-- The face's outline source, prepared once and lazily (`Ink.Src.make`):
  the source `underlineInk` and `inkExtent` decode from, and the one a
  subset reads its CFF structure from (`FontSubset.program`), so a face
  whose layout decoded its glyphs is never parsed a second time to embed
  them. -/
  inkSrc : Thunk Ink.Src
  /-- Lazily: the measured ink top of this face's own 'x' in font units,
  from its outline. `none` when the face has no 'x' or the outline does not
  decode. Optical size matching prefers this over the declared `xHeight`
  because OS/2 sxHeight lies in some fonts; decoded once, on first use. -/
  xInkTop : Thunk (Option Int)
  /-- GSUB carries `smcp` (lowercase to small capitals) for `latn`/`DFLT`.
  Measured by `parseGsubSmallCaps`; `smallCaps` below is the usable product. -/
  hasSmcp : Bool
  /-- GSUB carries `c2sc` (capitals to small capitals) for `latn`/`DFLT`. -/
  hasC2sc : Bool
  /-- The composed `smcp`+`c2sc` gid→gid substitution, sorted by source gid.
  Empty unless the face carries both features (see `parseGsubSmallCaps`);
  empty means the layout synthesises small caps instead. -/
  smallCaps : Array (Nat × Nat)
  /-- Pair kerning, lazily (`Thunk` is call-by-need, so a loaded-but-
  unused variant face never pays the ClassDef walk): the GPOS `kern`
  PairPos subtables parsed to their skeletons and queried per pair
  (`Font.kernAdv`, the class matrices staying in `data`), and the legacy
  `kern` table pairs read only when GPOS carries none — HarfBuzz's own
  fallback rule (F_GLOBAL_HAS_FALLBACK). Both empty for a face with
  neither: Open Sans, and every monospace done right (Source Code Pro). -/
  kernData : Thunk (Array KernSub × Array (Nat × Int))
  /-- Each glyph's pair kerns with the face's space glyph, lazily per glyph:
  `(kern (g, space), kern (space, g))` in font units, from the same pairs
  `Font.kernAdv` reads — luaotfload's `spacekerns` table, which its space
  kerning reads beside every interword glue. `(0, 0)` throughout for a
  face with no space glyph. Read through `Font.spaceKernAdv`. -/
  spaceKerns : Thunk (Array (Thunk (Int × Int)))
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
      -- glyphIdArray ranges: expand per char (rare segments, bounded)
      for c in [startC:endC+1] do
        let idx := rangeBase + 2 * k + rangeOff + 2 * (c - startC)
        if idx + 1 < b.size then
          let g := u16 b idx
          if g != 0 then
            let gid := (g + delta) % 0x10000
            out := out.push (UInt32.ofNat c, UInt32.ofNat c, UInt32.ofNat gid)
  return out

private def parseCmap12 (b : ByteArray) (off : Nat) : Array (UInt32 × UInt32 × UInt32) := Id.run do
  -- The group count is the one file-derived loop bound with no structural
  -- limit; clamp it by the bytes actually present, never trust it — a
  -- malformed installed face otherwise demands gigabytes of pushes (and a
  -- mass of identical past-the-end zero groups) at every resolve.
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

/-- Read one `name` table record. Prefers the typographic name (id 16/17)
over the legacy family/subfamily (id 1/2) when both are present. -/
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

/-- Identity and style of a face, from the metadata tables only. Split out
because classifying a font for a family scan needs none of its metrics: a
scan touches every installed face, and `hmtx` and `cmap` are the two tables
that make that expensive. `parse` uses the same code so the two can never
disagree about what a face is called. -/
structure Class where
  psName : String
  family : String
  subfamily : String
  isBold : Bool
  isItalic : Bool
  isFixedPitch : Bool
  weight : Nat
  deriving Repr, Inhabited

/-- Classify a face. Needs only `head`; `name`, `OS/2`, and `post` refine it. -/
def classify (data : ByteArray) : Except String Class := do
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
  -- OS/2 fsSelection is authoritative when present; the subfamily string is
  -- the fallback, and covers fonts that call oblique faces "Oblique".
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
  -- `post`: isFixedPitch is at offset 12 — version (4), italicAngle (4),
  -- underlinePosition (2), underlineThickness (2). Offset 16 is
  -- minMemType42, a memory hint most faces leave at 0 and some do not (two
  -- Arphic faces in TeX Live carry 100000), so a reader four bytes late
  -- called every monospace design proportional and those two fixed-pitch.
  -- The PDF descriptor's FixedPitch flag and the generic that closes every
  -- slot's HTML stack (`HtmlDoc.genericFor`) read this field.
  let isFixedPitch := match findTable data "post" with
    | some t => if t.offset + 16 ≤ data.size then u32 data (t.offset + 12) != 0 else false
    | none => false
  -- OS/2 usWeightClass (100–900). Families ship weights, not a bold flag:
  -- "Demi" at 600 is a family's bold face even when the BOLD bit is clear.
  let weight := match findTable data "OS/2" with
    | some t =>
      if t.offset + 6 ≤ data.size then
        let w := u16 data (t.offset + 4)
        if w == 0 then (if isBold then 700 else 400) else w
      else if isBold then 700 else 400
    | none => if isBold then 700 else 400
  return { psName, family, subfamily, isBold, isItalic, isFixedPitch, weight }

/-- The version of `classify`'s answer, for any store that keeps the answer
past one process: it moves whenever the answer changes for some byte
string, so an answer from another version is never read as this one's.
Version 2 reads `post.isFixedPitch` at offset 12; every classifier before it
read offset 16 and stored its answers under an unversioned name. The suite
pins the shipped faces' answers to this number, so a change to the answer
that leaves the number alone fails there. -/
def classifierVersion : Nat := 2

/-- The underline band a face declares, normalized to something drawable:
`(position, thickness)` in font units, the band spanning
`[position - thickness, position]` relative to the baseline. `post` values
are taken only when plausible — position strictly below the baseline and no
deeper than the face's own descender line (or half the em, whichever is
nearer: a band below the descent would leave the descender region an
underline is defined to occupy, `underline_in_descent`), thickness positive
and at most a quarter em — and each falls back to the convention
independently, so one absurd value does not discard the other. The fallback
band — a tenth of the em down, a twentieth thick — is the Adobe Type 1
convention (UnderlinePosition -100, UnderlineThickness 50 in the
1000-unit em: the Type 1 font-program defaults the ecosystem carried
forward). The single normalization shared by ink extraction (`parse`) and
rule placement (`Layout.underlineSegs`): the two must agree on the band,
or the rule is cleared against ink it does not overlap. -/
def underlineBand (upem descent pos thick : Int) : Int × Int :=
  let mag := if descent < 0 then -descent else descent
  let p := if pos < 0 && -(min (upem / 2) mag) ≤ pos then pos else -(upem / 10)
  let t := if 0 < thick && thick ≤ upem / 4 then thick else max 1 (upem / 20)
  (p, t)

/-- The tightened guard's algebra: for a face whose descent magnitude is
at least the em-tenth fallback, the normalized band position stays at or
above the descender line — the rule is drawn in the descender region,
inside the metric box `Layout.lineExtent` already reserves below the
baseline, so drawing it can never ask for room (`underline_no_growth` is
the placement half). Containment of the band's full thickness is per-face
(post values are fallback-normalized, so it is not a theorem) and is
pinned as a test over every shipped fixture face. -/
theorem underline_in_descent (upem descent pos thick : Int)
    (h : upem / 10 ≤ -descent) :
    descent ≤ (underlineBand upem descent pos thick).1 := by
  unfold underlineBand
  dsimp only
  repeat' split
  all_goals simp_all only [Bool.and_eq_true, decide_eq_true_eq]
  all_goals omega

/-- Glyph id for a scalar in sorted cmap ranges, or `none`. Binary search
over ranges (containment, not exact key — the one search `bsearch` does
not subsume). -/
def gidIn (cmap : Array (UInt32 × UInt32 × UInt32)) (c : Char) : Option Nat := Id.run do
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

def parse (data : ByteArray) : Except String Font := do
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
  -- OS/2 sxHeight (version 2+); tokens in `ex` need it. Falls back to half
  -- the em, which is the conventional approximation.
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
  -- post underline metrics: FWords at offsets 8 and 10 — and italicAngle,
  -- the face's own declared slant: a signed 16.16 Fixed in degrees at
  -- offset 4 (OpenType post table), floored to whole degrees.
  let (upos, uthick, italicAngle) := match findTable data "post" with
    | some t =>
      if t.offset + 12 ≤ data.size then
        let raw : Int := u32 data (t.offset + 4)
        let fixed := if raw ≥ 2147483648 then raw - 4294967296 else raw
        (i16 data (t.offset + 8), i16 data (t.offset + 10), fixed / 65536)
      else ((0 : Int), (0 : Int), (0 : Int))
    | none => (0, 0, 0)
  -- A glyph interrupts the rule where its ink crosses the band the rule
  -- occupies, `[position - thickness, position]` after normalization. Any
  -- glyph the decoder cannot answer for — malformed or truncated tables, a
  -- CID-keyed CFF, seac or point-matched composition, an exceeded budget —
  -- obstructs its whole advance: undecodable input clears the rule, it
  -- never leaves one through ink.
  let (bandPos, bandThick) := underlineBand (upem : Int) descent upos uthick
  let bandHi := bandPos
  let bandLo := bandPos - bandThick
  -- One lazy pattern for the ink tables: the decode source (whose CFF
  -- INDEX walk is O(numGlyphs)) and both per-gid thunk arrays sit behind
  -- an outer Thunk each, so a face never asked for ink pays nothing at
  -- load; the inner thunks keep per-gid memoization.
  let src : Thunk Ink.Src := Thunk.mk fun _ => Ink.Src.make data isCff numGlyphs
  let underlineInk : Thunk (Array (Thunk (Array (Int × Int)))) := Thunk.mk fun _ => Id.run do
    let mut ink : Array (Thunk (Array (Int × Int))) := Array.mkEmpty numGlyphs
    for g in [0:numGlyphs] do
      ink := ink.push (Thunk.mk fun _ =>
        match src.get.inkAt g bandLo bandHi with
        | some iv => iv
        | none => #[(0, (widths[g]?.getD 0 : Int))])
    return ink
  let inkExtent : Thunk (Array (Thunk (Option (Int × Int)))) := Thunk.mk fun _ => Id.run do
    let mut ext : Array (Thunk (Option (Int × Int))) := Array.mkEmpty numGlyphs
    for g in [0:numGlyphs] do
      ext := ext.push (Thunk.mk fun _ => src.get.yExtentAt g)
    return ext
  let sc := parseGsubSmallCaps data
  let kernData : Thunk (Array KernSub × Array (Nat × Int)) := Thunk.mk fun _ =>
    let subs := parseKernSubs data
    (subs, if subs.isEmpty then parseLegacyKern data else #[])
  let spaceKerns : Thunk (Array (Thunk (Int × Int))) := Thunk.mk fun _ => Id.run do
    let some sp := gidIn cmap ' ' | return Array.replicate numGlyphs (Thunk.pure (0, 0))
    let mut out : Array (Thunk (Int × Int)) := Array.mkEmpty numGlyphs
    for g in [0:numGlyphs] do
      out := out.push (Thunk.mk fun _ =>
        (pairAdv data kernData.get g sp, pairAdv data kernData.get sp g))
    return out
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

/-- A face's ink above the baseline, in font units: its cap height, or its
ascent when the face declares none — the one reading the line builder
places with (`lineExtent`) and the shipped-page census judges by
(`Check.Shipped.ofOut`), so a face cannot be placed under one convention
and judged under another. -/
def Font.inkAscent (f : Font) : Int :=
  if f.capHeight > 0 then f.capHeight else f.ascent

/-- Glyph id for a scalar, or `none` (missing glyph). -/
def Font.gid (f : Font) (c : Char) : Option Nat :=
  gidIn f.cmap c

/-- The small-caps form of glyph `g` under this face's `smcp`+`c2sc`
substitutions, or `g` itself when the face maps it nowhere — a digit or a
point of punctuation passes through unchanged. -/
def Font.smallCapGid (f : Font) (g : Nat) : Nat :=
  substGid f.smallCaps g

/-- The pair kern between two adjacent glyphs of this face, in font units
(usually negative — 'Ta' tightens): the first GPOS PairPos subtable whose
coverage holds `g1` answers (format 1 by pair-set scan, format 2 by class
matrix), else the legacy pairs, else 0 — including for every pair of a
face with no kern data at all. -/
def Font.kernAdv (f : Font) (g1 g2 : Nat) : Int :=
  pairAdv f.data f.kernData.get g1 g2

/-- Glyph `g`'s pair kern with the face's space glyph, in font units: the
pair `(g, space)` when `after` (the space follows `g`), `(space, g)`
otherwise — `Font.kernAdv`'s answer, read from the per-glyph memo
`spaceKerns` fills on first use (a gid past it is asked directly). -/
def Font.spaceKernAdv (f : Font) (after : Bool) (g : Nat) : Int :=
  match f.spaceKerns.get[g]? with
  | some t => if after then t.get.1 else t.get.2
  | none =>
    match f.gid ' ' with
    | some sp => if after then f.kernAdv g sp else f.kernAdv sp g
    | none => 0

/-- The char→glyph ranges of a font image alone, sorted, without parsing the
rest of it: what the per-glyph fallback scan asks of a candidate face is only
"has it the glyph". Empty when the image has no readable cmap. -/
def cmapRanges (data : ByteArray) : Array (UInt32 × UInt32 × UInt32) :=
  match findTable data "cmap" with
  | some t => if fits data t then sortByKey (parseCmap data t) (·.1.toNat) else #[]
  | none => #[]

/-- Advance width of a scalar in font units (0 when the glyph is missing). -/
def Font.advance (f : Font) (c : Char) : Nat :=
  match f.gid c with
  | some g => f.widths[g]?.getD 0
  | none => 0

/-- The interword space in font units: the space glyph's own advance —
what LuaTeX gives an OpenType face for `\fontdimen2` (luatex-fonts-merged
.lua, `constructors.scale`: `spaceunits = descriptions[0x20].width`, and
under the default `syncspace` the stretch and shrink follow as
`spaceunits/2` and `spaceunits/3`). A face without a space glyph takes the
same loader's fallback chain: half the em dash, else half the em (the
loader's `averagewidth` step between them is a field this engine does not
read; half the em is its same class of stand-in). Zero — words jammed
together with no room to justify — is never an answer. -/
def Font.spaceAdvance (f : Font) : Nat :=
  let sp := f.advance ' '
  if sp > 0 then sp
  else
    let em := f.advance '—'
    if em > 0 then em / 2 else f.unitsPerEm / 2

/-- The x-intervals (font units) where this glyph's ink crosses the underline
band. Empty means the rule runs unbroken; a gid past the table has no ink.
Forces the lazy decode; the answer is memoized in the font. -/
def Font.inkAt (f : Font) (g : Nat) : Array (Int × Int) :=
  match f.underlineInk.get[g]? with
  | some t => t.get
  | none => #[]

/-- The vertical ink extent `(minY, maxY)` of glyph `g` in font units, from
its own outline. `none` for an undecodable outline or a gid past the table;
the consumer falls back to nominal metrics. Memoized in the font. -/
def Font.yExtent (f : Font) (g : Nat) : Option (Int × Int) :=
  (f.inkExtent.get[g]?).bind (·.get)

/-- The x-height optical size matching trusts, in font units: the measured
ink top of the face's own 'x' when its outline decodes — OS/2 sxHeight lies
in some fonts — else the declared `xHeight` (sxHeight, half the em last: the
engine's existing metric fallback order), clamped into `(0, upem]` so
`Math.mathSize`'s agreement bounds hold for every font the parser accepts. -/
def Font.xHeightOptical (f : Font) : Nat :=
  let declared := f.xHeight.toNat
  let measured := match f.xInkTop.get with
    | some hi => if 0 < hi then hi.toNat else declared
    | none => declared
  (measured.min f.unitsPerEm).max 1

/-- The vertical size variants of glyph `g` — `(glyph id, advance height)`
in increasing size per the MATH spec — or empty when the face grows it no
further. -/
def Font.vertVariants (f : Font) (g : Nat) : Array (Nat × Int) :=
  match f.mathVariants.find? (·.1 == g) with
  | some (_, vs) => vs
  | none => #[]

/-- The horizontal size variants of glyph `g` — `(glyph id, advance
width)` in increasing size — or empty when the face stretches it no
further. -/
def Font.horizVariants (f : Font) (g : Nat) : Array (Nat × Int) :=
  match f.mathHorizVariants.find? (·.1 == g) with
  | some (_, vs) => vs
  | none => #[]

/-- Where a top accent attaches on glyph `g`, in design units from the
origin, clamped into the glyph's advance: the MATH table's value where the
coverage carries one, else half the advance — the spec's own default for
uncovered glyphs. The clamp is what `Math.accentAttach_covers` quantifies
over: the spec declares no bound on the value, and placement must stay
within the advance for every font, not only well-behaved ones. -/
def Font.topAccentX (f : Font) (g : Nat) : Int :=
  let w : Int := f.widths[g]?.getD 0
  match f.mathTopAccent.find? (·.1 == g) with
  | some (_, x) => min (max x 0) w
  | none => w / 2

/-- Accent placement stays within the base glyph's advance: the attachment
point — where the accent's own reference lands — lies in `[0, advance]`
for every glyph of every parsed font. The MATH spec declares no bound on
the table's value, so the bound is imposed at the read (`topAccentX`
clamps), the same sanitize-then-prove shape as `ScriptScales.clamp`. -/
theorem Font.topAccentX_covers (f : Font) (g : Nat) :
    0 ≤ f.topAccentX g ∧ f.topAccentX g ≤ (f.widths[g]?.getD 0 : Int) := by
  unfold Font.topAccentX
  dsimp only
  split <;> omega

/-- The accent mark's own attachment x, unclamped: a combining mark may
carry zero advance and attach inside or left of its ink, which the
base-side clamp would destroy; half the advance where the coverage says
nothing, the spec's default. -/
def Font.markAttachX (f : Font) (g : Nat) : Int :=
  match f.mathTopAccent.find? (·.1 == g) with
  | some (_, x) => x
  | none => (f.widths[g]?.getD 0 : Int) / 2

/-- This face's normalized underline band: `(position, thickness)` in font
units. See `underlineBand`. -/
def Font.band (f : Font) : Int × Int :=
  underlineBand (f.unitsPerEm : Int) f.descent f.underlinePosition
    f.underlineThickness

/-- The faces a document typesets with. Index 0 is always the body regular
face; `Style` resolves to an index at layout time. -/
structure FontSet where
  fonts : Array Font
  /-- (family slot, weight, italic) → index into `fonts`. The weight is the
  CSS/OpenType number of an NFSS series (`Ir.Weight.css`; 400 regular,
  700 bold), spelled `Nat` here because this module sits below the IR. -/
  index : Array ((Nat × Nat × Bool) × Nat) := #[]
  /-- Per-scalar fallback, precomputed by the driver from the document's own
  text: the font that sets a glyph when the styled face lacks it — the first
  declared face that covers the scalar, in declaration order, else the first
  covering scanned face (loaded at the end of `fonts`). Layout consults it
  only on a missing glyph, so a document whose faces cover their text is
  untouched by construction. -/
  fallback : Array (Char × Nat) := #[]
  /-- Index of the document's math face: declared, resolved, and carrying a
  MATH table. `none` sets a formula as its glyph text (`Ir.formulaFloor`)
  with the W0003 warning. -/
  math : Option Nat := none
  /-- Per-face deflated program bytes, filled by the driver through its
  content-hash cache (`deflateCached` in the driver): `zdata[i]`, when
  present, is the compressed stream of the program the PDF embeds for face
  `i` on these pages (`Pdf.facePrograms`) — one document's subset is the
  same bytes build after build, so its deflate is paid once per content,
  not per build. Empty (the default; every test constructor) means the PDF
  writer compresses inline. -/
  zdata : Array (Option ByteArray) := #[]
  deriving Inhabited

namespace FontSet

def body (fs : FontSet) : Font := fs.fonts[0]!

def get (fs : FontSet) (i : Nat) : Font := fs.fonts[i]?.getD fs.body

/-- The math face and its constants, when the document has a usable one. -/
def mathFont? (fs : FontSet) : Option (Nat × Font × MathConsts) := do
  let i ← fs.math
  let f ← fs.fonts[i]?
  let c ← f.math
  pure (i, f, c)

/-- Slot 0 = body/serif, 1 = sans, 2 = mono; `weight` is the CSS number of
the requested series. The driver resolves an index entry for every key the
document can ask for (its declared faces and the weights its styles use),
so the exact arm answers; a key it never saw falls to the slot's regular,
then to face 0 — never a hole. -/
def lookup (fs : FontSet) (slot : Nat) (weight : Nat) (italic : Bool) : Nat :=
  match fs.index.find? fun e => e.1 == (slot, weight, italic) with
  | some (_, i) => i
  | none =>
    match fs.index.find? fun e => e.1 == (slot, 400, false) with
    | some (_, i) => i
    | none => 0

/-- `index_total`: every `(slot, weight, italic)` resolves to some face —
the fallback chain ends at face 0, so with a well-formed index (every
entry in bounds, which `get`'s clamp also defends) the answer always
names a font of the set. The nearest-weight half of totality lives in
`FontDb.pickWeighted_total`: the driver's resolution never returns
empty-handed for a family that has any face at all. -/
theorem index_total (fs : FontSet) (h0 : 0 < fs.fonts.size)
    (hwf : ∀ e ∈ fs.index, e.2 < fs.fonts.size) (slot weight : Nat)
    (italic : Bool) : fs.lookup slot weight italic < fs.fonts.size := by
  unfold lookup
  split
  next heq => exact hwf _ (Array.mem_of_find?_eq_some heq)
  next =>
    split
    next heq => exact hwf _ (Array.mem_of_find?_eq_some heq)
    next => exact h0

/-- **Does this slot resolve to the body face?** Slot 2 is mono, and a
document that declares no mono family gets one: `lookup` falls through the
slot's regular to face 0, so a `\texttt`, `\url` or `verbatim` run sets in the
body face.

That fallback is correct — there is nothing else to set it in — but it is a
`degraded` loss and it has never been named. Measured from the bytes on a
synthetic document carrying all three constructs: with `mono` declared the PDF
embeds two faces, without it one, and the diagnostics are empty in both cases.
`pdffonts` can see the loss and the reader cannot.

The predicate is here rather than at a call site because `FontSet` is what
knows: the driver resolves the index, and whether two slots landed on one face
is a fact about the resolved set. Emission belongs to the driver, which is the
one place that holds both the document's `\fonts` declaration and the resolved
index (effects as data: this is the fact, not the diagnostic). -/
def slotCollapsed (fs : FontSet) (slot : Nat) : Bool :=
  slot != 0 && fs.lookup slot 400 false == fs.lookup 0 400 false

/-- Slot 0 is the body face, so asking whether it collapsed onto itself is
not a question this predicate answers — it is the reference. Keeps a caller
from reading "the body face collapsed" out of a vacuous truth. -/
theorem slotCollapsed_body (fs : FontSet) : fs.slotCollapsed 0 = false := by
  simp [slotCollapsed]

/-- **A collapsed slot is exactly a slot that resolves where the body does.**
The predicate is the equality it looks like, for every slot past the body, so
a diagnostic resting on it names the real condition rather than a proxy. -/
theorem slotCollapsed_exact (fs : FontSet) (slot : Nat) (h : slot != 0) :
    fs.slotCollapsed slot = (fs.lookup slot 400 false == fs.lookup 0 400 false) := by
  simp [slotCollapsed, h]

/-- **Is the face this slot resolved to fixed-pitch?** The face's own
answer (`post.isFixedPitch`), read through the same `lookup` the setter
uses, so the question is about the face that sets the run and not about the
family that was asked for.

A slot index says which face; it does not say what that face is. A document
whose body family is monospace sets `\texttt` in a fixed-pitch face while
slot 2 reads as collapsed, and a report resting on the index alone tells
that reader a loss it cannot see. This is the predicate that separates the
two, and `HtmlDoc.genericFor` already reads the same field for the CSS
generic — one source for "is this monospace", not two. -/
def slotIsFixedPitch (fs : FontSet) (slot : Nat) : Bool :=
  match fs.fonts[fs.lookup slot 400 false]? with
  | some f => f.isFixedPitch
  | none => false

/-- **A slot's fixed-pitch answer is the resolved face's own.** No index
arithmetic between the question and the face: whichever face `lookup` names
is the one whose `post` flag answers, so a caller cannot read a pitch off
the wrong face. -/
theorem slotIsFixedPitch_exact (fs : FontSet) (slot : Nat)
    (h : fs.lookup slot 400 false < fs.fonts.size) :
    fs.slotIsFixedPitch slot = (fs.fonts[fs.lookup slot 400 false]).isFixedPitch := by
  simp [slotIsFixedPitch, Array.getElem?_eq_getElem h]

/-- The font that sets a glyph the styled face lacks, if any face can. -/
def fallbackFor (fs : FontSet) (c : Char) : Option Nat :=
  (fs.fallback.find? (·.1 == c)).map (·.2)

end FontSet
end LeanTex.Core.Font
