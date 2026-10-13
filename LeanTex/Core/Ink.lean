module

import LeanTex.Core.GlyphList

namespace LeanTex.Core.Ink

/-! Glyph outlines decoded from TrueType and CFF data, total over arbitrary bytes: ink hulls and
the ink crossing the underline band; an undecodable glyph is `none`. -/

/-- A bounded byte read: 0 out of range, never a panic. -/
public def u8 (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (b[i]).toNat else 0

public def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i + 1)

public def u32 (b : ByteArray) (i : Nat) : Nat :=
  ((u8 b i * 256 + u8 b (i + 1)) * 256 + u8 b (i + 2)) * 256 + u8 b (i + 3)

def i8 (b : ByteArray) (i : Nat) : Int :=
  let v := u8 b i
  if v ≥ 0x80 then (v : Int) - 0x100 else v

public def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 0x8000 then (v : Int) - 0x10000 else v

public def i32 (b : ByteArray) (i : Nat) : Int :=
  let v := u32 b i
  if v ≥ 0x80000000 then (v : Int) - 0x100000000 else v

public structure Table where
  offset : Nat
  length : Nat

public def findTable (b : ByteArray) (tag : String) : Option Table := Id.run do
  if b.size < 12 then
    return none
  let n := u16 b 4
  let tagBytes := tag.toUTF8
  for k in [0:n] do
    let entry := 12 + 16 * k
    if entry + 16 > b.size then
      return none
    if b.extract entry (entry + 4) == tagBytes then
      return some ⟨u32 b (entry + 8), u32 b (entry + 12)⟩
  return none

/-- Does a table's declared extent fit inside the file? -/
public def fits (b : ByteArray) (t : Table) : Bool :=
  t.offset + t.length ≤ b.size

/-- One outline command, absolute font-unit coordinates. -/
public inductive Cmd where
  | move (x y : Int)
  | line (x y : Int)
  | quad (cx cy x y : Int)
  | cube (c1x c1y c2x c2y x y : Int)
  deriving Inhabited, BEq

/-- A decoded outline: its commands and the lowest y any point, control points included, reaches. -/
public structure Outline where
  cmds : Array Cmd
  minY : Int

/-- Straight edges in doubled coordinates, each curve cut into eight chords, every vertex at an
even y. -/
private def edgesOf (cmds : Array Cmd) : Array (Int × Int × Int × Int) := Id.run do
  let mut out : Array (Int × Int × Int × Int) := #[]
  let mut cx : Int := 0
  let mut cy : Int := 0
  let mut sx : Int := 0
  let mut sy : Int := 0
  let mut opened := false
  for c in cmds do
    match c with
    | .move x y =>
      if opened && (cx != sx || cy != sy) then
        out := out.push (cx, cy, sx, sy)
      cx := 2 * x
      cy := 2 * y
      sx := cx
      sy := cy
      opened := true
    | .line x y =>
      out := out.push (cx, cy, 2 * x, 2 * y)
      cx := 2 * x
      cy := 2 * y
    | .quad qx qy x y =>
      let x0 := cx
      let y0 := cy
      let x1 := 2 * qx
      let y1 := 2 * qy
      let x2 := 2 * x
      let y2 := 2 * y
      for k in [1:9] do
        let k : Int := k
        let a := (8 - k) * (8 - k)
        let m := 2 * k * (8 - k)
        let z := k * k
        let px := 2 * ((a * x0 + m * x1 + z * x2) / 128)
        let py := 2 * ((a * y0 + m * y1 + z * y2) / 128)
        out := out.push (cx, cy, px, py)
        cx := px
        cy := py
    | .cube c1x c1y c2x c2y x y =>
      let x0 := cx
      let y0 := cy
      let x1 := 2 * c1x
      let y1 := 2 * c1y
      let x2 := 2 * c2x
      let y2 := 2 * c2y
      let x3 := 2 * x
      let y3 := 2 * y
      for k in [1:9] do
        let k : Int := k
        let a := (8 - k) * (8 - k) * (8 - k)
        let m := 3 * k * (8 - k) * (8 - k)
        let z := 3 * k * k * (8 - k)
        let w := k * k * k
        let px := 2 * ((a * x0 + m * x1 + z * x2 + w * x3) / 1024)
        let py := 2 * ((a * y0 + m * y1 + z * y2 + w * y3) / 1024)
        out := out.push (cx, cy, px, py)
        cx := px
        cy := py
  if opened && (cx != sx || cy != sy) then
    out := out.push (cx, cy, sx, sy)
  return out

/-- Fill intervals along the horizontal line `y` (doubled coordinates, odd so
no vertex lies on it), by nonzero winding. -/
private def fillAt (edges : Array (Int × Int × Int × Int)) (y : Int) :
    Array (Int × Int) := Id.run do
  let mut xs : Array (Int × Int) := #[]
  for (x0, y0, x1, y1) in edges do
    if (y0 < y && y < y1) || (y1 < y && y < y0) then
      let cx := x0 + (x1 - x0) * (y - y0) / (y1 - y0)
      xs := xs.push (cx, if y0 < y1 then 1 else -1)
  let sorted := xs.qsort fun a b => a.1 < b.1
  let mut out : Array (Int × Int) := #[]
  let mut wind : Int := 0
  let mut lo : Int := 0
  for (x, d) in sorted do
    let w := wind + d
    if wind == 0 && w != 0 then
      lo := x
    if wind != 0 && w == 0 then
      out := out.push (lo, x)
    wind := w
  return out

/-- Merged x-intervals in font units of ink inside `[bandLo, bandHi]`, exact up to the
eight-chord flattening. -/
public def bandIntervals (o : Outline) (bandLo bandHi : Int) : Array (Int × Int) := Id.run do
  if o.minY ≥ bandHi then
    return #[]
  let edges := edgesOf o.cmds
  if edges.isEmpty then
    return #[]
  -- Doubled coordinates throughout, matching the edges.
  let lo2 := 2 * bandLo
  let hi2 := 2 * bandHi
  let mut iv : Array (Int × Int) := #[]
  for (x0, y0, x1, y1) in edges do
    let ylo := min y0 y1
    let yhi := max y0 y1
    if yhi ≥ lo2 && ylo ≤ hi2 then
      if y0 == y1 then
        iv := iv.push (min x0 x1, max x0 x1)
      else
        let xAt (y : Int) : Int := x0 + (x1 - x0) * (y - y0) / (y1 - y0)
        let xa := xAt (max ylo lo2)
        let xb := xAt (min yhi hi2)
        iv := iv.push (min xa xb, max xa xb)
  let mid := lo2 + (hi2 - lo2) / 2
  for (a, b) in fillAt edges (if mid % 2 == 0 then mid + 1 else mid) do
    iv := iv.push (a, b)
  let sorted := iv.qsort fun a b => a.1 < b.1
  let mut out : Array (Int × Int) := #[]
  for (a2, b2) in sorted do
    -- Halve back to font units, rounding outward.
    let a := a2.fdiv 2
    let b := (b2 + 1).fdiv 2
    match out.back? with
    | some (pa, pb) =>
      if a ≤ pb then out := out.pop.push (pa, max pb b)
      else out := out.push (a, b)
    | none => out := out.push (a, b)
  return out

/-- A composite component's 2×2 transform in F2Dot14 (÷16384) plus a
font-unit offset. -/
private structure Xf where
  a : Int := 16384
  b : Int := 0
  c : Int := 0
  d : Int := 16384
  dx : Int := 0
  dy : Int := 0

private def Xf.apply (t : Xf) (x y : Int) : Int × Int :=
  ((t.a * x + t.c * y) / 16384 + t.dx, (t.b * x + t.d * y) / 16384 + t.dy)

private def Xf.compose (p c : Xf) : Xf :=
  let (dx, dy) := p.apply c.dx c.dy
  { a := (p.a * c.a + p.c * c.b) / 16384
    b := (p.b * c.a + p.d * c.b) / 16384
    c := (p.a * c.c + p.c * c.d) / 16384
    d := (p.b * c.c + p.d * c.d) / 16384
    dx := dx
    dy := dy }

/-- One contour's commands from its points: TrueType quadratics with implied
on-curve midpoints between consecutive off-curve controls. -/
private def contourCmds (pts : Array (Int × Int × Bool)) (s e : Nat)
    (acc : Array Cmd) : Array Cmd := Id.run do
  let n := e + 1 - s
  if n == 0 then
    return acc
  let pt (k : Nat) : Int × Int × Bool := pts[s + k % n]?.getD (0, 0, true)
  let mut startIdx := 0
  let mut found := false
  for k in [0:n] do
    if !found && (pt k).2.2 then
      startIdx := k
      found := true
  let start : Int × Int :=
    if found then
      let (x, y, _) := pt startIdx
      (x, y)
    else
      let (x0, y0, _) := pt 0
      let (x1, y1, _) := pt (n - 1)
      ((x0 + x1) / 2, (y0 + y1) / 2)
  let mut acc := acc.push (.move start.1 start.2)
  let mut pending : Option (Int × Int) := none
  let steps := if found then n - 1 else n
  for j in [0:steps] do
    let idx := if found then startIdx + 1 + j else j
    let (qx, qy, on) := pt idx
    match pending with
    | some (px, py) =>
      if on then
        acc := acc.push (.quad px py qx qy)
        pending := none
      else
        acc := acc.push (.quad px py ((px + qx) / 2) ((py + qy) / 2))
        pending := some (qx, qy)
    | none =>
      if on then
        acc := acc.push (.line qx qy)
      else
        pending := some (qx, qy)
  match pending with
  | some (px, py) => acc := acc.push (.quad px py start.1 start.2)
  | none => acc := acc.push (.line start.1 start.2)
  return acc

/-- Decode a simple glyph at `off` under `t` onto `acc`; a read past `lim` or a budget makes it
`none`. -/
private def simpleOutline (b : ByteArray) (off lim : Nat) (t : Xf)
    (acc : Array Cmd) (minY0 : Int) : Option (Array Cmd × Int) := Id.run do
  let nc := (i16 b off).toNat
  if nc > 128 then
    return none
  let mut ends : Array Nat := #[]
  for k in [0:nc] do
    ends := ends.push (u16 b (off + 10 + 2 * k))
  let nPts := match ends.back? with
    | some e => e + 1
    | none => 0
  if nPts > 4096 then
    return none
  if nPts == 0 then
    return some (acc, minY0)
  let insLen := u16 b (off + 10 + 2 * nc)
  let mut p := off + 12 + 2 * nc + insLen
  let mut flags : Array Nat := #[]
  for _ in [0:nPts] do
    if flags.size ≥ nPts then
      break
    let f := u8 b p
    p := p + 1
    flags := flags.push f
    if f &&& 8 != 0 then
      let r := u8 b p
      p := p + 1
      for _ in [0:r] do
        if flags.size < nPts then
          flags := flags.push f
  let mut xs : Array Int := #[]
  let mut x : Int := 0
  for f in flags do
    if f &&& 2 != 0 then
      let d : Int := u8 b p
      p := p + 1
      x := x + (if f &&& 16 != 0 then d else -d)
    else if f &&& 16 == 0 then
      x := x + i16 b p
      p := p + 2
    xs := xs.push x
  let mut ys : Array Int := #[]
  let mut y : Int := 0
  for f in flags do
    if f &&& 4 != 0 then
      let d : Int := u8 b p
      p := p + 1
      y := y + (if f &&& 32 != 0 then d else -d)
    else if f &&& 32 == 0 then
      y := y + i16 b p
      p := p + 2
    ys := ys.push y
  -- p only ever advances, so one check catches any read past the slice.
  if p > lim then
    return none
  let mut pts : Array (Int × Int × Bool) := #[]
  let mut minY := minY0
  for k in [0:nPts] do
    let (px, py) := t.apply (xs[k]?.getD 0) (ys[k]?.getD 0)
    minY := min minY py
    pts := pts.push (px, py, (flags[k]?.getD 0) &&& 1 != 0)
  let mut acc := acc
  let mut s := 0
  for e in ends do
    let e := min e (nPts - 1)
    if s ≤ e then
      acc := contourCmds pts s e acc
      s := e + 1
  return some (acc, minY)

/-- Decode glyph `g` of a TrueType font; `none` for anything the decoder does not cover. -/
private def glyfOutline (b : ByteArray) (glyf loca : Table) (long : Bool)
    (numGlyphs g : Nat) : Option Outline := Id.run do
  let offAt (i : Nat) : Nat :=
    if long then u32 b (loca.offset + 4 * i) else 2 * u16 b (loca.offset + 2 * i)
  let mut work : Array (Nat × Xf) := #[(g, {})]
  let mut cmds : Array Cmd := #[]
  let mut minY : Int := 0x40000000
  let mut bad := false
  for _ in [0:64] do
    if bad || work.isEmpty then
      break
    let (gid, t) := work.back?.getD (0, {})
    work := work.pop
    if gid ≥ numGlyphs then
      bad := true
      continue
    let o1 := offAt gid
    let o2 := offAt (gid + 1)
    if o2 == o1 then
      continue
    if o2 < o1 || o2 > glyf.length || o1 + 10 > glyf.length then
      bad := true
      continue
    let base := glyf.offset + o1
    let lim := glyf.offset + o2
    if i16 b base ≥ 0 then
      match simpleOutline b base lim t cmds minY with
      | some (cs, my) =>
        cmds := cs
        minY := my
      | none => bad := true
    else
      let mut p := base + 10
      let mut more := true
      for _ in [0:16] do
        if !more || bad then
          break
        let flags := u16 b p
        let gi := u16 b (p + 2)
        p := p + 4
        let words := flags &&& 1 != 0
        if flags &&& 2 == 0 then
          bad := true
        else
          let (dx, dy) :=
            if words then (i16 b p, i16 b (p + 2))
            else (i8 b p, i8 b (p + 1))
          p := p + (if words then 4 else 2)
          let mut child : Xf := { dx := dx, dy := dy }
          if flags &&& 8 != 0 then
            let sc := i16 b p
            p := p + 2
            child := { child with a := sc, d := sc }
          else if flags &&& 64 != 0 then
            child := { child with a := i16 b p, d := i16 b (p + 2) }
            p := p + 4
          else if flags &&& 128 != 0 then
            child := { child with
              a := i16 b p
              b := i16 b (p + 2)
              c := i16 b (p + 4)
              d := i16 b (p + 6) }
            p := p + 8
          work := work.push (gi, t.compose child)
          more := flags &&& 32 != 0
      if more then
        bad := true
      if p > lim then
        bad := true
  if bad || !work.isEmpty then
    return none
  return some ⟨cmds, minY⟩

/-- Entries of a CFF INDEX as absolute (start, end) byte ranges, plus the
offset just past the INDEX. -/
public def parseIndex (b : ByteArray) (pos : Nat) :
    Option (Array (Nat × Nat) × Nat) := Id.run do
  if pos + 2 > b.size then
    return none
  let count := u16 b pos
  if count == 0 then
    return some (#[], pos + 2)
  let offSize := u8 b (pos + 2)
  if offSize == 0 || offSize > 4 then
    return none
  let offBase := pos + 3
  let readOff (i : Nat) : Nat := Id.run do
    let mut v := 0
    for k in [0:offSize] do
      v := v * 256 + u8 b (offBase + i * offSize + k)
    return v
  let dataBase := offBase + (count + 1) * offSize - 1
  if dataBase + readOff count > b.size then
    return none
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:count] do
    let a := readOff i
    let z := readOff (i + 1)
    if a == 0 || z < a then
      return none
    out := out.push (dataBase + a, dataBase + z)
  return some (out, dataBase + readOff count)

private structure CffDict where
  charStrings : Nat := 0
  privOff : Nat := 0
  privSize : Nat := 0
  subrs : Nat := 0
  cid : Bool := false
  cstype : Int := 2
  charset : Nat := 0
  encoding : Nat := 0
  fdArray : Nat := 0
  fdSelect : Nat := 0
  matrix : Option (Array Rat) := none

/-- A DICT real (Technical Note #5176 Table 5), nibbles up to the `f` terminator: its value and
the position after it. -/
private def dictReal (b : ByteArray) (p e : Nat) : Rat × Nat := Id.run do
  let mut q := p
  let mut neg := false
  let mut ip : Nat := 0
  let mut fr : Nat := 0
  let mut scale : Nat := 1
  let mut afterPoint := false
  let mut expo : Nat := 0
  let mut expoNeg := false
  let mut inExp := false
  let mut fin := false
  for _ in [0:e - p + 1] do
    if fin || q ≥ e then
      break
    let v := u8 b q
    q := q + 1
    for nib in [v / 16, v % 16] do
      if !fin then
        if nib ≤ 9 then
          if inExp then expo := expo * 10 + nib
          else if afterPoint then
            fr := fr * 10 + nib
            scale := scale * 10
          else ip := ip * 10 + nib
        else if nib == 0xa then afterPoint := true
        else if nib == 0xb then inExp := true
        else if nib == 0xc then
          inExp := true
          expoNeg := true
        else if nib == 0xe then neg := true
        else if nib == 0xf then fin := true
  let m : Rat := (ip : Rat) + mkRat fr scale
  let p10 : Rat := ((10 ^ (min expo 64) : Nat) : Rat)
  let v := if expoNeg then m / p10 else m * p10
  return (if neg then -v else v, q)

/-- The CFF DICT operators this consumer needs (Technical Note #5176 Tables 9 and 10). -/
private def parseDict (b : ByteArray) (s e : Nat) : CffDict := Id.run do
  let mut ops : Array Rat := #[]
  let mut d : CffDict := {}
  let mut p := s
  let natOf (r : Rat) : Nat := r.floor.toNat
  for _ in [0:e - s] do
    if p ≥ e then
      break
    let b0 := u8 b p
    if b0 ≥ 32 && b0 ≤ 246 then
      ops := ops.push ((b0 : Int) - 139)
      p := p + 1
    else if b0 ≥ 247 && b0 ≤ 250 then
      ops := ops.push (((b0 : Int) - 247) * 256 + (u8 b (p + 1) : Int) + 108)
      p := p + 2
    else if b0 ≥ 251 && b0 ≤ 254 then
      ops := ops.push (-((b0 : Int) - 251) * 256 - (u8 b (p + 1) : Int) - 108)
      p := p + 2
    else if b0 == 28 then
      ops := ops.push (i16 b (p + 1))
      p := p + 3
    else if b0 == 29 then
      ops := ops.push (i32 b (p + 1))
      p := p + 5
    else if b0 == 30 then
      let (v, q) := dictReal b (p + 1) e
      ops := ops.push v
      p := q
    else if b0 == 12 then
      let b1 := u8 b (p + 1)
      p := p + 2
      if b1 == 6 then
        d := { d with cstype := (ops.back?.getD 2).floor }
      else if b1 == 7 then
        if ops.size == 6 then d := { d with matrix := some ops }
      else if b1 == 30 then
        d := { d with cid := true }
      else if b1 == 36 then
        d := { d with cid := true, fdArray := natOf (ops.back?.getD 0) }
      else if b1 == 37 then
        d := { d with cid := true, fdSelect := natOf (ops.back?.getD 0) }
      ops := #[]
    else
      p := p + 1
      if b0 == 15 then
        d := { d with charset := natOf (ops.back?.getD 0) }
      else if b0 == 16 then
        d := { d with encoding := natOf (ops.back?.getD 0) }
      else if b0 == 17 then
        d := { d with charStrings := natOf (ops.back?.getD 0) }
      else if b0 == 18 then
        if ops.size ≥ 2 then
          d := { d with
            privSize := natOf (ops[ops.size - 2]?.getD 0)
            privOff := natOf (ops.back?.getD 0) }
      else if b0 == 19 then
        d := { d with subrs := natOf (ops.back?.getD 0) }
      ops := #[]
  return d

/-- The local subroutines a font dictionary's private dictionary names. -/
private def localSubrs (b : ByteArray) (d : CffDict) : Array (Nat × Nat) :=
  if d.privSize > 0 && d.privOff + d.privSize ≤ b.size then
    let pd := parseDict b d.privOff (d.privOff + d.privSize)
    if pd.subrs > 0 then
      match parseIndex b (d.privOff + pd.subrs) with
      | some (ls, _) => ls
      | none => #[]
    else #[]
  else #[]

/-- A charset (Technical Note #5176 §13): each glyph's string identifier or CID; the predefined
charsets read as the identity. -/
private def parseCharset (b : ByteArray) (off n : Nat) : Array Nat := Id.run do
  if off ≤ 2 then
    return Array.range n
  let fmt := u8 b off
  let mut out : Array Nat := #[0]
  let mut p := off + 1
  if fmt == 0 then
    for _ in [1:n] do
      out := out.push (u16 b p)
      p := p + 2
  else if fmt == 1 || fmt == 2 then
    for _ in [0:n] do
      if out.size ≥ n || p ≥ b.size then
        break
      let first := u16 b p
      let left := if fmt == 1 then u8 b (p + 2) else u16 b (p + 2)
      p := p + (if fmt == 1 then 3 else 4)
      for k in [0:left + 1] do
        if out.size < n then
          out := out.push (first + k)
  return out

/-- A name-keyed CFF's own encoding (Technical Note #5176 §12): each of the 256 codes' glyph. -/
private def parseEncoding (b : ByteArray) (off : Nat) (charset : Array Nat) : Array (Option Nat) := Id.run do
  let bySid (sid : Nat) : Option Nat := charset.findIdx? (· == sid)
  if off == 0 then
    return (Array.range 256).map fun c => (GlyphList.standardSid c).bind bySid
  if off == 1 then
    return (Array.range 256).map fun c =>
      let n := GlyphList.expertName c
      if n.isEmpty then none else (GlyphList.cffSid? n).bind bySid
  let mut enc : Array (Option Nat) := Array.replicate 256 none
  let fmt := u8 b off
  let n := u8 b (off + 1)
  let mut p := off + 2
  if fmt % 128 == 0 then
    for i in [0:n] do
      let code := u8 b (p + i)
      if i + 1 < charset.size then enc := enc.set! code (some (i + 1))
    p := p + n
  else if fmt % 128 == 1 then
    let mut gid := 1
    for _ in [0:n] do
      let first := u8 b p
      let left := u8 b (p + 1)
      p := p + 2
      for k in [0:left + 1] do
        if gid < charset.size && first + k < 256 then enc := enc.set! (first + k) (some gid)
        gid := gid + 1
  else
    return enc
  if fmt ≥ 128 then
    let nSups := u8 b p
    for i in [0:nSups] do
      let q := p + 1 + 3 * i
      enc := enc.set! (u8 b q) (bySid (u16 b (q + 1)))
  return enc

/-- An FDSelect (Technical Note #5176 §19): each glyph's font dictionary,
formats 0 and 3. -/
private def parseFdSelect (b : ByteArray) (off n : Nat) : Array Nat := Id.run do
  let fmt := u8 b off
  if fmt == 0 then
    return (Array.range n).map fun g => u8 b (off + 1 + g)
  if fmt != 3 then
    return #[]
  let nRanges := u16 b (off + 1)
  let mut out : Array Nat := #[]
  for r in [0:nRanges] do
    let first := u16 b (off + 3 + 3 * r)
    let fd := u8 b (off + 5 + 3 * r)
    let next := u16 b (off + 6 + 3 * r)
    for g in [first:next] do
      if out.size == g && g < n then
        out := out.push fd
  return out

/-- Prepared CFF data: charstrings, subroutines, charset, and a CID-keyed font's dictionaries. -/
public structure Cff where
  private charStrings : Array (Nat × Nat)
  private gsubrs : Array (Nat × Nat)
  private lsubrs : Array (Nat × Nat)
  private fdOf : Array Nat
  private fdSubrs : Array (Array (Nat × Nat))
  private fdMatrix : Array (Option (Array Rat))
  private charset : Array Nat
  private strings : Array (Nat × Nat)
  /-- A name-keyed font's own encoding: each code's glyph. -/
  private builtin : Array (Option Nat)
  /-- Whether the font is CID-keyed (its Top DICT has `ROS`). -/
  cid : Bool
  /-- The Top DICT's font matrix: glyph space to text space. -/
  matrix : Array Rat

/-- The CFF data at the start of `b`, name-keyed or CID-keyed; `none` for a charstring type
other than 2 or anything malformed. -/
private def parseCff (b : ByteArray) : Option Cff := do
  let hdrSize := u8 b 2
  let (_, p1) ← parseIndex b hdrSize
  let (tops, p2) ← parseIndex b p1
  let (strings, p3) ← parseIndex b p2
  let (gsubrs, _) ← parseIndex b p3
  let (ts, te) ← tops[0]?
  let d := parseDict b ts te
  guard (d.cstype == 2)
  let (cs, _) ← parseIndex b d.charStrings
  let n := cs.size
  let matrix := d.matrix.getD #[mkRat 1 1000, 0, 0, mkRat 1 1000, 0, 0]
  if d.cid then
    let (fds, _) ← parseIndex b d.fdArray
    let fdDicts := fds.map fun (s, e) => parseDict b s e
    return { charStrings := cs, gsubrs, lsubrs := #[], fdOf := parseFdSelect b d.fdSelect n
             fdSubrs := fdDicts.map (localSubrs b), fdMatrix := fdDicts.map (·.matrix)
             charset := parseCharset b d.charset n, strings, builtin := #[], cid := true, matrix }
  let charset := parseCharset b d.charset n
  return { charStrings := cs, gsubrs, lsubrs := localSubrs b d, fdOf := #[], fdSubrs := #[]
           fdMatrix := #[], charset, strings, builtin := parseEncoding b d.encoding charset
           cid := false, matrix }

/-- Run one Type 2 charstring into an outline under subroutine frames and a step budget; `none`
where uncovered. -/
private def runCharstring (b : ByteArray) (gsubrs lsubrs : Array (Nat × Nat)) (cs : Nat × Nat) :
    Option (Outline × Option (Int × Int × Nat × Nat)) := Id.run do
  let biasOf (n : Nat) : Int :=
    if n < 1240 then 107 else if n < 33900 then 1131 else 32768
  let mut stk : Array Int := #[]
  let mut cmds : Array Cmd := #[]
  let mut x : Int := 0
  let mut y : Int := 0
  let mut minY : Int := 0x40000000
  let mut nStems : Nat := 0
  let mut frames : Array (Nat × Nat) := #[]
  let mut pc := cs.1
  let mut lim := cs.2
  let mut bad := false
  let mut done := false
  let mut seac : Option (Int × Int × Nat × Nat) := none
  for _ in [0:65536] do
    if bad || done then
      break
    if pc ≥ lim then
      match frames.back? with
      | some (rp, rl) =>
        frames := frames.pop
        pc := rp
        lim := rl
      | none => done := true
    else
    let b0 := u8 b pc
    if b0 == 28 then
      stk := stk.push (i16 b (pc + 1))
      pc := pc + 3
    else if b0 ≥ 32 then
      if b0 ≤ 246 then
        stk := stk.push ((b0 : Int) - 139)
        pc := pc + 1
      else if b0 ≤ 250 then
        stk := stk.push (((b0 : Int) - 247) * 256 + (u8 b (pc + 1) : Int) + 108)
        pc := pc + 2
      else if b0 ≤ 254 then
        stk := stk.push (-((b0 : Int) - 251) * 256 - (u8 b (pc + 1) : Int) - 108)
        pc := pc + 2
      else
        stk := stk.push ((i32 b (pc + 1) + 32768) / 65536)
        pc := pc + 5
    else
      let n := stk.size
      let arg (i : Nat) : Int := stk[i]?.getD 0
      if b0 == 1 || b0 == 3 || b0 == 18 || b0 == 23 then
        nStems := nStems + n / 2
        stk := #[]
        pc := pc + 1
      else if b0 == 19 || b0 == 20 then
        nStems := nStems + n / 2
        stk := #[]
        pc := pc + 1 + (nStems + 7) / 8
      else if b0 == 21 || b0 == 22 || b0 == 4 then
        -- A leading width may pad the front, so moveto arguments read from the end.
        if b0 == 21 then
          x := x + arg (n - 2)
          y := y + arg (n - 1)
        else if b0 == 22 then
          x := x + arg (n - 1)
        else
          y := y + arg (n - 1)
        cmds := cmds.push (.move x y)
        minY := min minY y
        stk := #[]
        pc := pc + 1
      else if b0 == 5 then
        for k in [0:n / 2] do
          x := x + arg (2 * k)
          y := y + arg (2 * k + 1)
          cmds := cmds.push (.line x y)
          minY := min minY y
        stk := #[]
        pc := pc + 1
      else if b0 == 6 || b0 == 7 then
        let mut horiz := b0 == 6
        for k in [0:n] do
          if horiz then
            x := x + arg k
          else
            y := y + arg k
          cmds := cmds.push (.line x y)
          minY := min minY y
          horiz := !horiz
        stk := #[]
        pc := pc + 1
      else if b0 == 8 || b0 == 24 || b0 == 25 then
        let curves := if b0 == 8 then n / 6 else (n - 2) / 6
        -- rlinecurve (25) leads with lines instead of ending with one
        if b0 == 25 then
          let lines := (n - 6) / 2
          for k in [0:lines] do
            x := x + arg (2 * k)
            y := y + arg (2 * k + 1)
            cmds := cmds.push (.line x y)
            minY := min minY y
          let i := 2 * lines
          let c1x := x + arg i
          let c1y := y + arg (i + 1)
          let c2x := c1x + arg (i + 2)
          let c2y := c1y + arg (i + 3)
          x := c2x + arg (i + 4)
          y := c2y + arg (i + 5)
          cmds := cmds.push (.cube c1x c1y c2x c2y x y)
          minY := min minY (min c1y (min c2y y))
        else
          for k in [0:curves] do
            let i := 6 * k
            let c1x := x + arg i
            let c1y := y + arg (i + 1)
            let c2x := c1x + arg (i + 2)
            let c2y := c1y + arg (i + 3)
            x := c2x + arg (i + 4)
            y := c2y + arg (i + 5)
            cmds := cmds.push (.cube c1x c1y c2x c2y x y)
            minY := min minY (min c1y (min c2y y))
          if b0 == 24 then
            x := x + arg (6 * curves)
            y := y + arg (6 * curves + 1)
            cmds := cmds.push (.line x y)
            minY := min minY y
        stk := #[]
        pc := pc + 1
      else if b0 == 26 || b0 == 27 then
        let lead := if n % 4 == 1 then 1 else 0
        let d1 := if lead == 1 then arg 0 else 0
        for k in [0:(n - lead) / 4] do
          let i := lead + 4 * k
          let (c1x, c1y) :=
            if b0 == 26 then (x + (if k == 0 then d1 else 0), y + arg i)
            else (x + arg i, y + (if k == 0 then d1 else 0))
          let c2x := c1x + arg (i + 1)
          let c2y := c1y + arg (i + 2)
          if b0 == 26 then
            x := c2x
            y := c2y + arg (i + 3)
          else
            x := c2x + arg (i + 3)
            y := c2y
          cmds := cmds.push (.cube c1x c1y c2x c2y x y)
          minY := min minY (min c1y (min c2y y))
        stk := #[]
        pc := pc + 1
      else if b0 == 30 || b0 == 31 then
        let mut horiz := b0 == 31
        let mut i := 0
        for _ in [0:n] do
          if i + 4 > n then
            break
          let lastFive := i + 5 == n
          let (c1x, c1y) :=
            if horiz then (x + arg i, y) else (x, y + arg i)
          let c2x := c1x + arg (i + 1)
          let c2y := c1y + arg (i + 2)
          if horiz then
            x := c2x + (if lastFive then arg (i + 4) else 0)
            y := c2y + arg (i + 3)
          else
            x := c2x + arg (i + 3)
            y := c2y + (if lastFive then arg (i + 4) else 0)
          cmds := cmds.push (.cube c1x c1y c2x c2y x y)
          minY := min minY (min c1y (min c2y y))
          i := i + (if lastFive then 5 else 4)
          horiz := !horiz
        stk := #[]
        pc := pc + 1
      else if b0 == 10 || b0 == 29 then
        let subs := if b0 == 10 then lsubrs else gsubrs
        let idx := (stk.back?.getD 0) + biasOf subs.size
        stk := stk.pop
        if frames.size ≥ 24 || idx < 0 then
          bad := true
        else
          match subs[idx.toNat]? with
          | some (ss, se) =>
            frames := frames.push (pc + 1, lim)
            pc := ss
            lim := se
          | none => bad := true
      else if b0 == 11 then
        match frames.back? with
        | some (rp, rl) =>
          frames := frames.pop
          pc := rp
          lim := rl
        | none => done := true
      else if b0 == 14 then
        -- With four arguments, endchar is Type 1's `seac` (Technical Note #5177 Appendix C).
        if n ≥ 4 then
          let bc := arg (n - 2)
          let ac := arg (n - 1)
          if 0 ≤ bc && 0 ≤ ac then
            seac := some (arg (n - 4), arg (n - 3), bc.toNat, ac.toNat)
          else bad := true
        done := true
      else if b0 == 12 then
        let b1 := u8 b (pc + 1)
        if b1 == 35 && n ≥ 13 then
          for k in [0:2] do
            let i := 6 * k
            let c1x := x + arg i
            let c1y := y + arg (i + 1)
            let c2x := c1x + arg (i + 2)
            let c2y := c1y + arg (i + 3)
            x := c2x + arg (i + 4)
            y := c2y + arg (i + 5)
            cmds := cmds.push (.cube c1x c1y c2x c2y x y)
            minY := min minY (min c1y (min c2y y))
        else if b1 == 34 && n ≥ 7 then
          let y0 := y
          let c1x := x + arg 0
          let c2x := c1x + arg 1
          let c2y := y + arg 2
          let p1x := c2x + arg 3
          cmds := cmds.push (.cube c1x y c2x c2y p1x c2y)
          let c3x := p1x + arg 4
          let c4x := c3x + arg 5
          x := c4x + arg 6
          y := y0
          cmds := cmds.push (.cube c3x c2y c4x y0 x y0)
          minY := min minY (min y0 c2y)
        else if b1 == 36 && n ≥ 9 then
          let y0 := y
          let c1x := x + arg 0
          let c1y := y + arg 1
          let c2x := c1x + arg 2
          let c2y := c1y + arg 3
          let p1x := c2x + arg 4
          cmds := cmds.push (.cube c1x c1y c2x c2y p1x c2y)
          let c3x := p1x + arg 5
          let c4x := c3x + arg 6
          let c4y := c2y + arg 7
          x := c4x + arg 8
          y := y0
          cmds := cmds.push (.cube c3x c2y c4x c4y x y0)
          minY := min minY (min c1y (min c2y (min c4y y0)))
        else if b1 == 37 && n ≥ 11 then
          let x0 := x
          let y0 := y
          let dxs := arg 0 + arg 2 + arg 4 + arg 6 + arg 8
          let dys := arg 1 + arg 3 + arg 5 + arg 7 + arg 9
          let c1x := x + arg 0
          let c1y := y + arg 1
          let c2x := c1x + arg 2
          let c2y := c1y + arg 3
          let p1x := c2x + arg 4
          let p1y := c2y + arg 5
          cmds := cmds.push (.cube c1x c1y c2x c2y p1x p1y)
          let c3x := p1x + arg 6
          let c3y := p1y + arg 7
          let c4x := c3x + arg 8
          let c4y := c3y + arg 9
          if dxs.natAbs > dys.natAbs then
            x := c4x + arg 10
            y := y0
          else
            x := x0
            y := c4y + arg 10
          cmds := cmds.push (.cube c3x c3y c4x c4y x y)
          minY := min minY (min c1y (min c2y (min p1y (min c3y (min c4y y)))))
        else if b1 == 0 then
          pure ()
        else
          bad := true
        stk := #[]
        pc := pc + 2
      else
        bad := true
  if bad || !done then
    return none
  return some (⟨cmds, minY⟩, seac)

/-- The glyph that a StandardEncoding code names in a name-keyed font: the
charset entry holding the code's standard string. -/
private def Cff.stdGlyph (c : Cff) (code : Nat) : Option Nat := do
  let sid ← GlyphList.standardSid code
  c.charset.findIdx? (· == sid)

/-- An outline moved by `(dx, dy)`. -/
private def shiftCmds (dx dy : Int) : Cmd → Cmd
  | .move x y => .move (x + dx) (y + dy)
  | .line x y => .line (x + dx) (y + dy)
  | .quad cx cy x y => .quad (cx + dx) (cy + dy) (x + dx) (y + dy)
  | .cube a b c d x y => .cube (a + dx) (b + dy) (c + dx) (d + dy) (x + dx) (y + dy)

/-- Glyph `g`'s outline: its charstring run, a `seac` composed of base and accent glyphs. -/
private def Cff.outline (b : ByteArray) (c : Cff) (g : Nat) : Option Outline := do
  let cs ← c.charStrings[g]?
  let ls := if c.cid then ((c.fdOf[g]?).bind (c.fdSubrs[·]?)).getD #[] else c.lsubrs
  let (o, seac) ← runCharstring b c.gsubrs ls cs
  match seac with
  | none => some o
  | some (adx, ady, bc, ac) =>
    let bg ← c.stdGlyph bc
    let ag ← c.stdGlyph ac
    let bcs ← c.charStrings[bg]?
    let acs ← c.charStrings[ag]?
    let (bo, s1) ← runCharstring b c.gsubrs c.lsubrs bcs
    let (ao, s2) ← runCharstring b c.gsubrs c.lsubrs acs
    guard (s1.isNone && s2.isNone)
    some { cmds := o.cmds ++ bo.cmds ++ ao.cmds.map (shiftCmds adx ady)
           minY := min o.minY (min bo.minY (ao.minY + ady)) }

/-- The prepared outline source of one font; `.opaque` when outlines cannot be read at all. -/
public inductive Src where
  | cffSrc (data : ByteArray) (c : Cff)
  | glyfSrc (data : ByteArray) (glyf loca : Table) (long : Bool) (numGlyphs : Nat)
  | opaque

public instance : Inhabited Src := ⟨.opaque⟩

/-- An OpenType font's `CFF ` table, its bytes alone: offsets inside a CFF
are relative to its own start. -/
public def cffTable (b : ByteArray) : Option ByteArray := do
  let t ← findTable b "CFF "
  guard (fits b t)
  return b.extract t.offset (t.offset + t.length)

/-- The outline source of a bare CFF: a PDF's `FontFile3` of subtype
`Type1C` or `CIDFontType0C`, name-keyed or CID-keyed. -/
public def Src.ofCff (b : ByteArray) : Src :=
  match parseCff b with
  | some c => .cffSrc b c
  | none => .opaque

public def Src.make (b : ByteArray) (isCff : Bool) (numGlyphs : Nat) : Src :=
  if isCff then
    match cffTable b with
    | some t => Src.ofCff t
    | none => .opaque
  else
    match findTable b "head", findTable b "loca", findTable b "glyf" with
    | some head, some loca, some glyf =>
      let long := u16 b (head.offset + 50) == 1
      let entry := if long then 4 else 2
      if fits b loca && fits b glyf && (numGlyphs + 1) * entry ≤ loca.length then
        .glyfSrc b glyf loca long numGlyphs
      else
        .opaque
    | _, _, _ => .opaque

/-- An outline's rectangular hull in font units, control points included; empty is zero. -/
public structure Bounds where
  left : Int := 0
  bottom : Int := 0
  right : Int := 0
  top : Int := 0
  deriving Repr, BEq, Inhabited

public def Bounds.union (a b : Bounds) : Bounds :=
  ⟨min a.left b.left, min a.bottom b.bottom, max a.right b.right, max a.top b.top⟩

public def Outline.bounds (o : Outline) : Bounds := Id.run do
  let mut hull : Option Bounds := none
  let add (hull : Option Bounds) (x y : Int) :=
    let p : Bounds := ⟨x, y, x, y⟩
    some (hull.map (·.union p) |>.getD p)
  for c in o.cmds do
    match c with
    | .move x y | .line x y => hull := add hull x y
    | .quad cx cy x y => hull := add (add hull cx cy) x y
    | .cube c1x c1y c2x c2y x y => hull := add (add (add hull c1x c1y) c2x c2y) x y
  return hull.getD {}

public def Outline.yExtent (o : Outline) : Int × Int :=
  let b := o.bounds
  (b.bottom, b.top)

/-- The ink hull of glyph `g`, or `none` where its outline does not decode. -/
public def Src.boundsAt (s : Src) (g : Nat) : Option Bounds :=
  match s with
  | .opaque => none
  | .cffSrc b c => do
    let o ← c.outline b g
    some o.bounds
  | .glyfSrc b glyf loca long numGlyphs =>
    let o1 := if long then u32 b (loca.offset + 4 * g)
      else 2 * u16 b (loca.offset + 2 * g)
    let o2 := if long then u32 b (loca.offset + 4 * (g + 1))
      else 2 * u16 b (loca.offset + 2 * (g + 1))
    if g ≥ numGlyphs then
      none
    else if o2 == o1 then
      some {}
    else if o2 < o1 || o2 > glyf.length || o1 + 10 > glyf.length then
      none
    else
      (glyfOutline b glyf loca long numGlyphs g).map (·.bounds)

/-- The vertical ink extent `(minY, maxY)` of glyph `g` in font units. -/
public def Src.yExtentAt (s : Src) (g : Nat) : Option (Int × Int) :=
  (s.boundsAt g).map fun b => (b.bottom, b.top)

/-- Glyph `g`'s outline commands, or `none` where the decoder cannot read it. -/
public def Src.cmdsAt (s : Src) (g : Nat) : Option (Array Cmd) :=
  match s with
  | .opaque => none
  | .cffSrc b c => do
    let o ← c.outline b g
    some o.cmds
  | .glyfSrc b glyf loca long numGlyphs =>
    if g ≥ numGlyphs then none
    else (glyfOutline b glyf loca long numGlyphs g).map (·.cmds)

/-- Merged ink intervals of glyph `g` inside the underline band, or `none` where undecodable. -/
public def Src.inkAt (s : Src) (g : Nat) (bandLo bandHi : Int) :
    Option (Array (Int × Int)) :=
  match s with
  | .opaque => none
  | .cffSrc b c =>
    match c.outline b g with
    | none => none
    | some o => some (bandIntervals o bandLo bandHi)
  | .glyfSrc b glyf loca long numGlyphs =>
    let o1 := if long then u32 b (loca.offset + 4 * g)
      else 2 * u16 b (loca.offset + 2 * g)
    let o2 := if long then u32 b (loca.offset + 4 * (g + 1))
      else 2 * u16 b (loca.offset + 2 * (g + 1))
    if g ≥ numGlyphs then
      none
    else if o2 == o1 then
      some #[]
    else if o2 < o1 || o2 > glyf.length || o1 + 10 > glyf.length then
      none
    -- A simple glyph's own bbox may skip the decode; a composite's need not bound its components.
    else if i16 b (glyf.offset + o1) ≥ 0 && i16 b (glyf.offset + o1 + 4) ≥ bandHi then
      some #[]
    else
      match glyfOutline b glyf loca long numGlyphs g with
      | none => none
      | some o => some (bandIntervals o bandLo bandHi)

/-- Whether a source is a CID-keyed CFF. -/
public def Src.isCidCff : Src → Bool
  | .cffSrc _ c => c.cid
  | .glyfSrc .. => false
  | .opaque => false

/-- How many glyphs a CFF holds; 0 for any other source. -/
public def Src.cffGlyphCount : Src → Nat
  | .cffSrc _ c => c.charStrings.size
  | .glyfSrc .. => 0
  | .opaque => 0

/-- The glyph a CID names in a CID-keyed CFF: the charset entry holding it
(Technical Note #5176 §13). -/
public def Src.cidGlyph (s : Src) (cid : Nat) : Option Nat :=
  match s with
  | .cffSrc _ c => if c.cid then c.charset.findIdx? (· == cid) else none
  | .glyfSrc .. => none
  | .opaque => none

/-- Two font matrices composed, PDF's row-vector order: glyph space through
`inner`, then `outer`. -/
private def composeMatrix (inner outer : Array Rat) : Array Rat :=
  let g (m : Array Rat) (i : Nat) : Rat := m[i]?.getD 0
  #[g inner 0 * g outer 0 + g inner 1 * g outer 2, g inner 0 * g outer 1 + g inner 1 * g outer 3,
    g inner 2 * g outer 0 + g inner 3 * g outer 2, g inner 2 * g outer 1 + g inner 3 * g outer 3,
    g inner 4 * g outer 0 + g inner 5 * g outer 2 + g outer 4,
    g inner 4 * g outer 1 + g inner 5 * g outer 3 + g outer 5]

/-- A CFF glyph's font matrix, glyph space to text space: the Top DICT's,
and in a CID-keyed font its font dictionary's composed under it. -/
public def Src.cffMatrix (s : Src) (g : Nat) : Option (Array Rat) :=
  match s with
  | .cffSrc _ c =>
    if c.cid then
      match (c.fdOf[g]?).bind (c.fdMatrix[·]?) with
      | some (some fd) => some (composeMatrix fd c.matrix)
      | _ => some c.matrix
    else some c.matrix
  | .glyfSrc .. => none
  | .opaque => none

/-- The glyph a name names in a name-keyed CFF: the charset entry holding
its string identifier — a standard string's (0–390, Technical Note #5176
Appendix A), or a custom one's (391 on, from the String INDEX). -/
public def Src.nameGlyph (s : Src) (name : String) : Option Nat :=
  match s with
  | .cffSrc b c =>
    if c.cid then none else
    let bytes := name.toUTF8
    let sid := (GlyphList.cffSid? name).orElse fun _ =>
      (c.strings.findIdx? fun (st, en) => b.extract st en == bytes).map (391 + ·)
    sid.bind fun sid => c.charset.findIdx? (· == sid)
  | .glyfSrc .. => none
  | .opaque => none

/-- A glyph's charset entry in a CFF: its string identifier, or in a
CID-keyed font its CID. -/
public def Src.charsetAt (s : Src) (g : Nat) : Option Nat :=
  match s with
  | .cffSrc _ c => c.charset[g]?
  | .glyfSrc .. => none
  | .opaque => none

public theorem Src.cidCff_agree (s : Src) (cid g : Nat) (h : s.cidGlyph cid = some g) :
    s.charsetAt g = some cid := by
  cases s with
  | cffSrc b c =>
    simp only [Src.cidGlyph] at h
    split at h
    · obtain ⟨hg, hp, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp h
      simp only [Src.charsetAt, Array.getElem?_eq_getElem hg, Option.some.injEq]
      simpa using hp
    · simp at h
  | glyfSrc => simp [Src.cidGlyph] at h
  | «opaque» => simp [Src.cidGlyph] at h

public theorem Src.bareCff_agree (b t : ByteArray) (n : Nat) (h : cffTable b = some t) :
    Src.make b true n = Src.ofCff t := by
  simp [Src.make, h]

/-- The glyph a code selects through a name-keyed CFF's own encoding. -/
public def Src.builtinGlyph (s : Src) (code : Nat) : Option Nat :=
  match s with
  | .cffSrc _ c => if c.cid then none else (c.builtin[code]?).getD none
  | .glyfSrc .. => none
  | .opaque => none

/-- A glyph's name in a name-keyed CFF: the standard or custom string its
charset entry names. -/
public def Src.glyphName (s : Src) (g : Nat) : Option String :=
  match s with
  | .cffSrc b c =>
    if c.cid then none else do
    let sid ← c.charset[g]?
    if sid < 391 then GlyphList.cffString? sid
    else
      let (st, en) ← c.strings[sid - 391]?
      String.fromUTF8? (b.extract st en)
  | .glyfSrc .. => none
  | .opaque => none

end LeanTex.Core.Ink
