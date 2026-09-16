namespace LeanTex.Core.Ink

/-! Glyph ink in the underline band, from the font's own outlines.

For each glyph: the horizontal extent of actual ink crossing the band the
underline rule occupies, as merged x-intervals in font units. The rule is
interrupted only where an outline really crosses it — `q` keeps its rule
under the bowl and clears it at the stem. Everything here is total over
arbitrary bytes: a malformed table yields no intervals, never a panic, and a
glyph whose outline the decoder does not cover is reported as `none` so the
caller can fall back conservatively. -/

/-- A bounded byte read. Out of range is 0 rather than a panic: these parsers
are fed arbitrary files, and a reader that aborts the process on a short
table is not a parser. -/
def u8 (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (b[i]).toNat else 0

def u16 (b : ByteArray) (i : Nat) : Nat := u8 b i * 256 + u8 b (i + 1)

def u32 (b : ByteArray) (i : Nat) : Nat :=
  ((u8 b i * 256 + u8 b (i + 1)) * 256 + u8 b (i + 2)) * 256 + u8 b (i + 3)

def i8 (b : ByteArray) (i : Nat) : Int :=
  let v := u8 b i
  if v ≥ 0x80 then (v : Int) - 0x100 else v

def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 0x8000 then (v : Int) - 0x10000 else v

def i32 (b : ByteArray) (i : Nat) : Int :=
  let v := u32 b i
  if v ≥ 0x80000000 then (v : Int) - 0x100000000 else v

structure Table where
  offset : Nat
  length : Nat

def findTable (b : ByteArray) (tag : String) : Option Table := Id.run do
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

/-- Does a table's declared extent fit inside the file? A table that does not
is a broken font, and saying so beats reading zeros off the end of it. -/
def fits (b : ByteArray) (t : Table) : Bool :=
  t.offset + t.length ≤ b.size

/-- One outline command, absolute font-unit coordinates. -/
inductive Cmd where
  | move (x y : Int)
  | line (x y : Int)
  | quad (cx cy x y : Int)
  | cube (c1x c1y c2x c2y x y : Int)
  deriving Inhabited

/-- A decoded outline: its commands, and the lowest y any point reaches —
control points included, so by the convex-hull property the curve itself
never goes lower. A glyph whose `minY` clears the band has no ink in it and
is never flattened. -/
structure Outline where
  cmds : Array Cmd
  minY : Int

/-- Straight edges in doubled coordinates, each curve cut into eight chords.
Doubling puts every vertex at an even y, so a scanline at an odd y never
meets one and the crossing count is unambiguous. -/
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
        let px := (a * x0 + m * x1 + z * x2) / 64
        let py := (a * y0 + m * y1 + z * y2) / 64
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
        let px := (a * x0 + m * x1 + z * x2 + w * x3) / 512
        let py := (a * y0 + m * y1 + z * y2 + w * y3) / 512
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

/-- Merged x-intervals (font units) of ink inside `[bandLo, bandHi]`: the
x-projection of every flattened edge clipped to the band, unioned with the
winding-fill runs on the band's midline. This covers all flattened ink in
the band: a point of ink either has a contour edge somewhere on its vertical
line inside the band — the clipped projection of that edge covers it — or it
sits strictly inside ink across the whole band height, and then the midline
fill run covers it. What remains approximate is curve flattening (eight
chords per curve, a deviation of a few font units at the extremes) and the
integer interpolation at the clip (one unit); both are orders of magnitude
under the clearance the consumer dilates every interval by. -/
def bandIntervals (o : Outline) (bandLo bandHi : Int) : Array (Int × Int) := Id.run do
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

-- TrueType outlines --------------------------------------------------------

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

/-- Decode a simple glyph (numberOfContours ≥ 0 at `off`) under `t`,
appending to `acc`. Reads are bounded by `lim` (the end of this glyph's
slice): a glyph that declares more than its slice holds, or exceeds the
contour or point budget, is undecodable (`none`) rather than silently
truncated — the caller must fall back conservatively. -/
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

/-- Decode glyph `g` of a TrueType font. `none` for anything the decoder
does not cover or the data does not support: an out-of-range component gid,
a component list past the budget, point-matching arguments, a malformed
loca entry, or a glyph slice that overruns its table — the caller falls
back conservatively. Only a genuinely empty glyph decodes to nothing. -/
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
      -- A genuinely empty glyph (a space): no outline, no ink.
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
          -- point-matching component: not decoded
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
        -- component list past the budget: undecoded remainder
        bad := true
      if p > lim then
        bad := true
  if bad || !work.isEmpty then
    return none
  return some ⟨cmds, minY⟩

-- CFF (Type 2 charstring) outlines ------------------------------------------

/-- Entries of a CFF INDEX as absolute (start, end) byte ranges, plus the
offset just past the INDEX. -/
private def parseIndex (b : ByteArray) (pos : Nat) :
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

/-- The DICT operators this consumer needs; numbers it does not (reals) parse
as zero, which only ever loses an offset and falls back. -/
private def parseDict (b : ByteArray) (s e : Nat) : CffDict := Id.run do
  let mut ops : Array Int := #[]
  let mut d : CffDict := {}
  let mut p := s
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
      -- real number: skip nibbles to the 0xf terminator
      p := p + 1
      for _ in [0:e - p] do
        let v := u8 b p
        p := p + 1
        if v % 16 == 15 || v / 16 == 15 then
          break
      ops := ops.push 0
    else if b0 == 12 then
      let b1 := u8 b (p + 1)
      p := p + 2
      if b1 == 6 then
        d := { d with cstype := ops.back?.getD 2 }
      else if b1 == 36 || b1 == 37 then
        d := { d with cid := true }
      ops := #[]
    else
      p := p + 1
      if b0 == 17 then
        d := { d with charStrings := (ops.back?.getD 0).toNat }
      else if b0 == 18 then
        if ops.size ≥ 2 then
          d := { d with
            privSize := (ops[ops.size - 2]?.getD 0).toNat
            privOff := (ops.back?.getD 0).toNat }
      else if b0 == 19 then
        d := { d with subrs := (ops.back?.getD 0).toNat }
      ops := #[]
  return d

private structure Cff where
  charStrings : Array (Nat × Nat)
  gsubrs : Array (Nat × Nat)
  lsubrs : Array (Nat × Nat)

/-- The pieces of a non-CID CFF table the interpreter needs. `none` for a
CID-keyed font or anything malformed: every glyph then falls back. -/
private def parseCff (b : ByteArray) : Option Cff := do
  let t ← findTable b "CFF "
  guard (fits b t)
  let base := t.offset
  let hdrSize := u8 b (base + 2)
  let (_, p1) ← parseIndex b (base + hdrSize)
  let (tops, p2) ← parseIndex b p1
  let (_, p3) ← parseIndex b p2
  let (gsubrs, _) ← parseIndex b p3
  let (ts, te) ← tops[0]?
  let d := parseDict b ts te
  guard (!d.cid && d.cstype == 2)
  let (cs, _) ← parseIndex b (base + d.charStrings)
  let lsubrs :=
    if d.privSize > 0 && base + d.privOff + d.privSize ≤ b.size then
      let pd := parseDict b (base + d.privOff) (base + d.privOff + d.privSize)
      if pd.subrs > 0 then
        match parseIndex b (base + d.privOff + pd.subrs) with
        | some (ls, _) => ls
        | none => #[]
      else #[]
    else #[]
  return { charStrings := cs, gsubrs := gsubrs, lsubrs := lsubrs }

/-- Run one Type 2 charstring into an outline. Explicit subroutine frames
and a step budget keep it total on arbitrary bytes; `none` marks a
charstring the interpreter does not cover (seac composition, arithmetic
operators) or that never terminates within the budget, which the caller
treats conservatively. -/
private def runCharstring (b : ByteArray) (c : Cff) (cs : Nat × Nat) :
    Option Outline := Id.run do
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
        -- moveto family; a leading width may pad the front, so args read
        -- from the end
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
        let subs := if b0 == 10 then c.lsubrs else c.gsubrs
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
        if n ≥ 4 then
          -- seac accent composition: not decoded
          bad := true
        else
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
  return some ⟨cmds, minY⟩

/-- The prepared outline source of one font, tables resolved once so
per-glyph decoding is pay-as-you-go. `.opaque`: outlines that cannot be
read at all — a CFF table that would not parse or is CID-keyed, TrueType
tables missing, truncated, or too short for the glyph count — so every
glyph is `none` and the consumer falls back to clearing its whole
advance. -/
inductive Src where
  | cffSrc (data : ByteArray) (c : Cff)
  | glyfSrc (data : ByteArray) (glyf loca : Table) (long : Bool) (numGlyphs : Nat)
  | opaque

def Src.make (b : ByteArray) (isCff : Bool) (numGlyphs : Nat) : Src :=
  if isCff then
    match parseCff b with
    | some c => .cffSrc b c
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

/-- Merged ink intervals of glyph `g` inside the underline band, or `none`
where the outline could not be decoded and the caller must fall back. Total
over arbitrary bytes. -/
def Src.inkAt (s : Src) (g : Nat) (bandLo bandHi : Int) :
    Option (Array (Int × Int)) :=
  match s with
  | .opaque => none
  | .cffSrc b c =>
    match c.charStrings[g]? with
    | none => none
    | some cs =>
      match runCharstring b c cs with
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
      -- A genuinely empty glyph has no ink.
      some #[]
    else if o2 < o1 || o2 > glyf.length || o1 + 10 > glyf.length then
      none
    -- A header whose own yMin clears the band never needs its outline
    -- decoded.
    else if i16 b (glyf.offset + o1 + 4) ≥ bandHi then
      some #[]
    else
      match glyfOutline b glyf loca long numGlyphs g with
      | none => none
      | some o => some (bandIntervals o bandLo bandHi)

end LeanTex.Core.Ink
